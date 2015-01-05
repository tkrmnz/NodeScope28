var express = require("express");
var http = require("http");
var finalhandler = require('finalhandler');
var serveStatic = require('serve-static');
var SerialPort = require("serialport").SerialPort;
var hex = require('hex');
var async = require('async');
var fs = require('fs');
var lineReader = require('line-reader');
var csv = require('comma-separated-values');
var path = require("path");

var dirName = "/home/root/NodeScope28/public/";
//var dirName = "/home/root/NodeExp/public/";
var serve = serveStatic("/home/root/NodeScope28/public");
//var serve = serveStatic("/home/root/NodeExp/public");
var app = express();
var serialPort = new SerialPort("/dev/MSO-28-0",{
		baudrate: 460800
//		dataBits: 8,
//		parity: 'none',
//		stopBits: 1,
//		flowControl: false
		});
//app.use(logger());
//var msoRstADC = new Buffer('@LDS~^PNP~');
//var msoOff = new Buffer('@LDS~N@~');
//var HexBuf;
var DSOCtlBase = 0;
var MsoBusy=0;
var trigStatBusy=0
var spdata;
var dataValid = 0;
var trigStat = 0;
var serReadStyle = 0;
var FBuf=[];
var MBuf = new Buffer(32);
var bbb = new Buffer(4096);
//var bbb;
var bbbLength;
var PrevSid;
var CurrSid;
var sidA= 0;
var sidB= 0;
var sidC= 0;
var sidD= 0;
var sidE= 0;
var SetChanged=0;
var sidQueue = [];
var sidQueueSize = 30;
var connectionInstances = 0;

//-----param
var vbitDiv10=[];
var OffsetVBitDiv10=[];
var OffsetCenterValDiv10=[];
var vbit=[];
var OffsetVBit=[];
var  OffsetCenterVal=[];
var msoType;
var modelNumber;
var serialNumber;
var vDiv =[];
var ProbeAttn=[];
var ACDCMode = [];
var OffsetDbl=[];
var LogFam;
var sampleInterval;
var TrigLevel =[];
var TrigSlope = [];
var SLOPE_RISING = 0;
var SLOPE_FALLING = 1;
var TrigLAWord=[];
var TrigPosition;
var TrigSPIWd = [];
var TrigI2CWd =[];
var TrigSPIMode;
var TrigWidth =[];
var TrigModeDSO= [];
var TrigChan;

var TRIG_CHAN_DSO = 0;
var TRIG_CHAN_DSO1 = 1;
var TRIG_CHAN_LA = 2;
var TRIG_CHAN_SER_I2C = 3;
var TRIG_CHAN_SER_SPI = 4;

var TRIG_DSO_EDGE = 0;
var TRIG_DSO_GE = 1;
var TRIG_DSO_LT = 2;

var FALSE = 0;
var TRUE = 1;
var OffsetDacVal=[];
var VGND = 511.0;
var ADCMAX = 1023.0;


var STOP = FALSE;
var sampleInterval;
var ClkRateMSB;
var ClkRateLSB;

var rawMask;
var rawTmp;
var MAddr;
var currReq;
var currRes;

var AnalogDataA=[];
var AnalogDataB=[];
var LogicData=[];
var AnalogVoltageDataA=[];
var AnalogVoltageDataB=[];
var debug = 0;
var dispStat = 0;

//----------

//  serialPort.on("open", function () {
//     serialPort.on('data', function(data) {
//        console.log('data received: ' + data);
//      });
//  });


function BufTransLower(Addr,Val)
{
	var i;
	i = Val & 0x3f;
	if ((i & 0x20) != 0x20)
	    i |= 0x40;
	return i;
}

//-----------------------------------------------------

function BufTransUpper(Addr, Val)
{
	var i, j, k;
	i = Addr & 0x0f;
	j = Val & 0xc0;
	j = j >> 2;
	k = i | j;
	if ((k & 0x20) != 0x20)
	    k |= 0x40;
	return k;
}

//-----------------------------------------------------

function SerBufInit()
{
	var hBuf;
	//Preload @LDS~
	hBuf = '@LDS~';
	return hBuf;
}
//-----------------------------------------------------
function SPI_DevSel(Dev)
{
	var SPItmp = 0x00;
    var j;

	if (Dev == 0x02) j = SPItmp | 0x20;//SPI Mem
    else if (Dev == 0x01) j = SPItmp | 0x04;//SPI ADC
    else j = SPItmp;

	return j;
}
//-----------------------------------------------------
//SPI clock H
function SPI_CH(Dev)
{
    var j;
    var HexBuf;
    
	DSOCtlBase = 0x10;
	HexBuf=SerBufInit();
	j = SPI_DevSel(Dev);
    j ^= 0x01;
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI_CH');
		return results;
	});
}
//-----------------------------------------------------
//SPI clock L
function SPI_CL(Dev)
{
    var j;
    var HexBuf;
    
	DSOCtlBase = 0x10;
//	BufTransCnt = 0;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	j = SPI_DevSel(Dev);
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI_CL');
		return results;
	});
}
//-----------------------------------------------------
//SPI transfer Start
function SPI_Start(Dev)
{
    var j;
	var HexBuf;
	
	DSOCtlBase = 0x10;
//	BufTransCnt = 0;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	j = SPI_DevSel(Dev);
	HexBuf += String.fromCharCode(BufTransUpper(0x06, 0x00));//Pre start CS high
	HexBuf += String.fromCharCode(BufTransLower(0x06, 0x00));
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C CS low
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI_Start');
		return results;
	});
}
//-----------------------------------------------------
//SPI transfer Start
function SPI_Stop(Dev)
{
    var j;
	var HexBuf;
	
	DSOCtlBase = 0x10;
//	BufTransCnt = 0;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	j = SPI_DevSel(Dev);
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C CS low
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	HexBuf += String.fromCharCode(BufTransUpper(0x06, 0x00));//Pre start CS high
	HexBuf += String.fromCharCode(BufTransLower(0x06, 0x00));
	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI_Stop');
		return results;
	});
}
//-----------------------------------------------------
//SPI data out
function SPI_Mem_Out(val)
{
	var SPItmp = 0x20;
    var i,j;
	var HexBuf

	DSOCtlBase = 0x10;
//	BufTransCnt = 0;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	j = SPItmp;
    for (i = 0; i <= 7; i++)
    {
        if ((val & (0x80 >> i)) != 0x00) j |= 0x02;
        else j &= 0xfd;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
        j ^= 0x01;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
        j ^= 0x01;
    }
    j &= 0xfd;
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//Data L, Clk L
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
  	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI_Mem_Out');
		return results;
	});
}

//-----------------------------------------------------


function ResetFSM(){
//	var BufTransCnt = 0;
	var HexBuf;
	
	DSOCtlBase = 0x10;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, (DSOCtlBase|0x01)));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, (DSOCtlBase|0x01)));
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, DSOCtlBase));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, DSOCtlBase));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
//		console.log('ResetFSM');
		return results;
	});
};
//-----------------------------------------------------
function ForceCapture(){
//	var BufTransCnt = 0;
	var HexBuf;
	DSOCtlBase = 0x10;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();

	HexBuf += String.fromCharCode(BufTransUpper(0x0e, (DSOCtlBase|0x08)));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, (DSOCtlBase|0x08)));
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, DSOCtlBase));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, DSOCtlBase));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
//		console.log('ForceCap');
		return results;
	});
};
//-----------------------------------------------------
function LEDOff(){
//	var BufTransCnt = 0;
	var HexBuf;
	
	DSOCtlBase &= 0xef;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();

	HexBuf += String.fromCharCode(BufTransUpper(0x0e, DSOCtlBase));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, DSOCtlBase));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
//		console.log('msoOff');
		return results;
	});
};
//-----------------------------------------------------

function ResetADC(){
//	var BufTransCnt = 0;
	var HexBuf;
	
	DSOCtlBase = 0x10;
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();

	HexBuf += String.fromCharCode(BufTransUpper(0x0e, (DSOCtlBase|0x40)));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, (DSOCtlBase|0x40)));
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, DSOCtlBase));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, DSOCtlBase));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
//		console.log('resetADC');
		return results;
	});
};

//-----------------------------------------------------
function CheckTriggerStatus(){
	var HexBuf;
	var data;
	var j;
	
	HexBuf=SerBufInit();
	HexBuf += String.fromCharCode(BufTransUpper(0x02, 0x00));
	HexBuf += String.fromCharCode(BufTransLower(0x02, 0x00));
	HexBuf += '~';
	serReadStyle = 1;
	dataValid = 0;
	trigStatBusy=1;
	serialPort.write(HexBuf, function(err, result) {
		if(err) throw err;
		return result;
	});
};		
//------------------------
function watiForDataValid(){
	while (dataValid !=1);
	if(dispStat===1) console.log('raw data ready\n');
	
}
//------------------------------------------------------------------
//function CheckTriggerStatusRaw(valTmp,valMask){
function CheckTriggerStatusRaw(){
//	var BufTransCnt = 0;
	var HexBuf;
	var data;
	var j;
	
//	BufTransCnt = SerBufInit(BufTransCnt);
	HexBuf=SerBufInit();
	HexBuf += String.fromCharCode(BufTransUpper(0x02, 0x00));
	HexBuf += String.fromCharCode(BufTransLower(0x02, 0x00));
	HexBuf += '~';
//	console.log(HexBuf);

//	serialPort.on("open",function() {
	serReadStyle = 2;
	dataValid = 0;
/*	async.series([
		serialPort.write(HexBuf, function(err, result) {
//			console.log('write_wati for raw\n');
		}),
		function (){while(dataValid!=1);},
		function (){if(trigStat != 0x00) valTmp |= valMask;}

	]);
*/
	serialPort.write(HexBuf, function(err, result) {
//			console.log('write_wati for raw\n');
	});
//		waitForDataValid(),

//	return valTmp;
//	return trigStat 
};		
//----------------------------------------------------------
//SPI read byte 
function SPI_Read_Gut82(Dev)
{
    var val1;
    var ret = 0x00;
    var trgTmp;
    
  //  var rawTmp = 0x00;
	//var rawMask;
	rawTmp = 0x00;
	rawMask = 0x80;
	
	async.series([
		SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev),
	    SPI_CH(Dev),
		CheckTriggerStatusRaw(),
	    SPI_CL(Dev)
	    ]);
	    
 //   console.log("rawTmp="+rawTmp);

//	return rawTmp;
//    return ret;

}

//-----------------------------------------------------
//SPI read 16 byte page
function SPI_Read_Buf_Page(Dev, Page)
{
    var mode;
    var Addr, Cnt;//Data
    Cnt = 0;

	SPI_Start(Dev);
	mode = 0x03; //Read
	SPI_Mem_Out(mode);
	Addr = Page * 16;
	SPI_Mem_Out(Addr);
	for (Cnt = 0; Cnt <= 15; Cnt++)
	{
	    MBuf[Addr + Cnt] = SPI_Read_Gut82(Dev);
	}
	SPI_Stop(Dev);
}

//------------------------------------------
//Parse SPI EEProm data into MSO calibration parameters
function ParseEprom()
{
    var Chan, BufPos;
	var tmp;
	
//	console.log(FBuf);
	
	msoType = FBuf[0];
	modelNumber = FBuf[1];
	serialNumber = ((FBuf[3] << 8) + FBuf[2]);
    BufPos = 4;
    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        vbitDiv10[Chan] = tmp / 10000.0;
        BufPos += 2;
    }

    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        OffsetVBitDiv10[Chan] = tmp / 10000.0;
        BufPos += 2;
    }

    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        OffsetCenterValDiv10[Chan] = tmp;
        BufPos += 2;
    }
    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        vbit[Chan] = tmp / 10000.0;
        BufPos += 2;
    }

    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        OffsetVBit[Chan] = tmp / 10000.0;
        BufPos += 2;
    }

    for (Chan = 0; Chan < 2; Chan++)
    {
        tmp = (FBuf[BufPos + 1] << 8) + FBuf[BufPos];
        OffsetCenterVal[Chan] = tmp;
        BufPos += 2;
    }
	

}
//-----------------------------------------------------
//Screen dump of MSO calibration parameters
function PrintMsoParam()
{
	var i,j;


/*	for(j=0;j<2;j++){
		for(i=0;i<16;i++)
		//			console.log('write_wati for raw\n');
 		console.log(FBuf[(j*16)+i]+' ');
//		console.log("\n");
	}
	*/
	
		
	console.log("MSO Type= "+msoType);
	console.log("Model Number= "+modelNumber);
	console.log("SN= "+serialNumber);
//	console.log("\n");
	for(i=0;i<2;i++){
		console.log("vbit["+i+"]="+vbit[i]);
	}
	for(i=0;i<2;i++){
		console.log("OffsetVBit["+i+"]="+OffsetVBit[i]);
	}
	for(i=0;i<2;i++){
		console.log("OffsetCenterVal["+i+"]="+OffsetCenterVal[i]);
	}
	console.log("\n");
	for(i=0;i<2;i++){
		console.log("vbitDiv10["+i+"]="+vbitDiv10[i]);
	}
	for(i=0;i<2;i++){
		console.log("OffsetVBitDiv10["+i+"]="+OffsetVBitDiv10[i]);
	}
	for(i=0;i<2;i++){
		console.log("OffsetCenterValDiv10["+i+"]="+OffsetCenterValDiv10[i]);
	}
	//console.log("\n");
}
//----------------------------------------------
//write msodata.csv file
function WriteMsoData()
{
	var fileName = 'fcgi-bin/tmp/msodata'+CurrSid+'.csv';
	var Cnt;
	var tmpLine;
	var tmpBuffer = [];
	
	for(Cnt=0; Cnt <1023;Cnt++){
		tmpLine=null
		tmpLine = AnalogVoltageDataA[Cnt]+'\t'+AnalogVoltageDataB[Cnt]+'\t'+LogicData[Cnt]+'\n';
		tmpBuffer += tmpLine;
	}		

	fs.open(dirName+fileName, "w", function(err, fd) {
		if(err) throw err;
		fs.appendFile(dirName+fileName,tmpBuffer,function(){
			if(dispStat===1) console.log('MsoData write '+CurrSid);
			fs.close(fd);
			MsoBusy=0;
			trigStatBusy=0;
//							currRes.end('29\n'+CurrSid+"\n");

		});
	});
}
//----------------------------------
//write settings.bin file
function WriteMsoSettings()
{
	var fileName = 'fcgi-bin/msoset.txt';
	var Cnt;
	var tmpLine;
	var tmpBuffer = [];
	
	tmpBuffer = 'vDiv0,'+vDiv[0]+'\n';
	tmpBuffer += 'vDiv1,'+vDiv[1]+'\n';
	tmpBuffer += 'ProbeAttn0,'+ProbeAttn[0]+'\n';
	tmpBuffer += 'ProbeAttn1,'+ProbeAttn[1]+'\n';
	tmpBuffer += 'ACDCMode0,'+ACDCMode[0]+'\n';
	tmpBuffer += 'ACDCMode1,'+ACDCMode[1]+'\n';
	tmpBuffer += 'OffsetDbl0,'+OffsetDbl[0]+'\n';
	tmpBuffer += 'OffsetDbl1,'+OffsetDbl[1]+'\n';
	tmpBuffer += 'LogFam,'+LogFam+'\n';
	tmpBuffer += 'sampleInterval,'+sampleInterval+'\n';
	tmpBuffer += 'TrigLevel0,'+TrigLevel[0]+'\n';
	tmpBuffer += 'TrigLevel1,'+TrigLevel[1]+'\n';
	tmpBuffer += 'TrigSlope0,'+TrigSlope[0]+'\n';
	tmpBuffer += 'TrigSlope1,'+TrigSlope[1]+'\n';
	tmpBuffer += 'TrigLAWord,'+TrigLAWord+'\n';
	tmpBuffer += 'TrigLASlope,'+TrigSlope[2]+'\n';
	tmpBuffer += 'TrigPosition,'+TrigPosition+'\n';
	tmpBuffer += 'TrigSPIWd,'+TrigSPIWd+'\n';
	tmpBuffer += 'TrigI2CWd,'+TrigI2CWd+'\n';
	tmpBuffer += 'TrigSPIMode,'+TrigSPIMode+'\n';
	tmpBuffer += 'TrigWidth0,'+TrigWidth[0]+'\n';
	tmpBuffer += 'TrigWidth1,'+TrigWidth[1]+'\n';
	tmpBuffer += 'TrigModeDSO0,'+TrigModeDSO[0]+'\n';
	tmpBuffer += 'TrigModeDSO1,'+TrigModeDSO[1]+'\n';
	tmpBuffer += 'TrigChan,'+TrigChan+'\n';

	fs.open(dirName+fileName, "w", function(error, fd) {
		fs.appendFile(dirName+fileName,tmpBuffer,function(){
			if(dispStat===1) console.log('Msoset file write');
			if(debug ===1)console.log('WriteMSOSetting\n'+tmpBuffer);
			fs.close(fd);
		});
	});

}
//----------------------------------------------
//write msocfg.bin file
function WriteMsoParam()
{
//	var fileName = "home/root/NodeExp/public/fcgi-bin/msocfg.bin";
	var fileName = "fcgi-bin/msocfg.bin";

	fs.open(dirName+fileName, "w", function(error, fd) {
		fs.writeFile(dirName+fileName,MBuf,'Binary',function(err){
	  		if (err) throw err;
	  		if(dispStat===1) console.log('file Param write');
			fs.close(fd);
		});
	});
		
}

//-----------------------------------------------------
//Read msocfg.bin file 
function ReadMsoParam()
{
	var fileName = "fcgi-bin/msocfg.bin";

	fs.open(dirName+fileName, "r", function(error, fd) {
		fs.readFile(dirName+fileName,function(err,data){
			if(err) throw err;
			FBuf = data;
			fs.close(fd);
		});
	});
//	FBuf = fs.readFileSync(dirName+fileName,null);
//	console.log("RB="+FBuf);
	
}
//-----------------------------------------------------/Read msocfg.bin file 
//Read msodata.csv file 
function ReadMsoData()
{
	var fileName = "fcgi-bin/msocfg.bin";

	fs.open(dirName+fileName, "r", function(error, fd) {
		fs.readFile(dirName+fileName,function(error,data){
			if(err) throw err;
			FBuf = data;
		fs.close(fd);
		});
	});
//	FBuf = fs.readFileSync(dirName+fileName,null);


}
//-----------------------------------------------------
function ReadMsoSettings2()
{
	var fileName = "fcgi-bin/msoset.txt";
	var line;
	var pVal;
	var vVal;
	var n;
	var len;
	
	fs.exists(dirName+fileName, function(exists) {
		if(exists){
//			console.log('setting2');
			fs.open(dirName+fileName, "r", function(error, fd) {
			lineReader.eachLine(dirName+fileName, function(line, last) {
//		  		if (err) throw err;
		  		n= line.search(',');
				len = line.length;
				pVal = line.substring(0,n);
				vVal = line.substring(n+1,len);
			if(debug === 1)	console.log(line+" "+pVal+" "+vVal);
			if(pVal =="vDiv0") vDiv[0]=parseInt(vVal);
			if(pVal =="vDiv1") vDiv[1]=parseInt(vVal);
			if(pVal =="ProbeAttn0") ProbeAttn[0]=parseInt(vVal);
			if(pVal =="ProbeAttn1") ProbeAttn[1]=parseInt(vVal);
			if(pVal =="ACDCMode0") ACDCMode[0]=parseInt(vVal);
			if(pVal =="ACDCMode1") ACDCMode[1]=parseInt(vVal);
			if(pVal =="OffsetDbl0") OffsetDbl[0]=parseInt(vVal);
			if(pVal =="OffsetDbl1") OffsetDbl[1]=parseInt(vVal);
			if(pVal =="LogFam") LogFam=parseInt(vVal);
			if(pVal =="sampleInterval") sampleInterval=parseInt(vVal);
			if(pVal =="TrigLevel0") TrigLevel[0]=parseInt(vVal);
			if(pVal =="TrigLevel1") TrigLevel[1]=parseInt(vVal);
			if(pVal =="TrigSlope0") TrigSlope[0]=parseInt(vVal);
			if(pVal =="TrigSlope1") TrigSlope[1]=parseInt(vVal);
			if(pVal =="TrigLAWord") TrigLAWord = vVal;
			if(pVal =="TrigI2CWord") TrigI2CWord = vVal;
			if(pVal =="TrigSPIWord") TrigSPIWord = vVal;
			if(pVal =="TrigLASlope") TrigSlope[2]=parseInt(vVal);
			if(pVal =="TrigPosition") TrigPosition=parseInt(vVal);
			if(pVal =="TrigSPIMode") TrigSPIMode=parseInt(vVal);
			if(pVal =="TrigWidth0") TrigWidth[0]=parseInt(vVal);
			if(pVal =="TrigWidth1") TrigWidth[1]=parseInt(vVal);
			if(pVal =="TrigModeDSO0") TrigModeDSO[0]=parseInt(vVal);
			if(pVal =="TrigModeDSO1") TrigModeDSO[1]=parseInt(vVal);
			if(pVal =="TrigChan") TrigChan=parseInt(vVal);
//		  		console.log(line);
			if(last===true)	fs.close(fd);

			});
		});

		}
	});	


}
//-----------------------------------
function PrintMSOSettings()
{
	console.log("PrintMSOSettings");
	console.log("vDiv0 = "+vDiv[0]+" vDiv1 = "+vDiv[1]);
	console.log("ProbeAttn0 = "+ProbeAttn[0]+" ProbeAttn1 = "+ProbeAttn[1]);
	console.log("ACDCMode0 = "+ACDCMode[0]+" ACDCMode1 = "+ACDCMode[1]);
	console.log("OffsetDbl0 = "+OffsetDbl[0]+" OffsetDbl1 = "+OffsetDbl[1]);
	console.log("LogFam = "+LogFam);
	console.log("sampleInterval = "+sampleInterval);
	console.log("TrigLevel0 = "+TrigLevel[0]+" TrigLevel1 = "+TrigLevel[1]);
	console.log("TrigSlope0 = "+TrigSlope[0]+" TrigSlope1 = "+TrigSlope[1]);
	console.log("TrigLAWord = "+TrigLAWord);
	console.log("TrigLASlope = "+TrigSlope[2]);
	console.log("TrigPosition = "+TrigPosition);
	console.log("TrigSPIWd = "+TrigSPIWd);
	console.log("TrigI2CWd = "+TrigI2CWd);
	console.log("TrigSPIMode = "+TrigSPIMode);
	console.log("TrigWidth0 = "+TrigWidth[0]+" TrigWidth1 = "+TrigWidth[1]);
	console.log("TrigModeDSO0 = "+TrigModeDSO[0]+" TrigModeDSO1 = "+TrigModeDSO[1]);
	console.log("TrigChan = "+TrigChan);

}
//-----------------------------------
/*
function RotateSid(sidT)
{
	var Ret;
	Ret = sidE;
	sidE=sidD;
	sidD=sidC;
	sidC=sidB;
	sidB=sidA;
	sidA=sidT;
	return Ret;
}*/
//-----------------------------------
function RotateSid(sidT)
{
	var Ret;
	
	sidQueue.push(sidT);
	if (sidQueue.length > sidQueueSize) {
		Ret = sidQueue.shift();
	}
	else Ret = 0;
	if(debug===1) console.log(sidQueue.length+' '+Ret);
	return Ret;
}
//-----------------------------------
function ArmMSO()
{

	var BufTransCnt = 0;
	var HexBuf;

	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, (DSOCtlBase|0x01)));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, (DSOCtlBase|0x01)));
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, (DSOCtlBase|0x02)));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, (DSOCtlBase|0x02)));
	HexBuf += String.fromCharCode(BufTransUpper(0x0e, DSOCtlBase));
	HexBuf += String.fromCharCode(BufTransLower(0x0e, DSOCtlBase));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
		if(dispStat===1) console.log('Armed');
	});


}
//-----------------------------------------------------
function InitSettings()
{
	vDiv[0] = 500;			vDiv[1] = 500;
	//vDiv
	ProbeAttn[0] = 1;  	ProbeAttn[1] = 1;
	//ProbeAttn
	ACDCMode[0] = 0;		ACDCMode[1] = 0;
	//ACDCMode
	OffsetDbl[0] = 0;	   OffsetDbl[1] = 0;
	//OffsetDbl
	LogFam = 5;
	//LogFam
	sampleInterval = 10;
	//sampleInterval
	TrigLevel[0] = 0;	   	TrigLevel[1] = 0;
	//TrigLevel
//	printf("nv3.1= %s %s\n",name_val_pairs[0].name,name_val_pairs[0].value);

	TrigSlope[0] = SLOPE_RISING;
	TrigSlope[1] = SLOPE_RISING;
	TrigSlope[2] = SLOPE_RISING;
	//TrigSlope	
	TrigLAWord[0] = 0;
	TrigLAWord = "XXXXXXXX";
//	strcat(TrigLAWord,"XXXXXXXX");
//	printf("nv3.2= %s %s\n",name_val_pairs[0].name,name_val_pairs[0].value);
	//TrigLAWord
	TrigPosition = 500;
	//TrigPosition
	TrigSPIWd[0] = 0;
	TrigSPIWd = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX";
//	strcat(TrigSPIWd,"XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX");
	//TrigSPIWd
	TrigI2CWd[0] = 0;
	TrigI2CWd = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX";
//	strcat(TrigI2CWd,"XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX");
//	printf("nv3.3= %s %s\n",name_val_pairs[0].name,name_val_pairs[0].value);

	//TrigI2CWd
	TrigSPIMode = 0;
	//TrigSPIMode
	TrigWidth[0] = 0;
	TrigWidth[1] = 0;
	//TrigWidth
	TrigModeDSO[0] = 0;
	TrigModeDSO[1] = 0;
	//TrigModeDSO
	TrigChan = TRIG_CHAN_DSO;
	//TrigChan
}


//-----------------------------------------------------
function CalcRateMSBLSB(nsRate)
{
    var ret = 0;
    SlowMode = 0x00;
    switch (Number(nsRate))
    {
        case 1: //RIS mode 1GSa
        case 5: ClkRateMSB = 0x02; ClkRateLSB = 0x05; break;//Tstg = "200Msa/S";
        case 10: ClkRateMSB = 0x01; ClkRateLSB = 0x03; break;//Tstg = "100Msa/S";
        case 20: ClkRateMSB = 0x03; ClkRateLSB = 0x02; break;//Tstg = "50Msa/S";
        case 50: ClkRateMSB = 0x03; ClkRateLSB = 0x08; break;//Tstg = "20Msa/S" 3;
        case 100: ClkRateMSB = 0x03; ClkRateLSB = 0x12; break;//Tstg = "10Msa/S" 8;
        case 200: ClkRateMSB = 0x03; ClkRateLSB = 0x26; break;//Tstg = "5Msa/S" 18;
        case 500: ClkRateMSB = 0x03; ClkRateLSB = 0x62; break;//Tstg = "2Msa/S" 48;
        case 1000: ClkRateMSB = 0x03; ClkRateLSB = 0xc6; break;//Tstg = "1Msa/S" 98; 
        case 2000: ClkRateMSB = 0x07; ClkRateLSB = 0x8e; break;//Tstg = "500Ksa/S" 198;
        case 5000: ClkRateMSB = 0x0f; ClkRateLSB = 0xe6; break;//Tstg = "200Ksa/S" 498; 
        case 10000: ClkRateMSB = 0x1f; ClkRateLSB = 0xce; break;//Tstg = "100Ksa/S" 998;
        case 20000: ClkRateMSB = 0x3f; ClkRateLSB = 0x9e; break;//Tstg = "50Ksa/S" 1998; 
        case 50000: ClkRateMSB = 0x9f; ClkRateLSB = 0x0e; break;//Tstg = "20Ksa/S" 4998;
        //0322612 slow rate
		case 100000: ClkRateMSB = 0x03; ClkRateLSB = 0xc6; SlowMode = 0x20; break;//Tstg = "10Ksa/S" 9998;
        case 200000: ClkRateMSB = 0x07; ClkRateLSB = 0x8e; SlowMode = 0x20; break;//Tstg = "5Ksa/S" 199;  
        case 500000: ClkRateMSB = 0x0f; ClkRateLSB = 0xe6; SlowMode = 0x20; break;//Tstg = "2Ksa/S" 499;
        case 1000000: ClkRateMSB = 0x1f; ClkRateLSB = 0xce; SlowMode = 0x20; break;//Tstg = "1Ksa/S" 999;
        case 2000000: ClkRateMSB = 0x3f; ClkRateLSB = 0x9e; SlowMode = 0x20; break;//Tstg = "500sa/S" 1999; 
        case 5000000: ClkRateMSB = 0x9f; ClkRateLSB = 0x0e; SlowMode = 0x20; break;//Tstg = "20sa/S" 4999;
 //       case 10000000: ClkRateMSB = 0x9f; ClkRateLSB = 0x0f; SlowMode = 0x20; break;//Tstg = "10sa/S" 9999;
        default:
            ret = -1;
            break;
    }

    return ret;
}

//-----------------------------------------------------
function ClkRateOut(MSB, LSB)
{

	var BufTransCnt = 0;
	var HexBuf;
	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);
	HexBuf += String.fromCharCode(BufTransUpper(0x09, MSB));
	HexBuf += String.fromCharCode(BufTransLower(0x09, MSB));
	HexBuf += String.fromCharCode(BufTransUpper(0x0a, LSB));
	HexBuf += String.fromCharCode(BufTransLower(0x0a, LSB));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
		if(dispStat===1) console.log('clk out');
	});
}
//-----------------------------------------------------
function ReadBuffer()
{

	var BufTransCnt = 0;
	var HexBuf;
	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);
	HexBuf += String.fromCharCode(BufTransUpper(0x01, 0x00));
	HexBuf += String.fromCharCode(BufTransLower(0x01, 0x00));
	HexBuf += '~';
//	console.log(HexBuf);
	bbbLength = 0;
	bbb = [];
	
	serialPort.write(HexBuf, function(err, results) {
		if(dispStat===1) console.log('ReadBuffer');
	});
}
//-----------------------------------------------------
function GetOffsetVBit(Chan)
{
    if (vDiv[Chan] > 50)
		return OffsetVBitDiv10[Chan];
    else
		return OffsetVBit[Chan];
}
//-----------------------------------------------------
function GetOffsetCenterVal(Chan)
{
    if (vDiv[Chan] > 50)
        return OffsetCenterValDiv10[Chan];
    else
        return OffsetCenterVal[Chan];
}
//-----------------------------------------------------
function GetVbit(Chan)
{
    if (vDiv[Chan] > 50)
        return vbitDiv10[Chan];
    else
        return vbit[Chan];
}
//-----------------------------------------------------
function CalcOffsetRawValueFromVoltage(volts, Chan)
{ //don't need to adjust for probe atten
    var DacVal;
    var DacTmp;

	DacTmp = (GetOffsetCenterVal(Chan) - ((volts / ProbeAttn[Chan]) / GetOffsetVBit(Chan)));
	
	if (DacTmp < 0) DacVal = 0x0000;
    else if (DacTmp > 0x0fff) DacVal = 0x0fff;
    else DacVal = (DacTmp);
	
//	console.log('DacVal='+DacVal);
    return DacVal;
}
//-----------------------------------------------------
function DAC_Out_SPI()
{
    var MSB, LSB;

    LSB = OffsetDacVal[0] & 0x00ff;
    MSB = (OffsetDacVal[0] & 0xff00) >> 8;
    MSB |= 0x80;

    SPI_Out_DAC(2, MSB, LSB);//ChA

    LSB = OffsetDacVal[1] & 0x00ff;
    MSB = (OffsetDacVal[1] & 0xff00) >> 8;
    MSB |= 0x40;

    SPI_Out_DAC(2, MSB, LSB); //ChB
}        //set trigger value
//-----------------------------------------------------
function SPI_Out_DAC(DAC, MSB, LSB)
{
    var SPItmp = 0x00;
    var i, j;

	var BufTransCnt = 0;
	var HexBuf;

	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);

	if (DAC == 0x02) j = (SPItmp | 0x10);
	else if (DAC == 0x01) j = (SPItmp | 0x08);
	else j = SPItmp;

	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	for (i = 0; i <= 7; i++)
	{
	    if ((MSB & (0x80 >> i)) != 0x00) j |= 0x02;
	    else j &= 0xfd;
	    j ^= 0x01;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	    j ^= 0x01;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	}
	for (i = 0; i <= 7; i++)
	{
	    if ((LSB & (0x80 >> i)) != 0x00) j |= 0x02;
	    else j &= 0xfd;
	    j ^= 0x01;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	    j ^= 0x01;
		HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
		HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	}
	j = SPItmp;
	HexBuf += String.fromCharCode(BufTransUpper(0x06, j));//I2C Ctl
	HexBuf += String.fromCharCode(BufTransLower(0x06, j));
	HexBuf += '~';
	serialPort.write(HexBuf, function(err, results) {
//		console.log('SPI DAC out');
	});
}
//-----------------------------------------------------
function ConfigureThresholdLevel_SPI()
{
	var MSB, LSB;	
	var tmp = 0x3fc0;
    switch (Number(LogFam))
    {
        case 0: tmp = 0x1740; break;    //1.2V Logic 0x8600
        case 1: tmp = 0x1d00; break;    //1.5V Logic 0x8770
        case 2: tmp = 0x22c0; break;    //1.8V Logic 0x88ff
        case 3: tmp = 0x3080; break;    //2.5V Logic 0x8c70
        case 4: tmp = 0x3a40; break;    //3.0V Logic	0x8eff
        default:
        case 5: tmp = 0x3fc0; break;    //3.3V Logic family   0x8fff
    }

    LSB = tmp & 0x00ff;
    MSB = (tmp & 0xff00) >> 8;
 //	if(debug===1) console.log('Logic threshold MSB='+MSB+' LSB='+LSB)
    SPI_Out_DAC(1, MSB, LSB);//Logic Threshold

}
//-----------------------------------------------------
			
function CalcRawValueFromVoltage(val, Chan)
{
//	if(debug===1)console.log('Chan='+Chan+' val='+val+' ProbeAttn='+ProbeAttn[Chan]+' GetVbit='+GetVbit(Chan));
    return parseInt((512 - ((val/ProbeAttn[Chan]) / GetVbit(Chan))));
}
//-----------------------------------------------------
function ConfigureTriggerHardware()
{
    var MSB, LSB; //, SPIDataSource;
    var TrigVal=[];
    var TrigChSel=0;
    var ii;
    var logTrigWd = 0;
    var logTrigIgn = 0;
    var tmpTrigWord=[]; // = "XXXXXXXX";
  	var BufTransCnt = 0;
	var HexBuf;
  

	tmpTrigWord = TrigLAWord;
	
    for (ii = 0; ii < 8; ii++)
    {
        if (tmpTrigWord[ii] == '1')
            logTrigWd |= (0x01 << ii);
        if (tmpTrigWord[ii] == 'x' || tmpTrigWord[ii] == 'X')
            logTrigIgn |= (0x01 << ii);
    }
//	console.log('tmpTrigWorld='+tmpTrigWord+' logTrigWd='+logTrigWd+' logTrigIgn'+logTrigIgn);

	TrigVal[0] = CalcRawValueFromVoltage(
        Number(TrigLevel[TRIG_CHAN_DSO]) + Number(OffsetDbl[TRIG_CHAN_DSO]), 0);
    TrigVal[1] = CalcRawValueFromVoltage(
        Number(TrigLevel[TRIG_CHAN_DSO1]) + Number(OffsetDbl[TRIG_CHAN_DSO1]), 1);
//if(debug === 1)	console.log('TrigVal[0]='+TrigVal[0]+' TrigVal[1]'+TrigVal[1]);


    if (TrigChan == TRIG_CHAN_DSO)
        TrigChSel = 0x00;
    else if (TrigChan == TRIG_CHAN_DSO1)
        TrigChSel = 0x01;
    else if (TrigChan == TRIG_CHAN_LA)
        TrigChSel = 0x02;
    else if (TrigChan == TRIG_CHAN_SER_I2C)
        TrigChSel = 0x05;
    else if (TrigChan == TRIG_CHAN_SER_SPI)
        TrigChSel = 0x04;
        
//if(debug === 1)	console.log('TriChSel='+TrigChSel);

    // default TRIG_DSO_EDGE
    TrigVal[0] &= 0x9fff;
    TrigVal[1] &= 0x9fff;

    if(TrigModeDSO[0] == 1)//TRIG_DSO_GE
		TrigVal[0] |= 0x4000;
    else if(TrigModeDSO[0] == 2)//TRIG_DSO_LT
		TrigVal[0] |= 0x2000;
    
    
    if(TrigModeDSO[1] == 1)//TRIG_DSO_GE
		TrigVal[1] |= 0x4000;
    else if(TrigModeDSO[1] == 2)//TRIG_DSO_LT
		TrigVal[1] |= 0x2000;
     
    
    
    
	if (TrigSlope[0] == SLOPE_FALLING) TrigVal[0] |= 0x0400;
    else TrigVal[0] &= 0xfbff;

    if (TrigSlope[1] == SLOPE_FALLING) TrigVal[1] |= 0x0400;
    else TrigVal[1] &= 0xfbff;


    TrigVal[0] |= 0x0000;//ChVal load selector
    TrigVal[1] |= 0x0800;//ChVal load selector


	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);

	//Width first, TrigVal second

	//---------  Ch0 trig settings
	ii = TrigWidth[0] / sampleInterval;
	if (ii > 3)
	    ii -= 3;
	else
	    ii = 3;

	HexBuf += String.fromCharCode(BufTransUpper(0x0b, ii));
	HexBuf += String.fromCharCode(BufTransLower(0x0b, ii));

	LSB = TrigVal[0] & 0x00ff;
	MSB = (TrigVal[0] & 0xff00) >> 8;
	HexBuf += String.fromCharCode(BufTransUpper(0x03, LSB));
	HexBuf += String.fromCharCode(BufTransLower(0x03, LSB));
	HexBuf += String.fromCharCode(BufTransUpper(0x04, MSB));
	HexBuf += String.fromCharCode(BufTransLower(0x04, MSB));

	//---------  Ch1 trig settings
	ii = TrigWidth[1] / sampleInterval;
	if (ii > 3)
	    ii -= 3;
	else
	    ii = 3;

	HexBuf += String.fromCharCode(BufTransUpper(0x0b, ii));
	HexBuf += String.fromCharCode(BufTransLower(0x0b, ii));

	LSB = TrigVal[1] & 0x00ff;
	MSB = (TrigVal[1] & 0xff00) >> 8;
	HexBuf += String.fromCharCode(BufTransUpper(0x03, LSB));
	HexBuf += String.fromCharCode(BufTransLower(0x03, LSB));
	HexBuf += String.fromCharCode(BufTransUpper(0x04, MSB));
	HexBuf += String.fromCharCode(BufTransLower(0x04, MSB));

	if (TrigSlope[2] == SLOPE_FALLING) TrigChSel |= 0x08;
	else TrigChSel &= 0xf7;

	if (ACDCMode[0] != 0x00) //ChA1 AC/DC
	    TrigChSel |= 0x10;
	else
	    TrigChSel &= 0xef;

	if (ACDCMode[1] != 0x00)//ChA2 AC/DC
	    TrigChSel |= 0x20;
	else
	    TrigChSel &= 0xdf;

	if (vDiv[0] > 50) //ChA1 Div1/Div10
	    TrigChSel &= 0xbf;
	else
	    TrigChSel |= 0x40;

	if (vDiv[1] > 50)//ChA2 Div1/Div10
	    TrigChSel &= 0x7f;
	else
	    TrigChSel |= 0x80;

	var a;
	a = vDiv[0];

	HexBuf += String.fromCharCode(BufTransUpper(0x05, TrigChSel));//park TrigValSelector
	HexBuf += String.fromCharCode(BufTransLower(0x05, TrigChSel));

	HexBuf += String.fromCharCode(BufTransUpper(0x0c, logTrigWd));
	HexBuf += String.fromCharCode(BufTransLower(0x0c, logTrigWd));
	HexBuf += String.fromCharCode(BufTransUpper(0x0d, logTrigIgn));
	HexBuf += String.fromCharCode(BufTransLower(0x0d, logTrigIgn));

	HexBuf += String.fromCharCode(BufTransUpper(0x0f, (0x02 | SlowMode)));//Alt Page 2, SerTrig
	HexBuf += String.fromCharCode(BufTransLower(0x0f, (0x02 | SlowMode)));

	var Dex = 0;
	var SerTrigWd=[];
	var SerIgnWd=[];
	var chtmp;
		
    if (TrigChan == TRIG_CHAN_SER_SPI){
		for (ii = 0; ii < 4; ii++){
		    SerTrigWd[ii] = 0;
		    SerIgnWd[ii] = 0;
		    for (Dex = 0; Dex < 8; Dex++){
				chtmp = TrigSPIWd[((3-ii)*8)+Dex];
				if (chtmp == '1')
		            SerTrigWd[ii] |= (0x01 << Dex);
				else if((chtmp =='X')||(chtmp == 'x'))
		            SerIgnWd[ii] |= (0x01 << Dex);
			}
		}//SPI Parsing
		
		while(SerIgnWd[0] == 0xff){
			SerTrigWd[0] = SerTrigWd[1];
			SerTrigWd[1] = SerTrigWd[2];
			SerTrigWd[2] = SerTrigWd[3];
			SerTrigWd[3] = 0x00;
			SerIgnWd[0] = SerIgnWd[1];
			SerIgnWd[1] = SerIgnWd[2];
			SerIgnWd[2] = SerIgnWd[3];
			SerIgnWd[3] = 0xff;
		}//SPI trigword position swap
	}//SPI
	else if (TrigChan == TRIG_CHAN_SER_I2C){
		for (ii = 0; ii < 4; ii++){
		    SerTrigWd[ii] = 0;
		    SerIgnWd[ii] = 0;
		    for (Dex = 0; Dex < 8; Dex++){
				chtmp = TrigI2CWd[((3-ii)*8)+Dex];
				if (chtmp == '1')
		            SerTrigWd[ii] |= (0x01 << Dex);
				else if((chtmp =='X')||(chtmp == 'x'))
		            SerIgnWd[ii] |= (0x01 << Dex);
			}
		}//I2C Parsing
		
		while(SerIgnWd[0] == 0xff){
			SerTrigWd[0] = SerTrigWd[1];
			SerTrigWd[1] = SerTrigWd[2];
			SerTrigWd[2] = SerTrigWd[3];
			SerTrigWd[3] = 0x00;
			SerIgnWd[0] = SerIgnWd[1];
			SerIgnWd[1] = SerIgnWd[2];
			SerIgnWd[2] = SerIgnWd[3];
			SerIgnWd[3] = 0xff;
		}//I2C trigword position swap
	}//I2C
//Need to add I2C trigwd


	//serial trigger word [17] .. [24]  - must translate from menu
	HexBuf += String.fromCharCode(BufTransUpper(0x00, SerTrigWd[3]));//SerTrigWd1
	HexBuf += String.fromCharCode(BufTransLower(0x00, SerTrigWd[3]));
	HexBuf += String.fromCharCode(BufTransUpper(0x01, SerTrigWd[2]));
	HexBuf += String.fromCharCode(BufTransLower(0x01, SerTrigWd[2]));
	HexBuf += String.fromCharCode(BufTransUpper(0x02, SerTrigWd[1]));
	HexBuf += String.fromCharCode(BufTransLower(0x02, SerTrigWd[1]));
	HexBuf += String.fromCharCode(BufTransUpper(0x03, SerTrigWd[0]));
	HexBuf += String.fromCharCode(BufTransLower(0x03, SerTrigWd[0]));

	//serial trigger word [25] .. [32] ingnore bits X   - must translate from menu
	HexBuf += String.fromCharCode(BufTransUpper(0x04, SerIgnWd[3]));//SerTrigWd1
	HexBuf += String.fromCharCode(BufTransLower(0x04, SerIgnWd[3]));
	HexBuf += String.fromCharCode(BufTransUpper(0x05, SerIgnWd[2]));
	HexBuf += String.fromCharCode(BufTransLower(0x05, SerIgnWd[2]));
	HexBuf += String.fromCharCode(BufTransUpper(0x06, SerIgnWd[1]));
	HexBuf += String.fromCharCode(BufTransLower(0x06, SerIgnWd[1]));
	HexBuf += String.fromCharCode(BufTransUpper(0x07, SerIgnWd[0]));
	HexBuf += String.fromCharCode(BufTransLower(0x07, SerIgnWd[0]));

	HexBuf += String.fromCharCode(BufTransUpper(0x08, TrigSPIMode));//bit 0,1 = SPI mode
	HexBuf += String.fromCharCode(BufTransLower(0x08, TrigSPIMode));

	HexBuf += String.fromCharCode(BufTransUpper(0x0f, (0x00 | SlowMode)));//bit 0,1 = SPI mode
	HexBuf += String.fromCharCode(BufTransLower(0x0f, (0x00 | SlowMode)));
	//To turn on probe cal signal set (0x0f, 0x10)
	HexBuf += '~';
	
//	console.log('configure Hardware: '+HexBuf);
	serialPort.write(HexBuf, function(err, results) {
		if(dispStat===1) console.log('Config Trig Hardware');
	});

}
//-----------------------------------------------------
function ConfigureTriggerPosition()
{
    var LocalTrigPos;
	var MSB, LSB;

	var BufTransCnt = 0;
	var HexBuf;

    if (TrigPosition >= 0)
    {
        LocalTrigPos = TrigPosition;
        LocalTrigPos &= 0X7fff; //turn off holdoff counter
    }
    else
    {
        LocalTrigPos = TrigPosition * -1;
        LocalTrigPos |= 0X8000; //turn on holdoff counter
    }
    if (sampleInterval == 5) LocalTrigPos += 11;//6
    else if (sampleInterval == 10) LocalTrigPos += 9;//6
    else if (sampleInterval == 20) LocalTrigPos += 9;
    else LocalTrigPos += 3;

    LSB = LocalTrigPos & 0x00ff;
    MSB = (LocalTrigPos & 0xff00) >> 8;

	DSOCtlBase = 0x10;
	HexBuf = SerBufInit(BufTransCnt);
	HexBuf += String.fromCharCode(BufTransUpper(0x07, LSB));
	HexBuf += String.fromCharCode(BufTransLower(0x07, LSB));
	HexBuf += String.fromCharCode(BufTransUpper(0x08, MSB));
	HexBuf += String.fromCharCode(BufTransLower(0x08, MSB));
	HexBuf += '~';
//	console.log(HexBuf);

	serialPort.write(HexBuf, function(err, results) {
		if(dispStat===1) console.log('config Trig Position');
	});
}
//-----------------------------------------------------


function ConfigureHardwareMSO()
{
        CalcRateMSBLSB(sampleInterval);
        ClkRateOut(ClkRateMSB, ClkRateLSB);
//		if(debug===1) console.log('rate = '+sampleInterval+' MSB = '+ClkRateMSB+' LSB = '+ClkRateLSB );

        OffsetDacVal[0] = CalcOffsetRawValueFromVoltage(OffsetDbl[0], 0);
		OffsetDacVal[1] = CalcOffsetRawValueFromVoltage(OffsetDbl[1], 1);

        DAC_Out_SPI();
		ConfigureThresholdLevel_SPI();

        ConfigureTriggerHardware();
		ConfigureTriggerPosition();
        //SerialWrite(SerialP1, timer1, RateBuf + DACBuf1 + DACBuf2 + TrigBuf + TrigPosBuf, vars.DSOD[UnitNum].HardwareStatus);
}
//-----------------------------------------------------
function CalcVoltageFromRawValue(pt, vbit, ProbeAttn)
{
	var ret;
    var Vtmp, Vtmp2,Vtmp3; 
    Vtmp = pt;
    Vtmp2 = (1023.0 - Vtmp) - VGND;
    Vtmp3 = Vtmp2 * vbit * ProbeAttn;
	ret = Vtmp3.toFixed(4);

//	console.log('data='+pt+' vbit='+vbit+' VGND '+VGND+' ProbeAttn='+ProbeAttn+' ret='+ret);
    return ret;
}

//-----------------------------------------------------
function VoltageConvert()
{
    var ii; //, PageSize = 5;
    var VbitA,VbitB;
    var PAtnA,PAtnB;	

    VbitA=GetVbit(0);
    VbitB=GetVbit(1);
    PAtnA=ProbeAttn[0];
    PAtnB=ProbeAttn[1];

//	console.log(VbitA+' '+VbitB+' '+PAtnA+' '+PAtnB+' '+ProbeAttn[0]+' '+ProbeAttn[1]);


    for (ii = 0; ii < 1024; ii++)
        {
            AnalogVoltageDataA[ii] =
                CalcVoltageFromRawValue(AnalogDataA[ii],
                VbitA,
                PAtnA);

            AnalogVoltageDataB[ii] =
                CalcVoltageFromRawValue(AnalogDataB[ii],
                VbitB,
                PAtnB);
//        console.log(AnalogDataB[ii]+' '+AnalogVoltageDataB[ii]);
        }
}
//-----------------------------------------------------






process.argv.forEach(function(val, index, array) {
	if((val =='v')||(val == 'V')) dispStat=1;
	if((val =='d')||(val == 'D')) debug=1;
//  console.log(index + ': ' + val);
});//debug display flag


// Homepage
serialPort.on("open", function () {
  console.log('open');
  var g;
	serialPort.on('data',function(spdata){
//	    console.log('data received: ' + spdata+"\nLength "+spdata.length);
		if(spdata.length==1){//trigstat data
			if(serReadStyle==1){
				trigStat = (spdata.readUInt8(0)&31);
				dataValid = 1;
				if(currReq.query.i == 'T'){
						currRes.writeHead(200, { "Content-Type": "text/plain" });
						currRes.end(trigStat+"\n"+currReq.query.sid+"\n");
				}
				else{
					if(trigStat==22){//triggered ready for extraction
						if(currReq.query.sid==CurrSid){
							ReadBuffer();
							wd =1;
							currRes.writeHead(200, { "Content-Type": "text/plain" });
							currRes.end('29\n'+CurrSid+"\n");
						}//getting mso data
						else{
							currRes.writeHead(200, { "Content-Type": "text/plain" });
							currRes.end('35\n'+CurrSid+"\n");
						}//wrong sid, currently processing CurrSid
					}
					else{//Not triggered
						currRes.writeHead(200, { "Content-Type": "text/plain" });
						currRes.end(trigStat+"\n"+currReq.query.sid+"\n");
					}
				}
				trigStatBusy=0;
	
//				console.log('results ' + trigStat+' '+spdata.readUInt8(0));
			}
			else if(serReadStyle==2){//SPI eeprom read
				trigStat = (spdata.readUInt8(0)&64);
				g = trigStat;
				if(trigStat!=0){
					rawTmp|=rawMask;
//					g = 1;
				}
//				process.stdout.write(' '+g);
				
				if(rawMask==0x01){
					rawMask = 0x80;
				    MBuf[MAddr] = rawTmp;
//					console.log("\n"+MAddr+'='+MBuf[MAddr]+' '+MBuf[MAddr].toString(16));
//					console.log(MAddr+'='+MBuf[MAddr].toString(16));
					process.stdout.write(MBuf[MAddr].toString(16)+' ');
					rawTmp = 0x00;
					MAddr++;
				}
				else{
					rawMask = rawMask >>1;
				}
				if(MAddr == 32)	{
//					console.log('R '+MBuf+" Length="+MBuf.length);
//					console.log(MBuf[0],MBuf[1],MBuf[2]);
					WriteMsoParam();
				}
				dataValid = 1;
			}
		}
		else{//readBuf data
//			console.log('ReadBuffer Size='+spdata.length);
			var zz;
			for(zz=0;zz<spdata.length;zz++){
				bbb[bbbLength+zz] = spdata.readUInt8(zz);
//				console.log(bbb[bbbLength+zz]);
			}

//			bbb += spdata;
//			console.log(spdata);
			bbbLength += spdata.length;
//			console.log('bbbLength='+bbbLength);
			if(bbbLength===4096){
				var AdjAddr = 0;
				var CntPos;
				var Cnt;
								
		        for (Cnt = AdjAddr; Cnt < bbbLength/4; Cnt++){
		            CntPos= Cnt*4;
				    CntAdj=Cnt-AdjAddr;
					AnalogDataA[CntAdj] = ((bbb[CntPos + 1] & 0x03) << 8)|bbb[CntPos];
		            AnalogDataB[CntAdj] = ((bbb[CntPos + 1] & 0xfc) >> 2)|((bbb[CntPos + 2] & 0x0f) << 6); //dso2
		            LogicData[CntAdj]  = ((bbb[CntPos + 2] & 0xf0) >> 4)|((bbb[CntPos + 3] & 0x0f) << 4); //la
		        }//x4
				VoltageConvert();
				WriteMsoData();

			}
		}
	});

  
app.use(function(req, res, next) {
if(dispStat===1) console.log(req.query);
	var sidTmp;
	
	if(req.query.VDIV0){
		vDiv[0] = req.query.VDIV0;
		SetChanged++
	}	    
	if(req.query.VDIV1){
		vDiv[1] = req.query.VDIV1;
		SetChanged++
	}	    
	if(req.query.PATTN0){
		ProbeAttn[0] = req.query.PATTN0;
		SetChanged++
	}	    
	if(req.query.PATTN1){
		ProbeAttn[1] = req.query.PATTN1;
		SetChanged++
	}	    
	if(req.query.ACDC0){
		if(req.query.ACDC0=='DC')
			ACDCMode[0] = 1;
		else
			ACDCMode[0] = 0;
		SetChanged++
	}	    
	if(req.query.ACDC1){
		if(req.query.ACDC1=='DC')
			ACDCMode[1] = 1;
		else
			ACDCMode[1] = 0;
		SetChanged++
	}	    
	if(req.query.VOFF0){
		OffsetDbl[0] = req.query.VOFF0;
		SetChanged++
	}	    	    
	if(req.query.VOFF1){
		OffsetDbl[1] = req.query.VOFF1;
		SetChanged++
	}
	if(req.query.LAFM){
		LogFam = req.query.LAFM;
		SetChanged++
	}	    	    
	if(req.query.TSAMP){
		sampleInterval = req.query.TSAMP;
		SetChanged++
	}	    	    
	if(req.query.TRIGV0){
		TrigLevel[0] = req.query.TRIGV0;
		SetChanged++
	}	    	    
	if(req.query.TRIGV1){
		TrigLevel[1] = req.query.TRIGV1;
		SetChanged++
	}	    	    
	if(req.query.TRSLP0){
		if(req.query.TRSLP0=='R')
			TrigSlope[0] = SLOPE_RISING;
		else
			TrigSlope[0] = SLOPE_FALLING;
		SetChanged++
	}	    
	if(req.query.TRSLP1){
		if(req.query.TRSLP1=='R')
			TrigSlope[1] = SLOPE_RISING;
		else
			TrigSlope[1] = SLOPE_FALLING;
		SetChanged++
	}	    
	if(req.query.TRLAWD){
		TrigLAWord = req.query.TRLAWD;
		SetChanged++
	}	    	    
	if(req.query.TRLASLP){
		if(req.query.TRLASLP=='T')
			TrigSlope[2] = SLOPE_RISING;
		else
			TrigSlope[2] = SLOPE_FALLING;
		SetChanged++
	}	    
	if(req.query.TRPOS){
		TrigPosition = req.query.TRPOS;
		SetChanged++
	}	    	    
	//need TRSPIWD
	//need TRI2CWD
	
	if(req.query.SPIMODE){
		TrigSPIMode = req.query.SPIMODE;
		SetChanged++
	}	    	    
	if(req.query.TRIGWD0){
		TrigWidth[0] = req.query.TRIGWD0;
		SetChanged++
	}	    	    
	if(req.query.TRIGWD1){
		TrigWidth[1] = req.query.TRIGWD1;
		SetChanged++
	}	    	    
	if(req.query.TRMODE0){
		TrigModeDSO[0] = req.query.TRMODE0;
		SetChanged++
	}	    	    
	if(req.query.TRMODE1){
		TrigModeDSO[1] = req.query.TRMODE1;
		SetChanged++
	}	    	    
	if(req.query.TRGCH){
		if(req.query.TRGCH=='A0')
			TrigChan = TRIG_CHAN_DSO;
		else if(req.query.TRGCH=='A1')
			TrigChan = TRIG_CHAN_DSO1;
		else if(req.query.TRGCH=='LA')
			TrigChan = TRIG_CHAN_LA;
		else if(req.query.TRGCH=='I2C')
			TrigChan = TRIG_CHAN_SER_I2C;
		else if(req.query.TRGCH=='SPI')
			TrigChan = TRIG_CHAN_SER_SPI;
		else
			TrigChan = TRIG_CHAN_DSO;
		SetChanged++
	}	    
	
	
	//need wait
	
	
	
		    	    
		    
	if ((req.query.i == 't')||(req.query.i == 'T')){
		if(!trigStatBusy){
			currReq = req;
			currRes = res;
			trigStatReq = req.query.i;
			CheckTriggerStatus();
		}
		else{
			res.writeHead(200, { "Content-Type": "text/plain" });
			res.end("35\n"+CurrSid+"\n");
		}		
	  }
	else if (req.query.i == 'Q'){
		LEDOff();
		if(dispStat===1) console.log('Off');
		
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end("Bye\n"+req.query.sid+"\n");
	}
	else if (req.query.i == 'X'){
		ForceCapture();
		MsoBusy=0;
		if(dispStat===1) console.log('Forced Stop');
		
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end("30\n"+req.query.sid+"\n");
	}
	else if (req.query.i == 'F'){
		ResetFSM();
		MsoBusy=0;
		trigStatBusy=0;
		if(dispStat===1) console.log('ResetFSM');
		
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end("30\n"+req.query.sid+"\n");
	}
	else if (req.query.i == 'I'){
		ResetADC();
		MAddr = 0;
		SPI_Read_Buf_Page(2, 0);
		SPI_Read_Buf_Page(2, 1);
	//	WriteMsoParam(); //write under async read
		LEDOff();
		MsoBusy=0;
	
		if(dispStat===1) console.log('P_Rdy');
		
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end("P_Rdy\n"+req.query.sid+"\n");
	}
	else if (req.query.i == 'p'){
	
		ReadMsoParam();
		ParseEprom();
		PrintMsoParam();
		InitSettings();
		ReadMsoSettings2();
		PrintMSOSettings();			
	//	console.log('Print Param');	
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end(req.query.sid+"\n");
	}
	else if (req.query.i == 'M'){
	
		ReadMsoParam();
		ParseEprom();
	//	PrintMsoParam();
		InitSettings();
		ReadMsoSettings2();
		PrintMSOSettings();	
	
		ConfigureHardwareMSO();
			
	//	console.log('Print Param');	
		res.writeHead(200, { "Content-Type": "text/plain" });
		res.end('26'+req.query.sid+"\n");
	}
	else if ((req.query.i == 'c')||(req.query.i == 'C')){
		if(connectionInstances===0){
			ResetADC();
			if(dispStat===1) console.log('Connected '+connectionInstances);
			ReadMsoParam();
			ParseEprom();
			InitSettings();
	
				fs.readdir(dirName+'fcgi-bin/tmp',function(err,files){
					if(err) throw err;
					files.forEach(function(fileName){
						if(path.extname(fileName) === ".csv"){
							fs.unlink(dirName+'fcgi-bin/tmp/'+fileName,function(err){
								if(err) throw err;
					
								connectionInstances++;
								if(dispStat===1) console.log('delete '+fileName);
							});
		//					fs.unlinkSync(dirName+'fcgi-bin/tmp/'+fileName);
						}
					});
				});	
	//		fs.readdirSync(dirName+'fcgi-bin/tmp').forEach(function(fileName){
	//			if(path.extname(fileName) === ".csv"){
	//				fs.unlinkSync(dirName+'fcgi-bin/tmp/'+fileName);
	//			}
	//		});
		
		MsoBusy=0;
		}//only clear the tmp directory upon the first connection
	
		res.writeHead(200, { "Content-Type": "text/plain" });
		if (req.query.i == 'c'){
			PrintMsoParam();
			res.end("\n"+req.query.sid+"\n");
		}
		else
			res.end("Connected\n"+req.query.sid+"\n");
	}
	else if (req.query.i == 'a'){
		if(!MsoBusy){
			PrevSid=CurrSid;
			MsoBusy=1;
			sidTmp = RotateSid(PrevSid);
			if(sidTmp!=0){
				fs.exists(dirName+'fcgi-bin/tmp/msodata'+sidTmp+'.csv', function(exists) {
					if(exists){
						fs.unlink(dirName+'fcgi-bin/tmp/msodata'+ sidTmp+'.csv',function(err){
							if(err) throw err;
							if(dispStat===1) console.log('msodata delete a '+sidTmp);
						});
//						fs.unlinkSync(dirName+'fcgi-bin/tmp/msodata'+ sidTmp+'.csv');
//						console.log('msodata delete a '+sidTmp);
					}});
//				fs.unlinkSync(dirName+'fcgi-bin/tmp/msodata'+sidTmp+'.csv');
//				console.log('msodata delete');
			}
			
			ArmMSO();
			CurrSid=req.query.sid;
	
			if(dispStat===1) console.log('armed');
			res.writeHead(200, { "Content-Type": "text/plain" });
			res.end("28\n"+CurrSid+"\n");
		}
		else{
			res.writeHead(200, { "Content-Type": "text/plain" });
			res.end("36\n"+CurrSid+"\n");
		}
	}
	else if (req.query.i == 'A'){
		if(!MsoBusy){
			PrevSid=CurrSid;
			MsoBusy=1;
			sidTmp = RotateSid(PrevSid);
			if(sidTmp!=0){
				fs.exists(dirName+'fcgi-bin/tmp/msodata'+sidTmp+'.csv', function(exists) {
					if(exists){
						fs.unlink(dirName+'fcgi-bin/tmp/msodata'+ sidTmp+'.csv',function(err){
							if(err) throw err;
							if(dispStat===1) console.log('msodata delete A '+sidTmp);
						});
//						fs.unlinkSync(dirName+'fcgi-bin/tmp/msodata'+sidTmp+'.csv');
//						console.log('msodata delete A '+sidTmp);
					}});
			}

//			InitSettings();
			if(SetChanged){
				WriteMsoSettings();//write to msoset.txt
				SetChanged = 0;
			}
			ReadMsoParam();
			ParseEprom();
			ReadMsoSettings2();//read back from msoset.txt
			ConfigureHardwareMSO();
	
			CurrSid=req.query.sid;
			ArmMSO();
	
			if(dispStat===1) console.log('Armed');
			res.writeHead(200, { "Content-Type": "text/plain" });
			res.end("27\n"+CurrSid+"\n");
		}
		else{
			res.writeHead(200, { "Content-Type": "text/plain" });
			res.end("37\n"+CurrSid+"\n");
		}
	}
	else if ((req.query.i == 'b')||(req.query.i == 'B')){
		ReadMsoParam();
		ParseEprom();
		ReadBuffer();
//		MsoBusy=0;
//							VoltageConvert();
//							WriteMsoData();
		if(req.query.i=='b'){
			for(i=0;i<2;i++) console.log('vbit['+i+']='+vbit[i]);
			for(i=0;i<2;i++) console.log('OffsetVBit['+i+']='+OffsetVBit[i]);
			for(i=0;i<2;i++) console.log('OffsetCenterVal['+i+']='+OffsetCenterVal[i]);
			for(i=0;i<2;i++) console.log('vbitDiv10['+i+']='+vbitDiv10[i]);
			for(i=0;i<2;i++) console.log('OffsetVBitDiv10['+i+']='+OffsetVBitDiv10[i]);
			for(i=0;i<2;i++) console.log('OffsetCenterValDiv10['+i+']='+OffsetCenterValDiv10[i]);
		}
		
	
		res.writeHead(200, { "Content-Type": "text/plain" });
		if (req.query.i == 'c'){
			PrintMsoParam();
			res.end("\n"+req.query.sid+"\n");
		}
		else
			res.end("Connected\n"+req.query.sid+"\n");
	}


	 else {
	    next();
	  }
});


// 404'd!
app.use(function(req, res) {
  var done = finalhandler(req, res)
  serve(req, res, done)
});

http.createServer(app).listen(2880);
});
