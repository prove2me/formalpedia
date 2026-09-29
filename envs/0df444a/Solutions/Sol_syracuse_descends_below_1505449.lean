-- Prove2me | solution 1 for syracuse_descends_below_1505449
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T23:08:56.644316+00:00
-- url     : https://prove2.me/submissions/ccd68491-045f-4ed7-a04c-bf4b39f40e11

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_1166400
import Theorems.Thm_syracuse_descends_range_1166400_1168400
import Theorems.Thm_syracuse_descends_range_1168401_1170401
import Theorems.Thm_syracuse_descends_range_1170402_1172402
import Theorems.Thm_syracuse_descends_range_1172403_1174403
import Theorems.Thm_syracuse_descends_range_1174404_1176404
import Theorems.Thm_syracuse_descends_range_1176405_1178405
import Theorems.Thm_syracuse_descends_range_1178406_1180406
import Theorems.Thm_syracuse_descends_range_1180407_1182407
import Theorems.Thm_syracuse_descends_range_1182408_1184408
import Theorems.Thm_syracuse_descends_range_1184409_1186409
import Theorems.Thm_syracuse_descends_range_1186410_1188410
import Theorems.Thm_syracuse_descends_range_1188411_1190411
import Theorems.Thm_syracuse_descends_range_1190412_1192412
import Theorems.Thm_syracuse_descends_range_1192413_1194413
import Theorems.Thm_syracuse_descends_range_1194414_1196414
import Theorems.Thm_syracuse_descends_range_1196415_1198415
import Theorems.Thm_syracuse_descends_range_1198416_1200416
import Theorems.Thm_syracuse_descends_range_1200417_1202417
import Theorems.Thm_syracuse_descends_range_1202418_1204418
import Theorems.Thm_syracuse_descends_range_1204419_1206419
import Theorems.Thm_syracuse_descends_range_1206420_1207920
import Theorems.Thm_syracuse_descends_range_1207921_1209421
import Theorems.Thm_syracuse_descends_range_1209422_1211422
import Theorems.Thm_syracuse_descends_range_1211423_1213423
import Theorems.Thm_syracuse_descends_range_1213424_1215424
import Theorems.Thm_syracuse_descends_range_1215425_1217425
import Theorems.Thm_syracuse_descends_range_1217426_1219426
import Theorems.Thm_syracuse_descends_range_1219427_1220927
import Theorems.Thm_syracuse_descends_range_1220928_1222928
import Theorems.Thm_syracuse_descends_range_1222929_1224429
import Theorems.Thm_syracuse_descends_range_1224430_1226430
import Theorems.Thm_syracuse_descends_range_1226431_1228431
import Theorems.Thm_syracuse_descends_range_1228432_1230432
import Theorems.Thm_syracuse_descends_range_1230433_1232433
import Theorems.Thm_syracuse_descends_range_1232434_1234434
import Theorems.Thm_syracuse_descends_range_1234435_1236435
import Theorems.Thm_syracuse_descends_range_1236436_1238436
import Theorems.Thm_syracuse_descends_range_1238437_1240437
import Theorems.Thm_syracuse_descends_range_1240438_1242438
import Theorems.Thm_syracuse_descends_range_1242439_1244439
import Theorems.Thm_syracuse_descends_range_1244440_1246440
import Theorems.Thm_syracuse_descends_range_1246441_1248441
import Theorems.Thm_syracuse_descends_range_1248442_1250442
import Theorems.Thm_syracuse_descends_range_1250443_1252443
import Theorems.Thm_syracuse_descends_range_1252444_1254444
import Theorems.Thm_syracuse_descends_range_1254445_1256445
import Theorems.Thm_syracuse_descends_range_1256446_1258446
import Theorems.Thm_syracuse_descends_range_1258447_1260447
import Theorems.Thm_syracuse_descends_range_1260448_1262448
import Theorems.Thm_syracuse_descends_range_1262449_1264449
import Theorems.Thm_syracuse_descends_range_1264450_1266450
import Theorems.Thm_syracuse_descends_range_1266451_1268451
import Theorems.Thm_syracuse_descends_range_1268452_1270452
import Theorems.Thm_syracuse_descends_range_1270453_1271953
import Theorems.Thm_syracuse_descends_range_1271954_1273954
import Theorems.Thm_syracuse_descends_range_1273955_1275955
import Theorems.Thm_syracuse_descends_range_1275956_1277956
import Theorems.Thm_syracuse_descends_range_1277957_1279957
import Theorems.Thm_syracuse_descends_range_1279958_1281958
import Theorems.Thm_syracuse_descends_range_1281959_1283959
import Theorems.Thm_syracuse_descends_range_1283960_1285960
import Theorems.Thm_syracuse_descends_range_1285961_1287961
import Theorems.Thm_syracuse_descends_range_1287962_1289962
import Theorems.Thm_syracuse_descends_range_1289963_1291963
import Theorems.Thm_syracuse_descends_range_1291964_1293964
import Theorems.Thm_syracuse_descends_range_1293965_1295965
import Theorems.Thm_syracuse_descends_range_1295966_1297966
import Theorems.Thm_syracuse_descends_range_1297967_1299967
import Theorems.Thm_syracuse_descends_range_1299968_1301968
import Theorems.Thm_syracuse_descends_range_1301969_1303969
import Theorems.Thm_syracuse_descends_range_1303970_1305970
import Theorems.Thm_syracuse_descends_range_1305971_1307971
import Theorems.Thm_syracuse_descends_range_1307972_1309972
import Theorems.Thm_syracuse_descends_range_1309973_1311973
import Theorems.Thm_syracuse_descends_range_1311974_1313974
import Theorems.Thm_syracuse_descends_range_1313975_1315975
import Theorems.Thm_syracuse_descends_range_1315976_1317976
import Theorems.Thm_syracuse_descends_range_1317977_1319477
import Theorems.Thm_syracuse_descends_range_1319478_1321478
import Theorems.Thm_syracuse_descends_range_1321479_1323479
import Theorems.Thm_syracuse_descends_range_1323480_1325480
import Theorems.Thm_syracuse_descends_range_1325481_1327481
import Theorems.Thm_syracuse_descends_range_1327482_1328982
import Theorems.Thm_syracuse_descends_range_1328983_1330983
import Theorems.Thm_syracuse_descends_range_1330984_1332984
import Theorems.Thm_syracuse_descends_range_1332985_1334985
import Theorems.Thm_syracuse_descends_range_1334986_1336986
import Theorems.Thm_syracuse_descends_range_1336987_1338987
import Theorems.Thm_syracuse_descends_range_1338988_1340988
import Theorems.Thm_syracuse_descends_range_1340989_1342989
import Theorems.Thm_syracuse_descends_range_1342990_1344990
import Theorems.Thm_syracuse_descends_range_1344991_1346991
import Theorems.Thm_syracuse_descends_range_1346992_1348992
import Theorems.Thm_syracuse_descends_range_1348993_1350993
import Theorems.Thm_syracuse_descends_range_1350994_1352994
import Theorems.Thm_syracuse_descends_range_1352995_1354995
import Theorems.Thm_syracuse_descends_range_1354996_1356996
import Theorems.Thm_syracuse_descends_range_1356997_1358497
import Theorems.Thm_syracuse_descends_range_1358498_1360498
import Theorems.Thm_syracuse_descends_range_1360499_1362499
import Theorems.Thm_syracuse_descends_range_1362500_1364500
import Theorems.Thm_syracuse_descends_range_1364501_1366501
import Theorems.Thm_syracuse_descends_range_1366502_1368502
import Theorems.Thm_syracuse_descends_range_1368503_1370503
import Theorems.Thm_syracuse_descends_range_1370504_1372004
import Theorems.Thm_syracuse_descends_range_1372005_1374005
import Theorems.Thm_syracuse_descends_range_1374006_1375506
import Theorems.Thm_syracuse_descends_range_1375507_1377507
import Theorems.Thm_syracuse_descends_range_1377508_1379508
import Theorems.Thm_syracuse_descends_range_1379509_1381509
import Theorems.Thm_syracuse_descends_range_1381510_1383510
import Theorems.Thm_syracuse_descends_range_1383511_1385511
import Theorems.Thm_syracuse_descends_range_1385512_1387512
import Theorems.Thm_syracuse_descends_range_1387513_1389513
import Theorems.Thm_syracuse_descends_range_1389514_1391514
import Theorems.Thm_syracuse_descends_range_1391515_1393515
import Theorems.Thm_syracuse_descends_range_1393516_1395516
import Theorems.Thm_syracuse_descends_range_1395517_1397517
import Theorems.Thm_syracuse_descends_range_1397518_1399518
import Theorems.Thm_syracuse_descends_range_1399519_1401519
import Theorems.Thm_syracuse_descends_range_1401520_1403520
import Theorems.Thm_syracuse_descends_range_1403521_1405521
import Theorems.Thm_syracuse_descends_range_1405522_1407522
import Theorems.Thm_syracuse_descends_range_1407523_1409523
import Theorems.Thm_syracuse_descends_range_1409524_1411524
import Theorems.Thm_syracuse_descends_range_1411525_1413525
import Theorems.Thm_syracuse_descends_range_1413526_1415526
import Theorems.Thm_syracuse_descends_range_1415527_1417527
import Theorems.Thm_syracuse_descends_range_1417528_1419528
import Theorems.Thm_syracuse_descends_range_1419529_1421529
import Theorems.Thm_syracuse_descends_range_1421530_1423530
import Theorems.Thm_syracuse_descends_range_1423531_1425531
import Theorems.Thm_syracuse_descends_range_1425532_1427532
import Theorems.Thm_syracuse_descends_range_1427533_1429533
import Theorems.Thm_syracuse_descends_range_1429534_1431534
import Theorems.Thm_syracuse_descends_range_1431535_1433535
import Theorems.Thm_syracuse_descends_range_1433536_1435536
import Theorems.Thm_syracuse_descends_range_1435537_1437537
import Theorems.Thm_syracuse_descends_range_1437538_1439538
import Theorems.Thm_syracuse_descends_range_1439539_1441539
import Theorems.Thm_syracuse_descends_range_1441540_1443540
import Theorems.Thm_syracuse_descends_range_1443541_1445541
import Theorems.Thm_syracuse_descends_range_1445542_1447542
import Theorems.Thm_syracuse_descends_range_1447543_1449543
import Theorems.Thm_syracuse_descends_range_1449544_1451544
import Theorems.Thm_syracuse_descends_range_1451545_1453545
import Theorems.Thm_syracuse_descends_range_1453546_1455546
import Theorems.Thm_syracuse_descends_range_1455547_1457547
import Theorems.Thm_syracuse_descends_range_1457548_1459548
import Theorems.Thm_syracuse_descends_range_1459549_1461049
import Theorems.Thm_syracuse_descends_range_1461050_1462550
import Theorems.Thm_syracuse_descends_range_1462551_1464551
import Theorems.Thm_syracuse_descends_range_1464552_1466552
import Theorems.Thm_syracuse_descends_range_1466553_1468553
import Theorems.Thm_syracuse_descends_range_1468554_1470554
import Theorems.Thm_syracuse_descends_range_1470555_1472555
import Theorems.Thm_syracuse_descends_range_1472556_1474556
import Theorems.Thm_syracuse_descends_range_1474557_1476557
import Theorems.Thm_syracuse_descends_range_1476558_1478558
import Theorems.Thm_syracuse_descends_range_1478559_1480559
import Theorems.Thm_syracuse_descends_range_1480560_1482060
import Theorems.Thm_syracuse_descends_range_1482061_1484061
import Theorems.Thm_syracuse_descends_range_1484062_1486062
import Theorems.Thm_syracuse_descends_range_1486063_1488063
import Theorems.Thm_syracuse_descends_range_1488064_1490064
import Theorems.Thm_syracuse_descends_range_1490065_1492065
import Theorems.Thm_syracuse_descends_range_1492066_1494066
import Theorems.Thm_syracuse_descends_range_1494067_1496067
import Theorems.Thm_syracuse_descends_range_1496068_1498068
import Theorems.Thm_syracuse_descends_range_1498069_1500069
import Theorems.Thm_syracuse_descends_range_1500070_1502070
import Theorems.Thm_syracuse_descends_range_1502071_1503571
import Theorems.Thm_syracuse_descends_range_1503572_1505448

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 1505449) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 1166400 with hb | hb
  · exact syracuse_descends_below_1166400 m h1 hb hodd
  rcases Nat.lt_or_ge m 1168401 with hc0 | hc0
  · exact syracuse_descends_range_1166400_1168400 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1170402 with hc1 | hc1
  · exact syracuse_descends_range_1168401_1170401 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1172403 with hc2 | hc2
  · exact syracuse_descends_range_1170402_1172402 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1174404 with hc3 | hc3
  · exact syracuse_descends_range_1172403_1174403 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1176405 with hc4 | hc4
  · exact syracuse_descends_range_1174404_1176404 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1178406 with hc5 | hc5
  · exact syracuse_descends_range_1176405_1178405 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1180407 with hc6 | hc6
  · exact syracuse_descends_range_1178406_1180406 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1182408 with hc7 | hc7
  · exact syracuse_descends_range_1180407_1182407 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1184409 with hc8 | hc8
  · exact syracuse_descends_range_1182408_1184408 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1186410 with hc9 | hc9
  · exact syracuse_descends_range_1184409_1186409 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1188411 with hc10 | hc10
  · exact syracuse_descends_range_1186410_1188410 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1190412 with hc11 | hc11
  · exact syracuse_descends_range_1188411_1190411 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1192413 with hc12 | hc12
  · exact syracuse_descends_range_1190412_1192412 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1194414 with hc13 | hc13
  · exact syracuse_descends_range_1192413_1194413 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1196415 with hc14 | hc14
  · exact syracuse_descends_range_1194414_1196414 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1198416 with hc15 | hc15
  · exact syracuse_descends_range_1196415_1198415 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1200417 with hc16 | hc16
  · exact syracuse_descends_range_1198416_1200416 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1202418 with hc17 | hc17
  · exact syracuse_descends_range_1200417_1202417 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1204419 with hc18 | hc18
  · exact syracuse_descends_range_1202418_1204418 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1206420 with hc19 | hc19
  · exact syracuse_descends_range_1204419_1206419 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1207921 with hc20 | hc20
  · exact syracuse_descends_range_1206420_1207920 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1209422 with hc21 | hc21
  · exact syracuse_descends_range_1207921_1209421 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1211423 with hc22 | hc22
  · exact syracuse_descends_range_1209422_1211422 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1213424 with hc23 | hc23
  · exact syracuse_descends_range_1211423_1213423 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1215425 with hc24 | hc24
  · exact syracuse_descends_range_1213424_1215424 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1217426 with hc25 | hc25
  · exact syracuse_descends_range_1215425_1217425 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1219427 with hc26 | hc26
  · exact syracuse_descends_range_1217426_1219426 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1220928 with hc27 | hc27
  · exact syracuse_descends_range_1219427_1220927 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1222929 with hc28 | hc28
  · exact syracuse_descends_range_1220928_1222928 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1224430 with hc29 | hc29
  · exact syracuse_descends_range_1222929_1224429 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1226431 with hc30 | hc30
  · exact syracuse_descends_range_1224430_1226430 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1228432 with hc31 | hc31
  · exact syracuse_descends_range_1226431_1228431 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1230433 with hc32 | hc32
  · exact syracuse_descends_range_1228432_1230432 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1232434 with hc33 | hc33
  · exact syracuse_descends_range_1230433_1232433 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1234435 with hc34 | hc34
  · exact syracuse_descends_range_1232434_1234434 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1236436 with hc35 | hc35
  · exact syracuse_descends_range_1234435_1236435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1238437 with hc36 | hc36
  · exact syracuse_descends_range_1236436_1238436 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1240438 with hc37 | hc37
  · exact syracuse_descends_range_1238437_1240437 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1242439 with hc38 | hc38
  · exact syracuse_descends_range_1240438_1242438 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1244440 with hc39 | hc39
  · exact syracuse_descends_range_1242439_1244439 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1246441 with hc40 | hc40
  · exact syracuse_descends_range_1244440_1246440 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1248442 with hc41 | hc41
  · exact syracuse_descends_range_1246441_1248441 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1250443 with hc42 | hc42
  · exact syracuse_descends_range_1248442_1250442 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1252444 with hc43 | hc43
  · exact syracuse_descends_range_1250443_1252443 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1254445 with hc44 | hc44
  · exact syracuse_descends_range_1252444_1254444 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1256446 with hc45 | hc45
  · exact syracuse_descends_range_1254445_1256445 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1258447 with hc46 | hc46
  · exact syracuse_descends_range_1256446_1258446 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1260448 with hc47 | hc47
  · exact syracuse_descends_range_1258447_1260447 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1262449 with hc48 | hc48
  · exact syracuse_descends_range_1260448_1262448 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1264450 with hc49 | hc49
  · exact syracuse_descends_range_1262449_1264449 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1266451 with hc50 | hc50
  · exact syracuse_descends_range_1264450_1266450 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1268452 with hc51 | hc51
  · exact syracuse_descends_range_1266451_1268451 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1270453 with hc52 | hc52
  · exact syracuse_descends_range_1268452_1270452 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1271954 with hc53 | hc53
  · exact syracuse_descends_range_1270453_1271953 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1273955 with hc54 | hc54
  · exact syracuse_descends_range_1271954_1273954 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1275956 with hc55 | hc55
  · exact syracuse_descends_range_1273955_1275955 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1277957 with hc56 | hc56
  · exact syracuse_descends_range_1275956_1277956 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1279958 with hc57 | hc57
  · exact syracuse_descends_range_1277957_1279957 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1281959 with hc58 | hc58
  · exact syracuse_descends_range_1279958_1281958 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1283960 with hc59 | hc59
  · exact syracuse_descends_range_1281959_1283959 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1285961 with hc60 | hc60
  · exact syracuse_descends_range_1283960_1285960 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1287962 with hc61 | hc61
  · exact syracuse_descends_range_1285961_1287961 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1289963 with hc62 | hc62
  · exact syracuse_descends_range_1287962_1289962 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1291964 with hc63 | hc63
  · exact syracuse_descends_range_1289963_1291963 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1293965 with hc64 | hc64
  · exact syracuse_descends_range_1291964_1293964 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1295966 with hc65 | hc65
  · exact syracuse_descends_range_1293965_1295965 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1297967 with hc66 | hc66
  · exact syracuse_descends_range_1295966_1297966 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1299968 with hc67 | hc67
  · exact syracuse_descends_range_1297967_1299967 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1301969 with hc68 | hc68
  · exact syracuse_descends_range_1299968_1301968 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1303970 with hc69 | hc69
  · exact syracuse_descends_range_1301969_1303969 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1305971 with hc70 | hc70
  · exact syracuse_descends_range_1303970_1305970 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1307972 with hc71 | hc71
  · exact syracuse_descends_range_1305971_1307971 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1309973 with hc72 | hc72
  · exact syracuse_descends_range_1307972_1309972 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1311974 with hc73 | hc73
  · exact syracuse_descends_range_1309973_1311973 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1313975 with hc74 | hc74
  · exact syracuse_descends_range_1311974_1313974 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1315976 with hc75 | hc75
  · exact syracuse_descends_range_1313975_1315975 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1317977 with hc76 | hc76
  · exact syracuse_descends_range_1315976_1317976 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1319478 with hc77 | hc77
  · exact syracuse_descends_range_1317977_1319477 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1321479 with hc78 | hc78
  · exact syracuse_descends_range_1319478_1321478 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1323480 with hc79 | hc79
  · exact syracuse_descends_range_1321479_1323479 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1325481 with hc80 | hc80
  · exact syracuse_descends_range_1323480_1325480 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1327482 with hc81 | hc81
  · exact syracuse_descends_range_1325481_1327481 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1328983 with hc82 | hc82
  · exact syracuse_descends_range_1327482_1328982 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1330984 with hc83 | hc83
  · exact syracuse_descends_range_1328983_1330983 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1332985 with hc84 | hc84
  · exact syracuse_descends_range_1330984_1332984 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1334986 with hc85 | hc85
  · exact syracuse_descends_range_1332985_1334985 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1336987 with hc86 | hc86
  · exact syracuse_descends_range_1334986_1336986 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1338988 with hc87 | hc87
  · exact syracuse_descends_range_1336987_1338987 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1340989 with hc88 | hc88
  · exact syracuse_descends_range_1338988_1340988 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1342990 with hc89 | hc89
  · exact syracuse_descends_range_1340989_1342989 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1344991 with hc90 | hc90
  · exact syracuse_descends_range_1342990_1344990 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1346992 with hc91 | hc91
  · exact syracuse_descends_range_1344991_1346991 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1348993 with hc92 | hc92
  · exact syracuse_descends_range_1346992_1348992 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1350994 with hc93 | hc93
  · exact syracuse_descends_range_1348993_1350993 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1352995 with hc94 | hc94
  · exact syracuse_descends_range_1350994_1352994 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1354996 with hc95 | hc95
  · exact syracuse_descends_range_1352995_1354995 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1356997 with hc96 | hc96
  · exact syracuse_descends_range_1354996_1356996 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1358498 with hc97 | hc97
  · exact syracuse_descends_range_1356997_1358497 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1360499 with hc98 | hc98
  · exact syracuse_descends_range_1358498_1360498 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1362500 with hc99 | hc99
  · exact syracuse_descends_range_1360499_1362499 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1364501 with hc100 | hc100
  · exact syracuse_descends_range_1362500_1364500 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1366502 with hc101 | hc101
  · exact syracuse_descends_range_1364501_1366501 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1368503 with hc102 | hc102
  · exact syracuse_descends_range_1366502_1368502 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1370504 with hc103 | hc103
  · exact syracuse_descends_range_1368503_1370503 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1372005 with hc104 | hc104
  · exact syracuse_descends_range_1370504_1372004 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1374006 with hc105 | hc105
  · exact syracuse_descends_range_1372005_1374005 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1375507 with hc106 | hc106
  · exact syracuse_descends_range_1374006_1375506 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1377508 with hc107 | hc107
  · exact syracuse_descends_range_1375507_1377507 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1379509 with hc108 | hc108
  · exact syracuse_descends_range_1377508_1379508 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1381510 with hc109 | hc109
  · exact syracuse_descends_range_1379509_1381509 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1383511 with hc110 | hc110
  · exact syracuse_descends_range_1381510_1383510 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1385512 with hc111 | hc111
  · exact syracuse_descends_range_1383511_1385511 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1387513 with hc112 | hc112
  · exact syracuse_descends_range_1385512_1387512 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1389514 with hc113 | hc113
  · exact syracuse_descends_range_1387513_1389513 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1391515 with hc114 | hc114
  · exact syracuse_descends_range_1389514_1391514 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1393516 with hc115 | hc115
  · exact syracuse_descends_range_1391515_1393515 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1395517 with hc116 | hc116
  · exact syracuse_descends_range_1393516_1395516 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1397518 with hc117 | hc117
  · exact syracuse_descends_range_1395517_1397517 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1399519 with hc118 | hc118
  · exact syracuse_descends_range_1397518_1399518 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1401520 with hc119 | hc119
  · exact syracuse_descends_range_1399519_1401519 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1403521 with hc120 | hc120
  · exact syracuse_descends_range_1401520_1403520 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1405522 with hc121 | hc121
  · exact syracuse_descends_range_1403521_1405521 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1407523 with hc122 | hc122
  · exact syracuse_descends_range_1405522_1407522 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1409524 with hc123 | hc123
  · exact syracuse_descends_range_1407523_1409523 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1411525 with hc124 | hc124
  · exact syracuse_descends_range_1409524_1411524 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1413526 with hc125 | hc125
  · exact syracuse_descends_range_1411525_1413525 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1415527 with hc126 | hc126
  · exact syracuse_descends_range_1413526_1415526 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1417528 with hc127 | hc127
  · exact syracuse_descends_range_1415527_1417527 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1419529 with hc128 | hc128
  · exact syracuse_descends_range_1417528_1419528 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1421530 with hc129 | hc129
  · exact syracuse_descends_range_1419529_1421529 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1423531 with hc130 | hc130
  · exact syracuse_descends_range_1421530_1423530 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1425532 with hc131 | hc131
  · exact syracuse_descends_range_1423531_1425531 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1427533 with hc132 | hc132
  · exact syracuse_descends_range_1425532_1427532 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1429534 with hc133 | hc133
  · exact syracuse_descends_range_1427533_1429533 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1431535 with hc134 | hc134
  · exact syracuse_descends_range_1429534_1431534 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1433536 with hc135 | hc135
  · exact syracuse_descends_range_1431535_1433535 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1435537 with hc136 | hc136
  · exact syracuse_descends_range_1433536_1435536 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1437538 with hc137 | hc137
  · exact syracuse_descends_range_1435537_1437537 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1439539 with hc138 | hc138
  · exact syracuse_descends_range_1437538_1439538 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1441540 with hc139 | hc139
  · exact syracuse_descends_range_1439539_1441539 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1443541 with hc140 | hc140
  · exact syracuse_descends_range_1441540_1443540 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1445542 with hc141 | hc141
  · exact syracuse_descends_range_1443541_1445541 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1447543 with hc142 | hc142
  · exact syracuse_descends_range_1445542_1447542 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1449544 with hc143 | hc143
  · exact syracuse_descends_range_1447543_1449543 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1451545 with hc144 | hc144
  · exact syracuse_descends_range_1449544_1451544 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1453546 with hc145 | hc145
  · exact syracuse_descends_range_1451545_1453545 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1455547 with hc146 | hc146
  · exact syracuse_descends_range_1453546_1455546 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1457548 with hc147 | hc147
  · exact syracuse_descends_range_1455547_1457547 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1459549 with hc148 | hc148
  · exact syracuse_descends_range_1457548_1459548 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1461050 with hc149 | hc149
  · exact syracuse_descends_range_1459549_1461049 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1462551 with hc150 | hc150
  · exact syracuse_descends_range_1461050_1462550 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1464552 with hc151 | hc151
  · exact syracuse_descends_range_1462551_1464551 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1466553 with hc152 | hc152
  · exact syracuse_descends_range_1464552_1466552 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1468554 with hc153 | hc153
  · exact syracuse_descends_range_1466553_1468553 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1470555 with hc154 | hc154
  · exact syracuse_descends_range_1468554_1470554 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1472556 with hc155 | hc155
  · exact syracuse_descends_range_1470555_1472555 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1474557 with hc156 | hc156
  · exact syracuse_descends_range_1472556_1474556 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1476558 with hc157 | hc157
  · exact syracuse_descends_range_1474557_1476557 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1478559 with hc158 | hc158
  · exact syracuse_descends_range_1476558_1478558 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1480560 with hc159 | hc159
  · exact syracuse_descends_range_1478559_1480559 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1482061 with hc160 | hc160
  · exact syracuse_descends_range_1480560_1482060 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1484062 with hc161 | hc161
  · exact syracuse_descends_range_1482061_1484061 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1486063 with hc162 | hc162
  · exact syracuse_descends_range_1484062_1486062 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1488064 with hc163 | hc163
  · exact syracuse_descends_range_1486063_1488063 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1490065 with hc164 | hc164
  · exact syracuse_descends_range_1488064_1490064 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1492066 with hc165 | hc165
  · exact syracuse_descends_range_1490065_1492065 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1494067 with hc166 | hc166
  · exact syracuse_descends_range_1492066_1494066 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1496068 with hc167 | hc167
  · exact syracuse_descends_range_1494067_1496067 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1498069 with hc168 | hc168
  · exact syracuse_descends_range_1496068_1498068 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1500070 with hc169 | hc169
  · exact syracuse_descends_range_1498069_1500069 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1502071 with hc170 | hc170
  · exact syracuse_descends_range_1500070_1502070 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1503572 with hc171 | hc171
  · exact syracuse_descends_range_1502071_1503571 m (by omega) (by omega) hodd
  exact syracuse_descends_range_1503572_1505448 m (by omega) (by omega) hodd
