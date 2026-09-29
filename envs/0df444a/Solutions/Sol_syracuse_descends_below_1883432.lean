-- Prove2me | solution 1 for syracuse_descends_below_1883432
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:21:53.794289+00:00
-- url     : https://prove2.me/submissions/d45d2964-290b-41c9-a606-96ff09c6d850

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_1505449
import Theorems.Thm_syracuse_descends_range_1505449_1506949
import Theorems.Thm_syracuse_descends_range_1506950_1508950
import Theorems.Thm_syracuse_descends_range_1508951_1510951
import Theorems.Thm_syracuse_descends_range_1510952_1512952
import Theorems.Thm_syracuse_descends_range_1512953_1514953
import Theorems.Thm_syracuse_descends_range_1514954_1516954
import Theorems.Thm_syracuse_descends_range_1516955_1518455
import Theorems.Thm_syracuse_descends_range_1518456_1520456
import Theorems.Thm_syracuse_descends_range_1520457_1522457
import Theorems.Thm_syracuse_descends_range_1522458_1524458
import Theorems.Thm_syracuse_descends_range_1524459_1526459
import Theorems.Thm_syracuse_descends_range_1526460_1528460
import Theorems.Thm_syracuse_descends_range_1528461_1530461
import Theorems.Thm_syracuse_descends_range_1530462_1532462
import Theorems.Thm_syracuse_descends_range_1532463_1534463
import Theorems.Thm_syracuse_descends_range_1534464_1536464
import Theorems.Thm_syracuse_descends_range_1536465_1538465
import Theorems.Thm_syracuse_descends_range_1538466_1539966
import Theorems.Thm_syracuse_descends_range_1539967_1541467
import Theorems.Thm_syracuse_descends_range_1541468_1543468
import Theorems.Thm_syracuse_descends_range_1543469_1545469
import Theorems.Thm_syracuse_descends_range_1545470_1547470
import Theorems.Thm_syracuse_descends_range_1547471_1549471
import Theorems.Thm_syracuse_descends_range_1549472_1551472
import Theorems.Thm_syracuse_descends_range_1551473_1553473
import Theorems.Thm_syracuse_descends_range_1553474_1555474
import Theorems.Thm_syracuse_descends_range_1555475_1557475
import Theorems.Thm_syracuse_descends_range_1557476_1559476
import Theorems.Thm_syracuse_descends_range_1559477_1561477
import Theorems.Thm_syracuse_descends_range_1561478_1563478
import Theorems.Thm_syracuse_descends_range_1563479_1564979
import Theorems.Thm_syracuse_descends_range_1564980_1566980
import Theorems.Thm_syracuse_descends_range_1566981_1568981
import Theorems.Thm_syracuse_descends_range_1568982_1570982
import Theorems.Thm_syracuse_descends_range_1570983_1572483
import Theorems.Thm_syracuse_descends_range_1572484_1574484
import Theorems.Thm_syracuse_descends_range_1574485_1576485
import Theorems.Thm_syracuse_descends_range_1576486_1578486
import Theorems.Thm_syracuse_descends_range_1578487_1580487
import Theorems.Thm_syracuse_descends_range_1580488_1582488
import Theorems.Thm_syracuse_descends_range_1582489_1583989
import Theorems.Thm_syracuse_descends_range_1583990_1585490
import Theorems.Thm_syracuse_descends_range_1585491_1587491
import Theorems.Thm_syracuse_descends_range_1587492_1589492
import Theorems.Thm_syracuse_descends_range_1589493_1590993
import Theorems.Thm_syracuse_descends_range_1590994_1592994
import Theorems.Thm_syracuse_descends_range_1592995_1594995
import Theorems.Thm_syracuse_descends_range_1594996_1596996
import Theorems.Thm_syracuse_descends_range_1596997_1598997
import Theorems.Thm_syracuse_descends_range_1598998_1600998
import Theorems.Thm_syracuse_descends_range_1600999_1602999
import Theorems.Thm_syracuse_descends_range_1603000_1605000
import Theorems.Thm_syracuse_descends_range_1605001_1607001
import Theorems.Thm_syracuse_descends_range_1607002_1609002
import Theorems.Thm_syracuse_descends_range_1609003_1611003
import Theorems.Thm_syracuse_descends_range_1611004_1613004
import Theorems.Thm_syracuse_descends_range_1613005_1615005
import Theorems.Thm_syracuse_descends_range_1615006_1617006
import Theorems.Thm_syracuse_descends_range_1617007_1619007
import Theorems.Thm_syracuse_descends_range_1619008_1621008
import Theorems.Thm_syracuse_descends_range_1621009_1623009
import Theorems.Thm_syracuse_descends_range_1623010_1624510
import Theorems.Thm_syracuse_descends_range_1624511_1626511
import Theorems.Thm_syracuse_descends_range_1626512_1628512
import Theorems.Thm_syracuse_descends_range_1628513_1630513
import Theorems.Thm_syracuse_descends_range_1630514_1632514
import Theorems.Thm_syracuse_descends_range_1632515_1634015
import Theorems.Thm_syracuse_descends_range_1634016_1636016
import Theorems.Thm_syracuse_descends_range_1636017_1638017
import Theorems.Thm_syracuse_descends_range_1638018_1640018
import Theorems.Thm_syracuse_descends_range_1640019_1642019
import Theorems.Thm_syracuse_descends_range_1642020_1644020
import Theorems.Thm_syracuse_descends_range_1644021_1646021
import Theorems.Thm_syracuse_descends_range_1646022_1648022
import Theorems.Thm_syracuse_descends_range_1648023_1649523
import Theorems.Thm_syracuse_descends_range_1649524_1651524
import Theorems.Thm_syracuse_descends_range_1651525_1653525
import Theorems.Thm_syracuse_descends_range_1653526_1655526
import Theorems.Thm_syracuse_descends_range_1655527_1657527
import Theorems.Thm_syracuse_descends_range_1657528_1659528
import Theorems.Thm_syracuse_descends_range_1659529_1661529
import Theorems.Thm_syracuse_descends_range_1661530_1663030
import Theorems.Thm_syracuse_descends_range_1663031_1665031
import Theorems.Thm_syracuse_descends_range_1665032_1666532
import Theorems.Thm_syracuse_descends_range_1666533_1668033
import Theorems.Thm_syracuse_descends_range_1668034_1670034
import Theorems.Thm_syracuse_descends_range_1670035_1672035
import Theorems.Thm_syracuse_descends_range_1672036_1674036
import Theorems.Thm_syracuse_descends_range_1674037_1676037
import Theorems.Thm_syracuse_descends_range_1676038_1678038
import Theorems.Thm_syracuse_descends_range_1678039_1680039
import Theorems.Thm_syracuse_descends_range_1680040_1682040
import Theorems.Thm_syracuse_descends_range_1682041_1684041
import Theorems.Thm_syracuse_descends_range_1684042_1686042
import Theorems.Thm_syracuse_descends_range_1686043_1688043
import Theorems.Thm_syracuse_descends_range_1688044_1690044
import Theorems.Thm_syracuse_descends_range_1690045_1691545
import Theorems.Thm_syracuse_descends_range_1691546_1693546
import Theorems.Thm_syracuse_descends_range_1693547_1695547
import Theorems.Thm_syracuse_descends_range_1695548_1697548
import Theorems.Thm_syracuse_descends_range_1697549_1699549
import Theorems.Thm_syracuse_descends_range_1699550_1701550
import Theorems.Thm_syracuse_descends_range_1701551_1703551
import Theorems.Thm_syracuse_descends_range_1703552_1705052
import Theorems.Thm_syracuse_descends_range_1705053_1707053
import Theorems.Thm_syracuse_descends_range_1707054_1709054
import Theorems.Thm_syracuse_descends_range_1709055_1711055
import Theorems.Thm_syracuse_descends_range_1711056_1713056
import Theorems.Thm_syracuse_descends_range_1713057_1715057
import Theorems.Thm_syracuse_descends_range_1715058_1717058
import Theorems.Thm_syracuse_descends_range_1717059_1719059
import Theorems.Thm_syracuse_descends_range_1719060_1721060
import Theorems.Thm_syracuse_descends_range_1721061_1723061
import Theorems.Thm_syracuse_descends_range_1723062_1725062
import Theorems.Thm_syracuse_descends_range_1725063_1727063
import Theorems.Thm_syracuse_descends_range_1727064_1729064
import Theorems.Thm_syracuse_descends_range_1729065_1731065
import Theorems.Thm_syracuse_descends_range_1731066_1733066
import Theorems.Thm_syracuse_descends_range_1733067_1735067
import Theorems.Thm_syracuse_descends_range_1735068_1736568
import Theorems.Thm_syracuse_descends_range_1736569_1738569
import Theorems.Thm_syracuse_descends_range_1738570_1740570
import Theorems.Thm_syracuse_descends_range_1740571_1742571
import Theorems.Thm_syracuse_descends_range_1742572_1744572
import Theorems.Thm_syracuse_descends_range_1744573_1746573
import Theorems.Thm_syracuse_descends_range_1746574_1748574
import Theorems.Thm_syracuse_descends_range_1748575_1750575
import Theorems.Thm_syracuse_descends_range_1750576_1752576
import Theorems.Thm_syracuse_descends_range_1752577_1754577
import Theorems.Thm_syracuse_descends_range_1754578_1756578
import Theorems.Thm_syracuse_descends_range_1756579_1758079
import Theorems.Thm_syracuse_descends_range_1758080_1760080
import Theorems.Thm_syracuse_descends_range_1760081_1762081
import Theorems.Thm_syracuse_descends_range_1762082_1764082
import Theorems.Thm_syracuse_descends_range_1764083_1766083
import Theorems.Thm_syracuse_descends_range_1766084_1768084
import Theorems.Thm_syracuse_descends_range_1768085_1770085
import Theorems.Thm_syracuse_descends_range_1770086_1772086
import Theorems.Thm_syracuse_descends_range_1772087_1774087
import Theorems.Thm_syracuse_descends_range_1774088_1776088
import Theorems.Thm_syracuse_descends_range_1776089_1778089
import Theorems.Thm_syracuse_descends_range_1778090_1780090
import Theorems.Thm_syracuse_descends_range_1780091_1782091
import Theorems.Thm_syracuse_descends_range_1782092_1784092
import Theorems.Thm_syracuse_descends_range_1784093_1786093
import Theorems.Thm_syracuse_descends_range_1786094_1788094
import Theorems.Thm_syracuse_descends_range_1788095_1790095
import Theorems.Thm_syracuse_descends_range_1790096_1792096
import Theorems.Thm_syracuse_descends_range_1792097_1794097
import Theorems.Thm_syracuse_descends_range_1794098_1796098
import Theorems.Thm_syracuse_descends_range_1796099_1798099
import Theorems.Thm_syracuse_descends_range_1798100_1800100
import Theorems.Thm_syracuse_descends_range_1800101_1801601
import Theorems.Thm_syracuse_descends_range_1801602_1803602
import Theorems.Thm_syracuse_descends_range_1803603_1805603
import Theorems.Thm_syracuse_descends_range_1805604_1807604
import Theorems.Thm_syracuse_descends_range_1807605_1809605
import Theorems.Thm_syracuse_descends_range_1809606_1811606
import Theorems.Thm_syracuse_descends_range_1811607_1813607
import Theorems.Thm_syracuse_descends_range_1813608_1815608
import Theorems.Thm_syracuse_descends_range_1815609_1817609
import Theorems.Thm_syracuse_descends_range_1817610_1819610
import Theorems.Thm_syracuse_descends_range_1819611_1821611
import Theorems.Thm_syracuse_descends_range_1821612_1823612
import Theorems.Thm_syracuse_descends_range_1823613_1825613
import Theorems.Thm_syracuse_descends_range_1825614_1827614
import Theorems.Thm_syracuse_descends_range_1827615_1829615
import Theorems.Thm_syracuse_descends_range_1829616_1831616
import Theorems.Thm_syracuse_descends_range_1831617_1833617
import Theorems.Thm_syracuse_descends_range_1833618_1835618
import Theorems.Thm_syracuse_descends_range_1835619_1837619
import Theorems.Thm_syracuse_descends_range_1837620_1839620
import Theorems.Thm_syracuse_descends_range_1839621_1841621
import Theorems.Thm_syracuse_descends_range_1841622_1843622
import Theorems.Thm_syracuse_descends_range_1843623_1845623
import Theorems.Thm_syracuse_descends_range_1845624_1847624
import Theorems.Thm_syracuse_descends_range_1847625_1849625
import Theorems.Thm_syracuse_descends_range_1849626_1851626
import Theorems.Thm_syracuse_descends_range_1851627_1853627
import Theorems.Thm_syracuse_descends_range_1853628_1855628
import Theorems.Thm_syracuse_descends_range_1855629_1857629
import Theorems.Thm_syracuse_descends_range_1857630_1859630
import Theorems.Thm_syracuse_descends_range_1859631_1861631
import Theorems.Thm_syracuse_descends_range_1861632_1863632
import Theorems.Thm_syracuse_descends_range_1863633_1865633
import Theorems.Thm_syracuse_descends_range_1865634_1867634
import Theorems.Thm_syracuse_descends_range_1867635_1869635
import Theorems.Thm_syracuse_descends_range_1869636_1871636
import Theorems.Thm_syracuse_descends_range_1871637_1873637
import Theorems.Thm_syracuse_descends_range_1873638_1875638
import Theorems.Thm_syracuse_descends_range_1875639_1877139
import Theorems.Thm_syracuse_descends_range_1877140_1879140
import Theorems.Thm_syracuse_descends_range_1879141_1881141
import Theorems.Thm_syracuse_descends_range_1881142_1883142
import Theorems.Thm_syracuse_descends_range_1883143_1883431

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 1883432) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 1505449 with hb | hb
  · exact syracuse_descends_below_1505449 m h1 hb hodd
  rcases Nat.lt_or_ge m 1506950 with hc0 | hc0
  · exact syracuse_descends_range_1505449_1506949 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1508951 with hc1 | hc1
  · exact syracuse_descends_range_1506950_1508950 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1510952 with hc2 | hc2
  · exact syracuse_descends_range_1508951_1510951 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1512953 with hc3 | hc3
  · exact syracuse_descends_range_1510952_1512952 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1514954 with hc4 | hc4
  · exact syracuse_descends_range_1512953_1514953 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1516955 with hc5 | hc5
  · exact syracuse_descends_range_1514954_1516954 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1518456 with hc6 | hc6
  · exact syracuse_descends_range_1516955_1518455 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1520457 with hc7 | hc7
  · exact syracuse_descends_range_1518456_1520456 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1522458 with hc8 | hc8
  · exact syracuse_descends_range_1520457_1522457 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1524459 with hc9 | hc9
  · exact syracuse_descends_range_1522458_1524458 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1526460 with hc10 | hc10
  · exact syracuse_descends_range_1524459_1526459 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1528461 with hc11 | hc11
  · exact syracuse_descends_range_1526460_1528460 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1530462 with hc12 | hc12
  · exact syracuse_descends_range_1528461_1530461 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1532463 with hc13 | hc13
  · exact syracuse_descends_range_1530462_1532462 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1534464 with hc14 | hc14
  · exact syracuse_descends_range_1532463_1534463 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1536465 with hc15 | hc15
  · exact syracuse_descends_range_1534464_1536464 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1538466 with hc16 | hc16
  · exact syracuse_descends_range_1536465_1538465 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1539967 with hc17 | hc17
  · exact syracuse_descends_range_1538466_1539966 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1541468 with hc18 | hc18
  · exact syracuse_descends_range_1539967_1541467 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1543469 with hc19 | hc19
  · exact syracuse_descends_range_1541468_1543468 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1545470 with hc20 | hc20
  · exact syracuse_descends_range_1543469_1545469 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1547471 with hc21 | hc21
  · exact syracuse_descends_range_1545470_1547470 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1549472 with hc22 | hc22
  · exact syracuse_descends_range_1547471_1549471 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1551473 with hc23 | hc23
  · exact syracuse_descends_range_1549472_1551472 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1553474 with hc24 | hc24
  · exact syracuse_descends_range_1551473_1553473 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1555475 with hc25 | hc25
  · exact syracuse_descends_range_1553474_1555474 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1557476 with hc26 | hc26
  · exact syracuse_descends_range_1555475_1557475 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1559477 with hc27 | hc27
  · exact syracuse_descends_range_1557476_1559476 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1561478 with hc28 | hc28
  · exact syracuse_descends_range_1559477_1561477 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1563479 with hc29 | hc29
  · exact syracuse_descends_range_1561478_1563478 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1564980 with hc30 | hc30
  · exact syracuse_descends_range_1563479_1564979 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1566981 with hc31 | hc31
  · exact syracuse_descends_range_1564980_1566980 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1568982 with hc32 | hc32
  · exact syracuse_descends_range_1566981_1568981 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1570983 with hc33 | hc33
  · exact syracuse_descends_range_1568982_1570982 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1572484 with hc34 | hc34
  · exact syracuse_descends_range_1570983_1572483 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1574485 with hc35 | hc35
  · exact syracuse_descends_range_1572484_1574484 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1576486 with hc36 | hc36
  · exact syracuse_descends_range_1574485_1576485 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1578487 with hc37 | hc37
  · exact syracuse_descends_range_1576486_1578486 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1580488 with hc38 | hc38
  · exact syracuse_descends_range_1578487_1580487 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1582489 with hc39 | hc39
  · exact syracuse_descends_range_1580488_1582488 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1583990 with hc40 | hc40
  · exact syracuse_descends_range_1582489_1583989 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1585491 with hc41 | hc41
  · exact syracuse_descends_range_1583990_1585490 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1587492 with hc42 | hc42
  · exact syracuse_descends_range_1585491_1587491 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1589493 with hc43 | hc43
  · exact syracuse_descends_range_1587492_1589492 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1590994 with hc44 | hc44
  · exact syracuse_descends_range_1589493_1590993 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1592995 with hc45 | hc45
  · exact syracuse_descends_range_1590994_1592994 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1594996 with hc46 | hc46
  · exact syracuse_descends_range_1592995_1594995 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1596997 with hc47 | hc47
  · exact syracuse_descends_range_1594996_1596996 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1598998 with hc48 | hc48
  · exact syracuse_descends_range_1596997_1598997 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1600999 with hc49 | hc49
  · exact syracuse_descends_range_1598998_1600998 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1603000 with hc50 | hc50
  · exact syracuse_descends_range_1600999_1602999 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1605001 with hc51 | hc51
  · exact syracuse_descends_range_1603000_1605000 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1607002 with hc52 | hc52
  · exact syracuse_descends_range_1605001_1607001 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1609003 with hc53 | hc53
  · exact syracuse_descends_range_1607002_1609002 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1611004 with hc54 | hc54
  · exact syracuse_descends_range_1609003_1611003 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1613005 with hc55 | hc55
  · exact syracuse_descends_range_1611004_1613004 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1615006 with hc56 | hc56
  · exact syracuse_descends_range_1613005_1615005 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1617007 with hc57 | hc57
  · exact syracuse_descends_range_1615006_1617006 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1619008 with hc58 | hc58
  · exact syracuse_descends_range_1617007_1619007 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1621009 with hc59 | hc59
  · exact syracuse_descends_range_1619008_1621008 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1623010 with hc60 | hc60
  · exact syracuse_descends_range_1621009_1623009 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1624511 with hc61 | hc61
  · exact syracuse_descends_range_1623010_1624510 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1626512 with hc62 | hc62
  · exact syracuse_descends_range_1624511_1626511 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1628513 with hc63 | hc63
  · exact syracuse_descends_range_1626512_1628512 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1630514 with hc64 | hc64
  · exact syracuse_descends_range_1628513_1630513 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1632515 with hc65 | hc65
  · exact syracuse_descends_range_1630514_1632514 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1634016 with hc66 | hc66
  · exact syracuse_descends_range_1632515_1634015 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1636017 with hc67 | hc67
  · exact syracuse_descends_range_1634016_1636016 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1638018 with hc68 | hc68
  · exact syracuse_descends_range_1636017_1638017 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1640019 with hc69 | hc69
  · exact syracuse_descends_range_1638018_1640018 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1642020 with hc70 | hc70
  · exact syracuse_descends_range_1640019_1642019 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1644021 with hc71 | hc71
  · exact syracuse_descends_range_1642020_1644020 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1646022 with hc72 | hc72
  · exact syracuse_descends_range_1644021_1646021 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1648023 with hc73 | hc73
  · exact syracuse_descends_range_1646022_1648022 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1649524 with hc74 | hc74
  · exact syracuse_descends_range_1648023_1649523 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1651525 with hc75 | hc75
  · exact syracuse_descends_range_1649524_1651524 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1653526 with hc76 | hc76
  · exact syracuse_descends_range_1651525_1653525 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1655527 with hc77 | hc77
  · exact syracuse_descends_range_1653526_1655526 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1657528 with hc78 | hc78
  · exact syracuse_descends_range_1655527_1657527 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1659529 with hc79 | hc79
  · exact syracuse_descends_range_1657528_1659528 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1661530 with hc80 | hc80
  · exact syracuse_descends_range_1659529_1661529 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1663031 with hc81 | hc81
  · exact syracuse_descends_range_1661530_1663030 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1665032 with hc82 | hc82
  · exact syracuse_descends_range_1663031_1665031 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1666533 with hc83 | hc83
  · exact syracuse_descends_range_1665032_1666532 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1668034 with hc84 | hc84
  · exact syracuse_descends_range_1666533_1668033 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1670035 with hc85 | hc85
  · exact syracuse_descends_range_1668034_1670034 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1672036 with hc86 | hc86
  · exact syracuse_descends_range_1670035_1672035 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1674037 with hc87 | hc87
  · exact syracuse_descends_range_1672036_1674036 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1676038 with hc88 | hc88
  · exact syracuse_descends_range_1674037_1676037 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1678039 with hc89 | hc89
  · exact syracuse_descends_range_1676038_1678038 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1680040 with hc90 | hc90
  · exact syracuse_descends_range_1678039_1680039 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1682041 with hc91 | hc91
  · exact syracuse_descends_range_1680040_1682040 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1684042 with hc92 | hc92
  · exact syracuse_descends_range_1682041_1684041 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1686043 with hc93 | hc93
  · exact syracuse_descends_range_1684042_1686042 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1688044 with hc94 | hc94
  · exact syracuse_descends_range_1686043_1688043 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1690045 with hc95 | hc95
  · exact syracuse_descends_range_1688044_1690044 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1691546 with hc96 | hc96
  · exact syracuse_descends_range_1690045_1691545 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1693547 with hc97 | hc97
  · exact syracuse_descends_range_1691546_1693546 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1695548 with hc98 | hc98
  · exact syracuse_descends_range_1693547_1695547 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1697549 with hc99 | hc99
  · exact syracuse_descends_range_1695548_1697548 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1699550 with hc100 | hc100
  · exact syracuse_descends_range_1697549_1699549 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1701551 with hc101 | hc101
  · exact syracuse_descends_range_1699550_1701550 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1703552 with hc102 | hc102
  · exact syracuse_descends_range_1701551_1703551 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1705053 with hc103 | hc103
  · exact syracuse_descends_range_1703552_1705052 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1707054 with hc104 | hc104
  · exact syracuse_descends_range_1705053_1707053 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1709055 with hc105 | hc105
  · exact syracuse_descends_range_1707054_1709054 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1711056 with hc106 | hc106
  · exact syracuse_descends_range_1709055_1711055 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1713057 with hc107 | hc107
  · exact syracuse_descends_range_1711056_1713056 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1715058 with hc108 | hc108
  · exact syracuse_descends_range_1713057_1715057 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1717059 with hc109 | hc109
  · exact syracuse_descends_range_1715058_1717058 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1719060 with hc110 | hc110
  · exact syracuse_descends_range_1717059_1719059 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1721061 with hc111 | hc111
  · exact syracuse_descends_range_1719060_1721060 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1723062 with hc112 | hc112
  · exact syracuse_descends_range_1721061_1723061 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1725063 with hc113 | hc113
  · exact syracuse_descends_range_1723062_1725062 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1727064 with hc114 | hc114
  · exact syracuse_descends_range_1725063_1727063 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1729065 with hc115 | hc115
  · exact syracuse_descends_range_1727064_1729064 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1731066 with hc116 | hc116
  · exact syracuse_descends_range_1729065_1731065 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1733067 with hc117 | hc117
  · exact syracuse_descends_range_1731066_1733066 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1735068 with hc118 | hc118
  · exact syracuse_descends_range_1733067_1735067 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1736569 with hc119 | hc119
  · exact syracuse_descends_range_1735068_1736568 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1738570 with hc120 | hc120
  · exact syracuse_descends_range_1736569_1738569 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1740571 with hc121 | hc121
  · exact syracuse_descends_range_1738570_1740570 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1742572 with hc122 | hc122
  · exact syracuse_descends_range_1740571_1742571 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1744573 with hc123 | hc123
  · exact syracuse_descends_range_1742572_1744572 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1746574 with hc124 | hc124
  · exact syracuse_descends_range_1744573_1746573 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1748575 with hc125 | hc125
  · exact syracuse_descends_range_1746574_1748574 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1750576 with hc126 | hc126
  · exact syracuse_descends_range_1748575_1750575 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1752577 with hc127 | hc127
  · exact syracuse_descends_range_1750576_1752576 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1754578 with hc128 | hc128
  · exact syracuse_descends_range_1752577_1754577 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1756579 with hc129 | hc129
  · exact syracuse_descends_range_1754578_1756578 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1758080 with hc130 | hc130
  · exact syracuse_descends_range_1756579_1758079 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1760081 with hc131 | hc131
  · exact syracuse_descends_range_1758080_1760080 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1762082 with hc132 | hc132
  · exact syracuse_descends_range_1760081_1762081 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1764083 with hc133 | hc133
  · exact syracuse_descends_range_1762082_1764082 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1766084 with hc134 | hc134
  · exact syracuse_descends_range_1764083_1766083 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1768085 with hc135 | hc135
  · exact syracuse_descends_range_1766084_1768084 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1770086 with hc136 | hc136
  · exact syracuse_descends_range_1768085_1770085 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1772087 with hc137 | hc137
  · exact syracuse_descends_range_1770086_1772086 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1774088 with hc138 | hc138
  · exact syracuse_descends_range_1772087_1774087 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1776089 with hc139 | hc139
  · exact syracuse_descends_range_1774088_1776088 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1778090 with hc140 | hc140
  · exact syracuse_descends_range_1776089_1778089 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1780091 with hc141 | hc141
  · exact syracuse_descends_range_1778090_1780090 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1782092 with hc142 | hc142
  · exact syracuse_descends_range_1780091_1782091 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1784093 with hc143 | hc143
  · exact syracuse_descends_range_1782092_1784092 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1786094 with hc144 | hc144
  · exact syracuse_descends_range_1784093_1786093 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1788095 with hc145 | hc145
  · exact syracuse_descends_range_1786094_1788094 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1790096 with hc146 | hc146
  · exact syracuse_descends_range_1788095_1790095 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1792097 with hc147 | hc147
  · exact syracuse_descends_range_1790096_1792096 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1794098 with hc148 | hc148
  · exact syracuse_descends_range_1792097_1794097 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1796099 with hc149 | hc149
  · exact syracuse_descends_range_1794098_1796098 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1798100 with hc150 | hc150
  · exact syracuse_descends_range_1796099_1798099 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1800101 with hc151 | hc151
  · exact syracuse_descends_range_1798100_1800100 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1801602 with hc152 | hc152
  · exact syracuse_descends_range_1800101_1801601 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1803603 with hc153 | hc153
  · exact syracuse_descends_range_1801602_1803602 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1805604 with hc154 | hc154
  · exact syracuse_descends_range_1803603_1805603 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1807605 with hc155 | hc155
  · exact syracuse_descends_range_1805604_1807604 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1809606 with hc156 | hc156
  · exact syracuse_descends_range_1807605_1809605 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1811607 with hc157 | hc157
  · exact syracuse_descends_range_1809606_1811606 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1813608 with hc158 | hc158
  · exact syracuse_descends_range_1811607_1813607 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1815609 with hc159 | hc159
  · exact syracuse_descends_range_1813608_1815608 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1817610 with hc160 | hc160
  · exact syracuse_descends_range_1815609_1817609 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1819611 with hc161 | hc161
  · exact syracuse_descends_range_1817610_1819610 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1821612 with hc162 | hc162
  · exact syracuse_descends_range_1819611_1821611 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1823613 with hc163 | hc163
  · exact syracuse_descends_range_1821612_1823612 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1825614 with hc164 | hc164
  · exact syracuse_descends_range_1823613_1825613 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1827615 with hc165 | hc165
  · exact syracuse_descends_range_1825614_1827614 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1829616 with hc166 | hc166
  · exact syracuse_descends_range_1827615_1829615 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1831617 with hc167 | hc167
  · exact syracuse_descends_range_1829616_1831616 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1833618 with hc168 | hc168
  · exact syracuse_descends_range_1831617_1833617 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1835619 with hc169 | hc169
  · exact syracuse_descends_range_1833618_1835618 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1837620 with hc170 | hc170
  · exact syracuse_descends_range_1835619_1837619 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1839621 with hc171 | hc171
  · exact syracuse_descends_range_1837620_1839620 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1841622 with hc172 | hc172
  · exact syracuse_descends_range_1839621_1841621 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1843623 with hc173 | hc173
  · exact syracuse_descends_range_1841622_1843622 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1845624 with hc174 | hc174
  · exact syracuse_descends_range_1843623_1845623 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1847625 with hc175 | hc175
  · exact syracuse_descends_range_1845624_1847624 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1849626 with hc176 | hc176
  · exact syracuse_descends_range_1847625_1849625 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1851627 with hc177 | hc177
  · exact syracuse_descends_range_1849626_1851626 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1853628 with hc178 | hc178
  · exact syracuse_descends_range_1851627_1853627 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1855629 with hc179 | hc179
  · exact syracuse_descends_range_1853628_1855628 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1857630 with hc180 | hc180
  · exact syracuse_descends_range_1855629_1857629 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1859631 with hc181 | hc181
  · exact syracuse_descends_range_1857630_1859630 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1861632 with hc182 | hc182
  · exact syracuse_descends_range_1859631_1861631 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1863633 with hc183 | hc183
  · exact syracuse_descends_range_1861632_1863632 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1865634 with hc184 | hc184
  · exact syracuse_descends_range_1863633_1865633 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1867635 with hc185 | hc185
  · exact syracuse_descends_range_1865634_1867634 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1869636 with hc186 | hc186
  · exact syracuse_descends_range_1867635_1869635 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1871637 with hc187 | hc187
  · exact syracuse_descends_range_1869636_1871636 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1873638 with hc188 | hc188
  · exact syracuse_descends_range_1871637_1873637 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1875639 with hc189 | hc189
  · exact syracuse_descends_range_1873638_1875638 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1877140 with hc190 | hc190
  · exact syracuse_descends_range_1875639_1877139 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1879141 with hc191 | hc191
  · exact syracuse_descends_range_1877140_1879140 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1881142 with hc192 | hc192
  · exact syracuse_descends_range_1879141_1881141 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1883143 with hc193 | hc193
  · exact syracuse_descends_range_1881142_1883142 m (by omega) (by omega) hodd
  exact syracuse_descends_range_1883143_1883431 m (by omega) (by omega) hodd
