-- Prove2me | solution 1 for syracuse_descends_below_1166400
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:30:48.145859+00:00
-- url     : https://prove2.me/submissions/74a80c79-ac53-40f3-8c7d-33301614f752

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_860564
import Theorems.Thm_syracuse_descends_range_860564_864564
import Theorems.Thm_syracuse_descends_range_864565_868565
import Theorems.Thm_syracuse_descends_range_868566_872566
import Theorems.Thm_syracuse_descends_range_872567_876567
import Theorems.Thm_syracuse_descends_range_876568_880568
import Theorems.Thm_syracuse_descends_range_880569_884569
import Theorems.Thm_syracuse_descends_range_884570_888570
import Theorems.Thm_syracuse_descends_range_888571_892571
import Theorems.Thm_syracuse_descends_range_892572_896572
import Theorems.Thm_syracuse_descends_range_896573_900573
import Theorems.Thm_syracuse_descends_range_900574_904574
import Theorems.Thm_syracuse_descends_range_904575_908575
import Theorems.Thm_syracuse_descends_range_908576_912576
import Theorems.Thm_syracuse_descends_range_912577_916577
import Theorems.Thm_syracuse_descends_range_916578_920578
import Theorems.Thm_syracuse_descends_range_920579_924579
import Theorems.Thm_syracuse_descends_range_924580_928580
import Theorems.Thm_syracuse_descends_range_928581_932581
import Theorems.Thm_syracuse_descends_range_932582_936582
import Theorems.Thm_syracuse_descends_range_936583_940583
import Theorems.Thm_syracuse_descends_range_940584_944584
import Theorems.Thm_syracuse_descends_range_944585_948585
import Theorems.Thm_syracuse_descends_range_948586_952586
import Theorems.Thm_syracuse_descends_range_952587_956587
import Theorems.Thm_syracuse_descends_range_956588_960588
import Theorems.Thm_syracuse_descends_range_960589_964589
import Theorems.Thm_syracuse_descends_range_964590_968590
import Theorems.Thm_syracuse_descends_range_968591_972591
import Theorems.Thm_syracuse_descends_range_972592_976592
import Theorems.Thm_syracuse_descends_range_976593_980593
import Theorems.Thm_syracuse_descends_range_980594_984594
import Theorems.Thm_syracuse_descends_range_984595_988595
import Theorems.Thm_syracuse_descends_range_988596_992596
import Theorems.Thm_syracuse_descends_range_992597_996597
import Theorems.Thm_syracuse_descends_range_996598_1000598
import Theorems.Thm_syracuse_descends_range_1000599_1004599
import Theorems.Thm_syracuse_descends_range_1004600_1008600
import Theorems.Thm_syracuse_descends_range_1008601_1012601
import Theorems.Thm_syracuse_descends_range_1012602_1016602
import Theorems.Thm_syracuse_descends_range_1016603_1020603
import Theorems.Thm_syracuse_descends_range_1020604_1024604
import Theorems.Thm_syracuse_descends_range_1024605_1028605
import Theorems.Thm_syracuse_descends_range_1028606_1032606
import Theorems.Thm_syracuse_descends_range_1032607_1036607
import Theorems.Thm_syracuse_descends_range_1036608_1040608
import Theorems.Thm_syracuse_descends_range_1040609_1044609
import Theorems.Thm_syracuse_descends_range_1044610_1048610
import Theorems.Thm_syracuse_descends_range_1048611_1052611
import Theorems.Thm_syracuse_descends_range_1052612_1056612
import Theorems.Thm_syracuse_descends_range_1056613_1060613
import Theorems.Thm_syracuse_descends_range_1060614_1064614
import Theorems.Thm_syracuse_descends_range_1064615_1068615
import Theorems.Thm_syracuse_descends_range_1068616_1072616
import Theorems.Thm_syracuse_descends_range_1072617_1076617
import Theorems.Thm_syracuse_descends_range_1076618_1080618
import Theorems.Thm_syracuse_descends_range_1080619_1084619
import Theorems.Thm_syracuse_descends_range_1084620_1088620
import Theorems.Thm_syracuse_descends_range_1088621_1092621
import Theorems.Thm_syracuse_descends_range_1092622_1096622
import Theorems.Thm_syracuse_descends_range_1096623_1100623
import Theorems.Thm_syracuse_descends_range_1100624_1104624
import Theorems.Thm_syracuse_descends_range_1104625_1108625
import Theorems.Thm_syracuse_descends_range_1108626_1112626
import Theorems.Thm_syracuse_descends_range_1112627_1116627
import Theorems.Thm_syracuse_descends_range_1116628_1120628
import Theorems.Thm_syracuse_descends_range_1120629_1124629
import Theorems.Thm_syracuse_descends_range_1124630_1128630
import Theorems.Thm_syracuse_descends_range_1128631_1132631
import Theorems.Thm_syracuse_descends_range_1132632_1136632
import Theorems.Thm_syracuse_descends_range_1136633_1140633
import Theorems.Thm_syracuse_descends_range_1140634_1144634
import Theorems.Thm_syracuse_descends_range_1144635_1148635
import Theorems.Thm_syracuse_descends_range_1148636_1152636
import Theorems.Thm_syracuse_descends_range_1152637_1156637
import Theorems.Thm_syracuse_descends_range_1156638_1160638
import Theorems.Thm_syracuse_descends_range_1160639_1164639
import Theorems.Thm_syracuse_descends_range_1164640_1166399

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 1166400) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 860564 with hb | hb
  · exact syracuse_descends_below_860564 m h1 hb hodd
  rcases Nat.lt_or_ge m 864565 with hc0 | hc0
  · exact syracuse_descends_range_860564_864564 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 868566 with hc1 | hc1
  · exact syracuse_descends_range_864565_868565 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 872567 with hc2 | hc2
  · exact syracuse_descends_range_868566_872566 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 876568 with hc3 | hc3
  · exact syracuse_descends_range_872567_876567 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 880569 with hc4 | hc4
  · exact syracuse_descends_range_876568_880568 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 884570 with hc5 | hc5
  · exact syracuse_descends_range_880569_884569 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 888571 with hc6 | hc6
  · exact syracuse_descends_range_884570_888570 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 892572 with hc7 | hc7
  · exact syracuse_descends_range_888571_892571 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 896573 with hc8 | hc8
  · exact syracuse_descends_range_892572_896572 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 900574 with hc9 | hc9
  · exact syracuse_descends_range_896573_900573 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 904575 with hc10 | hc10
  · exact syracuse_descends_range_900574_904574 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 908576 with hc11 | hc11
  · exact syracuse_descends_range_904575_908575 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 912577 with hc12 | hc12
  · exact syracuse_descends_range_908576_912576 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 916578 with hc13 | hc13
  · exact syracuse_descends_range_912577_916577 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 920579 with hc14 | hc14
  · exact syracuse_descends_range_916578_920578 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 924580 with hc15 | hc15
  · exact syracuse_descends_range_920579_924579 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 928581 with hc16 | hc16
  · exact syracuse_descends_range_924580_928580 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 932582 with hc17 | hc17
  · exact syracuse_descends_range_928581_932581 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 936583 with hc18 | hc18
  · exact syracuse_descends_range_932582_936582 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 940584 with hc19 | hc19
  · exact syracuse_descends_range_936583_940583 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 944585 with hc20 | hc20
  · exact syracuse_descends_range_940584_944584 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 948586 with hc21 | hc21
  · exact syracuse_descends_range_944585_948585 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 952587 with hc22 | hc22
  · exact syracuse_descends_range_948586_952586 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 956588 with hc23 | hc23
  · exact syracuse_descends_range_952587_956587 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 960589 with hc24 | hc24
  · exact syracuse_descends_range_956588_960588 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 964590 with hc25 | hc25
  · exact syracuse_descends_range_960589_964589 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 968591 with hc26 | hc26
  · exact syracuse_descends_range_964590_968590 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 972592 with hc27 | hc27
  · exact syracuse_descends_range_968591_972591 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 976593 with hc28 | hc28
  · exact syracuse_descends_range_972592_976592 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 980594 with hc29 | hc29
  · exact syracuse_descends_range_976593_980593 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 984595 with hc30 | hc30
  · exact syracuse_descends_range_980594_984594 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 988596 with hc31 | hc31
  · exact syracuse_descends_range_984595_988595 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 992597 with hc32 | hc32
  · exact syracuse_descends_range_988596_992596 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 996598 with hc33 | hc33
  · exact syracuse_descends_range_992597_996597 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1000599 with hc34 | hc34
  · exact syracuse_descends_range_996598_1000598 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1004600 with hc35 | hc35
  · exact syracuse_descends_range_1000599_1004599 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1008601 with hc36 | hc36
  · exact syracuse_descends_range_1004600_1008600 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1012602 with hc37 | hc37
  · exact syracuse_descends_range_1008601_1012601 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1016603 with hc38 | hc38
  · exact syracuse_descends_range_1012602_1016602 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1020604 with hc39 | hc39
  · exact syracuse_descends_range_1016603_1020603 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1024605 with hc40 | hc40
  · exact syracuse_descends_range_1020604_1024604 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1028606 with hc41 | hc41
  · exact syracuse_descends_range_1024605_1028605 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1032607 with hc42 | hc42
  · exact syracuse_descends_range_1028606_1032606 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1036608 with hc43 | hc43
  · exact syracuse_descends_range_1032607_1036607 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1040609 with hc44 | hc44
  · exact syracuse_descends_range_1036608_1040608 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1044610 with hc45 | hc45
  · exact syracuse_descends_range_1040609_1044609 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1048611 with hc46 | hc46
  · exact syracuse_descends_range_1044610_1048610 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1052612 with hc47 | hc47
  · exact syracuse_descends_range_1048611_1052611 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1056613 with hc48 | hc48
  · exact syracuse_descends_range_1052612_1056612 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1060614 with hc49 | hc49
  · exact syracuse_descends_range_1056613_1060613 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1064615 with hc50 | hc50
  · exact syracuse_descends_range_1060614_1064614 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1068616 with hc51 | hc51
  · exact syracuse_descends_range_1064615_1068615 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1072617 with hc52 | hc52
  · exact syracuse_descends_range_1068616_1072616 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1076618 with hc53 | hc53
  · exact syracuse_descends_range_1072617_1076617 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1080619 with hc54 | hc54
  · exact syracuse_descends_range_1076618_1080618 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1084620 with hc55 | hc55
  · exact syracuse_descends_range_1080619_1084619 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1088621 with hc56 | hc56
  · exact syracuse_descends_range_1084620_1088620 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1092622 with hc57 | hc57
  · exact syracuse_descends_range_1088621_1092621 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1096623 with hc58 | hc58
  · exact syracuse_descends_range_1092622_1096622 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1100624 with hc59 | hc59
  · exact syracuse_descends_range_1096623_1100623 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1104625 with hc60 | hc60
  · exact syracuse_descends_range_1100624_1104624 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1108626 with hc61 | hc61
  · exact syracuse_descends_range_1104625_1108625 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1112627 with hc62 | hc62
  · exact syracuse_descends_range_1108626_1112626 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1116628 with hc63 | hc63
  · exact syracuse_descends_range_1112627_1116627 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1120629 with hc64 | hc64
  · exact syracuse_descends_range_1116628_1120628 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1124630 with hc65 | hc65
  · exact syracuse_descends_range_1120629_1124629 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1128631 with hc66 | hc66
  · exact syracuse_descends_range_1124630_1128630 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1132632 with hc67 | hc67
  · exact syracuse_descends_range_1128631_1132631 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1136633 with hc68 | hc68
  · exact syracuse_descends_range_1132632_1136632 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1140634 with hc69 | hc69
  · exact syracuse_descends_range_1136633_1140633 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1144635 with hc70 | hc70
  · exact syracuse_descends_range_1140634_1144634 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1148636 with hc71 | hc71
  · exact syracuse_descends_range_1144635_1148635 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1152637 with hc72 | hc72
  · exact syracuse_descends_range_1148636_1152636 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1156638 with hc73 | hc73
  · exact syracuse_descends_range_1152637_1156637 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1160639 with hc74 | hc74
  · exact syracuse_descends_range_1156638_1160638 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1164640 with hc75 | hc75
  · exact syracuse_descends_range_1160639_1164639 m (by omega) (by omega) hodd
  exact syracuse_descends_range_1164640_1166399 m (by omega) (by omega) hodd
