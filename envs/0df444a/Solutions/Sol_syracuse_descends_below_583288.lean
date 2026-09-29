-- Prove2me | solution 1 for syracuse_descends_below_583288
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:35:28.344222+00:00
-- url     : https://prove2.me/submissions/f8c22a81-770b-4b33-a434-e400f8a95c77

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_330750
import Theorems.Thm_syracuse_descends_range_330750_334750
import Theorems.Thm_syracuse_descends_range_334751_338751
import Theorems.Thm_syracuse_descends_range_338752_342752
import Theorems.Thm_syracuse_descends_range_342753_346753
import Theorems.Thm_syracuse_descends_range_346754_350754
import Theorems.Thm_syracuse_descends_range_350755_354755
import Theorems.Thm_syracuse_descends_range_354756_358756
import Theorems.Thm_syracuse_descends_range_358757_362757
import Theorems.Thm_syracuse_descends_range_362758_366758
import Theorems.Thm_syracuse_descends_range_366759_370759
import Theorems.Thm_syracuse_descends_range_370760_374760
import Theorems.Thm_syracuse_descends_range_374761_377761
import Theorems.Thm_syracuse_descends_range_377762_381762
import Theorems.Thm_syracuse_descends_range_381763_385763
import Theorems.Thm_syracuse_descends_range_385764_389764
import Theorems.Thm_syracuse_descends_range_389765_393765
import Theorems.Thm_syracuse_descends_range_393766_397766
import Theorems.Thm_syracuse_descends_range_397767_401767
import Theorems.Thm_syracuse_descends_range_401768_405768
import Theorems.Thm_syracuse_descends_range_405769_409769
import Theorems.Thm_syracuse_descends_range_409770_413770
import Theorems.Thm_syracuse_descends_range_413771_417771
import Theorems.Thm_syracuse_descends_range_417772_421772
import Theorems.Thm_syracuse_descends_range_421773_424773
import Theorems.Thm_syracuse_descends_range_424774_428774
import Theorems.Thm_syracuse_descends_range_428775_432775
import Theorems.Thm_syracuse_descends_range_432776_435776
import Theorems.Thm_syracuse_descends_range_435777_439777
import Theorems.Thm_syracuse_descends_range_439778_443778
import Theorems.Thm_syracuse_descends_range_443779_447779
import Theorems.Thm_syracuse_descends_range_447780_451780
import Theorems.Thm_syracuse_descends_range_451781_455781
import Theorems.Thm_syracuse_descends_range_455782_459782
import Theorems.Thm_syracuse_descends_range_459783_463783
import Theorems.Thm_syracuse_descends_range_463784_467784
import Theorems.Thm_syracuse_descends_range_467785_471785
import Theorems.Thm_syracuse_descends_range_471786_475786
import Theorems.Thm_syracuse_descends_range_475787_479787
import Theorems.Thm_syracuse_descends_range_479788_483788
import Theorems.Thm_syracuse_descends_range_483789_487789
import Theorems.Thm_syracuse_descends_range_487790_491790
import Theorems.Thm_syracuse_descends_range_491791_495791
import Theorems.Thm_syracuse_descends_range_495792_499792
import Theorems.Thm_syracuse_descends_range_499793_503793
import Theorems.Thm_syracuse_descends_range_503794_507794
import Theorems.Thm_syracuse_descends_range_507795_511795
import Theorems.Thm_syracuse_descends_range_511796_515796
import Theorems.Thm_syracuse_descends_range_515797_519797
import Theorems.Thm_syracuse_descends_range_519798_523798
import Theorems.Thm_syracuse_descends_range_523799_527799
import Theorems.Thm_syracuse_descends_range_527800_531800
import Theorems.Thm_syracuse_descends_range_531801_535801
import Theorems.Thm_syracuse_descends_range_535802_539802
import Theorems.Thm_syracuse_descends_range_539803_542803
import Theorems.Thm_syracuse_descends_range_542804_546804
import Theorems.Thm_syracuse_descends_range_546805_550805
import Theorems.Thm_syracuse_descends_range_550806_554806
import Theorems.Thm_syracuse_descends_range_554807_558807
import Theorems.Thm_syracuse_descends_range_558808_562808
import Theorems.Thm_syracuse_descends_range_562809_566809
import Theorems.Thm_syracuse_descends_range_566810_570810
import Theorems.Thm_syracuse_descends_range_570811_574811
import Theorems.Thm_syracuse_descends_range_574812_578812
import Theorems.Thm_syracuse_descends_range_578813_582813
import Theorems.Thm_syracuse_descends_range_582814_583287

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 583288) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 330750 with hb | hb
  · exact syracuse_descends_below_330750 m h1 hb hodd
  rcases Nat.lt_or_ge m 334751 with hc0 | hc0
  · exact syracuse_descends_range_330750_334750 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 338752 with hc1 | hc1
  · exact syracuse_descends_range_334751_338751 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 342753 with hc2 | hc2
  · exact syracuse_descends_range_338752_342752 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 346754 with hc3 | hc3
  · exact syracuse_descends_range_342753_346753 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 350755 with hc4 | hc4
  · exact syracuse_descends_range_346754_350754 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 354756 with hc5 | hc5
  · exact syracuse_descends_range_350755_354755 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 358757 with hc6 | hc6
  · exact syracuse_descends_range_354756_358756 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 362758 with hc7 | hc7
  · exact syracuse_descends_range_358757_362757 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 366759 with hc8 | hc8
  · exact syracuse_descends_range_362758_366758 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 370760 with hc9 | hc9
  · exact syracuse_descends_range_366759_370759 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 374761 with hc10 | hc10
  · exact syracuse_descends_range_370760_374760 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 377762 with hc11 | hc11
  · exact syracuse_descends_range_374761_377761 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 381763 with hc12 | hc12
  · exact syracuse_descends_range_377762_381762 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 385764 with hc13 | hc13
  · exact syracuse_descends_range_381763_385763 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 389765 with hc14 | hc14
  · exact syracuse_descends_range_385764_389764 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 393766 with hc15 | hc15
  · exact syracuse_descends_range_389765_393765 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 397767 with hc16 | hc16
  · exact syracuse_descends_range_393766_397766 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 401768 with hc17 | hc17
  · exact syracuse_descends_range_397767_401767 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 405769 with hc18 | hc18
  · exact syracuse_descends_range_401768_405768 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 409770 with hc19 | hc19
  · exact syracuse_descends_range_405769_409769 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 413771 with hc20 | hc20
  · exact syracuse_descends_range_409770_413770 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 417772 with hc21 | hc21
  · exact syracuse_descends_range_413771_417771 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 421773 with hc22 | hc22
  · exact syracuse_descends_range_417772_421772 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 424774 with hc23 | hc23
  · exact syracuse_descends_range_421773_424773 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 428775 with hc24 | hc24
  · exact syracuse_descends_range_424774_428774 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 432776 with hc25 | hc25
  · exact syracuse_descends_range_428775_432775 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 435777 with hc26 | hc26
  · exact syracuse_descends_range_432776_435776 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 439778 with hc27 | hc27
  · exact syracuse_descends_range_435777_439777 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 443779 with hc28 | hc28
  · exact syracuse_descends_range_439778_443778 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 447780 with hc29 | hc29
  · exact syracuse_descends_range_443779_447779 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 451781 with hc30 | hc30
  · exact syracuse_descends_range_447780_451780 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 455782 with hc31 | hc31
  · exact syracuse_descends_range_451781_455781 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 459783 with hc32 | hc32
  · exact syracuse_descends_range_455782_459782 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 463784 with hc33 | hc33
  · exact syracuse_descends_range_459783_463783 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 467785 with hc34 | hc34
  · exact syracuse_descends_range_463784_467784 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 471786 with hc35 | hc35
  · exact syracuse_descends_range_467785_471785 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 475787 with hc36 | hc36
  · exact syracuse_descends_range_471786_475786 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 479788 with hc37 | hc37
  · exact syracuse_descends_range_475787_479787 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 483789 with hc38 | hc38
  · exact syracuse_descends_range_479788_483788 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 487790 with hc39 | hc39
  · exact syracuse_descends_range_483789_487789 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 491791 with hc40 | hc40
  · exact syracuse_descends_range_487790_491790 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 495792 with hc41 | hc41
  · exact syracuse_descends_range_491791_495791 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 499793 with hc42 | hc42
  · exact syracuse_descends_range_495792_499792 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 503794 with hc43 | hc43
  · exact syracuse_descends_range_499793_503793 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 507795 with hc44 | hc44
  · exact syracuse_descends_range_503794_507794 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 511796 with hc45 | hc45
  · exact syracuse_descends_range_507795_511795 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 515797 with hc46 | hc46
  · exact syracuse_descends_range_511796_515796 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 519798 with hc47 | hc47
  · exact syracuse_descends_range_515797_519797 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 523799 with hc48 | hc48
  · exact syracuse_descends_range_519798_523798 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 527800 with hc49 | hc49
  · exact syracuse_descends_range_523799_527799 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 531801 with hc50 | hc50
  · exact syracuse_descends_range_527800_531800 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 535802 with hc51 | hc51
  · exact syracuse_descends_range_531801_535801 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 539803 with hc52 | hc52
  · exact syracuse_descends_range_535802_539802 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 542804 with hc53 | hc53
  · exact syracuse_descends_range_539803_542803 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 546805 with hc54 | hc54
  · exact syracuse_descends_range_542804_546804 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 550806 with hc55 | hc55
  · exact syracuse_descends_range_546805_550805 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 554807 with hc56 | hc56
  · exact syracuse_descends_range_550806_554806 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 558808 with hc57 | hc57
  · exact syracuse_descends_range_554807_558807 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 562809 with hc58 | hc58
  · exact syracuse_descends_range_558808_562808 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 566810 with hc59 | hc59
  · exact syracuse_descends_range_562809_566809 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 570811 with hc60 | hc60
  · exact syracuse_descends_range_566810_570810 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 574812 with hc61 | hc61
  · exact syracuse_descends_range_570811_574811 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 578813 with hc62 | hc62
  · exact syracuse_descends_range_574812_578812 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 582814 with hc63 | hc63
  · exact syracuse_descends_range_578813_582813 m (by omega) (by omega) hodd
  exact syracuse_descends_range_582814_583287 m (by omega) (by omega) hodd
