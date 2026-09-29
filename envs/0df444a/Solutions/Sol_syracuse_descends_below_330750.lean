-- Prove2me | solution 1 for syracuse_descends_below_330750
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:22:35.13219+00:00
-- url     : https://prove2.me/submissions/c5c7332d-cb12-4609-a9c6-5282ef817825

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_99781
import Theorems.Thm_syracuse_descends_range_99781_103781
import Theorems.Thm_syracuse_descends_range_103782_107782
import Theorems.Thm_syracuse_descends_range_107783_111783
import Theorems.Thm_syracuse_descends_range_111784_115784
import Theorems.Thm_syracuse_descends_range_115785_119785
import Theorems.Thm_syracuse_descends_range_119786_123786
import Theorems.Thm_syracuse_descends_range_123787_127787
import Theorems.Thm_syracuse_descends_range_127788_131788
import Theorems.Thm_syracuse_descends_range_131789_135789
import Theorems.Thm_syracuse_descends_range_135790_139790
import Theorems.Thm_syracuse_descends_range_139791_143791
import Theorems.Thm_syracuse_descends_range_143792_147792
import Theorems.Thm_syracuse_descends_range_147793_151793
import Theorems.Thm_syracuse_descends_range_151794_155794
import Theorems.Thm_syracuse_descends_range_155795_159795
import Theorems.Thm_syracuse_descends_range_159796_163796
import Theorems.Thm_syracuse_descends_range_163797_167797
import Theorems.Thm_syracuse_descends_range_167798_171798
import Theorems.Thm_syracuse_descends_range_171799_175799
import Theorems.Thm_syracuse_descends_range_175800_179800
import Theorems.Thm_syracuse_descends_range_179801_183801
import Theorems.Thm_syracuse_descends_range_183802_187802
import Theorems.Thm_syracuse_descends_range_187803_191803
import Theorems.Thm_syracuse_descends_range_191804_195804
import Theorems.Thm_syracuse_descends_range_195805_199805
import Theorems.Thm_syracuse_descends_range_199806_203806
import Theorems.Thm_syracuse_descends_range_203807_207807
import Theorems.Thm_syracuse_descends_range_207808_211808
import Theorems.Thm_syracuse_descends_range_211809_215809
import Theorems.Thm_syracuse_descends_range_215810_219810
import Theorems.Thm_syracuse_descends_range_219811_223811
import Theorems.Thm_syracuse_descends_range_223812_227812
import Theorems.Thm_syracuse_descends_range_227813_231813
import Theorems.Thm_syracuse_descends_range_231814_235814
import Theorems.Thm_syracuse_descends_range_235815_239815
import Theorems.Thm_syracuse_descends_range_239816_243816
import Theorems.Thm_syracuse_descends_range_243817_247817
import Theorems.Thm_syracuse_descends_range_247818_251818
import Theorems.Thm_syracuse_descends_range_251819_255819
import Theorems.Thm_syracuse_descends_range_255820_259820
import Theorems.Thm_syracuse_descends_range_259821_263821
import Theorems.Thm_syracuse_descends_range_263822_267822
import Theorems.Thm_syracuse_descends_range_267823_271823
import Theorems.Thm_syracuse_descends_range_271824_275824
import Theorems.Thm_syracuse_descends_range_275825_279825
import Theorems.Thm_syracuse_descends_range_279826_283826
import Theorems.Thm_syracuse_descends_range_283827_287827
import Theorems.Thm_syracuse_descends_range_287828_291828
import Theorems.Thm_syracuse_descends_range_291829_295829
import Theorems.Thm_syracuse_descends_range_295830_299830
import Theorems.Thm_syracuse_descends_range_299831_303831
import Theorems.Thm_syracuse_descends_range_303832_307832
import Theorems.Thm_syracuse_descends_range_307833_311833
import Theorems.Thm_syracuse_descends_range_311834_315834
import Theorems.Thm_syracuse_descends_range_315835_319835
import Theorems.Thm_syracuse_descends_range_319836_323836
import Theorems.Thm_syracuse_descends_range_323837_327837
import Theorems.Thm_syracuse_descends_range_327838_330749

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 330750) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 99781 with hb | hb
  · obtain ⟨k, hk⟩ := syracuse_reaches_one_below_99781 m (by omega) hodd (by omega)
    exact ⟨k, by rw [hk]; omega⟩
  rcases Nat.lt_or_ge m 103782 with hc0 | hc0
  · exact syracuse_descends_range_99781_103781 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 107783 with hc1 | hc1
  · exact syracuse_descends_range_103782_107782 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 111784 with hc2 | hc2
  · exact syracuse_descends_range_107783_111783 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 115785 with hc3 | hc3
  · exact syracuse_descends_range_111784_115784 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 119786 with hc4 | hc4
  · exact syracuse_descends_range_115785_119785 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 123787 with hc5 | hc5
  · exact syracuse_descends_range_119786_123786 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 127788 with hc6 | hc6
  · exact syracuse_descends_range_123787_127787 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 131789 with hc7 | hc7
  · exact syracuse_descends_range_127788_131788 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 135790 with hc8 | hc8
  · exact syracuse_descends_range_131789_135789 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 139791 with hc9 | hc9
  · exact syracuse_descends_range_135790_139790 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 143792 with hc10 | hc10
  · exact syracuse_descends_range_139791_143791 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 147793 with hc11 | hc11
  · exact syracuse_descends_range_143792_147792 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 151794 with hc12 | hc12
  · exact syracuse_descends_range_147793_151793 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 155795 with hc13 | hc13
  · exact syracuse_descends_range_151794_155794 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 159796 with hc14 | hc14
  · exact syracuse_descends_range_155795_159795 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 163797 with hc15 | hc15
  · exact syracuse_descends_range_159796_163796 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 167798 with hc16 | hc16
  · exact syracuse_descends_range_163797_167797 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 171799 with hc17 | hc17
  · exact syracuse_descends_range_167798_171798 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 175800 with hc18 | hc18
  · exact syracuse_descends_range_171799_175799 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 179801 with hc19 | hc19
  · exact syracuse_descends_range_175800_179800 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 183802 with hc20 | hc20
  · exact syracuse_descends_range_179801_183801 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 187803 with hc21 | hc21
  · exact syracuse_descends_range_183802_187802 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 191804 with hc22 | hc22
  · exact syracuse_descends_range_187803_191803 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 195805 with hc23 | hc23
  · exact syracuse_descends_range_191804_195804 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 199806 with hc24 | hc24
  · exact syracuse_descends_range_195805_199805 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 203807 with hc25 | hc25
  · exact syracuse_descends_range_199806_203806 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 207808 with hc26 | hc26
  · exact syracuse_descends_range_203807_207807 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 211809 with hc27 | hc27
  · exact syracuse_descends_range_207808_211808 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 215810 with hc28 | hc28
  · exact syracuse_descends_range_211809_215809 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 219811 with hc29 | hc29
  · exact syracuse_descends_range_215810_219810 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 223812 with hc30 | hc30
  · exact syracuse_descends_range_219811_223811 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 227813 with hc31 | hc31
  · exact syracuse_descends_range_223812_227812 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 231814 with hc32 | hc32
  · exact syracuse_descends_range_227813_231813 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 235815 with hc33 | hc33
  · exact syracuse_descends_range_231814_235814 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 239816 with hc34 | hc34
  · exact syracuse_descends_range_235815_239815 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 243817 with hc35 | hc35
  · exact syracuse_descends_range_239816_243816 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 247818 with hc36 | hc36
  · exact syracuse_descends_range_243817_247817 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 251819 with hc37 | hc37
  · exact syracuse_descends_range_247818_251818 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 255820 with hc38 | hc38
  · exact syracuse_descends_range_251819_255819 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 259821 with hc39 | hc39
  · exact syracuse_descends_range_255820_259820 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 263822 with hc40 | hc40
  · exact syracuse_descends_range_259821_263821 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 267823 with hc41 | hc41
  · exact syracuse_descends_range_263822_267822 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 271824 with hc42 | hc42
  · exact syracuse_descends_range_267823_271823 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 275825 with hc43 | hc43
  · exact syracuse_descends_range_271824_275824 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 279826 with hc44 | hc44
  · exact syracuse_descends_range_275825_279825 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 283827 with hc45 | hc45
  · exact syracuse_descends_range_279826_283826 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 287828 with hc46 | hc46
  · exact syracuse_descends_range_283827_287827 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 291829 with hc47 | hc47
  · exact syracuse_descends_range_287828_291828 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 295830 with hc48 | hc48
  · exact syracuse_descends_range_291829_295829 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 299831 with hc49 | hc49
  · exact syracuse_descends_range_295830_299830 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 303832 with hc50 | hc50
  · exact syracuse_descends_range_299831_303831 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 307833 with hc51 | hc51
  · exact syracuse_descends_range_303832_307832 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 311834 with hc52 | hc52
  · exact syracuse_descends_range_307833_311833 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 315835 with hc53 | hc53
  · exact syracuse_descends_range_311834_315834 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 319836 with hc54 | hc54
  · exact syracuse_descends_range_315835_319835 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 323837 with hc55 | hc55
  · exact syracuse_descends_range_319836_323836 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 327838 with hc56 | hc56
  · exact syracuse_descends_range_323837_327837 m (by omega) (by omega) hodd
  exact syracuse_descends_range_327838_330749 m (by omega) (by omega) hodd
