-- Prove2me | solution 1 for syracuse_descends_range_1200417_1202417
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:44.553386+00:00
-- url     : https://prove2.me/submissions/4c19319b-4eae-487d-aecf-11819f9fd88f

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B2703365 : Blo 1200417 2703365 := bbase (se 4 (by rfl) ⟨253440, by rfl⟩ : syracuseStep 2703365 = 506881) (by norm_num)
theorem B1802261 : Blo 1200417 1802261 := bbase (se 6 (by rfl) ⟨42240, by rfl⟩ : syracuseStep 1802261 = 84481) (by norm_num)
theorem B1925141 : Blo 1200417 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B1351705 : Blo 1200417 1351705 := bbase (se 2 (by rfl) ⟨506889, by rfl⟩ : syracuseStep 1351705 = 1013779) (by norm_num)
theorem B1802285 : Blo 1200417 1802285 := bbase (se 3 (by rfl) ⟨337928, by rfl⟩ : syracuseStep 1802285 = 675857) (by norm_num)
theorem B1351741 : Blo 1200417 1351741 := bbase (se 3 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 1351741 = 506903) (by norm_num)
theorem B1802309 : Blo 1200417 1802309 := bbase (se 4 (by rfl) ⟨168966, by rfl⟩ : syracuseStep 1802309 = 337933) (by norm_num)
theorem B2703437 : Blo 1200417 2703437 := bbase (se 3 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 2703437 = 1013789) (by norm_num)
theorem B1802333 : Blo 1200417 1802333 := bbase (se 3 (by rfl) ⟨337937, by rfl⟩ : syracuseStep 1802333 = 675875) (by norm_num)
theorem B1351777 : Blo 1200417 1351777 := bbase (se 2 (by rfl) ⟨506916, by rfl⟩ : syracuseStep 1351777 = 1013833) (by norm_num)
theorem B1802357 : Blo 1200417 1802357 := bbase (se 5 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 1802357 = 168971) (by norm_num)
theorem B1351813 : Blo 1200417 1351813 := bbase (se 4 (by rfl) ⟨126732, by rfl⟩ : syracuseStep 1351813 = 253465) (by norm_num)
theorem B1802381 : Blo 1200417 1802381 := bbase (se 3 (by rfl) ⟨337946, by rfl⟩ : syracuseStep 1802381 = 675893) (by norm_num)
theorem B15384725 : Blo 1200417 15384725 := bbase (se 6 (by rfl) ⟨360579, by rfl⟩ : syracuseStep 15384725 = 721159) (by norm_num)
theorem B9117845 : Blo 1200417 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B2703509 : Blo 1200417 2703509 := bbase (se 6 (by rfl) ⟨63363, by rfl⟩ : syracuseStep 2703509 = 126727) (by norm_num)
theorem B1802405 : Blo 1200417 1802405 := bbase (se 4 (by rfl) ⟨168975, by rfl⟩ : syracuseStep 1802405 = 337951) (by norm_num)
theorem B1351849 : Blo 1200417 1351849 := bbase (se 2 (by rfl) ⟨506943, by rfl⟩ : syracuseStep 1351849 = 1013887) (by norm_num)
theorem B1802429 : Blo 1200417 1802429 := bbase (se 3 (by rfl) ⟨337955, by rfl⟩ : syracuseStep 1802429 = 675911) (by norm_num)
theorem B4055237 : Blo 1200417 4055237 := bbase (se 4 (by rfl) ⟨380178, by rfl⟩ : syracuseStep 4055237 = 760357) (by norm_num)
theorem B1351885 : Blo 1200417 1351885 := bbase (se 3 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 1351885 = 506957) (by norm_num)
theorem B1802453 : Blo 1200417 1802453 := bbase (se 7 (by rfl) ⟨21122, by rfl⟩ : syracuseStep 1802453 = 42245) (by norm_num)
theorem B6496469 : Blo 1200417 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B2703581 : Blo 1200417 2703581 := bbase (se 3 (by rfl) ⟨506921, by rfl⟩ : syracuseStep 2703581 = 1013843) (by norm_num)
theorem B1802477 : Blo 1200417 1802477 := bbase (se 3 (by rfl) ⟨337964, by rfl⟩ : syracuseStep 1802477 = 675929) (by norm_num)
theorem B1351921 : Blo 1200417 1351921 := bbase (se 2 (by rfl) ⟨506970, by rfl⟩ : syracuseStep 1351921 = 1013941) (by norm_num)
theorem B6078725 : Blo 1200417 6078725 := bbase (se 4 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 6078725 = 1139761) (by norm_num)
theorem B1802501 : Blo 1200417 1802501 := bbase (se 4 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 1802501 = 337969) (by norm_num)
theorem B1351957 : Blo 1200417 1351957 := bbase (se 6 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 1351957 = 63373) (by norm_num)
theorem B1802525 : Blo 1200417 1802525 := bbase (se 3 (by rfl) ⟨337973, by rfl⟩ : syracuseStep 1802525 = 675947) (by norm_num)
theorem B2703653 : Blo 1200417 2703653 := bbase (se 4 (by rfl) ⟨253467, by rfl⟩ : syracuseStep 2703653 = 506935) (by norm_num)
theorem B1802549 : Blo 1200417 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B1351993 : Blo 1200417 1351993 := bbase (se 2 (by rfl) ⟨506997, by rfl⟩ : syracuseStep 1351993 = 1013995) (by norm_num)
theorem B4112693 : Blo 1200417 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B3039565 : Blo 1200417 3039565 := bbase (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) (by norm_num)
theorem B1802573 : Blo 1200417 1802573 := bbase (se 3 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 1802573 = 675965) (by norm_num)
theorem B1352029 : Blo 1200417 1352029 := bbase (se 3 (by rfl) ⟨253505, by rfl⟩ : syracuseStep 1352029 = 507011) (by norm_num)
theorem B1802597 : Blo 1200417 1802597 := bbase (se 4 (by rfl) ⟨168993, by rfl⟩ : syracuseStep 1802597 = 337987) (by norm_num)
theorem B2703725 : Blo 1200417 2703725 := bbase (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) (by norm_num)
theorem B1802621 : Blo 1200417 1802621 := bbase (se 3 (by rfl) ⟨337991, by rfl⟩ : syracuseStep 1802621 = 675983) (by norm_num)
theorem B1352065 : Blo 1200417 1352065 := bbase (se 2 (by rfl) ⟨507024, by rfl⟩ : syracuseStep 1352065 = 1014049) (by norm_num)
theorem B1802645 : Blo 1200417 1802645 := bbase (se 6 (by rfl) ⟨42249, by rfl⟩ : syracuseStep 1802645 = 84499) (by norm_num)
theorem B1352101 : Blo 1200417 1352101 := bbase (se 4 (by rfl) ⟨126759, by rfl⟩ : syracuseStep 1352101 = 253519) (by norm_num)
theorem B1802669 : Blo 1200417 1802669 := bbase (se 3 (by rfl) ⟨338000, by rfl⟩ : syracuseStep 1802669 = 676001) (by norm_num)
theorem B2703797 : Blo 1200417 2703797 := bbase (se 5 (by rfl) ⟨126740, by rfl⟩ : syracuseStep 2703797 = 253481) (by norm_num)
theorem B3039677 : Blo 1200417 3039677 := bbase (se 3 (by rfl) ⟨569939, by rfl⟩ : syracuseStep 3039677 = 1139879) (by norm_num)
theorem B1802693 : Blo 1200417 1802693 := bbase (se 4 (by rfl) ⟨169002, by rfl⟩ : syracuseStep 1802693 = 338005) (by norm_num)
theorem B1352137 : Blo 1200417 1352137 := bbase (se 2 (by rfl) ⟨507051, by rfl⟩ : syracuseStep 1352137 = 1014103) (by norm_num)
theorem B1540561 : Blo 1200417 1540561 := bbase (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) (by norm_num)
theorem B10961365 : Blo 1200417 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1851869 : Blo 1200417 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B1802717 : Blo 1200417 1802717 := bbase (se 3 (by rfl) ⟨338009, by rfl⟩ : syracuseStep 1802717 = 676019) (by norm_num)
theorem B1352173 : Blo 1200417 1352173 := bbase (se 3 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 1352173 = 507065) (by norm_num)
theorem B1802741 : Blo 1200417 1802741 := bbase (se 5 (by rfl) ⟨84503, by rfl⟩ : syracuseStep 1802741 = 169007) (by norm_num)
theorem B2703869 : Blo 1200417 2703869 := bbase (se 3 (by rfl) ⟨506975, by rfl⟩ : syracuseStep 2703869 = 1013951) (by norm_num)
theorem B1540621 : Blo 1200417 1540621 := bbase (se 3 (by rfl) ⟨288866, by rfl⟩ : syracuseStep 1540621 = 577733) (by norm_num)
theorem B1802765 : Blo 1200417 1802765 := bbase (se 3 (by rfl) ⟨338018, by rfl⟩ : syracuseStep 1802765 = 676037) (by norm_num)
theorem B1352209 : Blo 1200417 1352209 := bbase (se 2 (by rfl) ⟨507078, by rfl⟩ : syracuseStep 1352209 = 1014157) (by norm_num)
theorem B1802789 : Blo 1200417 1802789 := bbase (se 4 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 1802789 = 338023) (by norm_num)
theorem B1352245 : Blo 1200417 1352245 := bbase (se 5 (by rfl) ⟨63386, by rfl⟩ : syracuseStep 1352245 = 126773) (by norm_num)
theorem B1802813 : Blo 1200417 1802813 := bbase (se 3 (by rfl) ⟨338027, by rfl⟩ : syracuseStep 1802813 = 676055) (by norm_num)
theorem B2703941 : Blo 1200417 2703941 := bbase (se 4 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 2703941 = 506989) (by norm_num)
theorem B1802837 : Blo 1200417 1802837 := bbase (se 8 (by rfl) ⟨10563, by rfl⟩ : syracuseStep 1802837 = 21127) (by norm_num)
theorem B1352281 : Blo 1200417 1352281 := bbase (se 2 (by rfl) ⟨507105, by rfl⟩ : syracuseStep 1352281 = 1014211) (by norm_num)
theorem B1802861 : Blo 1200417 1802861 := bbase (se 3 (by rfl) ⟨338036, by rfl⟩ : syracuseStep 1802861 = 676073) (by norm_num)
theorem B2433653 : Blo 1200417 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B4055669 : Blo 1200417 4055669 := bbase (se 5 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 4055669 = 380219) (by norm_num)
theorem B3039869 : Blo 1200417 3039869 := bbase (se 3 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 3039869 = 1139951) (by norm_num)
theorem B1352317 : Blo 1200417 1352317 := bbase (se 3 (by rfl) ⟨253559, by rfl⟩ : syracuseStep 1352317 = 507119) (by norm_num)
theorem B1802885 : Blo 1200417 1802885 := bbase (se 4 (by rfl) ⟨169020, by rfl⟩ : syracuseStep 1802885 = 338041) (by norm_num)
theorem B2704013 : Blo 1200417 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B1442453 : Blo 1200417 1442453 := bbase (se 6 (by rfl) ⟨33807, by rfl⟩ : syracuseStep 1442453 = 67615) (by norm_num)
theorem B1802909 : Blo 1200417 1802909 := bbase (se 3 (by rfl) ⟨338045, by rfl⟩ : syracuseStep 1802909 = 676091) (by norm_num)
theorem B1352353 : Blo 1200417 1352353 := bbase (se 2 (by rfl) ⟨507132, by rfl⟩ : syracuseStep 1352353 = 1014265) (by norm_num)
theorem B1802933 : Blo 1200417 1802933 := bbase (se 5 (by rfl) ⟨84512, by rfl⟩ : syracuseStep 1802933 = 169025) (by norm_num)
theorem B2564797 : Blo 1200417 2564797 := bbase (se 3 (by rfl) ⟨480899, by rfl⟩ : syracuseStep 2564797 = 961799) (by norm_num)
theorem B1352389 : Blo 1200417 1352389 := bbase (se 4 (by rfl) ⟨126786, by rfl⟩ : syracuseStep 1352389 = 253573) (by norm_num)
theorem B1802957 : Blo 1200417 1802957 := bbase (se 3 (by rfl) ⟨338054, by rfl⟩ : syracuseStep 1802957 = 676109) (by norm_num)
theorem B2704085 : Blo 1200417 2704085 := bbase (se 7 (by rfl) ⟨31688, by rfl⟩ : syracuseStep 2704085 = 63377) (by norm_num)
theorem B1802981 : Blo 1200417 1802981 := bbase (se 4 (by rfl) ⟨169029, by rfl⟩ : syracuseStep 1802981 = 338059) (by norm_num)
theorem B1352425 : Blo 1200417 1352425 := bbase (se 2 (by rfl) ⟨507159, by rfl⟩ : syracuseStep 1352425 = 1014319) (by norm_num)
theorem B2884349 : Blo 1200417 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B1803005 : Blo 1200417 1803005 := bbase (se 3 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 1803005 = 676127) (by norm_num)
theorem B1352461 : Blo 1200417 1352461 := bbase (se 3 (by rfl) ⟨253586, by rfl⟩ : syracuseStep 1352461 = 507173) (by norm_num)
theorem B12985109 : Blo 1200417 12985109 := bbase (se 6 (by rfl) ⟨304338, by rfl⟩ : syracuseStep 12985109 = 608677) (by norm_num)
theorem B1803029 : Blo 1200417 1803029 := bbase (se 6 (by rfl) ⟨42258, by rfl⟩ : syracuseStep 1803029 = 84517) (by norm_num)
theorem B2704157 : Blo 1200417 2704157 := bbase (se 3 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 2704157 = 1014059) (by norm_num)
theorem B1803053 : Blo 1200417 1803053 := bbase (se 3 (by rfl) ⟨338072, by rfl⟩ : syracuseStep 1803053 = 676145) (by norm_num)
theorem B1352497 : Blo 1200417 1352497 := bbase (se 2 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 1352497 = 1014373) (by norm_num)
theorem B1803077 : Blo 1200417 1803077 := bbase (se 4 (by rfl) ⟨169038, by rfl⟩ : syracuseStep 1803077 = 338077) (by norm_num)
theorem B2564941 : Blo 1200417 2564941 := bbase (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) (by norm_num)
theorem B1540949 : Blo 1200417 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B1352533 : Blo 1200417 1352533 := bbase (se 9 (by rfl) ⟨3962, by rfl⟩ : syracuseStep 1352533 = 7925) (by norm_num)
theorem B1803101 : Blo 1200417 1803101 := bbase (se 3 (by rfl) ⟨338081, by rfl⟩ : syracuseStep 1803101 = 676163) (by norm_num)
theorem B2704229 : Blo 1200417 2704229 := bbase (se 4 (by rfl) ⟨253521, by rfl⟩ : syracuseStep 2704229 = 507043) (by norm_num)
theorem B1803125 : Blo 1200417 1803125 := bbase (se 5 (by rfl) ⟨84521, by rfl⟩ : syracuseStep 1803125 = 169043) (by norm_num)
theorem B1352569 : Blo 1200417 1352569 := bbase (se 2 (by rfl) ⟨507213, by rfl⟩ : syracuseStep 1352569 = 1014427) (by norm_num)
theorem B1926013 : Blo 1200417 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B1803149 : Blo 1200417 1803149 := bbase (se 3 (by rfl) ⟨338090, by rfl⟩ : syracuseStep 1803149 = 676181) (by norm_num)
theorem B4875157 : Blo 1200417 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B1352605 : Blo 1200417 1352605 := bbase (se 3 (by rfl) ⟨253613, by rfl⟩ : syracuseStep 1352605 = 507227) (by norm_num)
theorem B1803173 : Blo 1200417 1803173 := bbase (se 4 (by rfl) ⟨169047, by rfl⟩ : syracuseStep 1803173 = 338095) (by norm_num)
theorem B2704301 : Blo 1200417 2704301 := bbase (se 3 (by rfl) ⟨507056, by rfl⟩ : syracuseStep 2704301 = 1014113) (by norm_num)
theorem B1803197 : Blo 1200417 1803197 := bbase (se 3 (by rfl) ⟨338099, by rfl⟩ : syracuseStep 1803197 = 676199) (by norm_num)
theorem B1352641 : Blo 1200417 1352641 := bbase (se 2 (by rfl) ⟨507240, by rfl⟩ : syracuseStep 1352641 = 1014481) (by norm_num)
theorem B3040213 : Blo 1200417 3040213 := bbase (se 7 (by rfl) ⟨35627, by rfl⟩ : syracuseStep 3040213 = 71255) (by norm_num)
theorem B1803221 : Blo 1200417 1803221 := bbase (se 7 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 1803221 = 42263) (by norm_num)
theorem B1352677 : Blo 1200417 1352677 := bbase (se 4 (by rfl) ⟨126813, by rfl⟩ : syracuseStep 1352677 = 253627) (by norm_num)
theorem B1803245 : Blo 1200417 1803245 := bbase (se 3 (by rfl) ⟨338108, by rfl⟩ : syracuseStep 1803245 = 676217) (by norm_num)
theorem B2704373 : Blo 1200417 2704373 := bbase (se 5 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 2704373 = 253535) (by norm_num)
theorem B1803269 : Blo 1200417 1803269 := bbase (se 4 (by rfl) ⟨169056, by rfl⟩ : syracuseStep 1803269 = 338113) (by norm_num)
theorem B1352713 : Blo 1200417 1352713 := bbase (se 2 (by rfl) ⟨507267, by rfl⟩ : syracuseStep 1352713 = 1014535) (by norm_num)
theorem B1803293 : Blo 1200417 1803293 := bbase (se 3 (by rfl) ⟨338117, by rfl⟩ : syracuseStep 1803293 = 676235) (by norm_num)
theorem B4056101 : Blo 1200417 4056101 := bbase (se 4 (by rfl) ⟨380259, by rfl⟩ : syracuseStep 4056101 = 760519) (by norm_num)
theorem B1803317 : Blo 1200417 1803317 := bbase (se 5 (by rfl) ⟨84530, by rfl⟩ : syracuseStep 1803317 = 169061) (by norm_num)
theorem B2704445 : Blo 1200417 2704445 := bbase (se 3 (by rfl) ⟨507083, by rfl⟩ : syracuseStep 2704445 = 1014167) (by norm_num)
theorem B3040325 : Blo 1200417 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B1827917 : Blo 1200417 1827917 := bbase (se 3 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 1827917 = 685469) (by norm_num)
theorem B1803341 : Blo 1200417 1803341 := bbase (se 3 (by rfl) ⟨338126, by rfl⟩ : syracuseStep 1803341 = 676253) (by norm_num)
theorem B1803365 : Blo 1200417 1803365 := bbase (se 4 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 1803365 = 338131) (by norm_num)
theorem B1827965 : Blo 1200417 1827965 := bbase (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) (by norm_num)
theorem B1803389 : Blo 1200417 1803389 := bbase (se 3 (by rfl) ⟨338135, by rfl⟩ : syracuseStep 1803389 = 676271) (by norm_num)
theorem B2704517 : Blo 1200417 2704517 := bbase (se 4 (by rfl) ⟨253548, by rfl⟩ : syracuseStep 2704517 = 507097) (by norm_num)
theorem B1803413 : Blo 1200417 1803413 := bbase (se 6 (by rfl) ⟨42267, by rfl⟩ : syracuseStep 1803413 = 84535) (by norm_num)
theorem B4564133 : Blo 1200417 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B1803437 : Blo 1200417 1803437 := bbase (se 3 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 1803437 = 676289) (by norm_num)
theorem B2565317 : Blo 1200417 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B1803461 : Blo 1200417 1803461 := bbase (se 4 (by rfl) ⟨169074, by rfl⟩ : syracuseStep 1803461 = 338149) (by norm_num)
theorem B2704589 : Blo 1200417 2704589 := bbase (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) (by norm_num)
theorem B1803485 : Blo 1200417 1803485 := bbase (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) (by norm_num)
theorem B1803509 : Blo 1200417 1803509 := bbase (se 5 (by rfl) ⟨84539, by rfl⟩ : syracuseStep 1803509 = 169079) (by norm_num)
theorem B3040517 : Blo 1200417 3040517 := bbase (se 4 (by rfl) ⟨285048, by rfl⟩ : syracuseStep 3040517 = 570097) (by norm_num)
theorem B1803533 : Blo 1200417 1803533 := bbase (se 3 (by rfl) ⟨338162, by rfl⟩ : syracuseStep 1803533 = 676325) (by norm_num)
theorem B2704661 : Blo 1200417 2704661 := bbase (se 6 (by rfl) ⟨63390, by rfl⟩ : syracuseStep 2704661 = 126781) (by norm_num)
theorem B1803557 : Blo 1200417 1803557 := bbase (se 4 (by rfl) ⟨169083, by rfl⟩ : syracuseStep 1803557 = 338167) (by norm_num)
theorem B1803581 : Blo 1200417 1803581 := bbase (se 3 (by rfl) ⟨338171, by rfl⟩ : syracuseStep 1803581 = 676343) (by norm_num)
theorem B1443145 : Blo 1200417 1443145 := bbase (se 2 (by rfl) ⟨541179, by rfl⟩ : syracuseStep 1443145 = 1082359) (by norm_num)
theorem B1803605 : Blo 1200417 1803605 := bbase (se 12 (by rfl) ⟨660, by rfl⟩ : syracuseStep 1803605 = 1321) (by norm_num)
theorem B2704733 : Blo 1200417 2704733 := bbase (se 3 (by rfl) ⟨507137, by rfl⟩ : syracuseStep 2704733 = 1014275) (by norm_num)
theorem B6014341 : Blo 1200417 6014341 := bbase (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) (by norm_num)
theorem B2704805 : Blo 1200417 2704805 := bbase (se 4 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 2704805 = 507151) (by norm_num)
theorem B1443241 : Blo 1200417 1443241 := bbase (se 2 (by rfl) ⟨541215, by rfl⟩ : syracuseStep 1443241 = 1082431) (by norm_num)
theorem B2467253 : Blo 1200417 2467253 := bbase (se 5 (by rfl) ⟨115652, by rfl⟩ : syracuseStep 2467253 = 231305) (by norm_num)
theorem B3900869 : Blo 1200417 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B4564421 : Blo 1200417 4564421 := bbase (se 4 (by rfl) ⟨427914, by rfl⟩ : syracuseStep 4564421 = 855829) (by norm_num)
theorem B3851717 : Blo 1200417 3851717 := bbase (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) (by norm_num)
theorem B4056533 : Blo 1200417 4056533 := bbase (se 7 (by rfl) ⟨47537, by rfl⟩ : syracuseStep 4056533 = 95075) (by norm_num)
theorem B2704877 : Blo 1200417 2704877 := bbase (se 3 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 2704877 = 1014329) (by norm_num)
theorem B6080021 : Blo 1200417 6080021 := bbase (se 6 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 6080021 = 285001) (by norm_num)
theorem B2565685 : Blo 1200417 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B2311733 : Blo 1200417 2311733 := bbase (se 5 (by rfl) ⟨108362, by rfl⟩ : syracuseStep 2311733 = 216725) (by norm_num)
theorem B2704949 : Blo 1200417 2704949 := bbase (se 5 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 2704949 = 253589) (by norm_num)
theorem B3040861 : Blo 1200417 3040861 := bbase (se 3 (by rfl) ⟨570161, by rfl⟩ : syracuseStep 3040861 = 1140323) (by norm_num)
theorem B2279029 : Blo 1200417 2279029 := bbase (se 5 (by rfl) ⟨106829, by rfl⟩ : syracuseStep 2279029 = 213659) (by norm_num)
theorem B2705021 : Blo 1200417 2705021 := bbase (se 3 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 2705021 = 1014383) (by norm_num)
theorem B1369765 : Blo 1200417 1369765 := bbase (se 4 (by rfl) ⟨128415, by rfl⟩ : syracuseStep 1369765 = 256831) (by norm_num)
theorem B2705093 : Blo 1200417 2705093 := bbase (se 4 (by rfl) ⟨253602, by rfl⟩ : syracuseStep 2705093 = 507205) (by norm_num)
theorem B3040973 : Blo 1200417 3040973 := bbase (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) (by norm_num)
theorem B2344661 : Blo 1200417 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B2279173 : Blo 1200417 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B2705165 : Blo 1200417 2705165 := bbase (se 3 (by rfl) ⟨507218, by rfl⟩ : syracuseStep 2705165 = 1014437) (by norm_num)
theorem B3245845 : Blo 1200417 3245845 := bbase (se 6 (by rfl) ⟨76074, by rfl⟩ : syracuseStep 3245845 = 152149) (by norm_num)
theorem B1443625 : Blo 1200417 1443625 := bbase (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) (by norm_num)
theorem B2705237 : Blo 1200417 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B2164573 : Blo 1200417 2164573 := bbase (se 3 (by rfl) ⟨405857, by rfl⟩ : syracuseStep 2164573 = 811715) (by norm_num)
theorem B4056965 : Blo 1200417 4056965 := bbase (se 4 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 4056965 = 760681) (by norm_num)
theorem B3041165 : Blo 1200417 3041165 := bbase (se 3 (by rfl) ⟨570218, by rfl⟩ : syracuseStep 3041165 = 1140437) (by norm_num)
theorem B2705309 : Blo 1200417 2705309 := bbase (se 3 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 2705309 = 1014491) (by norm_num)
theorem B2279333 : Blo 1200417 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B7694261 : Blo 1200417 7694261 := bbase (se 5 (by rfl) ⟨360668, by rfl⟩ : syracuseStep 7694261 = 721337) (by norm_num)
theorem B2705381 : Blo 1200417 2705381 := bbase (se 4 (by rfl) ⟨253629, by rfl⟩ : syracuseStep 2705381 = 507259) (by norm_num)
theorem B2279477 : Blo 1200417 2279477 := bbase (se 5 (by rfl) ⟨106850, by rfl⟩ : syracuseStep 2279477 = 213701) (by norm_num)
theorem B3655733 : Blo 1200417 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B13674581 : Blo 1200417 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B3082333 : Blo 1200417 3082333 := bbase (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) (by norm_num)
theorem B9242741 : Blo 1200417 9242741 := bbase (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) (by norm_num)
theorem B3041509 : Blo 1200417 3041509 := bbase (se 4 (by rfl) ⟨285141, by rfl⟩ : syracuseStep 3041509 = 570283) (by norm_num)
theorem B12503285 : Blo 1200417 12503285 := bbase (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) (by norm_num)
theorem B2025749 : Blo 1200417 2025749 := bbase (se 6 (by rfl) ⟨47478, by rfl⟩ : syracuseStep 2025749 = 94957) (by norm_num)
theorem B4057397 : Blo 1200417 4057397 := bbase (se 5 (by rfl) ⟨190190, by rfl⟩ : syracuseStep 4057397 = 380381) (by norm_num)
theorem B2345269 : Blo 1200417 2345269 := bbase (se 5 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 2345269 = 219869) (by norm_num)
theorem B2279765 : Blo 1200417 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B3041621 : Blo 1200417 3041621 := bbase (se 10 (by rfl) ⟨4455, by rfl⟩ : syracuseStep 3041621 = 8911) (by norm_num)
theorem B2025877 : Blo 1200417 2025877 := bbase (se 6 (by rfl) ⟨47481, by rfl⟩ : syracuseStep 2025877 = 94963) (by norm_num)
theorem B4327877 : Blo 1200417 4327877 := bbase (se 4 (by rfl) ⟨405738, by rfl⟩ : syracuseStep 4327877 = 811477) (by norm_num)
theorem B2025965 : Blo 1200417 2025965 := bbase (se 3 (by rfl) ⟨379868, by rfl⟩ : syracuseStep 2025965 = 759737) (by norm_num)
theorem B2279917 : Blo 1200417 2279917 := bbase (se 3 (by rfl) ⟨427484, by rfl⟩ : syracuseStep 2279917 = 854969) (by norm_num)
theorem B2599445 : Blo 1200417 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B3041813 : Blo 1200417 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B7309909 : Blo 1200417 7309909 := bbase (se 8 (by rfl) ⟨42831, by rfl⟩ : syracuseStep 7309909 = 85663) (by norm_num)
theorem B2026093 : Blo 1200417 2026093 := bbase (se 3 (by rfl) ⟨379892, by rfl⟩ : syracuseStep 2026093 = 759785) (by norm_num)
theorem B2165381 : Blo 1200417 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B8440469 : Blo 1200417 8440469 := bbase (se 6 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 8440469 = 395647) (by norm_num)
theorem B1370801 : Blo 1200417 1370801 := bbase (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) (by norm_num)
theorem B2026181 : Blo 1200417 2026181 := bbase (se 4 (by rfl) ⟨189954, by rfl⟩ : syracuseStep 2026181 = 379909) (by norm_num)
theorem B6163141 : Blo 1200417 6163141 := bbase (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) (by norm_num)
theorem B4057829 : Blo 1200417 4057829 := bbase (se 4 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 4057829 = 760843) (by norm_num)
theorem B2280221 : Blo 1200417 2280221 := bbase (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) (by norm_num)
theorem B6081317 : Blo 1200417 6081317 := bbase (se 4 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 6081317 = 1140247) (by norm_num)
theorem B2026309 : Blo 1200417 2026309 := bbase (se 4 (by rfl) ⟨189966, by rfl⟩ : syracuseStep 2026309 = 379933) (by norm_num)
theorem B3083093 : Blo 1200417 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B3042157 : Blo 1200417 3042157 := bbase (se 3 (by rfl) ⟨570404, by rfl⟩ : syracuseStep 3042157 = 1140809) (by norm_num)
theorem B2026397 : Blo 1200417 2026397 := bbase (se 3 (by rfl) ⟨379949, by rfl⟩ : syracuseStep 2026397 = 759899) (by norm_num)
theorem B3042269 : Blo 1200417 3042269 := bbase (se 3 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 3042269 = 1140851) (by norm_num)
theorem B2567189 : Blo 1200417 2567189 := bbase (se 6 (by rfl) ⟨60168, by rfl⟩ : syracuseStep 2567189 = 120337) (by norm_num)
theorem B2026525 : Blo 1200417 2026525 := bbase (se 3 (by rfl) ⟨379973, by rfl⟩ : syracuseStep 2026525 = 759947) (by norm_num)
theorem B2026613 : Blo 1200417 2026613 := bbase (se 5 (by rfl) ⟨94997, by rfl⟩ : syracuseStep 2026613 = 189995) (by norm_num)
theorem B3042461 : Blo 1200417 3042461 := bbase (se 3 (by rfl) ⟨570461, by rfl⟩ : syracuseStep 3042461 = 1140923) (by norm_num)
theorem B2567333 : Blo 1200417 2567333 := bbase (se 4 (by rfl) ⟨240687, by rfl⟩ : syracuseStep 2567333 = 481375) (by norm_num)
theorem B10267829 : Blo 1200417 10267829 := bbase (se 5 (by rfl) ⟨481304, by rfl⟩ : syracuseStep 10267829 = 962609) (by norm_num)
theorem B2026741 : Blo 1200417 2026741 := bbase (se 5 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 2026741 = 190007) (by norm_num)
theorem B4558133 : Blo 1200417 4558133 := bbase (se 5 (by rfl) ⟨213662, by rfl⟩ : syracuseStep 4558133 = 427325) (by norm_num)
theorem B2026829 : Blo 1200417 2026829 := bbase (se 3 (by rfl) ⟨380030, by rfl⟩ : syracuseStep 2026829 = 760061) (by norm_num)
theorem B2026957 : Blo 1200417 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B2436589 : Blo 1200417 2436589 := bbase (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) (by norm_num)
theorem B8220149 : Blo 1200417 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B3042805 : Blo 1200417 3042805 := bbase (se 5 (by rfl) ⟨142631, by rfl⟩ : syracuseStep 3042805 = 285263) (by norm_num)
theorem B5131781 : Blo 1200417 5131781 := bbase (se 4 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 5131781 = 962209) (by norm_num)
theorem B2280973 : Blo 1200417 2280973 := bbase (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) (by norm_num)
theorem B2567693 : Blo 1200417 2567693 := bbase (se 3 (by rfl) ⟨481442, by rfl⟩ : syracuseStep 2567693 = 962885) (by norm_num)
theorem B2027045 : Blo 1200417 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B58453589 : Blo 1200417 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B3042917 : Blo 1200417 3042917 := bbase (se 4 (by rfl) ⟨285273, by rfl⟩ : syracuseStep 3042917 = 570547) (by norm_num)
theorem B2281117 : Blo 1200417 2281117 := bbase (se 3 (by rfl) ⟨427709, by rfl⟩ : syracuseStep 2281117 = 855419) (by norm_num)
theorem B2027173 : Blo 1200417 2027173 := bbase (se 4 (by rfl) ⟨190047, by rfl⟩ : syracuseStep 2027173 = 380095) (by norm_num)
theorem B8220341 : Blo 1200417 8220341 := bbase (se 5 (by rfl) ⟨385328, by rfl⟩ : syracuseStep 8220341 = 770657) (by norm_num)
theorem B24678101 : Blo 1200417 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B1519337 : Blo 1200417 1519337 := bbase (se 2 (by rfl) ⟨569751, by rfl⟩ : syracuseStep 1519337 = 1139503) (by norm_num)
theorem B2027261 : Blo 1200417 2027261 := bbase (se 3 (by rfl) ⟨380111, by rfl⟩ : syracuseStep 2027261 = 760223) (by norm_num)
theorem B1519393 : Blo 1200417 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B5132069 : Blo 1200417 5132069 := bbase (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) (by norm_num)
theorem B3043109 : Blo 1200417 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B11702069 : Blo 1200417 11702069 := bbase (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) (by norm_num)
theorem B2281277 : Blo 1200417 2281277 := bbase (se 3 (by rfl) ⟨427739, by rfl⟩ : syracuseStep 2281277 = 855479) (by norm_num)
theorem B2887501 : Blo 1200417 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B2027389 : Blo 1200417 2027389 := bbase (se 3 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 2027389 = 760271) (by norm_num)
theorem B1519489 : Blo 1200417 1519489 := bbase (se 2 (by rfl) ⟨569808, by rfl⟩ : syracuseStep 1519489 = 1139617) (by norm_num)
theorem B2281421 : Blo 1200417 2281421 := bbase (se 3 (by rfl) ⟨427766, by rfl⟩ : syracuseStep 2281421 = 855533) (by norm_num)
theorem B2027477 : Blo 1200417 2027477 := bbase (se 7 (by rfl) ⟨23759, by rfl⟩ : syracuseStep 2027477 = 47519) (by norm_num)
theorem B6164453 : Blo 1200417 6164453 := bbase (se 4 (by rfl) ⟨577917, by rfl⟩ : syracuseStep 6164453 = 1155835) (by norm_num)
theorem B1519661 : Blo 1200417 1519661 := bbase (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) (by norm_num)
theorem B6082613 : Blo 1200417 6082613 := bbase (se 5 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 6082613 = 570245) (by norm_num)
theorem B2027605 : Blo 1200417 2027605 := bbase (se 8 (by rfl) ⟨11880, by rfl⟩ : syracuseStep 2027605 = 23761) (by norm_num)
theorem B1519717 : Blo 1200417 1519717 := bbase (se 4 (by rfl) ⟨142473, by rfl⟩ : syracuseStep 1519717 = 284947) (by norm_num)
theorem B3043453 : Blo 1200417 3043453 := bbase (se 3 (by rfl) ⟨570647, by rfl⟩ : syracuseStep 3043453 = 1141295) (by norm_num)
theorem B4108421 : Blo 1200417 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2027693 : Blo 1200417 2027693 := bbase (se 3 (by rfl) ⟨380192, by rfl⟩ : syracuseStep 2027693 = 760385) (by norm_num)
theorem B1519813 : Blo 1200417 1519813 := bbase (se 4 (by rfl) ⟨142482, by rfl⟩ : syracuseStep 1519813 = 284965) (by norm_num)
theorem B2281709 : Blo 1200417 2281709 := bbase (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) (by norm_num)
theorem B3043565 : Blo 1200417 3043565 := bbase (se 3 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 3043565 = 1141337) (by norm_num)
theorem B2027821 : Blo 1200417 2027821 := bbase (se 3 (by rfl) ⟨380216, by rfl⟩ : syracuseStep 2027821 = 760433) (by norm_num)
theorem B1519985 : Blo 1200417 1519985 := bbase (se 2 (by rfl) ⟨569994, by rfl⟩ : syracuseStep 1519985 = 1139989) (by norm_num)
theorem B2027909 : Blo 1200417 2027909 := bbase (se 4 (by rfl) ⟨190116, by rfl⟩ : syracuseStep 2027909 = 380233) (by norm_num)
theorem B2281861 : Blo 1200417 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B4690325 : Blo 1200417 4690325 := bbase (se 6 (by rfl) ⟨109929, by rfl⟩ : syracuseStep 4690325 = 219859) (by norm_num)
theorem B1520041 : Blo 1200417 1520041 := bbase (se 2 (by rfl) ⟨570015, by rfl⟩ : syracuseStep 1520041 = 1140031) (by norm_num)
theorem B1282501 : Blo 1200417 1282501 := bbase (se 4 (by rfl) ⟨120234, by rfl⟩ : syracuseStep 1282501 = 240469) (by norm_num)
theorem B2888173 : Blo 1200417 2888173 := bbase (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) (by norm_num)
theorem B2028037 : Blo 1200417 2028037 := bbase (se 4 (by rfl) ⟨190128, by rfl⟩ : syracuseStep 2028037 = 380257) (by norm_num)
theorem B1520137 : Blo 1200417 1520137 := bbase (se 2 (by rfl) ⟨570051, by rfl⟩ : syracuseStep 1520137 = 1140103) (by norm_num)
theorem B1282573 : Blo 1200417 1282573 := bbase (se 3 (by rfl) ⟨240482, by rfl⟩ : syracuseStep 1282573 = 480965) (by norm_num)
theorem B5132821 : Blo 1200417 5132821 := bbase (se 6 (by rfl) ⟨120300, by rfl⟩ : syracuseStep 5132821 = 240601) (by norm_num)
theorem B6492725 : Blo 1200417 6492725 := bbase (se 5 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 6492725 = 608693) (by norm_num)
theorem B2028125 : Blo 1200417 2028125 := bbase (se 3 (by rfl) ⟨380273, by rfl⟩ : syracuseStep 2028125 = 760547) (by norm_num)
theorem B1520309 : Blo 1200417 1520309 := bbase (se 5 (by rfl) ⟨71264, by rfl⟩ : syracuseStep 1520309 = 142529) (by norm_num)
theorem B2282165 : Blo 1200417 2282165 := bbase (se 5 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 2282165 = 213953) (by norm_num)
theorem B2740925 : Blo 1200417 2740925 := bbase (se 3 (by rfl) ⟨513923, by rfl⟩ : syracuseStep 2740925 = 1027847) (by norm_num)
theorem B1282753 : Blo 1200417 1282753 := bbase (se 2 (by rfl) ⟨481032, by rfl⟩ : syracuseStep 1282753 = 962065) (by norm_num)
theorem B2888405 : Blo 1200417 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B2028253 : Blo 1200417 2028253 := bbase (se 3 (by rfl) ⟨380297, by rfl⟩ : syracuseStep 2028253 = 760595) (by norm_num)
theorem B1520365 : Blo 1200417 1520365 := bbase (se 3 (by rfl) ⟨285068, by rfl⟩ : syracuseStep 1520365 = 570137) (by norm_num)
theorem B2028341 : Blo 1200417 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B4051781 : Blo 1200417 4051781 := bbase (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) (by norm_num)
theorem B1520461 : Blo 1200417 1520461 := bbase (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) (by norm_num)
theorem B2888549 : Blo 1200417 2888549 := bbase (se 4 (by rfl) ⟨270801, by rfl⟩ : syracuseStep 2888549 = 541603) (by norm_num)
theorem B3421061 : Blo 1200417 3421061 := bbase (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) (by norm_num)
theorem B2888597 : Blo 1200417 2888597 := bbase (se 6 (by rfl) ⟨67701, by rfl⟩ : syracuseStep 2888597 = 135403) (by norm_num)
theorem B1561513 : Blo 1200417 1561513 := bbase (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) (by norm_num)
theorem B2028469 : Blo 1200417 2028469 := bbase (se 5 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 2028469 = 190169) (by norm_num)
theorem B1520633 : Blo 1200417 1520633 := bbase (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) (by norm_num)
theorem B2028557 : Blo 1200417 2028557 := bbase (se 3 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 2028557 = 760709) (by norm_num)
theorem B1520689 : Blo 1200417 1520689 := bbase (se 2 (by rfl) ⟨570258, by rfl⟩ : syracuseStep 1520689 = 1140517) (by norm_num)
theorem B1283197 : Blo 1200417 1283197 := bbase (se 3 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 1283197 = 481199) (by norm_num)
theorem B2028685 : Blo 1200417 2028685 := bbase (se 3 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 2028685 = 760757) (by norm_num)
theorem B1520785 : Blo 1200417 1520785 := bbase (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) (by norm_num)
theorem B5633189 : Blo 1200417 5633189 := bbase (se 4 (by rfl) ⟨528111, by rfl⟩ : syracuseStep 5633189 = 1056223) (by norm_num)
theorem B2888885 : Blo 1200417 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B5772485 : Blo 1200417 5772485 := bbase (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) (by norm_num)
theorem B2028773 : Blo 1200417 2028773 := bbase (se 4 (by rfl) ⟨190197, by rfl⟩ : syracuseStep 2028773 = 380395) (by norm_num)
theorem B4052213 : Blo 1200417 4052213 := bbase (se 5 (by rfl) ⟨189947, by rfl⟩ : syracuseStep 4052213 = 379895) (by norm_num)
theorem B5133557 : Blo 1200417 5133557 := bbase (se 5 (by rfl) ⟨240635, by rfl⟩ : syracuseStep 5133557 = 481271) (by norm_num)
theorem B1283321 : Blo 1200417 1283321 := bbase (se 2 (by rfl) ⟨481245, by rfl⟩ : syracuseStep 1283321 = 962491) (by norm_num)
theorem B1520957 : Blo 1200417 1520957 := bbase (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) (by norm_num)
theorem B6083909 : Blo 1200417 6083909 := bbase (se 4 (by rfl) ⟨570366, by rfl⟩ : syracuseStep 6083909 = 1140733) (by norm_num)
theorem B1217873 : Blo 1200417 1217873 := bbase (se 2 (by rfl) ⟨456702, by rfl⟩ : syracuseStep 1217873 = 913405) (by norm_num)
theorem B2028901 : Blo 1200417 2028901 := bbase (se 4 (by rfl) ⟨190209, by rfl⟩ : syracuseStep 2028901 = 380419) (by norm_num)
theorem B1217905 : Blo 1200417 1217905 := bbase (se 2 (by rfl) ⟨456714, by rfl⟩ : syracuseStep 1217905 = 913429) (by norm_num)
theorem B4560245 : Blo 1200417 4560245 := bbase (se 5 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 4560245 = 427523) (by norm_num)
theorem B1521013 : Blo 1200417 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B1709437 : Blo 1200417 1709437 := bbase (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) (by norm_num)
theorem B2028989 : Blo 1200417 2028989 := bbase (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) (by norm_num)
theorem B1521109 : Blo 1200417 1521109 := bbase (se 7 (by rfl) ⟨17825, by rfl⟩ : syracuseStep 1521109 = 35651) (by norm_num)
theorem B1283573 : Blo 1200417 1283573 := bbase (se 5 (by rfl) ⟨60167, by rfl⟩ : syracuseStep 1283573 = 120335) (by norm_num)
theorem B2053669 : Blo 1200417 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B1521281 : Blo 1200417 1521281 := bbase (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) (by norm_num)
theorem B4560533 : Blo 1200417 4560533 := bbase (se 6 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 4560533 = 213775) (by norm_num)
theorem B4052645 : Blo 1200417 4052645 := bbase (se 4 (by rfl) ⟨379935, by rfl⟩ : syracuseStep 4052645 = 759871) (by norm_num)
theorem B1218221 : Blo 1200417 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B3249845 : Blo 1200417 3249845 := bbase (se 5 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 3249845 = 304673) (by norm_num)
theorem B1521337 : Blo 1200417 1521337 := bbase (se 2 (by rfl) ⟨570501, by rfl⟩ : syracuseStep 1521337 = 1141003) (by norm_num)
theorem B2700989 : Blo 1200417 2700989 := bbase (se 3 (by rfl) ⟨506435, by rfl⟩ : syracuseStep 2700989 = 1012871) (by norm_num)
theorem B3847925 : Blo 1200417 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B2701061 : Blo 1200417 2701061 := bbase (se 4 (by rfl) ⟨253224, by rfl⟩ : syracuseStep 2701061 = 506449) (by norm_num)
theorem B1521433 : Blo 1200417 1521433 := bbase (se 2 (by rfl) ⟨570537, by rfl⟩ : syracuseStep 1521433 = 1141075) (by norm_num)
theorem B1922861 : Blo 1200417 1922861 := bbase (se 3 (by rfl) ⟨360536, by rfl⟩ : syracuseStep 1922861 = 721073) (by norm_num)
theorem B2701133 : Blo 1200417 2701133 := bbase (se 3 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 2701133 = 1012925) (by norm_num)
theorem B5773157 : Blo 1200417 5773157 := bbase (se 4 (by rfl) ⟨541233, by rfl⟩ : syracuseStep 5773157 = 1082467) (by norm_num)
theorem B2701205 : Blo 1200417 2701205 := bbase (se 6 (by rfl) ⟨63309, by rfl⟩ : syracuseStep 2701205 = 126619) (by norm_num)
theorem B1284017 : Blo 1200417 1284017 := bbase (se 2 (by rfl) ⟨481506, by rfl⟩ : syracuseStep 1284017 = 963013) (by norm_num)
theorem B1521605 : Blo 1200417 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B1710029 : Blo 1200417 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B2701277 : Blo 1200417 2701277 := bbase (se 3 (by rfl) ⟨506489, by rfl⟩ : syracuseStep 2701277 = 1012979) (by norm_num)
theorem B1521661 : Blo 1200417 1521661 := bbase (se 3 (by rfl) ⟨285311, by rfl⟩ : syracuseStep 1521661 = 570623) (by norm_num)
theorem B1710109 : Blo 1200417 1710109 := bbase (se 3 (by rfl) ⟨320645, by rfl⟩ : syracuseStep 1710109 = 641291) (by norm_num)
theorem B2701349 : Blo 1200417 2701349 := bbase (se 4 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 2701349 = 506503) (by norm_num)
theorem B3422245 : Blo 1200417 3422245 := bbase (se 4 (by rfl) ⟨320835, by rfl⟩ : syracuseStep 3422245 = 641671) (by norm_num)
theorem B2742349 : Blo 1200417 2742349 := bbase (se 3 (by rfl) ⟨514190, by rfl⟩ : syracuseStep 2742349 = 1028381) (by norm_num)
theorem B4053077 : Blo 1200417 4053077 := bbase (se 8 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 4053077 = 47497) (by norm_num)
theorem B1521757 : Blo 1200417 1521757 := bbase (se 3 (by rfl) ⟨285329, by rfl⟩ : syracuseStep 1521757 = 570659) (by norm_num)
theorem B2701421 : Blo 1200417 2701421 := bbase (se 3 (by rfl) ⟨506516, by rfl⟩ : syracuseStep 2701421 = 1013033) (by norm_num)
theorem B1235057 : Blo 1200417 1235057 := bbase (se 2 (by rfl) ⟨463146, by rfl⟩ : syracuseStep 1235057 = 926293) (by norm_num)
theorem B1710229 : Blo 1200417 1710229 := bbase (se 6 (by rfl) ⟨40083, by rfl⟩ : syracuseStep 1710229 = 80167) (by norm_num)
theorem B1923245 : Blo 1200417 1923245 := bbase (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) (by norm_num)
theorem B2701493 : Blo 1200417 2701493 := bbase (se 5 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 2701493 = 253265) (by norm_num)
theorem B3422405 : Blo 1200417 3422405 := bbase (se 4 (by rfl) ⟨320850, by rfl⟩ : syracuseStep 3422405 = 641701) (by norm_num)
theorem B6846677 : Blo 1200417 6846677 := bbase (se 7 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 6846677 = 160469) (by norm_num)
theorem B1710325 : Blo 1200417 1710325 := bbase (se 5 (by rfl) ⟨80171, by rfl⟩ : syracuseStep 1710325 = 160343) (by norm_num)
theorem B2701565 : Blo 1200417 2701565 := bbase (se 3 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 2701565 = 1013087) (by norm_num)
theorem B6584597 : Blo 1200417 6584597 := bbase (se 6 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 6584597 = 308653) (by norm_num)
theorem B1923373 : Blo 1200417 1923373 := bbase (se 3 (by rfl) ⟨360632, by rfl⟩ : syracuseStep 1923373 = 721265) (by norm_num)
theorem B2701637 : Blo 1200417 2701637 := bbase (se 4 (by rfl) ⟨253278, by rfl⟩ : syracuseStep 2701637 = 506557) (by norm_num)
theorem B6838613 : Blo 1200417 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B3651941 : Blo 1200417 3651941 := bbase (se 4 (by rfl) ⟨342369, by rfl⟩ : syracuseStep 3651941 = 684739) (by norm_num)
theorem B2775437 : Blo 1200417 2775437 := bbase (se 3 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 2775437 = 1040789) (by norm_num)
theorem B2701709 : Blo 1200417 2701709 := bbase (se 3 (by rfl) ⟨506570, by rfl⟩ : syracuseStep 2701709 = 1013141) (by norm_num)
theorem B1800629 : Blo 1200417 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B3422645 : Blo 1200417 3422645 := bbase (se 5 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 3422645 = 320873) (by norm_num)
theorem B1800653 : Blo 1200417 1800653 := bbase (se 3 (by rfl) ⟨337622, by rfl⟩ : syracuseStep 1800653 = 675245) (by norm_num)
theorem B2701781 : Blo 1200417 2701781 := bbase (se 7 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 2701781 = 63323) (by norm_num)
theorem B1800677 : Blo 1200417 1800677 := bbase (se 4 (by rfl) ⟨168813, by rfl⟩ : syracuseStep 1800677 = 337627) (by norm_num)
theorem B1800701 : Blo 1200417 1800701 := bbase (se 3 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 1800701 = 675263) (by norm_num)
theorem B4053509 : Blo 1200417 4053509 := bbase (se 4 (by rfl) ⟨380016, by rfl⟩ : syracuseStep 4053509 = 760033) (by norm_num)
theorem B1800725 : Blo 1200417 1800725 := bbase (se 6 (by rfl) ⟨42204, by rfl⟩ : syracuseStep 1800725 = 84409) (by norm_num)
theorem B2701853 : Blo 1200417 2701853 := bbase (se 3 (by rfl) ⟨506597, by rfl⟩ : syracuseStep 2701853 = 1013195) (by norm_num)
theorem B1800749 : Blo 1200417 1800749 := bbase (se 3 (by rfl) ⟨337640, by rfl⟩ : syracuseStep 1800749 = 675281) (by norm_num)
theorem B1800773 : Blo 1200417 1800773 := bbase (se 4 (by rfl) ⟨168822, by rfl⟩ : syracuseStep 1800773 = 337645) (by norm_num)
theorem B6085205 : Blo 1200417 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B1800797 : Blo 1200417 1800797 := bbase (se 3 (by rfl) ⟨337649, by rfl⟩ : syracuseStep 1800797 = 675299) (by norm_num)
theorem B2701925 : Blo 1200417 2701925 := bbase (se 4 (by rfl) ⟨253305, by rfl⟩ : syracuseStep 2701925 = 506611) (by norm_num)
theorem B1800821 : Blo 1200417 1800821 := bbase (se 5 (by rfl) ⟨84413, by rfl⟩ : syracuseStep 1800821 = 168827) (by norm_num)
theorem B3422837 : Blo 1200417 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B1800845 : Blo 1200417 1800845 := bbase (se 3 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 1800845 = 675317) (by norm_num)
theorem B1800869 : Blo 1200417 1800869 := bbase (se 4 (by rfl) ⟨168831, by rfl⟩ : syracuseStep 1800869 = 337663) (by norm_num)
theorem B2701997 : Blo 1200417 2701997 := bbase (se 3 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 2701997 = 1013249) (by norm_num)
theorem B1800893 : Blo 1200417 1800893 := bbase (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) (by norm_num)
theorem B1800917 : Blo 1200417 1800917 := bbase (se 7 (by rfl) ⟨21104, by rfl⟩ : syracuseStep 1800917 = 42209) (by norm_num)
theorem B1710821 : Blo 1200417 1710821 := bbase (se 4 (by rfl) ⟨160389, by rfl⟩ : syracuseStep 1710821 = 320779) (by norm_num)
theorem B1800941 : Blo 1200417 1800941 := bbase (se 3 (by rfl) ⟨337676, by rfl⟩ : syracuseStep 1800941 = 675353) (by norm_num)
theorem B2702069 : Blo 1200417 2702069 := bbase (se 5 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 2702069 = 253319) (by norm_num)
theorem B1800965 : Blo 1200417 1800965 := bbase (se 4 (by rfl) ⟨168840, by rfl⟩ : syracuseStep 1800965 = 337681) (by norm_num)
theorem B1800989 : Blo 1200417 1800989 := bbase (se 3 (by rfl) ⟨337685, by rfl⟩ : syracuseStep 1800989 = 675371) (by norm_num)
theorem B1801013 : Blo 1200417 1801013 := bbase (se 5 (by rfl) ⟨84422, by rfl⟩ : syracuseStep 1801013 = 168845) (by norm_num)
theorem B4561717 : Blo 1200417 4561717 := bbase (se 5 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 4561717 = 427661) (by norm_num)
theorem B2702141 : Blo 1200417 2702141 := bbase (se 3 (by rfl) ⟨506651, by rfl⟩ : syracuseStep 2702141 = 1013303) (by norm_num)
theorem B1801037 : Blo 1200417 1801037 := bbase (se 3 (by rfl) ⟨337694, by rfl⟩ : syracuseStep 1801037 = 675389) (by norm_num)
theorem B1350481 : Blo 1200417 1350481 := bbase (se 2 (by rfl) ⟨506430, by rfl⟩ : syracuseStep 1350481 = 1012861) (by norm_num)
theorem B1801061 : Blo 1200417 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B1350517 : Blo 1200417 1350517 := bbase (se 5 (by rfl) ⟨63305, by rfl⟩ : syracuseStep 1350517 = 126611) (by norm_num)
theorem B1801085 : Blo 1200417 1801085 := bbase (se 3 (by rfl) ⟨337703, by rfl⟩ : syracuseStep 1801085 = 675407) (by norm_num)
theorem B2702213 : Blo 1200417 2702213 := bbase (se 4 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 2702213 = 506665) (by norm_num)
theorem B1801109 : Blo 1200417 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B1350553 : Blo 1200417 1350553 := bbase (se 2 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 1350553 = 1012915) (by norm_num)
theorem B1801133 : Blo 1200417 1801133 := bbase (se 3 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 1801133 = 675425) (by norm_num)
theorem B4053941 : Blo 1200417 4053941 := bbase (se 5 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 4053941 = 380057) (by norm_num)
theorem B1350589 : Blo 1200417 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B1801157 : Blo 1200417 1801157 := bbase (se 4 (by rfl) ⟨168858, by rfl⟩ : syracuseStep 1801157 = 337717) (by norm_num)
theorem B2702285 : Blo 1200417 2702285 := bbase (se 3 (by rfl) ⟨506678, by rfl⟩ : syracuseStep 2702285 = 1013357) (by norm_num)
theorem B1801181 : Blo 1200417 1801181 := bbase (se 3 (by rfl) ⟨337721, by rfl⟩ : syracuseStep 1801181 = 675443) (by norm_num)
theorem B1350625 : Blo 1200417 1350625 := bbase (se 2 (by rfl) ⟨506484, by rfl⟩ : syracuseStep 1350625 = 1012969) (by norm_num)
theorem B6077429 : Blo 1200417 6077429 := bbase (se 5 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 6077429 = 569759) (by norm_num)
theorem B1801205 : Blo 1200417 1801205 := bbase (se 5 (by rfl) ⟨84431, by rfl⟩ : syracuseStep 1801205 = 168863) (by norm_num)
theorem B1350661 : Blo 1200417 1350661 := bbase (se 4 (by rfl) ⟨126624, by rfl⟩ : syracuseStep 1350661 = 253249) (by norm_num)
theorem B1801229 : Blo 1200417 1801229 := bbase (se 3 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 1801229 = 675461) (by norm_num)
theorem B2702357 : Blo 1200417 2702357 := bbase (se 6 (by rfl) ⟨63336, by rfl⟩ : syracuseStep 2702357 = 126673) (by norm_num)
theorem B1801253 : Blo 1200417 1801253 := bbase (se 4 (by rfl) ⟨168867, by rfl⟩ : syracuseStep 1801253 = 337735) (by norm_num)
theorem B1350697 : Blo 1200417 1350697 := bbase (se 2 (by rfl) ⟨506511, by rfl⟩ : syracuseStep 1350697 = 1013023) (by norm_num)
theorem B1801277 : Blo 1200417 1801277 := bbase (se 3 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 1801277 = 675479) (by norm_num)
theorem B3513413 : Blo 1200417 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B1350733 : Blo 1200417 1350733 := bbase (se 3 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 1350733 = 506525) (by norm_num)
theorem B1801301 : Blo 1200417 1801301 := bbase (se 8 (by rfl) ⟨10554, by rfl⟩ : syracuseStep 1801301 = 21109) (by norm_num)
theorem B2702429 : Blo 1200417 2702429 := bbase (se 3 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 2702429 = 1013411) (by norm_num)
theorem B4562021 : Blo 1200417 4562021 := bbase (se 4 (by rfl) ⟨427689, by rfl⟩ : syracuseStep 4562021 = 855379) (by norm_num)
theorem B1801325 : Blo 1200417 1801325 := bbase (se 3 (by rfl) ⟨337748, by rfl⟩ : syracuseStep 1801325 = 675497) (by norm_num)
theorem B1350769 : Blo 1200417 1350769 := bbase (se 2 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 1350769 = 1013077) (by norm_num)
theorem B1801349 : Blo 1200417 1801349 := bbase (se 4 (by rfl) ⟨168876, by rfl⟩ : syracuseStep 1801349 = 337753) (by norm_num)
theorem B1350805 : Blo 1200417 1350805 := bbase (se 6 (by rfl) ⟨31659, by rfl⟩ : syracuseStep 1350805 = 63319) (by norm_num)
theorem B2776213 : Blo 1200417 2776213 := bbase (se 6 (by rfl) ⟨65067, by rfl⟩ : syracuseStep 2776213 = 130135) (by norm_num)
theorem B1801373 : Blo 1200417 1801373 := bbase (se 3 (by rfl) ⟨337757, by rfl⟩ : syracuseStep 1801373 = 675515) (by norm_num)
theorem B2702501 : Blo 1200417 2702501 := bbase (se 4 (by rfl) ⟨253359, by rfl⟩ : syracuseStep 2702501 = 506719) (by norm_num)
theorem B1801397 : Blo 1200417 1801397 := bbase (se 5 (by rfl) ⟨84440, by rfl⟩ : syracuseStep 1801397 = 168881) (by norm_num)
theorem B1350841 : Blo 1200417 1350841 := bbase (se 2 (by rfl) ⟨506565, by rfl⟩ : syracuseStep 1350841 = 1013131) (by norm_num)
theorem B1801421 : Blo 1200417 1801421 := bbase (se 3 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 1801421 = 675533) (by norm_num)
theorem B1350877 : Blo 1200417 1350877 := bbase (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) (by norm_num)
theorem B1801445 : Blo 1200417 1801445 := bbase (se 4 (by rfl) ⟨168885, by rfl⟩ : syracuseStep 1801445 = 337771) (by norm_num)
theorem B2702573 : Blo 1200417 2702573 := bbase (se 3 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 2702573 = 1013465) (by norm_num)
theorem B1801469 : Blo 1200417 1801469 := bbase (se 3 (by rfl) ⟨337775, by rfl⟩ : syracuseStep 1801469 = 675551) (by norm_num)
theorem B1350913 : Blo 1200417 1350913 := bbase (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) (by norm_num)
theorem B1711373 : Blo 1200417 1711373 := bbase (se 3 (by rfl) ⟨320882, by rfl⟩ : syracuseStep 1711373 = 641765) (by norm_num)
theorem B1801493 : Blo 1200417 1801493 := bbase (se 6 (by rfl) ⟨42222, by rfl⟩ : syracuseStep 1801493 = 84445) (by norm_num)
theorem B1924373 : Blo 1200417 1924373 := bbase (se 6 (by rfl) ⟨45102, by rfl⟩ : syracuseStep 1924373 = 90205) (by norm_num)
theorem B1350949 : Blo 1200417 1350949 := bbase (se 4 (by rfl) ⟨126651, by rfl⟩ : syracuseStep 1350949 = 253303) (by norm_num)
theorem B1801517 : Blo 1200417 1801517 := bbase (se 3 (by rfl) ⟨337784, by rfl⟩ : syracuseStep 1801517 = 675569) (by norm_num)
theorem B2702645 : Blo 1200417 2702645 := bbase (se 5 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 2702645 = 253373) (by norm_num)
theorem B1801541 : Blo 1200417 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B1350985 : Blo 1200417 1350985 := bbase (se 2 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 1350985 = 1013239) (by norm_num)
theorem B1801565 : Blo 1200417 1801565 := bbase (se 3 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 1801565 = 675587) (by norm_num)
theorem B4054373 : Blo 1200417 4054373 := bbase (se 4 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 4054373 = 760195) (by norm_num)
theorem B3038573 : Blo 1200417 3038573 := bbase (se 3 (by rfl) ⟨569732, by rfl⟩ : syracuseStep 3038573 = 1139465) (by norm_num)
theorem B1351021 : Blo 1200417 1351021 := bbase (se 3 (by rfl) ⟨253316, by rfl⟩ : syracuseStep 1351021 = 506633) (by norm_num)
theorem B10255733 : Blo 1200417 10255733 := bbase (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) (by norm_num)
theorem B1801589 : Blo 1200417 1801589 := bbase (se 5 (by rfl) ⟨84449, by rfl⟩ : syracuseStep 1801589 = 168899) (by norm_num)
theorem B6847861 : Blo 1200417 6847861 := bbase (se 5 (by rfl) ⟨320993, by rfl⟩ : syracuseStep 6847861 = 641987) (by norm_num)
theorem B2702717 : Blo 1200417 2702717 := bbase (se 3 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 2702717 = 1013519) (by norm_num)
theorem B1801613 : Blo 1200417 1801613 := bbase (se 3 (by rfl) ⟨337802, by rfl⟩ : syracuseStep 1801613 = 675605) (by norm_num)
theorem B1351057 : Blo 1200417 1351057 := bbase (se 2 (by rfl) ⟨506646, by rfl⟩ : syracuseStep 1351057 = 1013293) (by norm_num)
theorem B1924501 : Blo 1200417 1924501 := bbase (se 6 (by rfl) ⟨45105, by rfl⟩ : syracuseStep 1924501 = 90211) (by norm_num)
theorem B1801637 : Blo 1200417 1801637 := bbase (se 4 (by rfl) ⟨168903, by rfl⟩ : syracuseStep 1801637 = 337807) (by norm_num)
theorem B1351093 : Blo 1200417 1351093 := bbase (se 5 (by rfl) ⟨63332, by rfl⟩ : syracuseStep 1351093 = 126665) (by norm_num)
theorem B1801661 : Blo 1200417 1801661 := bbase (se 3 (by rfl) ⟨337811, by rfl⟩ : syracuseStep 1801661 = 675623) (by norm_num)
theorem B2702789 : Blo 1200417 2702789 := bbase (se 4 (by rfl) ⟨253386, by rfl⟩ : syracuseStep 2702789 = 506773) (by norm_num)
theorem B1801685 : Blo 1200417 1801685 := bbase (se 7 (by rfl) ⟨21113, by rfl⟩ : syracuseStep 1801685 = 42227) (by norm_num)
theorem B1351129 : Blo 1200417 1351129 := bbase (se 2 (by rfl) ⟨506673, by rfl⟩ : syracuseStep 1351129 = 1013347) (by norm_num)
theorem B1801709 : Blo 1200417 1801709 := bbase (se 3 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 1801709 = 675641) (by norm_num)
theorem B1351165 : Blo 1200417 1351165 := bbase (se 3 (by rfl) ⟨253343, by rfl⟩ : syracuseStep 1351165 = 506687) (by norm_num)
theorem B1801733 : Blo 1200417 1801733 := bbase (se 4 (by rfl) ⟨168912, by rfl⟩ : syracuseStep 1801733 = 337825) (by norm_num)
theorem B2702861 : Blo 1200417 2702861 := bbase (se 3 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 2702861 = 1013573) (by norm_num)
theorem B1801757 : Blo 1200417 1801757 := bbase (se 3 (by rfl) ⟨337829, by rfl⟩ : syracuseStep 1801757 = 675659) (by norm_num)
theorem B1351201 : Blo 1200417 1351201 := bbase (se 2 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 1351201 = 1013401) (by norm_num)
theorem B1801781 : Blo 1200417 1801781 := bbase (se 5 (by rfl) ⟨84458, by rfl⟩ : syracuseStep 1801781 = 168917) (by norm_num)
theorem B2924093 : Blo 1200417 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B1351237 : Blo 1200417 1351237 := bbase (se 4 (by rfl) ⟨126678, by rfl⟩ : syracuseStep 1351237 = 253357) (by norm_num)
theorem B1801805 : Blo 1200417 1801805 := bbase (se 3 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 1801805 = 675677) (by norm_num)
theorem B25042517 : Blo 1200417 25042517 := bbase (se 8 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 25042517 = 293467) (by norm_num)
theorem B2702933 : Blo 1200417 2702933 := bbase (se 8 (by rfl) ⟨15837, by rfl⟩ : syracuseStep 2702933 = 31675) (by norm_num)
theorem B3423829 : Blo 1200417 3423829 := bbase (se 8 (by rfl) ⟨20061, by rfl⟩ : syracuseStep 3423829 = 40123) (by norm_num)
theorem B1801829 : Blo 1200417 1801829 := bbase (se 4 (by rfl) ⟨168921, by rfl⟩ : syracuseStep 1801829 = 337843) (by norm_num)
theorem B1351273 : Blo 1200417 1351273 := bbase (se 2 (by rfl) ⟨506727, by rfl⟩ : syracuseStep 1351273 = 1013455) (by norm_num)
theorem B1801853 : Blo 1200417 1801853 := bbase (se 3 (by rfl) ⟨337847, by rfl⟩ : syracuseStep 1801853 = 675695) (by norm_num)
theorem B1351309 : Blo 1200417 1351309 := bbase (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) (by norm_num)
theorem B1801877 : Blo 1200417 1801877 := bbase (se 6 (by rfl) ⟨42231, by rfl⟩ : syracuseStep 1801877 = 84463) (by norm_num)
theorem B2703005 : Blo 1200417 2703005 := bbase (se 3 (by rfl) ⟨506813, by rfl⟩ : syracuseStep 2703005 = 1013627) (by norm_num)
theorem B1801901 : Blo 1200417 1801901 := bbase (se 3 (by rfl) ⟨337856, by rfl⟩ : syracuseStep 1801901 = 675713) (by norm_num)
theorem B1351345 : Blo 1200417 1351345 := bbase (se 2 (by rfl) ⟨506754, by rfl⟩ : syracuseStep 1351345 = 1013509) (by norm_num)
theorem B2924221 : Blo 1200417 2924221 := bbase (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) (by norm_num)
theorem B3038917 : Blo 1200417 3038917 := bbase (se 4 (by rfl) ⟨284898, by rfl⟩ : syracuseStep 3038917 = 569797) (by norm_num)
theorem B1801925 : Blo 1200417 1801925 := bbase (se 4 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 1801925 = 337861) (by norm_num)
theorem B1351381 : Blo 1200417 1351381 := bbase (se 7 (by rfl) ⟨15836, by rfl⟩ : syracuseStep 1351381 = 31673) (by norm_num)
theorem B1801949 : Blo 1200417 1801949 := bbase (se 3 (by rfl) ⟨337865, by rfl⟩ : syracuseStep 1801949 = 675731) (by norm_num)
theorem B2703077 : Blo 1200417 2703077 := bbase (se 4 (by rfl) ⟨253413, by rfl⟩ : syracuseStep 2703077 = 506827) (by norm_num)
theorem B1801973 : Blo 1200417 1801973 := bbase (se 5 (by rfl) ⟨84467, by rfl⟩ : syracuseStep 1801973 = 168935) (by norm_num)
theorem B9125621 : Blo 1200417 9125621 := bbase (se 5 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 9125621 = 855527) (by norm_num)
theorem B1351417 : Blo 1200417 1351417 := bbase (se 2 (by rfl) ⟨506781, by rfl⟩ : syracuseStep 1351417 = 1013563) (by norm_num)
theorem B1801997 : Blo 1200417 1801997 := bbase (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) (by norm_num)
theorem B4054805 : Blo 1200417 4054805 := bbase (se 6 (by rfl) ⟨95034, by rfl⟩ : syracuseStep 4054805 = 190069) (by norm_num)
theorem B1924885 : Blo 1200417 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B1351453 : Blo 1200417 1351453 := bbase (se 3 (by rfl) ⟨253397, by rfl⟩ : syracuseStep 1351453 = 506795) (by norm_num)
theorem B1802021 : Blo 1200417 1802021 := bbase (se 4 (by rfl) ⟨168939, by rfl⟩ : syracuseStep 1802021 = 337879) (by norm_num)
theorem B2703149 : Blo 1200417 2703149 := bbase (se 3 (by rfl) ⟨506840, by rfl⟩ : syracuseStep 2703149 = 1013681) (by norm_num)
theorem B3039029 : Blo 1200417 3039029 := bbase (se 5 (by rfl) ⟨142454, by rfl⟩ : syracuseStep 3039029 = 284909) (by norm_num)
theorem B1802045 : Blo 1200417 1802045 := bbase (se 3 (by rfl) ⟨337883, by rfl⟩ : syracuseStep 1802045 = 675767) (by norm_num)
theorem B1351489 : Blo 1200417 1351489 := bbase (se 2 (by rfl) ⟨506808, by rfl⟩ : syracuseStep 1351489 = 1013617) (by norm_num)
theorem B4874053 : Blo 1200417 4874053 := bbase (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) (by norm_num)
theorem B1802069 : Blo 1200417 1802069 := bbase (se 9 (by rfl) ⟨5279, by rfl⟩ : syracuseStep 1802069 = 10559) (by norm_num)
theorem B1351525 : Blo 1200417 1351525 := bbase (se 4 (by rfl) ⟨126705, by rfl⟩ : syracuseStep 1351525 = 253411) (by norm_num)
theorem B6086501 : Blo 1200417 6086501 := bbase (se 4 (by rfl) ⟨570609, by rfl⟩ : syracuseStep 6086501 = 1141219) (by norm_num)
theorem B1802093 : Blo 1200417 1802093 := bbase (se 3 (by rfl) ⟨337892, by rfl⟩ : syracuseStep 1802093 = 675785) (by norm_num)
theorem B2703221 : Blo 1200417 2703221 := bbase (se 5 (by rfl) ⟨126713, by rfl⟩ : syracuseStep 2703221 = 253427) (by norm_num)
theorem B1802117 : Blo 1200417 1802117 := bbase (se 4 (by rfl) ⟨168948, by rfl⟩ : syracuseStep 1802117 = 337897) (by norm_num)
theorem B1351561 : Blo 1200417 1351561 := bbase (se 2 (by rfl) ⟨506835, by rfl⟩ : syracuseStep 1351561 = 1013671) (by norm_num)
theorem B1802141 : Blo 1200417 1802141 := bbase (se 3 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 1802141 = 675803) (by norm_num)
theorem B1351597 : Blo 1200417 1351597 := bbase (se 3 (by rfl) ⟨253424, by rfl⟩ : syracuseStep 1351597 = 506849) (by norm_num)
theorem B1802165 : Blo 1200417 1802165 := bbase (se 5 (by rfl) ⟨84476, by rfl⟩ : syracuseStep 1802165 = 168953) (by norm_num)
theorem B2703293 : Blo 1200417 2703293 := bbase (se 3 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 2703293 = 1013735) (by norm_num)
theorem B2564045 : Blo 1200417 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B1802189 : Blo 1200417 1802189 := bbase (se 3 (by rfl) ⟨337910, by rfl⟩ : syracuseStep 1802189 = 675821) (by norm_num)
theorem B1351633 : Blo 1200417 1351633 := bbase (se 2 (by rfl) ⟨506862, by rfl⟩ : syracuseStep 1351633 = 1013725) (by norm_num)
theorem B1802213 : Blo 1200417 1802213 := bbase (se 4 (by rfl) ⟨168957, by rfl⟩ : syracuseStep 1802213 = 337915) (by norm_num)
theorem B3039221 : Blo 1200417 3039221 := bbase (se 5 (by rfl) ⟨142463, by rfl⟩ : syracuseStep 3039221 = 284927) (by norm_num)
theorem B1351669 : Blo 1200417 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B1802237 : Blo 1200417 1802237 := bbase (se 3 (by rfl) ⟨337919, by rfl⟩ : syracuseStep 1802237 = 675839) (by norm_num)
theorem B1802243 : Blo 1200417 1802243 := bstep (se 1 (by rfl) ⟨1351682, by rfl⟩ : syracuseStep 1802243 = 2703365) B2703365
theorem B1802273 : Blo 1200417 1802273 := bstep (se 2 (by rfl) ⟨675852, by rfl⟩ : syracuseStep 1802273 = 1351705) B1351705
theorem B4055075 : Blo 1200417 4055075 := bstep (se 1 (by rfl) ⟨3041306, by rfl⟩ : syracuseStep 4055075 = 6082613) B6082613
theorem B4562993 : Blo 1200417 4562993 := bstep (se 2 (by rfl) ⟨1711122, by rfl⟩ : syracuseStep 4562993 = 3422245) B3422245
theorem B1802291 : Blo 1200417 1802291 := bstep (se 1 (by rfl) ⟨1351718, by rfl⟩ : syracuseStep 1802291 = 2703437) B2703437
theorem B6840389 : Blo 1200417 6840389 := bstep (se 4 (by rfl) ⟨641286, by rfl⟩ : syracuseStep 6840389 = 1282573) B1282573
theorem B1802321 : Blo 1200417 1802321 := bstep (se 2 (by rfl) ⟨675870, by rfl⟩ : syracuseStep 1802321 = 1351741) B1351741
theorem B10256483 : Blo 1200417 10256483 := bstep (se 1 (by rfl) ⟨7692362, by rfl⟩ : syracuseStep 10256483 = 15384725) B15384725
theorem B6078563 : Blo 1200417 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B1802339 : Blo 1200417 1802339 := bstep (se 1 (by rfl) ⟨1351754, by rfl⟩ : syracuseStep 1802339 = 2703509) B2703509
theorem B2703473 : Blo 1200417 2703473 := bstep (se 2 (by rfl) ⟨1013802, by rfl⟩ : syracuseStep 2703473 = 2027605) B2027605
theorem B1351795 : Blo 1200417 1351795 := bstep (se 1 (by rfl) ⟨1013846, by rfl⟩ : syracuseStep 1351795 = 2027693) B2027693
theorem B1802369 : Blo 1200417 1802369 := bstep (se 2 (by rfl) ⟨675888, by rfl⟩ : syracuseStep 1802369 = 1351777) B1351777
theorem B2703491 : Blo 1200417 2703491 := bstep (se 1 (by rfl) ⟨2027618, by rfl⟩ : syracuseStep 2703491 = 4055237) B4055237
theorem B9748621 : Blo 1200417 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B1802387 : Blo 1200417 1802387 := bstep (se 1 (by rfl) ⟨1351790, by rfl⟩ : syracuseStep 1802387 = 2703581) B2703581
theorem B1802417 : Blo 1200417 1802417 := bstep (se 2 (by rfl) ⟨675906, by rfl⟩ : syracuseStep 1802417 = 1351813) B1351813
theorem B1802435 : Blo 1200417 1802435 := bstep (se 1 (by rfl) ⟨1351826, by rfl⟩ : syracuseStep 1802435 = 2703653) B2703653
theorem B1802465 : Blo 1200417 1802465 := bstep (se 2 (by rfl) ⟨675924, by rfl⟩ : syracuseStep 1802465 = 1351849) B1351849
theorem B1802483 : Blo 1200417 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B1351939 : Blo 1200417 1351939 := bstep (se 1 (by rfl) ⟨1013954, by rfl⟩ : syracuseStep 1351939 = 2027909) B2027909
theorem B1802513 : Blo 1200417 1802513 := bstep (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) B1351885
theorem B1802531 : Blo 1200417 1802531 := bstep (se 1 (by rfl) ⟨1351898, by rfl⟩ : syracuseStep 1802531 = 2703797) B2703797
theorem B4055345 : Blo 1200417 4055345 := bstep (se 2 (by rfl) ⟨1520754, by rfl⟩ : syracuseStep 4055345 = 3041509) B3041509
theorem B1802561 : Blo 1200417 1802561 := bstep (se 2 (by rfl) ⟨675960, by rfl⟩ : syracuseStep 1802561 = 1351921) B1351921
theorem B4874573 : Blo 1200417 4874573 := bstep (se 3 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 4874573 = 1827965) B1827965
theorem B1802579 : Blo 1200417 1802579 := bstep (se 1 (by rfl) ⟨1351934, by rfl⟩ : syracuseStep 1802579 = 2703869) B2703869
theorem B1802609 : Blo 1200417 1802609 := bstep (se 2 (by rfl) ⟨675978, by rfl⟩ : syracuseStep 1802609 = 1351957) B1351957
theorem B1802627 : Blo 1200417 1802627 := bstep (se 1 (by rfl) ⟨1351970, by rfl⟩ : syracuseStep 1802627 = 2703941) B2703941
theorem B2564497 : Blo 1200417 2564497 := bstep (se 2 (by rfl) ⟨961686, by rfl⟩ : syracuseStep 2564497 = 1923373) B1923373
theorem B2703761 : Blo 1200417 2703761 := bstep (se 2 (by rfl) ⟨1013910, by rfl⟩ : syracuseStep 2703761 = 2027821) B2027821
theorem B1352083 : Blo 1200417 1352083 := bstep (se 1 (by rfl) ⟨1014062, by rfl⟩ : syracuseStep 1352083 = 2028125) B2028125
theorem B1802657 : Blo 1200417 1802657 := bstep (se 2 (by rfl) ⟨675996, by rfl⟩ : syracuseStep 1802657 = 1351993) B1351993
theorem B1622435 : Blo 1200417 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B2703779 : Blo 1200417 2703779 := bstep (se 1 (by rfl) ⟨2027834, by rfl⟩ : syracuseStep 2703779 = 4055669) B4055669
theorem B1802675 : Blo 1200417 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B38986181 : Blo 1200417 38986181 := bstep (se 4 (by rfl) ⟨3654954, by rfl⟩ : syracuseStep 38986181 = 7309909) B7309909
theorem B1802705 : Blo 1200417 1802705 := bstep (se 2 (by rfl) ⟨676014, by rfl⟩ : syracuseStep 1802705 = 1352029) B1352029
theorem B1827283 : Blo 1200417 1827283 := bstep (se 1 (by rfl) ⟨1370462, by rfl⟩ : syracuseStep 1827283 = 2740925) B2740925
theorem B1802723 : Blo 1200417 1802723 := bstep (se 1 (by rfl) ⟨1352042, by rfl⟩ : syracuseStep 1802723 = 2704085) B2704085
theorem B1925603 : Blo 1200417 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1802753 : Blo 1200417 1802753 := bstep (se 2 (by rfl) ⟨676032, by rfl⟩ : syracuseStep 1802753 = 1352065) B1352065
theorem B6840845 : Blo 1200417 6840845 := bstep (se 3 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 6840845 = 2565317) B2565317
theorem B1802771 : Blo 1200417 1802771 := bstep (se 1 (by rfl) ⟨1352078, by rfl⟩ : syracuseStep 1802771 = 2704157) B2704157
theorem B1352227 : Blo 1200417 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B1802801 : Blo 1200417 1802801 := bstep (se 2 (by rfl) ⟨676050, by rfl⟩ : syracuseStep 1802801 = 1352101) B1352101
theorem B1802819 : Blo 1200417 1802819 := bstep (se 1 (by rfl) ⟨1352114, by rfl⟩ : syracuseStep 1802819 = 2704229) B2704229
theorem B1925699 : Blo 1200417 1925699 := bstep (se 1 (by rfl) ⟨1444274, by rfl⟩ : syracuseStep 1925699 = 2888549) B2888549
theorem B1802849 : Blo 1200417 1802849 := bstep (se 2 (by rfl) ⟨676068, by rfl⟩ : syracuseStep 1802849 = 1352137) B1352137
theorem B1925731 : Blo 1200417 1925731 := bstep (se 1 (by rfl) ⟨1444298, by rfl⟩ : syracuseStep 1925731 = 2888597) B2888597
theorem B14615153 : Blo 1200417 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1802867 : Blo 1200417 1802867 := bstep (se 1 (by rfl) ⟨1352150, by rfl⟩ : syracuseStep 1802867 = 2704301) B2704301
theorem B3039889 : Blo 1200417 3039889 := bstep (se 2 (by rfl) ⟨1139958, by rfl⟩ : syracuseStep 3039889 = 2279917) B2279917
theorem B1802897 : Blo 1200417 1802897 := bstep (se 2 (by rfl) ⟨676086, by rfl⟩ : syracuseStep 1802897 = 1352173) B1352173
theorem B3850897 : Blo 1200417 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B1802915 : Blo 1200417 1802915 := bstep (se 1 (by rfl) ⟨1352186, by rfl⟩ : syracuseStep 1802915 = 2704373) B2704373
theorem B2704049 : Blo 1200417 2704049 := bstep (se 2 (by rfl) ⟨1014018, by rfl⟩ : syracuseStep 2704049 = 2028037) B2028037
theorem B1352371 : Blo 1200417 1352371 := bstep (se 1 (by rfl) ⟨1014278, by rfl⟩ : syracuseStep 1352371 = 2028557) B2028557
theorem B1802945 : Blo 1200417 1802945 := bstep (se 2 (by rfl) ⟨676104, by rfl⟩ : syracuseStep 1802945 = 1352209) B1352209
theorem B2704067 : Blo 1200417 2704067 := bstep (se 1 (by rfl) ⟨2028050, by rfl⟩ : syracuseStep 2704067 = 4056101) B4056101
theorem B4563661 : Blo 1200417 4563661 := bstep (se 3 (by rfl) ⟨855686, by rfl⟩ : syracuseStep 4563661 = 1711373) B1711373
theorem B1802963 : Blo 1200417 1802963 := bstep (se 1 (by rfl) ⟨1352222, by rfl⟩ : syracuseStep 1802963 = 2704445) B2704445
theorem B1802993 : Blo 1200417 1802993 := bstep (se 2 (by rfl) ⟨676122, by rfl⟩ : syracuseStep 1802993 = 1352245) B1352245
theorem B1803011 : Blo 1200417 1803011 := bstep (se 1 (by rfl) ⟨1352258, by rfl⟩ : syracuseStep 1803011 = 2704517) B2704517
theorem B1803041 : Blo 1200417 1803041 := bstep (se 2 (by rfl) ⟨676140, by rfl⟩ : syracuseStep 1803041 = 1352281) B1352281
theorem B1803059 : Blo 1200417 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B1352515 : Blo 1200417 1352515 := bstep (se 1 (by rfl) ⟨1014386, by rfl⟩ : syracuseStep 1352515 = 2028773) B2028773
theorem B4055885 : Blo 1200417 4055885 := bstep (se 3 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 4055885 = 1520957) B1520957
theorem B1803089 : Blo 1200417 1803089 := bstep (se 2 (by rfl) ⟨676158, by rfl⟩ : syracuseStep 1803089 = 1352317) B1352317
theorem B1803107 : Blo 1200417 1803107 := bstep (se 1 (by rfl) ⟨1352330, by rfl⟩ : syracuseStep 1803107 = 2704661) B2704661
theorem B1803137 : Blo 1200417 1803137 := bstep (se 2 (by rfl) ⟨676176, by rfl⟩ : syracuseStep 1803137 = 1352353) B1352353
theorem B4055939 : Blo 1200417 4055939 := bstep (se 1 (by rfl) ⟨3041954, by rfl⟩ : syracuseStep 4055939 = 6083909) B6083909
theorem B6079373 : Blo 1200417 6079373 := bstep (se 3 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 6079373 = 2279765) B2279765
theorem B1803155 : Blo 1200417 1803155 := bstep (se 1 (by rfl) ⟨1352366, by rfl⟩ : syracuseStep 1803155 = 2704733) B2704733
theorem B3040163 : Blo 1200417 3040163 := bstep (se 1 (by rfl) ⟨2280122, by rfl⟩ : syracuseStep 3040163 = 4560245) B4560245
theorem B8217521 : Blo 1200417 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B1803185 : Blo 1200417 1803185 := bstep (se 2 (by rfl) ⟨676194, by rfl⟩ : syracuseStep 1803185 = 1352389) B1352389
theorem B1803203 : Blo 1200417 1803203 := bstep (se 1 (by rfl) ⟨1352402, by rfl⟩ : syracuseStep 1803203 = 2704805) B2704805
theorem B2704337 : Blo 1200417 2704337 := bstep (se 2 (by rfl) ⟨1014126, by rfl⟩ : syracuseStep 2704337 = 2028253) B2028253
theorem B1352659 : Blo 1200417 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B1803233 : Blo 1200417 1803233 := bstep (se 2 (by rfl) ⟨676212, by rfl⟩ : syracuseStep 1803233 = 1352425) B1352425
theorem B2704355 : Blo 1200417 2704355 := bstep (se 1 (by rfl) ⟨2028266, by rfl⟩ : syracuseStep 2704355 = 4056533) B4056533
theorem B1803251 : Blo 1200417 1803251 := bstep (se 1 (by rfl) ⟨1352438, by rfl⟩ : syracuseStep 1803251 = 2704877) B2704877
theorem B1803281 : Blo 1200417 1803281 := bstep (se 2 (by rfl) ⟨676230, by rfl⟩ : syracuseStep 1803281 = 1352461) B1352461
theorem B1541155 : Blo 1200417 1541155 := bstep (se 1 (by rfl) ⟨1155866, by rfl⟩ : syracuseStep 1541155 = 2311733) B2311733
theorem B1803299 : Blo 1200417 1803299 := bstep (se 1 (by rfl) ⟨1352474, by rfl⟩ : syracuseStep 1803299 = 2704949) B2704949
theorem B1803329 : Blo 1200417 1803329 := bstep (se 2 (by rfl) ⟨676248, by rfl⟩ : syracuseStep 1803329 = 1352497) B1352497
theorem B1803347 : Blo 1200417 1803347 := bstep (se 1 (by rfl) ⟨1352510, by rfl⟩ : syracuseStep 1803347 = 2705021) B2705021
theorem B3040355 : Blo 1200417 3040355 := bstep (se 1 (by rfl) ⟨2280266, by rfl⟩ : syracuseStep 3040355 = 4560533) B4560533
theorem B1803377 : Blo 1200417 1803377 := bstep (se 2 (by rfl) ⟨676266, by rfl⟩ : syracuseStep 1803377 = 1352533) B1352533
theorem B1803395 : Blo 1200417 1803395 := bstep (se 1 (by rfl) ⟨1352546, by rfl⟩ : syracuseStep 1803395 = 2705093) B2705093
theorem B4056209 : Blo 1200417 4056209 := bstep (se 2 (by rfl) ⟨1521078, by rfl⟩ : syracuseStep 4056209 = 3042157) B3042157
theorem B1803425 : Blo 1200417 1803425 := bstep (se 2 (by rfl) ⟨676284, by rfl⟩ : syracuseStep 1803425 = 1352569) B1352569
theorem B2565283 : Blo 1200417 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1803443 : Blo 1200417 1803443 := bstep (se 1 (by rfl) ⟨1352582, by rfl⟩ : syracuseStep 1803443 = 2705165) B2705165
theorem B13173941 : Blo 1200417 13173941 := bstep (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) B1235057
theorem B1803473 : Blo 1200417 1803473 := bstep (se 2 (by rfl) ⟨676302, by rfl⟩ : syracuseStep 1803473 = 1352605) B1352605
theorem B2082017 : Blo 1200417 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B1803491 : Blo 1200417 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B2704625 : Blo 1200417 2704625 := bstep (se 2 (by rfl) ⟨1014234, by rfl⟩ : syracuseStep 2704625 = 2028469) B2028469
theorem B1803521 : Blo 1200417 1803521 := bstep (se 2 (by rfl) ⟨676320, by rfl⟩ : syracuseStep 1803521 = 1352641) B1352641
theorem B2704643 : Blo 1200417 2704643 := bstep (se 1 (by rfl) ⟨2028482, by rfl⟩ : syracuseStep 2704643 = 4056965) B4056965
theorem B1803539 : Blo 1200417 1803539 := bstep (se 1 (by rfl) ⟨1352654, by rfl⟩ : syracuseStep 1803539 = 2705309) B2705309
theorem B5129507 : Blo 1200417 5129507 := bstep (se 1 (by rfl) ⟨3847130, by rfl⟩ : syracuseStep 5129507 = 7694261) B7694261
theorem B1803569 : Blo 1200417 1803569 := bstep (se 2 (by rfl) ⟨676338, by rfl⟩ : syracuseStep 1803569 = 1352677) B1352677
theorem B1803587 : Blo 1200417 1803587 := bstep (se 1 (by rfl) ⟨1352690, by rfl⟩ : syracuseStep 1803587 = 2705381) B2705381
theorem B1803617 : Blo 1200417 1803617 := bstep (se 2 (by rfl) ⟨676356, by rfl⟩ : syracuseStep 1803617 = 1352713) B1352713
theorem B6161827 : Blo 1200417 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B4564451 : Blo 1200417 4564451 := bstep (se 1 (by rfl) ⟨3423338, by rfl⟩ : syracuseStep 4564451 = 6846677) B6846677
theorem B2704913 : Blo 1200417 2704913 := bstep (se 2 (by rfl) ⟨1014342, by rfl⟩ : syracuseStep 2704913 = 2028685) B2028685
theorem B2704931 : Blo 1200417 2704931 := bstep (se 1 (by rfl) ⟨2028698, by rfl⟩ : syracuseStep 2704931 = 4057397) B4057397
theorem B2434627 : Blo 1200417 2434627 := bstep (se 1 (by rfl) ⟨1825970, by rfl⟩ : syracuseStep 2434627 = 3651941) B3651941
theorem B9127565 : Blo 1200417 9127565 := bstep (se 3 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 9127565 = 3422837) B3422837
theorem B4056749 : Blo 1200417 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B4056803 : Blo 1200417 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B1443587 : Blo 1200417 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B3655469 : Blo 1200417 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B2705201 : Blo 1200417 2705201 := bstep (se 2 (by rfl) ⟨1014450, by rfl⟩ : syracuseStep 2705201 = 2028901) B2028901
theorem B12994357 : Blo 1200417 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B2705219 : Blo 1200417 2705219 := bstep (se 1 (by rfl) ⟨2028914, by rfl⟩ : syracuseStep 2705219 = 4057829) B4057829
theorem B11544389 : Blo 1200417 11544389 := bstep (se 4 (by rfl) ⟨1082286, by rfl⟩ : syracuseStep 11544389 = 2164573) B2164573
theorem B2279249 : Blo 1200417 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B2566001 : Blo 1200417 2566001 := bstep (se 2 (by rfl) ⟨962250, by rfl⟩ : syracuseStep 2566001 = 1924501) B1924501
theorem B4057073 : Blo 1200417 4057073 := bstep (se 2 (by rfl) ⟨1521402, by rfl⟩ : syracuseStep 4057073 = 3042805) B3042805
theorem B3041297 : Blo 1200417 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B2738225 : Blo 1200417 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B3041347 : Blo 1200417 3041347 := bstep (se 1 (by rfl) ⟨2281010, by rfl⟩ : syracuseStep 3041347 = 4562021) B4562021
theorem B4565105 : Blo 1200417 4565105 := bstep (se 2 (by rfl) ⟨1711914, by rfl⟩ : syracuseStep 4565105 = 3423829) B3423829
theorem B3041489 : Blo 1200417 3041489 := bstep (se 2 (by rfl) ⟨1140558, by rfl⟩ : syracuseStep 3041489 = 2281117) B2281117
theorem B2025715 : Blo 1200417 2025715 := bstep (se 1 (by rfl) ⟨1519286, by rfl⟩ : syracuseStep 2025715 = 3038573) B3038573
theorem B4327793 : Blo 1200417 4327793 := bstep (se 2 (by rfl) ⟨1622922, by rfl⟩ : syracuseStep 4327793 = 3245845) B3245845
theorem B2566513 : Blo 1200417 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B2025857 : Blo 1200417 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B6498737 : Blo 1200417 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B16452067 : Blo 1200417 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B2025985 : Blo 1200417 2025985 := bstep (se 2 (by rfl) ⟨759744, by rfl⟩ : syracuseStep 2025985 = 1519489) B1519489
theorem B4057613 : Blo 1200417 4057613 := bstep (se 3 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 4057613 = 1521605) B1521605
theorem B2026019 : Blo 1200417 2026019 := bstep (se 1 (by rfl) ⟨1519514, by rfl⟩ : syracuseStep 2026019 = 3039029) B3039029
theorem B7801379 : Blo 1200417 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B4057667 : Blo 1200417 4057667 := bstep (se 1 (by rfl) ⟨3043250, by rfl⟩ : syracuseStep 4057667 = 6086501) B6086501
theorem B2026147 : Blo 1200417 2026147 := bstep (se 1 (by rfl) ⟨1519610, by rfl⟩ : syracuseStep 2026147 = 3039221) B3039221
theorem B2280145 : Blo 1200417 2280145 := bstep (se 2 (by rfl) ⟨855054, by rfl⟩ : syracuseStep 2280145 = 1710109) B1710109
theorem B2738947 : Blo 1200417 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B3656465 : Blo 1200417 3656465 := bstep (se 2 (by rfl) ⟨1371174, by rfl⟩ : syracuseStep 3656465 = 2742349) B2742349
theorem B2026289 : Blo 1200417 2026289 := bstep (se 2 (by rfl) ⟨759858, by rfl⟩ : syracuseStep 2026289 = 1519717) B1519717
theorem B4057937 : Blo 1200417 4057937 := bstep (se 2 (by rfl) ⟨1521726, by rfl⟩ : syracuseStep 4057937 = 3043453) B3043453
theorem B2280305 : Blo 1200417 2280305 := bstep (se 2 (by rfl) ⟨855114, by rfl⟩ : syracuseStep 2280305 = 1710229) B1710229
theorem B2026417 : Blo 1200417 2026417 := bstep (se 2 (by rfl) ⟨759906, by rfl⟩ : syracuseStep 2026417 = 1519813) B1519813
theorem B2026451 : Blo 1200417 2026451 := bstep (se 1 (by rfl) ⟨1519838, by rfl⟩ : syracuseStep 2026451 = 3039677) B3039677
theorem B4328483 : Blo 1200417 4328483 := bstep (se 1 (by rfl) ⟨3246362, by rfl⟩ : syracuseStep 4328483 = 6492725) B6492725
theorem B2026579 : Blo 1200417 2026579 := bstep (se 1 (by rfl) ⟨1519934, by rfl⟩ : syracuseStep 2026579 = 3039869) B3039869
theorem B7703693 : Blo 1200417 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B3042481 : Blo 1200417 3042481 := bstep (se 2 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 3042481 = 2281861) B2281861
theorem B2026721 : Blo 1200417 2026721 := bstep (se 2 (by rfl) ⟨760020, by rfl⟩ : syracuseStep 2026721 = 1520041) B1520041
theorem B2280707 : Blo 1200417 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B2026849 : Blo 1200417 2026849 := bstep (se 2 (by rfl) ⟨760068, by rfl⟩ : syracuseStep 2026849 = 1520137) B1520137
theorem B6843761 : Blo 1200417 6843761 := bstep (se 2 (by rfl) ⟨2566410, by rfl⟩ : syracuseStep 6843761 = 5132821) B5132821
theorem B2026883 : Blo 1200417 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B3755459 : Blo 1200417 3755459 := bstep (se 1 (by rfl) ⟨2816594, by rfl⟩ : syracuseStep 3755459 = 5633189) B5633189
theorem B14806469 : Blo 1200417 14806469 := bstep (se 4 (by rfl) ⟨1388106, by rfl⟩ : syracuseStep 14806469 = 2776213) B2776213
theorem B3042755 : Blo 1200417 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B2027011 : Blo 1200417 2027011 := bstep (se 1 (by rfl) ⟨1520258, by rfl⟩ : syracuseStep 2027011 = 3040517) B3040517
theorem B30797333 : Blo 1200417 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B3247661 : Blo 1200417 3247661 := bstep (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) B1217873
theorem B3419729 : Blo 1200417 3419729 := bstep (se 2 (by rfl) ⟨1282398, by rfl⟩ : syracuseStep 3419729 = 2564797) B2564797
theorem B2600579 : Blo 1200417 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B3042947 : Blo 1200417 3042947 := bstep (se 1 (by rfl) ⟨2282210, by rfl⟩ : syracuseStep 3042947 = 4564421) B4564421
theorem B2027153 : Blo 1200417 2027153 := bstep (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) B1520365
theorem B6082289 : Blo 1200417 6082289 := bstep (se 2 (by rfl) ⟨2280858, by rfl⟩ : syracuseStep 6082289 = 4561717) B4561717
theorem B3419921 : Blo 1200417 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B2027281 : Blo 1200417 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B2166563 : Blo 1200417 2166563 := bstep (se 1 (by rfl) ⟨1624922, by rfl⟩ : syracuseStep 2166563 = 3249845) B3249845
theorem B2027315 : Blo 1200417 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B2568017 : Blo 1200417 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B6500209 : Blo 1200417 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B1281907 : Blo 1200417 1281907 := bstep (se 1 (by rfl) ⟨961430, by rfl⟩ : syracuseStep 1281907 = 1922861) B1922861
theorem B2027443 : Blo 1200417 2027443 := bstep (se 1 (by rfl) ⟨1520582, by rfl⟩ : syracuseStep 2027443 = 3041165) B3041165
theorem B1519555 : Blo 1200417 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B9121733 : Blo 1200417 9121733 := bstep (se 4 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 9121733 = 1710325) B1710325
theorem B1519651 : Blo 1200417 1519651 := bstep (se 1 (by rfl) ⟨1139738, by rfl⟩ : syracuseStep 1519651 = 2279477) B2279477
theorem B2027585 : Blo 1200417 2027585 := bstep (se 2 (by rfl) ⟨760344, by rfl⟩ : syracuseStep 2027585 = 1520689) B1520689
theorem B1282163 : Blo 1200417 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B2281603 : Blo 1200417 2281603 := bstep (se 1 (by rfl) ⟨1711202, by rfl⟩ : syracuseStep 2281603 = 3422405) B3422405
theorem B8335523 : Blo 1200417 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B2027713 : Blo 1200417 2027713 := bstep (se 2 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 2027713 = 1520785) B1520785
theorem B4559075 : Blo 1200417 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B2027747 : Blo 1200417 2027747 := bstep (se 1 (by rfl) ⟨1520810, by rfl⟩ : syracuseStep 2027747 = 3041621) B3041621
theorem B1200419 : Blo 1200417 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B2281763 : Blo 1200417 2281763 := bstep (se 1 (by rfl) ⟨1711322, by rfl⟩ : syracuseStep 2281763 = 3422645) B3422645
theorem B1200435 : Blo 1200417 1200435 := bstep (se 1 (by rfl) ⟨900326, by rfl⟩ : syracuseStep 1200435 = 1800653) B1800653
theorem B1200451 : Blo 1200417 1200451 := bstep (se 1 (by rfl) ⟨900338, by rfl⟩ : syracuseStep 1200451 = 1800677) B1800677
theorem B1200467 : Blo 1200417 1200467 := bstep (se 1 (by rfl) ⟨900350, by rfl⟩ : syracuseStep 1200467 = 1800701) B1800701
theorem B1200483 : Blo 1200417 1200483 := bstep (se 1 (by rfl) ⟨900362, by rfl⟩ : syracuseStep 1200483 = 1800725) B1800725
theorem B1732963 : Blo 1200417 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B2027875 : Blo 1200417 2027875 := bstep (se 1 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 2027875 = 3041813) B3041813
theorem B1200499 : Blo 1200417 1200499 := bstep (se 1 (by rfl) ⟨900374, by rfl⟩ : syracuseStep 1200499 = 1800749) B1800749
theorem B1200515 : Blo 1200417 1200515 := bstep (se 1 (by rfl) ⟨900386, by rfl⟩ : syracuseStep 1200515 = 1800773) B1800773
theorem B3846541 : Blo 1200417 3846541 := bstep (se 3 (by rfl) ⟨721226, by rfl⟩ : syracuseStep 3846541 = 1442453) B1442453
theorem B1200531 : Blo 1200417 1200531 := bstep (se 1 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 1200531 = 1800797) B1800797
theorem B1200547 : Blo 1200417 1200547 := bstep (se 1 (by rfl) ⟨900410, by rfl⟩ : syracuseStep 1200547 = 1800821) B1800821
theorem B1200563 : Blo 1200417 1200563 := bstep (se 1 (by rfl) ⟨900422, by rfl⟩ : syracuseStep 1200563 = 1800845) B1800845
theorem B1200579 : Blo 1200417 1200579 := bstep (se 1 (by rfl) ⟨900434, by rfl⟩ : syracuseStep 1200579 = 1800869) B1800869
theorem B1200595 : Blo 1200417 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B1200611 : Blo 1200417 1200611 := bstep (se 1 (by rfl) ⟨900458, by rfl⟩ : syracuseStep 1200611 = 1800917) B1800917
theorem B2028017 : Blo 1200417 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B9130481 : Blo 1200417 9130481 := bstep (se 2 (by rfl) ⟨3423930, by rfl⟩ : syracuseStep 9130481 = 6847861) B6847861
theorem B1200627 : Blo 1200417 1200627 := bstep (se 1 (by rfl) ⟨900470, by rfl⟩ : syracuseStep 1200627 = 1800941) B1800941
theorem B1200643 : Blo 1200417 1200643 := bstep (se 1 (by rfl) ⟨900482, by rfl⟩ : syracuseStep 1200643 = 1800965) B1800965
theorem B1200659 : Blo 1200417 1200659 := bstep (se 1 (by rfl) ⟨900494, by rfl⟩ : syracuseStep 1200659 = 1800989) B1800989
theorem B1520147 : Blo 1200417 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B1200675 : Blo 1200417 1200675 := bstep (se 1 (by rfl) ⟨900506, by rfl⟩ : syracuseStep 1200675 = 1801013) B1801013
theorem B1200691 : Blo 1200417 1200691 := bstep (se 1 (by rfl) ⟨900518, by rfl⟩ : syracuseStep 1200691 = 1801037) B1801037
theorem B1200707 : Blo 1200417 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B1200723 : Blo 1200417 1200723 := bstep (se 1 (by rfl) ⟨900542, by rfl⟩ : syracuseStep 1200723 = 1801085) B1801085
theorem B1200739 : Blo 1200417 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B4051565 : Blo 1200417 4051565 := bstep (se 3 (by rfl) ⟨759668, by rfl⟩ : syracuseStep 4051565 = 1519337) B1519337
theorem B2028145 : Blo 1200417 2028145 := bstep (se 2 (by rfl) ⟨760554, by rfl⟩ : syracuseStep 2028145 = 1521109) B1521109
theorem B1200755 : Blo 1200417 1200755 := bstep (se 1 (by rfl) ⟨900566, by rfl⟩ : syracuseStep 1200755 = 1801133) B1801133
theorem B1200771 : Blo 1200417 1200771 := bstep (se 1 (by rfl) ⟨900578, by rfl⟩ : syracuseStep 1200771 = 1801157) B1801157
theorem B3248785 : Blo 1200417 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B1200787 : Blo 1200417 1200787 := bstep (se 1 (by rfl) ⟨900590, by rfl⟩ : syracuseStep 1200787 = 1801181) B1801181
theorem B2028179 : Blo 1200417 2028179 := bstep (se 1 (by rfl) ⟨1521134, by rfl⟩ : syracuseStep 2028179 = 3042269) B3042269
theorem B4051619 : Blo 1200417 4051619 := bstep (se 1 (by rfl) ⟨3038714, by rfl⟩ : syracuseStep 4051619 = 6077429) B6077429
theorem B1200803 : Blo 1200417 1200803 := bstep (se 1 (by rfl) ⟨900602, by rfl⟩ : syracuseStep 1200803 = 1801205) B1801205
theorem B1200819 : Blo 1200417 1200819 := bstep (se 1 (by rfl) ⟨900614, by rfl⟩ : syracuseStep 1200819 = 1801229) B1801229
theorem B1200835 : Blo 1200417 1200835 := bstep (se 1 (by rfl) ⟨900626, by rfl⟩ : syracuseStep 1200835 = 1801253) B1801253
theorem B1200851 : Blo 1200417 1200851 := bstep (se 1 (by rfl) ⟨900638, by rfl⟩ : syracuseStep 1200851 = 1801277) B1801277
theorem B1200867 : Blo 1200417 1200867 := bstep (se 1 (by rfl) ⟨900650, by rfl⟩ : syracuseStep 1200867 = 1801301) B1801301
theorem B3420913 : Blo 1200417 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B1200883 : Blo 1200417 1200883 := bstep (se 1 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 1200883 = 1801325) B1801325
theorem B1200899 : Blo 1200417 1200899 := bstep (se 1 (by rfl) ⟨900674, by rfl⟩ : syracuseStep 1200899 = 1801349) B1801349
theorem B1200915 : Blo 1200417 1200915 := bstep (se 1 (by rfl) ⟨900686, by rfl⟩ : syracuseStep 1200915 = 1801373) B1801373
theorem B2028307 : Blo 1200417 2028307 := bstep (se 1 (by rfl) ⟨1521230, by rfl⟩ : syracuseStep 2028307 = 3042461) B3042461
theorem B1200931 : Blo 1200417 1200931 := bstep (se 1 (by rfl) ⟨900698, by rfl⟩ : syracuseStep 1200931 = 1801397) B1801397
theorem B6845219 : Blo 1200417 6845219 := bstep (se 1 (by rfl) ⟨5133914, by rfl⟩ : syracuseStep 6845219 = 10267829) B10267829
theorem B1200947 : Blo 1200417 1200947 := bstep (se 1 (by rfl) ⟨900710, by rfl⟩ : syracuseStep 1200947 = 1801421) B1801421
theorem B1200963 : Blo 1200417 1200963 := bstep (se 1 (by rfl) ⟨900722, by rfl⟩ : syracuseStep 1200963 = 1801445) B1801445
theorem B1200979 : Blo 1200417 1200979 := bstep (se 1 (by rfl) ⟨900734, by rfl⟩ : syracuseStep 1200979 = 1801469) B1801469
theorem B1200995 : Blo 1200417 1200995 := bstep (se 1 (by rfl) ⟨900746, by rfl⟩ : syracuseStep 1200995 = 1801493) B1801493
theorem B1282915 : Blo 1200417 1282915 := bstep (se 1 (by rfl) ⟨962186, by rfl⟩ : syracuseStep 1282915 = 1924373) B1924373
theorem B1201011 : Blo 1200417 1201011 := bstep (se 1 (by rfl) ⟨900758, by rfl⟩ : syracuseStep 1201011 = 1801517) B1801517
theorem B1201027 : Blo 1200417 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B4109197 : Blo 1200417 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B1201043 : Blo 1200417 1201043 := bstep (se 1 (by rfl) ⟨900782, by rfl⟩ : syracuseStep 1201043 = 1801565) B1801565
theorem B2028449 : Blo 1200417 2028449 := bstep (se 2 (by rfl) ⟨760668, by rfl⟩ : syracuseStep 2028449 = 1521337) B1521337
theorem B6837155 : Blo 1200417 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B1201059 : Blo 1200417 1201059 := bstep (se 1 (by rfl) ⟨900794, by rfl⟩ : syracuseStep 1201059 = 1801589) B1801589
theorem B4051889 : Blo 1200417 4051889 := bstep (se 2 (by rfl) ⟨1519458, by rfl⟩ : syracuseStep 4051889 = 3038917) B3038917
theorem B1201075 : Blo 1200417 1201075 := bstep (se 1 (by rfl) ⟨900806, by rfl⟩ : syracuseStep 1201075 = 1801613) B1801613
theorem B1201091 : Blo 1200417 1201091 := bstep (se 1 (by rfl) ⟨900818, by rfl⟩ : syracuseStep 1201091 = 1801637) B1801637
theorem B1201107 : Blo 1200417 1201107 := bstep (se 1 (by rfl) ⟨900830, by rfl⟩ : syracuseStep 1201107 = 1801661) B1801661
theorem B1201123 : Blo 1200417 1201123 := bstep (se 1 (by rfl) ⟨900842, by rfl⟩ : syracuseStep 1201123 = 1801685) B1801685
theorem B1201139 : Blo 1200417 1201139 := bstep (se 1 (by rfl) ⟨900854, by rfl⟩ : syracuseStep 1201139 = 1801709) B1801709
theorem B1201155 : Blo 1200417 1201155 := bstep (se 1 (by rfl) ⟨900866, by rfl⟩ : syracuseStep 1201155 = 1801733) B1801733
theorem B3421187 : Blo 1200417 3421187 := bstep (se 1 (by rfl) ⟨2565890, by rfl⟩ : syracuseStep 3421187 = 5131781) B5131781
theorem B1201171 : Blo 1200417 1201171 := bstep (se 1 (by rfl) ⟨900878, by rfl⟩ : syracuseStep 1201171 = 1801757) B1801757
theorem B2028577 : Blo 1200417 2028577 := bstep (se 2 (by rfl) ⟨760716, by rfl⟩ : syracuseStep 2028577 = 1521433) B1521433
theorem B1201187 : Blo 1200417 1201187 := bstep (se 1 (by rfl) ⟨900890, by rfl⟩ : syracuseStep 1201187 = 1801781) B1801781
theorem B1201203 : Blo 1200417 1201203 := bstep (se 1 (by rfl) ⟨900902, by rfl⟩ : syracuseStep 1201203 = 1801805) B1801805
theorem B1201219 : Blo 1200417 1201219 := bstep (se 1 (by rfl) ⟨900914, by rfl⟩ : syracuseStep 1201219 = 1801829) B1801829
theorem B2028611 : Blo 1200417 2028611 := bstep (se 1 (by rfl) ⟨1521458, by rfl⟩ : syracuseStep 2028611 = 3042917) B3042917
theorem B1201235 : Blo 1200417 1201235 := bstep (se 1 (by rfl) ⟨900926, by rfl⟩ : syracuseStep 1201235 = 1801853) B1801853
theorem B1201251 : Blo 1200417 1201251 := bstep (se 1 (by rfl) ⟨900938, by rfl⟩ : syracuseStep 1201251 = 1801877) B1801877
theorem B1201267 : Blo 1200417 1201267 := bstep (se 1 (by rfl) ⟨900950, by rfl⟩ : syracuseStep 1201267 = 1801901) B1801901
theorem B1201283 : Blo 1200417 1201283 := bstep (se 1 (by rfl) ⟨900962, by rfl⟩ : syracuseStep 1201283 = 1801925) B1801925
theorem B1201299 : Blo 1200417 1201299 := bstep (se 1 (by rfl) ⟨900974, by rfl⟩ : syracuseStep 1201299 = 1801949) B1801949
theorem B1201315 : Blo 1200417 1201315 := bstep (se 1 (by rfl) ⟨900986, by rfl⟩ : syracuseStep 1201315 = 1801973) B1801973
theorem B6083747 : Blo 1200417 6083747 := bstep (se 1 (by rfl) ⟨4562810, by rfl⟩ : syracuseStep 6083747 = 9125621) B9125621
theorem B1201331 : Blo 1200417 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B1201347 : Blo 1200417 1201347 := bstep (se 1 (by rfl) ⟨901010, by rfl⟩ : syracuseStep 1201347 = 1802021) B1802021
theorem B3421379 : Blo 1200417 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B2028739 : Blo 1200417 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B4560077 : Blo 1200417 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B1201363 : Blo 1200417 1201363 := bstep (se 1 (by rfl) ⟨901022, by rfl⟩ : syracuseStep 1201363 = 1802045) B1802045
theorem B1520851 : Blo 1200417 1520851 := bstep (se 1 (by rfl) ⟨1140638, by rfl⟩ : syracuseStep 1520851 = 2281277) B2281277
theorem B1201379 : Blo 1200417 1201379 := bstep (se 1 (by rfl) ⟨901034, by rfl⟩ : syracuseStep 1201379 = 1802069) B1802069
theorem B1201395 : Blo 1200417 1201395 := bstep (se 1 (by rfl) ⟨901046, by rfl⟩ : syracuseStep 1201395 = 1802093) B1802093
theorem B1201411 : Blo 1200417 1201411 := bstep (se 1 (by rfl) ⟨901058, by rfl⟩ : syracuseStep 1201411 = 1802117) B1802117
theorem B1201427 : Blo 1200417 1201427 := bstep (se 1 (by rfl) ⟨901070, by rfl⟩ : syracuseStep 1201427 = 1802141) B1802141
theorem B1201443 : Blo 1200417 1201443 := bstep (se 1 (by rfl) ⟨901082, by rfl⟩ : syracuseStep 1201443 = 1802165) B1802165
theorem B1709363 : Blo 1200417 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B1201459 : Blo 1200417 1201459 := bstep (se 1 (by rfl) ⟨901094, by rfl⟩ : syracuseStep 1201459 = 1802189) B1802189
theorem B1520947 : Blo 1200417 1520947 := bstep (se 1 (by rfl) ⟨1140710, by rfl⟩ : syracuseStep 1520947 = 2281421) B2281421
theorem B4109635 : Blo 1200417 4109635 := bstep (se 1 (by rfl) ⟨3082226, by rfl⟩ : syracuseStep 4109635 = 6164453) B6164453
theorem B1201475 : Blo 1200417 1201475 := bstep (se 1 (by rfl) ⟨901106, by rfl⟩ : syracuseStep 1201475 = 1802213) B1802213
theorem B2028881 : Blo 1200417 2028881 := bstep (se 2 (by rfl) ⟨760830, by rfl⟩ : syracuseStep 2028881 = 1521661) B1521661
theorem B1201491 : Blo 1200417 1201491 := bstep (se 1 (by rfl) ⟨901118, by rfl⟩ : syracuseStep 1201491 = 1802237) B1802237
theorem B1201507 : Blo 1200417 1201507 := bstep (se 1 (by rfl) ⟨901130, by rfl⟩ : syracuseStep 1201507 = 1802261) B1802261
theorem B1201523 : Blo 1200417 1201523 := bstep (se 1 (by rfl) ⟨901142, by rfl⟩ : syracuseStep 1201523 = 1802285) B1802285
theorem B1201539 : Blo 1200417 1201539 := bstep (se 1 (by rfl) ⟨901154, by rfl⟩ : syracuseStep 1201539 = 1802309) B1802309
theorem B5133709 : Blo 1200417 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1201555 : Blo 1200417 1201555 := bstep (se 1 (by rfl) ⟨901166, by rfl⟩ : syracuseStep 1201555 = 1802333) B1802333
theorem B1201571 : Blo 1200417 1201571 := bstep (se 1 (by rfl) ⟨901178, by rfl⟩ : syracuseStep 1201571 = 1802357) B1802357
theorem B1201587 : Blo 1200417 1201587 := bstep (se 1 (by rfl) ⟨901190, by rfl⟩ : syracuseStep 1201587 = 1802381) B1802381
theorem B1201603 : Blo 1200417 1201603 := bstep (se 1 (by rfl) ⟨901202, by rfl⟩ : syracuseStep 1201603 = 1802405) B1802405
theorem B4052429 : Blo 1200417 4052429 := bstep (se 3 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 4052429 = 1519661) B1519661
theorem B4109777 : Blo 1200417 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B1201619 : Blo 1200417 1201619 := bstep (se 1 (by rfl) ⟨901214, by rfl⟩ : syracuseStep 1201619 = 1802429) B1802429
theorem B2029009 : Blo 1200417 2029009 := bstep (se 2 (by rfl) ⟨760878, by rfl⟩ : syracuseStep 2029009 = 1521757) B1521757
theorem B1201635 : Blo 1200417 1201635 := bstep (se 1 (by rfl) ⟨901226, by rfl⟩ : syracuseStep 1201635 = 1802453) B1802453
theorem B4330979 : Blo 1200417 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B1201651 : Blo 1200417 1201651 := bstep (se 1 (by rfl) ⟨901238, by rfl⟩ : syracuseStep 1201651 = 1802477) B1802477
theorem B2029043 : Blo 1200417 2029043 := bstep (se 1 (by rfl) ⟨1521782, by rfl⟩ : syracuseStep 2029043 = 3043565) B3043565
theorem B4052483 : Blo 1200417 4052483 := bstep (se 1 (by rfl) ⟨3039362, by rfl⟩ : syracuseStep 4052483 = 6078725) B6078725
theorem B1201667 : Blo 1200417 1201667 := bstep (se 1 (by rfl) ⟨901250, by rfl⟩ : syracuseStep 1201667 = 1802501) B1802501
theorem B9369101 : Blo 1200417 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B1201683 : Blo 1200417 1201683 := bstep (se 1 (by rfl) ⟨901262, by rfl⟩ : syracuseStep 1201683 = 1802525) B1802525
theorem B1201699 : Blo 1200417 1201699 := bstep (se 1 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 1201699 = 1802549) B1802549
theorem B2741795 : Blo 1200417 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B1201715 : Blo 1200417 1201715 := bstep (se 1 (by rfl) ⟨901286, by rfl⟩ : syracuseStep 1201715 = 1802573) B1802573
theorem B1201731 : Blo 1200417 1201731 := bstep (se 1 (by rfl) ⟨901298, by rfl⟩ : syracuseStep 1201731 = 1802597) B1802597
theorem B1201747 : Blo 1200417 1201747 := bstep (se 1 (by rfl) ⟨901310, by rfl⟩ : syracuseStep 1201747 = 1802621) B1802621
theorem B1201763 : Blo 1200417 1201763 := bstep (se 1 (by rfl) ⟨901322, by rfl⟩ : syracuseStep 1201763 = 1802645) B1802645
theorem B3126883 : Blo 1200417 3126883 := bstep (se 1 (by rfl) ⟨2345162, by rfl⟩ : syracuseStep 3126883 = 4690325) B4690325
theorem B1201779 : Blo 1200417 1201779 := bstep (se 1 (by rfl) ⟨901334, by rfl⟩ : syracuseStep 1201779 = 1802669) B1802669
theorem B1201795 : Blo 1200417 1201795 := bstep (se 1 (by rfl) ⟨901346, by rfl⟩ : syracuseStep 1201795 = 1802693) B1802693
theorem B1201811 : Blo 1200417 1201811 := bstep (se 1 (by rfl) ⟨901358, by rfl⟩ : syracuseStep 1201811 = 1802717) B1802717
theorem B1201827 : Blo 1200417 1201827 := bstep (se 1 (by rfl) ⟨901370, by rfl⟩ : syracuseStep 1201827 = 1802741) B1802741
theorem B1201843 : Blo 1200417 1201843 := bstep (se 1 (by rfl) ⟨901382, by rfl⟩ : syracuseStep 1201843 = 1802765) B1802765
theorem B1201859 : Blo 1200417 1201859 := bstep (se 1 (by rfl) ⟨901394, by rfl⟩ : syracuseStep 1201859 = 1802789) B1802789
theorem B1201875 : Blo 1200417 1201875 := bstep (se 1 (by rfl) ⟨901406, by rfl⟩ : syracuseStep 1201875 = 1802813) B1802813
theorem B1201891 : Blo 1200417 1201891 := bstep (se 1 (by rfl) ⟨901418, by rfl⟩ : syracuseStep 1201891 = 1802837) B1802837
theorem B3127025 : Blo 1200417 3127025 := bstep (se 2 (by rfl) ⟨1172634, by rfl⟩ : syracuseStep 3127025 = 2345269) B2345269
theorem B1201907 : Blo 1200417 1201907 := bstep (se 1 (by rfl) ⟨901430, by rfl⟩ : syracuseStep 1201907 = 1802861) B1802861
theorem B1201923 : Blo 1200417 1201923 := bstep (se 1 (by rfl) ⟨901442, by rfl⟩ : syracuseStep 1201923 = 1802885) B1802885
theorem B6846221 : Blo 1200417 6846221 := bstep (se 3 (by rfl) ⟨1283666, by rfl⟩ : syracuseStep 6846221 = 2567333) B2567333
theorem B4052753 : Blo 1200417 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B1201939 : Blo 1200417 1201939 := bstep (se 1 (by rfl) ⟨901454, by rfl⟩ : syracuseStep 1201939 = 1802909) B1802909
theorem B1201955 : Blo 1200417 1201955 := bstep (se 1 (by rfl) ⟨901466, by rfl⟩ : syracuseStep 1201955 = 1802933) B1802933
theorem B1521443 : Blo 1200417 1521443 := bstep (se 1 (by rfl) ⟨1141082, by rfl⟩ : syracuseStep 1521443 = 2282165) B2282165
theorem B1201971 : Blo 1200417 1201971 := bstep (se 1 (by rfl) ⟨901478, by rfl⟩ : syracuseStep 1201971 = 1802957) B1802957
theorem B1201987 : Blo 1200417 1201987 := bstep (se 1 (by rfl) ⟨901490, by rfl⟩ : syracuseStep 1201987 = 1802981) B1802981
theorem B1202003 : Blo 1200417 1202003 := bstep (se 1 (by rfl) ⟨901502, by rfl⟩ : syracuseStep 1202003 = 1803005) B1803005
theorem B8656739 : Blo 1200417 8656739 := bstep (se 1 (by rfl) ⟨6492554, by rfl⟩ : syracuseStep 8656739 = 12985109) B12985109
theorem B1202019 : Blo 1200417 1202019 := bstep (se 1 (by rfl) ⟨901514, by rfl⟩ : syracuseStep 1202019 = 1803029) B1803029
theorem B2701169 : Blo 1200417 2701169 := bstep (se 2 (by rfl) ⟨1012938, by rfl⟩ : syracuseStep 2701169 = 2025877) B2025877
theorem B1202035 : Blo 1200417 1202035 := bstep (se 1 (by rfl) ⟨901526, by rfl⟩ : syracuseStep 1202035 = 1803053) B1803053
theorem B2701187 : Blo 1200417 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B1202051 : Blo 1200417 1202051 := bstep (se 1 (by rfl) ⟨901538, by rfl⟩ : syracuseStep 1202051 = 1803077) B1803077
theorem B1202067 : Blo 1200417 1202067 := bstep (se 1 (by rfl) ⟨901550, by rfl⟩ : syracuseStep 1202067 = 1803101) B1803101
theorem B1202083 : Blo 1200417 1202083 := bstep (se 1 (by rfl) ⟨901562, by rfl⟩ : syracuseStep 1202083 = 1803125) B1803125
theorem B1710001 : Blo 1200417 1710001 := bstep (se 2 (by rfl) ⟨641250, by rfl⟩ : syracuseStep 1710001 = 1282501) B1282501
theorem B1202099 : Blo 1200417 1202099 := bstep (se 1 (by rfl) ⟨901574, by rfl⟩ : syracuseStep 1202099 = 1803149) B1803149
theorem B2054081 : Blo 1200417 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B1202115 : Blo 1200417 1202115 := bstep (se 1 (by rfl) ⟨901586, by rfl⟩ : syracuseStep 1202115 = 1803173) B1803173
theorem B6084557 : Blo 1200417 6084557 := bstep (se 3 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 6084557 = 2281709) B2281709
theorem B1202131 : Blo 1200417 1202131 := bstep (se 1 (by rfl) ⟨901598, by rfl⟩ : syracuseStep 1202131 = 1803197) B1803197
theorem B1202147 : Blo 1200417 1202147 := bstep (se 1 (by rfl) ⟨901610, by rfl⟩ : syracuseStep 1202147 = 1803221) B1803221
theorem B3422189 : Blo 1200417 3422189 := bstep (se 3 (by rfl) ⟨641660, by rfl⟩ : syracuseStep 3422189 = 1283321) B1283321
theorem B1202163 : Blo 1200417 1202163 := bstep (se 1 (by rfl) ⟨901622, by rfl⟩ : syracuseStep 1202163 = 1803245) B1803245
theorem B1202179 : Blo 1200417 1202179 := bstep (se 1 (by rfl) ⟨901634, by rfl⟩ : syracuseStep 1202179 = 1803269) B1803269
theorem B2054161 : Blo 1200417 2054161 := bstep (se 2 (by rfl) ⟨770310, by rfl⟩ : syracuseStep 2054161 = 1540621) B1540621
theorem B1202195 : Blo 1200417 1202195 := bstep (se 1 (by rfl) ⟨901646, by rfl⟩ : syracuseStep 1202195 = 1803293) B1803293
theorem B1202211 : Blo 1200417 1202211 := bstep (se 1 (by rfl) ⟨901658, by rfl⟩ : syracuseStep 1202211 = 1803317) B1803317
theorem B1218611 : Blo 1200417 1218611 := bstep (se 1 (by rfl) ⟨913958, by rfl⟩ : syracuseStep 1218611 = 1827917) B1827917
theorem B1202227 : Blo 1200417 1202227 := bstep (se 1 (by rfl) ⟨901670, by rfl⟩ : syracuseStep 1202227 = 1803341) B1803341
theorem B1202243 : Blo 1200417 1202243 := bstep (se 1 (by rfl) ⟨901682, by rfl⟩ : syracuseStep 1202243 = 1803365) B1803365
theorem B1202259 : Blo 1200417 1202259 := bstep (se 1 (by rfl) ⟨901694, by rfl⟩ : syracuseStep 1202259 = 1803389) B1803389
theorem B1202275 : Blo 1200417 1202275 := bstep (se 1 (by rfl) ⟨901706, by rfl⟩ : syracuseStep 1202275 = 1803413) B1803413
theorem B1202291 : Blo 1200417 1202291 := bstep (se 1 (by rfl) ⟨901718, by rfl⟩ : syracuseStep 1202291 = 1803437) B1803437
theorem B3848323 : Blo 1200417 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B1202307 : Blo 1200417 1202307 := bstep (se 1 (by rfl) ⟨901730, by rfl⟩ : syracuseStep 1202307 = 1803461) B1803461
theorem B2701457 : Blo 1200417 2701457 := bstep (se 2 (by rfl) ⟨1013046, by rfl⟩ : syracuseStep 2701457 = 2026093) B2026093
theorem B1202323 : Blo 1200417 1202323 := bstep (se 1 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 1202323 = 1803485) B1803485
theorem B2701475 : Blo 1200417 2701475 := bstep (se 1 (by rfl) ⟨2026106, by rfl⟩ : syracuseStep 2701475 = 4052213) B4052213
theorem B3422371 : Blo 1200417 3422371 := bstep (se 1 (by rfl) ⟨2566778, by rfl⟩ : syracuseStep 3422371 = 5133557) B5133557
theorem B1202339 : Blo 1200417 1202339 := bstep (se 1 (by rfl) ⟨901754, by rfl⟩ : syracuseStep 1202339 = 1803509) B1803509
theorem B1202355 : Blo 1200417 1202355 := bstep (se 1 (by rfl) ⟨901766, by rfl⟩ : syracuseStep 1202355 = 1803533) B1803533
theorem B1202371 : Blo 1200417 1202371 := bstep (se 1 (by rfl) ⟨901778, by rfl⟩ : syracuseStep 1202371 = 1803557) B1803557
theorem B1202387 : Blo 1200417 1202387 := bstep (se 1 (by rfl) ⟨901790, by rfl⟩ : syracuseStep 1202387 = 1803581) B1803581
theorem B1202403 : Blo 1200417 1202403 := bstep (se 1 (by rfl) ⟨901802, by rfl⟩ : syracuseStep 1202403 = 1803605) B1803605
theorem B1710337 : Blo 1200417 1710337 := bstep (se 2 (by rfl) ⟨641376, by rfl⟩ : syracuseStep 1710337 = 1282753) B1282753
theorem B1644835 : Blo 1200417 1644835 := bstep (se 1 (by rfl) ⟨1233626, by rfl⟩ : syracuseStep 1644835 = 2467253) B2467253
theorem B4053293 : Blo 1200417 4053293 := bstep (se 3 (by rfl) ⟨759992, by rfl⟩ : syracuseStep 4053293 = 1519985) B1519985
theorem B4053347 : Blo 1200417 4053347 := bstep (se 1 (by rfl) ⟨3040010, by rfl⟩ : syracuseStep 4053347 = 6080021) B6080021
theorem B2701745 : Blo 1200417 2701745 := bstep (se 2 (by rfl) ⟨1013154, by rfl⟩ : syracuseStep 2701745 = 2026309) B2026309
theorem B1800641 : Blo 1200417 1800641 := bstep (se 2 (by rfl) ⟨675240, by rfl⟩ : syracuseStep 1800641 = 1350481) B1350481
theorem B2701763 : Blo 1200417 2701763 := bstep (se 1 (by rfl) ⟨2026322, by rfl⟩ : syracuseStep 2701763 = 4052645) B4052645
theorem B1800659 : Blo 1200417 1800659 := bstep (se 1 (by rfl) ⟨1350494, by rfl⟩ : syracuseStep 1800659 = 2700989) B2700989
theorem B1563107 : Blo 1200417 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B1800689 : Blo 1200417 1800689 := bstep (se 2 (by rfl) ⟨675258, by rfl⟩ : syracuseStep 1800689 = 1350517) B1350517
theorem B1800707 : Blo 1200417 1800707 := bstep (se 1 (by rfl) ⟨1350530, by rfl⟩ : syracuseStep 1800707 = 2701061) B2701061
theorem B11541005 : Blo 1200417 11541005 := bstep (se 3 (by rfl) ⟨2163938, by rfl⟩ : syracuseStep 11541005 = 4327877) B4327877
theorem B10271245 : Blo 1200417 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B1800737 : Blo 1200417 1800737 := bstep (se 2 (by rfl) ⟨675276, by rfl⟩ : syracuseStep 1800737 = 1350553) B1350553
theorem B1800755 : Blo 1200417 1800755 := bstep (se 1 (by rfl) ⟨1350566, by rfl⟩ : syracuseStep 1800755 = 2701133) B2701133
theorem B3848771 : Blo 1200417 3848771 := bstep (se 1 (by rfl) ⟨2886578, by rfl⟩ : syracuseStep 3848771 = 5773157) B5773157
theorem B4938317 : Blo 1200417 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B1800785 : Blo 1200417 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B1800803 : Blo 1200417 1800803 := bstep (se 1 (by rfl) ⟨1350602, by rfl⟩ : syracuseStep 1800803 = 2701205) B2701205
theorem B4053617 : Blo 1200417 4053617 := bstep (se 2 (by rfl) ⟨1520106, by rfl⟩ : syracuseStep 4053617 = 3040213) B3040213
theorem B1800833 : Blo 1200417 1800833 := bstep (se 2 (by rfl) ⟨675312, by rfl⟩ : syracuseStep 1800833 = 1350625) B1350625
theorem B3422861 : Blo 1200417 3422861 := bstep (se 3 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 3422861 = 1283573) B1283573
theorem B1800851 : Blo 1200417 1800851 := bstep (se 1 (by rfl) ⟨1350638, by rfl⟩ : syracuseStep 1800851 = 2701277) B2701277
theorem B1800881 : Blo 1200417 1800881 := bstep (se 2 (by rfl) ⟨675330, by rfl⟩ : syracuseStep 1800881 = 1350661) B1350661
theorem B1800899 : Blo 1200417 1800899 := bstep (se 1 (by rfl) ⟨1350674, by rfl⟩ : syracuseStep 1800899 = 2701349) B2701349
theorem B2702033 : Blo 1200417 2702033 := bstep (se 2 (by rfl) ⟨1013262, by rfl⟩ : syracuseStep 2702033 = 2026525) B2026525
theorem B1800929 : Blo 1200417 1800929 := bstep (se 2 (by rfl) ⟨675348, by rfl⟩ : syracuseStep 1800929 = 1350697) B1350697
theorem B9116387 : Blo 1200417 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B2702051 : Blo 1200417 2702051 := bstep (se 1 (by rfl) ⟨2026538, by rfl⟩ : syracuseStep 2702051 = 4053077) B4053077
theorem B1800947 : Blo 1200417 1800947 := bstep (se 1 (by rfl) ⟨1350710, by rfl⟩ : syracuseStep 1800947 = 2701421) B2701421
theorem B1800977 : Blo 1200417 1800977 := bstep (se 2 (by rfl) ⟨675366, by rfl⟩ : syracuseStep 1800977 = 1350733) B1350733
theorem B1800995 : Blo 1200417 1800995 := bstep (se 1 (by rfl) ⟨1350746, by rfl⟩ : syracuseStep 1800995 = 2701493) B2701493
theorem B1801025 : Blo 1200417 1801025 := bstep (se 2 (by rfl) ⟨675384, by rfl⟩ : syracuseStep 1801025 = 1350769) B1350769
theorem B1710929 : Blo 1200417 1710929 := bstep (se 2 (by rfl) ⟨641598, by rfl⟩ : syracuseStep 1710929 = 1283197) B1283197
theorem B1801043 : Blo 1200417 1801043 := bstep (se 1 (by rfl) ⟨1350782, by rfl⟩ : syracuseStep 1801043 = 2701565) B2701565
theorem B1350499 : Blo 1200417 1350499 := bstep (se 1 (by rfl) ⟨1012874, by rfl⟩ : syracuseStep 1350499 = 2025749) B2025749
theorem B4389731 : Blo 1200417 4389731 := bstep (se 1 (by rfl) ⟨3292298, by rfl⟩ : syracuseStep 4389731 = 6584597) B6584597
theorem B1801073 : Blo 1200417 1801073 := bstep (se 2 (by rfl) ⟨675402, by rfl⟩ : syracuseStep 1801073 = 1350805) B1350805
theorem B1801091 : Blo 1200417 1801091 := bstep (se 1 (by rfl) ⟨1350818, by rfl⟩ : syracuseStep 1801091 = 2701637) B2701637
theorem B1801121 : Blo 1200417 1801121 := bstep (se 2 (by rfl) ⟨675420, by rfl⟩ : syracuseStep 1801121 = 1350841) B1350841
theorem B1850291 : Blo 1200417 1850291 := bstep (se 1 (by rfl) ⟨1387718, by rfl⟩ : syracuseStep 1850291 = 2775437) B2775437
theorem B1801139 : Blo 1200417 1801139 := bstep (se 1 (by rfl) ⟨1350854, by rfl⟩ : syracuseStep 1801139 = 2701709) B2701709
theorem B1801169 : Blo 1200417 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B1801187 : Blo 1200417 1801187 := bstep (se 1 (by rfl) ⟨1350890, by rfl⟩ : syracuseStep 1801187 = 2701781) B2701781
theorem B2702321 : Blo 1200417 2702321 := bstep (se 2 (by rfl) ⟨1013370, by rfl⟩ : syracuseStep 2702321 = 2026741) B2026741
theorem B1350643 : Blo 1200417 1350643 := bstep (se 1 (by rfl) ⟨1012982, by rfl⟩ : syracuseStep 1350643 = 2025965) B2025965
theorem B1801217 : Blo 1200417 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B2702339 : Blo 1200417 2702339 := bstep (se 1 (by rfl) ⟨2026754, by rfl⟩ : syracuseStep 2702339 = 4053509) B4053509
theorem B1801235 : Blo 1200417 1801235 := bstep (se 1 (by rfl) ⟨1350926, by rfl⟩ : syracuseStep 1801235 = 2701853) B2701853
theorem B1801265 : Blo 1200417 1801265 := bstep (se 2 (by rfl) ⟨675474, by rfl⟩ : syracuseStep 1801265 = 1350949) B1350949
theorem B1801283 : Blo 1200417 1801283 := bstep (se 1 (by rfl) ⟨1350962, by rfl⟩ : syracuseStep 1801283 = 2701925) B2701925
theorem B1801313 : Blo 1200417 1801313 := bstep (se 2 (by rfl) ⟨675492, by rfl⟩ : syracuseStep 1801313 = 1350985) B1350985
theorem B1924193 : Blo 1200417 1924193 := bstep (se 2 (by rfl) ⟨721572, by rfl⟩ : syracuseStep 1924193 = 1443145) B1443145
theorem B5626979 : Blo 1200417 5626979 := bstep (se 1 (by rfl) ⟨4220234, by rfl⟩ : syracuseStep 5626979 = 8440469) B8440469
theorem B1801331 : Blo 1200417 1801331 := bstep (se 1 (by rfl) ⟨1350998, by rfl⟩ : syracuseStep 1801331 = 2701997) B2701997
theorem B1350787 : Blo 1200417 1350787 := bstep (se 1 (by rfl) ⟨1013090, by rfl⟩ : syracuseStep 1350787 = 2026181) B2026181
theorem B4054157 : Blo 1200417 4054157 := bstep (se 3 (by rfl) ⟨760154, by rfl⟩ : syracuseStep 4054157 = 1520309) B1520309
theorem B1801361 : Blo 1200417 1801361 := bstep (se 2 (by rfl) ⟨675510, by rfl⟩ : syracuseStep 1801361 = 1351021) B1351021
theorem B1801379 : Blo 1200417 1801379 := bstep (se 1 (by rfl) ⟨1351034, by rfl⟩ : syracuseStep 1801379 = 2702069) B2702069
theorem B8019121 : Blo 1200417 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B1801409 : Blo 1200417 1801409 := bstep (se 2 (by rfl) ⟨675528, by rfl⟩ : syracuseStep 1801409 = 1351057) B1351057
theorem B4054211 : Blo 1200417 4054211 := bstep (se 1 (by rfl) ⟨3040658, by rfl⟩ : syracuseStep 4054211 = 6081317) B6081317
theorem B1801427 : Blo 1200417 1801427 := bstep (se 1 (by rfl) ⟨1351070, by rfl⟩ : syracuseStep 1801427 = 2702141) B2702141
theorem B1924321 : Blo 1200417 1924321 := bstep (se 2 (by rfl) ⟨721620, by rfl⟩ : syracuseStep 1924321 = 1443241) B1443241
theorem B2055395 : Blo 1200417 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B1801457 : Blo 1200417 1801457 := bstep (se 2 (by rfl) ⟨675546, by rfl⟩ : syracuseStep 1801457 = 1351093) B1351093
theorem B1801475 : Blo 1200417 1801475 := bstep (se 1 (by rfl) ⟨1351106, by rfl⟩ : syracuseStep 1801475 = 2702213) B2702213
theorem B6495493 : Blo 1200417 6495493 := bstep (se 4 (by rfl) ⟨608952, by rfl⟩ : syracuseStep 6495493 = 1217905) B1217905
theorem B4562189 : Blo 1200417 4562189 := bstep (se 3 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 4562189 = 1710821) B1710821
theorem B2702609 : Blo 1200417 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B1350931 : Blo 1200417 1350931 := bstep (se 1 (by rfl) ⟨1013198, by rfl⟩ : syracuseStep 1350931 = 2026397) B2026397
theorem B1801505 : Blo 1200417 1801505 := bstep (se 2 (by rfl) ⟨675564, by rfl⟩ : syracuseStep 1801505 = 1351129) B1351129
theorem B2702627 : Blo 1200417 2702627 := bstep (se 1 (by rfl) ⟨2026970, by rfl⟩ : syracuseStep 2702627 = 4053941) B4053941
theorem B1801523 : Blo 1200417 1801523 := bstep (se 1 (by rfl) ⟨1351142, by rfl⟩ : syracuseStep 1801523 = 2702285) B2702285
theorem B7691597 : Blo 1200417 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B1801553 : Blo 1200417 1801553 := bstep (se 2 (by rfl) ⟨675582, by rfl⟩ : syracuseStep 1801553 = 1351165) B1351165
theorem B1801571 : Blo 1200417 1801571 := bstep (se 1 (by rfl) ⟨1351178, by rfl⟩ : syracuseStep 1801571 = 2702357) B2702357
theorem B1711459 : Blo 1200417 1711459 := bstep (se 1 (by rfl) ⟨1283594, by rfl⟩ : syracuseStep 1711459 = 2567189) B2567189
theorem B1801601 : Blo 1200417 1801601 := bstep (se 2 (by rfl) ⟨675600, by rfl⟩ : syracuseStep 1801601 = 1351201) B1351201
theorem B1801619 : Blo 1200417 1801619 := bstep (se 1 (by rfl) ⟨1351214, by rfl⟩ : syracuseStep 1801619 = 2702429) B2702429
theorem B1351075 : Blo 1200417 1351075 := bstep (se 1 (by rfl) ⟨1013306, by rfl⟩ : syracuseStep 1351075 = 2026613) B2026613
theorem B1801649 : Blo 1200417 1801649 := bstep (se 2 (by rfl) ⟨675618, by rfl⟩ : syracuseStep 1801649 = 1351237) B1351237
theorem B1801667 : Blo 1200417 1801667 := bstep (se 1 (by rfl) ⟨1351250, by rfl⟩ : syracuseStep 1801667 = 2702501) B2702501
theorem B4054481 : Blo 1200417 4054481 := bstep (se 2 (by rfl) ⟨1520430, by rfl⟩ : syracuseStep 4054481 = 3040861) B3040861
theorem B1801697 : Blo 1200417 1801697 := bstep (se 2 (by rfl) ⟨675636, by rfl⟩ : syracuseStep 1801697 = 1351273) B1351273
theorem B3038705 : Blo 1200417 3038705 := bstep (se 2 (by rfl) ⟨1139514, by rfl⟩ : syracuseStep 3038705 = 2279029) B2279029
theorem B1801715 : Blo 1200417 1801715 := bstep (se 1 (by rfl) ⟨1351286, by rfl⟩ : syracuseStep 1801715 = 2702573) B2702573
theorem B1801745 : Blo 1200417 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B3038755 : Blo 1200417 3038755 := bstep (se 1 (by rfl) ⟨2279066, by rfl⟩ : syracuseStep 3038755 = 4558133) B4558133
theorem B1801763 : Blo 1200417 1801763 := bstep (se 1 (by rfl) ⟨1351322, by rfl⟩ : syracuseStep 1801763 = 2702645) B2702645
theorem B1826353 : Blo 1200417 1826353 := bstep (se 2 (by rfl) ⟨684882, by rfl⟩ : syracuseStep 1826353 = 1369765) B1369765
theorem B1351219 : Blo 1200417 1351219 := bstep (se 1 (by rfl) ⟨1013414, by rfl⟩ : syracuseStep 1351219 = 2026829) B2026829
theorem B2702897 : Blo 1200417 2702897 := bstep (se 2 (by rfl) ⟨1013586, by rfl⟩ : syracuseStep 2702897 = 2027173) B2027173
theorem B1801793 : Blo 1200417 1801793 := bstep (se 2 (by rfl) ⟨675672, by rfl⟩ : syracuseStep 1801793 = 1351345) B1351345
theorem B2702915 : Blo 1200417 2702915 := bstep (se 1 (by rfl) ⟨2027186, by rfl⟩ : syracuseStep 2702915 = 4054373) B4054373
theorem B3898961 : Blo 1200417 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B1801811 : Blo 1200417 1801811 := bstep (se 1 (by rfl) ⟨1351358, by rfl⟩ : syracuseStep 1801811 = 2702717) B2702717
theorem B1801841 : Blo 1200417 1801841 := bstep (se 2 (by rfl) ⟨675690, by rfl⟩ : syracuseStep 1801841 = 1351381) B1351381
theorem B1801859 : Blo 1200417 1801859 := bstep (se 1 (by rfl) ⟨1351394, by rfl⟩ : syracuseStep 1801859 = 2702789) B2702789
theorem B1801889 : Blo 1200417 1801889 := bstep (se 2 (by rfl) ⟨675708, by rfl⟩ : syracuseStep 1801889 = 1351417) B1351417
theorem B5480099 : Blo 1200417 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B3038897 : Blo 1200417 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B1801907 : Blo 1200417 1801907 := bstep (se 1 (by rfl) ⟨1351430, by rfl⟩ : syracuseStep 1801907 = 2702861) B2702861
theorem B1711795 : Blo 1200417 1711795 := bstep (se 1 (by rfl) ⟨1283846, by rfl⟩ : syracuseStep 1711795 = 2567693) B2567693
theorem B1351363 : Blo 1200417 1351363 := bstep (se 1 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 1351363 = 2027045) B2027045
theorem B1801937 : Blo 1200417 1801937 := bstep (se 2 (by rfl) ⟨675726, by rfl⟩ : syracuseStep 1801937 = 1351453) B1351453
theorem B1949395 : Blo 1200417 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B16695011 : Blo 1200417 16695011 := bstep (se 1 (by rfl) ⟨12521258, by rfl⟩ : syracuseStep 16695011 = 25042517) B25042517
theorem B1801955 : Blo 1200417 1801955 := bstep (se 1 (by rfl) ⟨1351466, by rfl⟩ : syracuseStep 1801955 = 2702933) B2702933
theorem B38969059 : Blo 1200417 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B1801985 : Blo 1200417 1801985 := bstep (se 2 (by rfl) ⟨675744, by rfl⟩ : syracuseStep 1801985 = 1351489) B1351489
theorem B3850001 : Blo 1200417 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B1802003 : Blo 1200417 1802003 := bstep (se 1 (by rfl) ⟨1351502, by rfl⟩ : syracuseStep 1802003 = 2703005) B2703005
theorem B5480227 : Blo 1200417 5480227 := bstep (se 1 (by rfl) ⟨4110170, by rfl⟩ : syracuseStep 5480227 = 8220341) B8220341
theorem B3424045 : Blo 1200417 3424045 := bstep (se 3 (by rfl) ⟨642008, by rfl⟩ : syracuseStep 3424045 = 1284017) B1284017
theorem B1802033 : Blo 1200417 1802033 := bstep (se 2 (by rfl) ⟨675762, by rfl⟩ : syracuseStep 1802033 = 1351525) B1351525
theorem B1802051 : Blo 1200417 1802051 := bstep (se 1 (by rfl) ⟨1351538, by rfl⟩ : syracuseStep 1802051 = 2703077) B2703077
theorem B2703185 : Blo 1200417 2703185 := bstep (se 2 (by rfl) ⟨1013694, by rfl⟩ : syracuseStep 2703185 = 2027389) B2027389
theorem B1351507 : Blo 1200417 1351507 := bstep (se 1 (by rfl) ⟨1013630, by rfl⟩ : syracuseStep 1351507 = 2027261) B2027261
theorem B1802081 : Blo 1200417 1802081 := bstep (se 2 (by rfl) ⟨675780, by rfl⟩ : syracuseStep 1802081 = 1351561) B1351561
theorem B2703203 : Blo 1200417 2703203 := bstep (se 1 (by rfl) ⟨2027402, by rfl⟩ : syracuseStep 2703203 = 4054805) B4054805
theorem B1802099 : Blo 1200417 1802099 := bstep (se 1 (by rfl) ⟨1351574, by rfl⟩ : syracuseStep 1802099 = 2703149) B2703149
theorem B1802129 : Blo 1200417 1802129 := bstep (se 2 (by rfl) ⟨675798, by rfl⟩ : syracuseStep 1802129 = 1351597) B1351597
theorem B1802147 : Blo 1200417 1802147 := bstep (se 1 (by rfl) ⟨1351610, by rfl⟩ : syracuseStep 1802147 = 2703221) B2703221
theorem B1802177 : Blo 1200417 1802177 := bstep (se 2 (by rfl) ⟨675816, by rfl⟩ : syracuseStep 1802177 = 1351633) B1351633
theorem B1802195 : Blo 1200417 1802195 := bstep (se 1 (by rfl) ⟨1351646, by rfl⟩ : syracuseStep 1802195 = 2703293) B2703293
theorem B1351651 : Blo 1200417 1351651 := bstep (se 1 (by rfl) ⟨1013738, by rfl⟩ : syracuseStep 1351651 = 2027477) B2027477
theorem B4055021 : Blo 1200417 4055021 := bstep (se 3 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 4055021 = 1520633) B1520633
theorem B1802225 : Blo 1200417 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B2703383 : Blo 1200417 2703383 := bstep (se 1 (by rfl) ⟨2027537, by rfl⟩ : syracuseStep 2703383 = 4055075) B4055075
theorem B1351723 : Blo 1200417 1351723 := bstep (se 1 (by rfl) ⟨1013792, by rfl⟩ : syracuseStep 1351723 = 2027585) B2027585
theorem B1802315 : Blo 1200417 1802315 := bstep (se 1 (by rfl) ⟨1351736, by rfl⟩ : syracuseStep 1802315 = 2703473) B2703473
theorem B1802327 : Blo 1200417 1802327 := bstep (se 1 (by rfl) ⟨1351745, by rfl⟩ : syracuseStep 1802327 = 2703491) B2703491
theorem B4055129 : Blo 1200417 4055129 := bstep (se 2 (by rfl) ⟨1520673, by rfl⟩ : syracuseStep 4055129 = 3041347) B3041347
theorem B11542621 : Blo 1200417 11542621 := bstep (se 3 (by rfl) ⟨2164241, by rfl⟩ : syracuseStep 11542621 = 4328483) B4328483
theorem B3039383 : Blo 1200417 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B1802393 : Blo 1200417 1802393 := bstep (se 2 (by rfl) ⟨675897, by rfl⟩ : syracuseStep 1802393 = 1351795) B1351795
theorem B1351831 : Blo 1200417 1351831 := bstep (se 1 (by rfl) ⟨1013873, by rfl⟩ : syracuseStep 1351831 = 2027747) B2027747
theorem B2703563 : Blo 1200417 2703563 := bstep (se 1 (by rfl) ⟨2027672, by rfl⟩ : syracuseStep 2703563 = 4055345) B4055345
theorem B4563161 : Blo 1200417 4563161 := bstep (se 2 (by rfl) ⟨1711185, by rfl⟩ : syracuseStep 4563161 = 3422371) B3422371
theorem B2703617 : Blo 1200417 2703617 := bstep (se 2 (by rfl) ⟨1013856, by rfl⟩ : syracuseStep 2703617 = 2027713) B2027713
theorem B9740549 : Blo 1200417 9740549 := bstep (se 4 (by rfl) ⟨913176, by rfl⟩ : syracuseStep 9740549 = 1826353) B1826353
theorem B1802507 : Blo 1200417 1802507 := bstep (se 1 (by rfl) ⟨1351880, by rfl⟩ : syracuseStep 1802507 = 2703761) B2703761
theorem B1802519 : Blo 1200417 1802519 := bstep (se 1 (by rfl) ⟨1351889, by rfl⟩ : syracuseStep 1802519 = 2703779) B2703779
theorem B1352011 : Blo 1200417 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B6086987 : Blo 1200417 6086987 := bstep (se 1 (by rfl) ⟨4565240, by rfl⟩ : syracuseStep 6086987 = 9130481) B9130481
theorem B1802585 : Blo 1200417 1802585 := bstep (se 2 (by rfl) ⟨675969, by rfl⟩ : syracuseStep 1802585 = 1351939) B1351939
theorem B1352119 : Blo 1200417 1352119 := bstep (se 1 (by rfl) ⟨1014089, by rfl⟩ : syracuseStep 1352119 = 2028179) B2028179
theorem B1802699 : Blo 1200417 1802699 := bstep (se 1 (by rfl) ⟨1352024, by rfl⟩ : syracuseStep 1802699 = 2704049) B2704049
theorem B1802711 : Blo 1200417 1802711 := bstep (se 1 (by rfl) ⟨1352033, by rfl⟩ : syracuseStep 1802711 = 2704067) B2704067
theorem B2310617 : Blo 1200417 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B2703833 : Blo 1200417 2703833 := bstep (se 2 (by rfl) ⟨1013937, by rfl⟩ : syracuseStep 2703833 = 2027875) B2027875
theorem B5128721 : Blo 1200417 5128721 := bstep (se 2 (by rfl) ⟨1923270, by rfl⟩ : syracuseStep 5128721 = 3846541) B3846541
theorem B4563479 : Blo 1200417 4563479 := bstep (se 1 (by rfl) ⟨3422609, by rfl⟩ : syracuseStep 4563479 = 6845219) B6845219
theorem B1802777 : Blo 1200417 1802777 := bstep (se 2 (by rfl) ⟨676041, by rfl⟩ : syracuseStep 1802777 = 1352083) B1352083
theorem B2703923 : Blo 1200417 2703923 := bstep (se 1 (by rfl) ⟨2027942, by rfl⟩ : syracuseStep 2703923 = 4055885) B4055885
theorem B2703959 : Blo 1200417 2703959 := bstep (se 1 (by rfl) ⟨2027969, by rfl⟩ : syracuseStep 2703959 = 4055939) B4055939
theorem B1352299 : Blo 1200417 1352299 := bstep (se 1 (by rfl) ⟨1014224, by rfl⟩ : syracuseStep 1352299 = 2028449) B2028449
theorem B1802891 : Blo 1200417 1802891 := bstep (se 1 (by rfl) ⟨1352168, by rfl⟩ : syracuseStep 1802891 = 2704337) B2704337
theorem B1802903 : Blo 1200417 1802903 := bstep (se 1 (by rfl) ⟨1352177, by rfl⟩ : syracuseStep 1802903 = 2704355) B2704355
theorem B1352407 : Blo 1200417 1352407 := bstep (se 1 (by rfl) ⟨1014305, by rfl⟩ : syracuseStep 1352407 = 2028611) B2028611
theorem B1802969 : Blo 1200417 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B2704139 : Blo 1200417 2704139 := bstep (se 1 (by rfl) ⟨2028104, by rfl⟩ : syracuseStep 2704139 = 4056209) B4056209
theorem B4055831 : Blo 1200417 4055831 := bstep (se 1 (by rfl) ⟨3041873, by rfl⟩ : syracuseStep 4055831 = 6083747) B6083747
theorem B8782627 : Blo 1200417 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B3040051 : Blo 1200417 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B2704193 : Blo 1200417 2704193 := bstep (se 2 (by rfl) ⟨1014072, by rfl⟩ : syracuseStep 2704193 = 2028145) B2028145
theorem B1803083 : Blo 1200417 1803083 := bstep (se 1 (by rfl) ⟨1352312, by rfl⟩ : syracuseStep 1803083 = 2704625) B2704625
theorem B1803095 : Blo 1200417 1803095 := bstep (se 1 (by rfl) ⟨1352321, by rfl⟩ : syracuseStep 1803095 = 2704643) B2704643
theorem B1352587 : Blo 1200417 1352587 := bstep (se 1 (by rfl) ⟨1014440, by rfl⟩ : syracuseStep 1352587 = 2028881) B2028881
theorem B1803161 : Blo 1200417 1803161 := bstep (se 2 (by rfl) ⟨676185, by rfl⟩ : syracuseStep 1803161 = 1352371) B1352371
theorem B3040193 : Blo 1200417 3040193 := bstep (se 2 (by rfl) ⟨1140072, by rfl⟩ : syracuseStep 3040193 = 2280145) B2280145
theorem B1352695 : Blo 1200417 1352695 := bstep (se 1 (by rfl) ⟨1014521, by rfl⟩ : syracuseStep 1352695 = 2029043) B2029043
theorem B1803275 : Blo 1200417 1803275 := bstep (se 1 (by rfl) ⟨1352456, by rfl⟩ : syracuseStep 1803275 = 2704913) B2704913
theorem B1827863 : Blo 1200417 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B2704409 : Blo 1200417 2704409 := bstep (se 2 (by rfl) ⟨1014153, by rfl⟩ : syracuseStep 2704409 = 2028307) B2028307
theorem B1803287 : Blo 1200417 1803287 := bstep (se 1 (by rfl) ⟨1352465, by rfl⟩ : syracuseStep 1803287 = 2704931) B2704931
theorem B1803353 : Blo 1200417 1803353 := bstep (se 2 (by rfl) ⟨676257, by rfl⟩ : syracuseStep 1803353 = 1352515) B1352515
theorem B2704499 : Blo 1200417 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B2704535 : Blo 1200417 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B4564147 : Blo 1200417 4564147 := bstep (se 1 (by rfl) ⟨3423110, by rfl⟩ : syracuseStep 4564147 = 6846221) B6846221
theorem B1803467 : Blo 1200417 1803467 := bstep (se 1 (by rfl) ⟨1352600, by rfl⟩ : syracuseStep 1803467 = 2705201) B2705201
theorem B1803479 : Blo 1200417 1803479 := bstep (se 1 (by rfl) ⟨1352609, by rfl⟩ : syracuseStep 1803479 = 2705219) B2705219
theorem B1803545 : Blo 1200417 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B1369387 : Blo 1200417 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B4056371 : Blo 1200417 4056371 := bstep (se 1 (by rfl) ⟨3042278, by rfl⟩ : syracuseStep 4056371 = 6084557) B6084557
theorem B2704715 : Blo 1200417 2704715 := bstep (se 1 (by rfl) ⟨2028536, by rfl⟩ : syracuseStep 2704715 = 4057073) B4057073
theorem B2704769 : Blo 1200417 2704769 := bstep (se 2 (by rfl) ⟨1014288, by rfl⟩ : syracuseStep 2704769 = 2028577) B2028577
theorem B8660429 : Blo 1200417 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B10692161 : Blo 1200417 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B4056641 : Blo 1200417 4056641 := bstep (se 2 (by rfl) ⟨1521240, by rfl⟩ : syracuseStep 4056641 = 3042481) B3042481
theorem B2885195 : Blo 1200417 2885195 := bstep (se 1 (by rfl) ⟨2163896, by rfl⟩ : syracuseStep 2885195 = 4327793) B4327793
theorem B2704985 : Blo 1200417 2704985 := bstep (se 2 (by rfl) ⟨1014369, by rfl⟩ : syracuseStep 2704985 = 2028739) B2028739
theorem B2565761 : Blo 1200417 2565761 := bstep (se 2 (by rfl) ⟨962160, by rfl⟩ : syracuseStep 2565761 = 1924321) B1924321
theorem B8660657 : Blo 1200417 8660657 := bstep (se 2 (by rfl) ⟨3247746, by rfl⟩ : syracuseStep 8660657 = 6495493) B6495493
theorem B7694003 : Blo 1200417 7694003 := bstep (se 1 (by rfl) ⟨5770502, by rfl⟩ : syracuseStep 7694003 = 11541005) B11541005
theorem B2705075 : Blo 1200417 2705075 := bstep (se 1 (by rfl) ⟨2028806, by rfl⟩ : syracuseStep 2705075 = 4057613) B4057613
theorem B2565847 : Blo 1200417 2565847 := bstep (se 1 (by rfl) ⟨1924385, by rfl⟩ : syracuseStep 2565847 = 3848771) B3848771
theorem B2705111 : Blo 1200417 2705111 := bstep (se 1 (by rfl) ⟨2028833, by rfl⟩ : syracuseStep 2705111 = 4057667) B4057667
theorem B2705291 : Blo 1200417 2705291 := bstep (se 1 (by rfl) ⟨2028968, by rfl⟩ : syracuseStep 2705291 = 4057937) B4057937
theorem B2926487 : Blo 1200417 2926487 := bstep (se 1 (by rfl) ⟨2194865, by rfl⟩ : syracuseStep 2926487 = 4389731) B4389731
theorem B2705345 : Blo 1200417 2705345 := bstep (se 2 (by rfl) ⟨1014504, by rfl⟩ : syracuseStep 2705345 = 2029009) B2029009
theorem B9119789 : Blo 1200417 9119789 := bstep (se 3 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 9119789 = 3419921) B3419921
theorem B3246169 : Blo 1200417 3246169 := bstep (se 2 (by rfl) ⟨1217313, by rfl⟩ : syracuseStep 3246169 = 2434627) B2434627
theorem B4057181 : Blo 1200417 4057181 := bstep (se 3 (by rfl) ⟨760721, by rfl⟩ : syracuseStep 4057181 = 1521443) B1521443
theorem B1370263 : Blo 1200417 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B3041459 : Blo 1200417 3041459 := bstep (se 1 (by rfl) ⟨2281094, by rfl⟩ : syracuseStep 3041459 = 4562189) B4562189
theorem B2599193 : Blo 1200417 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B2025803 : Blo 1200417 2025803 := bstep (se 1 (by rfl) ⟨1519352, by rfl⟩ : syracuseStep 2025803 = 3038705) B3038705
theorem B20531555 : Blo 1200417 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B16673141 : Blo 1200417 16673141 := bstep (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) B1563107
theorem B2599307 : Blo 1200417 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B2279819 : Blo 1200417 2279819 := bstep (se 1 (by rfl) ⟨1709864, by rfl⟩ : syracuseStep 2279819 = 3419729) B3419729
theorem B4565393 : Blo 1200417 4565393 := bstep (se 2 (by rfl) ⟨1712022, by rfl⟩ : syracuseStep 4565393 = 3424045) B3424045
theorem B2025931 : Blo 1200417 2025931 := bstep (se 1 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 2025931 = 3038897) B3038897
theorem B2566667 : Blo 1200417 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B1444375 : Blo 1200417 1444375 := bstep (se 1 (by rfl) ⟨1083281, by rfl⟩ : syracuseStep 1444375 = 2166563) B2166563
theorem B2280001 : Blo 1200417 2280001 := bstep (se 2 (by rfl) ⟨855000, by rfl⟩ : syracuseStep 2280001 = 1710001) B1710001
theorem B2026073 : Blo 1200417 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B6081155 : Blo 1200417 6081155 := bstep (se 1 (by rfl) ⟨4560866, by rfl⟩ : syracuseStep 6081155 = 9121733) B9121733
theorem B2738881 : Blo 1200417 2738881 := bstep (se 2 (by rfl) ⟨1027080, by rfl⟩ : syracuseStep 2738881 = 2054161) B2054161
theorem B3041995 : Blo 1200417 3041995 := bstep (se 1 (by rfl) ⟨2281496, by rfl⟩ : syracuseStep 3041995 = 4562993) B4562993
theorem B2026201 : Blo 1200417 2026201 := bstep (se 2 (by rfl) ⟨759825, by rfl⟩ : syracuseStep 2026201 = 1519651) B1519651
theorem B5557015 : Blo 1200417 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B7301933 : Blo 1200417 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B5131097 : Blo 1200417 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B3042137 : Blo 1200417 3042137 := bstep (se 2 (by rfl) ⟨1140801, by rfl⟩ : syracuseStep 3042137 = 2281603) B2281603
theorem B5131181 : Blo 1200417 5131181 := bstep (se 3 (by rfl) ⟨962096, by rfl⟩ : syracuseStep 5131181 = 1924193) B1924193
theorem B3419101 : Blo 1200417 3419101 := bstep (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) B1282163
theorem B2280449 : Blo 1200417 2280449 := bstep (se 2 (by rfl) ⟨855168, by rfl⟩ : syracuseStep 2280449 = 1710337) B1710337
theorem B9743435 : Blo 1200417 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B3419329 : Blo 1200417 3419329 := bstep (se 2 (by rfl) ⟨1282248, by rfl⟩ : syracuseStep 3419329 = 2564497) B2564497
theorem B4558103 : Blo 1200417 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B2026775 : Blo 1200417 2026775 := bstep (se 1 (by rfl) ⟨1520081, by rfl⟩ : syracuseStep 2026775 = 3040163) B3040163
theorem B2436377 : Blo 1200417 2436377 := bstep (se 2 (by rfl) ⟨913641, by rfl⟩ : syracuseStep 2436377 = 1827283) B1827283
theorem B2280791 : Blo 1200417 2280791 := bstep (se 1 (by rfl) ⟨1710593, by rfl⟩ : syracuseStep 2280791 = 3421187) B3421187
theorem B2026903 : Blo 1200417 2026903 := bstep (se 1 (by rfl) ⟨1520177, by rfl⟩ : syracuseStep 2026903 = 3040355) B3040355
theorem B2567641 : Blo 1200417 2567641 := bstep (se 2 (by rfl) ⟨962865, by rfl⟩ : syracuseStep 2567641 = 1925731) B1925731
theorem B4558301 : Blo 1200417 4558301 := bstep (se 3 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 4558301 = 1709363) B1709363
theorem B1388011 : Blo 1200417 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B3419671 : Blo 1200417 3419671 := bstep (se 1 (by rfl) ⟨2564753, by rfl⟩ : syracuseStep 3419671 = 5129507) B5129507
theorem B2739851 : Blo 1200417 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B2887319 : Blo 1200417 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B3042967 : Blo 1200417 3042967 := bstep (se 1 (by rfl) ⟨2282225, by rfl⟩ : syracuseStep 3042967 = 4564451) B4564451
theorem B6246067 : Blo 1200417 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B2436979 : Blo 1200417 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B7696259 : Blo 1200417 7696259 := bstep (se 1 (by rfl) ⟨5772194, by rfl⟩ : syracuseStep 7696259 = 11544389) B11544389
theorem B1519499 : Blo 1200417 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B5771159 : Blo 1200417 5771159 := bstep (se 1 (by rfl) ⟨4328369, by rfl⟩ : syracuseStep 5771159 = 8656739) B8656739
theorem B2281459 : Blo 1200417 2281459 := bstep (se 1 (by rfl) ⟨1711094, by rfl⟩ : syracuseStep 2281459 = 3422189) B3422189
theorem B2027531 : Blo 1200417 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B3043403 : Blo 1200417 3043403 := bstep (se 1 (by rfl) ⟨2282552, by rfl⟩ : syracuseStep 3043403 = 4565105) B4565105
theorem B2027659 : Blo 1200417 2027659 := bstep (se 1 (by rfl) ⟨1520744, by rfl⟩ : syracuseStep 2027659 = 3041489) B3041489
theorem B3420377 : Blo 1200417 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B2027801 : Blo 1200417 2027801 := bstep (se 2 (by rfl) ⟨760425, by rfl⟩ : syracuseStep 2027801 = 1520851) B1520851
theorem B1200427 : Blo 1200417 1200427 := bstep (se 1 (by rfl) ⟨900320, by rfl⟩ : syracuseStep 1200427 = 1800641) B1800641
theorem B1200439 : Blo 1200417 1200439 := bstep (se 1 (by rfl) ⟨900329, by rfl⟩ : syracuseStep 1200439 = 1800659) B1800659
theorem B1200459 : Blo 1200417 1200459 := bstep (se 1 (by rfl) ⟨900344, by rfl⟩ : syracuseStep 1200459 = 1800689) B1800689
theorem B1200471 : Blo 1200417 1200471 := bstep (se 1 (by rfl) ⟨900353, by rfl⟩ : syracuseStep 1200471 = 1800707) B1800707
theorem B21918053 : Blo 1200417 21918053 := bstep (se 4 (by rfl) ⟨2054817, by rfl⟩ : syracuseStep 21918053 = 4109635) B4109635
theorem B1200491 : Blo 1200417 1200491 := bstep (se 1 (by rfl) ⟨900368, by rfl⟩ : syracuseStep 1200491 = 1800737) B1800737
theorem B17305973 : Blo 1200417 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B1200503 : Blo 1200417 1200503 := bstep (se 1 (by rfl) ⟨900377, by rfl⟩ : syracuseStep 1200503 = 1800755) B1800755
theorem B1200523 : Blo 1200417 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B1200535 : Blo 1200417 1200535 := bstep (se 1 (by rfl) ⟨900401, by rfl⟩ : syracuseStep 1200535 = 1800803) B1800803
theorem B2027929 : Blo 1200417 2027929 := bstep (se 2 (by rfl) ⟨760473, by rfl⟩ : syracuseStep 2027929 = 1520947) B1520947
theorem B1200555 : Blo 1200417 1200555 := bstep (se 1 (by rfl) ⟨900416, by rfl⟩ : syracuseStep 1200555 = 1800833) B1800833
theorem B2281907 : Blo 1200417 2281907 := bstep (se 1 (by rfl) ⟨1711430, by rfl⟩ : syracuseStep 2281907 = 3422861) B3422861
theorem B1200567 : Blo 1200417 1200567 := bstep (se 1 (by rfl) ⟨900425, by rfl⟩ : syracuseStep 1200567 = 1800851) B1800851
theorem B1200587 : Blo 1200417 1200587 := bstep (se 1 (by rfl) ⟨900440, by rfl⟩ : syracuseStep 1200587 = 1800881) B1800881
theorem B1200599 : Blo 1200417 1200599 := bstep (se 1 (by rfl) ⟨900449, by rfl⟩ : syracuseStep 1200599 = 1800899) B1800899
theorem B2281945 : Blo 1200417 2281945 := bstep (se 2 (by rfl) ⟨855729, by rfl⟩ : syracuseStep 2281945 = 1711459) B1711459
theorem B1200619 : Blo 1200417 1200619 := bstep (se 1 (by rfl) ⟨900464, by rfl⟩ : syracuseStep 1200619 = 1800929) B1800929
theorem B1200631 : Blo 1200417 1200631 := bstep (se 1 (by rfl) ⟨900473, by rfl⟩ : syracuseStep 1200631 = 1800947) B1800947
theorem B1200651 : Blo 1200417 1200651 := bstep (se 1 (by rfl) ⟨900488, by rfl⟩ : syracuseStep 1200651 = 1800977) B1800977
theorem B2437643 : Blo 1200417 2437643 := bstep (se 1 (by rfl) ⟨1828232, by rfl⟩ : syracuseStep 2437643 = 3656465) B3656465
theorem B6844945 : Blo 1200417 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B1200663 : Blo 1200417 1200663 := bstep (se 1 (by rfl) ⟨900497, by rfl⟩ : syracuseStep 1200663 = 1800995) B1800995
theorem B1200683 : Blo 1200417 1200683 := bstep (se 1 (by rfl) ⟨900512, by rfl⟩ : syracuseStep 1200683 = 1801025) B1801025
theorem B1200695 : Blo 1200417 1200695 := bstep (se 1 (by rfl) ⟨900521, by rfl⟩ : syracuseStep 1200695 = 1801043) B1801043
theorem B1200715 : Blo 1200417 1200715 := bstep (se 1 (by rfl) ⟨900536, by rfl⟩ : syracuseStep 1200715 = 1801073) B1801073
theorem B1520203 : Blo 1200417 1520203 := bstep (se 1 (by rfl) ⟨1140152, by rfl⟩ : syracuseStep 1520203 = 2280305) B2280305
theorem B1200727 : Blo 1200417 1200727 := bstep (se 1 (by rfl) ⟨900545, by rfl⟩ : syracuseStep 1200727 = 1801091) B1801091
theorem B44520029 : Blo 1200417 44520029 := bstep (se 3 (by rfl) ⟨8347505, by rfl⟩ : syracuseStep 44520029 = 16695011) B16695011
theorem B1200747 : Blo 1200417 1200747 := bstep (se 1 (by rfl) ⟨900560, by rfl⟩ : syracuseStep 1200747 = 1801121) B1801121
theorem B1233527 : Blo 1200417 1233527 := bstep (se 1 (by rfl) ⟨925145, by rfl⟩ : syracuseStep 1233527 = 1850291) B1850291
theorem B1200759 : Blo 1200417 1200759 := bstep (se 1 (by rfl) ⟨900569, by rfl⟩ : syracuseStep 1200759 = 1801139) B1801139
theorem B1200779 : Blo 1200417 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B1200791 : Blo 1200417 1200791 := bstep (se 1 (by rfl) ⟨900593, by rfl⟩ : syracuseStep 1200791 = 1801187) B1801187
theorem B1200811 : Blo 1200417 1200811 := bstep (se 1 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 1200811 = 1801217) B1801217
theorem B1200823 : Blo 1200417 1200823 := bstep (se 1 (by rfl) ⟨900617, by rfl⟩ : syracuseStep 1200823 = 1801235) B1801235
theorem B1200843 : Blo 1200417 1200843 := bstep (se 1 (by rfl) ⟨900632, by rfl⟩ : syracuseStep 1200843 = 1801265) B1801265
theorem B1200855 : Blo 1200417 1200855 := bstep (se 1 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 1200855 = 1801283) B1801283
theorem B4051673 : Blo 1200417 4051673 := bstep (se 2 (by rfl) ⟨1519377, by rfl⟩ : syracuseStep 4051673 = 3038755) B3038755
theorem B1200875 : Blo 1200417 1200875 := bstep (se 1 (by rfl) ⟨900656, by rfl⟩ : syracuseStep 1200875 = 1801313) B1801313
theorem B1200887 : Blo 1200417 1200887 := bstep (se 1 (by rfl) ⟨900665, by rfl⟩ : syracuseStep 1200887 = 1801331) B1801331
theorem B1200907 : Blo 1200417 1200907 := bstep (se 1 (by rfl) ⟨900680, by rfl⟩ : syracuseStep 1200907 = 1801361) B1801361
theorem B1200919 : Blo 1200417 1200919 := bstep (se 1 (by rfl) ⟨900689, by rfl⟩ : syracuseStep 1200919 = 1801379) B1801379
theorem B1200939 : Blo 1200417 1200939 := bstep (se 1 (by rfl) ⟨900704, by rfl⟩ : syracuseStep 1200939 = 1801409) B1801409
theorem B1200951 : Blo 1200417 1200951 := bstep (se 1 (by rfl) ⟨900713, by rfl⟩ : syracuseStep 1200951 = 1801427) B1801427
theorem B1200971 : Blo 1200417 1200971 := bstep (se 1 (by rfl) ⟨900728, by rfl⟩ : syracuseStep 1200971 = 1801457) B1801457
theorem B1200983 : Blo 1200417 1200983 := bstep (se 1 (by rfl) ⟨900737, by rfl⟩ : syracuseStep 1200983 = 1801475) B1801475
theorem B1520471 : Blo 1200417 1520471 := bstep (se 1 (by rfl) ⟨1140353, by rfl⟩ : syracuseStep 1520471 = 2280707) B2280707
theorem B1201003 : Blo 1200417 1201003 := bstep (se 1 (by rfl) ⟨900752, by rfl⟩ : syracuseStep 1201003 = 1801505) B1801505
theorem B1201015 : Blo 1200417 1201015 := bstep (se 1 (by rfl) ⟨900761, by rfl⟩ : syracuseStep 1201015 = 1801523) B1801523
theorem B1201035 : Blo 1200417 1201035 := bstep (se 1 (by rfl) ⟨900776, by rfl⟩ : syracuseStep 1201035 = 1801553) B1801553
theorem B1201047 : Blo 1200417 1201047 := bstep (se 1 (by rfl) ⟨900785, by rfl⟩ : syracuseStep 1201047 = 1801571) B1801571
theorem B2282393 : Blo 1200417 2282393 := bstep (se 2 (by rfl) ⟨855897, by rfl⟩ : syracuseStep 2282393 = 1711795) B1711795
theorem B1201067 : Blo 1200417 1201067 := bstep (se 1 (by rfl) ⟨900800, by rfl⟩ : syracuseStep 1201067 = 1801601) B1801601
theorem B1201079 : Blo 1200417 1201079 := bstep (se 1 (by rfl) ⟨900809, by rfl⟩ : syracuseStep 1201079 = 1801619) B1801619
theorem B1201099 : Blo 1200417 1201099 := bstep (se 1 (by rfl) ⟨900824, by rfl⟩ : syracuseStep 1201099 = 1801649) B1801649
theorem B1201111 : Blo 1200417 1201111 := bstep (se 1 (by rfl) ⟨900833, by rfl⟩ : syracuseStep 1201111 = 1801667) B1801667
theorem B51958745 : Blo 1200417 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B2503639 : Blo 1200417 2503639 := bstep (se 1 (by rfl) ⟨1877729, by rfl⟩ : syracuseStep 2503639 = 3755459) B3755459
theorem B2028503 : Blo 1200417 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B1201131 : Blo 1200417 1201131 := bstep (se 1 (by rfl) ⟨900848, by rfl⟩ : syracuseStep 1201131 = 1801697) B1801697
theorem B1201143 : Blo 1200417 1201143 := bstep (se 1 (by rfl) ⟨900857, by rfl⟩ : syracuseStep 1201143 = 1801715) B1801715
theorem B1201163 : Blo 1200417 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1201175 : Blo 1200417 1201175 := bstep (se 1 (by rfl) ⟨900881, by rfl⟩ : syracuseStep 1201175 = 1801763) B1801763
theorem B1201195 : Blo 1200417 1201195 := bstep (se 1 (by rfl) ⟨900896, by rfl⟩ : syracuseStep 1201195 = 1801793) B1801793
theorem B1201207 : Blo 1200417 1201207 := bstep (se 1 (by rfl) ⟨900905, by rfl⟩ : syracuseStep 1201207 = 1801811) B1801811
theorem B1201227 : Blo 1200417 1201227 := bstep (se 1 (by rfl) ⟨900920, by rfl⟩ : syracuseStep 1201227 = 1801841) B1801841
theorem B1201239 : Blo 1200417 1201239 := bstep (se 1 (by rfl) ⟨900929, by rfl⟩ : syracuseStep 1201239 = 1801859) B1801859
theorem B1733719 : Blo 1200417 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B2028631 : Blo 1200417 2028631 := bstep (se 1 (by rfl) ⟨1521473, by rfl⟩ : syracuseStep 2028631 = 3042947) B3042947
theorem B1201259 : Blo 1200417 1201259 := bstep (se 1 (by rfl) ⟨900944, by rfl⟩ : syracuseStep 1201259 = 1801889) B1801889
theorem B1201271 : Blo 1200417 1201271 := bstep (se 1 (by rfl) ⟨900953, by rfl⟩ : syracuseStep 1201271 = 1801907) B1801907
theorem B1201291 : Blo 1200417 1201291 := bstep (se 1 (by rfl) ⟨900968, by rfl⟩ : syracuseStep 1201291 = 1801937) B1801937
theorem B1201303 : Blo 1200417 1201303 := bstep (se 1 (by rfl) ⟨900977, by rfl⟩ : syracuseStep 1201303 = 1801955) B1801955
theorem B1709209 : Blo 1200417 1709209 := bstep (se 2 (by rfl) ⟨640953, by rfl⟩ : syracuseStep 1709209 = 1281907) B1281907
theorem B1201323 : Blo 1200417 1201323 := bstep (se 1 (by rfl) ⟨900992, by rfl⟩ : syracuseStep 1201323 = 1801985) B1801985
theorem B1201335 : Blo 1200417 1201335 := bstep (se 1 (by rfl) ⟨901001, by rfl⟩ : syracuseStep 1201335 = 1802003) B1802003
theorem B1201355 : Blo 1200417 1201355 := bstep (se 1 (by rfl) ⟨901016, by rfl⟩ : syracuseStep 1201355 = 1802033) B1802033
theorem B1201367 : Blo 1200417 1201367 := bstep (se 1 (by rfl) ⟨901025, by rfl⟩ : syracuseStep 1201367 = 1802051) B1802051
theorem B1201387 : Blo 1200417 1201387 := bstep (se 1 (by rfl) ⟨901040, by rfl⟩ : syracuseStep 1201387 = 1802081) B1802081
theorem B1201399 : Blo 1200417 1201399 := bstep (se 1 (by rfl) ⟨901049, by rfl⟩ : syracuseStep 1201399 = 1802099) B1802099
theorem B1201419 : Blo 1200417 1201419 := bstep (se 1 (by rfl) ⟨901064, by rfl⟩ : syracuseStep 1201419 = 1802129) B1802129
theorem B1201431 : Blo 1200417 1201431 := bstep (se 1 (by rfl) ⟨901073, by rfl⟩ : syracuseStep 1201431 = 1802147) B1802147
theorem B1201451 : Blo 1200417 1201451 := bstep (se 1 (by rfl) ⟨901088, by rfl⟩ : syracuseStep 1201451 = 1802177) B1802177
theorem B1201463 : Blo 1200417 1201463 := bstep (se 1 (by rfl) ⟨901097, by rfl⟩ : syracuseStep 1201463 = 1802195) B1802195
theorem B1201483 : Blo 1200417 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B1201495 : Blo 1200417 1201495 := bstep (se 1 (by rfl) ⟨901121, by rfl⟩ : syracuseStep 1201495 = 1802243) B1802243
theorem B1201515 : Blo 1200417 1201515 := bstep (se 1 (by rfl) ⟨901136, by rfl⟩ : syracuseStep 1201515 = 1802273) B1802273
theorem B1201527 : Blo 1200417 1201527 := bstep (se 1 (by rfl) ⟨901145, by rfl⟩ : syracuseStep 1201527 = 1802291) B1802291
theorem B4560259 : Blo 1200417 4560259 := bstep (se 1 (by rfl) ⟨3420194, by rfl⟩ : syracuseStep 4560259 = 6840389) B6840389
theorem B1201547 : Blo 1200417 1201547 := bstep (se 1 (by rfl) ⟨901160, by rfl⟩ : syracuseStep 1201547 = 1802321) B1802321
theorem B6837655 : Blo 1200417 6837655 := bstep (se 1 (by rfl) ⟨5128241, by rfl⟩ : syracuseStep 6837655 = 10256483) B10256483
theorem B4052375 : Blo 1200417 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B1201559 : Blo 1200417 1201559 := bstep (se 1 (by rfl) ⟨901169, by rfl⟩ : syracuseStep 1201559 = 1802339) B1802339
theorem B1201579 : Blo 1200417 1201579 := bstep (se 1 (by rfl) ⟨901184, by rfl⟩ : syracuseStep 1201579 = 1802369) B1802369
theorem B1201591 : Blo 1200417 1201591 := bstep (se 1 (by rfl) ⟨901193, by rfl⟩ : syracuseStep 1201591 = 1802387) B1802387
theorem B1201611 : Blo 1200417 1201611 := bstep (se 1 (by rfl) ⟨901208, by rfl⟩ : syracuseStep 1201611 = 1802417) B1802417
theorem B1201623 : Blo 1200417 1201623 := bstep (se 1 (by rfl) ⟨901217, by rfl⟩ : syracuseStep 1201623 = 1802435) B1802435
theorem B3249629 : Blo 1200417 3249629 := bstep (se 3 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 3249629 = 1218611) B1218611
theorem B1201643 : Blo 1200417 1201643 := bstep (se 1 (by rfl) ⟨901232, by rfl⟩ : syracuseStep 1201643 = 1802465) B1802465
theorem B1201655 : Blo 1200417 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B1201675 : Blo 1200417 1201675 := bstep (se 1 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 1201675 = 1802513) B1802513
theorem B12998161 : Blo 1200417 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B1201687 : Blo 1200417 1201687 := bstep (se 1 (by rfl) ⟨901265, by rfl⟩ : syracuseStep 1201687 = 1802531) B1802531
theorem B1521175 : Blo 1200417 1521175 := bstep (se 1 (by rfl) ⟨1140881, by rfl⟩ : syracuseStep 1521175 = 2281763) B2281763
theorem B1201707 : Blo 1200417 1201707 := bstep (se 1 (by rfl) ⟨901280, by rfl⟩ : syracuseStep 1201707 = 1802561) B1802561
theorem B3249715 : Blo 1200417 3249715 := bstep (se 1 (by rfl) ⟨2437286, by rfl⟩ : syracuseStep 3249715 = 4874573) B4874573
theorem B1201719 : Blo 1200417 1201719 := bstep (se 1 (by rfl) ⟨901289, by rfl⟩ : syracuseStep 1201719 = 1802579) B1802579
theorem B1201739 : Blo 1200417 1201739 := bstep (se 1 (by rfl) ⟨901304, by rfl⟩ : syracuseStep 1201739 = 1802609) B1802609
theorem B1201751 : Blo 1200417 1201751 := bstep (se 1 (by rfl) ⟨901313, by rfl⟩ : syracuseStep 1201751 = 1802627) B1802627
theorem B1201771 : Blo 1200417 1201771 := bstep (se 1 (by rfl) ⟨901328, by rfl⟩ : syracuseStep 1201771 = 1802657) B1802657
theorem B1201783 : Blo 1200417 1201783 := bstep (se 1 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 1201783 = 1802675) B1802675
theorem B25990787 : Blo 1200417 25990787 := bstep (se 1 (by rfl) ⟨19493090, by rfl⟩ : syracuseStep 25990787 = 38986181) B38986181
theorem B1201803 : Blo 1200417 1201803 := bstep (se 1 (by rfl) ⟨901352, by rfl⟩ : syracuseStep 1201803 = 1802705) B1802705
theorem B1201815 : Blo 1200417 1201815 := bstep (se 1 (by rfl) ⟨901361, by rfl⟩ : syracuseStep 1201815 = 1802723) B1802723
theorem B1283735 : Blo 1200417 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B2700953 : Blo 1200417 2700953 := bstep (se 2 (by rfl) ⟨1012857, by rfl⟩ : syracuseStep 2700953 = 2025715) B2025715
theorem B1201835 : Blo 1200417 1201835 := bstep (se 1 (by rfl) ⟨901376, by rfl⟩ : syracuseStep 1201835 = 1802753) B1802753
theorem B4560563 : Blo 1200417 4560563 := bstep (se 1 (by rfl) ⟨3420422, by rfl⟩ : syracuseStep 4560563 = 6840845) B6840845
theorem B1201847 : Blo 1200417 1201847 := bstep (se 1 (by rfl) ⟨901385, by rfl⟩ : syracuseStep 1201847 = 1802771) B1802771
theorem B1201867 : Blo 1200417 1201867 := bstep (se 1 (by rfl) ⟨901400, by rfl⟩ : syracuseStep 1201867 = 1802801) B1802801
theorem B1201879 : Blo 1200417 1201879 := bstep (se 1 (by rfl) ⟨901409, by rfl⟩ : syracuseStep 1201879 = 1802819) B1802819
theorem B2193113 : Blo 1200417 2193113 := bstep (se 2 (by rfl) ⟨822417, by rfl⟩ : syracuseStep 2193113 = 1644835) B1644835
theorem B1201899 : Blo 1200417 1201899 := bstep (se 1 (by rfl) ⟨901424, by rfl⟩ : syracuseStep 1201899 = 1802849) B1802849
theorem B2701043 : Blo 1200417 2701043 := bstep (se 1 (by rfl) ⟨2025782, by rfl⟩ : syracuseStep 2701043 = 4051565) B4051565
theorem B1201911 : Blo 1200417 1201911 := bstep (se 1 (by rfl) ⟨901433, by rfl⟩ : syracuseStep 1201911 = 1802867) B1802867
theorem B1201931 : Blo 1200417 1201931 := bstep (se 1 (by rfl) ⟨901448, by rfl⟩ : syracuseStep 1201931 = 1802897) B1802897
theorem B2701079 : Blo 1200417 2701079 := bstep (se 1 (by rfl) ⟨2025809, by rfl⟩ : syracuseStep 2701079 = 4051619) B4051619
theorem B1201943 : Blo 1200417 1201943 := bstep (se 1 (by rfl) ⟨901457, by rfl⟩ : syracuseStep 1201943 = 1802915) B1802915
theorem B1201963 : Blo 1200417 1201963 := bstep (se 1 (by rfl) ⟨901472, by rfl⟩ : syracuseStep 1201963 = 1802945) B1802945
theorem B1201975 : Blo 1200417 1201975 := bstep (se 1 (by rfl) ⟨901481, by rfl⟩ : syracuseStep 1201975 = 1802963) B1802963
theorem B3422017 : Blo 1200417 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B1201995 : Blo 1200417 1201995 := bstep (se 1 (by rfl) ⟨901496, by rfl⟩ : syracuseStep 1201995 = 1802993) B1802993
theorem B1202007 : Blo 1200417 1202007 := bstep (se 1 (by rfl) ⟨901505, by rfl⟩ : syracuseStep 1202007 = 1803011) B1803011
theorem B9123677 : Blo 1200417 9123677 := bstep (se 3 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 9123677 = 3421379) B3421379
theorem B1202027 : Blo 1200417 1202027 := bstep (se 1 (by rfl) ⟨901520, by rfl⟩ : syracuseStep 1202027 = 1803041) B1803041
theorem B1202039 : Blo 1200417 1202039 := bstep (se 1 (by rfl) ⟨901529, by rfl⟩ : syracuseStep 1202039 = 1803059) B1803059
theorem B1202059 : Blo 1200417 1202059 := bstep (se 1 (by rfl) ⟨901544, by rfl⟩ : syracuseStep 1202059 = 1803089) B1803089
theorem B1202071 : Blo 1200417 1202071 := bstep (se 1 (by rfl) ⟨901553, by rfl⟩ : syracuseStep 1202071 = 1803107) B1803107
theorem B1202091 : Blo 1200417 1202091 := bstep (se 1 (by rfl) ⟨901568, by rfl⟩ : syracuseStep 1202091 = 1803137) B1803137
theorem B4052915 : Blo 1200417 4052915 := bstep (se 1 (by rfl) ⟨3039686, by rfl⟩ : syracuseStep 4052915 = 6079373) B6079373
theorem B1202103 : Blo 1200417 1202103 := bstep (se 1 (by rfl) ⟨901577, by rfl⟩ : syracuseStep 1202103 = 1803155) B1803155
theorem B2701259 : Blo 1200417 2701259 := bstep (se 1 (by rfl) ⟨2025944, by rfl⟩ : syracuseStep 2701259 = 4051889) B4051889
theorem B5478347 : Blo 1200417 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B1202123 : Blo 1200417 1202123 := bstep (se 1 (by rfl) ⟨901592, by rfl⟩ : syracuseStep 1202123 = 1803185) B1803185
theorem B1202135 : Blo 1200417 1202135 := bstep (se 1 (by rfl) ⟨901601, by rfl⟩ : syracuseStep 1202135 = 1803203) B1803203
theorem B21936089 : Blo 1200417 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B1202155 : Blo 1200417 1202155 := bstep (se 1 (by rfl) ⟨901616, by rfl⟩ : syracuseStep 1202155 = 1803233) B1803233
theorem B1202167 : Blo 1200417 1202167 := bstep (se 1 (by rfl) ⟨901625, by rfl⟩ : syracuseStep 1202167 = 1803251) B1803251
theorem B2701313 : Blo 1200417 2701313 := bstep (se 2 (by rfl) ⟨1012992, by rfl⟩ : syracuseStep 2701313 = 2025985) B2025985
theorem B1202187 : Blo 1200417 1202187 := bstep (se 1 (by rfl) ⟨901640, by rfl⟩ : syracuseStep 1202187 = 1803281) B1803281
theorem B13694993 : Blo 1200417 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B1202199 : Blo 1200417 1202199 := bstep (se 1 (by rfl) ⟨901649, by rfl⟩ : syracuseStep 1202199 = 1803299) B1803299
theorem B1202219 : Blo 1200417 1202219 := bstep (se 1 (by rfl) ⟨901664, by rfl⟩ : syracuseStep 1202219 = 1803329) B1803329
theorem B1202231 : Blo 1200417 1202231 := bstep (se 1 (by rfl) ⟨901673, by rfl⟩ : syracuseStep 1202231 = 1803347) B1803347
theorem B1202251 : Blo 1200417 1202251 := bstep (se 1 (by rfl) ⟨901688, by rfl⟩ : syracuseStep 1202251 = 1803377) B1803377
theorem B1202263 : Blo 1200417 1202263 := bstep (se 1 (by rfl) ⟨901697, by rfl⟩ : syracuseStep 1202263 = 1803395) B1803395
theorem B1202283 : Blo 1200417 1202283 := bstep (se 1 (by rfl) ⟨901712, by rfl⟩ : syracuseStep 1202283 = 1803425) B1803425
theorem B1202295 : Blo 1200417 1202295 := bstep (se 1 (by rfl) ⟨901721, by rfl⟩ : syracuseStep 1202295 = 1803443) B1803443
theorem B1202315 : Blo 1200417 1202315 := bstep (se 1 (by rfl) ⟨901736, by rfl⟩ : syracuseStep 1202315 = 1803473) B1803473
theorem B1202327 : Blo 1200417 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B1202347 : Blo 1200417 1202347 := bstep (se 1 (by rfl) ⟨901760, by rfl⟩ : syracuseStep 1202347 = 1803521) B1803521
theorem B1202359 : Blo 1200417 1202359 := bstep (se 1 (by rfl) ⟨901769, by rfl⟩ : syracuseStep 1202359 = 1803539) B1803539
theorem B4053185 : Blo 1200417 4053185 := bstep (se 2 (by rfl) ⟨1519944, by rfl⟩ : syracuseStep 4053185 = 3039889) B3039889
theorem B4331713 : Blo 1200417 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B5134529 : Blo 1200417 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B1202379 : Blo 1200417 1202379 := bstep (se 1 (by rfl) ⟨901784, by rfl⟩ : syracuseStep 1202379 = 1803569) B1803569
theorem B1202391 : Blo 1200417 1202391 := bstep (se 1 (by rfl) ⟨901793, by rfl⟩ : syracuseStep 1202391 = 1803587) B1803587
theorem B2701529 : Blo 1200417 2701529 := bstep (se 2 (by rfl) ⟨1013073, by rfl⟩ : syracuseStep 2701529 = 2026147) B2026147
theorem B1202411 : Blo 1200417 1202411 := bstep (se 1 (by rfl) ⟨901808, by rfl⟩ : syracuseStep 1202411 = 1803617) B1803617
theorem B6084881 : Blo 1200417 6084881 := bstep (se 2 (by rfl) ⟨2281830, by rfl⟩ : syracuseStep 6084881 = 4563661) B4563661
theorem B2701619 : Blo 1200417 2701619 := bstep (se 1 (by rfl) ⟨2026214, by rfl⟩ : syracuseStep 2701619 = 4052429) B4052429
theorem B4561217 : Blo 1200417 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B2701655 : Blo 1200417 2701655 := bstep (se 1 (by rfl) ⟨2026241, by rfl⟩ : syracuseStep 2701655 = 4052483) B4052483
theorem B3651929 : Blo 1200417 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B6085043 : Blo 1200417 6085043 := bstep (se 1 (by rfl) ⟨4563782, by rfl⟩ : syracuseStep 6085043 = 9127565) B9127565
theorem B1800665 : Blo 1200417 1800665 := bstep (se 2 (by rfl) ⟨675249, by rfl⟩ : syracuseStep 1800665 = 1350499) B1350499
theorem B1710553 : Blo 1200417 1710553 := bstep (se 2 (by rfl) ⟨641457, by rfl⟩ : syracuseStep 1710553 = 1282915) B1282915
theorem B2701835 : Blo 1200417 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B5478929 : Blo 1200417 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B2701889 : Blo 1200417 2701889 := bstep (se 2 (by rfl) ⟨1013208, by rfl⟩ : syracuseStep 2701889 = 2026417) B2026417
theorem B1800779 : Blo 1200417 1800779 := bstep (se 1 (by rfl) ⟨1350584, by rfl⟩ : syracuseStep 1800779 = 2701169) B2701169
theorem B1710667 : Blo 1200417 1710667 := bstep (se 1 (by rfl) ⟨1283000, by rfl⟩ : syracuseStep 1710667 = 2566001) B2566001
theorem B1800791 : Blo 1200417 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B1800857 : Blo 1200417 1800857 := bstep (se 2 (by rfl) ⟨675321, by rfl⟩ : syracuseStep 1800857 = 1350643) B1350643
theorem B2054873 : Blo 1200417 2054873 := bstep (se 2 (by rfl) ⟨770577, by rfl⟩ : syracuseStep 2054873 = 1541155) B1541155
theorem B4053725 : Blo 1200417 4053725 := bstep (se 3 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 4053725 = 1520147) B1520147
theorem B1800971 : Blo 1200417 1800971 := bstep (se 1 (by rfl) ⟨1350728, by rfl⟩ : syracuseStep 1800971 = 2701457) B2701457
theorem B1800983 : Blo 1200417 1800983 := bstep (se 1 (by rfl) ⟨1350737, by rfl⟩ : syracuseStep 1800983 = 2701475) B2701475
theorem B2702105 : Blo 1200417 2702105 := bstep (se 2 (by rfl) ⟨1013289, by rfl⟩ : syracuseStep 2702105 = 2026579) B2026579
theorem B1801049 : Blo 1200417 1801049 := bstep (se 2 (by rfl) ⟨675393, by rfl⟩ : syracuseStep 1801049 = 1350787) B1350787
theorem B5135197 : Blo 1200417 5135197 := bstep (se 3 (by rfl) ⟨962849, by rfl⟩ : syracuseStep 5135197 = 1925699) B1925699
theorem B2702195 : Blo 1200417 2702195 := bstep (se 1 (by rfl) ⟨2026646, by rfl⟩ : syracuseStep 2702195 = 4053293) B4053293
theorem B2702231 : Blo 1200417 2702231 := bstep (se 1 (by rfl) ⟨2026673, by rfl⟩ : syracuseStep 2702231 = 4053347) B4053347
theorem B1350571 : Blo 1200417 1350571 := bstep (se 1 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 1350571 = 2025857) B2025857
theorem B1801163 : Blo 1200417 1801163 := bstep (se 1 (by rfl) ⟨1350872, by rfl⟩ : syracuseStep 1801163 = 2701745) B2701745
theorem B4332491 : Blo 1200417 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B1801175 : Blo 1200417 1801175 := bstep (se 1 (by rfl) ⟨1350881, by rfl⟩ : syracuseStep 1801175 = 2701763) B2701763
theorem B1350679 : Blo 1200417 1350679 := bstep (se 1 (by rfl) ⟨1013009, by rfl⟩ : syracuseStep 1350679 = 2026019) B2026019
theorem B5200919 : Blo 1200417 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B1801241 : Blo 1200417 1801241 := bstep (se 2 (by rfl) ⟨675465, by rfl⟩ : syracuseStep 1801241 = 1350931) B1350931
theorem B3292211 : Blo 1200417 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B2702411 : Blo 1200417 2702411 := bstep (se 1 (by rfl) ⟨2026808, by rfl⟩ : syracuseStep 2702411 = 4053617) B4053617
theorem B2702465 : Blo 1200417 2702465 := bstep (se 2 (by rfl) ⟨1013424, by rfl⟩ : syracuseStep 2702465 = 2026849) B2026849
theorem B1801355 : Blo 1200417 1801355 := bstep (se 1 (by rfl) ⟨1351016, by rfl⟩ : syracuseStep 1801355 = 2702033) B2702033
theorem B6077591 : Blo 1200417 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B1801367 : Blo 1200417 1801367 := bstep (se 1 (by rfl) ⟨1351025, by rfl⟩ : syracuseStep 1801367 = 2702051) B2702051
theorem B1350859 : Blo 1200417 1350859 := bstep (se 1 (by rfl) ⟨1013144, by rfl⟩ : syracuseStep 1350859 = 2026289) B2026289
theorem B8215769 : Blo 1200417 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B1801433 : Blo 1200417 1801433 := bstep (se 2 (by rfl) ⟨675537, by rfl⟩ : syracuseStep 1801433 = 1351075) B1351075
theorem B8338733 : Blo 1200417 8338733 := bstep (se 3 (by rfl) ⟨1563512, by rfl⟩ : syracuseStep 8338733 = 3127025) B3127025
theorem B1350967 : Blo 1200417 1350967 := bstep (se 1 (by rfl) ⟨1013225, by rfl⟩ : syracuseStep 1350967 = 2026451) B2026451
theorem B1801547 : Blo 1200417 1801547 := bstep (se 1 (by rfl) ⟨1351160, by rfl⟩ : syracuseStep 1801547 = 2702321) B2702321
theorem B1801559 : Blo 1200417 1801559 := bstep (se 1 (by rfl) ⟨1351169, by rfl⟩ : syracuseStep 1801559 = 2702339) B2702339
theorem B2702681 : Blo 1200417 2702681 := bstep (se 2 (by rfl) ⟨1013505, by rfl⟩ : syracuseStep 2702681 = 2027011) B2027011
theorem B3849565 : Blo 1200417 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B3751319 : Blo 1200417 3751319 := bstep (se 1 (by rfl) ⟨2813489, by rfl⟩ : syracuseStep 3751319 = 5626979) B5626979
theorem B1801625 : Blo 1200417 1801625 := bstep (se 2 (by rfl) ⟨675609, by rfl⟩ : syracuseStep 1801625 = 1351219) B1351219
theorem B2702771 : Blo 1200417 2702771 := bstep (se 1 (by rfl) ⟨2027078, by rfl⟩ : syracuseStep 2702771 = 4054157) B4054157
theorem B5135795 : Blo 1200417 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B2702807 : Blo 1200417 2702807 := bstep (se 1 (by rfl) ⟨2027105, by rfl⟩ : syracuseStep 2702807 = 4054211) B4054211
theorem B4169177 : Blo 1200417 4169177 := bstep (se 2 (by rfl) ⟨1563441, by rfl⟩ : syracuseStep 4169177 = 3126883) B3126883
theorem B1351147 : Blo 1200417 1351147 := bstep (se 1 (by rfl) ⟨1013360, by rfl⟩ : syracuseStep 1351147 = 2026721) B2026721
theorem B1801739 : Blo 1200417 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B1801751 : Blo 1200417 1801751 := bstep (se 1 (by rfl) ⟨1351313, by rfl⟩ : syracuseStep 1801751 = 2702627) B2702627
theorem B4562477 : Blo 1200417 4562477 := bstep (se 3 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 4562477 = 1710929) B1710929
theorem B5127731 : Blo 1200417 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B4562507 : Blo 1200417 4562507 := bstep (se 1 (by rfl) ⟨3421880, by rfl⟩ : syracuseStep 4562507 = 6843761) B6843761
theorem B1351255 : Blo 1200417 1351255 := bstep (se 1 (by rfl) ⟨1013441, by rfl⟩ : syracuseStep 1351255 = 2026883) B2026883
theorem B1801817 : Blo 1200417 1801817 := bstep (se 2 (by rfl) ⟨675681, by rfl⟩ : syracuseStep 1801817 = 1351363) B1351363
theorem B9870979 : Blo 1200417 9870979 := bstep (se 1 (by rfl) ⟨7403234, by rfl⟩ : syracuseStep 9870979 = 14806469) B14806469
theorem B2702987 : Blo 1200417 2702987 := bstep (se 1 (by rfl) ⟨2027240, by rfl⟩ : syracuseStep 2702987 = 4054481) B4054481
theorem B2703041 : Blo 1200417 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B1801931 : Blo 1200417 1801931 := bstep (se 1 (by rfl) ⟨1351448, by rfl⟩ : syracuseStep 1801931 = 2702897) B2702897
theorem B1801943 : Blo 1200417 1801943 := bstep (se 1 (by rfl) ⟨1351457, by rfl⟩ : syracuseStep 1801943 = 2702915) B2702915
theorem B7306969 : Blo 1200417 7306969 := bstep (se 2 (by rfl) ⟨2740113, by rfl⟩ : syracuseStep 7306969 = 5480227) B5480227
theorem B17325809 : Blo 1200417 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B1351435 : Blo 1200417 1351435 := bstep (se 1 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 1351435 = 2027153) B2027153
theorem B3653399 : Blo 1200417 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B1802009 : Blo 1200417 1802009 := bstep (se 2 (by rfl) ⟨675753, by rfl⟩ : syracuseStep 1802009 = 1351507) B1351507
theorem B8666945 : Blo 1200417 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B4054859 : Blo 1200417 4054859 := bstep (se 1 (by rfl) ⟨3041144, by rfl⟩ : syracuseStep 4054859 = 6082289) B6082289
theorem B1351543 : Blo 1200417 1351543 := bstep (se 1 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 1351543 = 2027315) B2027315
theorem B1802123 : Blo 1200417 1802123 := bstep (se 1 (by rfl) ⟨1351592, by rfl⟩ : syracuseStep 1802123 = 2703185) B2703185
theorem B1712011 : Blo 1200417 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1802135 : Blo 1200417 1802135 := bstep (se 1 (by rfl) ⟨1351601, by rfl⟩ : syracuseStep 1802135 = 2703203) B2703203
theorem B2703257 : Blo 1200417 2703257 := bstep (se 2 (by rfl) ⟨1013721, by rfl⟩ : syracuseStep 2703257 = 2027443) B2027443
theorem B1802201 : Blo 1200417 1802201 := bstep (se 2 (by rfl) ⟨675825, by rfl⟩ : syracuseStep 1802201 = 1351651) B1351651
theorem B2703347 : Blo 1200417 2703347 := bstep (se 1 (by rfl) ⟨2027510, by rfl⟩ : syracuseStep 2703347 = 4055021) B4055021
theorem B1351687 : Blo 1200417 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B1802255 : Blo 1200417 1802255 := bstep (se 1 (by rfl) ⟨1351691, by rfl⟩ : syracuseStep 1802255 = 2703383) B2703383
theorem B1802297 : Blo 1200417 1802297 := bstep (se 2 (by rfl) ⟨675861, by rfl⟩ : syracuseStep 1802297 = 1351723) B1351723
theorem B2703419 : Blo 1200417 2703419 := bstep (se 1 (by rfl) ⟨2027564, by rfl⟩ : syracuseStep 2703419 = 4055129) B4055129
theorem B1802375 : Blo 1200417 1802375 := bstep (se 1 (by rfl) ⟨1351781, by rfl⟩ : syracuseStep 1802375 = 2703563) B2703563
theorem B1802411 : Blo 1200417 1802411 := bstep (se 1 (by rfl) ⟨1351808, by rfl⟩ : syracuseStep 1802411 = 2703617) B2703617
theorem B2703545 : Blo 1200417 2703545 := bstep (se 2 (by rfl) ⟨1013829, by rfl⟩ : syracuseStep 2703545 = 2027659) B2027659
theorem B1351867 : Blo 1200417 1351867 := bstep (se 1 (by rfl) ⟨1013900, by rfl⟩ : syracuseStep 1351867 = 2027801) B2027801
theorem B1827017 : Blo 1200417 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B1802441 : Blo 1200417 1802441 := bstep (se 2 (by rfl) ⟨675915, by rfl⟩ : syracuseStep 1802441 = 1351831) B1351831
theorem B5775617 : Blo 1200417 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B1802555 : Blo 1200417 1802555 := bstep (se 1 (by rfl) ⟨1351916, by rfl⟩ : syracuseStep 1802555 = 2703833) B2703833
theorem B1802615 : Blo 1200417 1802615 := bstep (se 1 (by rfl) ⟨1351961, by rfl⟩ : syracuseStep 1802615 = 2703923) B2703923
theorem B1802639 : Blo 1200417 1802639 := bstep (se 1 (by rfl) ⟨1351979, by rfl⟩ : syracuseStep 1802639 = 2703959) B2703959
theorem B29680019 : Blo 1200417 29680019 := bstep (se 1 (by rfl) ⟨22260014, by rfl⟩ : syracuseStep 29680019 = 44520029) B44520029
theorem B1802681 : Blo 1200417 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B1802759 : Blo 1200417 1802759 := bstep (se 1 (by rfl) ⟨1352069, by rfl⟩ : syracuseStep 1802759 = 2704139) B2704139
theorem B2703887 : Blo 1200417 2703887 := bstep (se 1 (by rfl) ⟨2027915, by rfl⟩ : syracuseStep 2703887 = 4055831) B4055831
theorem B2703905 : Blo 1200417 2703905 := bstep (se 2 (by rfl) ⟨1013964, by rfl⟩ : syracuseStep 2703905 = 2027929) B2027929
theorem B1802795 : Blo 1200417 1802795 := bstep (se 1 (by rfl) ⟨1352096, by rfl⟩ : syracuseStep 1802795 = 2704193) B2704193
theorem B1802825 : Blo 1200417 1802825 := bstep (se 2 (by rfl) ⟨676059, by rfl⟩ : syracuseStep 1802825 = 1352119) B1352119
theorem B1352335 : Blo 1200417 1352335 := bstep (se 1 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 1352335 = 2028503) B2028503
theorem B1802939 : Blo 1200417 1802939 := bstep (se 1 (by rfl) ⟨1352204, by rfl⟩ : syracuseStep 1802939 = 2704409) B2704409
theorem B9126593 : Blo 1200417 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B6497005 : Blo 1200417 6497005 := bstep (se 3 (by rfl) ⟨1218188, by rfl⟩ : syracuseStep 6497005 = 2436377) B2436377
theorem B1802999 : Blo 1200417 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B3040001 : Blo 1200417 3040001 := bstep (se 2 (by rfl) ⟨1140000, by rfl⟩ : syracuseStep 3040001 = 2280001) B2280001
theorem B1803023 : Blo 1200417 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B1803065 : Blo 1200417 1803065 := bstep (se 2 (by rfl) ⟨676149, by rfl⟩ : syracuseStep 1803065 = 1352299) B1352299
theorem B2704247 : Blo 1200417 2704247 := bstep (se 1 (by rfl) ⟨2028185, by rfl⟩ : syracuseStep 2704247 = 4056371) B4056371
theorem B1803143 : Blo 1200417 1803143 := bstep (se 1 (by rfl) ⟨1352357, by rfl⟩ : syracuseStep 1803143 = 2704715) B2704715
theorem B1803179 : Blo 1200417 1803179 := bstep (se 1 (by rfl) ⟨1352384, by rfl⟩ : syracuseStep 1803179 = 2704769) B2704769
theorem B4055993 : Blo 1200417 4055993 := bstep (se 2 (by rfl) ⟨1520997, by rfl⟩ : syracuseStep 4055993 = 3041995) B3041995
theorem B1803209 : Blo 1200417 1803209 := bstep (se 2 (by rfl) ⟨676203, by rfl⟩ : syracuseStep 1803209 = 1352407) B1352407
theorem B7128107 : Blo 1200417 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B2704427 : Blo 1200417 2704427 := bstep (se 1 (by rfl) ⟨2028320, by rfl⟩ : syracuseStep 2704427 = 4056641) B4056641
theorem B1803323 : Blo 1200417 1803323 := bstep (se 1 (by rfl) ⟨1352492, by rfl⟩ : syracuseStep 1803323 = 2704985) B2704985
theorem B10003517 : Blo 1200417 10003517 := bstep (se 3 (by rfl) ⟨1875659, by rfl⟩ : syracuseStep 10003517 = 3751319) B3751319
theorem B17327191 : Blo 1200417 17327191 := bstep (se 1 (by rfl) ⟨12995393, by rfl⟩ : syracuseStep 17327191 = 25990787) B25990787
theorem B5129335 : Blo 1200417 5129335 := bstep (se 1 (by rfl) ⟨3847001, by rfl⟩ : syracuseStep 5129335 = 7694003) B7694003
theorem B3040375 : Blo 1200417 3040375 := bstep (se 1 (by rfl) ⟨2280281, by rfl⟩ : syracuseStep 3040375 = 4560563) B4560563
theorem B1803383 : Blo 1200417 1803383 := bstep (se 1 (by rfl) ⟨1352537, by rfl⟩ : syracuseStep 1803383 = 2705075) B2705075
theorem B1803407 : Blo 1200417 1803407 := bstep (se 1 (by rfl) ⟨1352555, by rfl⟩ : syracuseStep 1803407 = 2705111) B2705111
theorem B1803449 : Blo 1200417 1803449 := bstep (se 2 (by rfl) ⟨676293, by rfl⟩ : syracuseStep 1803449 = 1352587) B1352587
theorem B6161645 : Blo 1200417 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B1803527 : Blo 1200417 1803527 := bstep (se 1 (by rfl) ⟨1352645, by rfl⟩ : syracuseStep 1803527 = 2705291) B2705291
theorem B1803563 : Blo 1200417 1803563 := bstep (se 1 (by rfl) ⟨1352672, by rfl⟩ : syracuseStep 1803563 = 2705345) B2705345
theorem B14624059 : Blo 1200417 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B1803593 : Blo 1200417 1803593 := bstep (se 2 (by rfl) ⟨676347, by rfl⟩ : syracuseStep 1803593 = 1352695) B1352695
theorem B6079859 : Blo 1200417 6079859 := bstep (se 1 (by rfl) ⟨4559894, by rfl⟩ : syracuseStep 6079859 = 9119789) B9119789
theorem B2704787 : Blo 1200417 2704787 := bstep (se 1 (by rfl) ⟨2028590, by rfl⟩ : syracuseStep 2704787 = 4057181) B4057181
theorem B2311625 : Blo 1200417 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B2704841 : Blo 1200417 2704841 := bstep (se 2 (by rfl) ⟨1014315, by rfl⟩ : syracuseStep 2704841 = 2028631) B2028631
theorem B4056587 : Blo 1200417 4056587 := bstep (se 1 (by rfl) ⟨3042440, by rfl⟩ : syracuseStep 4056587 = 6084881) B6084881
theorem B2278945 : Blo 1200417 2278945 := bstep (se 2 (by rfl) ⟨854604, by rfl⟩ : syracuseStep 2278945 = 1709209) B1709209
theorem B3040811 : Blo 1200417 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B2434619 : Blo 1200417 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B4056695 : Blo 1200417 4056695 := bstep (se 1 (by rfl) ⟨3042521, by rfl⟩ : syracuseStep 4056695 = 6085043) B6085043
theorem B6842029 : Blo 1200417 6842029 := bstep (se 3 (by rfl) ⟨1282880, by rfl⟩ : syracuseStep 6842029 = 2565761) B2565761
theorem B1369915 : Blo 1200417 1369915 := bstep (se 1 (by rfl) ⟨1027436, by rfl⟩ : syracuseStep 1369915 = 2054873) B2054873
theorem B6080345 : Blo 1200417 6080345 := bstep (se 2 (by rfl) ⟨2280129, by rfl⟩ : syracuseStep 6080345 = 4560259) B4560259
theorem B4867955 : Blo 1200417 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B3467279 : Blo 1200417 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B4057289 : Blo 1200417 4057289 := bstep (se 2 (by rfl) ⟨1521483, by rfl⟩ : syracuseStep 4057289 = 3042967) B3042967
theorem B9742625 : Blo 1200417 9742625 := bstep (se 2 (by rfl) ⟨3653484, by rfl⟩ : syracuseStep 9742625 = 7306969) B7306969
theorem B2779451 : Blo 1200417 2779451 := bstep (se 1 (by rfl) ⟨2084588, by rfl⟩ : syracuseStep 2779451 = 4169177) B4169177
theorem B3041651 : Blo 1200417 3041651 := bstep (se 1 (by rfl) ⟨2281238, by rfl⟩ : syracuseStep 3041651 = 4562477) B4562477
theorem B3418487 : Blo 1200417 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B3041671 : Blo 1200417 3041671 := bstep (se 1 (by rfl) ⟨2281253, by rfl⟩ : syracuseStep 3041671 = 4562507) B4562507
theorem B2435599 : Blo 1200417 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B5777963 : Blo 1200417 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B5130839 : Blo 1200417 5130839 := bstep (se 1 (by rfl) ⟨3848129, by rfl⟩ : syracuseStep 5130839 = 7696259) B7696259
theorem B3041945 : Blo 1200417 3041945 := bstep (se 2 (by rfl) ⟨1140729, by rfl⟩ : syracuseStep 3041945 = 2281459) B2281459
theorem B69323525 : Blo 1200417 69323525 := bstep (se 4 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 69323525 = 12998161) B12998161
theorem B2026255 : Blo 1200417 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B4328225 : Blo 1200417 4328225 := bstep (se 2 (by rfl) ⟨1623084, by rfl⟩ : syracuseStep 4328225 = 3246169) B3246169
theorem B7703333 : Blo 1200417 7703333 := bstep (se 4 (by rfl) ⟨722187, by rfl⟩ : syracuseStep 7703333 = 1444375) B1444375
theorem B2280251 : Blo 1200417 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B3042107 : Blo 1200417 3042107 := bstep (se 1 (by rfl) ⟨2281580, by rfl⟩ : syracuseStep 3042107 = 4563161) B4563161
theorem B4057991 : Blo 1200417 4057991 := bstep (se 1 (by rfl) ⟨3043493, by rfl⟩ : syracuseStep 4057991 = 6086987) B6086987
theorem B11537315 : Blo 1200417 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B1625095 : Blo 1200417 1625095 := bstep (se 1 (by rfl) ⟨1218821, by rfl⟩ : syracuseStep 1625095 = 2437643) B2437643
theorem B3419147 : Blo 1200417 3419147 := bstep (se 1 (by rfl) ⟨2564360, by rfl⟩ : syracuseStep 3419147 = 5128721) B5128721
theorem B3042319 : Blo 1200417 3042319 := bstep (se 1 (by rfl) ⟨2281739, by rfl⟩ : syracuseStep 3042319 = 4563479) B4563479
theorem B13692077 : Blo 1200417 13692077 := bstep (se 3 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 13692077 = 5134529) B5134529
theorem B2280737 : Blo 1200417 2280737 := bstep (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) B1710553
theorem B3042593 : Blo 1200417 3042593 := bstep (se 2 (by rfl) ⟨1140972, by rfl⟩ : syracuseStep 3042593 = 2281945) B2281945
theorem B2026795 : Blo 1200417 2026795 := bstep (se 1 (by rfl) ⟨1520096, by rfl⟩ : syracuseStep 2026795 = 3040193) B3040193
theorem B34639163 : Blo 1200417 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B2026937 : Blo 1200417 2026937 := bstep (se 2 (by rfl) ⟨760101, by rfl⟩ : syracuseStep 2026937 = 1520203) B1520203
theorem B2280889 : Blo 1200417 2280889 := bstep (se 2 (by rfl) ⟨855333, by rfl⟩ : syracuseStep 2280889 = 1710667) B1710667
theorem B44461709 : Blo 1200417 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B2166419 : Blo 1200417 2166419 := bstep (se 1 (by rfl) ⟨1624814, by rfl⟩ : syracuseStep 2166419 = 3249629) B3249629
theorem B11710169 : Blo 1200417 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B6082451 : Blo 1200417 6082451 := bstep (se 1 (by rfl) ⟨4561838, by rfl⟩ : syracuseStep 6082451 = 9123677) B9123677
theorem B3338185 : Blo 1200417 3338185 := bstep (se 2 (by rfl) ⟨1251819, by rfl⟩ : syracuseStep 3338185 = 2503639) B2503639
theorem B4558801 : Blo 1200417 4558801 := bstep (se 2 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 4558801 = 3419101) B3419101
theorem B9129995 : Blo 1200417 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B6844445 : Blo 1200417 6844445 := bstep (se 3 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 6844445 = 2566667) B2566667
theorem B2027639 : Blo 1200417 2027639 := bstep (se 1 (by rfl) ⟨1520729, by rfl⟩ : syracuseStep 2027639 = 3041459) B3041459
theorem B1732795 : Blo 1200417 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B4559105 : Blo 1200417 4559105 := bstep (se 2 (by rfl) ⟨1709664, by rfl⟩ : syracuseStep 4559105 = 3419329) B3419329
theorem B1732871 : Blo 1200417 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B1519879 : Blo 1200417 1519879 := bstep (se 1 (by rfl) ⟨1139909, by rfl⟩ : syracuseStep 1519879 = 2279819) B2279819
theorem B3043595 : Blo 1200417 3043595 := bstep (se 1 (by rfl) ⟨2282696, by rfl⟩ : syracuseStep 3043595 = 4565393) B4565393
theorem B1200443 : Blo 1200417 1200443 := bstep (se 1 (by rfl) ⟨900332, by rfl⟩ : syracuseStep 1200443 = 1800665) B1800665
theorem B3289405 : Blo 1200417 3289405 := bstep (se 3 (by rfl) ⟨616763, by rfl⟩ : syracuseStep 3289405 = 1233527) B1233527
theorem B1200519 : Blo 1200417 1200519 := bstep (se 1 (by rfl) ⟨900389, by rfl⟩ : syracuseStep 1200519 = 1800779) B1800779
theorem B1200527 : Blo 1200417 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B1200571 : Blo 1200417 1200571 := bstep (se 1 (by rfl) ⟨900428, by rfl⟩ : syracuseStep 1200571 = 1800857) B1800857
theorem B5132753 : Blo 1200417 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B1200647 : Blo 1200417 1200647 := bstep (se 1 (by rfl) ⟨900485, by rfl⟩ : syracuseStep 1200647 = 1800971) B1800971
theorem B1200655 : Blo 1200417 1200655 := bstep (se 1 (by rfl) ⟨900491, by rfl⟩ : syracuseStep 1200655 = 1800983) B1800983
theorem B1200699 : Blo 1200417 1200699 := bstep (se 1 (by rfl) ⟨900524, by rfl⟩ : syracuseStep 1200699 = 1801049) B1801049
theorem B3420731 : Blo 1200417 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B2028091 : Blo 1200417 2028091 := bstep (se 1 (by rfl) ⟨1521068, by rfl⟩ : syracuseStep 2028091 = 3042137) B3042137
theorem B3420787 : Blo 1200417 3420787 := bstep (se 1 (by rfl) ⟨2565590, by rfl⟩ : syracuseStep 3420787 = 5131181) B5131181
theorem B1200775 : Blo 1200417 1200775 := bstep (se 1 (by rfl) ⟨900581, by rfl⟩ : syracuseStep 1200775 = 1801163) B1801163
theorem B2888327 : Blo 1200417 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B1200783 : Blo 1200417 1200783 := bstep (se 1 (by rfl) ⟨900587, by rfl⟩ : syracuseStep 1200783 = 1801175) B1801175
theorem B1520299 : Blo 1200417 1520299 := bstep (se 1 (by rfl) ⟨1140224, by rfl⟩ : syracuseStep 1520299 = 2280449) B2280449
theorem B1200827 : Blo 1200417 1200827 := bstep (se 1 (by rfl) ⟨900620, by rfl⟩ : syracuseStep 1200827 = 1801241) B1801241
theorem B4559561 : Blo 1200417 4559561 := bstep (se 2 (by rfl) ⟨1709835, by rfl⟩ : syracuseStep 4559561 = 3419671) B3419671
theorem B2028233 : Blo 1200417 2028233 := bstep (se 2 (by rfl) ⟨760587, by rfl⟩ : syracuseStep 2028233 = 1521175) B1521175
theorem B1200903 : Blo 1200417 1200903 := bstep (se 1 (by rfl) ⟨900677, by rfl⟩ : syracuseStep 1200903 = 1801355) B1801355
theorem B4051727 : Blo 1200417 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B1200911 : Blo 1200417 1200911 := bstep (se 1 (by rfl) ⟨900683, by rfl⟩ : syracuseStep 1200911 = 1801367) B1801367
theorem B5477179 : Blo 1200417 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B1200955 : Blo 1200417 1200955 := bstep (se 1 (by rfl) ⟨900716, by rfl⟩ : syracuseStep 1200955 = 1801433) B1801433
theorem B13161305 : Blo 1200417 13161305 := bstep (se 2 (by rfl) ⟨4935489, by rfl⟩ : syracuseStep 13161305 = 9870979) B9870979
theorem B5559155 : Blo 1200417 5559155 := bstep (se 1 (by rfl) ⟨4169366, by rfl⟩ : syracuseStep 5559155 = 8338733) B8338733
theorem B1201031 : Blo 1200417 1201031 := bstep (se 1 (by rfl) ⟨900773, by rfl⟩ : syracuseStep 1201031 = 1801547) B1801547
theorem B1201039 : Blo 1200417 1201039 := bstep (se 1 (by rfl) ⟨900779, by rfl⟩ : syracuseStep 1201039 = 1801559) B1801559
theorem B1520527 : Blo 1200417 1520527 := bstep (se 1 (by rfl) ⟨1140395, by rfl⟩ : syracuseStep 1520527 = 2280791) B2280791
theorem B8328089 : Blo 1200417 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B1201083 : Blo 1200417 1201083 := bstep (se 1 (by rfl) ⟨900812, by rfl⟩ : syracuseStep 1201083 = 1801625) B1801625
theorem B3421129 : Blo 1200417 3421129 := bstep (se 2 (by rfl) ⟨1282923, by rfl⟩ : syracuseStep 3421129 = 2565847) B2565847
theorem B1201159 : Blo 1200417 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B1201167 : Blo 1200417 1201167 := bstep (se 1 (by rfl) ⟨900875, by rfl⟩ : syracuseStep 1201167 = 1801751) B1801751
theorem B4051997 : Blo 1200417 4051997 := bstep (se 3 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 4051997 = 1519499) B1519499
theorem B1201211 : Blo 1200417 1201211 := bstep (se 1 (by rfl) ⟨900908, by rfl⟩ : syracuseStep 1201211 = 1801817) B1801817
theorem B7803965 : Blo 1200417 7803965 := bstep (se 3 (by rfl) ⟨1463243, by rfl⟩ : syracuseStep 7803965 = 2926487) B2926487
theorem B1201287 : Blo 1200417 1201287 := bstep (se 1 (by rfl) ⟨900965, by rfl⟩ : syracuseStep 1201287 = 1801931) B1801931
theorem B1201295 : Blo 1200417 1201295 := bstep (se 1 (by rfl) ⟨900971, by rfl⟩ : syracuseStep 1201295 = 1801943) B1801943
theorem B3249305 : Blo 1200417 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B2282681 : Blo 1200417 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B1201339 : Blo 1200417 1201339 := bstep (se 1 (by rfl) ⟨901004, by rfl⟩ : syracuseStep 1201339 = 1802009) B1802009
theorem B1201415 : Blo 1200417 1201415 := bstep (se 1 (by rfl) ⟨901061, by rfl⟩ : syracuseStep 1201415 = 1802123) B1802123
theorem B3847439 : Blo 1200417 3847439 := bstep (se 1 (by rfl) ⟨2885579, by rfl⟩ : syracuseStep 3847439 = 5771159) B5771159
theorem B1201423 : Blo 1200417 1201423 := bstep (se 1 (by rfl) ⟨901067, by rfl⟩ : syracuseStep 1201423 = 1802135) B1802135
theorem B1201467 : Blo 1200417 1201467 := bstep (se 1 (by rfl) ⟨901100, by rfl⟩ : syracuseStep 1201467 = 1802201) B1802201
theorem B1201543 : Blo 1200417 1201543 := bstep (se 1 (by rfl) ⟨901157, by rfl⟩ : syracuseStep 1201543 = 1802315) B1802315
theorem B2028935 : Blo 1200417 2028935 := bstep (se 1 (by rfl) ⟨1521701, by rfl⟩ : syracuseStep 2028935 = 3043403) B3043403
theorem B1201551 : Blo 1200417 1201551 := bstep (se 1 (by rfl) ⟨901163, by rfl⟩ : syracuseStep 1201551 = 1802327) B1802327
theorem B1201595 : Blo 1200417 1201595 := bstep (se 1 (by rfl) ⟨901196, by rfl⟩ : syracuseStep 1201595 = 1802393) B1802393
theorem B15390161 : Blo 1200417 15390161 := bstep (se 2 (by rfl) ⟨5771310, by rfl⟩ : syracuseStep 15390161 = 11542621) B11542621
theorem B8779229 : Blo 1200417 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B6493699 : Blo 1200417 6493699 := bstep (se 1 (by rfl) ⟨4870274, by rfl⟩ : syracuseStep 6493699 = 9740549) B9740549
theorem B1201671 : Blo 1200417 1201671 := bstep (se 1 (by rfl) ⟨901253, by rfl⟩ : syracuseStep 1201671 = 1802507) B1802507
theorem B1201679 : Blo 1200417 1201679 := bstep (se 1 (by rfl) ⟨901259, by rfl⟩ : syracuseStep 1201679 = 1802519) B1802519
theorem B1201723 : Blo 1200417 1201723 := bstep (se 1 (by rfl) ⟨901292, by rfl⟩ : syracuseStep 1201723 = 1802585) B1802585
theorem B14612035 : Blo 1200417 14612035 := bstep (se 1 (by rfl) ⟨10959026, by rfl⟩ : syracuseStep 14612035 = 21918053) B21918053
theorem B1521271 : Blo 1200417 1521271 := bstep (se 1 (by rfl) ⟨1140953, by rfl⟩ : syracuseStep 1521271 = 2281907) B2281907
theorem B1201799 : Blo 1200417 1201799 := bstep (se 1 (by rfl) ⟨901349, by rfl⟩ : syracuseStep 1201799 = 1802699) B1802699
theorem B1201807 : Blo 1200417 1201807 := bstep (se 1 (by rfl) ⟨901355, by rfl⟩ : syracuseStep 1201807 = 1802711) B1802711
theorem B1201851 : Blo 1200417 1201851 := bstep (se 1 (by rfl) ⟨901388, by rfl⟩ : syracuseStep 1201851 = 1802777) B1802777
theorem B1201927 : Blo 1200417 1201927 := bstep (se 1 (by rfl) ⟨901445, by rfl⟩ : syracuseStep 1201927 = 1802891) B1802891
theorem B1201935 : Blo 1200417 1201935 := bstep (se 1 (by rfl) ⟨901451, by rfl⟩ : syracuseStep 1201935 = 1802903) B1802903
theorem B2701115 : Blo 1200417 2701115 := bstep (se 1 (by rfl) ⟨2025836, by rfl⟩ : syracuseStep 2701115 = 4051673) B4051673
theorem B1201979 : Blo 1200417 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B1202055 : Blo 1200417 1202055 := bstep (se 1 (by rfl) ⟨901541, by rfl⟩ : syracuseStep 1202055 = 1803083) B1803083
theorem B1202063 : Blo 1200417 1202063 := bstep (se 1 (by rfl) ⟨901547, by rfl⟩ : syracuseStep 1202063 = 1803095) B1803095
theorem B2701241 : Blo 1200417 2701241 := bstep (se 2 (by rfl) ⟨1012965, by rfl⟩ : syracuseStep 2701241 = 2025931) B2025931
theorem B1202107 : Blo 1200417 1202107 := bstep (se 1 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 1202107 = 1803161) B1803161
theorem B1521595 : Blo 1200417 1521595 := bstep (se 1 (by rfl) ⟨1141196, by rfl⟩ : syracuseStep 1521595 = 2282393) B2282393
theorem B1202183 : Blo 1200417 1202183 := bstep (se 1 (by rfl) ⟨901637, by rfl⟩ : syracuseStep 1202183 = 1803275) B1803275
theorem B1218575 : Blo 1200417 1218575 := bstep (se 1 (by rfl) ⟨913931, by rfl⟩ : syracuseStep 1218575 = 1827863) B1827863
theorem B1202191 : Blo 1200417 1202191 := bstep (se 1 (by rfl) ⟨901643, by rfl⟩ : syracuseStep 1202191 = 1803287) B1803287
theorem B1202235 : Blo 1200417 1202235 := bstep (se 1 (by rfl) ⟨901676, by rfl⟩ : syracuseStep 1202235 = 1803353) B1803353
theorem B1202311 : Blo 1200417 1202311 := bstep (se 1 (by rfl) ⟨901733, by rfl⟩ : syracuseStep 1202311 = 1803467) B1803467
theorem B1202319 : Blo 1200417 1202319 := bstep (se 1 (by rfl) ⟨901739, by rfl⟩ : syracuseStep 1202319 = 1803479) B1803479
theorem B1202363 : Blo 1200417 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B3651841 : Blo 1200417 3651841 := bstep (se 2 (by rfl) ⟨1369440, by rfl⟩ : syracuseStep 3651841 = 2738881) B2738881
theorem B2701583 : Blo 1200417 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B2701601 : Blo 1200417 2701601 := bstep (se 2 (by rfl) ⟨1013100, by rfl⟩ : syracuseStep 2701601 = 2026201) B2026201
theorem B5773619 : Blo 1200417 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B1923463 : Blo 1200417 1923463 := bstep (se 1 (by rfl) ⟨1442597, by rfl⟩ : syracuseStep 1923463 = 2885195) B2885195
theorem B4053401 : Blo 1200417 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B1800635 : Blo 1200417 1800635 := bstep (se 1 (by rfl) ⟨1350476, by rfl⟩ : syracuseStep 1800635 = 2700953) B2700953
theorem B5773771 : Blo 1200417 5773771 := bstep (se 1 (by rfl) ⟨4330328, by rfl⟩ : syracuseStep 5773771 = 8660657) B8660657
theorem B6846929 : Blo 1200417 6846929 := bstep (se 2 (by rfl) ⟨2567598, by rfl⟩ : syracuseStep 6846929 = 5135197) B5135197
theorem B1800695 : Blo 1200417 1800695 := bstep (se 1 (by rfl) ⟨1350521, by rfl⟩ : syracuseStep 1800695 = 2701043) B2701043
theorem B1800719 : Blo 1200417 1800719 := bstep (se 1 (by rfl) ⟨1350539, by rfl⟩ : syracuseStep 1800719 = 2701079) B2701079
theorem B1800761 : Blo 1200417 1800761 := bstep (se 2 (by rfl) ⟨675285, by rfl⟩ : syracuseStep 1800761 = 1350571) B1350571
theorem B2701943 : Blo 1200417 2701943 := bstep (se 1 (by rfl) ⟨2026457, by rfl⟩ : syracuseStep 2701943 = 4052915) B4052915
theorem B1800839 : Blo 1200417 1800839 := bstep (se 1 (by rfl) ⟨1350629, by rfl⟩ : syracuseStep 1800839 = 2701259) B2701259
theorem B3652231 : Blo 1200417 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B1800875 : Blo 1200417 1800875 := bstep (se 1 (by rfl) ⟨1350656, by rfl⟩ : syracuseStep 1800875 = 2701313) B2701313
theorem B1800905 : Blo 1200417 1800905 := bstep (se 2 (by rfl) ⟨675339, by rfl⟩ : syracuseStep 1800905 = 1350679) B1350679
theorem B29637413 : Blo 1200417 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2702123 : Blo 1200417 2702123 := bstep (se 1 (by rfl) ⟨2026592, by rfl⟩ : syracuseStep 2702123 = 4053185) B4053185
theorem B1801019 : Blo 1200417 1801019 := bstep (se 1 (by rfl) ⟨1350764, by rfl⟩ : syracuseStep 1801019 = 2701529) B2701529
theorem B1801079 : Blo 1200417 1801079 := bstep (se 1 (by rfl) ⟨1350809, by rfl⟩ : syracuseStep 1801079 = 2701619) B2701619
theorem B1350535 : Blo 1200417 1350535 := bstep (se 1 (by rfl) ⟨1012901, by rfl⟩ : syracuseStep 1350535 = 2025803) B2025803
theorem B1801103 : Blo 1200417 1801103 := bstep (se 1 (by rfl) ⟨1350827, by rfl⟩ : syracuseStep 1801103 = 2701655) B2701655
theorem B13687703 : Blo 1200417 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B6085529 : Blo 1200417 6085529 := bstep (se 2 (by rfl) ⟨2282073, by rfl⟩ : syracuseStep 6085529 = 4564147) B4564147
theorem B1801145 : Blo 1200417 1801145 := bstep (se 2 (by rfl) ⟨675429, by rfl⟩ : syracuseStep 1801145 = 1350859) B1350859
theorem B1802231 : Blo 1200417 1802231 := bstep (se 1 (by rfl) ⟨1351673, by rfl⟩ : syracuseStep 1802231 = 2703347) B2703347
theorem B1801223 : Blo 1200417 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B3652619 : Blo 1200417 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B1801259 : Blo 1200417 1801259 := bstep (se 1 (by rfl) ⟨1350944, by rfl⟩ : syracuseStep 1801259 = 2701889) B2701889
theorem B1825849 : Blo 1200417 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1350715 : Blo 1200417 1350715 := bstep (se 1 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 1350715 = 2026073) B2026073
theorem B3423293 : Blo 1200417 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B1801289 : Blo 1200417 1801289 := bstep (se 2 (by rfl) ⟨675483, by rfl⟩ : syracuseStep 1801289 = 1350967) B1350967
theorem B4054103 : Blo 1200417 4054103 := bstep (se 1 (by rfl) ⟨3040577, by rfl⟩ : syracuseStep 4054103 = 6081155) B6081155
theorem B2702483 : Blo 1200417 2702483 := bstep (se 1 (by rfl) ⟨2026862, by rfl⟩ : syracuseStep 2702483 = 4053725) B4053725
theorem B1801403 : Blo 1200417 1801403 := bstep (se 1 (by rfl) ⟨1351052, by rfl⟩ : syracuseStep 1801403 = 2702105) B2702105
theorem B9116873 : Blo 1200417 9116873 := bstep (se 2 (by rfl) ⟨3418827, by rfl⟩ : syracuseStep 9116873 = 6837655) B6837655
theorem B2702537 : Blo 1200417 2702537 := bstep (se 2 (by rfl) ⟨1013451, by rfl⟩ : syracuseStep 2702537 = 2026903) B2026903
theorem B5848301 : Blo 1200417 5848301 := bstep (se 3 (by rfl) ⟨1096556, by rfl⟩ : syracuseStep 5848301 = 2193113) B2193113
theorem B1801463 : Blo 1200417 1801463 := bstep (se 1 (by rfl) ⟨1351097, by rfl⟩ : syracuseStep 1801463 = 2702195) B2702195
theorem B1801487 : Blo 1200417 1801487 := bstep (se 1 (by rfl) ⟨1351115, by rfl⟩ : syracuseStep 1801487 = 2702231) B2702231
theorem B3423521 : Blo 1200417 3423521 := bstep (se 2 (by rfl) ⟨1283820, by rfl⟩ : syracuseStep 3423521 = 2567641) B2567641
theorem B1850681 : Blo 1200417 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B1801529 : Blo 1200417 1801529 := bstep (se 2 (by rfl) ⟨675573, by rfl⟩ : syracuseStep 1801529 = 1351147) B1351147
theorem B1801607 : Blo 1200417 1801607 := bstep (se 1 (by rfl) ⟨1351205, by rfl⟩ : syracuseStep 1801607 = 2702411) B2702411
theorem B6495623 : Blo 1200417 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B4332953 : Blo 1200417 4332953 := bstep (se 2 (by rfl) ⟨1624857, by rfl⟩ : syracuseStep 4332953 = 3249715) B3249715
theorem B1801643 : Blo 1200417 1801643 := bstep (se 1 (by rfl) ⟨1351232, by rfl⟩ : syracuseStep 1801643 = 2702465) B2702465
theorem B1801673 : Blo 1200417 1801673 := bstep (se 2 (by rfl) ⟨675627, by rfl⟩ : syracuseStep 1801673 = 1351255) B1351255
theorem B3038735 : Blo 1200417 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B1351183 : Blo 1200417 1351183 := bstep (se 1 (by rfl) ⟨1013387, by rfl⟩ : syracuseStep 1351183 = 2026775) B2026775
theorem B1801787 : Blo 1200417 1801787 := bstep (se 1 (by rfl) ⟨1351340, by rfl⟩ : syracuseStep 1801787 = 2702681) B2702681
theorem B4054589 : Blo 1200417 4054589 := bstep (se 3 (by rfl) ⟨760235, by rfl⟩ : syracuseStep 4054589 = 1520471) B1520471
theorem B1801847 : Blo 1200417 1801847 := bstep (se 1 (by rfl) ⟨1351385, by rfl⟩ : syracuseStep 1801847 = 2702771) B2702771
theorem B3423863 : Blo 1200417 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B1801871 : Blo 1200417 1801871 := bstep (se 1 (by rfl) ⟨1351403, by rfl⟩ : syracuseStep 1801871 = 2702807) B2702807
theorem B3038867 : Blo 1200417 3038867 := bstep (se 1 (by rfl) ⟨2279150, by rfl⟩ : syracuseStep 3038867 = 4558301) B4558301
theorem B1801913 : Blo 1200417 1801913 := bstep (se 2 (by rfl) ⟨675717, by rfl⟩ : syracuseStep 1801913 = 1351435) B1351435
theorem B4562689 : Blo 1200417 4562689 := bstep (se 2 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 4562689 = 3422017) B3422017
theorem B1826567 : Blo 1200417 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B1801991 : Blo 1200417 1801991 := bstep (se 1 (by rfl) ⟨1351493, by rfl⟩ : syracuseStep 1801991 = 2702987) B2702987
theorem B1924879 : Blo 1200417 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B1802027 : Blo 1200417 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B1802057 : Blo 1200417 1802057 := bstep (se 2 (by rfl) ⟨675771, by rfl⟩ : syracuseStep 1802057 = 1351543) B1351543
theorem B11550539 : Blo 1200417 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B2703239 : Blo 1200417 2703239 := bstep (se 1 (by rfl) ⟨2027429, by rfl⟩ : syracuseStep 2703239 = 4054859) B4054859
theorem B1802171 : Blo 1200417 1802171 := bstep (se 1 (by rfl) ⟨1351628, by rfl⟩ : syracuseStep 1802171 = 2703257) B2703257
theorem B6086663 : Blo 1200417 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1802249 : Blo 1200417 1802249 := bstep (se 2 (by rfl) ⟨675843, by rfl⟩ : syracuseStep 1802249 = 1351687) B1351687
theorem B4562963 : Blo 1200417 4562963 := bstep (se 1 (by rfl) ⟨3422222, by rfl⟩ : syracuseStep 4562963 = 6844445) B6844445
theorem B1802279 : Blo 1200417 1802279 := bstep (se 1 (by rfl) ⟨1351709, by rfl⟩ : syracuseStep 1802279 = 2703419) B2703419
theorem B1351759 : Blo 1200417 1351759 := bstep (se 1 (by rfl) ⟨1013819, by rfl⟩ : syracuseStep 1351759 = 2027639) B2027639
theorem B38961269 : Blo 1200417 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1802363 : Blo 1200417 1802363 := bstep (se 1 (by rfl) ⟨1351772, by rfl⟩ : syracuseStep 1802363 = 2703545) B2703545
theorem B3039403 : Blo 1200417 3039403 := bstep (se 1 (by rfl) ⟨2279552, by rfl⟩ : syracuseStep 3039403 = 4559105) B4559105
theorem B3850411 : Blo 1200417 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B1802489 : Blo 1200417 1802489 := bstep (se 2 (by rfl) ⟨675933, by rfl⟩ : syracuseStep 1802489 = 1351867) B1351867
theorem B1802591 : Blo 1200417 1802591 := bstep (se 1 (by rfl) ⟨1351943, by rfl⟩ : syracuseStep 1802591 = 2703887) B2703887
theorem B1802603 : Blo 1200417 1802603 := bstep (se 1 (by rfl) ⟨1351952, by rfl⟩ : syracuseStep 1802603 = 2703905) B2703905
theorem B1925551 : Blo 1200417 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B3039707 : Blo 1200417 3039707 := bstep (se 1 (by rfl) ⟨2279780, by rfl⟩ : syracuseStep 3039707 = 4559561) B4559561
theorem B1352155 : Blo 1200417 1352155 := bstep (se 1 (by rfl) ⟨1014116, by rfl⟩ : syracuseStep 1352155 = 2028233) B2028233
theorem B6087149 : Blo 1200417 6087149 := bstep (se 3 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 6087149 = 2282681) B2282681
theorem B2564617 : Blo 1200417 2564617 := bstep (se 2 (by rfl) ⟨961731, by rfl⟩ : syracuseStep 2564617 = 1923463) B1923463
theorem B4055561 : Blo 1200417 4055561 := bstep (se 2 (by rfl) ⟨1520835, by rfl⟩ : syracuseStep 4055561 = 3041671) B3041671
theorem B8774203 : Blo 1200417 8774203 := bstep (se 1 (by rfl) ⟨6580652, by rfl⟩ : syracuseStep 8774203 = 13161305) B13161305
theorem B1802831 : Blo 1200417 1802831 := bstep (se 1 (by rfl) ⟨1352123, by rfl⟩ : syracuseStep 1802831 = 2704247) B2704247
theorem B2703995 : Blo 1200417 2703995 := bstep (se 1 (by rfl) ⟨2027996, by rfl⟩ : syracuseStep 2703995 = 4055993) B4055993
theorem B4620989 : Blo 1200417 4620989 := bstep (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) B1732871
theorem B4752071 : Blo 1200417 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B1802951 : Blo 1200417 1802951 := bstep (se 1 (by rfl) ⟨1352213, by rfl⟩ : syracuseStep 1802951 = 2704427) B2704427
theorem B6669011 : Blo 1200417 6669011 := bstep (se 1 (by rfl) ⟨5001758, by rfl⟩ : syracuseStep 6669011 = 10003517) B10003517
theorem B5202643 : Blo 1200417 5202643 := bstep (se 1 (by rfl) ⟨3901982, by rfl⟩ : syracuseStep 5202643 = 7803965) B7803965
theorem B2704121 : Blo 1200417 2704121 := bstep (se 2 (by rfl) ⟨1014045, by rfl⟩ : syracuseStep 2704121 = 2028091) B2028091
theorem B2564959 : Blo 1200417 2564959 := bstep (se 1 (by rfl) ⟨1923719, by rfl⟩ : syracuseStep 2564959 = 3847439) B3847439
theorem B1803113 : Blo 1200417 1803113 := bstep (se 2 (by rfl) ⟨676167, by rfl⟩ : syracuseStep 1803113 = 1352335) B1352335
theorem B1352623 : Blo 1200417 1352623 := bstep (se 1 (by rfl) ⟨1014467, by rfl⟩ : syracuseStep 1352623 = 2028935) B2028935
theorem B1803191 : Blo 1200417 1803191 := bstep (se 1 (by rfl) ⟨1352393, by rfl⟩ : syracuseStep 1803191 = 2704787) B2704787
theorem B1803227 : Blo 1200417 1803227 := bstep (se 1 (by rfl) ⟨1352420, by rfl⟩ : syracuseStep 1803227 = 2704841) B2704841
theorem B2704391 : Blo 1200417 2704391 := bstep (se 1 (by rfl) ⟨2028293, by rfl⟩ : syracuseStep 2704391 = 4056587) B4056587
theorem B1623079 : Blo 1200417 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B2704463 : Blo 1200417 2704463 := bstep (se 1 (by rfl) ⟨2028347, by rfl⟩ : syracuseStep 2704463 = 4056695) B4056695
theorem B3245303 : Blo 1200417 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B2311519 : Blo 1200417 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B4056425 : Blo 1200417 4056425 := bstep (se 2 (by rfl) ⟨1521159, by rfl⟩ : syracuseStep 4056425 = 3042319) B3042319
theorem B2434465 : Blo 1200417 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B23102921 : Blo 1200417 23102921 := bstep (se 2 (by rfl) ⟨8663595, by rfl⟩ : syracuseStep 23102921 = 17327191) B17327191
theorem B2704859 : Blo 1200417 2704859 := bstep (se 1 (by rfl) ⟨2028644, by rfl⟩ : syracuseStep 2704859 = 4057289) B4057289
theorem B1852967 : Blo 1200417 1852967 := bstep (se 1 (by rfl) ⟨1389725, by rfl⟩ : syracuseStep 1852967 = 2779451) B2779451
theorem B2278991 : Blo 1200417 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B4564619 : Blo 1200417 4564619 := bstep (se 1 (by rfl) ⟨3423464, by rfl⟩ : syracuseStep 4564619 = 6846929) B6846929
theorem B3851975 : Blo 1200417 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B19498745 : Blo 1200417 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B2885483 : Blo 1200417 2885483 := bstep (se 1 (by rfl) ⟨2164112, by rfl⟩ : syracuseStep 2885483 = 4328225) B4328225
theorem B3041185 : Blo 1200417 3041185 := bstep (se 2 (by rfl) ⟨1140444, by rfl⟩ : syracuseStep 3041185 = 2280889) B2280889
theorem B2705327 : Blo 1200417 2705327 := bstep (se 1 (by rfl) ⟨2028995, by rfl⟩ : syracuseStep 2705327 = 4057991) B4057991
theorem B4057019 : Blo 1200417 4057019 := bstep (se 1 (by rfl) ⟨3042764, by rfl⟩ : syracuseStep 4057019 = 6085529) B6085529
theorem B2279431 : Blo 1200417 2279431 := bstep (se 1 (by rfl) ⟨1709573, by rfl⟩ : syracuseStep 2279431 = 3419147) B3419147
theorem B19482713 : Blo 1200417 19482713 := bstep (se 2 (by rfl) ⟨7306017, by rfl⟩ : syracuseStep 19482713 = 14612035) B14612035
theorem B9128051 : Blo 1200417 9128051 := bstep (se 1 (by rfl) ⟨6846038, by rfl⟩ : syracuseStep 9128051 = 13692077) B13692077
theorem B6080669 : Blo 1200417 6080669 := bstep (se 3 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 6080669 = 2280251) B2280251
theorem B2025823 : Blo 1200417 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B2566505 : Blo 1200417 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B29641139 : Blo 1200417 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B2025911 : Blo 1200417 2025911 := bstep (se 1 (by rfl) ⟨1519433, by rfl⟩ : syracuseStep 2025911 = 3038867) B3038867
theorem B1444279 : Blo 1200417 1444279 := bstep (se 1 (by rfl) ⟨1083209, by rfl⟩ : syracuseStep 1444279 = 2166419) B2166419
theorem B4450913 : Blo 1200417 4450913 := bstep (se 2 (by rfl) ⟨1669092, by rfl⟩ : syracuseStep 4450913 = 3338185) B3338185
theorem B19786679 : Blo 1200417 19786679 := bstep (se 1 (by rfl) ⟨14840009, by rfl⟩ : syracuseStep 19786679 = 29680019) B29680019
theorem B4869121 : Blo 1200417 4869121 := bstep (se 2 (by rfl) ⟨1825920, by rfl⟩ : syracuseStep 4869121 = 3651841) B3651841
theorem B2026505 : Blo 1200417 2026505 := bstep (se 2 (by rfl) ⟨759939, by rfl⟩ : syracuseStep 2026505 = 1519879) B1519879
theorem B2280487 : Blo 1200417 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B4385873 : Blo 1200417 4385873 := bstep (se 2 (by rfl) ⟨1644702, by rfl⟩ : syracuseStep 4385873 = 3289405) B3289405
theorem B2026667 : Blo 1200417 2026667 := bstep (se 1 (by rfl) ⟨1520000, by rfl⟩ : syracuseStep 2026667 = 3040001) B3040001
theorem B3706103 : Blo 1200417 3706103 := bstep (se 1 (by rfl) ⟨2779577, by rfl⟩ : syracuseStep 3706103 = 5559155) B5559155
theorem B3247465 : Blo 1200417 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B6081965 : Blo 1200417 6081965 := bstep (se 3 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 6081965 = 2280737) B2280737
theorem B2166203 : Blo 1200417 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B4107763 : Blo 1200417 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B4869641 : Blo 1200417 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B2027065 : Blo 1200417 2027065 := bstep (se 2 (by rfl) ⟨760149, by rfl⟩ : syracuseStep 2027065 = 1520299) B1520299
theorem B10260107 : Blo 1200417 10260107 := bstep (se 1 (by rfl) ⟨7695080, by rfl⟩ : syracuseStep 10260107 = 15390161) B15390161
theorem B8662673 : Blo 1200417 8662673 := bstep (se 2 (by rfl) ⟨3248502, by rfl⟩ : syracuseStep 8662673 = 6497005) B6497005
theorem B5852819 : Blo 1200417 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B2027207 : Blo 1200417 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B7302905 : Blo 1200417 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B2027369 : Blo 1200417 2027369 := bstep (se 2 (by rfl) ⟨760263, by rfl⟩ : syracuseStep 2027369 = 1520527) B1520527
theorem B6164333 : Blo 1200417 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B36966293 : Blo 1200417 36966293 := bstep (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) B1732795
theorem B2166793 : Blo 1200417 2166793 := bstep (se 2 (by rfl) ⟨812547, by rfl⟩ : syracuseStep 2166793 = 1625095) B1625095
theorem B2027767 : Blo 1200417 2027767 := bstep (se 1 (by rfl) ⟨1520825, by rfl⟩ : syracuseStep 2027767 = 3041651) B3041651
theorem B1200423 : Blo 1200417 1200423 := bstep (se 1 (by rfl) ⟨900317, by rfl⟩ : syracuseStep 1200423 = 1800635) B1800635
theorem B1200463 : Blo 1200417 1200463 := bstep (se 1 (by rfl) ⟨900347, by rfl⟩ : syracuseStep 1200463 = 1800695) B1800695
theorem B1200479 : Blo 1200417 1200479 := bstep (se 1 (by rfl) ⟨900359, by rfl⟩ : syracuseStep 1200479 = 1800719) B1800719
theorem B1200507 : Blo 1200417 1200507 := bstep (se 1 (by rfl) ⟨900380, by rfl⟩ : syracuseStep 1200507 = 1800761) B1800761
theorem B3420559 : Blo 1200417 3420559 := bstep (se 1 (by rfl) ⟨2565419, by rfl⟩ : syracuseStep 3420559 = 5130839) B5130839
theorem B1200559 : Blo 1200417 1200559 := bstep (se 1 (by rfl) ⟨900419, by rfl⟩ : syracuseStep 1200559 = 1800839) B1800839
theorem B2027963 : Blo 1200417 2027963 := bstep (se 1 (by rfl) ⟨1520972, by rfl⟩ : syracuseStep 2027963 = 3041945) B3041945
theorem B1200583 : Blo 1200417 1200583 := bstep (se 1 (by rfl) ⟨900437, by rfl⟩ : syracuseStep 1200583 = 1800875) B1800875
theorem B1200603 : Blo 1200417 1200603 := bstep (se 1 (by rfl) ⟨900452, by rfl⟩ : syracuseStep 1200603 = 1800905) B1800905
theorem B46215683 : Blo 1200417 46215683 := bstep (se 1 (by rfl) ⟨34661762, by rfl⟩ : syracuseStep 46215683 = 69323525) B69323525
theorem B1200679 : Blo 1200417 1200679 := bstep (se 1 (by rfl) ⟨900509, by rfl⟩ : syracuseStep 1200679 = 1801019) B1801019
theorem B2028071 : Blo 1200417 2028071 := bstep (se 1 (by rfl) ⟨1521053, by rfl⟩ : syracuseStep 2028071 = 3042107) B3042107
theorem B1200719 : Blo 1200417 1200719 := bstep (se 1 (by rfl) ⟨900539, by rfl⟩ : syracuseStep 1200719 = 1801079) B1801079
theorem B1200735 : Blo 1200417 1200735 := bstep (se 1 (by rfl) ⟨900551, by rfl⟩ : syracuseStep 1200735 = 1801103) B1801103
theorem B1200763 : Blo 1200417 1200763 := bstep (se 1 (by rfl) ⟨900572, by rfl⟩ : syracuseStep 1200763 = 1801145) B1801145
theorem B1200815 : Blo 1200417 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B1200839 : Blo 1200417 1200839 := bstep (se 1 (by rfl) ⟨900629, by rfl⟩ : syracuseStep 1200839 = 1801259) B1801259
theorem B2282195 : Blo 1200417 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B1200859 : Blo 1200417 1200859 := bstep (se 1 (by rfl) ⟨900644, by rfl⟩ : syracuseStep 1200859 = 1801289) B1801289
theorem B1200935 : Blo 1200417 1200935 := bstep (se 1 (by rfl) ⟨900701, by rfl⟩ : syracuseStep 1200935 = 1801403) B1801403
theorem B2028361 : Blo 1200417 2028361 := bstep (se 2 (by rfl) ⟨760635, by rfl⟩ : syracuseStep 2028361 = 1521271) B1521271
theorem B1200975 : Blo 1200417 1200975 := bstep (se 1 (by rfl) ⟨900731, by rfl⟩ : syracuseStep 1200975 = 1801463) B1801463
theorem B1200991 : Blo 1200417 1200991 := bstep (se 1 (by rfl) ⟨900743, by rfl⟩ : syracuseStep 1200991 = 1801487) B1801487
theorem B2028395 : Blo 1200417 2028395 := bstep (se 1 (by rfl) ⟨1521296, by rfl⟩ : syracuseStep 2028395 = 3042593) B3042593
theorem B2282347 : Blo 1200417 2282347 := bstep (se 1 (by rfl) ⟨1711760, by rfl⟩ : syracuseStep 2282347 = 3423521) B3423521
theorem B1233787 : Blo 1200417 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B1201019 : Blo 1200417 1201019 := bstep (se 1 (by rfl) ⟨900764, by rfl⟩ : syracuseStep 1201019 = 1801529) B1801529
theorem B9122705 : Blo 1200417 9122705 := bstep (se 2 (by rfl) ⟨3421014, by rfl⟩ : syracuseStep 9122705 = 6842029) B6842029
theorem B1201071 : Blo 1200417 1201071 := bstep (se 1 (by rfl) ⟨900803, by rfl⟩ : syracuseStep 1201071 = 1801607) B1801607
theorem B4330415 : Blo 1200417 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2888635 : Blo 1200417 2888635 := bstep (se 1 (by rfl) ⟨2166476, by rfl⟩ : syracuseStep 2888635 = 4332953) B4332953
theorem B1201095 : Blo 1200417 1201095 := bstep (se 1 (by rfl) ⟨900821, by rfl⟩ : syracuseStep 1201095 = 1801643) B1801643
theorem B1201115 : Blo 1200417 1201115 := bstep (se 1 (by rfl) ⟨900836, by rfl⟩ : syracuseStep 1201115 = 1801673) B1801673
theorem B6083585 : Blo 1200417 6083585 := bstep (se 2 (by rfl) ⟨2281344, by rfl⟩ : syracuseStep 6083585 = 4562689) B4562689
theorem B1201191 : Blo 1200417 1201191 := bstep (se 1 (by rfl) ⟨900893, by rfl⟩ : syracuseStep 1201191 = 1801787) B1801787
theorem B1201231 : Blo 1200417 1201231 := bstep (se 1 (by rfl) ⟨900923, by rfl⟩ : syracuseStep 1201231 = 1801847) B1801847
theorem B2282575 : Blo 1200417 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B1201247 : Blo 1200417 1201247 := bstep (se 1 (by rfl) ⟨900935, by rfl⟩ : syracuseStep 1201247 = 1801871) B1801871
theorem B1201275 : Blo 1200417 1201275 := bstep (se 1 (by rfl) ⟨900956, by rfl⟩ : syracuseStep 1201275 = 1801913) B1801913
theorem B1217711 : Blo 1200417 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B1201327 : Blo 1200417 1201327 := bstep (se 1 (by rfl) ⟨900995, by rfl⟩ : syracuseStep 1201327 = 1801991) B1801991
theorem B1201351 : Blo 1200417 1201351 := bstep (se 1 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 1201351 = 1802027) B1802027
theorem B1201371 : Blo 1200417 1201371 := bstep (se 1 (by rfl) ⟨901028, by rfl⟩ : syracuseStep 1201371 = 1802057) B1802057
theorem B2028793 : Blo 1200417 2028793 := bstep (se 2 (by rfl) ⟨760797, by rfl⟩ : syracuseStep 2028793 = 1521595) B1521595
theorem B1201447 : Blo 1200417 1201447 := bstep (se 1 (by rfl) ⟨901085, by rfl⟩ : syracuseStep 1201447 = 1802171) B1802171
theorem B1201487 : Blo 1200417 1201487 := bstep (se 1 (by rfl) ⟨901115, by rfl⟩ : syracuseStep 1201487 = 1802231) B1802231
theorem B1201503 : Blo 1200417 1201503 := bstep (se 1 (by rfl) ⟨901127, by rfl⟩ : syracuseStep 1201503 = 1802255) B1802255
theorem B1201531 : Blo 1200417 1201531 := bstep (se 1 (by rfl) ⟨901148, by rfl⟩ : syracuseStep 1201531 = 1802297) B1802297
theorem B3249533 : Blo 1200417 3249533 := bstep (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) B1218575
theorem B1201583 : Blo 1200417 1201583 := bstep (se 1 (by rfl) ⟨901187, by rfl⟩ : syracuseStep 1201583 = 1802375) B1802375
theorem B1201607 : Blo 1200417 1201607 := bstep (se 1 (by rfl) ⟨901205, by rfl⟩ : syracuseStep 1201607 = 1802411) B1802411
theorem B1218011 : Blo 1200417 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B1201627 : Blo 1200417 1201627 := bstep (se 1 (by rfl) ⟨901220, by rfl⟩ : syracuseStep 1201627 = 1802441) B1802441
theorem B2029063 : Blo 1200417 2029063 := bstep (se 1 (by rfl) ⟨1521797, by rfl⟩ : syracuseStep 2029063 = 3043595) B3043595
theorem B1201703 : Blo 1200417 1201703 := bstep (se 1 (by rfl) ⟨901277, by rfl⟩ : syracuseStep 1201703 = 1802555) B1802555
theorem B1201743 : Blo 1200417 1201743 := bstep (se 1 (by rfl) ⟨901307, by rfl⟩ : syracuseStep 1201743 = 1802615) B1802615
theorem B1201759 : Blo 1200417 1201759 := bstep (se 1 (by rfl) ⟨901319, by rfl⟩ : syracuseStep 1201759 = 1802639) B1802639
theorem B1201787 : Blo 1200417 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B3421835 : Blo 1200417 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B1201839 : Blo 1200417 1201839 := bstep (se 1 (by rfl) ⟨901379, by rfl⟩ : syracuseStep 1201839 = 1802759) B1802759
theorem B1201863 : Blo 1200417 1201863 := bstep (se 1 (by rfl) ⟨901397, by rfl⟩ : syracuseStep 1201863 = 1802795) B1802795
theorem B1201883 : Blo 1200417 1201883 := bstep (se 1 (by rfl) ⟨901412, by rfl⟩ : syracuseStep 1201883 = 1802825) B1802825
theorem B1201959 : Blo 1200417 1201959 := bstep (se 1 (by rfl) ⟨901469, by rfl⟩ : syracuseStep 1201959 = 1802939) B1802939
theorem B6084395 : Blo 1200417 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B1201999 : Blo 1200417 1201999 := bstep (se 1 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 1201999 = 1802999) B1802999
theorem B2701151 : Blo 1200417 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B1202015 : Blo 1200417 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B1202043 : Blo 1200417 1202043 := bstep (se 1 (by rfl) ⟨901532, by rfl⟩ : syracuseStep 1202043 = 1803065) B1803065
theorem B1202095 : Blo 1200417 1202095 := bstep (se 1 (by rfl) ⟨901571, by rfl⟩ : syracuseStep 1202095 = 1803143) B1803143
theorem B7698361 : Blo 1200417 7698361 := bstep (se 2 (by rfl) ⟨2886885, by rfl⟩ : syracuseStep 7698361 = 5773771) B5773771
theorem B5552059 : Blo 1200417 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B1202119 : Blo 1200417 1202119 := bstep (se 1 (by rfl) ⟨901589, by rfl⟩ : syracuseStep 1202119 = 1803179) B1803179
theorem B1202139 : Blo 1200417 1202139 := bstep (se 1 (by rfl) ⟨901604, by rfl⟩ : syracuseStep 1202139 = 1803209) B1803209
theorem B2701331 : Blo 1200417 2701331 := bstep (se 1 (by rfl) ⟨2025998, by rfl⟩ : syracuseStep 2701331 = 4051997) B4051997
theorem B1202215 : Blo 1200417 1202215 := bstep (se 1 (by rfl) ⟨901661, by rfl⟩ : syracuseStep 1202215 = 1803323) B1803323
theorem B1202255 : Blo 1200417 1202255 := bstep (se 1 (by rfl) ⟨901691, by rfl⟩ : syracuseStep 1202255 = 1803383) B1803383
theorem B1202271 : Blo 1200417 1202271 := bstep (se 1 (by rfl) ⟨901703, by rfl⟩ : syracuseStep 1202271 = 1803407) B1803407
theorem B1202299 : Blo 1200417 1202299 := bstep (se 1 (by rfl) ⟨901724, by rfl⟩ : syracuseStep 1202299 = 1803449) B1803449
theorem B4561049 : Blo 1200417 4561049 := bstep (se 2 (by rfl) ⟨1710393, by rfl⟩ : syracuseStep 4561049 = 3420787) B3420787
theorem B1202351 : Blo 1200417 1202351 := bstep (se 1 (by rfl) ⟨901763, by rfl⟩ : syracuseStep 1202351 = 1803527) B1803527
theorem B1202375 : Blo 1200417 1202375 := bstep (se 1 (by rfl) ⟨901781, by rfl⟩ : syracuseStep 1202375 = 1803563) B1803563
theorem B1202395 : Blo 1200417 1202395 := bstep (se 1 (by rfl) ⟨901796, by rfl⟩ : syracuseStep 1202395 = 1803593) B1803593
theorem B4053239 : Blo 1200417 4053239 := bstep (se 1 (by rfl) ⟨3039929, by rfl⟩ : syracuseStep 4053239 = 6079859) B6079859
theorem B2701673 : Blo 1200417 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B1800713 : Blo 1200417 1800713 := bstep (se 2 (by rfl) ⟨675267, by rfl⟩ : syracuseStep 1800713 = 1350535) B1350535
theorem B1800743 : Blo 1200417 1800743 := bstep (se 1 (by rfl) ⟨1350557, by rfl⟩ : syracuseStep 1800743 = 2701115) B2701115
theorem B4053563 : Blo 1200417 4053563 := bstep (se 1 (by rfl) ⟨3040172, by rfl⟩ : syracuseStep 4053563 = 6080345) B6080345
theorem B4561505 : Blo 1200417 4561505 := bstep (se 2 (by rfl) ⟨1710564, by rfl⟩ : syracuseStep 4561505 = 3421129) B3421129
theorem B1800827 : Blo 1200417 1800827 := bstep (se 1 (by rfl) ⟨1350620, by rfl⟩ : syracuseStep 1800827 = 2701241) B2701241
theorem B1800953 : Blo 1200417 1800953 := bstep (se 2 (by rfl) ⟨675357, by rfl⟩ : syracuseStep 1800953 = 1350715) B1350715
theorem B6839113 : Blo 1200417 6839113 := bstep (se 2 (by rfl) ⟨2564667, by rfl⟩ : syracuseStep 6839113 = 5129335) B5129335
theorem B4053833 : Blo 1200417 4053833 := bstep (se 2 (by rfl) ⟨1520187, by rfl⟩ : syracuseStep 4053833 = 3040375) B3040375
theorem B1801055 : Blo 1200417 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B1801067 : Blo 1200417 1801067 := bstep (se 1 (by rfl) ⟨1350800, by rfl⟩ : syracuseStep 1801067 = 2701601) B2701601
theorem B6495083 : Blo 1200417 6495083 := bstep (se 1 (by rfl) ⟨4871312, by rfl⟩ : syracuseStep 6495083 = 9742625) B9742625
theorem B3849079 : Blo 1200417 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B2702267 : Blo 1200417 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B7306213 : Blo 1200417 7306213 := bstep (se 4 (by rfl) ⟨684957, by rfl⟩ : syracuseStep 7306213 = 1369915) B1369915
theorem B2702393 : Blo 1200417 2702393 := bstep (se 2 (by rfl) ⟨1013397, by rfl⟩ : syracuseStep 2702393 = 2026795) B2026795
theorem B1801295 : Blo 1200417 1801295 := bstep (se 1 (by rfl) ⟨1350971, by rfl⟩ : syracuseStep 1801295 = 2701943) B2701943
theorem B19758275 : Blo 1200417 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B5135555 : Blo 1200417 5135555 := bstep (se 1 (by rfl) ⟨3851666, by rfl⟩ : syracuseStep 5135555 = 7703333) B7703333
theorem B1801415 : Blo 1200417 1801415 := bstep (se 1 (by rfl) ⟨1351061, by rfl⟩ : syracuseStep 1801415 = 2702123) B2702123
theorem B9125135 : Blo 1200417 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B7691543 : Blo 1200417 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B8658265 : Blo 1200417 8658265 := bstep (se 2 (by rfl) ⟨3246849, by rfl⟩ : syracuseStep 8658265 = 6493699) B6493699
theorem B1801577 : Blo 1200417 1801577 := bstep (se 2 (by rfl) ⟨675591, by rfl⟩ : syracuseStep 1801577 = 1351183) B1351183
theorem B3038593 : Blo 1200417 3038593 := bstep (se 2 (by rfl) ⟨1139472, by rfl⟩ : syracuseStep 3038593 = 2278945) B2278945
theorem B2702735 : Blo 1200417 2702735 := bstep (se 1 (by rfl) ⟨2027051, by rfl⟩ : syracuseStep 2702735 = 4054103) B4054103
theorem B1801655 : Blo 1200417 1801655 := bstep (se 1 (by rfl) ⟨1351241, by rfl⟩ : syracuseStep 1801655 = 2702483) B2702483
theorem B6077915 : Blo 1200417 6077915 := bstep (se 1 (by rfl) ⟨4558436, by rfl⟩ : syracuseStep 6077915 = 9116873) B9116873
theorem B1801691 : Blo 1200417 1801691 := bstep (se 1 (by rfl) ⟨1351268, by rfl⟩ : syracuseStep 1801691 = 2702537) B2702537
theorem B3898867 : Blo 1200417 3898867 := bstep (se 1 (by rfl) ⟨2924150, by rfl⟩ : syracuseStep 3898867 = 5848301) B5848301
theorem B23092775 : Blo 1200417 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B1351291 : Blo 1200417 1351291 := bstep (se 1 (by rfl) ⟨1013468, by rfl⟩ : syracuseStep 1351291 = 2026937) B2026937
theorem B2703059 : Blo 1200417 2703059 := bstep (se 1 (by rfl) ⟨2027294, by rfl⟩ : syracuseStep 2703059 = 4054589) B4054589
theorem B7806779 : Blo 1200417 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B7700359 : Blo 1200417 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B1802159 : Blo 1200417 1802159 := bstep (se 1 (by rfl) ⟨1351619, by rfl⟩ : syracuseStep 1802159 = 2703239) B2703239
theorem B4054967 : Blo 1200417 4054967 := bstep (se 1 (by rfl) ⟨3041225, by rfl⟩ : syracuseStep 4054967 = 6082451) B6082451
theorem B6078401 : Blo 1200417 6078401 := bstep (se 2 (by rfl) ⟨2279400, by rfl⟩ : syracuseStep 6078401 = 4558801) B4558801
theorem B3039241 : Blo 1200417 3039241 := bstep (se 2 (by rfl) ⟨1139715, by rfl⟩ : syracuseStep 3039241 = 2279431) B2279431
theorem B1802345 : Blo 1200417 1802345 := bstep (se 2 (by rfl) ⟨675879, by rfl⟩ : syracuseStep 1802345 = 1351759) B1351759
theorem B1351975 : Blo 1200417 1351975 := bstep (se 1 (by rfl) ⟨1013981, by rfl⟩ : syracuseStep 1351975 = 2027963) B2027963
theorem B2703689 : Blo 1200417 2703689 := bstep (se 2 (by rfl) ⟨1013883, by rfl⟩ : syracuseStep 2703689 = 2027767) B2027767
theorem B30810455 : Blo 1200417 30810455 := bstep (se 1 (by rfl) ⟨23107841, by rfl⟩ : syracuseStep 30810455 = 46215683) B46215683
theorem B2703707 : Blo 1200417 2703707 := bstep (se 1 (by rfl) ⟨2027780, by rfl⟩ : syracuseStep 2703707 = 4055561) B4055561
theorem B1352047 : Blo 1200417 1352047 := bstep (se 1 (by rfl) ⟨1014035, by rfl⟩ : syracuseStep 1352047 = 2028071) B2028071
theorem B1802663 : Blo 1200417 1802663 := bstep (se 1 (by rfl) ⟨1351997, by rfl⟩ : syracuseStep 1802663 = 2703995) B2703995
theorem B1802747 : Blo 1200417 1802747 := bstep (se 1 (by rfl) ⟨1352060, by rfl⟩ : syracuseStep 1802747 = 2704121) B2704121
theorem B1352263 : Blo 1200417 1352263 := bstep (se 1 (by rfl) ⟨1014197, by rfl⟩ : syracuseStep 1352263 = 2028395) B2028395
theorem B1925705 : Blo 1200417 1925705 := bstep (se 2 (by rfl) ⟨722139, by rfl⟩ : syracuseStep 1925705 = 1444279) B1444279
theorem B1802873 : Blo 1200417 1802873 := bstep (se 2 (by rfl) ⟨676077, by rfl⟩ : syracuseStep 1802873 = 1352155) B1352155
theorem B4055723 : Blo 1200417 4055723 := bstep (se 1 (by rfl) ⟨3041792, by rfl⟩ : syracuseStep 4055723 = 6083585) B6083585
theorem B1802927 : Blo 1200417 1802927 := bstep (se 1 (by rfl) ⟨1352195, by rfl⟩ : syracuseStep 1802927 = 2704391) B2704391
theorem B1802975 : Blo 1200417 1802975 := bstep (se 1 (by rfl) ⟨1352231, by rfl⟩ : syracuseStep 1802975 = 2704463) B2704463
theorem B11698937 : Blo 1200417 11698937 := bstep (se 2 (by rfl) ⟨4387101, by rfl⟩ : syracuseStep 11698937 = 8774203) B8774203
theorem B2704283 : Blo 1200417 2704283 := bstep (se 1 (by rfl) ⟨2028212, by rfl⟩ : syracuseStep 2704283 = 4056425) B4056425
theorem B15401947 : Blo 1200417 15401947 := bstep (se 1 (by rfl) ⟨11551460, by rfl⟩ : syracuseStep 15401947 = 23102921) B23102921
theorem B1803239 : Blo 1200417 1803239 := bstep (se 1 (by rfl) ⟨1352429, by rfl⟩ : syracuseStep 1803239 = 2704859) B2704859
theorem B9118817 : Blo 1200417 9118817 := bstep (se 2 (by rfl) ⟨3419556, by rfl⟩ : syracuseStep 9118817 = 6839113) B6839113
theorem B2704481 : Blo 1200417 2704481 := bstep (se 2 (by rfl) ⟨1014180, by rfl⟩ : syracuseStep 2704481 = 2028361) B2028361
theorem B5776541 : Blo 1200417 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B4056263 : Blo 1200417 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1803497 : Blo 1200417 1803497 := bstep (se 2 (by rfl) ⟨676311, by rfl⟩ : syracuseStep 1803497 = 1352623) B1352623
theorem B3851513 : Blo 1200417 3851513 := bstep (se 2 (by rfl) ⟨1444317, by rfl⟩ : syracuseStep 3851513 = 2888635) B2888635
theorem B1803551 : Blo 1200417 1803551 := bstep (se 1 (by rfl) ⟨1352663, by rfl⟩ : syracuseStep 1803551 = 2705327) B2705327
theorem B2704679 : Blo 1200417 2704679 := bstep (se 1 (by rfl) ⟨2028509, by rfl⟩ : syracuseStep 2704679 = 4057019) B4057019
theorem B9741617 : Blo 1200417 9741617 := bstep (se 2 (by rfl) ⟨3653106, by rfl⟩ : syracuseStep 9741617 = 7306213) B7306213
theorem B2164105 : Blo 1200417 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B3040649 : Blo 1200417 3040649 := bstep (se 2 (by rfl) ⟨1140243, by rfl⟩ : syracuseStep 3040649 = 2280487) B2280487
theorem B3040699 : Blo 1200417 3040699 := bstep (se 1 (by rfl) ⟨2280524, by rfl⟩ : syracuseStep 3040699 = 4561049) B4561049
theorem B19760759 : Blo 1200417 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B2705057 : Blo 1200417 2705057 := bstep (se 2 (by rfl) ⟨1014396, by rfl⟩ : syracuseStep 2705057 = 2028793) B2028793
theorem B3041003 : Blo 1200417 3041003 := bstep (se 1 (by rfl) ⟨2280752, by rfl⟩ : syracuseStep 3041003 = 4561505) B4561505
theorem B2967275 : Blo 1200417 2967275 := bstep (se 1 (by rfl) ⟨2225456, by rfl⟩ : syracuseStep 2967275 = 4450913) B4450913
theorem B11544353 : Blo 1200417 11544353 := bstep (se 2 (by rfl) ⟨4329132, by rfl⟩ : syracuseStep 11544353 = 8658265) B8658265
theorem B3082025 : Blo 1200417 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B12322637 : Blo 1200417 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B3245953 : Blo 1200417 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B13191119 : Blo 1200417 13191119 := bstep (se 1 (by rfl) ⟨9893339, by rfl⟩ : syracuseStep 13191119 = 19786679) B19786679
theorem B2705417 : Blo 1200417 2705417 := bstep (se 2 (by rfl) ⟨1014531, by rfl⟩ : syracuseStep 2705417 = 2029063) B2029063
theorem B3246427 : Blo 1200417 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B15395183 : Blo 1200417 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B3901879 : Blo 1200417 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B4868603 : Blo 1200417 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B10267145 : Blo 1200417 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B5204519 : Blo 1200417 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B24644195 : Blo 1200417 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B21908069 : Blo 1200417 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B4057775 : Blo 1200417 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B3041975 : Blo 1200417 3041975 := bstep (se 1 (by rfl) ⟨2281481, by rfl⟩ : syracuseStep 3041975 = 4562963) B4562963
theorem B2026471 : Blo 1200417 2026471 := bstep (se 1 (by rfl) ⟨1519853, by rfl⟩ : syracuseStep 2026471 = 3039707) B3039707
theorem B4058099 : Blo 1200417 4058099 := bstep (se 1 (by rfl) ⟨3043574, by rfl⟩ : syracuseStep 4058099 = 6087149) B6087149
theorem B3247229 : Blo 1200417 3247229 := bstep (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) B1217711
theorem B6081803 : Blo 1200417 6081803 := bstep (se 1 (by rfl) ⟨4561352, by rfl⟩ : syracuseStep 6081803 = 9122705) B9122705
theorem B2886943 : Blo 1200417 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B8654141 : Blo 1200417 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B9882941 : Blo 1200417 9882941 := bstep (se 3 (by rfl) ⟨1853051, by rfl⟩ : syracuseStep 9882941 = 3706103) B3706103
theorem B3419489 : Blo 1200417 3419489 := bstep (se 2 (by rfl) ⟨1282308, by rfl⟩ : syracuseStep 3419489 = 2564617) B2564617
theorem B2166355 : Blo 1200417 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B6844013 : Blo 1200417 6844013 := bstep (se 3 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 6844013 = 2566505) B2566505
theorem B1519327 : Blo 1200417 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B2281223 : Blo 1200417 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B3043079 : Blo 1200417 3043079 := bstep (se 1 (by rfl) ⟨2282309, by rfl⟩ : syracuseStep 3043079 = 4564619) B4564619
theorem B3419945 : Blo 1200417 3419945 := bstep (se 2 (by rfl) ⟨1282479, by rfl⟩ : syracuseStep 3419945 = 2564959) B2564959
theorem B2567983 : Blo 1200417 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B3043129 : Blo 1200417 3043129 := bstep (se 2 (by rfl) ⟨1141173, by rfl⟩ : syracuseStep 3043129 = 2282347) B2282347
theorem B5132105 : Blo 1200417 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B3248029 : Blo 1200417 3248029 := bstep (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) B1218011
theorem B6492161 : Blo 1200417 6492161 := bstep (se 2 (by rfl) ⟨2434560, by rfl⟩ : syracuseStep 6492161 = 4869121) B4869121
theorem B12988475 : Blo 1200417 12988475 := bstep (se 1 (by rfl) ⟨9741356, by rfl⟩ : syracuseStep 12988475 = 19482713) B19482713
theorem B3043433 : Blo 1200417 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B1200475 : Blo 1200417 1200475 := bstep (se 1 (by rfl) ⟨900356, by rfl⟩ : syracuseStep 1200475 = 1800713) B1800713
theorem B1200495 : Blo 1200417 1200495 := bstep (se 1 (by rfl) ⟨900371, by rfl⟩ : syracuseStep 1200495 = 1800743) B1800743
theorem B1200551 : Blo 1200417 1200551 := bstep (se 1 (by rfl) ⟨900413, by rfl⟩ : syracuseStep 1200551 = 1800827) B1800827
theorem B4329953 : Blo 1200417 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B1200635 : Blo 1200417 1200635 := bstep (se 1 (by rfl) ⟨900476, by rfl⟩ : syracuseStep 1200635 = 1800953) B1800953
theorem B4051457 : Blo 1200417 4051457 := bstep (se 2 (by rfl) ⟨1519296, by rfl⟩ : syracuseStep 4051457 = 3038593) B3038593
theorem B1200703 : Blo 1200417 1200703 := bstep (se 1 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 1200703 = 1801055) B1801055
theorem B1200711 : Blo 1200417 1200711 := bstep (se 1 (by rfl) ⟨900533, by rfl⟩ : syracuseStep 1200711 = 1801067) B1801067
theorem B4330055 : Blo 1200417 4330055 := bstep (se 1 (by rfl) ⟨3247541, by rfl⟩ : syracuseStep 4330055 = 6495083) B6495083
theorem B5198489 : Blo 1200417 5198489 := bstep (se 2 (by rfl) ⟨1949433, by rfl⟩ : syracuseStep 5198489 = 3898867) B3898867
theorem B1200863 : Blo 1200417 1200863 := bstep (se 1 (by rfl) ⟨900647, by rfl⟩ : syracuseStep 1200863 = 1801295) B1801295
theorem B1200943 : Blo 1200417 1200943 := bstep (se 1 (by rfl) ⟨900707, by rfl⟩ : syracuseStep 1200943 = 1801415) B1801415
theorem B6083423 : Blo 1200417 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B1201051 : Blo 1200417 1201051 := bstep (se 1 (by rfl) ⟨900788, by rfl⟩ : syracuseStep 1201051 = 1801577) B1801577
theorem B10269605 : Blo 1200417 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B1201103 : Blo 1200417 1201103 := bstep (se 1 (by rfl) ⟨900827, by rfl⟩ : syracuseStep 1201103 = 1801655) B1801655
theorem B4051943 : Blo 1200417 4051943 := bstep (se 1 (by rfl) ⟨3038957, by rfl⟩ : syracuseStep 4051943 = 6077915) B6077915
theorem B1201127 : Blo 1200417 1201127 := bstep (se 1 (by rfl) ⟨900845, by rfl⟩ : syracuseStep 1201127 = 1801691) B1801691
theorem B4109555 : Blo 1200417 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B7402745 : Blo 1200417 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B1201439 : Blo 1200417 1201439 := bstep (se 1 (by rfl) ⟨901079, by rfl⟩ : syracuseStep 1201439 = 1802159) B1802159
theorem B4052267 : Blo 1200417 4052267 := bstep (se 1 (by rfl) ⟨3039200, by rfl⟩ : syracuseStep 4052267 = 6078401) B6078401
theorem B1201499 : Blo 1200417 1201499 := bstep (se 1 (by rfl) ⟨901124, by rfl⟩ : syracuseStep 1201499 = 1802249) B1802249
theorem B1201519 : Blo 1200417 1201519 := bstep (se 1 (by rfl) ⟨901139, by rfl⟩ : syracuseStep 1201519 = 1802279) B1802279
theorem B11556229 : Blo 1200417 11556229 := bstep (se 4 (by rfl) ⟨1083396, by rfl⟩ : syracuseStep 11556229 = 2166793) B2166793
theorem B25974179 : Blo 1200417 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B1201575 : Blo 1200417 1201575 := bstep (se 1 (by rfl) ⟨901181, by rfl⟩ : syracuseStep 1201575 = 1802363) B1802363
theorem B1201659 : Blo 1200417 1201659 := bstep (se 1 (by rfl) ⟨901244, by rfl⟩ : syracuseStep 1201659 = 1802489) B1802489
theorem B11695661 : Blo 1200417 11695661 := bstep (se 3 (by rfl) ⟨2192936, by rfl⟩ : syracuseStep 11695661 = 4385873) B4385873
theorem B4052537 : Blo 1200417 4052537 := bstep (se 2 (by rfl) ⟨1519701, by rfl⟩ : syracuseStep 4052537 = 3039403) B3039403
theorem B5133881 : Blo 1200417 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B1201727 : Blo 1200417 1201727 := bstep (se 1 (by rfl) ⟨901295, by rfl⟩ : syracuseStep 1201727 = 1802591) B1802591
theorem B1201735 : Blo 1200417 1201735 := bstep (se 1 (by rfl) ⟨901301, by rfl⟩ : syracuseStep 1201735 = 1802603) B1802603
theorem B1201887 : Blo 1200417 1201887 := bstep (se 1 (by rfl) ⟨901415, by rfl⟩ : syracuseStep 1201887 = 1802831) B1802831
theorem B2701097 : Blo 1200417 2701097 := bstep (se 2 (by rfl) ⟨1012911, by rfl⟩ : syracuseStep 2701097 = 2025823) B2025823
theorem B3168047 : Blo 1200417 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B1201967 : Blo 1200417 1201967 := bstep (se 1 (by rfl) ⟨901475, by rfl⟩ : syracuseStep 1201967 = 1802951) B1802951
theorem B4560745 : Blo 1200417 4560745 := bstep (se 2 (by rfl) ⟨1710279, by rfl⟩ : syracuseStep 4560745 = 3420559) B3420559
theorem B1202075 : Blo 1200417 1202075 := bstep (se 1 (by rfl) ⟨901556, by rfl⟩ : syracuseStep 1202075 = 1803113) B1803113
theorem B1202127 : Blo 1200417 1202127 := bstep (se 1 (by rfl) ⟨901595, by rfl⟩ : syracuseStep 1202127 = 1803191) B1803191
theorem B1202151 : Blo 1200417 1202151 := bstep (se 1 (by rfl) ⟨901613, by rfl⟩ : syracuseStep 1202151 = 1803227) B1803227
theorem B6936857 : Blo 1200417 6936857 := bstep (se 2 (by rfl) ⟨2601321, by rfl⟩ : syracuseStep 6936857 = 5202643) B5202643
theorem B1235311 : Blo 1200417 1235311 := bstep (se 1 (by rfl) ⟨926483, by rfl⟩ : syracuseStep 1235311 = 1852967) B1852967
theorem B1645049 : Blo 1200417 1645049 := bstep (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) B1233787
theorem B12999163 : Blo 1200417 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B1800767 : Blo 1200417 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B1923655 : Blo 1200417 1923655 := bstep (se 1 (by rfl) ⟨1442741, by rfl⟩ : syracuseStep 1923655 = 2885483) B2885483
theorem B1800887 : Blo 1200417 1800887 := bstep (se 1 (by rfl) ⟨1350665, by rfl⟩ : syracuseStep 1800887 = 2701331) B2701331
theorem B6085367 : Blo 1200417 6085367 := bstep (se 1 (by rfl) ⟨4564025, by rfl⟩ : syracuseStep 6085367 = 9128051) B9128051
theorem B4053779 : Blo 1200417 4053779 := bstep (se 1 (by rfl) ⟨3040334, by rfl⟩ : syracuseStep 4053779 = 6080669) B6080669
theorem B2702159 : Blo 1200417 2702159 := bstep (se 1 (by rfl) ⟨2026619, by rfl⟩ : syracuseStep 2702159 = 4053239) B4053239
theorem B1801115 : Blo 1200417 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B1350607 : Blo 1200417 1350607 := bstep (se 1 (by rfl) ⟨1012955, by rfl⟩ : syracuseStep 1350607 = 2025911) B2025911
theorem B2702375 : Blo 1200417 2702375 := bstep (se 1 (by rfl) ⟨2026781, by rfl⟩ : syracuseStep 2702375 = 4053563) B4053563
theorem B23100461 : Blo 1200417 23100461 := bstep (se 3 (by rfl) ⟨4331336, by rfl⟩ : syracuseStep 23100461 = 8662673) B8662673
theorem B2702555 : Blo 1200417 2702555 := bstep (se 1 (by rfl) ⟨2026916, by rfl⟩ : syracuseStep 2702555 = 4053833) B4053833
theorem B17784029 : Blo 1200417 17784029 := bstep (se 3 (by rfl) ⟨3334505, by rfl⟩ : syracuseStep 17784029 = 6669011) B6669011
theorem B6085853 : Blo 1200417 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B1801511 : Blo 1200417 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B1351003 : Blo 1200417 1351003 := bstep (se 1 (by rfl) ⟨1013252, by rfl⟩ : syracuseStep 1351003 = 2026505) B2026505
theorem B1801595 : Blo 1200417 1801595 := bstep (se 1 (by rfl) ⟨1351196, by rfl⟩ : syracuseStep 1801595 = 2702393) B2702393
theorem B2702753 : Blo 1200417 2702753 := bstep (se 2 (by rfl) ⟨1013532, by rfl⟩ : syracuseStep 2702753 = 2027065) B2027065
theorem B1351111 : Blo 1200417 1351111 := bstep (se 1 (by rfl) ⟨1013333, by rfl⟩ : syracuseStep 1351111 = 2026667) B2026667
theorem B13172183 : Blo 1200417 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B3423703 : Blo 1200417 3423703 := bstep (se 1 (by rfl) ⟨2567777, by rfl⟩ : syracuseStep 3423703 = 5135555) B5135555
theorem B1801721 : Blo 1200417 1801721 := bstep (se 2 (by rfl) ⟨675645, by rfl⟩ : syracuseStep 1801721 = 1351291) B1351291
theorem B5127695 : Blo 1200417 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B1801823 : Blo 1200417 1801823 := bstep (se 1 (by rfl) ⟨1351367, by rfl⟩ : syracuseStep 1801823 = 2702735) B2702735
theorem B4054643 : Blo 1200417 4054643 := bstep (se 1 (by rfl) ⟨3040982, by rfl⟩ : syracuseStep 4054643 = 6081965) B6081965
theorem B6840071 : Blo 1200417 6840071 := bstep (se 1 (by rfl) ⟨5130053, by rfl⟩ : syracuseStep 6840071 = 10260107) B10260107
theorem B1351471 : Blo 1200417 1351471 := bstep (se 1 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 1351471 = 2027207) B2027207
theorem B1802039 : Blo 1200417 1802039 := bstep (se 1 (by rfl) ⟨1351529, by rfl⟩ : syracuseStep 1802039 = 2703059) B2703059
theorem B4054913 : Blo 1200417 4054913 := bstep (se 2 (by rfl) ⟨1520592, by rfl⟩ : syracuseStep 4054913 = 3041185) B3041185
theorem B1351579 : Blo 1200417 1351579 := bstep (se 1 (by rfl) ⟨1013684, by rfl⟩ : syracuseStep 1351579 = 2027369) B2027369
theorem B10264481 : Blo 1200417 10264481 := bstep (se 2 (by rfl) ⟨3849180, by rfl⟩ : syracuseStep 10264481 = 7698361) B7698361
theorem B2703311 : Blo 1200417 2703311 := bstep (se 1 (by rfl) ⟨2027483, by rfl⟩ : syracuseStep 2703311 = 4054967) B4054967
theorem B8658983 : Blo 1200417 8658983 := bstep (se 1 (by rfl) ⟨6494237, by rfl⟩ : syracuseStep 8658983 = 12988475) B12988475
theorem B1802459 : Blo 1200417 1802459 := bstep (se 1 (by rfl) ⟨1351844, by rfl⟩ : syracuseStep 1802459 = 2703689) B2703689
theorem B1802471 : Blo 1200417 1802471 := bstep (se 1 (by rfl) ⟨1351853, by rfl⟩ : syracuseStep 1802471 = 2703707) B2703707
theorem B1802633 : Blo 1200417 1802633 := bstep (se 2 (by rfl) ⟨675987, by rfl⟩ : syracuseStep 1802633 = 1351975) B1351975
theorem B3465659 : Blo 1200417 3465659 := bstep (se 1 (by rfl) ⟨2599244, by rfl⟩ : syracuseStep 3465659 = 5198489) B5198489
theorem B2703815 : Blo 1200417 2703815 := bstep (se 1 (by rfl) ⟨2027861, by rfl⟩ : syracuseStep 2703815 = 4055723) B4055723
theorem B1802729 : Blo 1200417 1802729 := bstep (se 2 (by rfl) ⟨676023, by rfl⟩ : syracuseStep 1802729 = 1352047) B1352047
theorem B7799291 : Blo 1200417 7799291 := bstep (se 1 (by rfl) ⟨5849468, by rfl⟩ : syracuseStep 7799291 = 11698937) B11698937
theorem B4055615 : Blo 1200417 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B5202505 : Blo 1200417 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B1802855 : Blo 1200417 1802855 := bstep (se 1 (by rfl) ⟨1352141, by rfl⟩ : syracuseStep 1802855 = 2704283) B2704283
theorem B6079211 : Blo 1200417 6079211 := bstep (se 1 (by rfl) ⟨4559408, by rfl⟩ : syracuseStep 6079211 = 9118817) B9118817
theorem B1802987 : Blo 1200417 1802987 := bstep (se 1 (by rfl) ⟨1352240, by rfl⟩ : syracuseStep 1802987 = 2704481) B2704481
theorem B2564873 : Blo 1200417 2564873 := bstep (se 2 (by rfl) ⟨961827, by rfl⟩ : syracuseStep 2564873 = 1923655) B1923655
theorem B1803017 : Blo 1200417 1803017 := bstep (se 2 (by rfl) ⟨676131, by rfl⟩ : syracuseStep 1803017 = 1352263) B1352263
theorem B3851027 : Blo 1200417 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B2704175 : Blo 1200417 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1803119 : Blo 1200417 1803119 := bstep (se 1 (by rfl) ⟨1352339, by rfl⟩ : syracuseStep 1803119 = 2704679) B2704679
theorem B13173839 : Blo 1200417 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B1803371 : Blo 1200417 1803371 := bstep (se 1 (by rfl) ⟨1352528, by rfl⟩ : syracuseStep 1803371 = 2705057) B2705057
theorem B1803611 : Blo 1200417 1803611 := bstep (se 1 (by rfl) ⟨1352708, by rfl⟩ : syracuseStep 1803611 = 2705417) B2705417
theorem B3245735 : Blo 1200417 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B2705183 : Blo 1200417 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B4056911 : Blo 1200417 4056911 := bstep (se 1 (by rfl) ⟨3042683, by rfl⟩ : syracuseStep 4056911 = 6085367) B6085367
theorem B2885473 : Blo 1200417 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B6588325 : Blo 1200417 6588325 := bstep (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) B1235311
theorem B4564937 : Blo 1200417 4564937 := bstep (se 2 (by rfl) ⟨1711851, by rfl⟩ : syracuseStep 4564937 = 3423703) B3423703
theorem B2705399 : Blo 1200417 2705399 := bstep (se 1 (by rfl) ⟨2029049, by rfl⟩ : syracuseStep 2705399 = 4058099) B4058099
theorem B2164819 : Blo 1200417 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B11856019 : Blo 1200417 11856019 := bstep (se 1 (by rfl) ⟨8892014, by rfl⟩ : syracuseStep 11856019 = 17784029) B17784029
theorem B4057235 : Blo 1200417 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B5769427 : Blo 1200417 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B2279659 : Blo 1200417 2279659 := bstep (se 1 (by rfl) ⟨1709744, by rfl⟩ : syracuseStep 2279659 = 3419489) B3419489
theorem B2025769 : Blo 1200417 2025769 := bstep (se 2 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 2025769 = 1519327) B1519327
theorem B3418463 : Blo 1200417 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B4057505 : Blo 1200417 4057505 := bstep (se 2 (by rfl) ⟨1521564, by rfl⟩ : syracuseStep 4057505 = 3043129) B3043129
theorem B6080993 : Blo 1200417 6080993 := bstep (se 2 (by rfl) ⟨2280372, by rfl⟩ : syracuseStep 6080993 = 4560745) B4560745
theorem B4327937 : Blo 1200417 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2279963 : Blo 1200417 2279963 := bstep (se 1 (by rfl) ⟨1709972, by rfl⟩ : syracuseStep 2279963 = 3419945) B3419945
theorem B6842987 : Blo 1200417 6842987 := bstep (se 1 (by rfl) ⟨5132240, by rfl⟩ : syracuseStep 6842987 = 10264481) B10264481
theorem B17312429 : Blo 1200417 17312429 := bstep (se 3 (by rfl) ⟨3246080, by rfl⟩ : syracuseStep 17312429 = 6492161) B6492161
theorem B20540303 : Blo 1200417 20540303 := bstep (se 1 (by rfl) ⟨15405227, by rfl⟩ : syracuseStep 20540303 = 30810455) B30810455
theorem B2886635 : Blo 1200417 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B4328569 : Blo 1200417 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B105418037 : Blo 1200417 105418037 := bstep (se 5 (by rfl) ⟨4941470, by rfl⟩ : syracuseStep 105418037 = 9882941) B9882941
theorem B4935163 : Blo 1200417 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B2567675 : Blo 1200417 2567675 := bstep (se 1 (by rfl) ⟨1925756, by rfl⟩ : syracuseStep 2567675 = 3851513) B3851513
theorem B2027099 : Blo 1200417 2027099 := bstep (se 1 (by rfl) ⟨1520324, by rfl⟩ : syracuseStep 2027099 = 3040649) B3040649
theorem B2027335 : Blo 1200417 2027335 := bstep (se 1 (by rfl) ⟨1520501, by rfl⟩ : syracuseStep 2027335 = 3041003) B3041003
theorem B7696235 : Blo 1200417 7696235 := bstep (se 1 (by rfl) ⟨5772176, by rfl⟩ : syracuseStep 7696235 = 11544353) B11544353
theorem B8794079 : Blo 1200417 8794079 := bstep (se 1 (by rfl) ⟨6595559, by rfl⟩ : syracuseStep 8794079 = 13191119) B13191119
theorem B4386797 : Blo 1200417 4386797 := bstep (se 3 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 4386797 = 1645049) B1645049
theorem B4624571 : Blo 1200417 4624571 := bstep (se 1 (by rfl) ⟨3468428, by rfl⟩ : syracuseStep 4624571 = 6936857) B6936857
theorem B11546813 : Blo 1200417 11546813 := bstep (se 3 (by rfl) ⟨2165027, by rfl⟩ : syracuseStep 11546813 = 4330055) B4330055
theorem B6844763 : Blo 1200417 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B3469679 : Blo 1200417 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B1200511 : Blo 1200417 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B16429463 : Blo 1200417 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B1200591 : Blo 1200417 1200591 := bstep (se 1 (by rfl) ⟨900443, by rfl⟩ : syracuseStep 1200591 = 1800887) B1800887
theorem B2027983 : Blo 1200417 2027983 := bstep (se 1 (by rfl) ⟨1520987, by rfl⟩ : syracuseStep 2027983 = 3041975) B3041975
theorem B1200743 : Blo 1200417 1200743 := bstep (se 1 (by rfl) ⟨900557, by rfl⟩ : syracuseStep 1200743 = 1801115) B1801115
theorem B6083261 : Blo 1200417 6083261 := bstep (se 3 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 6083261 = 2281223) B2281223
theorem B2888473 : Blo 1200417 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B1201007 : Blo 1200417 1201007 := bstep (se 1 (by rfl) ⟨900755, by rfl⟩ : syracuseStep 1201007 = 1801511) B1801511
theorem B1201063 : Blo 1200417 1201063 := bstep (se 1 (by rfl) ⟨900797, by rfl⟩ : syracuseStep 1201063 = 1801595) B1801595
theorem B1201147 : Blo 1200417 1201147 := bstep (se 1 (by rfl) ⟨900860, by rfl⟩ : syracuseStep 1201147 = 1801721) B1801721
theorem B1201215 : Blo 1200417 1201215 := bstep (se 1 (by rfl) ⟨900911, by rfl⟩ : syracuseStep 1201215 = 1801823) B1801823
theorem B4560047 : Blo 1200417 4560047 := bstep (se 1 (by rfl) ⟨3420035, by rfl⟩ : syracuseStep 4560047 = 6840071) B6840071
theorem B2028719 : Blo 1200417 2028719 := bstep (se 1 (by rfl) ⟨1521539, by rfl⟩ : syracuseStep 2028719 = 3043079) B3043079
theorem B1201359 : Blo 1200417 1201359 := bstep (se 1 (by rfl) ⟨901019, by rfl⟩ : syracuseStep 1201359 = 1802039) B1802039
theorem B4330705 : Blo 1200417 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B3421403 : Blo 1200417 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B4052321 : Blo 1200417 4052321 := bstep (se 2 (by rfl) ⟨1519620, by rfl⟩ : syracuseStep 4052321 = 3039241) B3039241
theorem B1201563 : Blo 1200417 1201563 := bstep (se 1 (by rfl) ⟨901172, by rfl⟩ : syracuseStep 1201563 = 1802345) B1802345
theorem B2028955 : Blo 1200417 2028955 := bstep (se 1 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 2028955 = 3043433) B3043433
theorem B1201775 : Blo 1200417 1201775 := bstep (se 1 (by rfl) ⟨901331, by rfl⟩ : syracuseStep 1201775 = 1802663) B1802663
theorem B1201831 : Blo 1200417 1201831 := bstep (se 1 (by rfl) ⟨901373, by rfl⟩ : syracuseStep 1201831 = 1802747) B1802747
theorem B2700971 : Blo 1200417 2700971 := bstep (se 1 (by rfl) ⟨2025728, by rfl⟩ : syracuseStep 2700971 = 4051457) B4051457
theorem B1201915 : Blo 1200417 1201915 := bstep (se 1 (by rfl) ⟨901436, by rfl⟩ : syracuseStep 1201915 = 1802873) B1802873
theorem B1201951 : Blo 1200417 1201951 := bstep (se 1 (by rfl) ⟨901463, by rfl⟩ : syracuseStep 1201951 = 1802927) B1802927
theorem B1201983 : Blo 1200417 1201983 := bstep (se 1 (by rfl) ⟨901487, by rfl⟩ : syracuseStep 1201983 = 1802975) B1802975
theorem B6846403 : Blo 1200417 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B10958813 : Blo 1200417 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B2701295 : Blo 1200417 2701295 := bstep (se 1 (by rfl) ⟨2025971, by rfl⟩ : syracuseStep 2701295 = 4051943) B4051943
theorem B1202159 : Blo 1200417 1202159 := bstep (se 1 (by rfl) ⟨901619, by rfl⟩ : syracuseStep 1202159 = 1803239) B1803239
theorem B17332217 : Blo 1200417 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B1202331 : Blo 1200417 1202331 := bstep (se 1 (by rfl) ⟨901748, by rfl⟩ : syracuseStep 1202331 = 1803497) B1803497
theorem B1202367 : Blo 1200417 1202367 := bstep (se 1 (by rfl) ⟨901775, by rfl⟩ : syracuseStep 1202367 = 1803551) B1803551
theorem B2701511 : Blo 1200417 2701511 := bstep (se 1 (by rfl) ⟨2026133, by rfl⟩ : syracuseStep 2701511 = 4052267) B4052267
theorem B6494411 : Blo 1200417 6494411 := bstep (se 1 (by rfl) ⟨4870808, by rfl⟩ : syracuseStep 6494411 = 9741617) B9741617
theorem B17316119 : Blo 1200417 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B7797107 : Blo 1200417 7797107 := bstep (se 1 (by rfl) ⟨5847830, by rfl⟩ : syracuseStep 7797107 = 11695661) B11695661
theorem B2701691 : Blo 1200417 2701691 := bstep (se 1 (by rfl) ⟨2026268, by rfl⟩ : syracuseStep 2701691 = 4052537) B4052537
theorem B3422587 : Blo 1200417 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B1800731 : Blo 1200417 1800731 := bstep (se 1 (by rfl) ⟨1350548, by rfl⟩ : syracuseStep 1800731 = 2701097) B2701097
theorem B2054683 : Blo 1200417 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B2112031 : Blo 1200417 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B8215091 : Blo 1200417 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B1800809 : Blo 1200417 1800809 := bstep (se 2 (by rfl) ⟨675303, by rfl⟩ : syracuseStep 1800809 = 1350607) B1350607
theorem B20535929 : Blo 1200417 20535929 := bstep (se 2 (by rfl) ⟨7700973, by rfl⟩ : syracuseStep 20535929 = 15401947) B15401947
theorem B2701961 : Blo 1200417 2701961 := bstep (se 2 (by rfl) ⟨1013235, by rfl⟩ : syracuseStep 2701961 = 2026471) B2026471
theorem B5135213 : Blo 1200417 5135213 := bstep (se 3 (by rfl) ⟨962852, by rfl⟩ : syracuseStep 5135213 = 1925705) B1925705
theorem B10263455 : Blo 1200417 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B3849257 : Blo 1200417 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B14605379 : Blo 1200417 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B1801337 : Blo 1200417 1801337 := bstep (se 2 (by rfl) ⟨675501, by rfl⟩ : syracuseStep 1801337 = 1351003) B1351003
theorem B15408305 : Blo 1200417 15408305 := bstep (se 2 (by rfl) ⟨5778114, by rfl⟩ : syracuseStep 15408305 = 11556229) B11556229
theorem B2702519 : Blo 1200417 2702519 := bstep (se 1 (by rfl) ⟨2026889, by rfl⟩ : syracuseStep 2702519 = 4053779) B4053779
theorem B1801439 : Blo 1200417 1801439 := bstep (se 1 (by rfl) ⟨1351079, by rfl⟩ : syracuseStep 1801439 = 2702159) B2702159
theorem B4054265 : Blo 1200417 4054265 := bstep (se 2 (by rfl) ⟨1520349, by rfl⟩ : syracuseStep 4054265 = 3040699) B3040699
theorem B1801481 : Blo 1200417 1801481 := bstep (se 2 (by rfl) ⟨675555, by rfl⟩ : syracuseStep 1801481 = 1351111) B1351111
theorem B7912733 : Blo 1200417 7912733 := bstep (se 3 (by rfl) ⟨1483637, by rfl⟩ : syracuseStep 7912733 = 2967275) B2967275
theorem B1801583 : Blo 1200417 1801583 := bstep (se 1 (by rfl) ⟨1351187, by rfl⟩ : syracuseStep 1801583 = 2702375) B2702375
theorem B15400307 : Blo 1200417 15400307 := bstep (se 1 (by rfl) ⟨11550230, by rfl⟩ : syracuseStep 15400307 = 23100461) B23100461
theorem B1801703 : Blo 1200417 1801703 := bstep (se 1 (by rfl) ⟨1351277, by rfl⟩ : syracuseStep 1801703 = 2702555) B2702555
theorem B4054535 : Blo 1200417 4054535 := bstep (se 1 (by rfl) ⟨3040901, by rfl⟩ : syracuseStep 4054535 = 6081803) B6081803
theorem B1801835 : Blo 1200417 1801835 := bstep (se 1 (by rfl) ⟨1351376, by rfl⟩ : syracuseStep 1801835 = 2702753) B2702753
theorem B8781455 : Blo 1200417 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1801961 : Blo 1200417 1801961 := bstep (se 2 (by rfl) ⟨675735, by rfl⟩ : syracuseStep 1801961 = 1351471) B1351471
theorem B3423977 : Blo 1200417 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B4562675 : Blo 1200417 4562675 := bstep (se 1 (by rfl) ⟨3422006, by rfl⟩ : syracuseStep 4562675 = 6844013) B6844013
theorem B2703095 : Blo 1200417 2703095 := bstep (se 1 (by rfl) ⟨2027321, by rfl⟩ : syracuseStep 2703095 = 4054643) B4054643
theorem B1802105 : Blo 1200417 1802105 := bstep (se 2 (by rfl) ⟨675789, by rfl⟩ : syracuseStep 1802105 = 1351579) B1351579
theorem B2703275 : Blo 1200417 2703275 := bstep (se 1 (by rfl) ⟨2027456, by rfl⟩ : syracuseStep 2703275 = 4054913) B4054913
theorem B1802207 : Blo 1200417 1802207 := bstep (se 1 (by rfl) ⟨1351655, by rfl⟩ : syracuseStep 1802207 = 2703311) B2703311
theorem B4563175 : Blo 1200417 4563175 := bstep (se 1 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 4563175 = 6844763) B6844763
theorem B10952975 : Blo 1200417 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B7692569 : Blo 1200417 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B2310439 : Blo 1200417 2310439 := bstep (se 1 (by rfl) ⟨1732829, by rfl⟩ : syracuseStep 2310439 = 3465659) B3465659
theorem B1802543 : Blo 1200417 1802543 := bstep (se 1 (by rfl) ⟨1351907, by rfl⟩ : syracuseStep 1802543 = 2703815) B2703815
theorem B3039545 : Blo 1200417 3039545 := bstep (se 2 (by rfl) ⟨1139829, by rfl⟩ : syracuseStep 3039545 = 2279659) B2279659
theorem B2703743 : Blo 1200417 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B4055507 : Blo 1200417 4055507 := bstep (se 1 (by rfl) ⟨3041630, by rfl⟩ : syracuseStep 4055507 = 6083261) B6083261
theorem B4563449 : Blo 1200417 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B1802783 : Blo 1200417 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B2703977 : Blo 1200417 2703977 := bstep (se 2 (by rfl) ⟨1013991, by rfl⟩ : syracuseStep 2703977 = 2027983) B2027983
theorem B8782559 : Blo 1200417 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B3040031 : Blo 1200417 3040031 := bstep (se 1 (by rfl) ⟨2280023, by rfl⟩ : syracuseStep 3040031 = 4560047) B4560047
theorem B1352479 : Blo 1200417 1352479 := bstep (se 1 (by rfl) ⟨1014359, by rfl⟩ : syracuseStep 1352479 = 2028719) B2028719
theorem B20792285 : Blo 1200417 20792285 := bstep (se 3 (by rfl) ⟨3898553, by rfl⟩ : syracuseStep 20792285 = 7797107) B7797107
theorem B3851297 : Blo 1200417 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B2163823 : Blo 1200417 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B1803455 : Blo 1200417 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2704607 : Blo 1200417 2704607 := bstep (se 1 (by rfl) ⟨2028455, by rfl⟩ : syracuseStep 2704607 = 4056911) B4056911
theorem B1803599 : Blo 1200417 1803599 := bstep (se 1 (by rfl) ⟨1352699, by rfl⟩ : syracuseStep 1803599 = 2705399) B2705399
theorem B2704823 : Blo 1200417 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B2705003 : Blo 1200417 2705003 := bstep (se 1 (by rfl) ⟨2028752, by rfl⟩ : syracuseStep 2705003 = 4057505) B4057505
theorem B2885291 : Blo 1200417 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B13690619 : Blo 1200417 13690619 := bstep (se 1 (by rfl) ⟨10267964, by rfl⟩ : syracuseStep 13690619 = 20535929) B20535929
theorem B2705273 : Blo 1200417 2705273 := bstep (se 2 (by rfl) ⟨1014477, by rfl⟩ : syracuseStep 2705273 = 2028955) B2028955
theorem B6842303 : Blo 1200417 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B6580217 : Blo 1200417 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B2566171 : Blo 1200417 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B10266871 : Blo 1200417 10266871 := bstep (se 1 (by rfl) ⟨7700153, by rfl⟩ : syracuseStep 10266871 = 15400307) B15400307
theorem B3041783 : Blo 1200417 3041783 := bstep (se 1 (by rfl) ⟨2281337, by rfl⟩ : syracuseStep 3041783 = 4562675) B4562675
theorem B8784433 : Blo 1200417 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B5130823 : Blo 1200417 5130823 := bstep (se 1 (by rfl) ⟨3848117, by rfl⟩ : syracuseStep 5130823 = 7696235) B7696235
theorem B9128537 : Blo 1200417 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B2886425 : Blo 1200417 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B2313119 : Blo 1200417 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B12332189 : Blo 1200417 12332189 := bstep (se 3 (by rfl) ⟨2312285, by rfl⟩ : syracuseStep 12332189 = 4624571) B4624571
theorem B2567351 : Blo 1200417 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B2739577 : Blo 1200417 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B2280935 : Blo 1200417 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B3043291 : Blo 1200417 3043291 := bstep (se 1 (by rfl) ⟨2282468, by rfl⟩ : syracuseStep 3043291 = 4564937) B4564937
theorem B11554811 : Blo 1200417 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B4329607 : Blo 1200417 4329607 := bstep (se 1 (by rfl) ⟨3247205, by rfl⟩ : syracuseStep 4329607 = 6494411) B6494411
theorem B5771425 : Blo 1200417 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B1200487 : Blo 1200417 1200487 := bstep (se 1 (by rfl) ⟨900365, by rfl⟩ : syracuseStep 1200487 = 1800731) B1800731
theorem B1519975 : Blo 1200417 1519975 := bstep (se 1 (by rfl) ⟨1139981, by rfl⟩ : syracuseStep 1519975 = 2279963) B2279963
theorem B5476727 : Blo 1200417 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B1200539 : Blo 1200417 1200539 := bstep (se 1 (by rfl) ⟨900404, by rfl⟩ : syracuseStep 1200539 = 1800809) B1800809
theorem B15389189 : Blo 1200417 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B13693535 : Blo 1200417 13693535 := bstep (se 1 (by rfl) ⟨10270151, by rfl⟩ : syracuseStep 13693535 = 20540303) B20540303
theorem B9736919 : Blo 1200417 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B1200891 : Blo 1200417 1200891 := bstep (se 1 (by rfl) ⟨900668, by rfl⟩ : syracuseStep 1200891 = 1801337) B1801337
theorem B1200959 : Blo 1200417 1200959 := bstep (se 1 (by rfl) ⟨900719, by rfl⟩ : syracuseStep 1200959 = 1801439) B1801439
theorem B1200987 : Blo 1200417 1200987 := bstep (se 1 (by rfl) ⟨900740, by rfl⟩ : syracuseStep 1200987 = 1801481) B1801481
theorem B1201055 : Blo 1200417 1201055 := bstep (se 1 (by rfl) ⟨900791, by rfl⟩ : syracuseStep 1201055 = 1801583) B1801583
theorem B1201135 : Blo 1200417 1201135 := bstep (se 1 (by rfl) ⟨900851, by rfl⟩ : syracuseStep 1201135 = 1801703) B1801703
theorem B1201223 : Blo 1200417 1201223 := bstep (se 1 (by rfl) ⟨900917, by rfl⟩ : syracuseStep 1201223 = 1801835) B1801835
theorem B5854303 : Blo 1200417 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B1201307 : Blo 1200417 1201307 := bstep (se 1 (by rfl) ⟨900980, by rfl⟩ : syracuseStep 1201307 = 1801961) B1801961
theorem B2282651 : Blo 1200417 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B1201403 : Blo 1200417 1201403 := bstep (se 1 (by rfl) ⟨901052, by rfl⟩ : syracuseStep 1201403 = 1802105) B1802105
theorem B7697693 : Blo 1200417 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B5862719 : Blo 1200417 5862719 := bstep (se 1 (by rfl) ⟨4397039, by rfl⟩ : syracuseStep 5862719 = 8794079) B8794079
theorem B1201471 : Blo 1200417 1201471 := bstep (se 1 (by rfl) ⟨901103, by rfl⟩ : syracuseStep 1201471 = 1802207) B1802207
theorem B5772655 : Blo 1200417 5772655 := bstep (se 1 (by rfl) ⟨4329491, by rfl⟩ : syracuseStep 5772655 = 8658983) B8658983
theorem B7697875 : Blo 1200417 7697875 := bstep (se 1 (by rfl) ⟨5773406, by rfl⟩ : syracuseStep 7697875 = 11546813) B11546813
theorem B1201639 : Blo 1200417 1201639 := bstep (se 1 (by rfl) ⟨901229, by rfl⟩ : syracuseStep 1201639 = 1802459) B1802459
theorem B1201647 : Blo 1200417 1201647 := bstep (se 1 (by rfl) ⟨901235, by rfl⟩ : syracuseStep 1201647 = 1802471) B1802471
theorem B15808025 : Blo 1200417 15808025 := bstep (se 2 (by rfl) ⟨5928009, by rfl⟩ : syracuseStep 15808025 = 11856019) B11856019
theorem B1201755 : Blo 1200417 1201755 := bstep (se 1 (by rfl) ⟨901316, by rfl⟩ : syracuseStep 1201755 = 1802633) B1802633
theorem B1201819 : Blo 1200417 1201819 := bstep (se 1 (by rfl) ⟨901364, by rfl⟩ : syracuseStep 1201819 = 1802729) B1802729
theorem B5199527 : Blo 1200417 5199527 := bstep (se 1 (by rfl) ⟨3899645, by rfl⟩ : syracuseStep 5199527 = 7799291) B7799291
theorem B2701025 : Blo 1200417 2701025 := bstep (se 2 (by rfl) ⟨1012884, by rfl⟩ : syracuseStep 2701025 = 2025769) B2025769
theorem B1201903 : Blo 1200417 1201903 := bstep (se 1 (by rfl) ⟨901427, by rfl⟩ : syracuseStep 1201903 = 1802855) B1802855
theorem B4052807 : Blo 1200417 4052807 := bstep (se 1 (by rfl) ⟨3039605, by rfl⟩ : syracuseStep 4052807 = 6079211) B6079211
theorem B1201991 : Blo 1200417 1201991 := bstep (se 1 (by rfl) ⟨901493, by rfl⟩ : syracuseStep 1201991 = 1802987) B1802987
theorem B1709915 : Blo 1200417 1709915 := bstep (se 1 (by rfl) ⟨1282436, by rfl⟩ : syracuseStep 1709915 = 2564873) B2564873
theorem B1202011 : Blo 1200417 1202011 := bstep (se 1 (by rfl) ⟨901508, by rfl⟩ : syracuseStep 1202011 = 1803017) B1803017
theorem B1202079 : Blo 1200417 1202079 := bstep (se 1 (by rfl) ⟨901559, by rfl⟩ : syracuseStep 1202079 = 1803119) B1803119
theorem B2816041 : Blo 1200417 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B46176317 : Blo 1200417 46176317 := bstep (se 3 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 46176317 = 17316119) B17316119
theorem B1202247 : Blo 1200417 1202247 := bstep (se 1 (by rfl) ⟨901685, by rfl⟩ : syracuseStep 1202247 = 1803371) B1803371
theorem B21100621 : Blo 1200417 21100621 := bstep (se 3 (by rfl) ⟨3956366, by rfl⟩ : syracuseStep 21100621 = 7912733) B7912733
theorem B6936673 : Blo 1200417 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B1202407 : Blo 1200417 1202407 := bstep (se 1 (by rfl) ⟨901805, by rfl⟩ : syracuseStep 1202407 = 1803611) B1803611
theorem B2701547 : Blo 1200417 2701547 := bstep (se 1 (by rfl) ⟨2026160, by rfl⟩ : syracuseStep 2701547 = 4052321) B4052321
theorem B9115901 : Blo 1200417 9115901 := bstep (se 3 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 9115901 = 3418463) B3418463
theorem B1800647 : Blo 1200417 1800647 := bstep (se 1 (by rfl) ⟨1350485, by rfl⟩ : syracuseStep 1800647 = 2700971) B2700971
theorem B7305875 : Blo 1200417 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B1800863 : Blo 1200417 1800863 := bstep (se 1 (by rfl) ⟨1350647, by rfl⟩ : syracuseStep 1800863 = 2701295) B2701295
theorem B1801007 : Blo 1200417 1801007 := bstep (se 1 (by rfl) ⟨1350755, by rfl⟩ : syracuseStep 1801007 = 2701511) B2701511
theorem B1801127 : Blo 1200417 1801127 := bstep (se 1 (by rfl) ⟨1350845, by rfl⟩ : syracuseStep 1801127 = 2701691) B2701691
theorem B5774273 : Blo 1200417 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B4053995 : Blo 1200417 4053995 := bstep (se 1 (by rfl) ⟨3040496, by rfl⟩ : syracuseStep 4053995 = 6080993) B6080993
theorem B4561991 : Blo 1200417 4561991 := bstep (se 1 (by rfl) ⟨3421493, by rfl⟩ : syracuseStep 4561991 = 6842987) B6842987
theorem B1801307 : Blo 1200417 1801307 := bstep (se 1 (by rfl) ⟨1350980, by rfl⟩ : syracuseStep 1801307 = 2701961) B2701961
theorem B11541619 : Blo 1200417 11541619 := bstep (se 1 (by rfl) ⟨8656214, by rfl⟩ : syracuseStep 11541619 = 17312429) B17312429
theorem B3423475 : Blo 1200417 3423475 := bstep (se 1 (by rfl) ⟨2567606, by rfl⟩ : syracuseStep 3423475 = 5135213) B5135213
theorem B10272203 : Blo 1200417 10272203 := bstep (se 1 (by rfl) ⟨7704152, by rfl⟩ : syracuseStep 10272203 = 15408305) B15408305
theorem B1801679 : Blo 1200417 1801679 := bstep (se 1 (by rfl) ⟨1351259, by rfl⟩ : syracuseStep 1801679 = 2702519) B2702519
theorem B2702843 : Blo 1200417 2702843 := bstep (se 1 (by rfl) ⟨2027132, by rfl⟩ : syracuseStep 2702843 = 4054265) B4054265
theorem B70278691 : Blo 1200417 70278691 := bstep (se 1 (by rfl) ⟨52709018, by rfl⟩ : syracuseStep 70278691 = 105418037) B105418037
theorem B1711783 : Blo 1200417 1711783 := bstep (se 1 (by rfl) ⟨1283837, by rfl⟩ : syracuseStep 1711783 = 2567675) B2567675
theorem B2703023 : Blo 1200417 2703023 := bstep (se 1 (by rfl) ⟨2027267, by rfl⟩ : syracuseStep 2703023 = 4054535) B4054535
theorem B1351399 : Blo 1200417 1351399 := bstep (se 1 (by rfl) ⟨1013549, by rfl⟩ : syracuseStep 1351399 = 2027099) B2027099
theorem B2703113 : Blo 1200417 2703113 := bstep (se 2 (by rfl) ⟨1013667, by rfl⟩ : syracuseStep 2703113 = 2027335) B2027335
theorem B1802063 : Blo 1200417 1802063 := bstep (se 1 (by rfl) ⟨1351547, by rfl⟩ : syracuseStep 1802063 = 2703095) B2703095
theorem B1802183 : Blo 1200417 1802183 := bstep (se 1 (by rfl) ⟨1351637, by rfl⟩ : syracuseStep 1802183 = 2703275) B2703275
theorem B2924531 : Blo 1200417 2924531 := bstep (se 1 (by rfl) ⟨2193398, by rfl⟩ : syracuseStep 2924531 = 4386797) B4386797
theorem B9248897 : Blo 1200417 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B5128379 : Blo 1200417 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B1802495 : Blo 1200417 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B46850309 : Blo 1200417 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B2703671 : Blo 1200417 2703671 := bstep (se 1 (by rfl) ⟨2027753, by rfl⟩ : syracuseStep 2703671 = 4055507) B4055507
theorem B13689161 : Blo 1200417 13689161 := bstep (se 2 (by rfl) ⟨5133435, by rfl⟩ : syracuseStep 13689161 = 10266871) B10266871
theorem B3080585 : Blo 1200417 3080585 := bstep (se 2 (by rfl) ⟨1155219, by rfl⟩ : syracuseStep 3080585 = 2310439) B2310439
theorem B1802651 : Blo 1200417 1802651 := bstep (se 1 (by rfl) ⟨1351988, by rfl⟩ : syracuseStep 1802651 = 2703977) B2703977
theorem B13861523 : Blo 1200417 13861523 := bstep (se 1 (by rfl) ⟨10396142, by rfl⟩ : syracuseStep 13861523 = 20792285) B20792285
theorem B6841097 : Blo 1200417 6841097 := bstep (se 2 (by rfl) ⟨2565411, by rfl⟩ : syracuseStep 6841097 = 5130823) B5130823
theorem B1803071 : Blo 1200417 1803071 := bstep (se 1 (by rfl) ⟨1352303, by rfl⟩ : syracuseStep 1803071 = 2704607) B2704607
theorem B1803215 : Blo 1200417 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B1803305 : Blo 1200417 1803305 := bstep (se 2 (by rfl) ⟨676239, by rfl⟩ : syracuseStep 1803305 = 1352479) B1352479
theorem B1803335 : Blo 1200417 1803335 := bstep (se 1 (by rfl) ⟨1352501, by rfl⟩ : syracuseStep 1803335 = 2705003) B2705003
theorem B3466351 : Blo 1200417 3466351 := bstep (se 1 (by rfl) ⟨2599763, by rfl⟩ : syracuseStep 3466351 = 5199527) B5199527
theorem B9127079 : Blo 1200417 9127079 := bstep (se 1 (by rfl) ⟨6845309, by rfl⟩ : syracuseStep 9127079 = 13690619) B13690619
theorem B1803515 : Blo 1200417 1803515 := bstep (se 1 (by rfl) ⟨1352636, by rfl⟩ : syracuseStep 1803515 = 2705273) B2705273
theorem B4564633 : Blo 1200417 4564633 := bstep (se 2 (by rfl) ⟨1711737, by rfl⟩ : syracuseStep 4564633 = 3423475) B3423475
theorem B1542079 : Blo 1200417 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B3041327 : Blo 1200417 3041327 := bstep (se 1 (by rfl) ⟨2280995, by rfl⟩ : syracuseStep 3041327 = 4561991) B4561991
theorem B4057721 : Blo 1200417 4057721 := bstep (se 2 (by rfl) ⟨1521645, by rfl⟩ : syracuseStep 4057721 = 3043291) B3043291
theorem B7703207 : Blo 1200417 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B3754721 : Blo 1200417 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B28134161 : Blo 1200417 28134161 := bstep (se 2 (by rfl) ⟨10550310, by rfl⟩ : syracuseStep 28134161 = 21100621) B21100621
theorem B7301983 : Blo 1200417 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B2026363 : Blo 1200417 2026363 := bstep (se 1 (by rfl) ⟨1519772, by rfl⟩ : syracuseStep 2026363 = 3039545) B3039545
theorem B7695233 : Blo 1200417 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B3042299 : Blo 1200417 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B10259459 : Blo 1200417 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B9129023 : Blo 1200417 9129023 := bstep (se 1 (by rfl) ⟨6846767, by rfl⟩ : syracuseStep 9129023 = 13693535) B13693535
theorem B32885837 : Blo 1200417 32885837 := bstep (se 3 (by rfl) ⟨6166094, by rfl⟩ : syracuseStep 32885837 = 12332189) B12332189
theorem B2026633 : Blo 1200417 2026633 := bstep (se 2 (by rfl) ⟨759987, by rfl⟩ : syracuseStep 2026633 = 1519975) B1519975
theorem B6491279 : Blo 1200417 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B2026687 : Blo 1200417 2026687 := bstep (se 1 (by rfl) ⟨1520015, by rfl⟩ : syracuseStep 2026687 = 3040031) B3040031
theorem B2567531 : Blo 1200417 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B15633917 : Blo 1200417 15633917 := bstep (se 3 (by rfl) ⟨2931359, by rfl⟩ : syracuseStep 15633917 = 5862719) B5862719
theorem B9129509 : Blo 1200417 9129509 := bstep (se 4 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 9129509 = 1711783) B1711783
theorem B4386811 : Blo 1200417 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B15388825 : Blo 1200417 15388825 := bstep (se 2 (by rfl) ⟨5770809, by rfl⟩ : syracuseStep 15388825 = 11541619) B11541619
theorem B1200431 : Blo 1200417 1200431 := bstep (se 1 (by rfl) ⟨900323, by rfl⟩ : syracuseStep 1200431 = 1800647) B1800647
theorem B2027855 : Blo 1200417 2027855 := bstep (se 1 (by rfl) ⟨1520891, by rfl⟩ : syracuseStep 2027855 = 3041783) B3041783
theorem B4870583 : Blo 1200417 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B1200575 : Blo 1200417 1200575 := bstep (se 1 (by rfl) ⟨900431, by rfl⟩ : syracuseStep 1200575 = 1800863) B1800863
theorem B7696873 : Blo 1200417 7696873 := bstep (se 2 (by rfl) ⟨2886327, by rfl⟩ : syracuseStep 7696873 = 5772655) B5772655
theorem B1200671 : Blo 1200417 1200671 := bstep (se 1 (by rfl) ⟨900503, by rfl⟩ : syracuseStep 1200671 = 1801007) B1801007
theorem B1200751 : Blo 1200417 1200751 := bstep (se 1 (by rfl) ⟨900563, by rfl⟩ : syracuseStep 1200751 = 1801127) B1801127
theorem B93704921 : Blo 1200417 93704921 := bstep (se 2 (by rfl) ⟨35139345, by rfl⟩ : syracuseStep 93704921 = 70278691) B70278691
theorem B1200871 : Blo 1200417 1200871 := bstep (se 1 (by rfl) ⟨900653, by rfl⟩ : syracuseStep 1200871 = 1801307) B1801307
theorem B4559773 : Blo 1200417 4559773 := bstep (se 3 (by rfl) ⟨854957, by rfl⟩ : syracuseStep 4559773 = 1709915) B1709915
theorem B1201119 : Blo 1200417 1201119 := bstep (se 1 (by rfl) ⟨900839, by rfl⟩ : syracuseStep 1201119 = 1801679) B1801679
theorem B1520623 : Blo 1200417 1520623 := bstep (se 1 (by rfl) ⟨1140467, by rfl⟩ : syracuseStep 1520623 = 2280935) B2280935
theorem B1201375 : Blo 1200417 1201375 := bstep (se 1 (by rfl) ⟨901031, by rfl⟩ : syracuseStep 1201375 = 1802063) B1802063
theorem B1201455 : Blo 1200417 1201455 := bstep (se 1 (by rfl) ⟨901091, by rfl⟩ : syracuseStep 1201455 = 1802183) B1802183
theorem B13686245 : Blo 1200417 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B5772809 : Blo 1200417 5772809 := bstep (se 2 (by rfl) ⟨2164803, by rfl⟩ : syracuseStep 5772809 = 4329607) B4329607
theorem B1201695 : Blo 1200417 1201695 := bstep (se 1 (by rfl) ⟨901271, by rfl⟩ : syracuseStep 1201695 = 1802543) B1802543
theorem B3651151 : Blo 1200417 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B6084233 : Blo 1200417 6084233 := bstep (se 2 (by rfl) ⟨2281587, by rfl⟩ : syracuseStep 6084233 = 4563175) B4563175
theorem B1201855 : Blo 1200417 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B5855039 : Blo 1200417 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B11540389 : Blo 1200417 11540389 := bstep (se 4 (by rfl) ⟨1081911, by rfl⟩ : syracuseStep 11540389 = 2163823) B2163823
theorem B20527181 : Blo 1200417 20527181 := bstep (se 3 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 20527181 = 7697693) B7697693
theorem B1521767 : Blo 1200417 1521767 := bstep (se 1 (by rfl) ⟨1141325, by rfl⟩ : syracuseStep 1521767 = 2282651) B2282651
theorem B1202303 : Blo 1200417 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B1202399 : Blo 1200417 1202399 := bstep (se 1 (by rfl) ⟨901799, by rfl⟩ : syracuseStep 1202399 = 1803599) B1803599
theorem B1923527 : Blo 1200417 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B1800683 : Blo 1200417 1800683 := bstep (se 1 (by rfl) ⟨1350512, by rfl⟩ : syracuseStep 1800683 = 2701025) B2701025
theorem B2701871 : Blo 1200417 2701871 := bstep (se 1 (by rfl) ⟨2026403, by rfl⟩ : syracuseStep 2701871 = 4052807) B4052807
theorem B4561535 : Blo 1200417 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B30784211 : Blo 1200417 30784211 := bstep (se 1 (by rfl) ⟨23088158, by rfl⟩ : syracuseStep 30784211 = 46176317) B46176317
theorem B42154733 : Blo 1200417 42154733 := bstep (se 3 (by rfl) ⟨7904012, by rfl⟩ : syracuseStep 42154733 = 15808025) B15808025
theorem B7805737 : Blo 1200417 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B1801031 : Blo 1200417 1801031 := bstep (se 1 (by rfl) ⟨1350773, by rfl⟩ : syracuseStep 1801031 = 2701547) B2701547
theorem B6077267 : Blo 1200417 6077267 := bstep (se 1 (by rfl) ⟨4557950, by rfl⟩ : syracuseStep 6077267 = 9115901) B9115901
theorem B6085691 : Blo 1200417 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B3652769 : Blo 1200417 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B1924283 : Blo 1200417 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B10263833 : Blo 1200417 10263833 := bstep (se 2 (by rfl) ⟨3848937, by rfl⟩ : syracuseStep 10263833 = 7697875) B7697875
theorem B3849515 : Blo 1200417 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B2702663 : Blo 1200417 2702663 := bstep (se 1 (by rfl) ⟨2026997, by rfl⟩ : syracuseStep 2702663 = 4053995) B4053995
theorem B1711567 : Blo 1200417 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B6848135 : Blo 1200417 6848135 := bstep (se 1 (by rfl) ⟨5136101, by rfl⟩ : syracuseStep 6848135 = 10272203) B10272203
theorem B1801865 : Blo 1200417 1801865 := bstep (se 2 (by rfl) ⟨675699, by rfl⟩ : syracuseStep 1801865 = 1351399) B1351399
theorem B1801895 : Blo 1200417 1801895 := bstep (se 1 (by rfl) ⟨1351421, by rfl⟩ : syracuseStep 1801895 = 2702843) B2702843
theorem B1802015 : Blo 1200417 1802015 := bstep (se 1 (by rfl) ⟨1351511, by rfl⟩ : syracuseStep 1802015 = 2703023) B2703023
theorem B1802075 : Blo 1200417 1802075 := bstep (se 1 (by rfl) ⟨1351556, by rfl⟩ : syracuseStep 1802075 = 2703113) B2703113
theorem B1949687 : Blo 1200417 1949687 := bstep (se 1 (by rfl) ⟨1462265, by rfl⟩ : syracuseStep 1949687 = 2924531) B2924531
theorem B1802447 : Blo 1200417 1802447 := bstep (se 1 (by rfl) ⟨1351835, by rfl⟩ : syracuseStep 1802447 = 2703671) B2703671
theorem B9126107 : Blo 1200417 9126107 := bstep (se 1 (by rfl) ⟨6844580, by rfl⟩ : syracuseStep 9126107 = 13689161) B13689161
theorem B1351903 : Blo 1200417 1351903 := bstep (se 1 (by rfl) ⟨1013927, by rfl⟩ : syracuseStep 1351903 = 2027855) B2027855
theorem B9241015 : Blo 1200417 9241015 := bstep (se 1 (by rfl) ⟨6930761, by rfl⟩ : syracuseStep 9241015 = 13861523) B13861523
theorem B4056155 : Blo 1200417 4056155 := bstep (se 1 (by rfl) ⟨3042116, by rfl⟩ : syracuseStep 4056155 = 6084233) B6084233
theorem B5129405 : Blo 1200417 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B6079697 : Blo 1200417 6079697 := bstep (se 2 (by rfl) ⟨2279886, by rfl⟩ : syracuseStep 6079697 = 4559773) B4559773
theorem B15394157 : Blo 1200417 15394157 := bstep (se 3 (by rfl) ⟨2886404, by rfl⟩ : syracuseStep 15394157 = 5772809) B5772809
theorem B4621801 : Blo 1200417 4621801 := bstep (se 2 (by rfl) ⟨1733175, by rfl⟩ : syracuseStep 4621801 = 3466351) B3466351
theorem B2705147 : Blo 1200417 2705147 := bstep (se 1 (by rfl) ⟨2028860, by rfl⟩ : syracuseStep 2705147 = 4057721) B4057721
theorem B3041023 : Blo 1200417 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B20522807 : Blo 1200417 20522807 := bstep (se 1 (by rfl) ⟨15392105, by rfl⟩ : syracuseStep 20522807 = 30784211) B30784211
theorem B5130155 : Blo 1200417 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B4057127 : Blo 1200417 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B21923891 : Blo 1200417 21923891 := bstep (se 1 (by rfl) ⟨16442918, by rfl⟩ : syracuseStep 21923891 = 32885837) B32885837
theorem B4327519 : Blo 1200417 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B4868201 : Blo 1200417 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B2435179 : Blo 1200417 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B6842555 : Blo 1200417 6842555 := bstep (se 1 (by rfl) ⟨5131916, by rfl⟩ : syracuseStep 6842555 = 10263833) B10263833
theorem B2566343 : Blo 1200417 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B10422611 : Blo 1200417 10422611 := bstep (se 1 (by rfl) ⟨7816958, by rfl⟩ : syracuseStep 10422611 = 15633917) B15633917
theorem B4565423 : Blo 1200417 4565423 := bstep (se 1 (by rfl) ⟨3424067, by rfl⟩ : syracuseStep 4565423 = 6848135) B6848135
theorem B15387185 : Blo 1200417 15387185 := bstep (se 2 (by rfl) ⟨5770194, by rfl⟩ : syracuseStep 15387185 = 11540389) B11540389
theorem B3418919 : Blo 1200417 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B4058045 : Blo 1200417 4058045 := bstep (se 3 (by rfl) ⟨760883, by rfl⟩ : syracuseStep 4058045 = 1521767) B1521767
theorem B3247055 : Blo 1200417 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B5131421 : Blo 1200417 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B10407649 : Blo 1200417 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B9735977 : Blo 1200417 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B2027497 : Blo 1200417 2027497 := bstep (se 2 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 2027497 = 1520623) B1520623
theorem B2027551 : Blo 1200417 2027551 := bstep (se 1 (by rfl) ⟨1520663, by rfl⟩ : syracuseStep 2027551 = 3041327) B3041327
theorem B13684787 : Blo 1200417 13684787 := bstep (se 1 (by rfl) ⟨10263590, by rfl⟩ : syracuseStep 13684787 = 20527181) B20527181
theorem B1200455 : Blo 1200417 1200455 := bstep (se 1 (by rfl) ⟨900341, by rfl⟩ : syracuseStep 1200455 = 1800683) B1800683
theorem B2503147 : Blo 1200417 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B28103155 : Blo 1200417 28103155 := bstep (se 1 (by rfl) ⟨21077366, by rfl⟩ : syracuseStep 28103155 = 42154733) B42154733
theorem B18756107 : Blo 1200417 18756107 := bstep (se 1 (by rfl) ⟨14067080, by rfl⟩ : syracuseStep 18756107 = 28134161) B28134161
theorem B1200687 : Blo 1200417 1200687 := bstep (se 1 (by rfl) ⟨900515, by rfl⟩ : syracuseStep 1200687 = 1801031) B1801031
theorem B4051511 : Blo 1200417 4051511 := bstep (se 1 (by rfl) ⟨3038633, by rfl⟩ : syracuseStep 4051511 = 6077267) B6077267
theorem B2282089 : Blo 1200417 2282089 := bstep (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) B1711567
theorem B2028199 : Blo 1200417 2028199 := bstep (se 1 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 2028199 = 3042299) B3042299
theorem B1201243 : Blo 1200417 1201243 := bstep (se 1 (by rfl) ⟨900932, by rfl⟩ : syracuseStep 1201243 = 1801865) B1801865
theorem B1201263 : Blo 1200417 1201263 := bstep (se 1 (by rfl) ⟨900947, by rfl⟩ : syracuseStep 1201263 = 1801895) B1801895
theorem B1201343 : Blo 1200417 1201343 := bstep (se 1 (by rfl) ⟨901007, by rfl⟩ : syracuseStep 1201343 = 1802015) B1802015
theorem B1201383 : Blo 1200417 1201383 := bstep (se 1 (by rfl) ⟨901037, by rfl⟩ : syracuseStep 1201383 = 1802075) B1802075
theorem B1299791 : Blo 1200417 1299791 := bstep (se 1 (by rfl) ⟨974843, by rfl⟩ : syracuseStep 1299791 = 1949687) B1949687
theorem B6165931 : Blo 1200417 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B1201663 : Blo 1200417 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B31233539 : Blo 1200417 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B20518433 : Blo 1200417 20518433 := bstep (se 2 (by rfl) ⟨7694412, by rfl⟩ : syracuseStep 20518433 = 15388825) B15388825
theorem B2053723 : Blo 1200417 2053723 := bstep (se 1 (by rfl) ⟨1540292, by rfl⟩ : syracuseStep 2053723 = 3080585) B3080585
theorem B1201767 : Blo 1200417 1201767 := bstep (se 1 (by rfl) ⟨901325, by rfl⟩ : syracuseStep 1201767 = 1802651) B1802651
theorem B62469947 : Blo 1200417 62469947 := bstep (se 1 (by rfl) ⟨46852460, by rfl⟩ : syracuseStep 62469947 = 93704921) B93704921
theorem B4560731 : Blo 1200417 4560731 := bstep (se 1 (by rfl) ⟨3420548, by rfl⟩ : syracuseStep 4560731 = 6841097) B6841097
theorem B1202047 : Blo 1200417 1202047 := bstep (se 1 (by rfl) ⟨901535, by rfl⟩ : syracuseStep 1202047 = 1803071) B1803071
theorem B10262497 : Blo 1200417 10262497 := bstep (se 2 (by rfl) ⟨3848436, by rfl⟩ : syracuseStep 10262497 = 7696873) B7696873
theorem B1202143 : Blo 1200417 1202143 := bstep (se 1 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 1202143 = 1803215) B1803215
theorem B62453749 : Blo 1200417 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B1202203 : Blo 1200417 1202203 := bstep (se 1 (by rfl) ⟨901652, by rfl⟩ : syracuseStep 1202203 = 1803305) B1803305
theorem B1202223 : Blo 1200417 1202223 := bstep (se 1 (by rfl) ⟨901667, by rfl⟩ : syracuseStep 1202223 = 1803335) B1803335
theorem B6084719 : Blo 1200417 6084719 := bstep (se 1 (by rfl) ⟨4563539, by rfl⟩ : syracuseStep 6084719 = 9127079) B9127079
theorem B1202343 : Blo 1200417 1202343 := bstep (se 1 (by rfl) ⟨901757, by rfl⟩ : syracuseStep 1202343 = 1803515) B1803515
theorem B9124163 : Blo 1200417 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B2701817 : Blo 1200417 2701817 := bstep (se 2 (by rfl) ⟨1013181, by rfl⟩ : syracuseStep 2701817 = 2026363) B2026363
theorem B2702177 : Blo 1200417 2702177 := bstep (se 2 (by rfl) ⟨1013316, by rfl⟩ : syracuseStep 2702177 = 2026633) B2026633
theorem B2702249 : Blo 1200417 2702249 := bstep (se 2 (by rfl) ⟨1013343, by rfl⟩ : syracuseStep 2702249 = 2026687) B2026687
theorem B1801247 : Blo 1200417 1801247 := bstep (se 1 (by rfl) ⟨1350935, by rfl⟩ : syracuseStep 1801247 = 2701871) B2701871
theorem B5135471 : Blo 1200417 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B6839639 : Blo 1200417 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B6086015 : Blo 1200417 6086015 := bstep (se 1 (by rfl) ⟨4564511, by rfl⟩ : syracuseStep 6086015 = 9129023) B9129023
theorem B6086177 : Blo 1200417 6086177 := bstep (se 2 (by rfl) ⟨2282316, by rfl⟩ : syracuseStep 6086177 = 4564633) B4564633
theorem B1801775 : Blo 1200417 1801775 := bstep (se 1 (by rfl) ⟨1351331, by rfl⟩ : syracuseStep 1801775 = 2702663) B2702663
theorem B1711687 : Blo 1200417 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B6086339 : Blo 1200417 6086339 := bstep (se 1 (by rfl) ⟨4564754, by rfl⟩ : syracuseStep 6086339 = 9129509) B9129509
theorem B2056105 : Blo 1200417 2056105 := bstep (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) B1542079
theorem B5849081 : Blo 1200417 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B2703401 : Blo 1200417 2703401 := bstep (se 2 (by rfl) ⟨1013775, by rfl⟩ : syracuseStep 2703401 = 2027551) B2027551
theorem B1802537 : Blo 1200417 1802537 := bstep (se 2 (by rfl) ⟨675951, by rfl⟩ : syracuseStep 1802537 = 1351903) B1351903
theorem B12321353 : Blo 1200417 12321353 := bstep (se 2 (by rfl) ⟨4620507, by rfl⟩ : syracuseStep 12321353 = 9241015) B9241015
theorem B2704103 : Blo 1200417 2704103 := bstep (se 1 (by rfl) ⟨2028077, by rfl⟩ : syracuseStep 2704103 = 4056155) B4056155
theorem B3466109 : Blo 1200417 3466109 := bstep (se 3 (by rfl) ⟨649895, by rfl⟩ : syracuseStep 3466109 = 1299791) B1299791
theorem B2704265 : Blo 1200417 2704265 := bstep (se 2 (by rfl) ⟨1014099, by rfl⟩ : syracuseStep 2704265 = 2028199) B2028199
theorem B1803431 : Blo 1200417 1803431 := bstep (se 1 (by rfl) ⟨1352573, by rfl⟩ : syracuseStep 1803431 = 2705147) B2705147
theorem B13681871 : Blo 1200417 13681871 := bstep (se 1 (by rfl) ⟨10261403, by rfl⟩ : syracuseStep 13681871 = 20522807) B20522807
theorem B3040487 : Blo 1200417 3040487 := bstep (se 1 (by rfl) ⟨2280365, by rfl⟩ : syracuseStep 3040487 = 4560731) B4560731
theorem B2704751 : Blo 1200417 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B14615927 : Blo 1200417 14615927 := bstep (se 1 (by rfl) ⟨10961945, by rfl⟩ : syracuseStep 14615927 = 21923891) B21923891
theorem B3245467 : Blo 1200417 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B4056479 : Blo 1200417 4056479 := bstep (se 1 (by rfl) ⟨3042359, by rfl⟩ : syracuseStep 4056479 = 6084719) B6084719
theorem B6948407 : Blo 1200417 6948407 := bstep (se 1 (by rfl) ⟨5211305, by rfl⟩ : syracuseStep 6948407 = 10422611) B10422611
theorem B10258123 : Blo 1200417 10258123 := bstep (se 1 (by rfl) ⟨7693592, by rfl⟩ : syracuseStep 10258123 = 15387185) B15387185
theorem B2279279 : Blo 1200417 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B2705363 : Blo 1200417 2705363 := bstep (se 1 (by rfl) ⟨2029022, by rfl⟩ : syracuseStep 2705363 = 4058045) B4058045
theorem B2164703 : Blo 1200417 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B6162401 : Blo 1200417 6162401 := bstep (se 2 (by rfl) ⟨2310900, by rfl⟩ : syracuseStep 6162401 = 4621801) B4621801
theorem B2738297 : Blo 1200417 2738297 := bstep (se 2 (by rfl) ⟨1026861, by rfl⟩ : syracuseStep 2738297 = 2053723) B2053723
theorem B4057343 : Blo 1200417 4057343 := bstep (se 1 (by rfl) ⟨3043007, by rfl⟩ : syracuseStep 4057343 = 6086015) B6086015
theorem B4057451 : Blo 1200417 4057451 := bstep (se 1 (by rfl) ⟨3043088, by rfl⟩ : syracuseStep 4057451 = 6086177) B6086177
theorem B4057559 : Blo 1200417 4057559 := bstep (se 1 (by rfl) ⟨3043169, by rfl⟩ : syracuseStep 4057559 = 6086339) B6086339
theorem B6490651 : Blo 1200417 6490651 := bstep (se 1 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 6490651 = 9735977) B9735977
theorem B149883493 : Blo 1200417 149883493 := bstep (se 4 (by rfl) ⟨14051577, by rfl⟩ : syracuseStep 149883493 = 28103155) B28103155
theorem B13683329 : Blo 1200417 13683329 := bstep (se 2 (by rfl) ⟨5131248, by rfl⟩ : syracuseStep 13683329 = 10262497) B10262497
theorem B5770025 : Blo 1200417 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B3246905 : Blo 1200417 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B12504071 : Blo 1200417 12504071 := bstep (se 1 (by rfl) ⟨9378053, by rfl⟩ : syracuseStep 12504071 = 18756107) B18756107
theorem B3337529 : Blo 1200417 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B3419603 : Blo 1200417 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B3042785 : Blo 1200417 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B6082775 : Blo 1200417 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B3043615 : Blo 1200417 3043615 := bstep (se 1 (by rfl) ⟨2282711, by rfl⟩ : syracuseStep 3043615 = 4565423) B4565423
theorem B8221241 : Blo 1200417 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B1200831 : Blo 1200417 1200831 := bstep (se 1 (by rfl) ⟨900623, by rfl⟩ : syracuseStep 1200831 = 1801247) B1801247
theorem B2282249 : Blo 1200417 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B3420947 : Blo 1200417 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B4559759 : Blo 1200417 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B1201183 : Blo 1200417 1201183 := bstep (se 1 (by rfl) ⟨900887, by rfl⟩ : syracuseStep 1201183 = 1801775) B1801775
theorem B2741473 : Blo 1200417 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B9123191 : Blo 1200417 9123191 := bstep (se 1 (by rfl) ⟨6842393, by rfl⟩ : syracuseStep 9123191 = 13684787) B13684787
theorem B1201631 : Blo 1200417 1201631 := bstep (se 1 (by rfl) ⟨901223, by rfl⟩ : syracuseStep 1201631 = 1802447) B1802447
theorem B6084071 : Blo 1200417 6084071 := bstep (se 1 (by rfl) ⟨4563053, by rfl⟩ : syracuseStep 6084071 = 9126107) B9126107
theorem B2701007 : Blo 1200417 2701007 := bstep (se 1 (by rfl) ⟨2025755, by rfl⟩ : syracuseStep 2701007 = 4051511) B4051511
theorem B4053131 : Blo 1200417 4053131 := bstep (se 1 (by rfl) ⟨3039848, by rfl⟩ : syracuseStep 4053131 = 6079697) B6079697
theorem B10262771 : Blo 1200417 10262771 := bstep (se 1 (by rfl) ⟨7697078, by rfl⟩ : syracuseStep 10262771 = 15394157) B15394157
theorem B20822359 : Blo 1200417 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B13678955 : Blo 1200417 13678955 := bstep (se 1 (by rfl) ⟨10259216, by rfl⟩ : syracuseStep 13678955 = 20518433) B20518433
theorem B41646631 : Blo 1200417 41646631 := bstep (se 1 (by rfl) ⟨31234973, by rfl⟩ : syracuseStep 41646631 = 62469947) B62469947
theorem B4561703 : Blo 1200417 4561703 := bstep (se 1 (by rfl) ⟨3421277, by rfl⟩ : syracuseStep 4561703 = 6842555) B6842555
theorem B1710895 : Blo 1200417 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B1801211 : Blo 1200417 1801211 := bstep (se 1 (by rfl) ⟨1350908, by rfl⟩ : syracuseStep 1801211 = 2701817) B2701817
theorem B1801451 : Blo 1200417 1801451 := bstep (se 1 (by rfl) ⟨1351088, by rfl⟩ : syracuseStep 1801451 = 2702177) B2702177
theorem B1801499 : Blo 1200417 1801499 := bstep (se 1 (by rfl) ⟨1351124, by rfl⟩ : syracuseStep 1801499 = 2702249) B2702249
theorem B3423647 : Blo 1200417 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B13876865 : Blo 1200417 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B4054697 : Blo 1200417 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B13680413 : Blo 1200417 13680413 := bstep (se 3 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 13680413 = 5130155) B5130155
theorem B2703329 : Blo 1200417 2703329 := bstep (se 2 (by rfl) ⟨1013748, by rfl⟩ : syracuseStep 2703329 = 2027497) B2027497
theorem B83271665 : Blo 1200417 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B3899387 : Blo 1200417 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B1802267 : Blo 1200417 1802267 := bstep (se 1 (by rfl) ⟨1351700, by rfl⟩ : syracuseStep 1802267 = 2703401) B2703401
theorem B4055183 : Blo 1200417 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B5480827 : Blo 1200417 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B27763145 : Blo 1200417 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B1802735 : Blo 1200417 1802735 := bstep (se 1 (by rfl) ⟨1352051, by rfl⟩ : syracuseStep 1802735 = 2704103) B2704103
theorem B1802843 : Blo 1200417 1802843 := bstep (se 1 (by rfl) ⟨1352132, by rfl⟩ : syracuseStep 1802843 = 2704265) B2704265
theorem B3039839 : Blo 1200417 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B199844657 : Blo 1200417 199844657 := bstep (se 2 (by rfl) ⟨74941746, by rfl⟩ : syracuseStep 199844657 = 149883493) B149883493
theorem B1803167 : Blo 1200417 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B2704319 : Blo 1200417 2704319 := bstep (se 1 (by rfl) ⟨2028239, by rfl⟩ : syracuseStep 2704319 = 4056479) B4056479
theorem B4056047 : Blo 1200417 4056047 := bstep (se 1 (by rfl) ⟨3042035, by rfl⟩ : syracuseStep 4056047 = 6084071) B6084071
theorem B1803575 : Blo 1200417 1803575 := bstep (se 1 (by rfl) ⟨1352681, by rfl⟩ : syracuseStep 1803575 = 2705363) B2705363
theorem B6841847 : Blo 1200417 6841847 := bstep (se 1 (by rfl) ⟨5131385, by rfl⟩ : syracuseStep 6841847 = 10262771) B10262771
theorem B2704895 : Blo 1200417 2704895 := bstep (se 1 (by rfl) ⟨2028671, by rfl⟩ : syracuseStep 2704895 = 4057343) B4057343
theorem B9119303 : Blo 1200417 9119303 := bstep (se 1 (by rfl) ⟨6839477, by rfl⟩ : syracuseStep 9119303 = 13678955) B13678955
theorem B2704967 : Blo 1200417 2704967 := bstep (se 1 (by rfl) ⟨2028725, by rfl⟩ : syracuseStep 2704967 = 4057451) B4057451
theorem B3655297 : Blo 1200417 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B2705039 : Blo 1200417 2705039 := bstep (se 1 (by rfl) ⟨2028779, by rfl⟩ : syracuseStep 2705039 = 4057559) B4057559
theorem B3041135 : Blo 1200417 3041135 := bstep (se 1 (by rfl) ⟨2280851, by rfl⟩ : syracuseStep 3041135 = 4561703) B4561703
theorem B4327289 : Blo 1200417 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B2164603 : Blo 1200417 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B2279735 : Blo 1200417 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B9242957 : Blo 1200417 9242957 := bstep (se 3 (by rfl) ⟨1733054, by rfl⟩ : syracuseStep 9242957 = 3466109) B3466109
theorem B9251243 : Blo 1200417 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B9120275 : Blo 1200417 9120275 := bstep (se 1 (by rfl) ⟨6840206, by rfl⟩ : syracuseStep 9120275 = 13680413) B13680413
theorem B10398365 : Blo 1200417 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B7302125 : Blo 1200417 7302125 := bstep (se 3 (by rfl) ⟨1369148, by rfl⟩ : syracuseStep 7302125 = 2738297) B2738297
theorem B4058153 : Blo 1200417 4058153 := bstep (se 2 (by rfl) ⟨1521807, by rfl⟩ : syracuseStep 4058153 = 3043615) B3043615
theorem B2280631 : Blo 1200417 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B8654201 : Blo 1200417 8654201 := bstep (se 2 (by rfl) ⟨3245325, by rfl⟩ : syracuseStep 8654201 = 6490651) B6490651
theorem B55528841 : Blo 1200417 55528841 := bstep (se 2 (by rfl) ⟨20823315, by rfl⟩ : syracuseStep 55528841 = 41646631) B41646631
theorem B9121247 : Blo 1200417 9121247 := bstep (se 1 (by rfl) ⟨6840935, by rfl⟩ : syracuseStep 9121247 = 13681871) B13681871
theorem B8900077 : Blo 1200417 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B2026991 : Blo 1200417 2026991 := bstep (se 1 (by rfl) ⟨1520243, by rfl⟩ : syracuseStep 2026991 = 3040487) B3040487
theorem B6082127 : Blo 1200417 6082127 := bstep (se 1 (by rfl) ⟨4561595, by rfl⟩ : syracuseStep 6082127 = 9123191) B9123191
theorem B9743951 : Blo 1200417 9743951 := bstep (se 1 (by rfl) ⟨7307963, by rfl⟩ : syracuseStep 9743951 = 14615927) B14615927
theorem B4632271 : Blo 1200417 4632271 := bstep (se 1 (by rfl) ⟨3474203, by rfl⟩ : syracuseStep 4632271 = 6948407) B6948407
theorem B2281193 : Blo 1200417 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B4108267 : Blo 1200417 4108267 := bstep (se 1 (by rfl) ⟨3081200, by rfl⟩ : syracuseStep 4108267 = 6162401) B6162401
theorem B9122219 : Blo 1200417 9122219 := bstep (se 1 (by rfl) ⟨6841664, by rfl⟩ : syracuseStep 9122219 = 13683329) B13683329
theorem B3846683 : Blo 1200417 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B1200807 : Blo 1200417 1200807 := bstep (se 1 (by rfl) ⟨900605, by rfl⟩ : syracuseStep 1200807 = 1801211) B1801211
theorem B8336047 : Blo 1200417 8336047 := bstep (se 1 (by rfl) ⟨6252035, by rfl⟩ : syracuseStep 8336047 = 12504071) B12504071
theorem B1200967 : Blo 1200417 1200967 := bstep (se 1 (by rfl) ⟨900725, by rfl⟩ : syracuseStep 1200967 = 1801451) B1801451
theorem B1200999 : Blo 1200417 1200999 := bstep (se 1 (by rfl) ⟨900749, by rfl⟩ : syracuseStep 1200999 = 1801499) B1801499
theorem B13677497 : Blo 1200417 13677497 := bstep (se 2 (by rfl) ⟨5129061, by rfl⟩ : syracuseStep 13677497 = 10258123) B10258123
theorem B2282431 : Blo 1200417 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B2028523 : Blo 1200417 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B5772541 : Blo 1200417 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B55514443 : Blo 1200417 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B1201691 : Blo 1200417 1201691 := bstep (se 1 (by rfl) ⟨901268, by rfl⟩ : syracuseStep 1201691 = 1802537) B1802537
theorem B1521499 : Blo 1200417 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B1202287 : Blo 1200417 1202287 := bstep (se 1 (by rfl) ⟨901715, by rfl⟩ : syracuseStep 1202287 = 1803431) B1803431
theorem B1800671 : Blo 1200417 1800671 := bstep (se 1 (by rfl) ⟨1350503, by rfl⟩ : syracuseStep 1800671 = 2701007) B2701007
theorem B2702087 : Blo 1200417 2702087 := bstep (se 1 (by rfl) ⟨2026565, by rfl⟩ : syracuseStep 2702087 = 4053131) B4053131
theorem B32856941 : Blo 1200417 32856941 := bstep (se 3 (by rfl) ⟨6160676, by rfl⟩ : syracuseStep 32856941 = 12321353) B12321353
theorem B6078077 : Blo 1200417 6078077 := bstep (se 3 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 6078077 = 2279279) B2279279
theorem B2703131 : Blo 1200417 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B1802219 : Blo 1200417 1802219 := bstep (se 1 (by rfl) ⟨1351664, by rfl⟩ : syracuseStep 1802219 = 2703329) B2703329
theorem B2703455 : Blo 1200417 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B2564455 : Blo 1200417 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B9118331 : Blo 1200417 9118331 := bstep (se 1 (by rfl) ⟨6838748, by rfl⟩ : syracuseStep 9118331 = 13677497) B13677497
theorem B1802879 : Blo 1200417 1802879 := bstep (se 1 (by rfl) ⟨1352159, by rfl⟩ : syracuseStep 1802879 = 2704319) B2704319
theorem B2704031 : Blo 1200417 2704031 := bstep (se 1 (by rfl) ⟨2028023, by rfl⟩ : syracuseStep 2704031 = 4056047) B4056047
theorem B1803263 : Blo 1200417 1803263 := bstep (se 1 (by rfl) ⟨1352447, by rfl⟩ : syracuseStep 1803263 = 2704895) B2704895
theorem B6079535 : Blo 1200417 6079535 := bstep (se 1 (by rfl) ⟨4559651, by rfl⟩ : syracuseStep 6079535 = 9119303) B9119303
theorem B1803311 : Blo 1200417 1803311 := bstep (se 1 (by rfl) ⟨1352483, by rfl⟩ : syracuseStep 1803311 = 2704967) B2704967
theorem B1803359 : Blo 1200417 1803359 := bstep (se 1 (by rfl) ⟨1352519, by rfl⟩ : syracuseStep 1803359 = 2705039) B2705039
theorem B2884859 : Blo 1200417 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B2704697 : Blo 1200417 2704697 := bstep (se 2 (by rfl) ⟨1014261, by rfl⟩ : syracuseStep 2704697 = 2028523) B2028523
theorem B3040841 : Blo 1200417 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B98821781 : Blo 1200417 98821781 := bstep (se 6 (by rfl) ⟨2316135, by rfl⟩ : syracuseStep 98821781 = 4632271) B4632271
theorem B6080183 : Blo 1200417 6080183 := bstep (se 1 (by rfl) ⟨4560137, by rfl⟩ : syracuseStep 6080183 = 9120275) B9120275
theorem B6932243 : Blo 1200417 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B29231077 : Blo 1200417 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B4868083 : Blo 1200417 4868083 := bstep (se 1 (by rfl) ⟨3651062, by rfl⟩ : syracuseStep 4868083 = 7302125) B7302125
theorem B2705435 : Blo 1200417 2705435 := bstep (se 1 (by rfl) ⟨2029076, by rfl⟩ : syracuseStep 2705435 = 4058153) B4058153
theorem B5769467 : Blo 1200417 5769467 := bstep (se 1 (by rfl) ⟨4327100, by rfl⟩ : syracuseStep 5769467 = 8654201) B8654201
theorem B6080831 : Blo 1200417 6080831 := bstep (se 1 (by rfl) ⟨4560623, by rfl⟩ : syracuseStep 6080831 = 9121247) B9121247
theorem B2886137 : Blo 1200417 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B6081479 : Blo 1200417 6081479 := bstep (se 1 (by rfl) ⟨4561109, by rfl⟩ : syracuseStep 6081479 = 9122219) B9122219
theorem B18508763 : Blo 1200417 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B2026559 : Blo 1200417 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B133229771 : Blo 1200417 133229771 := bstep (se 1 (by rfl) ⟨99922328, by rfl⟩ : syracuseStep 133229771 = 199844657) B199844657
theorem B2027423 : Blo 1200417 2027423 := bstep (se 1 (by rfl) ⟨1520567, by rfl⟩ : syracuseStep 2027423 = 3041135) B3041135
theorem B3043241 : Blo 1200417 3043241 := bstep (se 2 (by rfl) ⟨1141215, by rfl⟩ : syracuseStep 3043241 = 2282431) B2282431
theorem B1519823 : Blo 1200417 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B1200447 : Blo 1200417 1200447 := bstep (se 1 (by rfl) ⟨900335, by rfl⟩ : syracuseStep 1200447 = 1800671) B1800671
theorem B7696721 : Blo 1200417 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B74019257 : Blo 1200417 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B11866769 : Blo 1200417 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B4052051 : Blo 1200417 4052051 := bstep (se 1 (by rfl) ⟨3039038, by rfl⟩ : syracuseStep 4052051 = 6078077) B6078077
theorem B2028665 : Blo 1200417 2028665 := bstep (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) B1521499
theorem B1520795 : Blo 1200417 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B5477689 : Blo 1200417 5477689 := bstep (se 2 (by rfl) ⟨2054133, by rfl⟩ : syracuseStep 5477689 = 4108267) B4108267
theorem B1201479 : Blo 1200417 1201479 := bstep (se 1 (by rfl) ⟨901109, by rfl⟩ : syracuseStep 1201479 = 1802219) B1802219
theorem B1201511 : Blo 1200417 1201511 := bstep (se 1 (by rfl) ⟨901133, by rfl⟩ : syracuseStep 1201511 = 1802267) B1802267
theorem B1201823 : Blo 1200417 1201823 := bstep (se 1 (by rfl) ⟨901367, by rfl⟩ : syracuseStep 1201823 = 1802735) B1802735
theorem B1201895 : Blo 1200417 1201895 := bstep (se 1 (by rfl) ⟨901421, by rfl⟩ : syracuseStep 1201895 = 1802843) B1802843
theorem B1202111 : Blo 1200417 1202111 := bstep (se 1 (by rfl) ⟨901583, by rfl⟩ : syracuseStep 1202111 = 1803167) B1803167
theorem B19494917 : Blo 1200417 19494917 := bstep (se 4 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 19494917 = 3655297) B3655297
theorem B24647885 : Blo 1200417 24647885 := bstep (se 3 (by rfl) ⟨4621478, by rfl⟩ : syracuseStep 24647885 = 9242957) B9242957
theorem B1202383 : Blo 1200417 1202383 := bstep (se 1 (by rfl) ⟨901787, by rfl⟩ : syracuseStep 1202383 = 1803575) B1803575
theorem B11114729 : Blo 1200417 11114729 := bstep (se 2 (by rfl) ⟨4168023, by rfl⟩ : syracuseStep 11114729 = 8336047) B8336047
theorem B4561231 : Blo 1200417 4561231 := bstep (se 1 (by rfl) ⟨3420923, by rfl⟩ : syracuseStep 4561231 = 6841847) B6841847
theorem B6167495 : Blo 1200417 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1801391 : Blo 1200417 1801391 := bstep (se 1 (by rfl) ⟨1351043, by rfl⟩ : syracuseStep 1801391 = 2702087) B2702087
theorem B21904627 : Blo 1200417 21904627 := bstep (se 1 (by rfl) ⟨16428470, by rfl⟩ : syracuseStep 21904627 = 32856941) B32856941
theorem B37019227 : Blo 1200417 37019227 := bstep (se 1 (by rfl) ⟨27764420, by rfl⟩ : syracuseStep 37019227 = 55528841) B55528841
theorem B1351327 : Blo 1200417 1351327 := bstep (se 1 (by rfl) ⟨1013495, by rfl⟩ : syracuseStep 1351327 = 2026991) B2026991
theorem B4054751 : Blo 1200417 4054751 := bstep (se 1 (by rfl) ⟨3041063, by rfl⟩ : syracuseStep 4054751 = 6082127) B6082127
theorem B6495967 : Blo 1200417 6495967 := bstep (se 1 (by rfl) ⟨4871975, by rfl⟩ : syracuseStep 6495967 = 9743951) B9743951
theorem B1802087 : Blo 1200417 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1802303 : Blo 1200417 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B4055453 : Blo 1200417 4055453 := bstep (se 3 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 4055453 = 1520795) B1520795
theorem B6078887 : Blo 1200417 6078887 := bstep (se 1 (by rfl) ⟨4559165, by rfl⟩ : syracuseStep 6078887 = 9118331) B9118331
theorem B1802687 : Blo 1200417 1802687 := bstep (se 1 (by rfl) ⟨1352015, by rfl⟩ : syracuseStep 1802687 = 2704031) B2704031
theorem B1352443 : Blo 1200417 1352443 := bstep (se 1 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 1352443 = 2028665) B2028665
theorem B1803131 : Blo 1200417 1803131 := bstep (se 1 (by rfl) ⟨1352348, by rfl⟩ : syracuseStep 1803131 = 2704697) B2704697
theorem B65881187 : Blo 1200417 65881187 := bstep (se 1 (by rfl) ⟨49410890, by rfl⟩ : syracuseStep 65881187 = 98821781) B98821781
theorem B34645157 : Blo 1200417 34645157 := bstep (se 4 (by rfl) ⟨3247983, by rfl⟩ : syracuseStep 34645157 = 6495967) B6495967
theorem B1803623 : Blo 1200417 1803623 := bstep (se 1 (by rfl) ⟨1352717, by rfl⟩ : syracuseStep 1803623 = 2705435) B2705435
theorem B29214341 : Blo 1200417 29214341 := bstep (se 4 (by rfl) ⟨2738844, by rfl⟩ : syracuseStep 29214341 = 5477689) B5477689
theorem B29206169 : Blo 1200417 29206169 := bstep (se 2 (by rfl) ⟨10952313, by rfl⟩ : syracuseStep 29206169 = 21904627) B21904627
theorem B12339175 : Blo 1200417 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B49358969 : Blo 1200417 49358969 := bstep (se 2 (by rfl) ⟨18509613, by rfl⟩ : syracuseStep 49358969 = 37019227) B37019227
theorem B88819847 : Blo 1200417 88819847 := bstep (se 1 (by rfl) ⟨66614885, by rfl⟩ : syracuseStep 88819847 = 133229771) B133229771
theorem B6490777 : Blo 1200417 6490777 := bstep (se 2 (by rfl) ⟨2434041, by rfl⟩ : syracuseStep 6490777 = 4868083) B4868083
theorem B5131147 : Blo 1200417 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B6081641 : Blo 1200417 6081641 := bstep (se 2 (by rfl) ⟨2280615, by rfl⟩ : syracuseStep 6081641 = 4561231) B4561231
theorem B3419273 : Blo 1200417 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B2027227 : Blo 1200417 2027227 := bstep (se 1 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 2027227 = 3040841) B3040841
theorem B12996611 : Blo 1200417 12996611 := bstep (se 1 (by rfl) ⟨9747458, by rfl⟩ : syracuseStep 12996611 = 19494917) B19494917
theorem B7409819 : Blo 1200417 7409819 := bstep (se 1 (by rfl) ⟨5557364, by rfl⟩ : syracuseStep 7409819 = 11114729) B11114729
theorem B3846311 : Blo 1200417 3846311 := bstep (se 1 (by rfl) ⟨2884733, by rfl⟩ : syracuseStep 3846311 = 5769467) B5769467
theorem B18485981 : Blo 1200417 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B1200927 : Blo 1200417 1200927 := bstep (se 1 (by rfl) ⟨900695, by rfl⟩ : syracuseStep 1200927 = 1801391) B1801391
theorem B1201391 : Blo 1200417 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B2028827 : Blo 1200417 2028827 := bstep (se 1 (by rfl) ⟨1521620, by rfl⟩ : syracuseStep 2028827 = 3043241) B3043241
theorem B38974769 : Blo 1200417 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B49346171 : Blo 1200417 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B1201919 : Blo 1200417 1201919 := bstep (se 1 (by rfl) ⟨901439, by rfl⟩ : syracuseStep 1201919 = 1802879) B1802879
theorem B7911179 : Blo 1200417 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B4052861 : Blo 1200417 4052861 := bstep (se 3 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 4052861 = 1519823) B1519823
theorem B1202175 : Blo 1200417 1202175 := bstep (se 1 (by rfl) ⟨901631, by rfl⟩ : syracuseStep 1202175 = 1803263) B1803263
theorem B4053023 : Blo 1200417 4053023 := bstep (se 1 (by rfl) ⟨3039767, by rfl⟩ : syracuseStep 4053023 = 6079535) B6079535
theorem B1202207 : Blo 1200417 1202207 := bstep (se 1 (by rfl) ⟨901655, by rfl⟩ : syracuseStep 1202207 = 1803311) B1803311
theorem B2701367 : Blo 1200417 2701367 := bstep (se 1 (by rfl) ⟨2026025, by rfl⟩ : syracuseStep 2701367 = 4052051) B4052051
theorem B1202239 : Blo 1200417 1202239 := bstep (se 1 (by rfl) ⟨901679, by rfl⟩ : syracuseStep 1202239 = 1803359) B1803359
theorem B1923239 : Blo 1200417 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B4053455 : Blo 1200417 4053455 := bstep (se 1 (by rfl) ⟨3040091, by rfl⟩ : syracuseStep 4053455 = 6080183) B6080183
theorem B16431923 : Blo 1200417 16431923 := bstep (se 1 (by rfl) ⟨12323942, by rfl⟩ : syracuseStep 16431923 = 24647885) B24647885
theorem B4053887 : Blo 1200417 4053887 := bstep (se 1 (by rfl) ⟨3040415, by rfl⟩ : syracuseStep 4053887 = 6080831) B6080831
theorem B1924091 : Blo 1200417 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B4054319 : Blo 1200417 4054319 := bstep (se 1 (by rfl) ⟨3040739, by rfl⟩ : syracuseStep 4054319 = 6081479) B6081479
theorem B4111663 : Blo 1200417 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B1351039 : Blo 1200417 1351039 := bstep (se 1 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 1351039 = 2026559) B2026559
theorem B1801769 : Blo 1200417 1801769 := bstep (se 2 (by rfl) ⟨675663, by rfl⟩ : syracuseStep 1801769 = 1351327) B1351327
theorem B2703167 : Blo 1200417 2703167 := bstep (se 1 (by rfl) ⟨2027375, by rfl⟩ : syracuseStep 2703167 = 4054751) B4054751
theorem B1351615 : Blo 1200417 1351615 := bstep (se 1 (by rfl) ⟨1013711, by rfl⟩ : syracuseStep 1351615 = 2027423) B2027423
theorem B4939879 : Blo 1200417 4939879 := bstep (se 1 (by rfl) ⟨3704909, by rfl⟩ : syracuseStep 4939879 = 7409819) B7409819
theorem B2564207 : Blo 1200417 2564207 := bstep (se 1 (by rfl) ⟨1923155, by rfl⟩ : syracuseStep 2564207 = 3846311) B3846311
theorem B2703635 : Blo 1200417 2703635 := bstep (se 1 (by rfl) ⟨2027726, by rfl⟩ : syracuseStep 2703635 = 4055453) B4055453
theorem B1352551 : Blo 1200417 1352551 := bstep (se 1 (by rfl) ⟨1014413, by rfl⟩ : syracuseStep 1352551 = 2028827) B2028827
theorem B1803257 : Blo 1200417 1803257 := bstep (se 2 (by rfl) ⟨676221, by rfl⟩ : syracuseStep 1803257 = 1352443) B1352443
theorem B6841529 : Blo 1200417 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B59213231 : Blo 1200417 59213231 := bstep (se 1 (by rfl) ⟨44409923, by rfl⟩ : syracuseStep 59213231 = 88819847) B88819847
theorem B5482217 : Blo 1200417 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B10954615 : Blo 1200417 10954615 := bstep (se 1 (by rfl) ⟨8215961, by rfl⟩ : syracuseStep 10954615 = 16431923) B16431923
theorem B2279515 : Blo 1200417 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B16452233 : Blo 1200417 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B12323987 : Blo 1200417 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B43920791 : Blo 1200417 43920791 := bstep (se 1 (by rfl) ⟨32940593, by rfl⟩ : syracuseStep 43920791 = 65881187) B65881187
theorem B23096771 : Blo 1200417 23096771 := bstep (se 1 (by rfl) ⟨17322578, by rfl⟩ : syracuseStep 23096771 = 34645157) B34645157
theorem B8654369 : Blo 1200417 8654369 := bstep (se 2 (by rfl) ⟨3245388, by rfl⟩ : syracuseStep 8654369 = 6490777) B6490777
theorem B19476227 : Blo 1200417 19476227 := bstep (se 1 (by rfl) ⟨14607170, by rfl⟩ : syracuseStep 19476227 = 29214341) B29214341
theorem B1282159 : Blo 1200417 1282159 := bstep (se 1 (by rfl) ⟨961619, by rfl⟩ : syracuseStep 1282159 = 1923239) B1923239
theorem B1282727 : Blo 1200417 1282727 := bstep (se 1 (by rfl) ⟨962045, by rfl⟩ : syracuseStep 1282727 = 1924091) B1924091
theorem B1201179 : Blo 1200417 1201179 := bstep (se 1 (by rfl) ⟨900884, by rfl⟩ : syracuseStep 1201179 = 1801769) B1801769
theorem B8664407 : Blo 1200417 8664407 := bstep (se 1 (by rfl) ⟨6498305, by rfl⟩ : syracuseStep 8664407 = 12996611) B12996611
theorem B1201535 : Blo 1200417 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B4052591 : Blo 1200417 4052591 := bstep (se 1 (by rfl) ⟨3039443, by rfl⟩ : syracuseStep 4052591 = 6078887) B6078887
theorem B1201791 : Blo 1200417 1201791 := bstep (se 1 (by rfl) ⟨901343, by rfl⟩ : syracuseStep 1201791 = 1802687) B1802687
theorem B1202087 : Blo 1200417 1202087 := bstep (se 1 (by rfl) ⟨901565, by rfl⟩ : syracuseStep 1202087 = 1803131) B1803131
theorem B25983179 : Blo 1200417 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B1202415 : Blo 1200417 1202415 := bstep (se 1 (by rfl) ⟨901811, by rfl⟩ : syracuseStep 1202415 = 1803623) B1803623
theorem B32897447 : Blo 1200417 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B19470779 : Blo 1200417 19470779 := bstep (se 1 (by rfl) ⟨14603084, by rfl⟩ : syracuseStep 19470779 = 29206169) B29206169
theorem B5274119 : Blo 1200417 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B2701907 : Blo 1200417 2701907 := bstep (se 1 (by rfl) ⟨2026430, by rfl⟩ : syracuseStep 2701907 = 4052861) B4052861
theorem B2702015 : Blo 1200417 2702015 := bstep (se 1 (by rfl) ⟨2026511, by rfl⟩ : syracuseStep 2702015 = 4053023) B4053023
theorem B1800911 : Blo 1200417 1800911 := bstep (se 1 (by rfl) ⟨1350683, by rfl⟩ : syracuseStep 1800911 = 2701367) B2701367
theorem B32905979 : Blo 1200417 32905979 := bstep (se 1 (by rfl) ⟨24679484, by rfl⟩ : syracuseStep 32905979 = 49358969) B49358969
theorem B2702303 : Blo 1200417 2702303 := bstep (se 1 (by rfl) ⟨2026727, by rfl⟩ : syracuseStep 2702303 = 4053455) B4053455
theorem B1801385 : Blo 1200417 1801385 := bstep (se 2 (by rfl) ⟨675519, by rfl⟩ : syracuseStep 1801385 = 1351039) B1351039
theorem B2702591 : Blo 1200417 2702591 := bstep (se 1 (by rfl) ⟨2026943, by rfl⟩ : syracuseStep 2702591 = 4053887) B4053887
theorem B4054427 : Blo 1200417 4054427 := bstep (se 1 (by rfl) ⟨3040820, by rfl⟩ : syracuseStep 4054427 = 6081641) B6081641
theorem B2702879 : Blo 1200417 2702879 := bstep (se 1 (by rfl) ⟨2027159, by rfl⟩ : syracuseStep 2702879 = 4054319) B4054319
theorem B2702969 : Blo 1200417 2702969 := bstep (se 2 (by rfl) ⟨1013613, by rfl⟩ : syracuseStep 2702969 = 2027227) B2027227
theorem B1802111 : Blo 1200417 1802111 := bstep (se 1 (by rfl) ⟨1351583, by rfl⟩ : syracuseStep 1802111 = 2703167) B2703167
theorem B1802153 : Blo 1200417 1802153 := bstep (se 2 (by rfl) ⟨675807, by rfl⟩ : syracuseStep 1802153 = 1351615) B1351615
theorem B3039353 : Blo 1200417 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B6586505 : Blo 1200417 6586505 := bstep (se 2 (by rfl) ⟨2469939, by rfl⟩ : syracuseStep 6586505 = 4939879) B4939879
theorem B1802423 : Blo 1200417 1802423 := bstep (se 1 (by rfl) ⟨1351817, by rfl⟩ : syracuseStep 1802423 = 2703635) B2703635
theorem B5776271 : Blo 1200417 5776271 := bstep (se 1 (by rfl) ⟨4332203, by rfl⟩ : syracuseStep 5776271 = 8664407) B8664407
theorem B1803401 : Blo 1200417 1803401 := bstep (se 2 (by rfl) ⟨676275, by rfl⟩ : syracuseStep 1803401 = 1352551) B1352551
theorem B3654811 : Blo 1200417 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B23078317 : Blo 1200417 23078317 := bstep (se 3 (by rfl) ⟨4327184, by rfl⟩ : syracuseStep 23078317 = 8654369) B8654369
theorem B21931631 : Blo 1200417 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B29280527 : Blo 1200417 29280527 := bstep (se 1 (by rfl) ⟨21960395, by rfl⟩ : syracuseStep 29280527 = 43920791) B43920791
theorem B17322119 : Blo 1200417 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B12980519 : Blo 1200417 12980519 := bstep (se 1 (by rfl) ⟨9735389, by rfl⟩ : syracuseStep 12980519 = 19470779) B19470779
theorem B3420605 : Blo 1200417 3420605 := bstep (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) B1282727
theorem B1200607 : Blo 1200417 1200607 := bstep (se 1 (by rfl) ⟨900455, by rfl⟩ : syracuseStep 1200607 = 1800911) B1800911
theorem B1200923 : Blo 1200417 1200923 := bstep (se 1 (by rfl) ⟨900692, by rfl⟩ : syracuseStep 1200923 = 1801385) B1801385
theorem B15397847 : Blo 1200417 15397847 := bstep (se 1 (by rfl) ⟨11548385, by rfl⟩ : syracuseStep 15397847 = 23096771) B23096771
theorem B1201407 : Blo 1200417 1201407 := bstep (se 1 (by rfl) ⟨901055, by rfl⟩ : syracuseStep 1201407 = 1802111) B1802111
theorem B1201435 : Blo 1200417 1201435 := bstep (se 1 (by rfl) ⟨901076, by rfl⟩ : syracuseStep 1201435 = 1802153) B1802153
theorem B1709471 : Blo 1200417 1709471 := bstep (se 1 (by rfl) ⟨1282103, by rfl⟩ : syracuseStep 1709471 = 2564207) B2564207
theorem B6838181 : Blo 1200417 6838181 := bstep (se 4 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 6838181 = 1282159) B1282159
theorem B1202171 : Blo 1200417 1202171 := bstep (se 1 (by rfl) ⟨901628, by rfl⟩ : syracuseStep 1202171 = 1803257) B1803257
theorem B4561019 : Blo 1200417 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B39475487 : Blo 1200417 39475487 := bstep (se 1 (by rfl) ⟨29606615, by rfl⟩ : syracuseStep 39475487 = 59213231) B59213231
theorem B2701727 : Blo 1200417 2701727 := bstep (se 1 (by rfl) ⟨2026295, by rfl⟩ : syracuseStep 2701727 = 4052591) B4052591
theorem B14064317 : Blo 1200417 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B1801271 : Blo 1200417 1801271 := bstep (se 1 (by rfl) ⟨1350953, by rfl⟩ : syracuseStep 1801271 = 2701907) B2701907
theorem B10968155 : Blo 1200417 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B1801343 : Blo 1200417 1801343 := bstep (se 1 (by rfl) ⟨1351007, by rfl⟩ : syracuseStep 1801343 = 2702015) B2702015
theorem B21937319 : Blo 1200417 21937319 := bstep (se 1 (by rfl) ⟨16452989, by rfl⟩ : syracuseStep 21937319 = 32905979) B32905979
theorem B1801535 : Blo 1200417 1801535 := bstep (se 1 (by rfl) ⟨1351151, by rfl⟩ : syracuseStep 1801535 = 2702303) B2702303
theorem B8215991 : Blo 1200417 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B1801727 : Blo 1200417 1801727 := bstep (se 1 (by rfl) ⟨1351295, by rfl⟩ : syracuseStep 1801727 = 2702591) B2702591
theorem B2702951 : Blo 1200417 2702951 := bstep (se 1 (by rfl) ⟨2027213, by rfl⟩ : syracuseStep 2702951 = 4054427) B4054427
theorem B1801919 : Blo 1200417 1801919 := bstep (se 1 (by rfl) ⟨1351439, by rfl⟩ : syracuseStep 1801919 = 2702879) B2702879
theorem B1801979 : Blo 1200417 1801979 := bstep (se 1 (by rfl) ⟨1351484, by rfl⟩ : syracuseStep 1801979 = 2702969) B2702969
theorem B14606153 : Blo 1200417 14606153 := bstep (se 2 (by rfl) ⟨5477307, by rfl⟩ : syracuseStep 14606153 = 10954615) B10954615
theorem B12984151 : Blo 1200417 12984151 := bstep (se 1 (by rfl) ⟨9738113, by rfl⟩ : syracuseStep 12984151 = 19476227) B19476227
theorem B4391003 : Blo 1200417 4391003 := bstep (se 1 (by rfl) ⟨3293252, by rfl⟩ : syracuseStep 4391003 = 6586505) B6586505
theorem B3850847 : Blo 1200417 3850847 := bstep (se 1 (by rfl) ⟨2888135, by rfl⟩ : syracuseStep 3850847 = 5776271) B5776271
theorem B10265231 : Blo 1200417 10265231 := bstep (se 1 (by rfl) ⟨7698923, by rfl⟩ : syracuseStep 10265231 = 15397847) B15397847
theorem B3040679 : Blo 1200417 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B30771089 : Blo 1200417 30771089 := bstep (se 2 (by rfl) ⟨11539158, by rfl⟩ : syracuseStep 30771089 = 23078317) B23078317
theorem B14624879 : Blo 1200417 14624879 := bstep (se 1 (by rfl) ⟨10968659, by rfl⟩ : syracuseStep 14624879 = 21937319) B21937319
theorem B17312201 : Blo 1200417 17312201 := bstep (se 2 (by rfl) ⟨6492075, by rfl⟩ : syracuseStep 17312201 = 12984151) B12984151
theorem B2026235 : Blo 1200417 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B8653679 : Blo 1200417 8653679 := bstep (se 1 (by rfl) ⟨6490259, by rfl⟩ : syracuseStep 8653679 = 12980519) B12980519
theorem B2280403 : Blo 1200417 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B4558589 : Blo 1200417 4558589 := bstep (se 3 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 4558589 = 1709471) B1709471
theorem B4558787 : Blo 1200417 4558787 := bstep (se 1 (by rfl) ⟨3419090, by rfl⟩ : syracuseStep 4558787 = 6838181) B6838181
theorem B26316991 : Blo 1200417 26316991 := bstep (se 1 (by rfl) ⟨19737743, by rfl⟩ : syracuseStep 26316991 = 39475487) B39475487
theorem B9376211 : Blo 1200417 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B1200847 : Blo 1200417 1200847 := bstep (se 1 (by rfl) ⟨900635, by rfl⟩ : syracuseStep 1200847 = 1801271) B1801271
theorem B7312103 : Blo 1200417 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B1200895 : Blo 1200417 1200895 := bstep (se 1 (by rfl) ⟨900671, by rfl⟩ : syracuseStep 1200895 = 1801343) B1801343
theorem B1201023 : Blo 1200417 1201023 := bstep (se 1 (by rfl) ⟨900767, by rfl⟩ : syracuseStep 1201023 = 1801535) B1801535
theorem B5477327 : Blo 1200417 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B1201151 : Blo 1200417 1201151 := bstep (se 1 (by rfl) ⟨900863, by rfl⟩ : syracuseStep 1201151 = 1801727) B1801727
theorem B1201279 : Blo 1200417 1201279 := bstep (se 1 (by rfl) ⟨900959, by rfl⟩ : syracuseStep 1201279 = 1801919) B1801919
theorem B1201319 : Blo 1200417 1201319 := bstep (se 1 (by rfl) ⟨900989, by rfl⟩ : syracuseStep 1201319 = 1801979) B1801979
theorem B9737435 : Blo 1200417 9737435 := bstep (se 1 (by rfl) ⟨7303076, by rfl⟩ : syracuseStep 9737435 = 14606153) B14606153
theorem B11548079 : Blo 1200417 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B1201615 : Blo 1200417 1201615 := bstep (se 1 (by rfl) ⟨901211, by rfl⟩ : syracuseStep 1201615 = 1802423) B1802423
theorem B1202267 : Blo 1200417 1202267 := bstep (se 1 (by rfl) ⟨901700, by rfl⟩ : syracuseStep 1202267 = 1803401) B1803401
theorem B14621087 : Blo 1200417 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B19520351 : Blo 1200417 19520351 := bstep (se 1 (by rfl) ⟨14640263, by rfl⟩ : syracuseStep 19520351 = 29280527) B29280527
theorem B4873081 : Blo 1200417 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1801151 : Blo 1200417 1801151 := bstep (se 1 (by rfl) ⟨1350863, by rfl⟩ : syracuseStep 1801151 = 2701727) B2701727
theorem B1801967 : Blo 1200417 1801967 := bstep (se 1 (by rfl) ⟨1351475, by rfl⟩ : syracuseStep 1801967 = 2702951) B2702951
theorem B6250807 : Blo 1200417 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B4874735 : Blo 1200417 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B6497441 : Blo 1200417 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B20514059 : Blo 1200417 20514059 := bstep (se 1 (by rfl) ⟨15385544, by rfl⟩ : syracuseStep 20514059 = 30771089) B30771089
theorem B3040537 : Blo 1200417 3040537 := bstep (se 2 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 3040537 = 2280403) B2280403
theorem B5769119 : Blo 1200417 5769119 := bstep (se 1 (by rfl) ⟨4326839, by rfl⟩ : syracuseStep 5769119 = 8653679) B8653679
theorem B2927335 : Blo 1200417 2927335 := bstep (se 1 (by rfl) ⟨2195501, by rfl⟩ : syracuseStep 2927335 = 4391003) B4391003
theorem B35089321 : Blo 1200417 35089321 := bstep (se 2 (by rfl) ⟨13158495, by rfl⟩ : syracuseStep 35089321 = 26316991) B26316991
theorem B2567231 : Blo 1200417 2567231 := bstep (se 1 (by rfl) ⟨1925423, by rfl⟩ : syracuseStep 2567231 = 3850847) B3850847
theorem B6843487 : Blo 1200417 6843487 := bstep (se 1 (by rfl) ⟨5132615, by rfl⟩ : syracuseStep 6843487 = 10265231) B10265231
theorem B2027119 : Blo 1200417 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B13013567 : Blo 1200417 13013567 := bstep (se 1 (by rfl) ⟨9760175, by rfl⟩ : syracuseStep 13013567 = 19520351) B19520351
theorem B1200767 : Blo 1200417 1200767 := bstep (se 1 (by rfl) ⟨900575, by rfl⟩ : syracuseStep 1200767 = 1801151) B1801151
theorem B1201311 : Blo 1200417 1201311 := bstep (se 1 (by rfl) ⟨900983, by rfl⟩ : syracuseStep 1201311 = 1801967) B1801967
theorem B38999677 : Blo 1200417 38999677 := bstep (se 3 (by rfl) ⟨7312439, by rfl⟩ : syracuseStep 38999677 = 14624879) B14624879
theorem B25966493 : Blo 1200417 25966493 := bstep (se 3 (by rfl) ⟨4868717, by rfl⟩ : syracuseStep 25966493 = 9737435) B9737435
theorem B3651551 : Blo 1200417 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B7698719 : Blo 1200417 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B9747391 : Blo 1200417 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B11541467 : Blo 1200417 11541467 := bstep (se 1 (by rfl) ⟨8656100, by rfl⟩ : syracuseStep 11541467 = 17312201) B17312201
theorem B1350823 : Blo 1200417 1350823 := bstep (se 1 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 1350823 = 2026235) B2026235
theorem B3039059 : Blo 1200417 3039059 := bstep (se 1 (by rfl) ⟨2279294, by rfl⟩ : syracuseStep 3039059 = 4558589) B4558589
theorem B3039191 : Blo 1200417 3039191 := bstep (se 1 (by rfl) ⟨2279393, by rfl⟩ : syracuseStep 3039191 = 4558787) B4558787
theorem B8675711 : Blo 1200417 8675711 := bstep (se 1 (by rfl) ⟨6506783, by rfl⟩ : syracuseStep 8675711 = 13013567) B13013567
theorem B46785761 : Blo 1200417 46785761 := bstep (se 2 (by rfl) ⟨17544660, by rfl⟩ : syracuseStep 46785761 = 35089321) B35089321
theorem B17310995 : Blo 1200417 17310995 := bstep (se 1 (by rfl) ⟨12983246, by rfl⟩ : syracuseStep 17310995 = 25966493) B25966493
theorem B2434367 : Blo 1200417 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B7694311 : Blo 1200417 7694311 := bstep (se 1 (by rfl) ⟨5770733, by rfl⟩ : syracuseStep 7694311 = 11541467) B11541467
theorem B2026039 : Blo 1200417 2026039 := bstep (se 1 (by rfl) ⟨1519529, by rfl⟩ : syracuseStep 2026039 = 3039059) B3039059
theorem B2026127 : Blo 1200417 2026127 := bstep (se 1 (by rfl) ⟨1519595, by rfl⟩ : syracuseStep 2026127 = 3039191) B3039191
theorem B8334409 : Blo 1200417 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B13676039 : Blo 1200417 13676039 := bstep (se 1 (by rfl) ⟨10257029, by rfl⟩ : syracuseStep 13676039 = 20514059) B20514059
theorem B3903113 : Blo 1200417 3903113 := bstep (se 2 (by rfl) ⟨1463667, by rfl⟩ : syracuseStep 3903113 = 2927335) B2927335
theorem B12996521 : Blo 1200417 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B3846079 : Blo 1200417 3846079 := bstep (se 1 (by rfl) ⟨2884559, by rfl⟩ : syracuseStep 3846079 = 5769119) B5769119
theorem B5132479 : Blo 1200417 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B51999569 : Blo 1200417 51999569 := bstep (se 2 (by rfl) ⟨19499838, by rfl⟩ : syracuseStep 51999569 = 38999677) B38999677
theorem B3249823 : Blo 1200417 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B4331627 : Blo 1200417 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B9124649 : Blo 1200417 9124649 := bstep (se 2 (by rfl) ⟨3421743, by rfl⟩ : syracuseStep 9124649 = 6843487) B6843487
theorem B1801097 : Blo 1200417 1801097 := bstep (se 2 (by rfl) ⟨675411, by rfl⟩ : syracuseStep 1801097 = 1350823) B1350823
theorem B4054049 : Blo 1200417 4054049 := bstep (se 2 (by rfl) ⟨1520268, by rfl⟩ : syracuseStep 4054049 = 3040537) B3040537
theorem B1711487 : Blo 1200417 1711487 := bstep (se 1 (by rfl) ⟨1283615, by rfl⟩ : syracuseStep 1711487 = 2567231) B2567231
theorem B2702825 : Blo 1200417 2702825 := bstep (se 2 (by rfl) ⟨1013559, by rfl⟩ : syracuseStep 2702825 = 2027119) B2027119
theorem B5783807 : Blo 1200417 5783807 := bstep (se 1 (by rfl) ⟨4337855, by rfl⟩ : syracuseStep 5783807 = 8675711) B8675711
theorem B1622911 : Blo 1200417 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B4563965 : Blo 1200417 4563965 := bstep (se 3 (by rfl) ⟨855743, by rfl⟩ : syracuseStep 4563965 = 1711487) B1711487
theorem B10259081 : Blo 1200417 10259081 := bstep (se 2 (by rfl) ⟨3847155, by rfl⟩ : syracuseStep 10259081 = 7694311) B7694311
theorem B6843305 : Blo 1200417 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B31190507 : Blo 1200417 31190507 := bstep (se 1 (by rfl) ⟨23392880, by rfl⟩ : syracuseStep 31190507 = 46785761) B46785761
theorem B2887751 : Blo 1200417 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B11112545 : Blo 1200417 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B10408301 : Blo 1200417 10408301 := bstep (se 3 (by rfl) ⟨1951556, by rfl⟩ : syracuseStep 10408301 = 3903113) B3903113
theorem B6083099 : Blo 1200417 6083099 := bstep (se 1 (by rfl) ⟨4562324, by rfl⟩ : syracuseStep 6083099 = 9124649) B9124649
theorem B1200731 : Blo 1200417 1200731 := bstep (se 1 (by rfl) ⟨900548, by rfl⟩ : syracuseStep 1200731 = 1801097) B1801097
theorem B8664347 : Blo 1200417 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B34666379 : Blo 1200417 34666379 := bstep (se 1 (by rfl) ⟨25999784, by rfl⟩ : syracuseStep 34666379 = 51999569) B51999569
theorem B2701385 : Blo 1200417 2701385 := bstep (se 2 (by rfl) ⟨1013019, by rfl⟩ : syracuseStep 2701385 = 2026039) B2026039
theorem B11540663 : Blo 1200417 11540663 := bstep (se 1 (by rfl) ⟨8655497, by rfl⟩ : syracuseStep 11540663 = 17310995) B17310995
theorem B1350751 : Blo 1200417 1350751 := bstep (se 1 (by rfl) ⟨1013063, by rfl⟩ : syracuseStep 1350751 = 2026127) B2026127
theorem B2702699 : Blo 1200417 2702699 := bstep (se 1 (by rfl) ⟨2027024, by rfl⟩ : syracuseStep 2702699 = 4054049) B4054049
theorem B4333097 : Blo 1200417 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B1801883 : Blo 1200417 1801883 := bstep (se 1 (by rfl) ⟨1351412, by rfl⟩ : syracuseStep 1801883 = 2702825) B2702825
theorem B9117359 : Blo 1200417 9117359 := bstep (se 1 (by rfl) ⟨6838019, by rfl⟩ : syracuseStep 9117359 = 13676039) B13676039
theorem B5128105 : Blo 1200417 5128105 := bstep (se 2 (by rfl) ⟨1923039, by rfl⟩ : syracuseStep 5128105 = 3846079) B3846079
theorem B7700669 : Blo 1200417 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B6938867 : Blo 1200417 6938867 := bstep (se 1 (by rfl) ⟨5204150, by rfl⟩ : syracuseStep 6938867 = 10408301) B10408301
theorem B4055399 : Blo 1200417 4055399 := bstep (se 1 (by rfl) ⟨3041549, by rfl⟩ : syracuseStep 4055399 = 6083099) B6083099
theorem B2163881 : Blo 1200417 2163881 := bstep (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) B1622911
theorem B23110919 : Blo 1200417 23110919 := bstep (se 1 (by rfl) ⟨17333189, by rfl⟩ : syracuseStep 23110919 = 34666379) B34666379
theorem B7693775 : Blo 1200417 7693775 := bstep (se 1 (by rfl) ⟨5770331, by rfl⟩ : syracuseStep 7693775 = 11540663) B11540663
theorem B20793671 : Blo 1200417 20793671 := bstep (se 1 (by rfl) ⟨15595253, by rfl⟩ : syracuseStep 20793671 = 31190507) B31190507
theorem B7408363 : Blo 1200417 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B3042643 : Blo 1200417 3042643 := bstep (se 1 (by rfl) ⟨2281982, by rfl⟩ : syracuseStep 3042643 = 4563965) B4563965
theorem B23104925 : Blo 1200417 23104925 := bstep (se 3 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 23104925 = 8664347) B8664347
theorem B2888731 : Blo 1200417 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B1201255 : Blo 1200417 1201255 := bstep (se 1 (by rfl) ⟨900941, by rfl⟩ : syracuseStep 1201255 = 1801883) B1801883
theorem B6837473 : Blo 1200417 6837473 := bstep (se 2 (by rfl) ⟨2564052, by rfl⟩ : syracuseStep 6837473 = 5128105) B5128105
theorem B3855871 : Blo 1200417 3855871 := bstep (se 1 (by rfl) ⟨2891903, by rfl⟩ : syracuseStep 3855871 = 5783807) B5783807
theorem B1800923 : Blo 1200417 1800923 := bstep (se 1 (by rfl) ⟨1350692, by rfl⟩ : syracuseStep 1800923 = 2701385) B2701385
theorem B1801001 : Blo 1200417 1801001 := bstep (se 2 (by rfl) ⟨675375, by rfl⟩ : syracuseStep 1801001 = 1350751) B1350751
theorem B6839387 : Blo 1200417 6839387 := bstep (se 1 (by rfl) ⟨5129540, by rfl⟩ : syracuseStep 6839387 = 10259081) B10259081
theorem B4562203 : Blo 1200417 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B1801799 : Blo 1200417 1801799 := bstep (se 1 (by rfl) ⟨1351349, by rfl⟩ : syracuseStep 1801799 = 2702699) B2702699
theorem B6078239 : Blo 1200417 6078239 := bstep (se 1 (by rfl) ⟨4558679, by rfl⟩ : syracuseStep 6078239 = 9117359) B9117359
theorem B2703599 : Blo 1200417 2703599 := bstep (se 1 (by rfl) ⟨2027699, by rfl⟩ : syracuseStep 2703599 = 4055399) B4055399
theorem B5129183 : Blo 1200417 5129183 := bstep (se 1 (by rfl) ⟨3846887, by rfl⟩ : syracuseStep 5129183 = 7693775) B7693775
theorem B3851641 : Blo 1200417 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B13862447 : Blo 1200417 13862447 := bstep (se 1 (by rfl) ⟨10396835, by rfl⟩ : syracuseStep 13862447 = 20793671) B20793671
theorem B4056857 : Blo 1200417 4056857 := bstep (se 2 (by rfl) ⟨1521321, by rfl⟩ : syracuseStep 4056857 = 3042643) B3042643
theorem B15403283 : Blo 1200417 15403283 := bstep (se 1 (by rfl) ⟨11552462, by rfl⟩ : syracuseStep 15403283 = 23104925) B23104925
theorem B5770349 : Blo 1200417 5770349 := bstep (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) B2163881
theorem B4558315 : Blo 1200417 4558315 := bstep (se 1 (by rfl) ⟨3418736, by rfl⟩ : syracuseStep 4558315 = 6837473) B6837473
theorem B6082937 : Blo 1200417 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B1200615 : Blo 1200417 1200615 := bstep (se 1 (by rfl) ⟨900461, by rfl⟩ : syracuseStep 1200615 = 1800923) B1800923
theorem B1200667 : Blo 1200417 1200667 := bstep (se 1 (by rfl) ⟨900500, by rfl⟩ : syracuseStep 1200667 = 1801001) B1801001
theorem B5141161 : Blo 1200417 5141161 := bstep (se 2 (by rfl) ⟨1927935, by rfl⟩ : syracuseStep 5141161 = 3855871) B3855871
theorem B4559591 : Blo 1200417 4559591 := bstep (se 1 (by rfl) ⟨3419693, by rfl⟩ : syracuseStep 4559591 = 6839387) B6839387
theorem B1201199 : Blo 1200417 1201199 := bstep (se 1 (by rfl) ⟨900899, by rfl⟩ : syracuseStep 1201199 = 1801799) B1801799
theorem B4052159 : Blo 1200417 4052159 := bstep (se 1 (by rfl) ⟨3039119, by rfl⟩ : syracuseStep 4052159 = 6078239) B6078239
theorem B5133779 : Blo 1200417 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B18503645 : Blo 1200417 18503645 := bstep (se 3 (by rfl) ⟨3469433, by rfl⟩ : syracuseStep 18503645 = 6938867) B6938867
theorem B15407279 : Blo 1200417 15407279 := bstep (se 1 (by rfl) ⟨11555459, by rfl⟩ : syracuseStep 15407279 = 23110919) B23110919
theorem B9877817 : Blo 1200417 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B1802399 : Blo 1200417 1802399 := bstep (se 1 (by rfl) ⟨1351799, by rfl⟩ : syracuseStep 1802399 = 2703599) B2703599
theorem B4055291 : Blo 1200417 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B3039727 : Blo 1200417 3039727 := bstep (se 1 (by rfl) ⟨2279795, by rfl⟩ : syracuseStep 3039727 = 4559591) B4559591
theorem B9241631 : Blo 1200417 9241631 := bstep (se 1 (by rfl) ⟨6931223, by rfl⟩ : syracuseStep 9241631 = 13862447) B13862447
theorem B2704571 : Blo 1200417 2704571 := bstep (se 1 (by rfl) ⟨2028428, by rfl⟩ : syracuseStep 2704571 = 4056857) B4056857
theorem B49343053 : Blo 1200417 49343053 := bstep (se 3 (by rfl) ⟨9251822, by rfl⟩ : syracuseStep 49343053 = 18503645) B18503645
theorem B3419455 : Blo 1200417 3419455 := bstep (se 1 (by rfl) ⟨2564591, by rfl⟩ : syracuseStep 3419455 = 5129183) B5129183
theorem B10268855 : Blo 1200417 10268855 := bstep (se 1 (by rfl) ⟨7701641, by rfl⟩ : syracuseStep 10268855 = 15403283) B15403283
theorem B3846899 : Blo 1200417 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B2701439 : Blo 1200417 2701439 := bstep (se 1 (by rfl) ⟨2026079, by rfl⟩ : syracuseStep 2701439 = 4052159) B4052159
theorem B6854881 : Blo 1200417 6854881 := bstep (se 2 (by rfl) ⟨2570580, by rfl⟩ : syracuseStep 6854881 = 5141161) B5141161
theorem B3422519 : Blo 1200417 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B10271519 : Blo 1200417 10271519 := bstep (se 1 (by rfl) ⟨7703639, by rfl⟩ : syracuseStep 10271519 = 15407279) B15407279
theorem B6585211 : Blo 1200417 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B5135521 : Blo 1200417 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B6077753 : Blo 1200417 6077753 := bstep (se 2 (by rfl) ⟨2279157, by rfl⟩ : syracuseStep 6077753 = 4558315) B4558315
theorem B2703527 : Blo 1200417 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B6161087 : Blo 1200417 6161087 := bstep (se 1 (by rfl) ⟨4620815, by rfl⟩ : syracuseStep 6161087 = 9241631) B9241631
theorem B65790737 : Blo 1200417 65790737 := bstep (se 2 (by rfl) ⟨24671526, by rfl⟩ : syracuseStep 65790737 = 49343053) B49343053
theorem B1803047 : Blo 1200417 1803047 := bstep (se 1 (by rfl) ⟨1352285, by rfl⟩ : syracuseStep 1803047 = 2704571) B2704571
theorem B10258397 : Blo 1200417 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B2281679 : Blo 1200417 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B4559273 : Blo 1200417 4559273 := bstep (se 2 (by rfl) ⟨1709727, by rfl⟩ : syracuseStep 4559273 = 3419455) B3419455
theorem B4051835 : Blo 1200417 4051835 := bstep (se 1 (by rfl) ⟨3038876, by rfl⟩ : syracuseStep 4051835 = 6077753) B6077753
theorem B1201599 : Blo 1200417 1201599 := bstep (se 1 (by rfl) ⟨901199, by rfl⟩ : syracuseStep 1201599 = 1802399) B1802399
theorem B6845903 : Blo 1200417 6845903 := bstep (se 1 (by rfl) ⟨5134427, by rfl⟩ : syracuseStep 6845903 = 10268855) B10268855
theorem B9139841 : Blo 1200417 9139841 := bstep (se 2 (by rfl) ⟨3427440, by rfl⟩ : syracuseStep 9139841 = 6854881) B6854881
theorem B4052969 : Blo 1200417 4052969 := bstep (se 2 (by rfl) ⟨1519863, by rfl⟩ : syracuseStep 4052969 = 3039727) B3039727
theorem B8780281 : Blo 1200417 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B1800959 : Blo 1200417 1800959 := bstep (se 1 (by rfl) ⟨1350719, by rfl⟩ : syracuseStep 1800959 = 2701439) B2701439
theorem B6847361 : Blo 1200417 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B6847679 : Blo 1200417 6847679 := bstep (se 1 (by rfl) ⟨5135759, by rfl⟩ : syracuseStep 6847679 = 10271519) B10271519
theorem B1802351 : Blo 1200417 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B3039515 : Blo 1200417 3039515 := bstep (se 1 (by rfl) ⟨2279636, by rfl⟩ : syracuseStep 3039515 = 4559273) B4559273
theorem B43860491 : Blo 1200417 43860491 := bstep (se 1 (by rfl) ⟨32895368, by rfl⟩ : syracuseStep 43860491 = 65790737) B65790737
theorem B4563935 : Blo 1200417 4563935 := bstep (se 1 (by rfl) ⟨3422951, by rfl⟩ : syracuseStep 4563935 = 6845903) B6845903
theorem B4564907 : Blo 1200417 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B4565119 : Blo 1200417 4565119 := bstep (se 1 (by rfl) ⟨3423839, by rfl⟩ : syracuseStep 4565119 = 6847679) B6847679
theorem B46828165 : Blo 1200417 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B4107391 : Blo 1200417 4107391 := bstep (se 1 (by rfl) ⟨3080543, by rfl⟩ : syracuseStep 4107391 = 6161087) B6161087
theorem B1200639 : Blo 1200417 1200639 := bstep (se 1 (by rfl) ⟨900479, by rfl⟩ : syracuseStep 1200639 = 1800959) B1800959
theorem B1521119 : Blo 1200417 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B1202031 : Blo 1200417 1202031 := bstep (se 1 (by rfl) ⟨901523, by rfl⟩ : syracuseStep 1202031 = 1803047) B1803047
theorem B2701223 : Blo 1200417 2701223 := bstep (se 1 (by rfl) ⟨2025917, by rfl⟩ : syracuseStep 2701223 = 4051835) B4051835
theorem B6093227 : Blo 1200417 6093227 := bstep (se 1 (by rfl) ⟨4569920, by rfl⟩ : syracuseStep 6093227 = 9139841) B9139841
theorem B6838931 : Blo 1200417 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B2701979 : Blo 1200417 2701979 := bstep (se 1 (by rfl) ⟨2026484, by rfl⟩ : syracuseStep 2701979 = 4052969) B4052969
theorem B6086825 : Blo 1200417 6086825 := bstep (se 2 (by rfl) ⟨2282559, by rfl⟩ : syracuseStep 6086825 = 4565119) B4565119
theorem B4056317 : Blo 1200417 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B87624341 : Blo 1200417 87624341 := bstep (se 6 (by rfl) ⟨2053695, by rfl⟩ : syracuseStep 87624341 = 4107391) B4107391
theorem B2026343 : Blo 1200417 2026343 := bstep (se 1 (by rfl) ⟨1519757, by rfl⟩ : syracuseStep 2026343 = 3039515) B3039515
theorem B29240327 : Blo 1200417 29240327 := bstep (se 1 (by rfl) ⟨21930245, by rfl⟩ : syracuseStep 29240327 = 43860491) B43860491
theorem B3042623 : Blo 1200417 3042623 := bstep (se 1 (by rfl) ⟨2281967, by rfl⟩ : syracuseStep 3042623 = 4563935) B4563935
theorem B16248605 : Blo 1200417 16248605 := bstep (se 3 (by rfl) ⟨3046613, by rfl⟩ : syracuseStep 16248605 = 6093227) B6093227
theorem B3043271 : Blo 1200417 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B4559287 : Blo 1200417 4559287 := bstep (se 1 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 4559287 = 6838931) B6838931
theorem B1201567 : Blo 1200417 1201567 := bstep (se 1 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 1201567 = 1802351) B1802351
theorem B62437553 : Blo 1200417 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B1800815 : Blo 1200417 1800815 := bstep (se 1 (by rfl) ⟨1350611, by rfl⟩ : syracuseStep 1800815 = 2701223) B2701223
theorem B1801319 : Blo 1200417 1801319 := bstep (se 1 (by rfl) ⟨1350989, by rfl⟩ : syracuseStep 1801319 = 2701979) B2701979
theorem B173318453 : Blo 1200417 173318453 := bstep (se 5 (by rfl) ⟨8124302, by rfl⟩ : syracuseStep 173318453 = 16248605) B16248605
theorem B6079049 : Blo 1200417 6079049 := bstep (se 2 (by rfl) ⟨2279643, by rfl⟩ : syracuseStep 6079049 = 4559287) B4559287
theorem B2704211 : Blo 1200417 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B41625035 : Blo 1200417 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B4057883 : Blo 1200417 4057883 := bstep (se 1 (by rfl) ⟨3043412, by rfl⟩ : syracuseStep 4057883 = 6086825) B6086825
theorem B1200543 : Blo 1200417 1200543 := bstep (se 1 (by rfl) ⟨900407, by rfl⟩ : syracuseStep 1200543 = 1800815) B1800815
theorem B19493551 : Blo 1200417 19493551 := bstep (se 1 (by rfl) ⟨14620163, by rfl⟩ : syracuseStep 19493551 = 29240327) B29240327
theorem B1200879 : Blo 1200417 1200879 := bstep (se 1 (by rfl) ⟨900659, by rfl⟩ : syracuseStep 1200879 = 1801319) B1801319
theorem B2028415 : Blo 1200417 2028415 := bstep (se 1 (by rfl) ⟨1521311, by rfl⟩ : syracuseStep 2028415 = 3042623) B3042623
theorem B2028847 : Blo 1200417 2028847 := bstep (se 1 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 2028847 = 3043271) B3043271
theorem B58416227 : Blo 1200417 58416227 := bstep (se 1 (by rfl) ⟨43812170, by rfl⟩ : syracuseStep 58416227 = 87624341) B87624341
theorem B1350895 : Blo 1200417 1350895 := bstep (se 1 (by rfl) ⟨1013171, by rfl⟩ : syracuseStep 1350895 = 2026343) B2026343
theorem B1802807 : Blo 1200417 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B2704553 : Blo 1200417 2704553 := bstep (se 2 (by rfl) ⟨1014207, by rfl⟩ : syracuseStep 2704553 = 2028415) B2028415
theorem B2705129 : Blo 1200417 2705129 := bstep (se 2 (by rfl) ⟨1014423, by rfl⟩ : syracuseStep 2705129 = 2028847) B2028847
theorem B2705255 : Blo 1200417 2705255 := bstep (se 1 (by rfl) ⟨2028941, by rfl⟩ : syracuseStep 2705255 = 4057883) B4057883
theorem B27750023 : Blo 1200417 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B115545635 : Blo 1200417 115545635 := bstep (se 1 (by rfl) ⟨86659226, by rfl⟩ : syracuseStep 115545635 = 173318453) B173318453
theorem B4052699 : Blo 1200417 4052699 := bstep (se 1 (by rfl) ⟨3039524, by rfl⟩ : syracuseStep 4052699 = 6079049) B6079049
theorem B25991401 : Blo 1200417 25991401 := bstep (se 2 (by rfl) ⟨9746775, by rfl⟩ : syracuseStep 25991401 = 19493551) B19493551
theorem B1801193 : Blo 1200417 1801193 := bstep (se 2 (by rfl) ⟨675447, by rfl⟩ : syracuseStep 1801193 = 1350895) B1350895
theorem B38944151 : Blo 1200417 38944151 := bstep (se 1 (by rfl) ⟨29208113, by rfl⟩ : syracuseStep 38944151 = 58416227) B58416227
theorem B1803035 : Blo 1200417 1803035 := bstep (se 1 (by rfl) ⟨1352276, by rfl⟩ : syracuseStep 1803035 = 2704553) B2704553
theorem B77030423 : Blo 1200417 77030423 := bstep (se 1 (by rfl) ⟨57772817, by rfl⟩ : syracuseStep 77030423 = 115545635) B115545635
theorem B1803419 : Blo 1200417 1803419 := bstep (se 1 (by rfl) ⟨1352564, by rfl⟩ : syracuseStep 1803419 = 2705129) B2705129
theorem B1803503 : Blo 1200417 1803503 := bstep (se 1 (by rfl) ⟨1352627, by rfl⟩ : syracuseStep 1803503 = 2705255) B2705255
theorem B25962767 : Blo 1200417 25962767 := bstep (se 1 (by rfl) ⟨19472075, by rfl⟩ : syracuseStep 25962767 = 38944151) B38944151
theorem B18500015 : Blo 1200417 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B34655201 : Blo 1200417 34655201 := bstep (se 2 (by rfl) ⟨12995700, by rfl⟩ : syracuseStep 34655201 = 25991401) B25991401
theorem B1200795 : Blo 1200417 1200795 := bstep (se 1 (by rfl) ⟨900596, by rfl⟩ : syracuseStep 1200795 = 1801193) B1801193
theorem B1201871 : Blo 1200417 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B2701799 : Blo 1200417 2701799 := bstep (se 1 (by rfl) ⟨2026349, by rfl⟩ : syracuseStep 2701799 = 4052699) B4052699
theorem B23103467 : Blo 1200417 23103467 := bstep (se 1 (by rfl) ⟨17327600, by rfl⟩ : syracuseStep 23103467 = 34655201) B34655201
theorem B12333343 : Blo 1200417 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B1202023 : Blo 1200417 1202023 := bstep (se 1 (by rfl) ⟨901517, by rfl⟩ : syracuseStep 1202023 = 1803035) B1803035
theorem B51353615 : Blo 1200417 51353615 := bstep (se 1 (by rfl) ⟨38515211, by rfl⟩ : syracuseStep 51353615 = 77030423) B77030423
theorem B1202279 : Blo 1200417 1202279 := bstep (se 1 (by rfl) ⟨901709, by rfl⟩ : syracuseStep 1202279 = 1803419) B1803419
theorem B1202335 : Blo 1200417 1202335 := bstep (se 1 (by rfl) ⟨901751, by rfl⟩ : syracuseStep 1202335 = 1803503) B1803503
theorem B17308511 : Blo 1200417 17308511 := bstep (se 1 (by rfl) ⟨12981383, by rfl⟩ : syracuseStep 17308511 = 25962767) B25962767
theorem B1801199 : Blo 1200417 1801199 := bstep (se 1 (by rfl) ⟨1350899, by rfl⟩ : syracuseStep 1801199 = 2701799) B2701799
theorem B15402311 : Blo 1200417 15402311 := bstep (se 1 (by rfl) ⟨11551733, by rfl⟩ : syracuseStep 15402311 = 23103467) B23103467
theorem B34235743 : Blo 1200417 34235743 := bstep (se 1 (by rfl) ⟨25676807, by rfl⟩ : syracuseStep 34235743 = 51353615) B51353615
theorem B16444457 : Blo 1200417 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B11539007 : Blo 1200417 11539007 := bstep (se 1 (by rfl) ⟨8654255, by rfl⟩ : syracuseStep 11539007 = 17308511) B17308511
theorem B1200799 : Blo 1200417 1200799 := bstep (se 1 (by rfl) ⟨900599, by rfl⟩ : syracuseStep 1200799 = 1801199) B1801199
theorem B7692671 : Blo 1200417 7692671 := bstep (se 1 (by rfl) ⟨5769503, by rfl⟩ : syracuseStep 7692671 = 11539007) B11539007
theorem B45647657 : Blo 1200417 45647657 := bstep (se 2 (by rfl) ⟨17117871, by rfl⟩ : syracuseStep 45647657 = 34235743) B34235743
theorem B10962971 : Blo 1200417 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B10268207 : Blo 1200417 10268207 := bstep (se 1 (by rfl) ⟨7701155, by rfl⟩ : syracuseStep 10268207 = 15402311) B15402311
theorem B5128447 : Blo 1200417 5128447 := bstep (se 1 (by rfl) ⟨3846335, by rfl⟩ : syracuseStep 5128447 = 7692671) B7692671
theorem B7308647 : Blo 1200417 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B6845471 : Blo 1200417 6845471 := bstep (se 1 (by rfl) ⟨5134103, by rfl⟩ : syracuseStep 6845471 = 10268207) B10268207
theorem B30431771 : Blo 1200417 30431771 := bstep (se 1 (by rfl) ⟨22823828, by rfl⟩ : syracuseStep 30431771 = 45647657) B45647657
theorem B4563647 : Blo 1200417 4563647 := bstep (se 1 (by rfl) ⟨3422735, by rfl⟩ : syracuseStep 4563647 = 6845471) B6845471
theorem B20287847 : Blo 1200417 20287847 := bstep (se 1 (by rfl) ⟨15215885, by rfl⟩ : syracuseStep 20287847 = 30431771) B30431771
theorem B6837929 : Blo 1200417 6837929 := bstep (se 2 (by rfl) ⟨2564223, by rfl⟩ : syracuseStep 6837929 = 5128447) B5128447
theorem B4872431 : Blo 1200417 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B13525231 : Blo 1200417 13525231 := bstep (se 1 (by rfl) ⟨10143923, by rfl⟩ : syracuseStep 13525231 = 20287847) B20287847
theorem B12993149 : Blo 1200417 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B3042431 : Blo 1200417 3042431 := bstep (se 1 (by rfl) ⟨2281823, by rfl⟩ : syracuseStep 3042431 = 4563647) B4563647
theorem B4558619 : Blo 1200417 4558619 := bstep (se 1 (by rfl) ⟨3418964, by rfl⟩ : syracuseStep 4558619 = 6837929) B6837929
theorem B18033641 : Blo 1200417 18033641 := bstep (se 2 (by rfl) ⟨6762615, by rfl⟩ : syracuseStep 18033641 = 13525231) B13525231
theorem B8662099 : Blo 1200417 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B2028287 : Blo 1200417 2028287 := bstep (se 1 (by rfl) ⟨1521215, by rfl⟩ : syracuseStep 2028287 = 3042431) B3042431
theorem B3039079 : Blo 1200417 3039079 := bstep (se 1 (by rfl) ⟨2279309, by rfl⟩ : syracuseStep 3039079 = 4558619) B4558619
theorem B1352191 : Blo 1200417 1352191 := bstep (se 1 (by rfl) ⟨1014143, by rfl⟩ : syracuseStep 1352191 = 2028287) B2028287
theorem B12022427 : Blo 1200417 12022427 := bstep (se 1 (by rfl) ⟨9016820, by rfl⟩ : syracuseStep 12022427 = 18033641) B18033641
theorem B4052105 : Blo 1200417 4052105 := bstep (se 2 (by rfl) ⟨1519539, by rfl⟩ : syracuseStep 4052105 = 3039079) B3039079
theorem B11549465 : Blo 1200417 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B1802921 : Blo 1200417 1802921 := bstep (se 2 (by rfl) ⟨676095, by rfl⟩ : syracuseStep 1802921 = 1352191) B1352191
theorem B8014951 : Blo 1200417 8014951 := bstep (se 1 (by rfl) ⟨6011213, by rfl⟩ : syracuseStep 8014951 = 12022427) B12022427
theorem B2701403 : Blo 1200417 2701403 := bstep (se 1 (by rfl) ⟨2026052, by rfl⟩ : syracuseStep 2701403 = 4052105) B4052105
theorem B7699643 : Blo 1200417 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B10686601 : Blo 1200417 10686601 := bstep (se 2 (by rfl) ⟨4007475, by rfl⟩ : syracuseStep 10686601 = 8014951) B8014951
theorem B5133095 : Blo 1200417 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B1201947 : Blo 1200417 1201947 := bstep (se 1 (by rfl) ⟨901460, by rfl⟩ : syracuseStep 1201947 = 1802921) B1802921
theorem B1800935 : Blo 1200417 1800935 := bstep (se 1 (by rfl) ⟨1350701, by rfl⟩ : syracuseStep 1800935 = 2701403) B2701403
theorem B14248801 : Blo 1200417 14248801 := bstep (se 2 (by rfl) ⟨5343300, by rfl⟩ : syracuseStep 14248801 = 10686601) B10686601
theorem B1200623 : Blo 1200417 1200623 := bstep (se 1 (by rfl) ⟨900467, by rfl⟩ : syracuseStep 1200623 = 1800935) B1800935
theorem B3422063 : Blo 1200417 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B18998401 : Blo 1200417 18998401 := bstep (se 2 (by rfl) ⟨7124400, by rfl⟩ : syracuseStep 18998401 = 14248801) B14248801
theorem B2281375 : Blo 1200417 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B25331201 : Blo 1200417 25331201 := bstep (se 2 (by rfl) ⟨9499200, by rfl⟩ : syracuseStep 25331201 = 18998401) B18998401
theorem B3041833 : Blo 1200417 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B4055777 : Blo 1200417 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B16887467 : Blo 1200417 16887467 := bstep (se 1 (by rfl) ⟨12665600, by rfl⟩ : syracuseStep 16887467 = 25331201) B25331201
theorem B2703851 : Blo 1200417 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B11258311 : Blo 1200417 11258311 := bstep (se 1 (by rfl) ⟨8443733, by rfl⟩ : syracuseStep 11258311 = 16887467) B16887467
theorem B1802567 : Blo 1200417 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B15011081 : Blo 1200417 15011081 := bstep (se 2 (by rfl) ⟨5629155, by rfl⟩ : syracuseStep 15011081 = 11258311) B11258311
theorem B10007387 : Blo 1200417 10007387 := bstep (se 1 (by rfl) ⟨7505540, by rfl⟩ : syracuseStep 10007387 = 15011081) B15011081
theorem B1201711 : Blo 1200417 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B6671591 : Blo 1200417 6671591 := bstep (se 1 (by rfl) ⟨5003693, by rfl⟩ : syracuseStep 6671591 = 10007387) B10007387
theorem B4447727 : Blo 1200417 4447727 := bstep (se 1 (by rfl) ⟨3335795, by rfl⟩ : syracuseStep 4447727 = 6671591) B6671591
theorem B2965151 : Blo 1200417 2965151 := bstep (se 1 (by rfl) ⟨2223863, by rfl⟩ : syracuseStep 2965151 = 4447727) B4447727
theorem B1976767 : Blo 1200417 1976767 := bstep (se 1 (by rfl) ⟨1482575, by rfl⟩ : syracuseStep 1976767 = 2965151) B2965151
theorem B10542757 : Blo 1200417 10542757 := bstep (se 4 (by rfl) ⟨988383, by rfl⟩ : syracuseStep 10542757 = 1976767) B1976767
theorem B14057009 : Blo 1200417 14057009 := bstep (se 2 (by rfl) ⟨5271378, by rfl⟩ : syracuseStep 14057009 = 10542757) B10542757
theorem B9371339 : Blo 1200417 9371339 := bstep (se 1 (by rfl) ⟨7028504, by rfl⟩ : syracuseStep 9371339 = 14057009) B14057009
theorem B6247559 : Blo 1200417 6247559 := bstep (se 1 (by rfl) ⟨4685669, by rfl⟩ : syracuseStep 6247559 = 9371339) B9371339
theorem B4165039 : Blo 1200417 4165039 := bstep (se 1 (by rfl) ⟨3123779, by rfl⟩ : syracuseStep 4165039 = 6247559) B6247559
theorem B22213541 : Blo 1200417 22213541 := bstep (se 4 (by rfl) ⟨2082519, by rfl⟩ : syracuseStep 22213541 = 4165039) B4165039
theorem B14809027 : Blo 1200417 14809027 := bstep (se 1 (by rfl) ⟨11106770, by rfl⟩ : syracuseStep 14809027 = 22213541) B22213541
theorem B19745369 : Blo 1200417 19745369 := bstep (se 2 (by rfl) ⟨7404513, by rfl⟩ : syracuseStep 19745369 = 14809027) B14809027
theorem B13163579 : Blo 1200417 13163579 := bstep (se 1 (by rfl) ⟨9872684, by rfl⟩ : syracuseStep 13163579 = 19745369) B19745369
theorem B8775719 : Blo 1200417 8775719 := bstep (se 1 (by rfl) ⟨6581789, by rfl⟩ : syracuseStep 8775719 = 13163579) B13163579
theorem B5850479 : Blo 1200417 5850479 := bstep (se 1 (by rfl) ⟨4387859, by rfl⟩ : syracuseStep 5850479 = 8775719) B8775719
theorem B15601277 : Blo 1200417 15601277 := bstep (se 3 (by rfl) ⟨2925239, by rfl⟩ : syracuseStep 15601277 = 5850479) B5850479
theorem B10400851 : Blo 1200417 10400851 := bstep (se 1 (by rfl) ⟨7800638, by rfl⟩ : syracuseStep 10400851 = 15601277) B15601277
theorem B55471205 : Blo 1200417 55471205 := bstep (se 4 (by rfl) ⟨5200425, by rfl⟩ : syracuseStep 55471205 = 10400851) B10400851
theorem B36980803 : Blo 1200417 36980803 := bstep (se 1 (by rfl) ⟨27735602, by rfl⟩ : syracuseStep 36980803 = 55471205) B55471205
theorem B49307737 : Blo 1200417 49307737 := bstep (se 2 (by rfl) ⟨18490401, by rfl⟩ : syracuseStep 49307737 = 36980803) B36980803
theorem B65743649 : Blo 1200417 65743649 := bstep (se 2 (by rfl) ⟨24653868, by rfl⟩ : syracuseStep 65743649 = 49307737) B49307737
theorem B43829099 : Blo 1200417 43829099 := bstep (se 1 (by rfl) ⟨32871824, by rfl⟩ : syracuseStep 43829099 = 65743649) B65743649
theorem B29219399 : Blo 1200417 29219399 := bstep (se 1 (by rfl) ⟨21914549, by rfl⟩ : syracuseStep 29219399 = 43829099) B43829099
theorem B19479599 : Blo 1200417 19479599 := bstep (se 1 (by rfl) ⟨14609699, by rfl⟩ : syracuseStep 19479599 = 29219399) B29219399
theorem B12986399 : Blo 1200417 12986399 := bstep (se 1 (by rfl) ⟨9739799, by rfl⟩ : syracuseStep 12986399 = 19479599) B19479599
theorem B8657599 : Blo 1200417 8657599 := bstep (se 1 (by rfl) ⟨6493199, by rfl⟩ : syracuseStep 8657599 = 12986399) B12986399
theorem B11543465 : Blo 1200417 11543465 := bstep (se 2 (by rfl) ⟨4328799, by rfl⟩ : syracuseStep 11543465 = 8657599) B8657599
theorem B7695643 : Blo 1200417 7695643 := bstep (se 1 (by rfl) ⟨5771732, by rfl⟩ : syracuseStep 7695643 = 11543465) B11543465
theorem B10260857 : Blo 1200417 10260857 := bstep (se 2 (by rfl) ⟨3847821, by rfl⟩ : syracuseStep 10260857 = 7695643) B7695643
theorem B6840571 : Blo 1200417 6840571 := bstep (se 1 (by rfl) ⟨5130428, by rfl⟩ : syracuseStep 6840571 = 10260857) B10260857
theorem B9120761 : Blo 1200417 9120761 := bstep (se 2 (by rfl) ⟨3420285, by rfl⟩ : syracuseStep 9120761 = 6840571) B6840571
theorem B6080507 : Blo 1200417 6080507 := bstep (se 1 (by rfl) ⟨4560380, by rfl⟩ : syracuseStep 6080507 = 9120761) B9120761
theorem B4053671 : Blo 1200417 4053671 := bstep (se 1 (by rfl) ⟨3040253, by rfl⟩ : syracuseStep 4053671 = 6080507) B6080507
theorem B2702447 : Blo 1200417 2702447 := bstep (se 1 (by rfl) ⟨2026835, by rfl⟩ : syracuseStep 2702447 = 4053671) B4053671
theorem B1801631 : Blo 1200417 1801631 := bstep (se 1 (by rfl) ⟨1351223, by rfl⟩ : syracuseStep 1801631 = 2702447) B2702447
theorem B1201087 : Blo 1200417 1201087 := bstep (se 1 (by rfl) ⟨900815, by rfl⟩ : syracuseStep 1201087 = 1801631) B1801631

theorem C0 (j : ℕ) (h1 : 300104 ≤ j) (h2 : j ≤ 300603) : Blo 1200417 (4 * j + 3) := by
  interval_cases j
  · exact B1200419
  · exact B1200423
  · exact B1200427
  · exact B1200431
  · exact B1200435
  · exact B1200439
  · exact B1200443
  · exact B1200447
  · exact B1200451
  · exact B1200455
  · exact B1200459
  · exact B1200463
  · exact B1200467
  · exact B1200471
  · exact B1200475
  · exact B1200479
  · exact B1200483
  · exact B1200487
  · exact B1200491
  · exact B1200495
  · exact B1200499
  · exact B1200503
  · exact B1200507
  · exact B1200511
  · exact B1200515
  · exact B1200519
  · exact B1200523
  · exact B1200527
  · exact B1200531
  · exact B1200535
  · exact B1200539
  · exact B1200543
  · exact B1200547
  · exact B1200551
  · exact B1200555
  · exact B1200559
  · exact B1200563
  · exact B1200567
  · exact B1200571
  · exact B1200575
  · exact B1200579
  · exact B1200583
  · exact B1200587
  · exact B1200591
  · exact B1200595
  · exact B1200599
  · exact B1200603
  · exact B1200607
  · exact B1200611
  · exact B1200615
  · exact B1200619
  · exact B1200623
  · exact B1200627
  · exact B1200631
  · exact B1200635
  · exact B1200639
  · exact B1200643
  · exact B1200647
  · exact B1200651
  · exact B1200655
  · exact B1200659
  · exact B1200663
  · exact B1200667
  · exact B1200671
  · exact B1200675
  · exact B1200679
  · exact B1200683
  · exact B1200687
  · exact B1200691
  · exact B1200695
  · exact B1200699
  · exact B1200703
  · exact B1200707
  · exact B1200711
  · exact B1200715
  · exact B1200719
  · exact B1200723
  · exact B1200727
  · exact B1200731
  · exact B1200735
  · exact B1200739
  · exact B1200743
  · exact B1200747
  · exact B1200751
  · exact B1200755
  · exact B1200759
  · exact B1200763
  · exact B1200767
  · exact B1200771
  · exact B1200775
  · exact B1200779
  · exact B1200783
  · exact B1200787
  · exact B1200791
  · exact B1200795
  · exact B1200799
  · exact B1200803
  · exact B1200807
  · exact B1200811
  · exact B1200815
  · exact B1200819
  · exact B1200823
  · exact B1200827
  · exact B1200831
  · exact B1200835
  · exact B1200839
  · exact B1200843
  · exact B1200847
  · exact B1200851
  · exact B1200855
  · exact B1200859
  · exact B1200863
  · exact B1200867
  · exact B1200871
  · exact B1200875
  · exact B1200879
  · exact B1200883
  · exact B1200887
  · exact B1200891
  · exact B1200895
  · exact B1200899
  · exact B1200903
  · exact B1200907
  · exact B1200911
  · exact B1200915
  · exact B1200919
  · exact B1200923
  · exact B1200927
  · exact B1200931
  · exact B1200935
  · exact B1200939
  · exact B1200943
  · exact B1200947
  · exact B1200951
  · exact B1200955
  · exact B1200959
  · exact B1200963
  · exact B1200967
  · exact B1200971
  · exact B1200975
  · exact B1200979
  · exact B1200983
  · exact B1200987
  · exact B1200991
  · exact B1200995
  · exact B1200999
  · exact B1201003
  · exact B1201007
  · exact B1201011
  · exact B1201015
  · exact B1201019
  · exact B1201023
  · exact B1201027
  · exact B1201031
  · exact B1201035
  · exact B1201039
  · exact B1201043
  · exact B1201047
  · exact B1201051
  · exact B1201055
  · exact B1201059
  · exact B1201063
  · exact B1201067
  · exact B1201071
  · exact B1201075
  · exact B1201079
  · exact B1201083
  · exact B1201087
  · exact B1201091
  · exact B1201095
  · exact B1201099
  · exact B1201103
  · exact B1201107
  · exact B1201111
  · exact B1201115
  · exact B1201119
  · exact B1201123
  · exact B1201127
  · exact B1201131
  · exact B1201135
  · exact B1201139
  · exact B1201143
  · exact B1201147
  · exact B1201151
  · exact B1201155
  · exact B1201159
  · exact B1201163
  · exact B1201167
  · exact B1201171
  · exact B1201175
  · exact B1201179
  · exact B1201183
  · exact B1201187
  · exact B1201191
  · exact B1201195
  · exact B1201199
  · exact B1201203
  · exact B1201207
  · exact B1201211
  · exact B1201215
  · exact B1201219
  · exact B1201223
  · exact B1201227
  · exact B1201231
  · exact B1201235
  · exact B1201239
  · exact B1201243
  · exact B1201247
  · exact B1201251
  · exact B1201255
  · exact B1201259
  · exact B1201263
  · exact B1201267
  · exact B1201271
  · exact B1201275
  · exact B1201279
  · exact B1201283
  · exact B1201287
  · exact B1201291
  · exact B1201295
  · exact B1201299
  · exact B1201303
  · exact B1201307
  · exact B1201311
  · exact B1201315
  · exact B1201319
  · exact B1201323
  · exact B1201327
  · exact B1201331
  · exact B1201335
  · exact B1201339
  · exact B1201343
  · exact B1201347
  · exact B1201351
  · exact B1201355
  · exact B1201359
  · exact B1201363
  · exact B1201367
  · exact B1201371
  · exact B1201375
  · exact B1201379
  · exact B1201383
  · exact B1201387
  · exact B1201391
  · exact B1201395
  · exact B1201399
  · exact B1201403
  · exact B1201407
  · exact B1201411
  · exact B1201415
  · exact B1201419
  · exact B1201423
  · exact B1201427
  · exact B1201431
  · exact B1201435
  · exact B1201439
  · exact B1201443
  · exact B1201447
  · exact B1201451
  · exact B1201455
  · exact B1201459
  · exact B1201463
  · exact B1201467
  · exact B1201471
  · exact B1201475
  · exact B1201479
  · exact B1201483
  · exact B1201487
  · exact B1201491
  · exact B1201495
  · exact B1201499
  · exact B1201503
  · exact B1201507
  · exact B1201511
  · exact B1201515
  · exact B1201519
  · exact B1201523
  · exact B1201527
  · exact B1201531
  · exact B1201535
  · exact B1201539
  · exact B1201543
  · exact B1201547
  · exact B1201551
  · exact B1201555
  · exact B1201559
  · exact B1201563
  · exact B1201567
  · exact B1201571
  · exact B1201575
  · exact B1201579
  · exact B1201583
  · exact B1201587
  · exact B1201591
  · exact B1201595
  · exact B1201599
  · exact B1201603
  · exact B1201607
  · exact B1201611
  · exact B1201615
  · exact B1201619
  · exact B1201623
  · exact B1201627
  · exact B1201631
  · exact B1201635
  · exact B1201639
  · exact B1201643
  · exact B1201647
  · exact B1201651
  · exact B1201655
  · exact B1201659
  · exact B1201663
  · exact B1201667
  · exact B1201671
  · exact B1201675
  · exact B1201679
  · exact B1201683
  · exact B1201687
  · exact B1201691
  · exact B1201695
  · exact B1201699
  · exact B1201703
  · exact B1201707
  · exact B1201711
  · exact B1201715
  · exact B1201719
  · exact B1201723
  · exact B1201727
  · exact B1201731
  · exact B1201735
  · exact B1201739
  · exact B1201743
  · exact B1201747
  · exact B1201751
  · exact B1201755
  · exact B1201759
  · exact B1201763
  · exact B1201767
  · exact B1201771
  · exact B1201775
  · exact B1201779
  · exact B1201783
  · exact B1201787
  · exact B1201791
  · exact B1201795
  · exact B1201799
  · exact B1201803
  · exact B1201807
  · exact B1201811
  · exact B1201815
  · exact B1201819
  · exact B1201823
  · exact B1201827
  · exact B1201831
  · exact B1201835
  · exact B1201839
  · exact B1201843
  · exact B1201847
  · exact B1201851
  · exact B1201855
  · exact B1201859
  · exact B1201863
  · exact B1201867
  · exact B1201871
  · exact B1201875
  · exact B1201879
  · exact B1201883
  · exact B1201887
  · exact B1201891
  · exact B1201895
  · exact B1201899
  · exact B1201903
  · exact B1201907
  · exact B1201911
  · exact B1201915
  · exact B1201919
  · exact B1201923
  · exact B1201927
  · exact B1201931
  · exact B1201935
  · exact B1201939
  · exact B1201943
  · exact B1201947
  · exact B1201951
  · exact B1201955
  · exact B1201959
  · exact B1201963
  · exact B1201967
  · exact B1201971
  · exact B1201975
  · exact B1201979
  · exact B1201983
  · exact B1201987
  · exact B1201991
  · exact B1201995
  · exact B1201999
  · exact B1202003
  · exact B1202007
  · exact B1202011
  · exact B1202015
  · exact B1202019
  · exact B1202023
  · exact B1202027
  · exact B1202031
  · exact B1202035
  · exact B1202039
  · exact B1202043
  · exact B1202047
  · exact B1202051
  · exact B1202055
  · exact B1202059
  · exact B1202063
  · exact B1202067
  · exact B1202071
  · exact B1202075
  · exact B1202079
  · exact B1202083
  · exact B1202087
  · exact B1202091
  · exact B1202095
  · exact B1202099
  · exact B1202103
  · exact B1202107
  · exact B1202111
  · exact B1202115
  · exact B1202119
  · exact B1202123
  · exact B1202127
  · exact B1202131
  · exact B1202135
  · exact B1202139
  · exact B1202143
  · exact B1202147
  · exact B1202151
  · exact B1202155
  · exact B1202159
  · exact B1202163
  · exact B1202167
  · exact B1202171
  · exact B1202175
  · exact B1202179
  · exact B1202183
  · exact B1202187
  · exact B1202191
  · exact B1202195
  · exact B1202199
  · exact B1202203
  · exact B1202207
  · exact B1202211
  · exact B1202215
  · exact B1202219
  · exact B1202223
  · exact B1202227
  · exact B1202231
  · exact B1202235
  · exact B1202239
  · exact B1202243
  · exact B1202247
  · exact B1202251
  · exact B1202255
  · exact B1202259
  · exact B1202263
  · exact B1202267
  · exact B1202271
  · exact B1202275
  · exact B1202279
  · exact B1202283
  · exact B1202287
  · exact B1202291
  · exact B1202295
  · exact B1202299
  · exact B1202303
  · exact B1202307
  · exact B1202311
  · exact B1202315
  · exact B1202319
  · exact B1202323
  · exact B1202327
  · exact B1202331
  · exact B1202335
  · exact B1202339
  · exact B1202343
  · exact B1202347
  · exact B1202351
  · exact B1202355
  · exact B1202359
  · exact B1202363
  · exact B1202367
  · exact B1202371
  · exact B1202375
  · exact B1202379
  · exact B1202383
  · exact B1202387
  · exact B1202391
  · exact B1202395
  · exact B1202399
  · exact B1202403
  · exact B1202407
  · exact B1202411
  · exact B1202415

theorem solution (m : ℕ) (hlo : 1200417 ≤ m) (hhi : m ≤ 1202417) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 300104 ≤ j := by omega
    have hj2 : j ≤ 300603 := by omega
    have hb : Blo 1200417 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
