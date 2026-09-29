-- Prove2me | solution 1 for syracuse_descends_range_1281959_1283959
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:19.633888+00:00
-- url     : https://prove2.me/submissions/9c0ae795-14e0-4672-8f33-20667c4e86c0

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


theorem B1925141 : Blo 1281959 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B1925165 : Blo 1281959 1925165 := bbase (se 3 (by rfl) ⟨360968, by rfl⟩ : syracuseStep 1925165 = 721937) (by norm_num)
theorem B1826869 : Blo 1281959 1826869 := bbase (se 5 (by rfl) ⟨85634, by rfl⟩ : syracuseStep 1826869 = 171269) (by norm_num)
theorem B3293237 : Blo 1281959 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B1925189 : Blo 1281959 1925189 := bbase (se 4 (by rfl) ⟨180486, by rfl⟩ : syracuseStep 1925189 = 360973) (by norm_num)
theorem B1925213 : Blo 1281959 1925213 := bbase (se 3 (by rfl) ⟨360977, by rfl⟩ : syracuseStep 1925213 = 721955) (by norm_num)
theorem B1925237 : Blo 1281959 1925237 := bbase (se 5 (by rfl) ⟨90245, by rfl⟩ : syracuseStep 1925237 = 180491) (by norm_num)
theorem B1540229 : Blo 1281959 1540229 := bbase (se 4 (by rfl) ⟨144396, by rfl⟩ : syracuseStep 1540229 = 288793) (by norm_num)
theorem B1925261 : Blo 1281959 1925261 := bbase (se 3 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 1925261 = 721973) (by norm_num)
theorem B1826965 : Blo 1281959 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B1540253 : Blo 1281959 1540253 := bbase (se 3 (by rfl) ⟨288797, by rfl⟩ : syracuseStep 1540253 = 577595) (by norm_num)
theorem B1925285 : Blo 1281959 1925285 := bbase (se 4 (by rfl) ⟨180495, by rfl⟩ : syracuseStep 1925285 = 360991) (by norm_num)
theorem B1925309 : Blo 1281959 1925309 := bbase (se 3 (by rfl) ⟨360995, by rfl⟩ : syracuseStep 1925309 = 721991) (by norm_num)
theorem B1925333 : Blo 1281959 1925333 := bbase (se 7 (by rfl) ⟨22562, by rfl⟩ : syracuseStep 1925333 = 45125) (by norm_num)
theorem B1925357 : Blo 1281959 1925357 := bbase (se 3 (by rfl) ⟨361004, by rfl⟩ : syracuseStep 1925357 = 722009) (by norm_num)
theorem B1925381 : Blo 1281959 1925381 := bbase (se 4 (by rfl) ⟨180504, by rfl⟩ : syracuseStep 1925381 = 361009) (by norm_num)
theorem B1925405 : Blo 1281959 1925405 := bbase (se 3 (by rfl) ⟨361013, by rfl⟩ : syracuseStep 1925405 = 722027) (by norm_num)
theorem B1925429 : Blo 1281959 1925429 := bbase (se 5 (by rfl) ⟨90254, by rfl⟩ : syracuseStep 1925429 = 180509) (by norm_num)
theorem B1925453 : Blo 1281959 1925453 := bbase (se 3 (by rfl) ⟨361022, by rfl⟩ : syracuseStep 1925453 = 722045) (by norm_num)
theorem B1925477 : Blo 1281959 1925477 := bbase (se 4 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 1925477 = 361027) (by norm_num)
theorem B2343277 : Blo 1281959 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1925501 : Blo 1281959 1925501 := bbase (se 3 (by rfl) ⟨361031, by rfl⟩ : syracuseStep 1925501 = 722063) (by norm_num)
theorem B1925525 : Blo 1281959 1925525 := bbase (se 6 (by rfl) ⟨45129, by rfl⟩ : syracuseStep 1925525 = 90259) (by norm_num)
theorem B1442209 : Blo 1281959 1442209 := bbase (se 2 (by rfl) ⟨540828, by rfl⟩ : syracuseStep 1442209 = 1081657) (by norm_num)
theorem B1925549 : Blo 1281959 1925549 := bbase (se 3 (by rfl) ⟨361040, by rfl⟩ : syracuseStep 1925549 = 722081) (by norm_num)
theorem B1442245 : Blo 1281959 1442245 := bbase (se 4 (by rfl) ⟨135210, by rfl⟩ : syracuseStep 1442245 = 270421) (by norm_num)
theorem B1925573 : Blo 1281959 1925573 := bbase (se 4 (by rfl) ⟨180522, by rfl⟩ : syracuseStep 1925573 = 361045) (by norm_num)
theorem B1540561 : Blo 1281959 1540561 := bbase (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) (by norm_num)
theorem B29630933 : Blo 1281959 29630933 := bbase (se 7 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 29630933 = 694475) (by norm_num)
theorem B1925597 : Blo 1281959 1925597 := bbase (se 3 (by rfl) ⟨361049, by rfl⟩ : syracuseStep 1925597 = 722099) (by norm_num)
theorem B1442281 : Blo 1281959 1442281 := bbase (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) (by norm_num)
theorem B1925621 : Blo 1281959 1925621 := bbase (se 5 (by rfl) ⟨90263, by rfl⟩ : syracuseStep 1925621 = 180527) (by norm_num)
theorem B1622521 : Blo 1281959 1622521 := bbase (se 2 (by rfl) ⟨608445, by rfl⟩ : syracuseStep 1622521 = 1216891) (by norm_num)
theorem B1442317 : Blo 1281959 1442317 := bbase (se 3 (by rfl) ⟨270434, by rfl⟩ : syracuseStep 1442317 = 540869) (by norm_num)
theorem B1925645 : Blo 1281959 1925645 := bbase (se 3 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 1925645 = 722117) (by norm_num)
theorem B1925669 : Blo 1281959 1925669 := bbase (se 4 (by rfl) ⟨180531, by rfl⟩ : syracuseStep 1925669 = 361063) (by norm_num)
theorem B1442353 : Blo 1281959 1442353 := bbase (se 2 (by rfl) ⟨540882, by rfl⟩ : syracuseStep 1442353 = 1081765) (by norm_num)
theorem B1925693 : Blo 1281959 1925693 := bbase (se 3 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 1925693 = 722135) (by norm_num)
theorem B2310725 : Blo 1281959 2310725 := bbase (se 4 (by rfl) ⟨216630, by rfl⟩ : syracuseStep 2310725 = 433261) (by norm_num)
theorem B1442389 : Blo 1281959 1442389 := bbase (se 8 (by rfl) ⟨8451, by rfl⟩ : syracuseStep 1442389 = 16903) (by norm_num)
theorem B1925717 : Blo 1281959 1925717 := bbase (se 8 (by rfl) ⟨11283, by rfl⟩ : syracuseStep 1925717 = 22567) (by norm_num)
theorem B1925741 : Blo 1281959 1925741 := bbase (se 3 (by rfl) ⟨361076, by rfl⟩ : syracuseStep 1925741 = 722153) (by norm_num)
theorem B1442425 : Blo 1281959 1442425 := bbase (se 2 (by rfl) ⟨540909, by rfl⟩ : syracuseStep 1442425 = 1081819) (by norm_num)
theorem B1540733 : Blo 1281959 1540733 := bbase (se 3 (by rfl) ⟨288887, by rfl⟩ : syracuseStep 1540733 = 577775) (by norm_num)
theorem B1827461 : Blo 1281959 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B1925765 : Blo 1281959 1925765 := bbase (se 4 (by rfl) ⟨180540, by rfl⟩ : syracuseStep 1925765 = 361081) (by norm_num)
theorem B2163341 : Blo 1281959 2163341 := bbase (se 3 (by rfl) ⟨405626, by rfl⟩ : syracuseStep 2163341 = 811253) (by norm_num)
theorem B2310805 : Blo 1281959 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B1442461 : Blo 1281959 1442461 := bbase (se 3 (by rfl) ⟨270461, by rfl⟩ : syracuseStep 1442461 = 540923) (by norm_num)
theorem B1925789 : Blo 1281959 1925789 := bbase (se 3 (by rfl) ⟨361085, by rfl⟩ : syracuseStep 1925789 = 722171) (by norm_num)
theorem B1622693 : Blo 1281959 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B1925813 : Blo 1281959 1925813 := bbase (se 5 (by rfl) ⟨90272, by rfl⟩ : syracuseStep 1925813 = 180545) (by norm_num)
theorem B1442497 : Blo 1281959 1442497 := bbase (se 2 (by rfl) ⟨540936, by rfl⟩ : syracuseStep 1442497 = 1081873) (by norm_num)
theorem B3654341 : Blo 1281959 3654341 := bbase (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) (by norm_num)
theorem B1925837 : Blo 1281959 1925837 := bbase (se 3 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 1925837 = 722189) (by norm_num)
theorem B1622749 : Blo 1281959 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B1442533 : Blo 1281959 1442533 := bbase (se 4 (by rfl) ⟨135237, by rfl⟩ : syracuseStep 1442533 = 270475) (by norm_num)
theorem B1925861 : Blo 1281959 1925861 := bbase (se 4 (by rfl) ⟨180549, by rfl⟩ : syracuseStep 1925861 = 361099) (by norm_num)
theorem B1540849 : Blo 1281959 1540849 := bbase (se 2 (by rfl) ⟨577818, by rfl⟩ : syracuseStep 1540849 = 1155637) (by norm_num)
theorem B1925885 : Blo 1281959 1925885 := bbase (se 3 (by rfl) ⟨361103, by rfl⟩ : syracuseStep 1925885 = 722207) (by norm_num)
theorem B2433797 : Blo 1281959 2433797 := bbase (se 4 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 2433797 = 456337) (by norm_num)
theorem B1442569 : Blo 1281959 1442569 := bbase (se 2 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 1442569 = 1081927) (by norm_num)
theorem B2163469 : Blo 1281959 2163469 := bbase (se 3 (by rfl) ⟨405650, by rfl⟩ : syracuseStep 2163469 = 811301) (by norm_num)
theorem B1925909 : Blo 1281959 1925909 := bbase (se 6 (by rfl) ⟨45138, by rfl⟩ : syracuseStep 1925909 = 90277) (by norm_num)
theorem B3081005 : Blo 1281959 3081005 := bbase (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) (by norm_num)
theorem B1442605 : Blo 1281959 1442605 := bbase (se 3 (by rfl) ⟨270488, by rfl⟩ : syracuseStep 1442605 = 540977) (by norm_num)
theorem B1925933 : Blo 1281959 1925933 := bbase (se 3 (by rfl) ⟨361112, by rfl⟩ : syracuseStep 1925933 = 722225) (by norm_num)
theorem B1622845 : Blo 1281959 1622845 := bbase (se 3 (by rfl) ⟨304283, by rfl⟩ : syracuseStep 1622845 = 608567) (by norm_num)
theorem B4391749 : Blo 1281959 4391749 := bbase (se 4 (by rfl) ⟨411726, by rfl⟩ : syracuseStep 4391749 = 823453) (by norm_num)
theorem B1442641 : Blo 1281959 1442641 := bbase (se 2 (by rfl) ⟨540990, by rfl⟩ : syracuseStep 1442641 = 1081981) (by norm_num)
theorem B1540945 : Blo 1281959 1540945 := bbase (se 2 (by rfl) ⟨577854, by rfl⟩ : syracuseStep 1540945 = 1155709) (by norm_num)
theorem B2884445 : Blo 1281959 2884445 := bbase (se 3 (by rfl) ⟨540833, by rfl⟩ : syracuseStep 2884445 = 1081667) (by norm_num)
theorem B2163557 : Blo 1281959 2163557 := bbase (se 4 (by rfl) ⟨202833, by rfl⟩ : syracuseStep 2163557 = 405667) (by norm_num)
theorem B10953589 : Blo 1281959 10953589 := bbase (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) (by norm_num)
theorem B1442677 : Blo 1281959 1442677 := bbase (se 5 (by rfl) ⟨67625, by rfl⟩ : syracuseStep 1442677 = 135251) (by norm_num)
theorem B11707253 : Blo 1281959 11707253 := bbase (se 5 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 11707253 = 1097555) (by norm_num)
theorem B1442713 : Blo 1281959 1442713 := bbase (se 2 (by rfl) ⟨541017, by rfl⟩ : syracuseStep 1442713 = 1082035) (by norm_num)
theorem B2884517 : Blo 1281959 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B3244981 : Blo 1281959 3244981 := bbase (se 5 (by rfl) ⟨152108, by rfl⟩ : syracuseStep 3244981 = 304217) (by norm_num)
theorem B1442749 : Blo 1281959 1442749 := bbase (se 3 (by rfl) ⟨270515, by rfl⟩ : syracuseStep 1442749 = 541031) (by norm_num)
theorem B1369045 : Blo 1281959 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B12329941 : Blo 1281959 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B1442785 : Blo 1281959 1442785 := bbase (se 2 (by rfl) ⟨541044, by rfl⟩ : syracuseStep 1442785 = 1082089) (by norm_num)
theorem B1541089 : Blo 1281959 1541089 := bbase (se 2 (by rfl) ⟨577908, by rfl⟩ : syracuseStep 1541089 = 1155817) (by norm_num)
theorem B2163685 : Blo 1281959 2163685 := bbase (se 4 (by rfl) ⟨202845, by rfl⟩ : syracuseStep 2163685 = 405691) (by norm_num)
theorem B1623017 : Blo 1281959 1623017 := bbase (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) (by norm_num)
theorem B2884589 : Blo 1281959 2884589 := bbase (se 3 (by rfl) ⟨540860, by rfl⟩ : syracuseStep 2884589 = 1081721) (by norm_num)
theorem B1442821 : Blo 1281959 1442821 := bbase (se 4 (by rfl) ⟨135264, by rfl⟩ : syracuseStep 1442821 = 270529) (by norm_num)
theorem B1623073 : Blo 1281959 1623073 := bbase (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) (by norm_num)
theorem B3245093 : Blo 1281959 3245093 := bbase (se 4 (by rfl) ⟨304227, by rfl⟩ : syracuseStep 3245093 = 608455) (by norm_num)
theorem B1442857 : Blo 1281959 1442857 := bbase (se 2 (by rfl) ⟨541071, by rfl⟩ : syracuseStep 1442857 = 1082143) (by norm_num)
theorem B2884661 : Blo 1281959 2884661 := bbase (se 5 (by rfl) ⟨135218, by rfl⟩ : syracuseStep 2884661 = 270437) (by norm_num)
theorem B6497333 : Blo 1281959 6497333 := bbase (se 5 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 6497333 = 609125) (by norm_num)
theorem B2163773 : Blo 1281959 2163773 := bbase (se 3 (by rfl) ⟨405707, by rfl⟩ : syracuseStep 2163773 = 811415) (by norm_num)
theorem B1442893 : Blo 1281959 1442893 := bbase (se 3 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 1442893 = 541085) (by norm_num)
theorem B1442929 : Blo 1281959 1442929 := bbase (se 2 (by rfl) ⟨541098, by rfl⟩ : syracuseStep 1442929 = 1082197) (by norm_num)
theorem B2884733 : Blo 1281959 2884733 := bbase (se 3 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 2884733 = 1081775) (by norm_num)
theorem B1623169 : Blo 1281959 1623169 := bbase (se 2 (by rfl) ⟨608688, by rfl⟩ : syracuseStep 1623169 = 1217377) (by norm_num)
theorem B1369229 : Blo 1281959 1369229 := bbase (se 3 (by rfl) ⟨256730, by rfl⟩ : syracuseStep 1369229 = 513461) (by norm_num)
theorem B1442965 : Blo 1281959 1442965 := bbase (se 6 (by rfl) ⟨33819, by rfl⟩ : syracuseStep 1442965 = 67639) (by norm_num)
theorem B3900565 : Blo 1281959 3900565 := bbase (se 6 (by rfl) ⟨91419, by rfl⟩ : syracuseStep 3900565 = 182839) (by norm_num)
theorem B1828013 : Blo 1281959 1828013 := bbase (se 3 (by rfl) ⟨342752, by rfl⟩ : syracuseStep 1828013 = 685505) (by norm_num)
theorem B13173941 : Blo 1281959 13173941 := bbase (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) (by norm_num)
theorem B1443001 : Blo 1281959 1443001 := bbase (se 2 (by rfl) ⟨541125, by rfl⟩ : syracuseStep 1443001 = 1082251) (by norm_num)
theorem B2163901 : Blo 1281959 2163901 := bbase (se 3 (by rfl) ⟨405731, by rfl⟩ : syracuseStep 2163901 = 811463) (by norm_num)
theorem B2884805 : Blo 1281959 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B40035541 : Blo 1281959 40035541 := bbase (se 7 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 40035541 = 938333) (by norm_num)
theorem B1443037 : Blo 1281959 1443037 := bbase (se 3 (by rfl) ⟨270569, by rfl⟩ : syracuseStep 1443037 = 541139) (by norm_num)
theorem B1950941 : Blo 1281959 1950941 := bbase (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) (by norm_num)
theorem B3245285 : Blo 1281959 3245285 := bbase (se 4 (by rfl) ⟨304245, by rfl⟩ : syracuseStep 3245285 = 608491) (by norm_num)
theorem B5481701 : Blo 1281959 5481701 := bbase (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) (by norm_num)
theorem B1443073 : Blo 1281959 1443073 := bbase (se 2 (by rfl) ⟨541152, by rfl⟩ : syracuseStep 1443073 = 1082305) (by norm_num)
theorem B2884877 : Blo 1281959 2884877 := bbase (se 3 (by rfl) ⟨540914, by rfl⟩ : syracuseStep 2884877 = 1081829) (by norm_num)
theorem B2163989 : Blo 1281959 2163989 := bbase (se 6 (by rfl) ⟨50718, by rfl⟩ : syracuseStep 2163989 = 101437) (by norm_num)
theorem B1443109 : Blo 1281959 1443109 := bbase (se 4 (by rfl) ⟨135291, by rfl⟩ : syracuseStep 1443109 = 270583) (by norm_num)
theorem B1623341 : Blo 1281959 1623341 := bbase (se 3 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 1623341 = 608753) (by norm_num)
theorem B5203253 : Blo 1281959 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B1443145 : Blo 1281959 1443145 := bbase (se 2 (by rfl) ⟨541179, by rfl⟩ : syracuseStep 1443145 = 1082359) (by norm_num)
theorem B2884949 : Blo 1281959 2884949 := bbase (se 12 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 2884949 = 2113) (by norm_num)
theorem B14607701 : Blo 1281959 14607701 := bbase (se 12 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 14607701 = 10699) (by norm_num)
theorem B1951061 : Blo 1281959 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B1623397 : Blo 1281959 1623397 := bbase (se 4 (by rfl) ⟨152193, by rfl⟩ : syracuseStep 1623397 = 304387) (by norm_num)
theorem B1443181 : Blo 1281959 1443181 := bbase (se 3 (by rfl) ⟨270596, by rfl⟩ : syracuseStep 1443181 = 541193) (by norm_num)
theorem B1443217 : Blo 1281959 1443217 := bbase (se 2 (by rfl) ⟨541206, by rfl⟩ : syracuseStep 1443217 = 1082413) (by norm_num)
theorem B2164117 : Blo 1281959 2164117 := bbase (se 6 (by rfl) ⟨50721, by rfl⟩ : syracuseStep 2164117 = 101443) (by norm_num)
theorem B5203349 : Blo 1281959 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B2885021 : Blo 1281959 2885021 := bbase (se 3 (by rfl) ⟨540941, by rfl⟩ : syracuseStep 2885021 = 1081883) (by norm_num)
theorem B1443253 : Blo 1281959 1443253 := bbase (se 5 (by rfl) ⟨67652, by rfl⟩ : syracuseStep 1443253 = 135305) (by norm_num)
theorem B1623493 : Blo 1281959 1623493 := bbase (se 4 (by rfl) ⟨152202, by rfl⟩ : syracuseStep 1623493 = 304405) (by norm_num)
theorem B1443289 : Blo 1281959 1443289 := bbase (se 2 (by rfl) ⟨541233, by rfl⟩ : syracuseStep 1443289 = 1082467) (by norm_num)
theorem B2885093 : Blo 1281959 2885093 := bbase (se 4 (by rfl) ⟨270477, by rfl⟩ : syracuseStep 2885093 = 540955) (by norm_num)
theorem B2164205 : Blo 1281959 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B2434549 : Blo 1281959 2434549 := bbase (se 5 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 2434549 = 228239) (by norm_num)
theorem B1443325 : Blo 1281959 1443325 := bbase (se 3 (by rfl) ⟨270623, by rfl⟩ : syracuseStep 1443325 = 541247) (by norm_num)
theorem B5481989 : Blo 1281959 5481989 := bbase (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) (by norm_num)
theorem B20809237 : Blo 1281959 20809237 := bbase (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) (by norm_num)
theorem B1443361 : Blo 1281959 1443361 := bbase (se 2 (by rfl) ⟨541260, by rfl⟩ : syracuseStep 1443361 = 1082521) (by norm_num)
theorem B2885165 : Blo 1281959 2885165 := bbase (se 3 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 2885165 = 1081937) (by norm_num)
theorem B4326965 : Blo 1281959 4326965 := bbase (se 5 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 4326965 = 405653) (by norm_num)
theorem B3245629 : Blo 1281959 3245629 := bbase (se 3 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 3245629 = 1217111) (by norm_num)
theorem B1443397 : Blo 1281959 1443397 := bbase (se 4 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 1443397 = 270637) (by norm_num)
theorem B4867685 : Blo 1281959 4867685 := bbase (se 4 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 4867685 = 912691) (by norm_num)
theorem B1443433 : Blo 1281959 1443433 := bbase (se 2 (by rfl) ⟨541287, by rfl⟩ : syracuseStep 1443433 = 1082575) (by norm_num)
theorem B2164333 : Blo 1281959 2164333 := bbase (se 3 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 2164333 = 811625) (by norm_num)
theorem B2672237 : Blo 1281959 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B1623665 : Blo 1281959 1623665 := bbase (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) (by norm_num)
theorem B2885237 : Blo 1281959 2885237 := bbase (se 5 (by rfl) ⟨135245, by rfl⟩ : syracuseStep 2885237 = 270491) (by norm_num)
theorem B2434693 : Blo 1281959 2434693 := bbase (se 4 (by rfl) ⟨228252, by rfl⟩ : syracuseStep 2434693 = 456505) (by norm_num)
theorem B1443469 : Blo 1281959 1443469 := bbase (se 3 (by rfl) ⟨270650, by rfl⟩ : syracuseStep 1443469 = 541301) (by norm_num)
theorem B3466901 : Blo 1281959 3466901 := bbase (se 6 (by rfl) ⟨81255, by rfl⟩ : syracuseStep 3466901 = 162511) (by norm_num)
theorem B1623721 : Blo 1281959 1623721 := bbase (se 2 (by rfl) ⟨608895, by rfl⟩ : syracuseStep 1623721 = 1217791) (by norm_num)
theorem B3245741 : Blo 1281959 3245741 := bbase (se 3 (by rfl) ⟨608576, by rfl⟩ : syracuseStep 3245741 = 1217153) (by norm_num)
theorem B1443505 : Blo 1281959 1443505 := bbase (se 2 (by rfl) ⟨541314, by rfl⟩ : syracuseStep 1443505 = 1082629) (by norm_num)
theorem B2885309 : Blo 1281959 2885309 := bbase (se 3 (by rfl) ⟨540995, by rfl⟩ : syracuseStep 2885309 = 1081991) (by norm_num)
theorem B2164421 : Blo 1281959 2164421 := bbase (se 4 (by rfl) ⟨202914, by rfl⟩ : syracuseStep 2164421 = 405829) (by norm_num)
theorem B1443541 : Blo 1281959 1443541 := bbase (se 7 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 1443541 = 33833) (by norm_num)
theorem B1443577 : Blo 1281959 1443577 := bbase (se 2 (by rfl) ⟨541341, by rfl⟩ : syracuseStep 1443577 = 1082683) (by norm_num)
theorem B2885381 : Blo 1281959 2885381 := bbase (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) (by norm_num)
theorem B1623817 : Blo 1281959 1623817 := bbase (se 2 (by rfl) ⟨608931, by rfl⟩ : syracuseStep 1623817 = 1217863) (by norm_num)
theorem B1443613 : Blo 1281959 1443613 := bbase (se 3 (by rfl) ⟨270677, by rfl⟩ : syracuseStep 1443613 = 541355) (by norm_num)
theorem B2434853 : Blo 1281959 2434853 := bbase (se 4 (by rfl) ⟨228267, by rfl⟩ : syracuseStep 2434853 = 456535) (by norm_num)
theorem B2926373 : Blo 1281959 2926373 := bbase (se 4 (by rfl) ⟨274347, by rfl⟩ : syracuseStep 2926373 = 548695) (by norm_num)
theorem B1443649 : Blo 1281959 1443649 := bbase (se 2 (by rfl) ⟨541368, by rfl⟩ : syracuseStep 1443649 = 1082737) (by norm_num)
theorem B2164549 : Blo 1281959 2164549 := bbase (se 4 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 2164549 = 405853) (by norm_num)
theorem B2885453 : Blo 1281959 2885453 := bbase (se 3 (by rfl) ⟨541022, by rfl⟩ : syracuseStep 2885453 = 1082045) (by norm_num)
theorem B1443685 : Blo 1281959 1443685 := bbase (se 4 (by rfl) ⟨135345, by rfl⟩ : syracuseStep 1443685 = 270691) (by norm_num)
theorem B3655525 : Blo 1281959 3655525 := bbase (se 4 (by rfl) ⟨342705, by rfl⟩ : syracuseStep 3655525 = 685411) (by norm_num)
theorem B3245933 : Blo 1281959 3245933 := bbase (se 3 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 3245933 = 1217225) (by norm_num)
theorem B1369981 : Blo 1281959 1369981 := bbase (se 3 (by rfl) ⟨256871, by rfl⟩ : syracuseStep 1369981 = 513743) (by norm_num)
theorem B1443721 : Blo 1281959 1443721 := bbase (se 2 (by rfl) ⟨541395, by rfl⟩ : syracuseStep 1443721 = 1082791) (by norm_num)
theorem B1427345 : Blo 1281959 1427345 := bbase (se 2 (by rfl) ⟨535254, by rfl⟩ : syracuseStep 1427345 = 1070509) (by norm_num)
theorem B2885525 : Blo 1281959 2885525 := bbase (se 6 (by rfl) ⟨67629, by rfl⟩ : syracuseStep 2885525 = 135259) (by norm_num)
theorem B2164637 : Blo 1281959 2164637 := bbase (se 3 (by rfl) ⟨405869, by rfl⟩ : syracuseStep 2164637 = 811739) (by norm_num)
theorem B1443757 : Blo 1281959 1443757 := bbase (se 3 (by rfl) ⟨270704, by rfl⟩ : syracuseStep 1443757 = 541409) (by norm_num)
theorem B2434997 : Blo 1281959 2434997 := bbase (se 5 (by rfl) ⟨114140, by rfl⟩ : syracuseStep 2434997 = 228281) (by norm_num)
theorem B1623989 : Blo 1281959 1623989 := bbase (se 5 (by rfl) ⟨76124, by rfl⟩ : syracuseStep 1623989 = 152249) (by norm_num)
theorem B2738117 : Blo 1281959 2738117 := bbase (se 4 (by rfl) ⟨256698, by rfl⟩ : syracuseStep 2738117 = 513397) (by norm_num)
theorem B1370053 : Blo 1281959 1370053 := bbase (se 4 (by rfl) ⟨128442, by rfl⟩ : syracuseStep 1370053 = 256885) (by norm_num)
theorem B2779085 : Blo 1281959 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B1443793 : Blo 1281959 1443793 := bbase (se 2 (by rfl) ⟨541422, by rfl⟩ : syracuseStep 1443793 = 1082845) (by norm_num)
theorem B2885597 : Blo 1281959 2885597 := bbase (se 3 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 2885597 = 1082099) (by norm_num)
theorem B4327397 : Blo 1281959 4327397 := bbase (se 4 (by rfl) ⟨405693, by rfl⟩ : syracuseStep 4327397 = 811387) (by norm_num)
theorem B1624045 : Blo 1281959 1624045 := bbase (se 3 (by rfl) ⟨304508, by rfl⟩ : syracuseStep 1624045 = 609017) (by norm_num)
theorem B1443829 : Blo 1281959 1443829 := bbase (se 5 (by rfl) ⟨67679, by rfl⟩ : syracuseStep 1443829 = 135359) (by norm_num)
theorem B3655685 : Blo 1281959 3655685 := bbase (se 4 (by rfl) ⟨342720, by rfl⟩ : syracuseStep 3655685 = 685441) (by norm_num)
theorem B1443865 : Blo 1281959 1443865 := bbase (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) (by norm_num)
theorem B2164765 : Blo 1281959 2164765 := bbase (se 3 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 2164765 = 811787) (by norm_num)
theorem B2885669 : Blo 1281959 2885669 := bbase (se 4 (by rfl) ⟨270531, by rfl⟩ : syracuseStep 2885669 = 541063) (by norm_num)
theorem B1443901 : Blo 1281959 1443901 := bbase (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) (by norm_num)
theorem B1624141 : Blo 1281959 1624141 := bbase (se 3 (by rfl) ⟨304526, by rfl⟩ : syracuseStep 1624141 = 609053) (by norm_num)
theorem B2738261 : Blo 1281959 2738261 := bbase (se 8 (by rfl) ⟨16044, by rfl⟩ : syracuseStep 2738261 = 32089) (by norm_num)
theorem B2345045 : Blo 1281959 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B2926685 : Blo 1281959 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B1443937 : Blo 1281959 1443937 := bbase (se 2 (by rfl) ⟨541476, by rfl⟩ : syracuseStep 1443937 = 1082953) (by norm_num)
theorem B2885741 : Blo 1281959 2885741 := bbase (se 3 (by rfl) ⟨541076, by rfl⟩ : syracuseStep 2885741 = 1082153) (by norm_num)
theorem B2164853 : Blo 1281959 2164853 := bbase (se 5 (by rfl) ⟨101477, by rfl⟩ : syracuseStep 2164853 = 202955) (by norm_num)
theorem B1370233 : Blo 1281959 1370233 := bbase (se 2 (by rfl) ⟨513837, by rfl⟩ : syracuseStep 1370233 = 1027675) (by norm_num)
theorem B1443973 : Blo 1281959 1443973 := bbase (se 4 (by rfl) ⟨135372, by rfl⟩ : syracuseStep 1443973 = 270745) (by norm_num)
theorem B1444009 : Blo 1281959 1444009 := bbase (se 2 (by rfl) ⟨541503, by rfl⟩ : syracuseStep 1444009 = 1083007) (by norm_num)
theorem B2885813 : Blo 1281959 2885813 := bbase (se 5 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 2885813 = 270545) (by norm_num)
theorem B3246277 : Blo 1281959 3246277 := bbase (se 4 (by rfl) ⟨304338, by rfl⟩ : syracuseStep 3246277 = 608677) (by norm_num)
theorem B1444045 : Blo 1281959 1444045 := bbase (se 3 (by rfl) ⟨270758, by rfl⟩ : syracuseStep 1444045 = 541517) (by norm_num)
theorem B2435285 : Blo 1281959 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B1444081 : Blo 1281959 1444081 := bbase (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) (by norm_num)
theorem B2164981 : Blo 1281959 2164981 := bbase (se 5 (by rfl) ⟨101483, by rfl⟩ : syracuseStep 2164981 = 202967) (by norm_num)
theorem B5482741 : Blo 1281959 5482741 := bbase (se 5 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 5482741 = 514007) (by norm_num)
theorem B3655925 : Blo 1281959 3655925 := bbase (se 5 (by rfl) ⟨171371, by rfl⟩ : syracuseStep 3655925 = 342743) (by norm_num)
theorem B1624313 : Blo 1281959 1624313 := bbase (se 2 (by rfl) ⟨609117, by rfl⟩ : syracuseStep 1624313 = 1218235) (by norm_num)
theorem B2885885 : Blo 1281959 2885885 := bbase (se 3 (by rfl) ⟨541103, by rfl⟩ : syracuseStep 2885885 = 1082207) (by norm_num)
theorem B1444117 : Blo 1281959 1444117 := bbase (se 6 (by rfl) ⟨33846, by rfl⟩ : syracuseStep 1444117 = 67693) (by norm_num)
theorem B1624369 : Blo 1281959 1624369 := bbase (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) (by norm_num)
theorem B3246389 : Blo 1281959 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B1444153 : Blo 1281959 1444153 := bbase (se 2 (by rfl) ⟨541557, by rfl⟩ : syracuseStep 1444153 = 1083115) (by norm_num)
theorem B2885957 : Blo 1281959 2885957 := bbase (se 4 (by rfl) ⟨270558, by rfl⟩ : syracuseStep 2885957 = 541117) (by norm_num)
theorem B6498629 : Blo 1281959 6498629 := bbase (se 4 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 6498629 = 1218493) (by norm_num)
theorem B2165069 : Blo 1281959 2165069 := bbase (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) (by norm_num)
theorem B1444189 : Blo 1281959 1444189 := bbase (se 3 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 1444189 = 541571) (by norm_num)
theorem B2435437 : Blo 1281959 2435437 := bbase (se 3 (by rfl) ⟨456644, by rfl⟩ : syracuseStep 2435437 = 913289) (by norm_num)
theorem B1444225 : Blo 1281959 1444225 := bbase (se 2 (by rfl) ⟨541584, by rfl⟩ : syracuseStep 1444225 = 1083169) (by norm_num)
theorem B2886029 : Blo 1281959 2886029 := bbase (se 3 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 2886029 = 1082261) (by norm_num)
theorem B1624465 : Blo 1281959 1624465 := bbase (se 2 (by rfl) ⟨609174, by rfl⟩ : syracuseStep 1624465 = 1218349) (by norm_num)
theorem B4327829 : Blo 1281959 4327829 := bbase (se 6 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 4327829 = 202867) (by norm_num)
theorem B1444261 : Blo 1281959 1444261 := bbase (se 4 (by rfl) ⟨135399, by rfl⟩ : syracuseStep 1444261 = 270799) (by norm_num)
theorem B3656117 : Blo 1281959 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B1444297 : Blo 1281959 1444297 := bbase (se 2 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 1444297 = 1083223) (by norm_num)
theorem B2165197 : Blo 1281959 2165197 := bbase (se 3 (by rfl) ⟨405974, by rfl⟩ : syracuseStep 2165197 = 811949) (by norm_num)
theorem B2886101 : Blo 1281959 2886101 := bbase (se 7 (by rfl) ⟨33821, by rfl⟩ : syracuseStep 2886101 = 67643) (by norm_num)
theorem B1444333 : Blo 1281959 1444333 := bbase (se 3 (by rfl) ⟨270812, by rfl⟩ : syracuseStep 1444333 = 541625) (by norm_num)
theorem B3246581 : Blo 1281959 3246581 := bbase (se 5 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 3246581 = 304367) (by norm_num)
theorem B6941173 : Blo 1281959 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1444369 : Blo 1281959 1444369 := bbase (se 2 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 1444369 = 1083277) (by norm_num)
theorem B2468381 : Blo 1281959 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B2886173 : Blo 1281959 2886173 := bbase (se 3 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 2886173 = 1082315) (by norm_num)
theorem B2165285 : Blo 1281959 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B1370677 : Blo 1281959 1370677 := bbase (se 5 (by rfl) ⟨64250, by rfl⟩ : syracuseStep 1370677 = 128501) (by norm_num)
theorem B1444405 : Blo 1281959 1444405 := bbase (se 5 (by rfl) ⟨67706, by rfl⟩ : syracuseStep 1444405 = 135413) (by norm_num)
theorem B1624637 : Blo 1281959 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B3467861 : Blo 1281959 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B10693205 : Blo 1281959 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B1444441 : Blo 1281959 1444441 := bbase (se 2 (by rfl) ⟨541665, by rfl⟩ : syracuseStep 1444441 = 1083331) (by norm_num)
theorem B2886245 : Blo 1281959 2886245 := bbase (se 4 (by rfl) ⟨270585, by rfl⟩ : syracuseStep 2886245 = 541171) (by norm_num)
theorem B1624693 : Blo 1281959 1624693 := bbase (se 5 (by rfl) ⟨76157, by rfl⟩ : syracuseStep 1624693 = 152315) (by norm_num)
theorem B2435741 : Blo 1281959 2435741 := bbase (se 3 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 2435741 = 913403) (by norm_num)
theorem B2165413 : Blo 1281959 2165413 := bbase (se 4 (by rfl) ⟨203007, by rfl⟩ : syracuseStep 2165413 = 406015) (by norm_num)
theorem B2886317 : Blo 1281959 2886317 := bbase (se 3 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 2886317 = 1082369) (by norm_num)
theorem B1370801 : Blo 1281959 1370801 := bbase (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) (by norm_num)
theorem B1624789 : Blo 1281959 1624789 := bbase (se 7 (by rfl) ⟨19040, by rfl⟩ : syracuseStep 1624789 = 38081) (by norm_num)
theorem B4106981 : Blo 1281959 4106981 := bbase (se 4 (by rfl) ⟨385029, by rfl⟩ : syracuseStep 4106981 = 770059) (by norm_num)
theorem B6490853 : Blo 1281959 6490853 := bbase (se 4 (by rfl) ⟨608517, by rfl⟩ : syracuseStep 6490853 = 1217035) (by norm_num)
theorem B2886389 : Blo 1281959 2886389 := bbase (se 5 (by rfl) ⟨135299, by rfl⟩ : syracuseStep 2886389 = 270599) (by norm_num)
theorem B2165501 : Blo 1281959 2165501 := bbase (se 3 (by rfl) ⟨406031, by rfl⟩ : syracuseStep 2165501 = 812063) (by norm_num)
theorem B4868869 : Blo 1281959 4868869 := bbase (se 4 (by rfl) ⟨456456, by rfl⟩ : syracuseStep 4868869 = 912913) (by norm_num)
theorem B10955573 : Blo 1281959 10955573 := bbase (se 5 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 10955573 = 1027085) (by norm_num)
theorem B2739005 : Blo 1281959 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B2886461 : Blo 1281959 2886461 := bbase (se 3 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 2886461 = 1082423) (by norm_num)
theorem B4328261 : Blo 1281959 4328261 := bbase (se 4 (by rfl) ⟨405774, by rfl⟩ : syracuseStep 4328261 = 811549) (by norm_num)
theorem B3246925 : Blo 1281959 3246925 := bbase (se 3 (by rfl) ⟨608798, by rfl⟩ : syracuseStep 3246925 = 1217597) (by norm_num)
theorem B2165629 : Blo 1281959 2165629 := bbase (se 3 (by rfl) ⟨406055, by rfl⟩ : syracuseStep 2165629 = 812111) (by norm_num)
theorem B1624961 : Blo 1281959 1624961 := bbase (se 2 (by rfl) ⟨609360, by rfl⟩ : syracuseStep 1624961 = 1218721) (by norm_num)
theorem B2886533 : Blo 1281959 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B1371053 : Blo 1281959 1371053 := bbase (se 3 (by rfl) ⟨257072, by rfl⟩ : syracuseStep 1371053 = 514145) (by norm_num)
theorem B3247037 : Blo 1281959 3247037 := bbase (se 3 (by rfl) ⟨608819, by rfl⟩ : syracuseStep 3247037 = 1217639) (by norm_num)
theorem B2886605 : Blo 1281959 2886605 := bbase (se 3 (by rfl) ⟨541238, by rfl⟩ : syracuseStep 2886605 = 1082477) (by norm_num)
theorem B2165717 : Blo 1281959 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B5483477 : Blo 1281959 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B2886677 : Blo 1281959 2886677 := bbase (se 6 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 2886677 = 135313) (by norm_num)
theorem B4869173 : Blo 1281959 4869173 := bbase (se 5 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 4869173 = 456485) (by norm_num)
theorem B11103317 : Blo 1281959 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B2165845 : Blo 1281959 2165845 := bbase (se 8 (by rfl) ⟨12690, by rfl⟩ : syracuseStep 2165845 = 25381) (by norm_num)
theorem B2886749 : Blo 1281959 2886749 := bbase (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) (by norm_num)
theorem B3247229 : Blo 1281959 3247229 := bbase (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) (by norm_num)
theorem B2886821 : Blo 1281959 2886821 := bbase (se 4 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 2886821 = 541279) (by norm_num)
theorem B2165933 : Blo 1281959 2165933 := bbase (se 3 (by rfl) ⟨406112, by rfl⟩ : syracuseStep 2165933 = 812225) (by norm_num)
theorem B6163685 : Blo 1281959 6163685 := bbase (se 4 (by rfl) ⟨577845, by rfl⟩ : syracuseStep 6163685 = 1155691) (by norm_num)
theorem B2886893 : Blo 1281959 2886893 := bbase (se 3 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 2886893 = 1082585) (by norm_num)
theorem B4328693 : Blo 1281959 4328693 := bbase (se 5 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 4328693 = 405815) (by norm_num)
theorem B1387777 : Blo 1281959 1387777 := bbase (se 2 (by rfl) ⟨520416, by rfl⟩ : syracuseStep 1387777 = 1040833) (by norm_num)
theorem B2166061 : Blo 1281959 2166061 := bbase (se 3 (by rfl) ⟨406136, by rfl⟩ : syracuseStep 2166061 = 812273) (by norm_num)
theorem B2886965 : Blo 1281959 2886965 := bbase (se 5 (by rfl) ⟨135326, by rfl⟩ : syracuseStep 2886965 = 270653) (by norm_num)
theorem B2887037 : Blo 1281959 2887037 := bbase (se 3 (by rfl) ⟨541319, by rfl⟩ : syracuseStep 2887037 = 1082639) (by norm_num)
theorem B2166149 : Blo 1281959 2166149 := bbase (se 4 (by rfl) ⟨203076, by rfl⟩ : syracuseStep 2166149 = 406153) (by norm_num)
theorem B2436493 : Blo 1281959 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B2887109 : Blo 1281959 2887109 := bbase (se 4 (by rfl) ⟨270666, by rfl⟩ : syracuseStep 2887109 = 541333) (by norm_num)
theorem B3247573 : Blo 1281959 3247573 := bbase (se 7 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 3247573 = 76115) (by norm_num)
theorem B1756669 : Blo 1281959 1756669 := bbase (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) (by norm_num)
theorem B3083773 : Blo 1281959 3083773 := bbase (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) (by norm_num)
theorem B2166277 : Blo 1281959 2166277 := bbase (se 4 (by rfl) ⟨203088, by rfl⟩ : syracuseStep 2166277 = 406177) (by norm_num)
theorem B2887181 : Blo 1281959 2887181 := bbase (se 3 (by rfl) ⟨541346, by rfl⟩ : syracuseStep 2887181 = 1082693) (by norm_num)
theorem B2436637 : Blo 1281959 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B2739757 : Blo 1281959 2739757 := bbase (se 3 (by rfl) ⟨513704, by rfl⟩ : syracuseStep 2739757 = 1027409) (by norm_num)
theorem B3247685 : Blo 1281959 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B2887253 : Blo 1281959 2887253 := bbase (se 8 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 2887253 = 33835) (by norm_num)
theorem B6499925 : Blo 1281959 6499925 := bbase (se 8 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 6499925 = 76171) (by norm_num)
theorem B2166365 : Blo 1281959 2166365 := bbase (se 3 (by rfl) ⟨406193, by rfl⟩ : syracuseStep 2166365 = 812387) (by norm_num)
theorem B2502253 : Blo 1281959 2502253 := bbase (se 3 (by rfl) ⟨469172, by rfl⟩ : syracuseStep 2502253 = 938345) (by norm_num)
theorem B10407541 : Blo 1281959 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B2887325 : Blo 1281959 2887325 := bbase (se 3 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 2887325 = 1082747) (by norm_num)
theorem B4329125 : Blo 1281959 4329125 := bbase (se 4 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 4329125 = 811711) (by norm_num)
theorem B2739901 : Blo 1281959 2739901 := bbase (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) (by norm_num)
theorem B2436797 : Blo 1281959 2436797 := bbase (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) (by norm_num)
theorem B2166493 : Blo 1281959 2166493 := bbase (se 3 (by rfl) ⟨406217, by rfl⟩ : syracuseStep 2166493 = 812435) (by norm_num)
theorem B1388261 : Blo 1281959 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B2887397 : Blo 1281959 2887397 := bbase (se 4 (by rfl) ⟨270693, by rfl⟩ : syracuseStep 2887397 = 541387) (by norm_num)
theorem B3247877 : Blo 1281959 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B2887469 : Blo 1281959 2887469 := bbase (se 3 (by rfl) ⟨541400, by rfl⟩ : syracuseStep 2887469 = 1082801) (by norm_num)
theorem B11702069 : Blo 1281959 11702069 := bbase (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) (by norm_num)
theorem B2166581 : Blo 1281959 2166581 := bbase (se 5 (by rfl) ⟨101558, by rfl⟩ : syracuseStep 2166581 = 203117) (by norm_num)
theorem B2436941 : Blo 1281959 2436941 := bbase (se 3 (by rfl) ⟨456926, by rfl⟩ : syracuseStep 2436941 = 913853) (by norm_num)
theorem B2887541 : Blo 1281959 2887541 := bbase (se 5 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 2887541 = 270707) (by norm_num)
theorem B3084149 : Blo 1281959 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B2887613 : Blo 1281959 2887613 := bbase (se 3 (by rfl) ⟨541427, by rfl⟩ : syracuseStep 2887613 = 1082855) (by norm_num)
theorem B6492149 : Blo 1281959 6492149 := bbase (se 5 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 6492149 = 608639) (by norm_num)
theorem B2887685 : Blo 1281959 2887685 := bbase (se 4 (by rfl) ⟨270720, by rfl⟩ : syracuseStep 2887685 = 541441) (by norm_num)
theorem B2740277 : Blo 1281959 2740277 := bbase (se 5 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 2740277 = 256901) (by norm_num)
theorem B2887757 : Blo 1281959 2887757 := bbase (se 3 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 2887757 = 1082909) (by norm_num)
theorem B1462357 : Blo 1281959 1462357 := bbase (se 8 (by rfl) ⟨8568, by rfl⟩ : syracuseStep 1462357 = 17137) (by norm_num)
theorem B4329557 : Blo 1281959 4329557 := bbase (se 8 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 4329557 = 50737) (by norm_num)
theorem B3248221 : Blo 1281959 3248221 := bbase (se 3 (by rfl) ⟨609041, by rfl⟩ : syracuseStep 3248221 = 1218083) (by norm_num)
theorem B2437229 : Blo 1281959 2437229 := bbase (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) (by norm_num)
theorem B2887829 : Blo 1281959 2887829 := bbase (se 6 (by rfl) ⟨67683, by rfl⟩ : syracuseStep 2887829 = 135367) (by norm_num)
theorem B3248333 : Blo 1281959 3248333 := bbase (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) (by norm_num)
theorem B2887901 : Blo 1281959 2887901 := bbase (se 3 (by rfl) ⟨541481, by rfl⟩ : syracuseStep 2887901 = 1082963) (by norm_num)
theorem B2437381 : Blo 1281959 2437381 := bbase (se 4 (by rfl) ⟨228504, by rfl⟩ : syracuseStep 2437381 = 457009) (by norm_num)
theorem B2887973 : Blo 1281959 2887973 := bbase (se 4 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 2887973 = 541495) (by norm_num)
theorem B3084581 : Blo 1281959 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B5476693 : Blo 1281959 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B2888045 : Blo 1281959 2888045 := bbase (se 3 (by rfl) ⟨541508, by rfl⟩ : syracuseStep 2888045 = 1083017) (by norm_num)
theorem B3248525 : Blo 1281959 3248525 := bbase (se 3 (by rfl) ⟨609098, by rfl⟩ : syracuseStep 3248525 = 1218197) (by norm_num)
theorem B2740645 : Blo 1281959 2740645 := bbase (se 4 (by rfl) ⟨256935, by rfl⟩ : syracuseStep 2740645 = 513871) (by norm_num)
theorem B2888117 : Blo 1281959 2888117 := bbase (se 5 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 2888117 = 270761) (by norm_num)
theorem B2888189 : Blo 1281959 2888189 := bbase (se 3 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 2888189 = 1083071) (by norm_num)
theorem B4329989 : Blo 1281959 4329989 := bbase (se 4 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 4329989 = 811873) (by norm_num)
theorem B12497429 : Blo 1281959 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B2888261 : Blo 1281959 2888261 := bbase (se 4 (by rfl) ⟨270774, by rfl⟩ : syracuseStep 2888261 = 541549) (by norm_num)
theorem B2888333 : Blo 1281959 2888333 := bbase (se 3 (by rfl) ⟨541562, by rfl⟩ : syracuseStep 2888333 = 1083125) (by norm_num)
theorem B4108981 : Blo 1281959 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B2888405 : Blo 1281959 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B3248869 : Blo 1281959 3248869 := bbase (se 4 (by rfl) ⟨304581, by rfl⟩ : syracuseStep 3248869 = 609163) (by norm_num)
theorem B2888477 : Blo 1281959 2888477 := bbase (se 3 (by rfl) ⟨541589, by rfl⟩ : syracuseStep 2888477 = 1083179) (by norm_num)
theorem B1463077 : Blo 1281959 1463077 := bbase (se 4 (by rfl) ⟨137163, by rfl⟩ : syracuseStep 1463077 = 274327) (by norm_num)
theorem B3248981 : Blo 1281959 3248981 := bbase (se 9 (by rfl) ⟨9518, by rfl⟩ : syracuseStep 3248981 = 19037) (by norm_num)
theorem B2888549 : Blo 1281959 2888549 := bbase (se 4 (by rfl) ⟨270801, by rfl⟩ : syracuseStep 2888549 = 541603) (by norm_num)
theorem B3289997 : Blo 1281959 3289997 := bbase (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) (by norm_num)
theorem B2888621 : Blo 1281959 2888621 := bbase (se 3 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 2888621 = 1083233) (by norm_num)
theorem B4330421 : Blo 1281959 4330421 := bbase (se 5 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 4330421 = 405977) (by norm_num)
theorem B1463269 : Blo 1281959 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B2888693 : Blo 1281959 2888693 := bbase (se 5 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 2888693 = 270815) (by norm_num)
theorem B3249173 : Blo 1281959 3249173 := bbase (se 6 (by rfl) ⟨76152, by rfl⟩ : syracuseStep 3249173 = 152305) (by norm_num)
theorem B12334133 : Blo 1281959 12334133 := bbase (se 5 (by rfl) ⟨578162, by rfl⟩ : syracuseStep 12334133 = 1156325) (by norm_num)
theorem B2888765 : Blo 1281959 2888765 := bbase (se 3 (by rfl) ⟨541643, by rfl⟩ : syracuseStep 2888765 = 1083287) (by norm_num)
theorem B4871285 : Blo 1281959 4871285 := bbase (se 5 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 4871285 = 456683) (by norm_num)
theorem B2888837 : Blo 1281959 2888837 := bbase (se 4 (by rfl) ⟨270828, by rfl⟩ : syracuseStep 2888837 = 541657) (by norm_num)
theorem B3650741 : Blo 1281959 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B2888909 : Blo 1281959 2888909 := bbase (se 3 (by rfl) ⟨541670, by rfl⟩ : syracuseStep 2888909 = 1083341) (by norm_num)
theorem B6493445 : Blo 1281959 6493445 := bbase (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) (by norm_num)
theorem B2053453 : Blo 1281959 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B4330853 : Blo 1281959 4330853 := bbase (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) (by norm_num)
theorem B3249517 : Blo 1281959 3249517 := bbase (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) (by norm_num)
theorem B4871573 : Blo 1281959 4871573 := bbase (se 6 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 4871573 = 228355) (by norm_num)
theorem B2602405 : Blo 1281959 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B1734061 : Blo 1281959 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B1668541 : Blo 1281959 1668541 := bbase (se 3 (by rfl) ⟨312851, by rfl⟩ : syracuseStep 1668541 = 625703) (by norm_num)
theorem B3249629 : Blo 1281959 3249629 := bbase (se 3 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 3249629 = 1218611) (by norm_num)
theorem B1463789 : Blo 1281959 1463789 := bbase (se 3 (by rfl) ⟨274460, by rfl⟩ : syracuseStep 1463789 = 548921) (by norm_num)
theorem B4388357 : Blo 1281959 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B3249821 : Blo 1281959 3249821 := bbase (se 3 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 3249821 = 1218683) (by norm_num)
theorem B2053901 : Blo 1281959 2053901 := bbase (se 3 (by rfl) ⟨385106, by rfl⟩ : syracuseStep 2053901 = 770213) (by norm_num)
theorem B4331285 : Blo 1281959 4331285 := bbase (se 6 (by rfl) ⟨101514, by rfl⟩ : syracuseStep 4331285 = 203029) (by norm_num)
theorem B32896853 : Blo 1281959 32896853 := bbase (se 9 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 32896853 = 192755) (by norm_num)
theorem B2742149 : Blo 1281959 2742149 := bbase (se 4 (by rfl) ⟨257076, by rfl⟩ : syracuseStep 2742149 = 514153) (by norm_num)
theorem B1922957 : Blo 1281959 1922957 := bbase (se 3 (by rfl) ⟨360554, by rfl⟩ : syracuseStep 1922957 = 721109) (by norm_num)
theorem B1922981 : Blo 1281959 1922981 := bbase (se 4 (by rfl) ⟨180279, by rfl⟩ : syracuseStep 1922981 = 360559) (by norm_num)
theorem B3651493 : Blo 1281959 3651493 := bbase (se 4 (by rfl) ⟨342327, by rfl⟩ : syracuseStep 3651493 = 684655) (by norm_num)
theorem B9254837 : Blo 1281959 9254837 := bbase (se 5 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 9254837 = 867641) (by norm_num)
theorem B1923005 : Blo 1281959 1923005 := bbase (se 3 (by rfl) ⟨360563, by rfl⟩ : syracuseStep 1923005 = 721127) (by norm_num)
theorem B6166469 : Blo 1281959 6166469 := bbase (se 4 (by rfl) ⟨578106, by rfl⟩ : syracuseStep 6166469 = 1156213) (by norm_num)
theorem B1923029 : Blo 1281959 1923029 := bbase (se 7 (by rfl) ⟨22535, by rfl⟩ : syracuseStep 1923029 = 45071) (by norm_num)
theorem B31193045 : Blo 1281959 31193045 := bbase (se 7 (by rfl) ⟨365543, by rfl⟩ : syracuseStep 31193045 = 731087) (by norm_num)
theorem B7305173 : Blo 1281959 7305173 := bbase (se 7 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 7305173 = 171215) (by norm_num)
theorem B1923053 : Blo 1281959 1923053 := bbase (se 3 (by rfl) ⟨360572, by rfl⟩ : syracuseStep 1923053 = 721145) (by norm_num)
theorem B9369589 : Blo 1281959 9369589 := bbase (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) (by norm_num)
theorem B1923077 : Blo 1281959 1923077 := bbase (se 4 (by rfl) ⟨180288, by rfl⟩ : syracuseStep 1923077 = 360577) (by norm_num)
theorem B1923101 : Blo 1281959 1923101 := bbase (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) (by norm_num)
theorem B1923125 : Blo 1281959 1923125 := bbase (se 5 (by rfl) ⟨90146, by rfl⟩ : syracuseStep 1923125 = 180293) (by norm_num)
theorem B1923149 : Blo 1281959 1923149 := bbase (se 3 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 1923149 = 721181) (by norm_num)
theorem B1923173 : Blo 1281959 1923173 := bbase (se 4 (by rfl) ⟨180297, by rfl⟩ : syracuseStep 1923173 = 360595) (by norm_num)
theorem B1923197 : Blo 1281959 1923197 := bbase (se 3 (by rfl) ⟨360599, by rfl⟩ : syracuseStep 1923197 = 721199) (by norm_num)
theorem B1923221 : Blo 1281959 1923221 := bbase (se 6 (by rfl) ⟨45075, by rfl⟩ : syracuseStep 1923221 = 90151) (by norm_num)
theorem B1923245 : Blo 1281959 1923245 := bbase (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) (by norm_num)
theorem B1923269 : Blo 1281959 1923269 := bbase (se 4 (by rfl) ⟨180306, by rfl⟩ : syracuseStep 1923269 = 360613) (by norm_num)
theorem B4331717 : Blo 1281959 4331717 := bbase (se 4 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 4331717 = 812197) (by norm_num)
theorem B1923293 : Blo 1281959 1923293 := bbase (se 3 (by rfl) ⟨360617, by rfl⟩ : syracuseStep 1923293 = 721235) (by norm_num)
theorem B1923317 : Blo 1281959 1923317 := bbase (se 5 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 1923317 = 180311) (by norm_num)
theorem B1923341 : Blo 1281959 1923341 := bbase (se 3 (by rfl) ⟨360626, by rfl⟩ : syracuseStep 1923341 = 721253) (by norm_num)
theorem B2193685 : Blo 1281959 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1923365 : Blo 1281959 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B1923389 : Blo 1281959 1923389 := bbase (se 3 (by rfl) ⟨360635, by rfl⟩ : syracuseStep 1923389 = 721271) (by norm_num)
theorem B1923413 : Blo 1281959 1923413 := bbase (se 10 (by rfl) ⟨2817, by rfl⟩ : syracuseStep 1923413 = 5635) (by norm_num)
theorem B1923437 : Blo 1281959 1923437 := bbase (se 3 (by rfl) ⟨360644, by rfl⟩ : syracuseStep 1923437 = 721289) (by norm_num)
theorem B1923461 : Blo 1281959 1923461 := bbase (se 4 (by rfl) ⟨180324, by rfl⟩ : syracuseStep 1923461 = 360649) (by norm_num)
theorem B1923485 : Blo 1281959 1923485 := bbase (se 3 (by rfl) ⟨360653, by rfl⟩ : syracuseStep 1923485 = 721307) (by norm_num)
theorem B8214965 : Blo 1281959 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B1923509 : Blo 1281959 1923509 := bbase (se 5 (by rfl) ⟨90164, by rfl⟩ : syracuseStep 1923509 = 180329) (by norm_num)
theorem B1923533 : Blo 1281959 1923533 := bbase (se 3 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 1923533 = 721325) (by norm_num)
theorem B1923557 : Blo 1281959 1923557 := bbase (se 4 (by rfl) ⟨180333, by rfl⟩ : syracuseStep 1923557 = 360667) (by norm_num)
theorem B1923581 : Blo 1281959 1923581 := bbase (se 3 (by rfl) ⟨360671, by rfl⟩ : syracuseStep 1923581 = 721343) (by norm_num)
theorem B1923605 : Blo 1281959 1923605 := bbase (se 6 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 1923605 = 90169) (by norm_num)
theorem B6494741 : Blo 1281959 6494741 := bbase (se 6 (by rfl) ⟨152220, by rfl⟩ : syracuseStep 6494741 = 304441) (by norm_num)
theorem B1923629 : Blo 1281959 1923629 := bbase (se 3 (by rfl) ⟨360680, by rfl⟩ : syracuseStep 1923629 = 721361) (by norm_num)
theorem B4872757 : Blo 1281959 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B1923653 : Blo 1281959 1923653 := bbase (se 4 (by rfl) ⟨180342, by rfl⟩ : syracuseStep 1923653 = 360685) (by norm_num)
theorem B13163093 : Blo 1281959 13163093 := bbase (se 8 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 13163093 = 154255) (by norm_num)
theorem B1923677 : Blo 1281959 1923677 := bbase (se 3 (by rfl) ⟨360689, by rfl⟩ : syracuseStep 1923677 = 721379) (by norm_num)
theorem B1923701 : Blo 1281959 1923701 := bbase (se 5 (by rfl) ⟨90173, by rfl⟩ : syracuseStep 1923701 = 180347) (by norm_num)
theorem B7404149 : Blo 1281959 7404149 := bbase (se 5 (by rfl) ⟨347069, by rfl⟩ : syracuseStep 7404149 = 694139) (by norm_num)
theorem B4332149 : Blo 1281959 4332149 := bbase (se 5 (by rfl) ⟨203069, by rfl⟩ : syracuseStep 4332149 = 406139) (by norm_num)
theorem B10967669 : Blo 1281959 10967669 := bbase (se 5 (by rfl) ⟨514109, by rfl⟩ : syracuseStep 10967669 = 1028219) (by norm_num)
theorem B1923725 : Blo 1281959 1923725 := bbase (se 3 (by rfl) ⟨360698, by rfl⟩ : syracuseStep 1923725 = 721397) (by norm_num)
theorem B1923749 : Blo 1281959 1923749 := bbase (se 4 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 1923749 = 360703) (by norm_num)
theorem B1923773 : Blo 1281959 1923773 := bbase (se 3 (by rfl) ⟨360707, by rfl⟩ : syracuseStep 1923773 = 721415) (by norm_num)
theorem B1923797 : Blo 1281959 1923797 := bbase (se 7 (by rfl) ⟨22544, by rfl⟩ : syracuseStep 1923797 = 45089) (by norm_num)
theorem B1923821 : Blo 1281959 1923821 := bbase (se 3 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 1923821 = 721433) (by norm_num)
theorem B1923845 : Blo 1281959 1923845 := bbase (se 4 (by rfl) ⟨180360, by rfl⟩ : syracuseStep 1923845 = 360721) (by norm_num)
theorem B1923869 : Blo 1281959 1923869 := bbase (se 3 (by rfl) ⟨360725, by rfl⟩ : syracuseStep 1923869 = 721451) (by norm_num)
theorem B1563425 : Blo 1281959 1563425 := bbase (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) (by norm_num)
theorem B1645357 : Blo 1281959 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1923893 : Blo 1281959 1923893 := bbase (se 5 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 1923893 = 180365) (by norm_num)
theorem B1923917 : Blo 1281959 1923917 := bbase (se 3 (by rfl) ⟨360734, by rfl⟩ : syracuseStep 1923917 = 721469) (by norm_num)
theorem B1923941 : Blo 1281959 1923941 := bbase (se 4 (by rfl) ⟨180369, by rfl⟩ : syracuseStep 1923941 = 360739) (by norm_num)
theorem B4873061 : Blo 1281959 4873061 := bbase (se 4 (by rfl) ⟨456849, by rfl⟩ : syracuseStep 4873061 = 913699) (by norm_num)
theorem B1923965 : Blo 1281959 1923965 := bbase (se 3 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 1923965 = 721487) (by norm_num)
theorem B4225925 : Blo 1281959 4225925 := bbase (se 4 (by rfl) ⟨396180, by rfl⟩ : syracuseStep 4225925 = 792361) (by norm_num)
theorem B1923989 : Blo 1281959 1923989 := bbase (se 6 (by rfl) ⟨45093, by rfl⟩ : syracuseStep 1923989 = 90187) (by norm_num)
theorem B1924013 : Blo 1281959 1924013 := bbase (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) (by norm_num)
theorem B1924037 : Blo 1281959 1924037 := bbase (se 4 (by rfl) ⟨180378, by rfl⟩ : syracuseStep 1924037 = 360757) (by norm_num)
theorem B1924061 : Blo 1281959 1924061 := bbase (se 3 (by rfl) ⟨360761, by rfl⟩ : syracuseStep 1924061 = 721523) (by norm_num)
theorem B1924085 : Blo 1281959 1924085 := bbase (se 5 (by rfl) ⟨90191, by rfl⟩ : syracuseStep 1924085 = 180383) (by norm_num)
theorem B1924109 : Blo 1281959 1924109 := bbase (se 3 (by rfl) ⟨360770, by rfl⟩ : syracuseStep 1924109 = 721541) (by norm_num)
theorem B1924133 : Blo 1281959 1924133 := bbase (se 4 (by rfl) ⟨180387, by rfl⟩ : syracuseStep 1924133 = 360775) (by norm_num)
theorem B4332581 : Blo 1281959 4332581 := bbase (se 4 (by rfl) ⟨406179, by rfl⟩ : syracuseStep 4332581 = 812359) (by norm_num)
theorem B1924157 : Blo 1281959 1924157 := bbase (se 3 (by rfl) ⟨360779, by rfl⟩ : syracuseStep 1924157 = 721559) (by norm_num)
theorem B3513413 : Blo 1281959 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B1317961 : Blo 1281959 1317961 := bbase (se 2 (by rfl) ⟨494235, by rfl⟩ : syracuseStep 1317961 = 988471) (by norm_num)
theorem B1924181 : Blo 1281959 1924181 := bbase (se 8 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 1924181 = 22549) (by norm_num)
theorem B1924205 : Blo 1281959 1924205 := bbase (se 3 (by rfl) ⟨360788, by rfl⟩ : syracuseStep 1924205 = 721577) (by norm_num)
theorem B1924229 : Blo 1281959 1924229 := bbase (se 4 (by rfl) ⟨180396, by rfl⟩ : syracuseStep 1924229 = 360793) (by norm_num)
theorem B4168837 : Blo 1281959 4168837 := bbase (se 4 (by rfl) ⟨390828, by rfl⟩ : syracuseStep 4168837 = 781657) (by norm_num)
theorem B1924253 : Blo 1281959 1924253 := bbase (se 3 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 1924253 = 721595) (by norm_num)
theorem B1924277 : Blo 1281959 1924277 := bbase (se 5 (by rfl) ⟨90200, by rfl⟩ : syracuseStep 1924277 = 180401) (by norm_num)
theorem B1924301 : Blo 1281959 1924301 := bbase (se 3 (by rfl) ⟨360806, by rfl⟩ : syracuseStep 1924301 = 721613) (by norm_num)
theorem B1924325 : Blo 1281959 1924325 := bbase (se 4 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 1924325 = 360811) (by norm_num)
theorem B2055413 : Blo 1281959 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B9747701 : Blo 1281959 9747701 := bbase (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) (by norm_num)
theorem B1924349 : Blo 1281959 1924349 := bbase (se 3 (by rfl) ⟨360815, by rfl⟩ : syracuseStep 1924349 = 721631) (by norm_num)
theorem B1924373 : Blo 1281959 1924373 := bbase (se 6 (by rfl) ⟨45102, by rfl⟩ : syracuseStep 1924373 = 90205) (by norm_num)
theorem B1482013 : Blo 1281959 1482013 := bbase (se 3 (by rfl) ⟨277877, by rfl⟩ : syracuseStep 1482013 = 555755) (by norm_num)
theorem B1826077 : Blo 1281959 1826077 := bbase (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) (by norm_num)
theorem B1924397 : Blo 1281959 1924397 := bbase (se 3 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 1924397 = 721649) (by norm_num)
theorem B1924421 : Blo 1281959 1924421 := bbase (se 4 (by rfl) ⟨180414, by rfl⟩ : syracuseStep 1924421 = 360829) (by norm_num)
theorem B7806293 : Blo 1281959 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B1924445 : Blo 1281959 1924445 := bbase (se 3 (by rfl) ⟨360833, by rfl⟩ : syracuseStep 1924445 = 721667) (by norm_num)
theorem B1924469 : Blo 1281959 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B2055541 : Blo 1281959 2055541 := bbase (se 5 (by rfl) ⟨96353, by rfl⟩ : syracuseStep 2055541 = 192707) (by norm_num)
theorem B1924493 : Blo 1281959 1924493 := bbase (se 3 (by rfl) ⟨360842, by rfl⟩ : syracuseStep 1924493 = 721685) (by norm_num)
theorem B1924517 : Blo 1281959 1924517 := bbase (se 4 (by rfl) ⟨180423, by rfl⟩ : syracuseStep 1924517 = 360847) (by norm_num)
theorem B1924541 : Blo 1281959 1924541 := bbase (se 3 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 1924541 = 721703) (by norm_num)
theorem B1924565 : Blo 1281959 1924565 := bbase (se 7 (by rfl) ⟨22553, by rfl⟩ : syracuseStep 1924565 = 45107) (by norm_num)
theorem B4333013 : Blo 1281959 4333013 := bbase (se 7 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 4333013 = 101555) (by norm_num)
theorem B1924589 : Blo 1281959 1924589 := bbase (se 3 (by rfl) ⟨360860, by rfl⟩ : syracuseStep 1924589 = 721721) (by norm_num)
theorem B1924613 : Blo 1281959 1924613 := bbase (se 4 (by rfl) ⟨180432, by rfl⟩ : syracuseStep 1924613 = 360865) (by norm_num)
theorem B1924637 : Blo 1281959 1924637 := bbase (se 3 (by rfl) ⟨360869, by rfl⟩ : syracuseStep 1924637 = 721739) (by norm_num)
theorem B1924661 : Blo 1281959 1924661 := bbase (se 5 (by rfl) ⟨90218, by rfl⟩ : syracuseStep 1924661 = 180437) (by norm_num)
theorem B1924685 : Blo 1281959 1924685 := bbase (se 3 (by rfl) ⟨360878, by rfl⟩ : syracuseStep 1924685 = 721757) (by norm_num)
theorem B1924709 : Blo 1281959 1924709 := bbase (se 4 (by rfl) ⟨180441, by rfl⟩ : syracuseStep 1924709 = 360883) (by norm_num)
theorem B1949309 : Blo 1281959 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B1924733 : Blo 1281959 1924733 := bbase (se 3 (by rfl) ⟨360887, by rfl⟩ : syracuseStep 1924733 = 721775) (by norm_num)
theorem B4112005 : Blo 1281959 4112005 := bbase (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) (by norm_num)
theorem B9739925 : Blo 1281959 9739925 := bbase (se 6 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 9739925 = 456559) (by norm_num)
theorem B1924757 : Blo 1281959 1924757 := bbase (se 6 (by rfl) ⟨45111, by rfl⟩ : syracuseStep 1924757 = 90223) (by norm_num)
theorem B1924781 : Blo 1281959 1924781 := bbase (se 3 (by rfl) ⟨360896, by rfl⟩ : syracuseStep 1924781 = 721793) (by norm_num)
theorem B2924221 : Blo 1281959 2924221 := bbase (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) (by norm_num)
theorem B1924805 : Blo 1281959 1924805 := bbase (se 4 (by rfl) ⟨180450, by rfl⟩ : syracuseStep 1924805 = 360901) (by norm_num)
theorem B1924829 : Blo 1281959 1924829 := bbase (se 3 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 1924829 = 721811) (by norm_num)
theorem B1924853 : Blo 1281959 1924853 := bbase (se 5 (by rfl) ⟨90227, by rfl⟩ : syracuseStep 1924853 = 180455) (by norm_num)
theorem B1924877 : Blo 1281959 1924877 := bbase (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) (by norm_num)
theorem B6496037 : Blo 1281959 6496037 := bbase (se 4 (by rfl) ⟨609003, by rfl⟩ : syracuseStep 6496037 = 1218007) (by norm_num)
theorem B1924901 : Blo 1281959 1924901 := bbase (se 4 (by rfl) ⟨180459, by rfl⟩ : syracuseStep 1924901 = 360919) (by norm_num)
theorem B1924925 : Blo 1281959 1924925 := bbase (se 3 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 1924925 = 721847) (by norm_num)
theorem B1924949 : Blo 1281959 1924949 := bbase (se 9 (by rfl) ⟨5639, by rfl⟩ : syracuseStep 1924949 = 11279) (by norm_num)
theorem B1826669 : Blo 1281959 1826669 := bbase (se 3 (by rfl) ⟨342500, by rfl⟩ : syracuseStep 1826669 = 685001) (by norm_num)
theorem B1924973 : Blo 1281959 1924973 := bbase (se 3 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 1924973 = 721865) (by norm_num)
theorem B3383165 : Blo 1281959 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B1924997 : Blo 1281959 1924997 := bbase (se 4 (by rfl) ⟨180468, by rfl⟩ : syracuseStep 1924997 = 360937) (by norm_num)
theorem B1925021 : Blo 1281959 1925021 := bbase (se 3 (by rfl) ⟨360941, by rfl⟩ : syracuseStep 1925021 = 721883) (by norm_num)
theorem B1925045 : Blo 1281959 1925045 := bbase (se 5 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 1925045 = 180473) (by norm_num)
theorem B1826749 : Blo 1281959 1826749 := bbase (se 3 (by rfl) ⟨342515, by rfl⟩ : syracuseStep 1826749 = 685031) (by norm_num)
theorem B3702725 : Blo 1281959 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B6586309 : Blo 1281959 6586309 := bbase (se 4 (by rfl) ⟨617466, by rfl⟩ : syracuseStep 6586309 = 1234933) (by norm_num)
theorem B1925069 : Blo 1281959 1925069 := bbase (se 3 (by rfl) ⟨360950, by rfl⟩ : syracuseStep 1925069 = 721901) (by norm_num)
theorem B1925093 : Blo 1281959 1925093 := bbase (se 4 (by rfl) ⟨180477, by rfl⟩ : syracuseStep 1925093 = 360955) (by norm_num)
theorem B1925117 : Blo 1281959 1925117 := bbase (se 3 (by rfl) ⟨360959, by rfl⟩ : syracuseStep 1925117 = 721919) (by norm_num)
theorem B1925123 : Blo 1281959 1925123 := bstep (se 1 (by rfl) ⟨1443842, by rfl⟩ : syracuseStep 1925123 = 2887685) B2887685
theorem B1925153 : Blo 1281959 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1925171 : Blo 1281959 1925171 := bstep (se 1 (by rfl) ⟨1443878, by rfl⟩ : syracuseStep 1925171 = 2887757) B2887757
theorem B1925201 : Blo 1281959 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B1925219 : Blo 1281959 1925219 := bstep (se 1 (by rfl) ⟨1443914, by rfl⟩ : syracuseStep 1925219 = 2887829) B2887829
theorem B1925249 : Blo 1281959 1925249 := bstep (se 2 (by rfl) ⟨721968, by rfl⟩ : syracuseStep 1925249 = 1443937) B1443937
theorem B7307405 : Blo 1281959 7307405 := bstep (se 3 (by rfl) ⟨1370138, by rfl⟩ : syracuseStep 7307405 = 2740277) B2740277
theorem B8781965 : Blo 1281959 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B1925267 : Blo 1281959 1925267 := bstep (se 1 (by rfl) ⟨1443950, by rfl⟩ : syracuseStep 1925267 = 2887901) B2887901
theorem B1826977 : Blo 1281959 1826977 := bstep (se 2 (by rfl) ⟨685116, by rfl⟩ : syracuseStep 1826977 = 1370233) B1370233
theorem B1925297 : Blo 1281959 1925297 := bstep (se 2 (by rfl) ⟨721986, by rfl⟩ : syracuseStep 1925297 = 1443973) B1443973
theorem B1925315 : Blo 1281959 1925315 := bstep (se 1 (by rfl) ⟨1443986, by rfl⟩ : syracuseStep 1925315 = 2887973) B2887973
theorem B1925345 : Blo 1281959 1925345 := bstep (se 2 (by rfl) ⟨722004, by rfl⟩ : syracuseStep 1925345 = 1444009) B1444009
theorem B1925363 : Blo 1281959 1925363 := bstep (se 1 (by rfl) ⟨1444022, by rfl⟩ : syracuseStep 1925363 = 2888045) B2888045
theorem B1925393 : Blo 1281959 1925393 := bstep (se 2 (by rfl) ⟨722022, by rfl⟩ : syracuseStep 1925393 = 1444045) B1444045
theorem B1925411 : Blo 1281959 1925411 := bstep (se 1 (by rfl) ⟨1444058, by rfl⟩ : syracuseStep 1925411 = 2888117) B2888117
theorem B1925441 : Blo 1281959 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B1925459 : Blo 1281959 1925459 := bstep (se 1 (by rfl) ⟨1444094, by rfl⟩ : syracuseStep 1925459 = 2888189) B2888189
theorem B1925489 : Blo 1281959 1925489 := bstep (se 2 (by rfl) ⟨722058, by rfl⟩ : syracuseStep 1925489 = 1444117) B1444117
theorem B1925507 : Blo 1281959 1925507 := bstep (se 1 (by rfl) ⟨1444130, by rfl⟩ : syracuseStep 1925507 = 2888261) B2888261
theorem B7029125 : Blo 1281959 7029125 := bstep (se 4 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 7029125 = 1317961) B1317961
theorem B1925537 : Blo 1281959 1925537 := bstep (se 2 (by rfl) ⟨722076, by rfl⟩ : syracuseStep 1925537 = 1444153) B1444153
theorem B1442227 : Blo 1281959 1442227 := bstep (se 1 (by rfl) ⟨1081670, by rfl⟩ : syracuseStep 1442227 = 2163341) B2163341
theorem B1925555 : Blo 1281959 1925555 := bstep (se 1 (by rfl) ⟨1444166, by rfl⟩ : syracuseStep 1925555 = 2888333) B2888333
theorem B7799237 : Blo 1281959 7799237 := bstep (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) B1462357
theorem B4874701 : Blo 1281959 4874701 := bstep (se 3 (by rfl) ⟨914006, by rfl⟩ : syracuseStep 4874701 = 1828013) B1828013
theorem B1925585 : Blo 1281959 1925585 := bstep (se 2 (by rfl) ⟨722094, by rfl⟩ : syracuseStep 1925585 = 1444189) B1444189
theorem B1925603 : Blo 1281959 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1925633 : Blo 1281959 1925633 := bstep (se 2 (by rfl) ⟨722112, by rfl⟩ : syracuseStep 1925633 = 1444225) B1444225
theorem B1622531 : Blo 1281959 1622531 := bstep (se 1 (by rfl) ⟨1216898, by rfl⟩ : syracuseStep 1622531 = 2433797) B2433797
theorem B1925651 : Blo 1281959 1925651 := bstep (se 1 (by rfl) ⟨1444238, by rfl⟩ : syracuseStep 1925651 = 2888477) B2888477
theorem B3654193 : Blo 1281959 3654193 := bstep (se 2 (by rfl) ⟨1370322, by rfl⟩ : syracuseStep 3654193 = 2740645) B2740645
theorem B1925681 : Blo 1281959 1925681 := bstep (se 2 (by rfl) ⟨722130, by rfl⟩ : syracuseStep 1925681 = 1444261) B1444261
theorem B1442371 : Blo 1281959 1442371 := bstep (se 1 (by rfl) ⟨1081778, by rfl⟩ : syracuseStep 1442371 = 2163557) B2163557
theorem B1925699 : Blo 1281959 1925699 := bstep (se 1 (by rfl) ⟨1444274, by rfl⟩ : syracuseStep 1925699 = 2888549) B2888549
theorem B1925729 : Blo 1281959 1925729 := bstep (se 2 (by rfl) ⟨722148, by rfl⟩ : syracuseStep 1925729 = 1444297) B1444297
theorem B1925747 : Blo 1281959 1925747 := bstep (se 1 (by rfl) ⟨1444310, by rfl⟩ : syracuseStep 1925747 = 2888621) B2888621
theorem B5481101 : Blo 1281959 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B1925777 : Blo 1281959 1925777 := bstep (se 2 (by rfl) ⟨722166, by rfl⟩ : syracuseStep 1925777 = 1444333) B1444333
theorem B2163361 : Blo 1281959 2163361 := bstep (se 2 (by rfl) ⟨811260, by rfl⟩ : syracuseStep 2163361 = 1622521) B1622521
theorem B1925795 : Blo 1281959 1925795 := bstep (se 1 (by rfl) ⟨1444346, by rfl⟩ : syracuseStep 1925795 = 2888693) B2888693
theorem B2163395 : Blo 1281959 2163395 := bstep (se 1 (by rfl) ⟨1622546, by rfl⟩ : syracuseStep 2163395 = 3245093) B3245093
theorem B1925825 : Blo 1281959 1925825 := bstep (se 2 (by rfl) ⟨722184, by rfl⟩ : syracuseStep 1925825 = 1444369) B1444369
theorem B1442515 : Blo 1281959 1442515 := bstep (se 1 (by rfl) ⟨1081886, by rfl⟩ : syracuseStep 1442515 = 2163773) B2163773
theorem B1925843 : Blo 1281959 1925843 := bstep (se 1 (by rfl) ⟨1444382, by rfl⟩ : syracuseStep 1925843 = 2888765) B2888765
theorem B6497009 : Blo 1281959 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1827569 : Blo 1281959 1827569 := bstep (se 2 (by rfl) ⟨685338, by rfl⟩ : syracuseStep 1827569 = 1370677) B1370677
theorem B1925873 : Blo 1281959 1925873 := bstep (se 2 (by rfl) ⟨722202, by rfl⟩ : syracuseStep 1925873 = 1444405) B1444405
theorem B1925891 : Blo 1281959 1925891 := bstep (se 1 (by rfl) ⟨1444418, by rfl⟩ : syracuseStep 1925891 = 2888837) B2888837
theorem B8225549 : Blo 1281959 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B1925921 : Blo 1281959 1925921 := bstep (se 2 (by rfl) ⟨722220, by rfl⟩ : syracuseStep 1925921 = 1444441) B1444441
theorem B2433827 : Blo 1281959 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B8782627 : Blo 1281959 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B1925939 : Blo 1281959 1925939 := bstep (se 1 (by rfl) ⟨1444454, by rfl⟩ : syracuseStep 1925939 = 2888909) B2888909
theorem B2163523 : Blo 1281959 2163523 := bstep (se 1 (by rfl) ⟨1622642, by rfl⟩ : syracuseStep 2163523 = 3245285) B3245285
theorem B3654467 : Blo 1281959 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B1442659 : Blo 1281959 1442659 := bstep (se 1 (by rfl) ⟨1081994, by rfl⟩ : syracuseStep 1442659 = 2163989) B2163989
theorem B3081073 : Blo 1281959 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B5202829 : Blo 1281959 5202829 := bstep (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) B1951061
theorem B2163665 : Blo 1281959 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1442803 : Blo 1281959 1442803 := bstep (se 1 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 1442803 = 2164205) B2164205
theorem B2925571 : Blo 1281959 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B3654659 : Blo 1281959 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B2884625 : Blo 1281959 2884625 := bstep (se 2 (by rfl) ⟨1081734, by rfl⟩ : syracuseStep 2884625 = 2163469) B2163469
theorem B2884643 : Blo 1281959 2884643 := bstep (se 1 (by rfl) ⟨2163482, by rfl⟩ : syracuseStep 2884643 = 4326965) B4326965
theorem B1950769 : Blo 1281959 1950769 := bstep (se 2 (by rfl) ⟨731538, by rfl⟩ : syracuseStep 1950769 = 1463077) B1463077
theorem B3245123 : Blo 1281959 3245123 := bstep (se 1 (by rfl) ⟨2433842, by rfl⟩ : syracuseStep 3245123 = 4867685) B4867685
theorem B2163793 : Blo 1281959 2163793 := bstep (se 2 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 2163793 = 1622845) B1622845
theorem B2311267 : Blo 1281959 2311267 := bstep (se 1 (by rfl) ⟨1733450, by rfl⟩ : syracuseStep 2311267 = 3466901) B3466901
theorem B2163827 : Blo 1281959 2163827 := bstep (se 1 (by rfl) ⟨1622870, by rfl⟩ : syracuseStep 2163827 = 3245741) B3245741
theorem B1442947 : Blo 1281959 1442947 := bstep (se 1 (by rfl) ⟨1082210, by rfl⟩ : syracuseStep 1442947 = 2164421) B2164421
theorem B9749645 : Blo 1281959 9749645 := bstep (se 3 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 9749645 = 3656117) B3656117
theorem B1369267 : Blo 1281959 1369267 := bstep (se 1 (by rfl) ⟨1026950, by rfl⟩ : syracuseStep 1369267 = 2053901) B2053901
theorem B1623235 : Blo 1281959 1623235 := bstep (se 1 (by rfl) ⟨1217426, by rfl⟩ : syracuseStep 1623235 = 2434853) B2434853
theorem B21931235 : Blo 1281959 21931235 := bstep (se 1 (by rfl) ⟨16448426, by rfl⟩ : syracuseStep 21931235 = 32896853) B32896853
theorem B4326641 : Blo 1281959 4326641 := bstep (se 2 (by rfl) ⟨1622490, by rfl⟩ : syracuseStep 4326641 = 3244981) B3244981
theorem B2163955 : Blo 1281959 2163955 := bstep (se 1 (by rfl) ⟨1622966, by rfl⟩ : syracuseStep 2163955 = 3245933) B3245933
theorem B1828099 : Blo 1281959 1828099 := bstep (se 1 (by rfl) ⟨1371074, by rfl⟩ : syracuseStep 1828099 = 2742149) B2742149
theorem B1443091 : Blo 1281959 1443091 := bstep (se 1 (by rfl) ⟨1082318, by rfl⟩ : syracuseStep 1443091 = 2164637) B2164637
theorem B1623331 : Blo 1281959 1623331 := bstep (se 1 (by rfl) ⟨1217498, by rfl⟩ : syracuseStep 1623331 = 2434997) B2434997
theorem B2884913 : Blo 1281959 2884913 := bstep (se 2 (by rfl) ⟨1081842, by rfl⟩ : syracuseStep 2884913 = 2163685) B2163685
theorem B1951025 : Blo 1281959 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1852723 : Blo 1281959 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B20792629 : Blo 1281959 20792629 := bstep (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) B1949309
theorem B16434485 : Blo 1281959 16434485 := bstep (se 5 (by rfl) ⟨770366, by rfl⟩ : syracuseStep 16434485 = 1540733) B1540733
theorem B2884931 : Blo 1281959 2884931 := bstep (se 1 (by rfl) ⟨2163698, by rfl⟩ : syracuseStep 2884931 = 4327397) B4327397
theorem B2164097 : Blo 1281959 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B33326477 : Blo 1281959 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B1951123 : Blo 1281959 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B1443235 : Blo 1281959 1443235 := bstep (se 1 (by rfl) ⟨1082426, by rfl⟩ : syracuseStep 1443235 = 2164853) B2164853
theorem B11699653 : Blo 1281959 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B2164225 : Blo 1281959 2164225 := bstep (se 2 (by rfl) ⟨811584, by rfl⟩ : syracuseStep 2164225 = 1623169) B1623169
theorem B6161933 : Blo 1281959 6161933 := bstep (se 3 (by rfl) ⟨1155362, by rfl⟩ : syracuseStep 6161933 = 2310725) B2310725
theorem B2164259 : Blo 1281959 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B1443379 : Blo 1281959 1443379 := bstep (se 1 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 1443379 = 2165069) B2165069
theorem B2885201 : Blo 1281959 2885201 := bstep (se 2 (by rfl) ⟨1081950, by rfl⟩ : syracuseStep 2885201 = 2163901) B2163901
theorem B2885219 : Blo 1281959 2885219 := bstep (se 1 (by rfl) ⟨2163914, by rfl⟩ : syracuseStep 2885219 = 4327829) B4327829
theorem B53380721 : Blo 1281959 53380721 := bstep (se 2 (by rfl) ⟨20017770, by rfl⟩ : syracuseStep 53380721 = 40035541) B40035541
theorem B19744397 : Blo 1281959 19744397 := bstep (se 3 (by rfl) ⟨3702074, by rfl⟩ : syracuseStep 19744397 = 7404149) B7404149
theorem B2164387 : Blo 1281959 2164387 := bstep (se 1 (by rfl) ⟨1623290, by rfl⟩ : syracuseStep 2164387 = 3246581) B3246581
theorem B1443523 : Blo 1281959 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B2434769 : Blo 1281959 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B8775395 : Blo 1281959 8775395 := bstep (se 1 (by rfl) ⟨6581546, by rfl⟩ : syracuseStep 8775395 = 13163093) B13163093
theorem B2311907 : Blo 1281959 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B7128803 : Blo 1281959 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B4327181 : Blo 1281959 4327181 := bstep (se 3 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 4327181 = 1622693) B1622693
theorem B2737937 : Blo 1281959 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B1623827 : Blo 1281959 1623827 := bstep (se 1 (by rfl) ⟨1217870, by rfl⟩ : syracuseStep 1623827 = 2435741) B2435741
theorem B3655469 : Blo 1281959 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B2164529 : Blo 1281959 2164529 := bstep (se 2 (by rfl) ⟨811698, by rfl⟩ : syracuseStep 2164529 = 1623397) B1623397
theorem B4327235 : Blo 1281959 4327235 := bstep (se 1 (by rfl) ⟨3245426, by rfl⟩ : syracuseStep 4327235 = 6490853) B6490853
theorem B1443667 : Blo 1281959 1443667 := bstep (se 1 (by rfl) ⟨1082750, by rfl⟩ : syracuseStep 1443667 = 2165501) B2165501
theorem B2885489 : Blo 1281959 2885489 := bstep (se 2 (by rfl) ⟨1082058, by rfl⟩ : syracuseStep 2885489 = 2164117) B2164117
theorem B2885507 : Blo 1281959 2885507 := bstep (se 1 (by rfl) ⟨2164130, by rfl⟩ : syracuseStep 2885507 = 4328261) B4328261
theorem B2312081 : Blo 1281959 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2164657 : Blo 1281959 2164657 := bstep (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) B1623493
theorem B2164691 : Blo 1281959 2164691 := bstep (se 1 (by rfl) ⟨1623518, by rfl⟩ : syracuseStep 2164691 = 3247037) B3247037
theorem B1443811 : Blo 1281959 1443811 := bstep (se 1 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 1443811 = 2165717) B2165717
theorem B3655651 : Blo 1281959 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B3246065 : Blo 1281959 3246065 := bstep (se 2 (by rfl) ⟨1217274, by rfl⟩ : syracuseStep 3246065 = 2434549) B2434549
theorem B3246115 : Blo 1281959 3246115 := bstep (se 1 (by rfl) ⟨2434586, by rfl⟩ : syracuseStep 3246115 = 4869173) B4869173
theorem B4327505 : Blo 1281959 4327505 := bstep (se 2 (by rfl) ⟨1622814, by rfl⟩ : syracuseStep 4327505 = 3245629) B3245629
theorem B2164819 : Blo 1281959 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B1443955 : Blo 1281959 1443955 := bstep (se 1 (by rfl) ⟨1082966, by rfl⟩ : syracuseStep 1443955 = 2165933) B2165933
theorem B2885777 : Blo 1281959 2885777 := bstep (se 2 (by rfl) ⟨1082166, by rfl⟩ : syracuseStep 2885777 = 2164333) B2164333
theorem B3336337 : Blo 1281959 3336337 := bstep (se 2 (by rfl) ⟨1251126, by rfl⟩ : syracuseStep 3336337 = 2502253) B2502253
theorem B2885795 : Blo 1281959 2885795 := bstep (se 1 (by rfl) ⟨2164346, by rfl⟩ : syracuseStep 2885795 = 4328693) B4328693
theorem B6498467 : Blo 1281959 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B3246257 : Blo 1281959 3246257 := bstep (se 2 (by rfl) ⟨1217346, by rfl⟩ : syracuseStep 3246257 = 2434693) B2434693
theorem B5482673 : Blo 1281959 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B2164961 : Blo 1281959 2164961 := bstep (se 2 (by rfl) ⟨811860, by rfl⟩ : syracuseStep 2164961 = 1623721) B1623721
theorem B5204195 : Blo 1281959 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1444099 : Blo 1281959 1444099 := bstep (se 1 (by rfl) ⟨1083074, by rfl⟩ : syracuseStep 1444099 = 2166149) B2166149
theorem B9021773 : Blo 1281959 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B2165089 : Blo 1281959 2165089 := bstep (se 2 (by rfl) ⟨811908, by rfl⟩ : syracuseStep 2165089 = 1623817) B1623817
theorem B2165123 : Blo 1281959 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B1444243 : Blo 1281959 1444243 := bstep (se 1 (by rfl) ⟨1083182, by rfl⟩ : syracuseStep 1444243 = 2166365) B2166365
theorem B2886065 : Blo 1281959 2886065 := bstep (se 2 (by rfl) ⟨1082274, by rfl⟩ : syracuseStep 2886065 = 2164549) B2164549
theorem B2886083 : Blo 1281959 2886083 := bstep (se 1 (by rfl) ⟨2164562, by rfl⟩ : syracuseStep 2886083 = 4329125) B4329125
theorem B7301573 : Blo 1281959 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B3656141 : Blo 1281959 3656141 := bstep (se 3 (by rfl) ⟨685526, by rfl⟩ : syracuseStep 3656141 = 1371053) B1371053
theorem B1624531 : Blo 1281959 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B2165251 : Blo 1281959 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B8219141 : Blo 1281959 8219141 := bstep (se 4 (by rfl) ⟨770544, by rfl⟩ : syracuseStep 8219141 = 1541089) B1541089
theorem B16443917 : Blo 1281959 16443917 := bstep (se 3 (by rfl) ⟨3083234, by rfl⟩ : syracuseStep 16443917 = 6166469) B6166469
theorem B7801379 : Blo 1281959 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B1444387 : Blo 1281959 1444387 := bstep (se 1 (by rfl) ⟨1083290, by rfl⟩ : syracuseStep 1444387 = 2166581) B2166581
theorem B4868657 : Blo 1281959 4868657 := bstep (se 2 (by rfl) ⟨1825746, by rfl⟩ : syracuseStep 4868657 = 3651493) B3651493
theorem B1624627 : Blo 1281959 1624627 := bstep (se 1 (by rfl) ⟨1218470, by rfl⟩ : syracuseStep 1624627 = 2436941) B2436941
theorem B2435665 : Blo 1281959 2435665 := bstep (se 2 (by rfl) ⟨913374, by rfl⟩ : syracuseStep 2435665 = 1826749) B1826749
theorem B4328045 : Blo 1281959 4328045 := bstep (se 3 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 4328045 = 1623017) B1623017
theorem B2468483 : Blo 1281959 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B2165393 : Blo 1281959 2165393 := bstep (se 2 (by rfl) ⟨812022, by rfl⟩ : syracuseStep 2165393 = 1624045) B1624045
theorem B4328099 : Blo 1281959 4328099 := bstep (se 1 (by rfl) ⟨3246074, by rfl⟩ : syracuseStep 4328099 = 6492149) B6492149
theorem B2886353 : Blo 1281959 2886353 := bstep (se 2 (by rfl) ⟨1082382, by rfl⟩ : syracuseStep 2886353 = 2164765) B2164765
theorem B2886371 : Blo 1281959 2886371 := bstep (se 1 (by rfl) ⟨2164778, by rfl⟩ : syracuseStep 2886371 = 4329557) B4329557
theorem B2435825 : Blo 1281959 2435825 := bstep (se 2 (by rfl) ⟨913434, by rfl⟩ : syracuseStep 2435825 = 1826869) B1826869
theorem B2165521 : Blo 1281959 2165521 := bstep (se 2 (by rfl) ⟨812070, by rfl⟩ : syracuseStep 2165521 = 1624141) B1624141
theorem B2165555 : Blo 1281959 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B6253453 : Blo 1281959 6253453 := bstep (se 3 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 6253453 = 2345045) B2345045
theorem B4328369 : Blo 1281959 4328369 := bstep (se 2 (by rfl) ⟨1623138, by rfl⟩ : syracuseStep 4328369 = 3246277) B3246277
theorem B2165683 : Blo 1281959 2165683 := bstep (se 1 (by rfl) ⟨1624262, by rfl⟩ : syracuseStep 2165683 = 3248525) B3248525
theorem B6499277 : Blo 1281959 6499277 := bstep (se 3 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 6499277 = 2437229) B2437229
theorem B19753955 : Blo 1281959 19753955 := bstep (se 1 (by rfl) ⟨14815466, by rfl⟩ : syracuseStep 19753955 = 29630933) B29630933
theorem B2886641 : Blo 1281959 2886641 := bstep (se 2 (by rfl) ⟨1082490, by rfl⟩ : syracuseStep 2886641 = 2164981) B2164981
theorem B7310321 : Blo 1281959 7310321 := bstep (se 2 (by rfl) ⟨2741370, by rfl⟩ : syracuseStep 7310321 = 5482741) B5482741
theorem B2886659 : Blo 1281959 2886659 := bstep (se 1 (by rfl) ⟨2164994, by rfl⟩ : syracuseStep 2886659 = 4329989) B4329989
theorem B4107277 : Blo 1281959 4107277 := bstep (se 3 (by rfl) ⟨770114, by rfl⟩ : syracuseStep 4107277 = 1540229) B1540229
theorem B2165825 : Blo 1281959 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B4107341 : Blo 1281959 4107341 := bstep (se 3 (by rfl) ⟨770126, by rfl⟩ : syracuseStep 4107341 = 1540253) B1540253
theorem B7302257 : Blo 1281959 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B2436227 : Blo 1281959 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B3124369 : Blo 1281959 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B3247249 : Blo 1281959 3247249 := bstep (se 2 (by rfl) ⟨1217718, by rfl⟩ : syracuseStep 3247249 = 2435437) B2435437
theorem B2165953 : Blo 1281959 2165953 := bstep (se 2 (by rfl) ⟨812232, by rfl⟩ : syracuseStep 2165953 = 1624465) B1624465
theorem B2165987 : Blo 1281959 2165987 := bstep (se 1 (by rfl) ⟨1624490, by rfl⟩ : syracuseStep 2165987 = 3248981) B3248981
theorem B2886929 : Blo 1281959 2886929 := bstep (se 2 (by rfl) ⟨1082598, by rfl⟩ : syracuseStep 2886929 = 2165197) B2165197
theorem B2886947 : Blo 1281959 2886947 := bstep (se 1 (by rfl) ⟨2165210, by rfl⟩ : syracuseStep 2886947 = 4330421) B4330421
theorem B2166115 : Blo 1281959 2166115 := bstep (se 1 (by rfl) ⟨1624586, by rfl⟩ : syracuseStep 2166115 = 3249173) B3249173
theorem B3247523 : Blo 1281959 3247523 := bstep (se 1 (by rfl) ⟨2435642, by rfl⟩ : syracuseStep 3247523 = 4871285) B4871285
theorem B9743813 : Blo 1281959 9743813 := bstep (se 4 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 9743813 = 1826965) B1826965
theorem B4328909 : Blo 1281959 4328909 := bstep (se 3 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 4328909 = 1623341) B1623341
theorem B2166257 : Blo 1281959 2166257 := bstep (se 2 (by rfl) ⟨812346, by rfl⟩ : syracuseStep 2166257 = 1624693) B1624693
theorem B4328963 : Blo 1281959 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B3468835 : Blo 1281959 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B2887217 : Blo 1281959 2887217 := bstep (se 2 (by rfl) ⟨1082706, by rfl⟩ : syracuseStep 2887217 = 2165413) B2165413
theorem B2887235 : Blo 1281959 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B3247715 : Blo 1281959 3247715 := bstep (se 1 (by rfl) ⟨2435786, by rfl⟩ : syracuseStep 3247715 = 4871573) B4871573
theorem B3468899 : Blo 1281959 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B2166385 : Blo 1281959 2166385 := bstep (se 2 (by rfl) ⟨812394, by rfl⟩ : syracuseStep 2166385 = 1624789) B1624789
theorem B2166419 : Blo 1281959 2166419 := bstep (se 1 (by rfl) ⟨1624814, by rfl⟩ : syracuseStep 2166419 = 3249629) B3249629
theorem B6491825 : Blo 1281959 6491825 := bstep (se 2 (by rfl) ⟨2434434, by rfl⟩ : syracuseStep 6491825 = 4868869) B4868869
theorem B4329233 : Blo 1281959 4329233 := bstep (se 2 (by rfl) ⟨1623462, by rfl⟩ : syracuseStep 4329233 = 3246925) B3246925
theorem B2166547 : Blo 1281959 2166547 := bstep (se 1 (by rfl) ⟨1624910, by rfl⟩ : syracuseStep 2166547 = 3249821) B3249821
theorem B2887505 : Blo 1281959 2887505 := bstep (se 2 (by rfl) ⟨1082814, by rfl⟩ : syracuseStep 2887505 = 2165629) B2165629
theorem B2887523 : Blo 1281959 2887523 := bstep (se 1 (by rfl) ⟨2165642, by rfl⟩ : syracuseStep 2887523 = 4331285) B4331285
theorem B1281971 : Blo 1281959 1281971 := bstep (se 1 (by rfl) ⟨961478, by rfl⟩ : syracuseStep 1281971 = 1922957) B1922957
theorem B1281987 : Blo 1281959 1281987 := bstep (se 1 (by rfl) ⟨961490, by rfl⟩ : syracuseStep 1281987 = 1922981) B1922981
theorem B3903437 : Blo 1281959 3903437 := bstep (se 3 (by rfl) ⟨731894, by rfl⟩ : syracuseStep 3903437 = 1463789) B1463789
theorem B1282003 : Blo 1281959 1282003 := bstep (se 1 (by rfl) ⟨961502, by rfl⟩ : syracuseStep 1282003 = 1923005) B1923005
theorem B1282019 : Blo 1281959 1282019 := bstep (se 1 (by rfl) ⟨961514, by rfl⟩ : syracuseStep 1282019 = 1923029) B1923029
theorem B20795363 : Blo 1281959 20795363 := bstep (se 1 (by rfl) ⟨15596522, by rfl⟩ : syracuseStep 20795363 = 31193045) B31193045
theorem B4870115 : Blo 1281959 4870115 := bstep (se 1 (by rfl) ⟨3652586, by rfl⟩ : syracuseStep 4870115 = 7305173) B7305173
theorem B1282035 : Blo 1281959 1282035 := bstep (se 1 (by rfl) ⟨961526, by rfl⟩ : syracuseStep 1282035 = 1923053) B1923053
theorem B1282051 : Blo 1281959 1282051 := bstep (se 1 (by rfl) ⟨961538, by rfl⟩ : syracuseStep 1282051 = 1923077) B1923077
theorem B2437123 : Blo 1281959 2437123 := bstep (se 1 (by rfl) ⟨1827842, by rfl⟩ : syracuseStep 2437123 = 3655685) B3655685
theorem B1282067 : Blo 1281959 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B1282083 : Blo 1281959 1282083 := bstep (se 1 (by rfl) ⟨961562, by rfl⟩ : syracuseStep 1282083 = 1923125) B1923125
theorem B1282099 : Blo 1281959 1282099 := bstep (se 1 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 1282099 = 1923149) B1923149
theorem B1282115 : Blo 1281959 1282115 := bstep (se 1 (by rfl) ⟨961586, by rfl⟩ : syracuseStep 1282115 = 1923173) B1923173
theorem B6582349 : Blo 1281959 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B1282131 : Blo 1281959 1282131 := bstep (se 1 (by rfl) ⟨961598, by rfl⟩ : syracuseStep 1282131 = 1923197) B1923197
theorem B1282147 : Blo 1281959 1282147 := bstep (se 1 (by rfl) ⟨961610, by rfl⟩ : syracuseStep 1282147 = 1923221) B1923221
theorem B2887793 : Blo 1281959 2887793 := bstep (se 2 (by rfl) ⟨1082922, by rfl⟩ : syracuseStep 2887793 = 2165845) B2165845
theorem B1282163 : Blo 1281959 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B1282179 : Blo 1281959 1282179 := bstep (se 1 (by rfl) ⟨961634, by rfl⟩ : syracuseStep 1282179 = 1923269) B1923269
theorem B2887811 : Blo 1281959 2887811 := bstep (se 1 (by rfl) ⟨2165858, by rfl⟩ : syracuseStep 2887811 = 4331717) B4331717
theorem B1282195 : Blo 1281959 1282195 := bstep (se 1 (by rfl) ⟨961646, by rfl⟩ : syracuseStep 1282195 = 1923293) B1923293
theorem B1282211 : Blo 1281959 1282211 := bstep (se 1 (by rfl) ⟨961658, by rfl⟩ : syracuseStep 1282211 = 1923317) B1923317
theorem B2437283 : Blo 1281959 2437283 := bstep (se 1 (by rfl) ⟨1827962, by rfl⟩ : syracuseStep 2437283 = 3655925) B3655925
theorem B5558449 : Blo 1281959 5558449 := bstep (se 2 (by rfl) ⟨2084418, by rfl⟩ : syracuseStep 5558449 = 4168837) B4168837
theorem B1282227 : Blo 1281959 1282227 := bstep (se 1 (by rfl) ⟨961670, by rfl⟩ : syracuseStep 1282227 = 1923341) B1923341
theorem B15225013 : Blo 1281959 15225013 := bstep (se 5 (by rfl) ⟨713672, by rfl⟩ : syracuseStep 15225013 = 1427345) B1427345
theorem B1282243 : Blo 1281959 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B1282259 : Blo 1281959 1282259 := bstep (se 1 (by rfl) ⟨961694, by rfl⟩ : syracuseStep 1282259 = 1923389) B1923389
theorem B1282275 : Blo 1281959 1282275 := bstep (se 1 (by rfl) ⟨961706, by rfl⟩ : syracuseStep 1282275 = 1923413) B1923413
theorem B1282291 : Blo 1281959 1282291 := bstep (se 1 (by rfl) ⟨961718, by rfl⟩ : syracuseStep 1282291 = 1923437) B1923437
theorem B1282307 : Blo 1281959 1282307 := bstep (se 1 (by rfl) ⟨961730, by rfl⟩ : syracuseStep 1282307 = 1923461) B1923461
theorem B1282323 : Blo 1281959 1282323 := bstep (se 1 (by rfl) ⟨961742, by rfl⟩ : syracuseStep 1282323 = 1923485) B1923485
theorem B5476643 : Blo 1281959 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B1282339 : Blo 1281959 1282339 := bstep (se 1 (by rfl) ⟨961754, by rfl⟩ : syracuseStep 1282339 = 1923509) B1923509
theorem B4329773 : Blo 1281959 4329773 := bstep (se 3 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 4329773 = 1623665) B1623665
theorem B1282355 : Blo 1281959 1282355 := bstep (se 1 (by rfl) ⟨961766, by rfl⟩ : syracuseStep 1282355 = 1923533) B1923533
theorem B1282371 : Blo 1281959 1282371 := bstep (se 1 (by rfl) ⟨961778, by rfl⟩ : syracuseStep 1282371 = 1923557) B1923557
theorem B1282387 : Blo 1281959 1282387 := bstep (se 1 (by rfl) ⟨961790, by rfl⟩ : syracuseStep 1282387 = 1923581) B1923581
theorem B1282403 : Blo 1281959 1282403 := bstep (se 1 (by rfl) ⟨961802, by rfl⟩ : syracuseStep 1282403 = 1923605) B1923605
theorem B4329827 : Blo 1281959 4329827 := bstep (se 1 (by rfl) ⟨3247370, by rfl⟩ : syracuseStep 4329827 = 6494741) B6494741
theorem B1282419 : Blo 1281959 1282419 := bstep (se 1 (by rfl) ⟨961814, by rfl⟩ : syracuseStep 1282419 = 1923629) B1923629
theorem B1282435 : Blo 1281959 1282435 := bstep (se 1 (by rfl) ⟨961826, by rfl⟩ : syracuseStep 1282435 = 1923653) B1923653
theorem B2888081 : Blo 1281959 2888081 := bstep (se 2 (by rfl) ⟨1083030, by rfl⟩ : syracuseStep 2888081 = 2166061) B2166061
theorem B1282451 : Blo 1281959 1282451 := bstep (se 1 (by rfl) ⟨961838, by rfl⟩ : syracuseStep 1282451 = 1923677) B1923677
theorem B1282467 : Blo 1281959 1282467 := bstep (se 1 (by rfl) ⟨961850, by rfl⟩ : syracuseStep 1282467 = 1923701) B1923701
theorem B2888099 : Blo 1281959 2888099 := bstep (se 1 (by rfl) ⟨2166074, by rfl⟩ : syracuseStep 2888099 = 4332149) B4332149
theorem B7311779 : Blo 1281959 7311779 := bstep (se 1 (by rfl) ⟨5483834, by rfl⟩ : syracuseStep 7311779 = 10967669) B10967669
theorem B1282483 : Blo 1281959 1282483 := bstep (se 1 (by rfl) ⟨961862, by rfl⟩ : syracuseStep 1282483 = 1923725) B1923725
theorem B1282499 : Blo 1281959 1282499 := bstep (se 1 (by rfl) ⟨961874, by rfl⟩ : syracuseStep 1282499 = 1923749) B1923749
theorem B1282515 : Blo 1281959 1282515 := bstep (se 1 (by rfl) ⟨961886, by rfl⟩ : syracuseStep 1282515 = 1923773) B1923773
theorem B1282531 : Blo 1281959 1282531 := bstep (se 1 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 1282531 = 1923797) B1923797
theorem B2740721 : Blo 1281959 2740721 := bstep (se 2 (by rfl) ⟨1027770, by rfl⟩ : syracuseStep 2740721 = 2055541) B2055541
theorem B1282547 : Blo 1281959 1282547 := bstep (se 1 (by rfl) ⟨961910, by rfl⟩ : syracuseStep 1282547 = 1923821) B1923821
theorem B1282563 : Blo 1281959 1282563 := bstep (se 1 (by rfl) ⟨961922, by rfl⟩ : syracuseStep 1282563 = 1923845) B1923845
theorem B3248657 : Blo 1281959 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B1282579 : Blo 1281959 1282579 := bstep (se 1 (by rfl) ⟨961934, by rfl⟩ : syracuseStep 1282579 = 1923869) B1923869
theorem B7303715 : Blo 1281959 7303715 := bstep (se 1 (by rfl) ⟨5477786, by rfl⟩ : syracuseStep 7303715 = 10955573) B10955573
theorem B1282595 : Blo 1281959 1282595 := bstep (se 1 (by rfl) ⟨961946, by rfl⟩ : syracuseStep 1282595 = 1923893) B1923893
theorem B3469873 : Blo 1281959 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1282611 : Blo 1281959 1282611 := bstep (se 1 (by rfl) ⟨961958, by rfl⟩ : syracuseStep 1282611 = 1923917) B1923917
theorem B1282627 : Blo 1281959 1282627 := bstep (se 1 (by rfl) ⟨961970, by rfl⟩ : syracuseStep 1282627 = 1923941) B1923941
theorem B3248707 : Blo 1281959 3248707 := bstep (se 1 (by rfl) ⟨2436530, by rfl⟩ : syracuseStep 3248707 = 4873061) B4873061
theorem B2224721 : Blo 1281959 2224721 := bstep (se 2 (by rfl) ⟨834270, by rfl⟩ : syracuseStep 2224721 = 1668541) B1668541
theorem B1282643 : Blo 1281959 1282643 := bstep (se 1 (by rfl) ⟨961982, by rfl⟩ : syracuseStep 1282643 = 1923965) B1923965
theorem B1282659 : Blo 1281959 1282659 := bstep (se 1 (by rfl) ⟨961994, by rfl⟩ : syracuseStep 1282659 = 1923989) B1923989
theorem B4330097 : Blo 1281959 4330097 := bstep (se 2 (by rfl) ⟨1623786, by rfl⟩ : syracuseStep 4330097 = 3247573) B3247573
theorem B1282675 : Blo 1281959 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B1282691 : Blo 1281959 1282691 := bstep (se 1 (by rfl) ⟨962018, by rfl⟩ : syracuseStep 1282691 = 1924037) B1924037
theorem B1282707 : Blo 1281959 1282707 := bstep (se 1 (by rfl) ⟨962030, by rfl⟩ : syracuseStep 1282707 = 1924061) B1924061
theorem B1282723 : Blo 1281959 1282723 := bstep (se 1 (by rfl) ⟨962042, by rfl⟩ : syracuseStep 1282723 = 1924085) B1924085
theorem B2888369 : Blo 1281959 2888369 := bstep (se 2 (by rfl) ⟨1083138, by rfl⟩ : syracuseStep 2888369 = 2166277) B2166277
theorem B1282739 : Blo 1281959 1282739 := bstep (se 1 (by rfl) ⟨962054, by rfl⟩ : syracuseStep 1282739 = 1924109) B1924109
theorem B1282755 : Blo 1281959 1282755 := bstep (se 1 (by rfl) ⟨962066, by rfl⟩ : syracuseStep 1282755 = 1924133) B1924133
theorem B2888387 : Blo 1281959 2888387 := bstep (se 1 (by rfl) ⟨2166290, by rfl⟩ : syracuseStep 2888387 = 4332581) B4332581
theorem B3248849 : Blo 1281959 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B1282771 : Blo 1281959 1282771 := bstep (se 1 (by rfl) ⟨962078, by rfl⟩ : syracuseStep 1282771 = 1924157) B1924157
theorem B7402211 : Blo 1281959 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B1282787 : Blo 1281959 1282787 := bstep (se 1 (by rfl) ⟨962090, by rfl⟩ : syracuseStep 1282787 = 1924181) B1924181
theorem B1282803 : Blo 1281959 1282803 := bstep (se 1 (by rfl) ⟨962102, by rfl⟩ : syracuseStep 1282803 = 1924205) B1924205
theorem B1282819 : Blo 1281959 1282819 := bstep (se 1 (by rfl) ⟨962114, by rfl⟩ : syracuseStep 1282819 = 1924229) B1924229
theorem B7803661 : Blo 1281959 7803661 := bstep (se 3 (by rfl) ⟨1463186, by rfl⟩ : syracuseStep 7803661 = 2926373) B2926373
theorem B1282835 : Blo 1281959 1282835 := bstep (se 1 (by rfl) ⟨962126, by rfl⟩ : syracuseStep 1282835 = 1924253) B1924253
theorem B1282851 : Blo 1281959 1282851 := bstep (se 1 (by rfl) ⟨962138, by rfl⟩ : syracuseStep 1282851 = 1924277) B1924277
theorem B1282867 : Blo 1281959 1282867 := bstep (se 1 (by rfl) ⟨962150, by rfl⟩ : syracuseStep 1282867 = 1924301) B1924301
theorem B4109123 : Blo 1281959 4109123 := bstep (se 1 (by rfl) ⟨3081842, by rfl⟩ : syracuseStep 4109123 = 6163685) B6163685
theorem B1282883 : Blo 1281959 1282883 := bstep (se 1 (by rfl) ⟨962162, by rfl⟩ : syracuseStep 1282883 = 1924325) B1924325
theorem B1282899 : Blo 1281959 1282899 := bstep (se 1 (by rfl) ⟨962174, by rfl⟩ : syracuseStep 1282899 = 1924349) B1924349
theorem B1282915 : Blo 1281959 1282915 := bstep (se 1 (by rfl) ⟨962186, by rfl⟩ : syracuseStep 1282915 = 1924373) B1924373
theorem B1282931 : Blo 1281959 1282931 := bstep (se 1 (by rfl) ⟨962198, by rfl⟩ : syracuseStep 1282931 = 1924397) B1924397
theorem B1282947 : Blo 1281959 1282947 := bstep (se 1 (by rfl) ⟨962210, by rfl⟩ : syracuseStep 1282947 = 1924421) B1924421
theorem B1282963 : Blo 1281959 1282963 := bstep (se 1 (by rfl) ⟨962222, by rfl⟩ : syracuseStep 1282963 = 1924445) B1924445
theorem B1282979 : Blo 1281959 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B1282995 : Blo 1281959 1282995 := bstep (se 1 (by rfl) ⟨962246, by rfl⟩ : syracuseStep 1282995 = 1924493) B1924493
theorem B1283011 : Blo 1281959 1283011 := bstep (se 1 (by rfl) ⟨962258, by rfl⟩ : syracuseStep 1283011 = 1924517) B1924517
theorem B4871117 : Blo 1281959 4871117 := bstep (se 3 (by rfl) ⟨913334, by rfl⟩ : syracuseStep 4871117 = 1826669) B1826669
theorem B2888657 : Blo 1281959 2888657 := bstep (se 2 (by rfl) ⟨1083246, by rfl⟩ : syracuseStep 2888657 = 2166493) B2166493
theorem B1283027 : Blo 1281959 1283027 := bstep (se 1 (by rfl) ⟨962270, by rfl⟩ : syracuseStep 1283027 = 1924541) B1924541
theorem B1283043 : Blo 1281959 1283043 := bstep (se 1 (by rfl) ⟨962282, by rfl⟩ : syracuseStep 1283043 = 1924565) B1924565
theorem B2888675 : Blo 1281959 2888675 := bstep (se 1 (by rfl) ⟨2166506, by rfl⟩ : syracuseStep 2888675 = 4333013) B4333013
theorem B1283059 : Blo 1281959 1283059 := bstep (se 1 (by rfl) ⟨962294, by rfl⟩ : syracuseStep 1283059 = 1924589) B1924589
theorem B1283075 : Blo 1281959 1283075 := bstep (se 1 (by rfl) ⟨962306, by rfl⟩ : syracuseStep 1283075 = 1924613) B1924613
theorem B11269133 : Blo 1281959 11269133 := bstep (se 3 (by rfl) ⟨2112962, by rfl⟩ : syracuseStep 11269133 = 4225925) B4225925
theorem B1283091 : Blo 1281959 1283091 := bstep (se 1 (by rfl) ⟨962318, by rfl⟩ : syracuseStep 1283091 = 1924637) B1924637
theorem B1283107 : Blo 1281959 1283107 := bstep (se 1 (by rfl) ⟨962330, by rfl⟩ : syracuseStep 1283107 = 1924661) B1924661
theorem B1283123 : Blo 1281959 1283123 := bstep (se 1 (by rfl) ⟨962342, by rfl⟩ : syracuseStep 1283123 = 1924685) B1924685
theorem B1283139 : Blo 1281959 1283139 := bstep (se 1 (by rfl) ⟨962354, by rfl⟩ : syracuseStep 1283139 = 1924709) B1924709
theorem B1283155 : Blo 1281959 1283155 := bstep (se 1 (by rfl) ⟨962366, by rfl⟩ : syracuseStep 1283155 = 1924733) B1924733
theorem B6493283 : Blo 1281959 6493283 := bstep (se 1 (by rfl) ⟨4869962, by rfl⟩ : syracuseStep 6493283 = 9739925) B9739925
theorem B1283171 : Blo 1281959 1283171 := bstep (se 1 (by rfl) ⟨962378, by rfl⟩ : syracuseStep 1283171 = 1924757) B1924757
theorem B1283187 : Blo 1281959 1283187 := bstep (se 1 (by rfl) ⟨962390, by rfl⟩ : syracuseStep 1283187 = 1924781) B1924781
theorem B1283203 : Blo 1281959 1283203 := bstep (se 1 (by rfl) ⟨962402, by rfl⟩ : syracuseStep 1283203 = 1924805) B1924805
theorem B4330637 : Blo 1281959 4330637 := bstep (se 3 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 4330637 = 1623989) B1623989
theorem B24679565 : Blo 1281959 24679565 := bstep (se 3 (by rfl) ⟨4627418, by rfl⟩ : syracuseStep 24679565 = 9254837) B9254837
theorem B1283219 : Blo 1281959 1283219 := bstep (se 1 (by rfl) ⟨962414, by rfl⟩ : syracuseStep 1283219 = 1924829) B1924829
theorem B1283235 : Blo 1281959 1283235 := bstep (se 1 (by rfl) ⟨962426, by rfl⟩ : syracuseStep 1283235 = 1924853) B1924853
theorem B1283251 : Blo 1281959 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B4330691 : Blo 1281959 4330691 := bstep (se 1 (by rfl) ⟨3248018, by rfl⟩ : syracuseStep 4330691 = 6496037) B6496037
theorem B1283267 : Blo 1281959 1283267 := bstep (se 1 (by rfl) ⟨962450, by rfl⟩ : syracuseStep 1283267 = 1924901) B1924901
theorem B1283283 : Blo 1281959 1283283 := bstep (se 1 (by rfl) ⟨962462, by rfl⟩ : syracuseStep 1283283 = 1924925) B1924925
theorem B1283299 : Blo 1281959 1283299 := bstep (se 1 (by rfl) ⟨962474, by rfl⟩ : syracuseStep 1283299 = 1924949) B1924949
theorem B1283315 : Blo 1281959 1283315 := bstep (se 1 (by rfl) ⟨962486, by rfl⟩ : syracuseStep 1283315 = 1924973) B1924973
theorem B1283331 : Blo 1281959 1283331 := bstep (se 1 (by rfl) ⟨962498, by rfl⟩ : syracuseStep 1283331 = 1924997) B1924997
theorem B1283347 : Blo 1281959 1283347 := bstep (se 1 (by rfl) ⟨962510, by rfl⟩ : syracuseStep 1283347 = 1925021) B1925021
theorem B1283363 : Blo 1281959 1283363 := bstep (se 1 (by rfl) ⟨962522, by rfl⟩ : syracuseStep 1283363 = 1925045) B1925045
theorem B1283379 : Blo 1281959 1283379 := bstep (se 1 (by rfl) ⟨962534, by rfl⟩ : syracuseStep 1283379 = 1925069) B1925069
theorem B1283395 : Blo 1281959 1283395 := bstep (se 1 (by rfl) ⟨962546, by rfl⟩ : syracuseStep 1283395 = 1925093) B1925093
theorem B1283411 : Blo 1281959 1283411 := bstep (se 1 (by rfl) ⟨962558, by rfl⟩ : syracuseStep 1283411 = 1925117) B1925117
theorem B1283427 : Blo 1281959 1283427 := bstep (se 1 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 1283427 = 1925141) B1925141
theorem B1283443 : Blo 1281959 1283443 := bstep (se 1 (by rfl) ⟨962582, by rfl⟩ : syracuseStep 1283443 = 1925165) B1925165
theorem B1283459 : Blo 1281959 1283459 := bstep (se 1 (by rfl) ⟨962594, by rfl⟩ : syracuseStep 1283459 = 1925189) B1925189
theorem B1283475 : Blo 1281959 1283475 := bstep (se 1 (by rfl) ⟨962606, by rfl⟩ : syracuseStep 1283475 = 1925213) B1925213
theorem B1283491 : Blo 1281959 1283491 := bstep (se 1 (by rfl) ⟨962618, by rfl⟩ : syracuseStep 1283491 = 1925237) B1925237
theorem B1283507 : Blo 1281959 1283507 := bstep (se 1 (by rfl) ⟨962630, by rfl⟩ : syracuseStep 1283507 = 1925261) B1925261
theorem B1283523 : Blo 1281959 1283523 := bstep (se 1 (by rfl) ⟨962642, by rfl⟩ : syracuseStep 1283523 = 1925285) B1925285
theorem B4330961 : Blo 1281959 4330961 := bstep (se 2 (by rfl) ⟨1624110, by rfl⟩ : syracuseStep 4330961 = 3248221) B3248221
theorem B1283539 : Blo 1281959 1283539 := bstep (se 1 (by rfl) ⟨962654, by rfl⟩ : syracuseStep 1283539 = 1925309) B1925309
theorem B1283555 : Blo 1281959 1283555 := bstep (se 1 (by rfl) ⟨962666, by rfl⟩ : syracuseStep 1283555 = 1925333) B1925333
theorem B1283571 : Blo 1281959 1283571 := bstep (se 1 (by rfl) ⟨962678, by rfl⟩ : syracuseStep 1283571 = 1925357) B1925357
theorem B1283587 : Blo 1281959 1283587 := bstep (se 1 (by rfl) ⟨962690, by rfl⟩ : syracuseStep 1283587 = 1925381) B1925381
theorem B9369101 : Blo 1281959 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B1283603 : Blo 1281959 1283603 := bstep (se 1 (by rfl) ⟨962702, by rfl⟩ : syracuseStep 1283603 = 1925405) B1925405
theorem B1283619 : Blo 1281959 1283619 := bstep (se 1 (by rfl) ⟨962714, by rfl⟩ : syracuseStep 1283619 = 1925429) B1925429
theorem B1283635 : Blo 1281959 1283635 := bstep (se 1 (by rfl) ⟨962726, by rfl⟩ : syracuseStep 1283635 = 1925453) B1925453
theorem B1283651 : Blo 1281959 1283651 := bstep (se 1 (by rfl) ⟨962738, by rfl⟩ : syracuseStep 1283651 = 1925477) B1925477
theorem B1283667 : Blo 1281959 1283667 := bstep (se 1 (by rfl) ⟨962750, by rfl⟩ : syracuseStep 1283667 = 1925501) B1925501
theorem B1283683 : Blo 1281959 1283683 := bstep (se 1 (by rfl) ⟨962762, by rfl⟩ : syracuseStep 1283683 = 1925525) B1925525
theorem B1283699 : Blo 1281959 1283699 := bstep (se 1 (by rfl) ⟨962774, by rfl⟩ : syracuseStep 1283699 = 1925549) B1925549
theorem B1283715 : Blo 1281959 1283715 := bstep (se 1 (by rfl) ⟨962786, by rfl⟩ : syracuseStep 1283715 = 1925573) B1925573
theorem B1283731 : Blo 1281959 1283731 := bstep (se 1 (by rfl) ⟨962798, by rfl⟩ : syracuseStep 1283731 = 1925597) B1925597
theorem B1283747 : Blo 1281959 1283747 := bstep (se 1 (by rfl) ⟨962810, by rfl⟩ : syracuseStep 1283747 = 1925621) B1925621
theorem B3249841 : Blo 1281959 3249841 := bstep (se 2 (by rfl) ⟨1218690, by rfl⟩ : syracuseStep 3249841 = 2437381) B2437381
theorem B1283763 : Blo 1281959 1283763 := bstep (se 1 (by rfl) ⟨962822, by rfl⟩ : syracuseStep 1283763 = 1925645) B1925645
theorem B16676533 : Blo 1281959 16676533 := bstep (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) B1563425
theorem B1283779 : Blo 1281959 1283779 := bstep (se 1 (by rfl) ⟨962834, by rfl⟩ : syracuseStep 1283779 = 1925669) B1925669
theorem B3651277 : Blo 1281959 3651277 := bstep (se 3 (by rfl) ⟨684614, by rfl⟩ : syracuseStep 3651277 = 1369229) B1369229
theorem B1283795 : Blo 1281959 1283795 := bstep (se 1 (by rfl) ⟨962846, by rfl⟩ : syracuseStep 1283795 = 1925693) B1925693
theorem B1283811 : Blo 1281959 1283811 := bstep (se 1 (by rfl) ⟨962858, by rfl⟩ : syracuseStep 1283811 = 1925717) B1925717
theorem B1283827 : Blo 1281959 1283827 := bstep (se 1 (by rfl) ⟨962870, by rfl⟩ : syracuseStep 1283827 = 1925741) B1925741
theorem B1283843 : Blo 1281959 1283843 := bstep (se 1 (by rfl) ⟨962882, by rfl⟩ : syracuseStep 1283843 = 1925765) B1925765
theorem B1283859 : Blo 1281959 1283859 := bstep (se 1 (by rfl) ⟨962894, by rfl⟩ : syracuseStep 1283859 = 1925789) B1925789
theorem B1283875 : Blo 1281959 1283875 := bstep (se 1 (by rfl) ⟨962906, by rfl⟩ : syracuseStep 1283875 = 1925813) B1925813
theorem B1283891 : Blo 1281959 1283891 := bstep (se 1 (by rfl) ⟨962918, by rfl⟩ : syracuseStep 1283891 = 1925837) B1925837
theorem B1283907 : Blo 1281959 1283907 := bstep (se 1 (by rfl) ⟨962930, by rfl⟩ : syracuseStep 1283907 = 1925861) B1925861
theorem B1283923 : Blo 1281959 1283923 := bstep (se 1 (by rfl) ⟨962942, by rfl⟩ : syracuseStep 1283923 = 1925885) B1925885
theorem B1283939 : Blo 1281959 1283939 := bstep (se 1 (by rfl) ⟨962954, by rfl⟩ : syracuseStep 1283939 = 1925909) B1925909
theorem B2054003 : Blo 1281959 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B1283955 : Blo 1281959 1283955 := bstep (se 1 (by rfl) ⟨962966, by rfl⟩ : syracuseStep 1283955 = 1925933) B1925933
theorem B1922945 : Blo 1281959 1922945 := bstep (se 2 (by rfl) ⟨721104, by rfl⟩ : syracuseStep 1922945 = 1442209) B1442209
theorem B6494093 : Blo 1281959 6494093 := bstep (se 3 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 6494093 = 2435285) B2435285
theorem B1922963 : Blo 1281959 1922963 := bstep (se 1 (by rfl) ⟨1442222, by rfl⟩ : syracuseStep 1922963 = 2884445) B2884445
theorem B7804835 : Blo 1281959 7804835 := bstep (se 1 (by rfl) ⟨5853626, by rfl⟩ : syracuseStep 7804835 = 11707253) B11707253
theorem B1922993 : Blo 1281959 1922993 := bstep (se 2 (by rfl) ⟨721122, by rfl⟩ : syracuseStep 1922993 = 1442245) B1442245
theorem B2193331 : Blo 1281959 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B2054081 : Blo 1281959 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B1923011 : Blo 1281959 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B1923041 : Blo 1281959 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B4331501 : Blo 1281959 4331501 := bstep (se 3 (by rfl) ⟨812156, by rfl⟩ : syracuseStep 4331501 = 1624313) B1624313
theorem B9254897 : Blo 1281959 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B1923059 : Blo 1281959 1923059 := bstep (se 1 (by rfl) ⟨1442294, by rfl⟩ : syracuseStep 1923059 = 2884589) B2884589
theorem B1923089 : Blo 1281959 1923089 := bstep (se 2 (by rfl) ⟨721158, by rfl⟩ : syracuseStep 1923089 = 1442317) B1442317
theorem B1923107 : Blo 1281959 1923107 := bstep (se 1 (by rfl) ⟨1442330, by rfl⟩ : syracuseStep 1923107 = 2884661) B2884661
theorem B8222755 : Blo 1281959 8222755 := bstep (se 1 (by rfl) ⟨6167066, by rfl⟩ : syracuseStep 8222755 = 12334133) B12334133
theorem B4331555 : Blo 1281959 4331555 := bstep (se 1 (by rfl) ⟨3248666, by rfl⟩ : syracuseStep 4331555 = 6497333) B6497333
theorem B1923137 : Blo 1281959 1923137 := bstep (se 2 (by rfl) ⟨721176, by rfl⟩ : syracuseStep 1923137 = 1442353) B1442353
theorem B1923155 : Blo 1281959 1923155 := bstep (se 1 (by rfl) ⟨1442366, by rfl⟩ : syracuseStep 1923155 = 2884733) B2884733
theorem B1923185 : Blo 1281959 1923185 := bstep (se 2 (by rfl) ⟨721194, by rfl⟩ : syracuseStep 1923185 = 1442389) B1442389
theorem B1923203 : Blo 1281959 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B1300627 : Blo 1281959 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B1923233 : Blo 1281959 1923233 := bstep (se 2 (by rfl) ⟨721212, by rfl⟩ : syracuseStep 1923233 = 1442425) B1442425
theorem B1923251 : Blo 1281959 1923251 := bstep (se 1 (by rfl) ⟨1442438, by rfl⟩ : syracuseStep 1923251 = 2884877) B2884877
theorem B1923281 : Blo 1281959 1923281 := bstep (se 2 (by rfl) ⟨721230, by rfl⟩ : syracuseStep 1923281 = 1442461) B1442461
theorem B1923299 : Blo 1281959 1923299 := bstep (se 1 (by rfl) ⟨1442474, by rfl⟩ : syracuseStep 1923299 = 2884949) B2884949
theorem B9738467 : Blo 1281959 9738467 := bstep (se 1 (by rfl) ⟨7303850, by rfl⟩ : syracuseStep 9738467 = 14607701) B14607701
theorem B5478641 : Blo 1281959 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B1923329 : Blo 1281959 1923329 := bstep (se 2 (by rfl) ⟨721248, by rfl⟩ : syracuseStep 1923329 = 1442497) B1442497
theorem B1923347 : Blo 1281959 1923347 := bstep (se 1 (by rfl) ⟨1442510, by rfl⟩ : syracuseStep 1923347 = 2885021) B2885021
theorem B1923377 : Blo 1281959 1923377 := bstep (se 2 (by rfl) ⟨721266, by rfl⟩ : syracuseStep 1923377 = 1442533) B1442533
theorem B4331825 : Blo 1281959 4331825 := bstep (se 2 (by rfl) ⟨1624434, by rfl⟩ : syracuseStep 4331825 = 3248869) B3248869
theorem B2054465 : Blo 1281959 2054465 := bstep (se 2 (by rfl) ⟨770424, by rfl⟩ : syracuseStep 2054465 = 1540849) B1540849
theorem B1923395 : Blo 1281959 1923395 := bstep (se 1 (by rfl) ⟨1442546, by rfl⟩ : syracuseStep 1923395 = 2885093) B2885093
theorem B1923425 : Blo 1281959 1923425 := bstep (se 2 (by rfl) ⟨721284, by rfl⟩ : syracuseStep 1923425 = 1442569) B1442569
theorem B1923443 : Blo 1281959 1923443 := bstep (se 1 (by rfl) ⟨1442582, by rfl⟩ : syracuseStep 1923443 = 2885165) B2885165
theorem B1923473 : Blo 1281959 1923473 := bstep (se 2 (by rfl) ⟨721302, by rfl⟩ : syracuseStep 1923473 = 1442605) B1442605
theorem B2193809 : Blo 1281959 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1923491 : Blo 1281959 1923491 := bstep (se 1 (by rfl) ⟨1442618, by rfl⟩ : syracuseStep 1923491 = 2885237) B2885237
theorem B5855665 : Blo 1281959 5855665 := bstep (se 2 (by rfl) ⟨2195874, by rfl⟩ : syracuseStep 5855665 = 4391749) B4391749
theorem B1923521 : Blo 1281959 1923521 := bstep (se 2 (by rfl) ⟨721320, by rfl⟩ : syracuseStep 1923521 = 1442641) B1442641
theorem B2054593 : Blo 1281959 2054593 := bstep (se 2 (by rfl) ⟨770472, by rfl⟩ : syracuseStep 2054593 = 1540945) B1540945
theorem B1923539 : Blo 1281959 1923539 := bstep (se 1 (by rfl) ⟨1442654, by rfl⟩ : syracuseStep 1923539 = 2885309) B2885309
theorem B14604785 : Blo 1281959 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B1923569 : Blo 1281959 1923569 := bstep (se 2 (by rfl) ⟨721338, by rfl⟩ : syracuseStep 1923569 = 1442677) B1442677
theorem B1923587 : Blo 1281959 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B1923617 : Blo 1281959 1923617 := bstep (se 2 (by rfl) ⟨721356, by rfl⟩ : syracuseStep 1923617 = 1442713) B1442713
theorem B1923635 : Blo 1281959 1923635 := bstep (se 1 (by rfl) ⟨1442726, by rfl⟩ : syracuseStep 1923635 = 2885453) B2885453
theorem B1923665 : Blo 1281959 1923665 := bstep (se 2 (by rfl) ⟨721374, by rfl⟩ : syracuseStep 1923665 = 1442749) B1442749
theorem B1923683 : Blo 1281959 1923683 := bstep (se 1 (by rfl) ⟨1442762, by rfl⟩ : syracuseStep 1923683 = 2885525) B2885525
theorem B16439921 : Blo 1281959 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B1923713 : Blo 1281959 1923713 := bstep (se 2 (by rfl) ⟨721392, by rfl⟩ : syracuseStep 1923713 = 1442785) B1442785
theorem B1825411 : Blo 1281959 1825411 := bstep (se 1 (by rfl) ⟨1369058, by rfl⟩ : syracuseStep 1825411 = 2738117) B2738117
theorem B1923731 : Blo 1281959 1923731 := bstep (se 1 (by rfl) ⟨1442798, by rfl⟩ : syracuseStep 1923731 = 2885597) B2885597
theorem B1923761 : Blo 1281959 1923761 := bstep (se 2 (by rfl) ⟨721410, by rfl⟩ : syracuseStep 1923761 = 1442821) B1442821
theorem B1923779 : Blo 1281959 1923779 := bstep (se 1 (by rfl) ⟨1442834, by rfl⟩ : syracuseStep 1923779 = 2885669) B2885669
theorem B1923809 : Blo 1281959 1923809 := bstep (se 2 (by rfl) ⟨721428, by rfl⟩ : syracuseStep 1923809 = 1442857) B1442857
theorem B1825507 : Blo 1281959 1825507 := bstep (se 1 (by rfl) ⟨1369130, by rfl⟩ : syracuseStep 1825507 = 2738261) B2738261
theorem B1923827 : Blo 1281959 1923827 := bstep (se 1 (by rfl) ⟨1442870, by rfl⟩ : syracuseStep 1923827 = 2885741) B2885741
theorem B1923857 : Blo 1281959 1923857 := bstep (se 2 (by rfl) ⟨721446, by rfl⟩ : syracuseStep 1923857 = 1442893) B1442893
theorem B1923875 : Blo 1281959 1923875 := bstep (se 1 (by rfl) ⟨1442906, by rfl⟩ : syracuseStep 1923875 = 2885813) B2885813
theorem B1923905 : Blo 1281959 1923905 := bstep (se 2 (by rfl) ⟨721464, by rfl⟩ : syracuseStep 1923905 = 1442929) B1442929
theorem B7904069 : Blo 1281959 7904069 := bstep (se 4 (by rfl) ⟨741006, by rfl⟩ : syracuseStep 7904069 = 1482013) B1482013
theorem B4332365 : Blo 1281959 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B1923923 : Blo 1281959 1923923 := bstep (se 1 (by rfl) ⟨1442942, by rfl⟩ : syracuseStep 1923923 = 2885885) B2885885
theorem B1923953 : Blo 1281959 1923953 := bstep (se 2 (by rfl) ⟨721482, by rfl⟩ : syracuseStep 1923953 = 1442965) B1442965
theorem B5200753 : Blo 1281959 5200753 := bstep (se 2 (by rfl) ⟨1950282, by rfl⟩ : syracuseStep 5200753 = 3900565) B3900565
theorem B1923971 : Blo 1281959 1923971 := bstep (se 1 (by rfl) ⟨1442978, by rfl⟩ : syracuseStep 1923971 = 2885957) B2885957
theorem B4332419 : Blo 1281959 4332419 := bstep (se 1 (by rfl) ⟨3249314, by rfl⟩ : syracuseStep 4332419 = 6498629) B6498629
theorem B1924001 : Blo 1281959 1924001 := bstep (se 2 (by rfl) ⟨721500, by rfl⟩ : syracuseStep 1924001 = 1443001) B1443001
theorem B1924019 : Blo 1281959 1924019 := bstep (se 1 (by rfl) ⟨1443014, by rfl⟩ : syracuseStep 1924019 = 2886029) B2886029
theorem B7125965 : Blo 1281959 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B1924049 : Blo 1281959 1924049 := bstep (se 2 (by rfl) ⟨721518, by rfl⟩ : syracuseStep 1924049 = 1443037) B1443037
theorem B1924067 : Blo 1281959 1924067 := bstep (se 1 (by rfl) ⟨1443050, by rfl⟩ : syracuseStep 1924067 = 2886101) B2886101
theorem B1850369 : Blo 1281959 1850369 := bstep (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) B1387777
theorem B1924097 : Blo 1281959 1924097 := bstep (se 2 (by rfl) ⟨721536, by rfl⟩ : syracuseStep 1924097 = 1443073) B1443073
theorem B4873229 : Blo 1281959 4873229 := bstep (se 3 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 4873229 = 1827461) B1827461
theorem B1924115 : Blo 1281959 1924115 := bstep (se 1 (by rfl) ⟨1443086, by rfl⟩ : syracuseStep 1924115 = 2886173) B2886173
theorem B1924145 : Blo 1281959 1924145 := bstep (se 2 (by rfl) ⟨721554, by rfl⟩ : syracuseStep 1924145 = 1443109) B1443109
theorem B1924163 : Blo 1281959 1924163 := bstep (se 1 (by rfl) ⟨1443122, by rfl⟩ : syracuseStep 1924163 = 2886245) B2886245
theorem B1924193 : Blo 1281959 1924193 := bstep (se 2 (by rfl) ⟨721572, by rfl⟩ : syracuseStep 1924193 = 1443145) B1443145
theorem B1924211 : Blo 1281959 1924211 := bstep (se 1 (by rfl) ⟨1443158, by rfl⟩ : syracuseStep 1924211 = 2886317) B2886317
theorem B1924241 : Blo 1281959 1924241 := bstep (se 2 (by rfl) ⟨721590, by rfl⟩ : syracuseStep 1924241 = 1443181) B1443181
theorem B4332689 : Blo 1281959 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B1924259 : Blo 1281959 1924259 := bstep (se 1 (by rfl) ⟨1443194, by rfl⟩ : syracuseStep 1924259 = 2886389) B2886389
theorem B1924289 : Blo 1281959 1924289 := bstep (se 2 (by rfl) ⟨721608, by rfl⟩ : syracuseStep 1924289 = 1443217) B1443217
theorem B1826003 : Blo 1281959 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B1924307 : Blo 1281959 1924307 := bstep (se 1 (by rfl) ⟨1443230, by rfl⟩ : syracuseStep 1924307 = 2886461) B2886461
theorem B1924337 : Blo 1281959 1924337 := bstep (se 2 (by rfl) ⟨721626, by rfl⟩ : syracuseStep 1924337 = 1443253) B1443253
theorem B1924355 : Blo 1281959 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B10951949 : Blo 1281959 10951949 := bstep (se 3 (by rfl) ⟨2053490, by rfl⟩ : syracuseStep 10951949 = 4106981) B4106981
theorem B3702029 : Blo 1281959 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B1924385 : Blo 1281959 1924385 := bstep (se 2 (by rfl) ⟨721644, by rfl⟩ : syracuseStep 1924385 = 1443289) B1443289
theorem B1924403 : Blo 1281959 1924403 := bstep (se 1 (by rfl) ⟨1443302, by rfl⟩ : syracuseStep 1924403 = 2886605) B2886605
theorem B2342225 : Blo 1281959 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B1924433 : Blo 1281959 1924433 := bstep (se 2 (by rfl) ⟨721662, by rfl⟩ : syracuseStep 1924433 = 1443325) B1443325
theorem B4111697 : Blo 1281959 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B1924451 : Blo 1281959 1924451 := bstep (se 1 (by rfl) ⟨1443338, by rfl⟩ : syracuseStep 1924451 = 2886677) B2886677
theorem B27745649 : Blo 1281959 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B1924481 : Blo 1281959 1924481 := bstep (se 2 (by rfl) ⟨721680, by rfl⟩ : syracuseStep 1924481 = 1443361) B1443361
theorem B3653009 : Blo 1281959 3653009 := bstep (se 2 (by rfl) ⟨1369878, by rfl⟩ : syracuseStep 3653009 = 2739757) B2739757
theorem B1924499 : Blo 1281959 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1924529 : Blo 1281959 1924529 := bstep (se 2 (by rfl) ⟨721698, by rfl⟩ : syracuseStep 1924529 = 1443397) B1443397
theorem B1924547 : Blo 1281959 1924547 := bstep (se 1 (by rfl) ⟨1443410, by rfl⟩ : syracuseStep 1924547 = 2886821) B2886821
theorem B1924577 : Blo 1281959 1924577 := bstep (se 2 (by rfl) ⟨721716, by rfl⟩ : syracuseStep 1924577 = 1443433) B1443433
theorem B13876721 : Blo 1281959 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B1924595 : Blo 1281959 1924595 := bstep (se 1 (by rfl) ⟨1443446, by rfl⟩ : syracuseStep 1924595 = 2886893) B2886893
theorem B1924625 : Blo 1281959 1924625 := bstep (se 2 (by rfl) ⟨721734, by rfl⟩ : syracuseStep 1924625 = 1443469) B1443469
theorem B1924643 : Blo 1281959 1924643 := bstep (se 1 (by rfl) ⟨1443482, by rfl⟩ : syracuseStep 1924643 = 2886965) B2886965
theorem B1924673 : Blo 1281959 1924673 := bstep (se 2 (by rfl) ⟨721752, by rfl⟩ : syracuseStep 1924673 = 1443505) B1443505
theorem B3898961 : Blo 1281959 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B3653201 : Blo 1281959 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B1924691 : Blo 1281959 1924691 := bstep (se 1 (by rfl) ⟨1443518, by rfl⟩ : syracuseStep 1924691 = 2887037) B2887037
theorem B1924721 : Blo 1281959 1924721 := bstep (se 2 (by rfl) ⟨721770, by rfl⟩ : syracuseStep 1924721 = 1443541) B1443541
theorem B1924739 : Blo 1281959 1924739 := bstep (se 1 (by rfl) ⟨1443554, by rfl⟩ : syracuseStep 1924739 = 2887109) B2887109
theorem B1924769 : Blo 1281959 1924769 := bstep (se 2 (by rfl) ⟨721788, by rfl⟩ : syracuseStep 1924769 = 1443577) B1443577
theorem B4333229 : Blo 1281959 4333229 := bstep (se 3 (by rfl) ⟨812480, by rfl⟩ : syracuseStep 4333229 = 1624961) B1624961
theorem B1924787 : Blo 1281959 1924787 := bstep (se 1 (by rfl) ⟨1443590, by rfl⟩ : syracuseStep 1924787 = 2887181) B2887181
theorem B7306949 : Blo 1281959 7306949 := bstep (se 4 (by rfl) ⟨685026, by rfl⟩ : syracuseStep 7306949 = 1370053) B1370053
theorem B1924817 : Blo 1281959 1924817 := bstep (se 2 (by rfl) ⟨721806, by rfl⟩ : syracuseStep 1924817 = 1443613) B1443613
theorem B1924835 : Blo 1281959 1924835 := bstep (se 1 (by rfl) ⟨1443626, by rfl⟩ : syracuseStep 1924835 = 2887253) B2887253
theorem B4333283 : Blo 1281959 4333283 := bstep (se 1 (by rfl) ⟨3249962, by rfl⟩ : syracuseStep 4333283 = 6499925) B6499925
theorem B1924865 : Blo 1281959 1924865 := bstep (se 2 (by rfl) ⟨721824, by rfl⟩ : syracuseStep 1924865 = 1443649) B1443649
theorem B1924883 : Blo 1281959 1924883 := bstep (se 1 (by rfl) ⟨1443662, by rfl⟩ : syracuseStep 1924883 = 2887325) B2887325
theorem B1924913 : Blo 1281959 1924913 := bstep (se 2 (by rfl) ⟨721842, by rfl⟩ : syracuseStep 1924913 = 1443685) B1443685
theorem B4874033 : Blo 1281959 4874033 := bstep (se 2 (by rfl) ⟨1827762, by rfl⟩ : syracuseStep 4874033 = 3655525) B3655525
theorem B1924931 : Blo 1281959 1924931 := bstep (se 1 (by rfl) ⟨1443698, by rfl⟩ : syracuseStep 1924931 = 2887397) B2887397
theorem B1826641 : Blo 1281959 1826641 := bstep (se 2 (by rfl) ⟨684990, by rfl⟩ : syracuseStep 1826641 = 1369981) B1369981
theorem B1924961 : Blo 1281959 1924961 := bstep (se 2 (by rfl) ⟨721860, by rfl⟩ : syracuseStep 1924961 = 1443721) B1443721
theorem B1924979 : Blo 1281959 1924979 := bstep (se 1 (by rfl) ⟨1443734, by rfl⟩ : syracuseStep 1924979 = 2887469) B2887469
theorem B1925009 : Blo 1281959 1925009 := bstep (se 2 (by rfl) ⟨721878, by rfl⟩ : syracuseStep 1925009 = 1443757) B1443757
theorem B1925027 : Blo 1281959 1925027 := bstep (se 1 (by rfl) ⟨1443770, by rfl⟩ : syracuseStep 1925027 = 2887541) B2887541
theorem B2056099 : Blo 1281959 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B8781745 : Blo 1281959 8781745 := bstep (se 2 (by rfl) ⟨3293154, by rfl⟩ : syracuseStep 8781745 = 6586309) B6586309
theorem B1925057 : Blo 1281959 1925057 := bstep (se 2 (by rfl) ⟨721896, by rfl⟩ : syracuseStep 1925057 = 1443793) B1443793
theorem B1925075 : Blo 1281959 1925075 := bstep (se 1 (by rfl) ⟨1443806, by rfl⟩ : syracuseStep 1925075 = 2887613) B2887613
theorem B12492785 : Blo 1281959 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B1925105 : Blo 1281959 1925105 := bstep (se 2 (by rfl) ⟨721914, by rfl⟩ : syracuseStep 1925105 = 1443829) B1443829
theorem B1925195 : Blo 1281959 1925195 := bstep (se 1 (by rfl) ⟨1443896, by rfl⟩ : syracuseStep 1925195 = 2887793) B2887793
theorem B1925207 : Blo 1281959 1925207 := bstep (se 1 (by rfl) ⟨1443905, by rfl⟩ : syracuseStep 1925207 = 2887811) B2887811
theorem B1925273 : Blo 1281959 1925273 := bstep (se 2 (by rfl) ⟨721977, by rfl⟩ : syracuseStep 1925273 = 1443955) B1443955
theorem B4448449 : Blo 1281959 4448449 := bstep (se 2 (by rfl) ⟨1668168, by rfl⟩ : syracuseStep 4448449 = 3336337) B3336337
theorem B20300017 : Blo 1281959 20300017 := bstep (se 2 (by rfl) ⟨7612506, by rfl⟩ : syracuseStep 20300017 = 15225013) B15225013
theorem B4686083 : Blo 1281959 4686083 := bstep (se 1 (by rfl) ⟨3514562, by rfl⟩ : syracuseStep 4686083 = 7029125) B7029125
theorem B10404101 : Blo 1281959 10404101 := bstep (se 4 (by rfl) ⟨975384, by rfl⟩ : syracuseStep 10404101 = 1950769) B1950769
theorem B1925387 : Blo 1281959 1925387 := bstep (se 1 (by rfl) ⟨1444040, by rfl⟩ : syracuseStep 1925387 = 2888081) B2888081
theorem B1925399 : Blo 1281959 1925399 := bstep (se 1 (by rfl) ⟨1444049, by rfl⟩ : syracuseStep 1925399 = 2888099) B2888099
theorem B4874519 : Blo 1281959 4874519 := bstep (se 1 (by rfl) ⟨3655889, by rfl⟩ : syracuseStep 4874519 = 7311779) B7311779
theorem B1925465 : Blo 1281959 1925465 := bstep (se 2 (by rfl) ⟨722049, by rfl⟩ : syracuseStep 1925465 = 1444099) B1444099
theorem B1483147 : Blo 1281959 1483147 := bstep (se 1 (by rfl) ⟨1112360, by rfl⟩ : syracuseStep 1483147 = 2224721) B2224721
theorem B3654067 : Blo 1281959 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B1925579 : Blo 1281959 1925579 := bstep (se 1 (by rfl) ⟨1444184, by rfl⟩ : syracuseStep 1925579 = 2888369) B2888369
theorem B1442263 : Blo 1281959 1442263 := bstep (se 1 (by rfl) ⟨1081697, by rfl⟩ : syracuseStep 1442263 = 2163395) B2163395
theorem B1925591 : Blo 1281959 1925591 := bstep (se 1 (by rfl) ⟨1444193, by rfl⟩ : syracuseStep 1925591 = 2888387) B2888387
theorem B1925657 : Blo 1281959 1925657 := bstep (se 2 (by rfl) ⟨722121, by rfl⟩ : syracuseStep 1925657 = 1444243) B1444243
theorem B7807553 : Blo 1281959 7807553 := bstep (se 2 (by rfl) ⟨2927832, by rfl⟩ : syracuseStep 7807553 = 5855665) B5855665
theorem B1442443 : Blo 1281959 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B1925771 : Blo 1281959 1925771 := bstep (se 1 (by rfl) ⟨1444328, by rfl⟩ : syracuseStep 1925771 = 2888657) B2888657
theorem B1925783 : Blo 1281959 1925783 := bstep (se 1 (by rfl) ⟨1444337, by rfl⟩ : syracuseStep 1925783 = 2888675) B2888675
theorem B7512755 : Blo 1281959 7512755 := bstep (se 1 (by rfl) ⟨5634566, by rfl⟩ : syracuseStep 7512755 = 11269133) B11269133
theorem B9872077 : Blo 1281959 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B2163415 : Blo 1281959 2163415 := bstep (se 1 (by rfl) ⟨1622561, by rfl⟩ : syracuseStep 2163415 = 3245123) B3245123
theorem B1925849 : Blo 1281959 1925849 := bstep (se 2 (by rfl) ⟨722193, by rfl⟩ : syracuseStep 1925849 = 1444387) B1444387
theorem B1442551 : Blo 1281959 1442551 := bstep (se 1 (by rfl) ⟨1081913, by rfl⟩ : syracuseStep 1442551 = 2163827) B2163827
theorem B5202733 : Blo 1281959 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B2884427 : Blo 1281959 2884427 := bstep (se 1 (by rfl) ⟨2163320, by rfl⟩ : syracuseStep 2884427 = 4326641) B4326641
theorem B2433881 : Blo 1281959 2433881 := bstep (se 2 (by rfl) ⟨912705, by rfl⟩ : syracuseStep 2433881 = 1825411) B1825411
theorem B2884481 : Blo 1281959 2884481 := bstep (se 2 (by rfl) ⟨1081680, by rfl⟩ : syracuseStep 2884481 = 2163361) B2163361
theorem B1442731 : Blo 1281959 1442731 := bstep (se 1 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 1442731 = 2164097) B2164097
theorem B22217651 : Blo 1281959 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B88941509 : Blo 1281959 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B10404881 : Blo 1281959 10404881 := bstep (se 2 (by rfl) ⟨3901830, by rfl⟩ : syracuseStep 10404881 = 7803661) B7803661
theorem B1442839 : Blo 1281959 1442839 := bstep (se 1 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 1442839 = 2164259) B2164259
theorem B5850157 : Blo 1281959 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B35587147 : Blo 1281959 35587147 := bstep (se 1 (by rfl) ⟨26690360, by rfl⟩ : syracuseStep 35587147 = 53380721) B53380721
theorem B2884697 : Blo 1281959 2884697 := bstep (se 2 (by rfl) ⟨1081761, by rfl⟩ : syracuseStep 2884697 = 2163523) B2163523
theorem B1623179 : Blo 1281959 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B5850263 : Blo 1281959 5850263 := bstep (se 1 (by rfl) ⟨4387697, by rfl⟩ : syracuseStep 5850263 = 8775395) B8775395
theorem B4752535 : Blo 1281959 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B2884787 : Blo 1281959 2884787 := bstep (se 1 (by rfl) ⟨2163590, by rfl⟩ : syracuseStep 2884787 = 4327181) B4327181
theorem B1443019 : Blo 1281959 1443019 := bstep (se 1 (by rfl) ⟨1082264, by rfl⟩ : syracuseStep 1443019 = 2164529) B2164529
theorem B2884823 : Blo 1281959 2884823 := bstep (se 1 (by rfl) ⟨2163617, by rfl⟩ : syracuseStep 2884823 = 4327235) B4327235
theorem B1541387 : Blo 1281959 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B5203223 : Blo 1281959 5203223 := bstep (se 1 (by rfl) ⟨3902417, by rfl⟩ : syracuseStep 5203223 = 7804835) B7804835
theorem B1369387 : Blo 1281959 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B7308589 : Blo 1281959 7308589 := bstep (se 3 (by rfl) ⟨1370360, by rfl⟩ : syracuseStep 7308589 = 2740721) B2740721
theorem B1443127 : Blo 1281959 1443127 := bstep (se 1 (by rfl) ⟨1082345, by rfl⟩ : syracuseStep 1443127 = 2164691) B2164691
theorem B2164043 : Blo 1281959 2164043 := bstep (se 1 (by rfl) ⟨1623032, by rfl⟩ : syracuseStep 2164043 = 3246065) B3246065
theorem B6169931 : Blo 1281959 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B3900761 : Blo 1281959 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B4326749 : Blo 1281959 4326749 := bstep (se 3 (by rfl) ⟨811265, by rfl⟩ : syracuseStep 4326749 = 1622531) B1622531
theorem B2885003 : Blo 1281959 2885003 := bstep (se 1 (by rfl) ⟨2163752, by rfl⟩ : syracuseStep 2885003 = 4327505) B4327505
theorem B2885057 : Blo 1281959 2885057 := bstep (se 2 (by rfl) ⟨1081896, by rfl⟩ : syracuseStep 2885057 = 2163793) B2163793
theorem B2164171 : Blo 1281959 2164171 := bstep (se 1 (by rfl) ⟨1623128, by rfl⟩ : syracuseStep 2164171 = 3246257) B3246257
theorem B3655115 : Blo 1281959 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B3081689 : Blo 1281959 3081689 := bstep (se 2 (by rfl) ⟨1155633, by rfl⟩ : syracuseStep 3081689 = 2311267) B2311267
theorem B1443307 : Blo 1281959 1443307 := bstep (se 1 (by rfl) ⟨1082480, by rfl⟩ : syracuseStep 1443307 = 2164961) B2164961
theorem B1369643 : Blo 1281959 1369643 := bstep (se 1 (by rfl) ⟨1027232, by rfl⟩ : syracuseStep 1369643 = 2054465) B2054465
theorem B9741869 : Blo 1281959 9741869 := bstep (se 3 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 9741869 = 3653201) B3653201
theorem B6014515 : Blo 1281959 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B1443415 : Blo 1281959 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B2164313 : Blo 1281959 2164313 := bstep (se 2 (by rfl) ⟨811617, by rfl⟩ : syracuseStep 2164313 = 1623235) B1623235
theorem B9881189 : Blo 1281959 9881189 := bstep (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) B1852723
theorem B4867715 : Blo 1281959 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B2885273 : Blo 1281959 2885273 := bstep (se 2 (by rfl) ⟨1081977, by rfl⟩ : syracuseStep 2885273 = 2163955) B2163955
theorem B10962611 : Blo 1281959 10962611 := bstep (se 1 (by rfl) ⟨8221958, by rfl⟩ : syracuseStep 10962611 = 16443917) B16443917
theorem B3245771 : Blo 1281959 3245771 := bstep (se 1 (by rfl) ⟨2434328, by rfl⟩ : syracuseStep 3245771 = 4868657) B4868657
theorem B2164441 : Blo 1281959 2164441 := bstep (se 2 (by rfl) ⟨811665, by rfl⟩ : syracuseStep 2164441 = 1623331) B1623331
theorem B2885363 : Blo 1281959 2885363 := bstep (se 1 (by rfl) ⟨2164022, by rfl⟩ : syracuseStep 2885363 = 4328045) B4328045
theorem B1443595 : Blo 1281959 1443595 := bstep (se 1 (by rfl) ⟨1082696, by rfl⟩ : syracuseStep 1443595 = 2165393) B2165393
theorem B2885399 : Blo 1281959 2885399 := bstep (se 1 (by rfl) ⟨2164049, by rfl⟩ : syracuseStep 2885399 = 4328099) B4328099
theorem B1623883 : Blo 1281959 1623883 := bstep (se 1 (by rfl) ⟨1217912, by rfl⟩ : syracuseStep 1623883 = 2435825) B2435825
theorem B1443703 : Blo 1281959 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B5269379 : Blo 1281959 5269379 := bstep (se 1 (by rfl) ⟨3952034, by rfl⟩ : syracuseStep 5269379 = 7904069) B7904069
theorem B15599537 : Blo 1281959 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B2885579 : Blo 1281959 2885579 := bstep (se 1 (by rfl) ⟨2164184, by rfl⟩ : syracuseStep 2885579 = 4328369) B4328369
theorem B2885633 : Blo 1281959 2885633 := bstep (se 2 (by rfl) ⟨1082112, by rfl⟩ : syracuseStep 2885633 = 2164225) B2164225
theorem B1443883 : Blo 1281959 1443883 := bstep (se 1 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 1443883 = 2165825) B2165825
theorem B2738227 : Blo 1281959 2738227 := bstep (se 1 (by rfl) ⟨2053670, by rfl⟩ : syracuseStep 2738227 = 4107341) B4107341
theorem B4868171 : Blo 1281959 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B1624151 : Blo 1281959 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B6490205 : Blo 1281959 6490205 := bstep (se 3 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 6490205 = 2433827) B2433827
theorem B1443991 : Blo 1281959 1443991 := bstep (se 1 (by rfl) ⟨1082993, by rfl⟩ : syracuseStep 1443991 = 2165987) B2165987
theorem B7301299 : Blo 1281959 7301299 := bstep (se 1 (by rfl) ⟨5475974, by rfl⟩ : syracuseStep 7301299 = 10951949) B10951949
theorem B2885849 : Blo 1281959 2885849 := bstep (se 2 (by rfl) ⟨1082193, by rfl⟩ : syracuseStep 2885849 = 2164387) B2164387
theorem B2435339 : Blo 1281959 2435339 := bstep (se 1 (by rfl) ⟨1826504, by rfl⟩ : syracuseStep 2435339 = 3653009) B3653009
theorem B4868369 : Blo 1281959 4868369 := bstep (se 2 (by rfl) ⟨1825638, by rfl⟩ : syracuseStep 4868369 = 3651277) B3651277
theorem B2165015 : Blo 1281959 2165015 := bstep (se 1 (by rfl) ⟨1623761, by rfl⟩ : syracuseStep 2165015 = 3247523) B3247523
theorem B2885939 : Blo 1281959 2885939 := bstep (se 1 (by rfl) ⟨2164454, by rfl⟩ : syracuseStep 2885939 = 4328909) B4328909
theorem B9251147 : Blo 1281959 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B1444171 : Blo 1281959 1444171 := bstep (se 1 (by rfl) ⟨1083128, by rfl⟩ : syracuseStep 1444171 = 2166257) B2166257
theorem B2885975 : Blo 1281959 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B2599307 : Blo 1281959 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B2165143 : Blo 1281959 2165143 := bstep (se 1 (by rfl) ⟨1623857, by rfl⟩ : syracuseStep 2165143 = 3247715) B3247715
theorem B2312599 : Blo 1281959 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B1444279 : Blo 1281959 1444279 := bstep (se 1 (by rfl) ⟨1083209, by rfl⟩ : syracuseStep 1444279 = 2166419) B2166419
theorem B2435521 : Blo 1281959 2435521 := bstep (se 2 (by rfl) ⟨913320, by rfl⟩ : syracuseStep 2435521 = 1826641) B1826641
theorem B4327883 : Blo 1281959 4327883 := bstep (se 1 (by rfl) ⟨3245912, by rfl⟩ : syracuseStep 4327883 = 6491825) B6491825
theorem B2886155 : Blo 1281959 2886155 := bstep (se 1 (by rfl) ⟨2164616, by rfl⟩ : syracuseStep 2886155 = 4329233) B4329233
theorem B2886209 : Blo 1281959 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B11708993 : Blo 1281959 11708993 := bstep (se 2 (by rfl) ⟨4390872, by rfl⟩ : syracuseStep 11708993 = 8781745) B8781745
theorem B13863575 : Blo 1281959 13863575 := bstep (se 1 (by rfl) ⟨10397681, by rfl⟩ : syracuseStep 13863575 = 20795363) B20795363
theorem B3246743 : Blo 1281959 3246743 := bstep (se 1 (by rfl) ⟨2435057, by rfl⟩ : syracuseStep 3246743 = 4870115) B4870115
theorem B4934317 : Blo 1281959 4934317 := bstep (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) B1850369
theorem B4328153 : Blo 1281959 4328153 := bstep (se 2 (by rfl) ⟨1623057, by rfl⟩ : syracuseStep 4328153 = 3246115) B3246115
theorem B10963673 : Blo 1281959 10963673 := bstep (se 2 (by rfl) ⟨4111377, by rfl⟩ : syracuseStep 10963673 = 8222755) B8222755
theorem B1624855 : Blo 1281959 1624855 := bstep (se 1 (by rfl) ⟨1218641, by rfl⟩ : syracuseStep 1624855 = 2437283) B2437283
theorem B2886425 : Blo 1281959 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B2886515 : Blo 1281959 2886515 := bstep (se 1 (by rfl) ⟨2164886, by rfl⟩ : syracuseStep 2886515 = 4329773) B4329773
theorem B2435969 : Blo 1281959 2435969 := bstep (se 2 (by rfl) ⟨913488, by rfl⟩ : syracuseStep 2435969 = 1826977) B1826977
theorem B2886551 : Blo 1281959 2886551 := bstep (se 1 (by rfl) ⟨2164913, by rfl⟩ : syracuseStep 2886551 = 4329827) B4329827
theorem B2165771 : Blo 1281959 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B4869143 : Blo 1281959 4869143 := bstep (se 1 (by rfl) ⟨3651857, by rfl⟩ : syracuseStep 4869143 = 7303715) B7303715
theorem B35105861 : Blo 1281959 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B2886731 : Blo 1281959 2886731 := bstep (se 1 (by rfl) ⟨2165048, by rfl⟩ : syracuseStep 2886731 = 4330097) B4330097
theorem B2886785 : Blo 1281959 2886785 := bstep (se 2 (by rfl) ⟨1082544, by rfl⟩ : syracuseStep 2886785 = 2165089) B2165089
theorem B2165899 : Blo 1281959 2165899 := bstep (se 1 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 2165899 = 3248849) B3248849
theorem B4934807 : Blo 1281959 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B5483699 : Blo 1281959 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B2739415 : Blo 1281959 2739415 := bstep (se 1 (by rfl) ⟨2054561, by rfl⟩ : syracuseStep 2739415 = 4109123) B4109123
theorem B2436311 : Blo 1281959 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B4869341 : Blo 1281959 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B2739457 : Blo 1281959 2739457 := bstep (se 2 (by rfl) ⟨1027296, by rfl⟩ : syracuseStep 2739457 = 2054593) B2054593
theorem B6499601 : Blo 1281959 6499601 := bstep (se 2 (by rfl) ⟨2437350, by rfl⟩ : syracuseStep 6499601 = 4874701) B4874701
theorem B2166041 : Blo 1281959 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B3247411 : Blo 1281959 3247411 := bstep (se 1 (by rfl) ⟨2435558, by rfl⟩ : syracuseStep 3247411 = 4871117) B4871117
theorem B2887001 : Blo 1281959 2887001 := bstep (se 2 (by rfl) ⟨1082625, by rfl⟩ : syracuseStep 2887001 = 2165251) B2165251
theorem B4328855 : Blo 1281959 4328855 := bstep (se 1 (by rfl) ⟨3246641, by rfl⟩ : syracuseStep 4328855 = 6493283) B6493283
theorem B2166169 : Blo 1281959 2166169 := bstep (se 2 (by rfl) ⟨812313, by rfl⟩ : syracuseStep 2166169 = 1624627) B1624627
theorem B2887091 : Blo 1281959 2887091 := bstep (se 1 (by rfl) ⟨2165318, by rfl⟩ : syracuseStep 2887091 = 4330637) B4330637
theorem B6499763 : Blo 1281959 6499763 := bstep (se 1 (by rfl) ⟨4874822, by rfl⟩ : syracuseStep 6499763 = 9749645) B9749645
theorem B16453043 : Blo 1281959 16453043 := bstep (se 1 (by rfl) ⟨12339782, by rfl⟩ : syracuseStep 16453043 = 24679565) B24679565
theorem B3247553 : Blo 1281959 3247553 := bstep (se 2 (by rfl) ⟨1217832, by rfl⟩ : syracuseStep 3247553 = 2435665) B2435665
theorem B2887127 : Blo 1281959 2887127 := bstep (se 1 (by rfl) ⟨2165345, by rfl⟩ : syracuseStep 2887127 = 4330691) B4330691
theorem B10956323 : Blo 1281959 10956323 := bstep (se 1 (by rfl) ⟨8217242, by rfl⟩ : syracuseStep 10956323 = 16434485) B16434485
theorem B7302757 : Blo 1281959 7302757 := bstep (se 4 (by rfl) ⟨684633, by rfl⟩ : syracuseStep 7302757 = 1369267) B1369267
theorem B2887307 : Blo 1281959 2887307 := bstep (se 1 (by rfl) ⟨2165480, by rfl⟩ : syracuseStep 2887307 = 4330961) B4330961
theorem B6246067 : Blo 1281959 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B2887361 : Blo 1281959 2887361 := bstep (se 2 (by rfl) ⟨1082760, by rfl⟩ : syracuseStep 2887361 = 2165521) B2165521
theorem B11710169 : Blo 1281959 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B4108097 : Blo 1281959 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B6934337 : Blo 1281959 6934337 := bstep (se 2 (by rfl) ⟨2600376, by rfl⟩ : syracuseStep 6934337 = 5200753) B5200753
theorem B9736037 : Blo 1281959 9736037 := bstep (se 4 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 9736037 = 1825507) B1825507
theorem B2436979 : Blo 1281959 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B21909365 : Blo 1281959 21909365 := bstep (se 5 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 21909365 = 2054003) B2054003
theorem B2887577 : Blo 1281959 2887577 := bstep (se 2 (by rfl) ⟨1082841, by rfl⟩ : syracuseStep 2887577 = 2165683) B2165683
theorem B1281963 : Blo 1281959 1281963 := bstep (se 1 (by rfl) ⟨961472, by rfl⟩ : syracuseStep 1281963 = 1922945) B1922945
theorem B4329395 : Blo 1281959 4329395 := bstep (se 1 (by rfl) ⟨3247046, by rfl⟩ : syracuseStep 4329395 = 6494093) B6494093
theorem B1281975 : Blo 1281959 1281975 := bstep (se 1 (by rfl) ⟨961481, by rfl⟩ : syracuseStep 1281975 = 1922963) B1922963
theorem B1281995 : Blo 1281959 1281995 := bstep (se 1 (by rfl) ⟨961496, by rfl⟩ : syracuseStep 1281995 = 1922993) B1922993
theorem B1282007 : Blo 1281959 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B1282027 : Blo 1281959 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B2887667 : Blo 1281959 2887667 := bstep (se 1 (by rfl) ⟨2165750, by rfl⟩ : syracuseStep 2887667 = 4331501) B4331501
theorem B1282039 : Blo 1281959 1282039 := bstep (se 1 (by rfl) ⟨961529, by rfl⟩ : syracuseStep 1282039 = 1923059) B1923059
theorem B1282059 : Blo 1281959 1282059 := bstep (se 1 (by rfl) ⟨961544, by rfl⟩ : syracuseStep 1282059 = 1923089) B1923089
theorem B5476369 : Blo 1281959 5476369 := bstep (se 2 (by rfl) ⟨2053638, by rfl⟩ : syracuseStep 5476369 = 4107277) B4107277
theorem B1282071 : Blo 1281959 1282071 := bstep (se 1 (by rfl) ⟨961553, by rfl⟩ : syracuseStep 1282071 = 1923107) B1923107
theorem B2887703 : Blo 1281959 2887703 := bstep (se 1 (by rfl) ⟨2165777, by rfl⟩ : syracuseStep 2887703 = 4331555) B4331555
theorem B1282091 : Blo 1281959 1282091 := bstep (se 1 (by rfl) ⟨961568, by rfl⟩ : syracuseStep 1282091 = 1923137) B1923137
theorem B1282103 : Blo 1281959 1282103 := bstep (se 1 (by rfl) ⟨961577, by rfl⟩ : syracuseStep 1282103 = 1923155) B1923155
theorem B1282123 : Blo 1281959 1282123 := bstep (se 1 (by rfl) ⟨961592, by rfl⟩ : syracuseStep 1282123 = 1923185) B1923185
theorem B1282135 : Blo 1281959 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B1282155 : Blo 1281959 1282155 := bstep (se 1 (by rfl) ⟨961616, by rfl⟩ : syracuseStep 1282155 = 1923233) B1923233
theorem B1282167 : Blo 1281959 1282167 := bstep (se 1 (by rfl) ⟨961625, by rfl⟩ : syracuseStep 1282167 = 1923251) B1923251
theorem B1282187 : Blo 1281959 1282187 := bstep (se 1 (by rfl) ⟨961640, by rfl⟩ : syracuseStep 1282187 = 1923281) B1923281
theorem B1282199 : Blo 1281959 1282199 := bstep (se 1 (by rfl) ⟨961649, by rfl⟩ : syracuseStep 1282199 = 1923299) B1923299
theorem B6492311 : Blo 1281959 6492311 := bstep (se 1 (by rfl) ⟨4869233, by rfl⟩ : syracuseStep 6492311 = 9738467) B9738467
theorem B3469463 : Blo 1281959 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B1282219 : Blo 1281959 1282219 := bstep (se 1 (by rfl) ⟨961664, by rfl⟩ : syracuseStep 1282219 = 1923329) B1923329
theorem B1282231 : Blo 1281959 1282231 := bstep (se 1 (by rfl) ⟨961673, by rfl⟩ : syracuseStep 1282231 = 1923347) B1923347
theorem B4165825 : Blo 1281959 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B4329665 : Blo 1281959 4329665 := bstep (se 2 (by rfl) ⟨1623624, by rfl⟩ : syracuseStep 4329665 = 3247249) B3247249
theorem B1282251 : Blo 1281959 1282251 := bstep (se 1 (by rfl) ⟨961688, by rfl⟩ : syracuseStep 1282251 = 1923377) B1923377
theorem B2887883 : Blo 1281959 2887883 := bstep (se 1 (by rfl) ⟨2165912, by rfl⟩ : syracuseStep 2887883 = 4331825) B4331825
theorem B1282263 : Blo 1281959 1282263 := bstep (se 1 (by rfl) ⟨961697, by rfl⟩ : syracuseStep 1282263 = 1923395) B1923395
theorem B1282283 : Blo 1281959 1282283 := bstep (se 1 (by rfl) ⟨961712, by rfl⟩ : syracuseStep 1282283 = 1923425) B1923425
theorem B1282295 : Blo 1281959 1282295 := bstep (se 1 (by rfl) ⟨961721, by rfl⟩ : syracuseStep 1282295 = 1923443) B1923443
theorem B2887937 : Blo 1281959 2887937 := bstep (se 2 (by rfl) ⟨1082976, by rfl⟩ : syracuseStep 2887937 = 2165953) B2165953
theorem B1282315 : Blo 1281959 1282315 := bstep (se 1 (by rfl) ⟨961736, by rfl⟩ : syracuseStep 1282315 = 1923473) B1923473
theorem B1282327 : Blo 1281959 1282327 := bstep (se 1 (by rfl) ⟨961745, by rfl⟩ : syracuseStep 1282327 = 1923491) B1923491
theorem B1282347 : Blo 1281959 1282347 := bstep (se 1 (by rfl) ⟨961760, by rfl⟩ : syracuseStep 1282347 = 1923521) B1923521
theorem B2437427 : Blo 1281959 2437427 := bstep (se 1 (by rfl) ⟨1828070, by rfl⟩ : syracuseStep 2437427 = 3656141) B3656141
theorem B1282359 : Blo 1281959 1282359 := bstep (se 1 (by rfl) ⟨961769, by rfl⟩ : syracuseStep 1282359 = 1923539) B1923539
theorem B9736523 : Blo 1281959 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B1282379 : Blo 1281959 1282379 := bstep (se 1 (by rfl) ⟨961784, by rfl⟩ : syracuseStep 1282379 = 1923569) B1923569
theorem B1282391 : Blo 1281959 1282391 := bstep (se 1 (by rfl) ⟨961793, by rfl⟩ : syracuseStep 1282391 = 1923587) B1923587
theorem B2437465 : Blo 1281959 2437465 := bstep (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) B1828099
theorem B1282411 : Blo 1281959 1282411 := bstep (se 1 (by rfl) ⟨961808, by rfl⟩ : syracuseStep 1282411 = 1923617) B1923617
theorem B1282423 : Blo 1281959 1282423 := bstep (se 1 (by rfl) ⟨961817, by rfl⟩ : syracuseStep 1282423 = 1923635) B1923635
theorem B1282443 : Blo 1281959 1282443 := bstep (se 1 (by rfl) ⟨961832, by rfl⟩ : syracuseStep 1282443 = 1923665) B1923665
theorem B1282455 : Blo 1281959 1282455 := bstep (se 1 (by rfl) ⟨961841, by rfl⟩ : syracuseStep 1282455 = 1923683) B1923683
theorem B1282475 : Blo 1281959 1282475 := bstep (se 1 (by rfl) ⟨961856, by rfl⟩ : syracuseStep 1282475 = 1923713) B1923713
theorem B1282487 : Blo 1281959 1282487 := bstep (se 1 (by rfl) ⟨961865, by rfl⟩ : syracuseStep 1282487 = 1923731) B1923731
theorem B1282507 : Blo 1281959 1282507 := bstep (se 1 (by rfl) ⟨961880, by rfl⟩ : syracuseStep 1282507 = 1923761) B1923761
theorem B1282519 : Blo 1281959 1282519 := bstep (se 1 (by rfl) ⟨961889, by rfl⟩ : syracuseStep 1282519 = 1923779) B1923779
theorem B2888153 : Blo 1281959 2888153 := bstep (se 2 (by rfl) ⟨1083057, by rfl⟩ : syracuseStep 2888153 = 2166115) B2166115
theorem B1282539 : Blo 1281959 1282539 := bstep (se 1 (by rfl) ⟨961904, by rfl⟩ : syracuseStep 1282539 = 1923809) B1923809
theorem B1282551 : Blo 1281959 1282551 := bstep (se 1 (by rfl) ⟨961913, by rfl⟩ : syracuseStep 1282551 = 1923827) B1923827
theorem B1282571 : Blo 1281959 1282571 := bstep (se 1 (by rfl) ⟨961928, by rfl⟩ : syracuseStep 1282571 = 1923857) B1923857
theorem B1282583 : Blo 1281959 1282583 := bstep (se 1 (by rfl) ⟨961937, by rfl⟩ : syracuseStep 1282583 = 1923875) B1923875
theorem B2601497 : Blo 1281959 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B1282603 : Blo 1281959 1282603 := bstep (se 1 (by rfl) ⟨961952, by rfl⟩ : syracuseStep 1282603 = 1923905) B1923905
theorem B2888243 : Blo 1281959 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B1282615 : Blo 1281959 1282615 := bstep (se 1 (by rfl) ⟨961961, by rfl⟩ : syracuseStep 1282615 = 1923923) B1923923
theorem B1282635 : Blo 1281959 1282635 := bstep (se 1 (by rfl) ⟨961976, by rfl⟩ : syracuseStep 1282635 = 1923953) B1923953
theorem B1282647 : Blo 1281959 1282647 := bstep (se 1 (by rfl) ⟨961985, by rfl⟩ : syracuseStep 1282647 = 1923971) B1923971
theorem B2888279 : Blo 1281959 2888279 := bstep (se 1 (by rfl) ⟨2166209, by rfl⟩ : syracuseStep 2888279 = 4332419) B4332419
theorem B6165085 : Blo 1281959 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B1282667 : Blo 1281959 1282667 := bstep (se 1 (by rfl) ⟨962000, by rfl⟩ : syracuseStep 1282667 = 1924001) B1924001
theorem B1282679 : Blo 1281959 1282679 := bstep (se 1 (by rfl) ⟨962009, by rfl⟩ : syracuseStep 1282679 = 1924019) B1924019
theorem B1282699 : Blo 1281959 1282699 := bstep (se 1 (by rfl) ⟨962024, by rfl⟩ : syracuseStep 1282699 = 1924049) B1924049
theorem B1282711 : Blo 1281959 1282711 := bstep (se 1 (by rfl) ⟨962033, by rfl⟩ : syracuseStep 1282711 = 1924067) B1924067
theorem B13169303 : Blo 1281959 13169303 := bstep (se 1 (by rfl) ⟨9876977, by rfl⟩ : syracuseStep 13169303 = 19753955) B19753955
theorem B1282731 : Blo 1281959 1282731 := bstep (se 1 (by rfl) ⟨962048, by rfl⟩ : syracuseStep 1282731 = 1924097) B1924097
theorem B3248819 : Blo 1281959 3248819 := bstep (se 1 (by rfl) ⟨2436614, by rfl⟩ : syracuseStep 3248819 = 4873229) B4873229
theorem B1282743 : Blo 1281959 1282743 := bstep (se 1 (by rfl) ⟨962057, by rfl⟩ : syracuseStep 1282743 = 1924115) B1924115
theorem B1282763 : Blo 1281959 1282763 := bstep (se 1 (by rfl) ⟨962072, by rfl⟩ : syracuseStep 1282763 = 1924145) B1924145
theorem B1282775 : Blo 1281959 1282775 := bstep (se 1 (by rfl) ⟨962081, by rfl⟩ : syracuseStep 1282775 = 1924163) B1924163
theorem B4625113 : Blo 1281959 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B4330205 : Blo 1281959 4330205 := bstep (se 3 (by rfl) ⟨811913, by rfl⟩ : syracuseStep 4330205 = 1623827) B1623827
theorem B1282795 : Blo 1281959 1282795 := bstep (se 1 (by rfl) ⟨962096, by rfl⟩ : syracuseStep 1282795 = 1924193) B1924193
theorem B1282807 : Blo 1281959 1282807 := bstep (se 1 (by rfl) ⟨962105, by rfl⟩ : syracuseStep 1282807 = 1924211) B1924211
theorem B1282827 : Blo 1281959 1282827 := bstep (se 1 (by rfl) ⟨962120, by rfl⟩ : syracuseStep 1282827 = 1924241) B1924241
theorem B2888459 : Blo 1281959 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B1282839 : Blo 1281959 1282839 := bstep (se 1 (by rfl) ⟨962129, by rfl⟩ : syracuseStep 1282839 = 1924259) B1924259
theorem B1282859 : Blo 1281959 1282859 := bstep (se 1 (by rfl) ⟨962144, by rfl⟩ : syracuseStep 1282859 = 1924289) B1924289
theorem B1282871 : Blo 1281959 1282871 := bstep (se 1 (by rfl) ⟨962153, by rfl⟩ : syracuseStep 1282871 = 1924307) B1924307
theorem B2888513 : Blo 1281959 2888513 := bstep (se 2 (by rfl) ⟨1083192, by rfl⟩ : syracuseStep 2888513 = 2166385) B2166385
theorem B1282891 : Blo 1281959 1282891 := bstep (se 1 (by rfl) ⟨962168, by rfl⟩ : syracuseStep 1282891 = 1924337) B1924337
theorem B1282903 : Blo 1281959 1282903 := bstep (se 1 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 1282903 = 1924355) B1924355
theorem B1282923 : Blo 1281959 1282923 := bstep (se 1 (by rfl) ⟨962192, by rfl⟩ : syracuseStep 1282923 = 1924385) B1924385
theorem B1282935 : Blo 1281959 1282935 := bstep (se 1 (by rfl) ⟨962201, by rfl⟩ : syracuseStep 1282935 = 1924403) B1924403
theorem B1561483 : Blo 1281959 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1282955 : Blo 1281959 1282955 := bstep (se 1 (by rfl) ⟨962216, by rfl⟩ : syracuseStep 1282955 = 1924433) B1924433
theorem B2741131 : Blo 1281959 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B1282967 : Blo 1281959 1282967 := bstep (se 1 (by rfl) ⟨962225, by rfl⟩ : syracuseStep 1282967 = 1924451) B1924451
theorem B1282987 : Blo 1281959 1282987 := bstep (se 1 (by rfl) ⟨962240, by rfl⟩ : syracuseStep 1282987 = 1924481) B1924481
theorem B1282999 : Blo 1281959 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B1283019 : Blo 1281959 1283019 := bstep (se 1 (by rfl) ⟨962264, by rfl⟩ : syracuseStep 1283019 = 1924529) B1924529
theorem B1283031 : Blo 1281959 1283031 := bstep (se 1 (by rfl) ⟨962273, by rfl⟩ : syracuseStep 1283031 = 1924547) B1924547
theorem B1283051 : Blo 1281959 1283051 := bstep (se 1 (by rfl) ⟨962288, by rfl⟩ : syracuseStep 1283051 = 1924577) B1924577
theorem B1283063 : Blo 1281959 1283063 := bstep (se 1 (by rfl) ⟨962297, by rfl⟩ : syracuseStep 1283063 = 1924595) B1924595
theorem B1283083 : Blo 1281959 1283083 := bstep (se 1 (by rfl) ⟨962312, by rfl⟩ : syracuseStep 1283083 = 1924625) B1924625
theorem B1283095 : Blo 1281959 1283095 := bstep (se 1 (by rfl) ⟨962321, by rfl⟩ : syracuseStep 1283095 = 1924643) B1924643
theorem B2888729 : Blo 1281959 2888729 := bstep (se 2 (by rfl) ⟨1083273, by rfl⟩ : syracuseStep 2888729 = 2166547) B2166547
theorem B1283115 : Blo 1281959 1283115 := bstep (se 1 (by rfl) ⟨962336, by rfl⟩ : syracuseStep 1283115 = 1924673) B1924673
theorem B1283127 : Blo 1281959 1283127 := bstep (se 1 (by rfl) ⟨962345, by rfl⟩ : syracuseStep 1283127 = 1924691) B1924691
theorem B1283147 : Blo 1281959 1283147 := bstep (se 1 (by rfl) ⟨962360, by rfl⟩ : syracuseStep 1283147 = 1924721) B1924721
theorem B1283159 : Blo 1281959 1283159 := bstep (se 1 (by rfl) ⟨962369, by rfl⟩ : syracuseStep 1283159 = 1924739) B1924739
theorem B1283179 : Blo 1281959 1283179 := bstep (se 1 (by rfl) ⟨962384, by rfl⟩ : syracuseStep 1283179 = 1924769) B1924769
theorem B2888819 : Blo 1281959 2888819 := bstep (se 1 (by rfl) ⟨2166614, by rfl⟩ : syracuseStep 2888819 = 4333229) B4333229
theorem B1283191 : Blo 1281959 1283191 := bstep (se 1 (by rfl) ⟨962393, by rfl⟩ : syracuseStep 1283191 = 1924787) B1924787
theorem B4871299 : Blo 1281959 4871299 := bstep (se 1 (by rfl) ⟨3653474, by rfl⟩ : syracuseStep 4871299 = 7306949) B7306949
theorem B1283211 : Blo 1281959 1283211 := bstep (se 1 (by rfl) ⟨962408, by rfl⟩ : syracuseStep 1283211 = 1924817) B1924817
theorem B1283223 : Blo 1281959 1283223 := bstep (se 1 (by rfl) ⟨962417, by rfl⟩ : syracuseStep 1283223 = 1924835) B1924835
theorem B2888855 : Blo 1281959 2888855 := bstep (se 1 (by rfl) ⟨2166641, by rfl⟩ : syracuseStep 2888855 = 4333283) B4333283
theorem B1283243 : Blo 1281959 1283243 := bstep (se 1 (by rfl) ⟨962432, by rfl⟩ : syracuseStep 1283243 = 1924865) B1924865
theorem B1283255 : Blo 1281959 1283255 := bstep (se 1 (by rfl) ⟨962441, by rfl⟩ : syracuseStep 1283255 = 1924883) B1924883
theorem B1283275 : Blo 1281959 1283275 := bstep (se 1 (by rfl) ⟨962456, by rfl⟩ : syracuseStep 1283275 = 1924913) B1924913
theorem B3249355 : Blo 1281959 3249355 := bstep (se 1 (by rfl) ⟨2437016, by rfl⟩ : syracuseStep 3249355 = 4874033) B4874033
theorem B1283287 : Blo 1281959 1283287 := bstep (se 1 (by rfl) ⟨962465, by rfl⟩ : syracuseStep 1283287 = 1924931) B1924931
theorem B2741465 : Blo 1281959 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B1283307 : Blo 1281959 1283307 := bstep (se 1 (by rfl) ⟨962480, by rfl⟩ : syracuseStep 1283307 = 1924961) B1924961
theorem B1283319 : Blo 1281959 1283319 := bstep (se 1 (by rfl) ⟨962489, by rfl⟩ : syracuseStep 1283319 = 1924979) B1924979
theorem B1283339 : Blo 1281959 1283339 := bstep (se 1 (by rfl) ⟨962504, by rfl⟩ : syracuseStep 1283339 = 1925009) B1925009
theorem B1283351 : Blo 1281959 1283351 := bstep (se 1 (by rfl) ⟨962513, by rfl⟩ : syracuseStep 1283351 = 1925027) B1925027
theorem B1283371 : Blo 1281959 1283371 := bstep (se 1 (by rfl) ⟨962528, by rfl⟩ : syracuseStep 1283371 = 1925057) B1925057
theorem B33314093 : Blo 1281959 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B2602291 : Blo 1281959 2602291 := bstep (se 1 (by rfl) ⟨1951718, by rfl⟩ : syracuseStep 2602291 = 3903437) B3903437
theorem B1283383 : Blo 1281959 1283383 := bstep (se 1 (by rfl) ⟨962537, by rfl⟩ : syracuseStep 1283383 = 1925075) B1925075
theorem B1283403 : Blo 1281959 1283403 := bstep (se 1 (by rfl) ⟨962552, by rfl⟩ : syracuseStep 1283403 = 1925105) B1925105
theorem B1283415 : Blo 1281959 1283415 := bstep (se 1 (by rfl) ⟨962561, by rfl⟩ : syracuseStep 1283415 = 1925123) B1925123
theorem B3249497 : Blo 1281959 3249497 := bstep (se 2 (by rfl) ⟨1218561, by rfl⟩ : syracuseStep 3249497 = 2437123) B2437123
theorem B9745757 : Blo 1281959 9745757 := bstep (se 3 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 9745757 = 3654659) B3654659
theorem B1283435 : Blo 1281959 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B1283447 : Blo 1281959 1283447 := bstep (se 1 (by rfl) ⟨962585, by rfl⟩ : syracuseStep 1283447 = 1925171) B1925171
theorem B1283467 : Blo 1281959 1283467 := bstep (se 1 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 1283467 = 1925201) B1925201
theorem B1283479 : Blo 1281959 1283479 := bstep (se 1 (by rfl) ⟨962609, by rfl⟩ : syracuseStep 1283479 = 1925219) B1925219
theorem B1283499 : Blo 1281959 1283499 := bstep (se 1 (by rfl) ⟨962624, by rfl⟩ : syracuseStep 1283499 = 1925249) B1925249
theorem B4871603 : Blo 1281959 4871603 := bstep (se 1 (by rfl) ⟨3653702, by rfl⟩ : syracuseStep 4871603 = 7307405) B7307405
theorem B5854643 : Blo 1281959 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B1283511 : Blo 1281959 1283511 := bstep (se 1 (by rfl) ⟨962633, by rfl⟩ : syracuseStep 1283511 = 1925267) B1925267
theorem B1283531 : Blo 1281959 1283531 := bstep (se 1 (by rfl) ⟨962648, by rfl⟩ : syracuseStep 1283531 = 1925297) B1925297
theorem B1283543 : Blo 1281959 1283543 := bstep (se 1 (by rfl) ⟨962657, by rfl⟩ : syracuseStep 1283543 = 1925315) B1925315
theorem B1283563 : Blo 1281959 1283563 := bstep (se 1 (by rfl) ⟨962672, by rfl⟩ : syracuseStep 1283563 = 1925345) B1925345
theorem B1283575 : Blo 1281959 1283575 := bstep (se 1 (by rfl) ⟨962681, by rfl⟩ : syracuseStep 1283575 = 1925363) B1925363
theorem B1283595 : Blo 1281959 1283595 := bstep (se 1 (by rfl) ⟨962696, by rfl⟩ : syracuseStep 1283595 = 1925393) B1925393
theorem B3651095 : Blo 1281959 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B1283607 : Blo 1281959 1283607 := bstep (se 1 (by rfl) ⟨962705, by rfl⟩ : syracuseStep 1283607 = 1925411) B1925411
theorem B1283627 : Blo 1281959 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B1283639 : Blo 1281959 1283639 := bstep (se 1 (by rfl) ⟨962729, by rfl⟩ : syracuseStep 1283639 = 1925459) B1925459
theorem B7411265 : Blo 1281959 7411265 := bstep (se 2 (by rfl) ⟨2779224, by rfl⟩ : syracuseStep 7411265 = 5558449) B5558449
theorem B1283659 : Blo 1281959 1283659 := bstep (se 1 (by rfl) ⟨962744, by rfl⟩ : syracuseStep 1283659 = 1925489) B1925489
theorem B1283671 : Blo 1281959 1283671 := bstep (se 1 (by rfl) ⟨962753, by rfl⟩ : syracuseStep 1283671 = 1925507) B1925507
theorem B1283691 : Blo 1281959 1283691 := bstep (se 1 (by rfl) ⟨962768, by rfl⟩ : syracuseStep 1283691 = 1925537) B1925537
theorem B1283703 : Blo 1281959 1283703 := bstep (se 1 (by rfl) ⟨962777, by rfl⟩ : syracuseStep 1283703 = 1925555) B1925555
theorem B5199491 : Blo 1281959 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B1283723 : Blo 1281959 1283723 := bstep (se 1 (by rfl) ⟨962792, by rfl⟩ : syracuseStep 1283723 = 1925585) B1925585
theorem B1283735 : Blo 1281959 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B1283755 : Blo 1281959 1283755 := bstep (se 1 (by rfl) ⟨962816, by rfl⟩ : syracuseStep 1283755 = 1925633) B1925633
theorem B1283767 : Blo 1281959 1283767 := bstep (se 1 (by rfl) ⟨962825, by rfl⟩ : syracuseStep 1283767 = 1925651) B1925651
theorem B1283787 : Blo 1281959 1283787 := bstep (se 1 (by rfl) ⟨962840, by rfl⟩ : syracuseStep 1283787 = 1925681) B1925681
theorem B1283799 : Blo 1281959 1283799 := bstep (se 1 (by rfl) ⟨962849, by rfl⟩ : syracuseStep 1283799 = 1925699) B1925699
theorem B1283819 : Blo 1281959 1283819 := bstep (se 1 (by rfl) ⟨962864, by rfl⟩ : syracuseStep 1283819 = 1925729) B1925729
theorem B1283831 : Blo 1281959 1283831 := bstep (se 1 (by rfl) ⟨962873, by rfl⟩ : syracuseStep 1283831 = 1925747) B1925747
theorem B1283851 : Blo 1281959 1283851 := bstep (se 1 (by rfl) ⟨962888, by rfl⟩ : syracuseStep 1283851 = 1925777) B1925777
theorem B1283863 : Blo 1281959 1283863 := bstep (se 1 (by rfl) ⟨962897, by rfl⟩ : syracuseStep 1283863 = 1925795) B1925795
theorem B1283883 : Blo 1281959 1283883 := bstep (se 1 (by rfl) ⟨962912, by rfl⟩ : syracuseStep 1283883 = 1925825) B1925825
theorem B1283895 : Blo 1281959 1283895 := bstep (se 1 (by rfl) ⟨962921, by rfl⟩ : syracuseStep 1283895 = 1925843) B1925843
theorem B4331339 : Blo 1281959 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1283915 : Blo 1281959 1283915 := bstep (se 1 (by rfl) ⟨962936, by rfl⟩ : syracuseStep 1283915 = 1925873) B1925873
theorem B1283927 : Blo 1281959 1283927 := bstep (se 1 (by rfl) ⟨962945, by rfl⟩ : syracuseStep 1283927 = 1925891) B1925891
theorem B1283947 : Blo 1281959 1283947 := bstep (se 1 (by rfl) ⟨962960, by rfl⟩ : syracuseStep 1283947 = 1925921) B1925921
theorem B1283959 : Blo 1281959 1283959 := bstep (se 1 (by rfl) ⟨962969, by rfl⟩ : syracuseStep 1283959 = 1925939) B1925939
theorem B1922969 : Blo 1281959 1922969 := bstep (se 2 (by rfl) ⟨721113, by rfl⟩ : syracuseStep 1922969 = 1442227) B1442227
theorem B1923083 : Blo 1281959 1923083 := bstep (se 1 (by rfl) ⟨1442312, by rfl⟩ : syracuseStep 1923083 = 2884625) B2884625
theorem B1923095 : Blo 1281959 1923095 := bstep (se 1 (by rfl) ⟨1442321, by rfl⟩ : syracuseStep 1923095 = 2884643) B2884643
theorem B4872257 : Blo 1281959 4872257 := bstep (se 2 (by rfl) ⟨1827096, by rfl⟩ : syracuseStep 4872257 = 3654193) B3654193
theorem B4626497 : Blo 1281959 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B1923161 : Blo 1281959 1923161 := bstep (se 2 (by rfl) ⟨721185, by rfl⟩ : syracuseStep 1923161 = 1442371) B1442371
theorem B4331609 : Blo 1281959 4331609 := bstep (se 2 (by rfl) ⟨1624353, by rfl⟩ : syracuseStep 4331609 = 3248707) B3248707
theorem B6936677 : Blo 1281959 6936677 := bstep (se 4 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 6936677 = 1300627) B1300627
theorem B14620823 : Blo 1281959 14620823 := bstep (se 1 (by rfl) ⟨10965617, by rfl⟩ : syracuseStep 14620823 = 21931235) B21931235
theorem B1923275 : Blo 1281959 1923275 := bstep (se 1 (by rfl) ⟨1442456, by rfl⟩ : syracuseStep 1923275 = 2884913) B2884913
theorem B1923287 : Blo 1281959 1923287 := bstep (se 1 (by rfl) ⟨1442465, by rfl⟩ : syracuseStep 1923287 = 2884931) B2884931
theorem B1923353 : Blo 1281959 1923353 := bstep (se 2 (by rfl) ⟨721257, by rfl⟩ : syracuseStep 1923353 = 1442515) B1442515
theorem B1923467 : Blo 1281959 1923467 := bstep (se 1 (by rfl) ⟨1442600, by rfl⟩ : syracuseStep 1923467 = 2885201) B2885201
theorem B1923479 : Blo 1281959 1923479 := bstep (se 1 (by rfl) ⟨1442609, by rfl⟩ : syracuseStep 1923479 = 2885219) B2885219
theorem B13162931 : Blo 1281959 13162931 := bstep (se 1 (by rfl) ⟨9872198, by rfl⟩ : syracuseStep 13162931 = 19744397) B19744397
theorem B1923545 : Blo 1281959 1923545 := bstep (se 2 (by rfl) ⟨721329, by rfl⟩ : syracuseStep 1923545 = 1442659) B1442659
theorem B1825291 : Blo 1281959 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B6937105 : Blo 1281959 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B8337937 : Blo 1281959 8337937 := bstep (se 2 (by rfl) ⟨3126726, by rfl⟩ : syracuseStep 8337937 = 6253453) B6253453
theorem B1923659 : Blo 1281959 1923659 := bstep (se 1 (by rfl) ⟨1442744, by rfl⟩ : syracuseStep 1923659 = 2885489) B2885489
theorem B1923671 : Blo 1281959 1923671 := bstep (se 1 (by rfl) ⟨1442753, by rfl⟩ : syracuseStep 1923671 = 2885507) B2885507
theorem B1923737 : Blo 1281959 1923737 := bstep (se 2 (by rfl) ⟨721401, by rfl⟩ : syracuseStep 1923737 = 1442803) B1442803
theorem B16431821 : Blo 1281959 16431821 := bstep (se 3 (by rfl) ⟨3080966, by rfl⟩ : syracuseStep 16431821 = 6161933) B6161933
theorem B1923851 : Blo 1281959 1923851 := bstep (se 1 (by rfl) ⟨1442888, by rfl⟩ : syracuseStep 1923851 = 2885777) B2885777
theorem B1923863 : Blo 1281959 1923863 := bstep (se 1 (by rfl) ⟨1442897, by rfl⟩ : syracuseStep 1923863 = 2885795) B2885795
theorem B4332311 : Blo 1281959 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B3652427 : Blo 1281959 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B1923929 : Blo 1281959 1923929 := bstep (se 2 (by rfl) ⟨721473, by rfl⟩ : syracuseStep 1923929 = 1442947) B1442947
theorem B110894021 : Blo 1281959 110894021 := bstep (se 4 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 110894021 = 20792629) B20792629
theorem B1924043 : Blo 1281959 1924043 := bstep (se 1 (by rfl) ⟨1443032, by rfl⟩ : syracuseStep 1924043 = 2886065) B2886065
theorem B1924055 : Blo 1281959 1924055 := bstep (se 1 (by rfl) ⟨1443041, by rfl⟩ : syracuseStep 1924055 = 2886083) B2886083
theorem B5479427 : Blo 1281959 5479427 := bstep (se 1 (by rfl) ⟨4109570, by rfl⟩ : syracuseStep 5479427 = 8219141) B8219141
theorem B5200919 : Blo 1281959 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B1924121 : Blo 1281959 1924121 := bstep (se 2 (by rfl) ⟨721545, by rfl⟩ : syracuseStep 1924121 = 1443091) B1443091
theorem B10959947 : Blo 1281959 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B1645655 : Blo 1281959 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1924235 : Blo 1281959 1924235 := bstep (se 1 (by rfl) ⟨1443176, by rfl⟩ : syracuseStep 1924235 = 2886353) B2886353
theorem B1924247 : Blo 1281959 1924247 := bstep (se 1 (by rfl) ⟨1443185, by rfl⟩ : syracuseStep 1924247 = 2886371) B2886371
theorem B1924313 : Blo 1281959 1924313 := bstep (se 2 (by rfl) ⟨721617, by rfl⟩ : syracuseStep 1924313 = 1443235) B1443235
theorem B4873517 : Blo 1281959 4873517 := bstep (se 3 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 4873517 = 1827569) B1827569
theorem B4750643 : Blo 1281959 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B4332851 : Blo 1281959 4332851 := bstep (se 1 (by rfl) ⟨3249638, by rfl⟩ : syracuseStep 4332851 = 6499277) B6499277
theorem B1924427 : Blo 1281959 1924427 := bstep (se 1 (by rfl) ⟨1443320, by rfl⟩ : syracuseStep 1924427 = 2886641) B2886641
theorem B4873547 : Blo 1281959 4873547 := bstep (se 1 (by rfl) ⟨3655160, by rfl⟩ : syracuseStep 4873547 = 7310321) B7310321
theorem B1924439 : Blo 1281959 1924439 := bstep (se 1 (by rfl) ⟨1443329, by rfl⟩ : syracuseStep 1924439 = 2886659) B2886659
theorem B1924505 : Blo 1281959 1924505 := bstep (se 2 (by rfl) ⟨721689, by rfl⟩ : syracuseStep 1924505 = 1443379) B1443379
theorem B1924619 : Blo 1281959 1924619 := bstep (se 1 (by rfl) ⟨1443464, by rfl⟩ : syracuseStep 1924619 = 2886929) B2886929
theorem B1924631 : Blo 1281959 1924631 := bstep (se 1 (by rfl) ⟨1443473, by rfl⟩ : syracuseStep 1924631 = 2886947) B2886947
theorem B4333121 : Blo 1281959 4333121 := bstep (se 2 (by rfl) ⟨1624920, by rfl⟩ : syracuseStep 4333121 = 3249841) B3249841
theorem B18497099 : Blo 1281959 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B1924697 : Blo 1281959 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B6495875 : Blo 1281959 6495875 := bstep (se 1 (by rfl) ⟨4871906, by rfl⟩ : syracuseStep 6495875 = 9743813) B9743813
theorem B1924811 : Blo 1281959 1924811 := bstep (se 1 (by rfl) ⟨1443608, by rfl⟩ : syracuseStep 1924811 = 2887217) B2887217
theorem B1924823 : Blo 1281959 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1924889 : Blo 1281959 1924889 := bstep (se 2 (by rfl) ⟨721833, by rfl⟩ : syracuseStep 1924889 = 1443667) B1443667
theorem B1925003 : Blo 1281959 1925003 := bstep (se 1 (by rfl) ⟨1443752, by rfl⟩ : syracuseStep 1925003 = 2887505) B2887505
theorem B1925015 : Blo 1281959 1925015 := bstep (se 1 (by rfl) ⟨1443761, by rfl⟩ : syracuseStep 1925015 = 2887523) B2887523
theorem B2924441 : Blo 1281959 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B1925081 : Blo 1281959 1925081 := bstep (se 2 (by rfl) ⟨721905, by rfl⟩ : syracuseStep 1925081 = 1443811) B1443811
theorem B4874201 : Blo 1281959 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B1925135 : Blo 1281959 1925135 := bstep (se 1 (by rfl) ⟨1443851, by rfl⟩ : syracuseStep 1925135 = 2887703) B2887703
theorem B1925177 : Blo 1281959 1925177 := bstep (se 2 (by rfl) ⟨721941, by rfl⟩ : syracuseStep 1925177 = 1443883) B1443883
theorem B1925255 : Blo 1281959 1925255 := bstep (se 1 (by rfl) ⟨1443941, by rfl⟩ : syracuseStep 1925255 = 2887883) B2887883
theorem B1925291 : Blo 1281959 1925291 := bstep (se 1 (by rfl) ⟨1443968, by rfl⟩ : syracuseStep 1925291 = 2887937) B2887937
theorem B1925321 : Blo 1281959 1925321 := bstep (se 2 (by rfl) ⟨721995, by rfl⟩ : syracuseStep 1925321 = 1443991) B1443991
theorem B5931265 : Blo 1281959 5931265 := bstep (se 2 (by rfl) ⟨2224224, by rfl⟩ : syracuseStep 5931265 = 4448449) B4448449
theorem B5554433 : Blo 1281959 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1925435 : Blo 1281959 1925435 := bstep (se 1 (by rfl) ⟨1444076, by rfl⟩ : syracuseStep 1925435 = 2888153) B2888153
theorem B27066689 : Blo 1281959 27066689 := bstep (se 2 (by rfl) ⟨10150008, by rfl⟩ : syracuseStep 27066689 = 20300017) B20300017
theorem B1925495 : Blo 1281959 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B1925519 : Blo 1281959 1925519 := bstep (se 1 (by rfl) ⟨1444139, by rfl⟩ : syracuseStep 1925519 = 2888279) B2888279
theorem B1925561 : Blo 1281959 1925561 := bstep (se 2 (by rfl) ⟨722085, by rfl⟩ : syracuseStep 1925561 = 1444171) B1444171
theorem B1925639 : Blo 1281959 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B1925675 : Blo 1281959 1925675 := bstep (se 1 (by rfl) ⟨1444256, by rfl⟩ : syracuseStep 1925675 = 2888513) B2888513
theorem B1622587 : Blo 1281959 1622587 := bstep (se 1 (by rfl) ⟨1216940, by rfl⟩ : syracuseStep 1622587 = 2433881) B2433881
theorem B1925705 : Blo 1281959 1925705 := bstep (se 2 (by rfl) ⟨722139, by rfl⟩ : syracuseStep 1925705 = 1444279) B1444279
theorem B14811767 : Blo 1281959 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B59294339 : Blo 1281959 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B2433721 : Blo 1281959 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B1925819 : Blo 1281959 1925819 := bstep (se 1 (by rfl) ⟨1444364, by rfl⟩ : syracuseStep 1925819 = 2888729) B2888729
theorem B9249473 : Blo 1281959 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B11117249 : Blo 1281959 11117249 := bstep (se 2 (by rfl) ⟨4168968, by rfl⟩ : syracuseStep 11117249 = 8337937) B8337937
theorem B1925879 : Blo 1281959 1925879 := bstep (se 1 (by rfl) ⟨1444409, by rfl⟩ : syracuseStep 1925879 = 2888819) B2888819
theorem B1925903 : Blo 1281959 1925903 := bstep (se 1 (by rfl) ⟨1444427, by rfl⟩ : syracuseStep 1925903 = 2888855) B2888855
theorem B22209395 : Blo 1281959 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B1442695 : Blo 1281959 1442695 := bstep (se 1 (by rfl) ⟨1082021, by rfl⟩ : syracuseStep 1442695 = 2164043) B2164043
theorem B4113287 : Blo 1281959 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B6579089 : Blo 1281959 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B2884499 : Blo 1281959 2884499 := bstep (se 1 (by rfl) ⟨2163374, by rfl⟩ : syracuseStep 2884499 = 4326749) B4326749
theorem B6497171 : Blo 1281959 6497171 := bstep (se 1 (by rfl) ⟨4872878, by rfl⟩ : syracuseStep 6497171 = 9745757) B9745757
theorem B2884553 : Blo 1281959 2884553 := bstep (se 2 (by rfl) ⟨1081707, by rfl⟩ : syracuseStep 2884553 = 2163415) B2163415
theorem B2434063 : Blo 1281959 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B4940843 : Blo 1281959 4940843 := bstep (se 1 (by rfl) ⟨3705632, by rfl⟩ : syracuseStep 4940843 = 7411265) B7411265
theorem B1442875 : Blo 1281959 1442875 := bstep (se 1 (by rfl) ⟨1082156, by rfl⟩ : syracuseStep 1442875 = 2164313) B2164313
theorem B6587459 : Blo 1281959 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B3245143 : Blo 1281959 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B3466327 : Blo 1281959 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B7308407 : Blo 1281959 7308407 := bstep (se 1 (by rfl) ⟨5481305, by rfl⟩ : syracuseStep 7308407 = 10962611) B10962611
theorem B2163847 : Blo 1281959 2163847 := bstep (se 1 (by rfl) ⟨1622885, by rfl⟩ : syracuseStep 2163847 = 3245771) B3245771
theorem B3245447 : Blo 1281959 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B7800209 : Blo 1281959 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B4326803 : Blo 1281959 4326803 := bstep (se 1 (by rfl) ⟨3245102, by rfl⟩ : syracuseStep 4326803 = 6490205) B6490205
theorem B47449529 : Blo 1281959 47449529 := bstep (se 2 (by rfl) ⟨17793573, by rfl⟩ : syracuseStep 47449529 = 35587147) B35587147
theorem B1623559 : Blo 1281959 1623559 := bstep (se 1 (by rfl) ⟨1217669, by rfl⟩ : syracuseStep 1623559 = 2435339) B2435339
theorem B3245579 : Blo 1281959 3245579 := bstep (se 1 (by rfl) ⟨2434184, by rfl⟩ : syracuseStep 3245579 = 4868369) B4868369
theorem B1443343 : Blo 1281959 1443343 := bstep (se 1 (by rfl) ⟨1082507, by rfl⟩ : syracuseStep 1443343 = 2165015) B2165015
theorem B49325597 : Blo 1281959 49325597 := bstep (se 3 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 49325597 = 18497099) B18497099
theorem B8775287 : Blo 1281959 8775287 := bstep (se 1 (by rfl) ⟨6581465, by rfl⟩ : syracuseStep 8775287 = 13162931) B13162931
theorem B2885255 : Blo 1281959 2885255 := bstep (se 1 (by rfl) ⟨2163941, by rfl⟩ : syracuseStep 2885255 = 4327883) B4327883
theorem B9242383 : Blo 1281959 9242383 := bstep (se 1 (by rfl) ⟨6931787, by rfl⟩ : syracuseStep 9242383 = 13863575) B13863575
theorem B2164495 : Blo 1281959 2164495 := bstep (se 1 (by rfl) ⟨1623371, by rfl⟩ : syracuseStep 2164495 = 3246743) B3246743
theorem B10954547 : Blo 1281959 10954547 := bstep (se 1 (by rfl) ⟨8215910, by rfl⟩ : syracuseStep 10954547 = 16431821) B16431821
theorem B2885435 : Blo 1281959 2885435 := bstep (se 1 (by rfl) ⟨2164076, by rfl⟩ : syracuseStep 2885435 = 4328153) B4328153
theorem B7309115 : Blo 1281959 7309115 := bstep (se 1 (by rfl) ⟨5481836, by rfl⟩ : syracuseStep 7309115 = 10963673) B10963673
theorem B2434951 : Blo 1281959 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B1623979 : Blo 1281959 1623979 := bstep (se 1 (by rfl) ⟨1217984, by rfl⟩ : syracuseStep 1623979 = 2435969) B2435969
theorem B2885561 : Blo 1281959 2885561 := bstep (se 2 (by rfl) ⟨1082085, by rfl⟩ : syracuseStep 2885561 = 2164171) B2164171
theorem B1443847 : Blo 1281959 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B3246095 : Blo 1281959 3246095 := bstep (se 1 (by rfl) ⟨2434571, by rfl⟩ : syracuseStep 3246095 = 4869143) B4869143
theorem B3467279 : Blo 1281959 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B3655799 : Blo 1281959 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B1624207 : Blo 1281959 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B3246227 : Blo 1281959 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B10954925 : Blo 1281959 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B1444027 : Blo 1281959 1444027 := bstep (se 1 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 1444027 = 2166041) B2166041
theorem B2885903 : Blo 1281959 2885903 := bstep (se 1 (by rfl) ⟨2164427, by rfl⟩ : syracuseStep 2885903 = 4328855) B4328855
theorem B2885921 : Blo 1281959 2885921 := bstep (se 2 (by rfl) ⟨1082220, by rfl⟩ : syracuseStep 2885921 = 2164441) B2164441
theorem B2165035 : Blo 1281959 2165035 := bstep (se 1 (by rfl) ⟨1623776, by rfl⟩ : syracuseStep 2165035 = 3247553) B3247553
theorem B14051677 : Blo 1281959 14051677 := bstep (se 3 (by rfl) ⟨2634689, by rfl⟩ : syracuseStep 14051677 = 5269379) B5269379
theorem B2165177 : Blo 1281959 2165177 := bstep (se 2 (by rfl) ⟨811941, by rfl⟩ : syracuseStep 2165177 = 1623883) B1623883
theorem B4622891 : Blo 1281959 4622891 := bstep (se 1 (by rfl) ⟨3467168, by rfl⟩ : syracuseStep 4622891 = 6934337) B6934337
theorem B6490691 : Blo 1281959 6490691 := bstep (se 1 (by rfl) ⟨4868018, by rfl⟩ : syracuseStep 6490691 = 9736037) B9736037
theorem B2886263 : Blo 1281959 2886263 := bstep (se 1 (by rfl) ⟨2164697, by rfl⟩ : syracuseStep 2886263 = 4329395) B4329395
theorem B7301825 : Blo 1281959 7301825 := bstep (se 2 (by rfl) ⟨2738184, by rfl⟩ : syracuseStep 7301825 = 5476369) B5476369
theorem B4328207 : Blo 1281959 4328207 := bstep (se 1 (by rfl) ⟨3246155, by rfl⟩ : syracuseStep 4328207 = 6492311) B6492311
theorem B2312975 : Blo 1281959 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B2886443 : Blo 1281959 2886443 := bstep (se 1 (by rfl) ⟨2164832, by rfl⟩ : syracuseStep 2886443 = 4329665) B4329665
theorem B3124055 : Blo 1281959 3124055 := bstep (se 1 (by rfl) ⟨2343041, by rfl⟩ : syracuseStep 3124055 = 4686083) B4686083
theorem B1624951 : Blo 1281959 1624951 := bstep (se 1 (by rfl) ⟨1218713, by rfl⟩ : syracuseStep 1624951 = 2437427) B2437427
theorem B6491015 : Blo 1281959 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B9735065 : Blo 1281959 9735065 := bstep (se 2 (by rfl) ⟨3650649, by rfl⟩ : syracuseStep 9735065 = 7301299) B7301299
theorem B4328477 : Blo 1281959 4328477 := bstep (se 3 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 4328477 = 1623179) B1623179
theorem B5205035 : Blo 1281959 5205035 := bstep (se 1 (by rfl) ⟨3903776, by rfl⟩ : syracuseStep 5205035 = 7807553) B7807553
theorem B15600701 : Blo 1281959 15600701 := bstep (se 3 (by rfl) ⟨2925131, by rfl⟩ : syracuseStep 15600701 = 5850263) B5850263
theorem B2165879 : Blo 1281959 2165879 := bstep (se 1 (by rfl) ⟨1624409, by rfl⟩ : syracuseStep 2165879 = 3248819) B3248819
theorem B2886803 : Blo 1281959 2886803 := bstep (se 1 (by rfl) ⟨2165102, by rfl⟩ : syracuseStep 2886803 = 4330205) B4330205
theorem B1977529 : Blo 1281959 1977529 := bstep (se 2 (by rfl) ⟨741573, by rfl⟩ : syracuseStep 1977529 = 1483147) B1483147
theorem B2886857 : Blo 1281959 2886857 := bstep (se 2 (by rfl) ⟨1082571, by rfl⟩ : syracuseStep 2886857 = 2165143) B2165143
theorem B3083465 : Blo 1281959 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B7310573 : Blo 1281959 7310573 := bstep (se 3 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 7310573 = 2741465) B2741465
theorem B3247361 : Blo 1281959 3247361 := bstep (se 2 (by rfl) ⟨1217760, by rfl⟩ : syracuseStep 3247361 = 2435521) B2435521
theorem B8220113 : Blo 1281959 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B3468815 : Blo 1281959 3468815 := bstep (se 1 (by rfl) ⟨2601611, by rfl⟩ : syracuseStep 3468815 = 5203223) B5203223
theorem B2600507 : Blo 1281959 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B2166331 : Blo 1281959 2166331 := bstep (se 1 (by rfl) ⟨1624748, by rfl⟩ : syracuseStep 2166331 = 3249497) B3249497
theorem B3247735 : Blo 1281959 3247735 := bstep (se 1 (by rfl) ⟨2435801, by rfl⟩ : syracuseStep 3247735 = 4871603) B4871603
theorem B3903095 : Blo 1281959 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B2436743 : Blo 1281959 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B2166473 : Blo 1281959 2166473 := bstep (se 2 (by rfl) ⟨812427, by rfl⟩ : syracuseStep 2166473 = 1624855) B1624855
theorem B2887559 : Blo 1281959 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B1281979 : Blo 1281959 1281979 := bstep (se 1 (by rfl) ⟨961484, by rfl⟩ : syracuseStep 1281979 = 1922969) B1922969
theorem B10399691 : Blo 1281959 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B1282055 : Blo 1281959 1282055 := bstep (se 1 (by rfl) ⟨961541, by rfl⟩ : syracuseStep 1282055 = 1923083) B1923083
theorem B1282063 : Blo 1281959 1282063 := bstep (se 1 (by rfl) ⟨961547, by rfl⟩ : syracuseStep 1282063 = 1923095) B1923095
theorem B3248171 : Blo 1281959 3248171 := bstep (se 1 (by rfl) ⟨2436128, by rfl⟩ : syracuseStep 3248171 = 4872257) B4872257
theorem B3084331 : Blo 1281959 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B1282107 : Blo 1281959 1282107 := bstep (se 1 (by rfl) ⟨961580, by rfl⟩ : syracuseStep 1282107 = 1923161) B1923161
theorem B2887739 : Blo 1281959 2887739 := bstep (se 1 (by rfl) ⟨2165804, by rfl⟩ : syracuseStep 2887739 = 4331609) B4331609
theorem B4624451 : Blo 1281959 4624451 := bstep (se 1 (by rfl) ⟨3468338, by rfl⟩ : syracuseStep 4624451 = 6936677) B6936677
theorem B1282183 : Blo 1281959 1282183 := bstep (se 1 (by rfl) ⟨961637, by rfl⟩ : syracuseStep 1282183 = 1923275) B1923275
theorem B1282191 : Blo 1281959 1282191 := bstep (se 1 (by rfl) ⟨961643, by rfl⟩ : syracuseStep 1282191 = 1923287) B1923287
theorem B31223981 : Blo 1281959 31223981 := bstep (se 3 (by rfl) ⟨5854496, by rfl⟩ : syracuseStep 31223981 = 11708993) B11708993
theorem B2887865 : Blo 1281959 2887865 := bstep (se 2 (by rfl) ⟨1082949, by rfl⟩ : syracuseStep 2887865 = 2165899) B2165899
theorem B1282235 : Blo 1281959 1282235 := bstep (se 1 (by rfl) ⟨961676, by rfl⟩ : syracuseStep 1282235 = 1923353) B1923353
theorem B6336713 : Blo 1281959 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B1732871 : Blo 1281959 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B1282311 : Blo 1281959 1282311 := bstep (se 1 (by rfl) ⟨961733, by rfl⟩ : syracuseStep 1282311 = 1923467) B1923467
theorem B1282319 : Blo 1281959 1282319 := bstep (se 1 (by rfl) ⟨961739, by rfl⟩ : syracuseStep 1282319 = 1923479) B1923479
theorem B1282363 : Blo 1281959 1282363 := bstep (se 1 (by rfl) ⟨961772, by rfl⟩ : syracuseStep 1282363 = 1923545) B1923545
theorem B1282439 : Blo 1281959 1282439 := bstep (se 1 (by rfl) ⟨961829, by rfl⟩ : syracuseStep 1282439 = 1923659) B1923659
theorem B1282447 : Blo 1281959 1282447 := bstep (se 1 (by rfl) ⟨961835, by rfl⟩ : syracuseStep 1282447 = 1923671) B1923671
theorem B9744785 : Blo 1281959 9744785 := bstep (se 2 (by rfl) ⟨3654294, by rfl⟩ : syracuseStep 9744785 = 7308589) B7308589
theorem B4329881 : Blo 1281959 4329881 := bstep (se 2 (by rfl) ⟨1623705, by rfl⟩ : syracuseStep 4329881 = 3247411) B3247411
theorem B3469721 : Blo 1281959 3469721 := bstep (se 2 (by rfl) ⟨1301145, by rfl⟩ : syracuseStep 3469721 = 2602291) B2602291
theorem B1282491 : Blo 1281959 1282491 := bstep (se 1 (by rfl) ⟨961868, by rfl⟩ : syracuseStep 1282491 = 1923737) B1923737
theorem B20034013 : Blo 1281959 20034013 := bstep (se 3 (by rfl) ⟨3756377, by rfl⟩ : syracuseStep 20034013 = 7512755) B7512755
theorem B1282567 : Blo 1281959 1282567 := bstep (se 1 (by rfl) ⟨961925, by rfl⟩ : syracuseStep 1282567 = 1923851) B1923851
theorem B1282575 : Blo 1281959 1282575 := bstep (se 1 (by rfl) ⟨961931, by rfl⟩ : syracuseStep 1282575 = 1923863) B1923863
theorem B2888207 : Blo 1281959 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B2888225 : Blo 1281959 2888225 := bstep (se 2 (by rfl) ⟨1083084, by rfl⟩ : syracuseStep 2888225 = 2166169) B2166169
theorem B1282619 : Blo 1281959 1282619 := bstep (se 1 (by rfl) ⟨961964, by rfl⟩ : syracuseStep 1282619 = 1923929) B1923929
theorem B73929347 : Blo 1281959 73929347 := bstep (se 1 (by rfl) ⟨55447010, by rfl⟩ : syracuseStep 73929347 = 110894021) B110894021
theorem B1282695 : Blo 1281959 1282695 := bstep (se 1 (by rfl) ⟨962021, by rfl⟩ : syracuseStep 1282695 = 1924043) B1924043
theorem B1282703 : Blo 1281959 1282703 := bstep (se 1 (by rfl) ⟨962027, by rfl⟩ : syracuseStep 1282703 = 1924055) B1924055
theorem B1282747 : Blo 1281959 1282747 := bstep (se 1 (by rfl) ⟨962060, by rfl⟩ : syracuseStep 1282747 = 1924121) B1924121
theorem B8327909 : Blo 1281959 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B14619365 : Blo 1281959 14619365 := bstep (se 4 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 14619365 = 2741131) B2741131
theorem B1282823 : Blo 1281959 1282823 := bstep (se 1 (by rfl) ⟨962117, by rfl⟩ : syracuseStep 1282823 = 1924235) B1924235
theorem B3289871 : Blo 1281959 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B1282831 : Blo 1281959 1282831 := bstep (se 1 (by rfl) ⟨962123, by rfl⟩ : syracuseStep 1282831 = 1924247) B1924247
theorem B9737009 : Blo 1281959 9737009 := bstep (se 2 (by rfl) ⟨3651378, by rfl⟩ : syracuseStep 9737009 = 7302757) B7302757
theorem B1282875 : Blo 1281959 1282875 := bstep (se 1 (by rfl) ⟨962156, by rfl⟩ : syracuseStep 1282875 = 1924313) B1924313
theorem B3249011 : Blo 1281959 3249011 := bstep (se 1 (by rfl) ⟨2436758, by rfl⟩ : syracuseStep 3249011 = 4873517) B4873517
theorem B3167095 : Blo 1281959 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B2888567 : Blo 1281959 2888567 := bstep (se 1 (by rfl) ⟨2166425, by rfl⟩ : syracuseStep 2888567 = 4332851) B4332851
theorem B1282951 : Blo 1281959 1282951 := bstep (se 1 (by rfl) ⟨962213, by rfl⟩ : syracuseStep 1282951 = 1924427) B1924427
theorem B3249031 : Blo 1281959 3249031 := bstep (se 1 (by rfl) ⟨2436773, by rfl⟩ : syracuseStep 3249031 = 4873547) B4873547
theorem B1282959 : Blo 1281959 1282959 := bstep (se 1 (by rfl) ⟨962219, by rfl⟩ : syracuseStep 1282959 = 1924439) B1924439
theorem B8328089 : Blo 1281959 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B1283003 : Blo 1281959 1283003 := bstep (se 1 (by rfl) ⟨962252, by rfl⟩ : syracuseStep 1283003 = 1924505) B1924505
theorem B1283079 : Blo 1281959 1283079 := bstep (se 1 (by rfl) ⟨962309, by rfl⟩ : syracuseStep 1283079 = 1924619) B1924619
theorem B1283087 : Blo 1281959 1283087 := bstep (se 1 (by rfl) ⟨962315, by rfl⟩ : syracuseStep 1283087 = 1924631) B1924631
theorem B7304215 : Blo 1281959 7304215 := bstep (se 1 (by rfl) ⟨5478161, by rfl⟩ : syracuseStep 7304215 = 10956323) B10956323
theorem B2888747 : Blo 1281959 2888747 := bstep (se 1 (by rfl) ⟨2166560, by rfl⟩ : syracuseStep 2888747 = 4333121) B4333121
theorem B1283131 : Blo 1281959 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B4330583 : Blo 1281959 4330583 := bstep (se 1 (by rfl) ⟨3247937, by rfl⟩ : syracuseStep 4330583 = 6495875) B6495875
theorem B1283207 : Blo 1281959 1283207 := bstep (se 1 (by rfl) ⟨962405, by rfl⟩ : syracuseStep 1283207 = 1924811) B1924811
theorem B1283215 : Blo 1281959 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B3249305 : Blo 1281959 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B1283259 : Blo 1281959 1283259 := bstep (se 1 (by rfl) ⟨962444, by rfl⟩ : syracuseStep 1283259 = 1924889) B1924889
theorem B1283335 : Blo 1281959 1283335 := bstep (se 1 (by rfl) ⟨962501, by rfl⟩ : syracuseStep 1283335 = 1925003) B1925003
theorem B1283343 : Blo 1281959 1283343 := bstep (se 1 (by rfl) ⟨962507, by rfl⟩ : syracuseStep 1283343 = 1925015) B1925015
theorem B1283387 : Blo 1281959 1283387 := bstep (se 1 (by rfl) ⟨962540, by rfl⟩ : syracuseStep 1283387 = 1925081) B1925081
theorem B3249467 : Blo 1281959 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B1283463 : Blo 1281959 1283463 := bstep (se 1 (by rfl) ⟨962597, by rfl⟩ : syracuseStep 1283463 = 1925195) B1925195
theorem B1283471 : Blo 1281959 1283471 := bstep (se 1 (by rfl) ⟨962603, by rfl⟩ : syracuseStep 1283471 = 1925207) B1925207
theorem B3650969 : Blo 1281959 3650969 := bstep (se 2 (by rfl) ⟨1369113, by rfl⟩ : syracuseStep 3650969 = 2738227) B2738227
theorem B1283515 : Blo 1281959 1283515 := bstep (se 1 (by rfl) ⟨962636, by rfl⟩ : syracuseStep 1283515 = 1925273) B1925273
theorem B6936067 : Blo 1281959 6936067 := bstep (se 1 (by rfl) ⟨5202050, by rfl⟩ : syracuseStep 6936067 = 10404101) B10404101
theorem B1283591 : Blo 1281959 1283591 := bstep (se 1 (by rfl) ⟨962693, by rfl⟩ : syracuseStep 1283591 = 1925387) B1925387
theorem B1283599 : Blo 1281959 1283599 := bstep (se 1 (by rfl) ⟨962699, by rfl⟩ : syracuseStep 1283599 = 1925399) B1925399
theorem B3249679 : Blo 1281959 3249679 := bstep (se 1 (by rfl) ⟨2437259, by rfl⟩ : syracuseStep 3249679 = 4874519) B4874519
theorem B1283643 : Blo 1281959 1283643 := bstep (se 1 (by rfl) ⟨962732, by rfl⟩ : syracuseStep 1283643 = 1925465) B1925465
theorem B4388413 : Blo 1281959 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B4331069 : Blo 1281959 4331069 := bstep (se 3 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 4331069 = 1624151) B1624151
theorem B1283719 : Blo 1281959 1283719 := bstep (se 1 (by rfl) ⟨962789, by rfl⟩ : syracuseStep 1283719 = 1925579) B1925579
theorem B1283727 : Blo 1281959 1283727 := bstep (se 1 (by rfl) ⟨962795, by rfl⟩ : syracuseStep 1283727 = 1925591) B1925591
theorem B1283771 : Blo 1281959 1283771 := bstep (se 1 (by rfl) ⟨962828, by rfl⟩ : syracuseStep 1283771 = 1925657) B1925657
theorem B1283847 : Blo 1281959 1283847 := bstep (se 1 (by rfl) ⟨962885, by rfl⟩ : syracuseStep 1283847 = 1925771) B1925771
theorem B8779535 : Blo 1281959 8779535 := bstep (se 1 (by rfl) ⟨6584651, by rfl⟩ : syracuseStep 8779535 = 13169303) B13169303
theorem B1283855 : Blo 1281959 1283855 := bstep (se 1 (by rfl) ⟨962891, by rfl⟩ : syracuseStep 1283855 = 1925783) B1925783
theorem B3249953 : Blo 1281959 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B1283899 : Blo 1281959 1283899 := bstep (se 1 (by rfl) ⟨962924, by rfl⟩ : syracuseStep 1283899 = 1925849) B1925849
theorem B1922951 : Blo 1281959 1922951 := bstep (se 1 (by rfl) ⟨1442213, by rfl⟩ : syracuseStep 1922951 = 2884427) B2884427
theorem B4872089 : Blo 1281959 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B1922987 : Blo 1281959 1922987 := bstep (se 1 (by rfl) ⟨1442240, by rfl⟩ : syracuseStep 1922987 = 2884481) B2884481
theorem B1923017 : Blo 1281959 1923017 := bstep (se 2 (by rfl) ⟨721131, by rfl⟩ : syracuseStep 1923017 = 1442263) B1442263
theorem B6936587 : Blo 1281959 6936587 := bstep (se 1 (by rfl) ⟨5202440, by rfl⟩ : syracuseStep 6936587 = 10404881) B10404881
theorem B4110365 : Blo 1281959 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B1923131 : Blo 1281959 1923131 := bstep (se 1 (by rfl) ⟨1442348, by rfl⟩ : syracuseStep 1923131 = 2884697) B2884697
theorem B1923191 : Blo 1281959 1923191 := bstep (se 1 (by rfl) ⟨1442393, by rfl⟩ : syracuseStep 1923191 = 2884787) B2884787
theorem B1923215 : Blo 1281959 1923215 := bstep (se 1 (by rfl) ⟨1442411, by rfl⟩ : syracuseStep 1923215 = 2884823) B2884823
theorem B1923257 : Blo 1281959 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B1923335 : Blo 1281959 1923335 := bstep (se 1 (by rfl) ⟨1442501, by rfl⟩ : syracuseStep 1923335 = 2885003) B2885003
theorem B13162769 : Blo 1281959 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B6166817 : Blo 1281959 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B1923371 : Blo 1281959 1923371 := bstep (se 1 (by rfl) ⟨1442528, by rfl⟩ : syracuseStep 1923371 = 2885057) B2885057
theorem B2054459 : Blo 1281959 2054459 := bstep (se 1 (by rfl) ⟨1540844, by rfl⟩ : syracuseStep 2054459 = 3081689) B3081689
theorem B1923401 : Blo 1281959 1923401 := bstep (se 2 (by rfl) ⟨721275, by rfl⟩ : syracuseStep 1923401 = 1442551) B1442551
theorem B6494579 : Blo 1281959 6494579 := bstep (se 1 (by rfl) ⟨4870934, by rfl⟩ : syracuseStep 6494579 = 9741869) B9741869
theorem B6936977 : Blo 1281959 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B1923515 : Blo 1281959 1923515 := bstep (se 1 (by rfl) ⟨1442636, by rfl⟩ : syracuseStep 1923515 = 2885273) B2885273
theorem B1923575 : Blo 1281959 1923575 := bstep (se 1 (by rfl) ⟨1442681, by rfl⟩ : syracuseStep 1923575 = 2885363) B2885363
theorem B1923599 : Blo 1281959 1923599 := bstep (se 1 (by rfl) ⟨1442699, by rfl⟩ : syracuseStep 1923599 = 2885399) B2885399
theorem B1923641 : Blo 1281959 1923641 := bstep (se 2 (by rfl) ⟨721365, by rfl⟩ : syracuseStep 1923641 = 1442731) B1442731
theorem B1923719 : Blo 1281959 1923719 := bstep (se 1 (by rfl) ⟨1442789, by rfl⟩ : syracuseStep 1923719 = 2885579) B2885579
theorem B1923755 : Blo 1281959 1923755 := bstep (se 1 (by rfl) ⟨1442816, by rfl⟩ : syracuseStep 1923755 = 2885633) B2885633
theorem B1923785 : Blo 1281959 1923785 := bstep (se 2 (by rfl) ⟨721419, by rfl⟩ : syracuseStep 1923785 = 1442839) B1442839
theorem B6937325 : Blo 1281959 6937325 := bstep (se 3 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 6937325 = 2601497) B2601497
theorem B9747215 : Blo 1281959 9747215 := bstep (se 1 (by rfl) ⟨7310411, by rfl⟩ : syracuseStep 9747215 = 14620823) B14620823
theorem B3652381 : Blo 1281959 3652381 := bstep (se 3 (by rfl) ⟨684821, by rfl⟩ : syracuseStep 3652381 = 1369643) B1369643
theorem B1923899 : Blo 1281959 1923899 := bstep (se 1 (by rfl) ⟨1442924, by rfl⟩ : syracuseStep 1923899 = 2885849) B2885849
theorem B6495065 : Blo 1281959 6495065 := bstep (se 2 (by rfl) ⟨2435649, by rfl⟩ : syracuseStep 6495065 = 4871299) B4871299
theorem B1923959 : Blo 1281959 1923959 := bstep (se 1 (by rfl) ⟨1442969, by rfl⟩ : syracuseStep 1923959 = 2885939) B2885939
theorem B6167431 : Blo 1281959 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B1923983 : Blo 1281959 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B1924025 : Blo 1281959 1924025 := bstep (se 2 (by rfl) ⟨721509, by rfl⟩ : syracuseStep 1924025 = 1443019) B1443019
theorem B4332473 : Blo 1281959 4332473 := bstep (se 2 (by rfl) ⟨1624677, by rfl⟩ : syracuseStep 4332473 = 3249355) B3249355
theorem B3652553 : Blo 1281959 3652553 := bstep (se 2 (by rfl) ⟨1369707, by rfl⟩ : syracuseStep 3652553 = 2739415) B2739415
theorem B3652609 : Blo 1281959 3652609 := bstep (se 2 (by rfl) ⟨1369728, by rfl⟩ : syracuseStep 3652609 = 2739457) B2739457
theorem B1924103 : Blo 1281959 1924103 := bstep (se 1 (by rfl) ⟨1443077, by rfl⟩ : syracuseStep 1924103 = 2886155) B2886155
theorem B1924139 : Blo 1281959 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B1825849 : Blo 1281959 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1924169 : Blo 1281959 1924169 := bstep (se 2 (by rfl) ⟨721563, by rfl⟩ : syracuseStep 1924169 = 1443127) B1443127
theorem B1924283 : Blo 1281959 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B1924343 : Blo 1281959 1924343 := bstep (se 1 (by rfl) ⟨1443257, by rfl⟩ : syracuseStep 1924343 = 2886515) B2886515
theorem B1924367 : Blo 1281959 1924367 := bstep (se 1 (by rfl) ⟨1443275, by rfl⟩ : syracuseStep 1924367 = 2886551) B2886551
theorem B1924409 : Blo 1281959 1924409 := bstep (se 2 (by rfl) ⟨721653, by rfl⟩ : syracuseStep 1924409 = 1443307) B1443307
theorem B3652951 : Blo 1281959 3652951 := bstep (se 1 (by rfl) ⟨2739713, by rfl⟩ : syracuseStep 3652951 = 5479427) B5479427
theorem B23403907 : Blo 1281959 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B7306631 : Blo 1281959 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B1924487 : Blo 1281959 1924487 := bstep (se 1 (by rfl) ⟨1443365, by rfl⟩ : syracuseStep 1924487 = 2886731) B2886731
theorem B8019353 : Blo 1281959 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B1924523 : Blo 1281959 1924523 := bstep (se 1 (by rfl) ⟨1443392, by rfl⟩ : syracuseStep 1924523 = 2886785) B2886785
theorem B1924553 : Blo 1281959 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B4333067 : Blo 1281959 4333067 := bstep (se 1 (by rfl) ⟨3249800, by rfl⟩ : syracuseStep 4333067 = 6499601) B6499601
theorem B1924667 : Blo 1281959 1924667 := bstep (se 1 (by rfl) ⟨1443500, by rfl⟩ : syracuseStep 1924667 = 2887001) B2887001
theorem B1924727 : Blo 1281959 1924727 := bstep (se 1 (by rfl) ⟨1443545, by rfl⟩ : syracuseStep 1924727 = 2887091) B2887091
theorem B4333175 : Blo 1281959 4333175 := bstep (se 1 (by rfl) ⟨3249881, by rfl⟩ : syracuseStep 4333175 = 6499763) B6499763
theorem B10968695 : Blo 1281959 10968695 := bstep (se 1 (by rfl) ⟨8226521, by rfl⟩ : syracuseStep 10968695 = 16453043) B16453043
theorem B1924751 : Blo 1281959 1924751 := bstep (se 1 (by rfl) ⟨1443563, by rfl⟩ : syracuseStep 1924751 = 2887127) B2887127
theorem B1924793 : Blo 1281959 1924793 := bstep (se 2 (by rfl) ⟨721797, by rfl⟩ : syracuseStep 1924793 = 1443595) B1443595
theorem B1924871 : Blo 1281959 1924871 := bstep (se 1 (by rfl) ⟨1443653, by rfl⟩ : syracuseStep 1924871 = 2887307) B2887307
theorem B1924907 : Blo 1281959 1924907 := bstep (se 1 (by rfl) ⟨1443680, by rfl⟩ : syracuseStep 1924907 = 2887361) B2887361
theorem B7806779 : Blo 1281959 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B1924937 : Blo 1281959 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B14606243 : Blo 1281959 14606243 := bstep (se 1 (by rfl) ⟨10954682, by rfl⟩ : syracuseStep 14606243 = 21909365) B21909365
theorem B1949627 : Blo 1281959 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B1925051 : Blo 1281959 1925051 := bstep (se 1 (by rfl) ⟨1443788, by rfl⟩ : syracuseStep 1925051 = 2887577) B2887577
theorem B1925111 : Blo 1281959 1925111 := bstep (se 1 (by rfl) ⟨1443833, by rfl⟩ : syracuseStep 1925111 = 2887667) B2887667
theorem B1925129 : Blo 1281959 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B1925159 : Blo 1281959 1925159 := bstep (se 1 (by rfl) ⟨1443869, by rfl⟩ : syracuseStep 1925159 = 2887739) B2887739
theorem B4112441 : Blo 1281959 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B20815987 : Blo 1281959 20815987 := bstep (se 1 (by rfl) ⟨15611990, by rfl⟩ : syracuseStep 20815987 = 31223981) B31223981
theorem B1925243 : Blo 1281959 1925243 := bstep (se 1 (by rfl) ⟨1443932, by rfl⟩ : syracuseStep 1925243 = 2887865) B2887865
theorem B1925369 : Blo 1281959 1925369 := bstep (se 2 (by rfl) ⟨722013, by rfl⟩ : syracuseStep 1925369 = 1444027) B1444027
theorem B6496523 : Blo 1281959 6496523 := bstep (se 1 (by rfl) ⟨4872392, by rfl⟩ : syracuseStep 6496523 = 9744785) B9744785
theorem B1925471 : Blo 1281959 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B1925483 : Blo 1281959 1925483 := bstep (se 1 (by rfl) ⟨1444112, by rfl⟩ : syracuseStep 1925483 = 2888225) B2888225
theorem B18735569 : Blo 1281959 18735569 := bstep (se 2 (by rfl) ⟨7025838, by rfl⟩ : syracuseStep 18735569 = 14051677) B14051677
theorem B1925711 : Blo 1281959 1925711 := bstep (se 1 (by rfl) ⟨1444283, by rfl⟩ : syracuseStep 1925711 = 2888567) B2888567
theorem B14811821 : Blo 1281959 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B4620989 : Blo 1281959 4620989 := bstep (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) B1732871
theorem B1925831 : Blo 1281959 1925831 := bstep (se 1 (by rfl) ⟨1444373, by rfl⟩ : syracuseStep 1925831 = 2888747) B2888747
theorem B4391639 : Blo 1281959 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B2163449 : Blo 1281959 2163449 := bstep (se 2 (by rfl) ⟨811293, by rfl⟩ : syracuseStep 2163449 = 1622587) B1622587
theorem B3244961 : Blo 1281959 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2163631 : Blo 1281959 2163631 := bstep (se 1 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 2163631 = 3245447) B3245447
theorem B2884535 : Blo 1281959 2884535 := bstep (se 1 (by rfl) ⟨2163401, by rfl⟩ : syracuseStep 2884535 = 4326803) B4326803
theorem B2433979 : Blo 1281959 2433979 := bstep (se 1 (by rfl) ⟨1825484, by rfl⟩ : syracuseStep 2433979 = 3650969) B3650969
theorem B2163719 : Blo 1281959 2163719 := bstep (se 1 (by rfl) ⟨1622789, by rfl⟩ : syracuseStep 2163719 = 3245579) B3245579
theorem B32883731 : Blo 1281959 32883731 := bstep (se 1 (by rfl) ⟨24662798, by rfl⟩ : syracuseStep 32883731 = 49325597) B49325597
theorem B5850191 : Blo 1281959 5850191 := bstep (se 1 (by rfl) ⟨4387643, by rfl⟩ : syracuseStep 5850191 = 8775287) B8775287
theorem B2164063 : Blo 1281959 2164063 := bstep (se 1 (by rfl) ⟨1623047, by rfl⟩ : syracuseStep 2164063 = 3246095) B3246095
theorem B2311519 : Blo 1281959 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B3245417 : Blo 1281959 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B2434465 : Blo 1281959 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B2164151 : Blo 1281959 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B4326857 : Blo 1281959 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B4621769 : Blo 1281959 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B2885129 : Blo 1281959 2885129 := bstep (se 2 (by rfl) ⟨1081923, by rfl⟩ : syracuseStep 2885129 = 2163847) B2163847
theorem B8775179 : Blo 1281959 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1369639 : Blo 1281959 1369639 := bstep (se 1 (by rfl) ⟨1027229, by rfl⟩ : syracuseStep 1369639 = 2054459) B2054459
theorem B1443451 : Blo 1281959 1443451 := bstep (se 1 (by rfl) ⟨1082588, by rfl⟩ : syracuseStep 1443451 = 2165177) B2165177
theorem B6497981 : Blo 1281959 6497981 := bstep (se 3 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 6497981 = 2436743) B2436743
theorem B4327127 : Blo 1281959 4327127 := bstep (se 1 (by rfl) ⟨3245345, by rfl⟩ : syracuseStep 4327127 = 6490691) B6490691
theorem B4867883 : Blo 1281959 4867883 := bstep (se 1 (by rfl) ⟨3650912, by rfl⟩ : syracuseStep 4867883 = 7301825) B7301825
theorem B31205209 : Blo 1281959 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B2885471 : Blo 1281959 2885471 := bstep (se 1 (by rfl) ⟨2164103, by rfl⟩ : syracuseStep 2885471 = 4328207) B4328207
theorem B6498143 : Blo 1281959 6498143 := bstep (se 1 (by rfl) ⟨4873607, by rfl⟩ : syracuseStep 6498143 = 9747215) B9747215
theorem B2082703 : Blo 1281959 2082703 := bstep (se 1 (by rfl) ⟨1562027, by rfl⟩ : syracuseStep 2082703 = 3124055) B3124055
theorem B4327343 : Blo 1281959 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B6490043 : Blo 1281959 6490043 := bstep (se 1 (by rfl) ⟨4867532, by rfl⟩ : syracuseStep 6490043 = 9735065) B9735065
theorem B2435035 : Blo 1281959 2435035 := bstep (se 1 (by rfl) ⟨1826276, by rfl⟩ : syracuseStep 2435035 = 3652553) B3652553
theorem B2164745 : Blo 1281959 2164745 := bstep (se 2 (by rfl) ⟨811779, by rfl⟩ : syracuseStep 2164745 = 1623559) B1623559
theorem B2885651 : Blo 1281959 2885651 := bstep (se 1 (by rfl) ⟨2164238, by rfl⟩ : syracuseStep 2885651 = 4328477) B4328477
theorem B1443919 : Blo 1281959 1443919 := bstep (se 1 (by rfl) ⟨1082939, by rfl⟩ : syracuseStep 1443919 = 2165879) B2165879
theorem B5851217 : Blo 1281959 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B2164907 : Blo 1281959 2164907 := bstep (se 1 (by rfl) ⟨1623680, by rfl⟩ : syracuseStep 2164907 = 3247361) B3247361
theorem B2312543 : Blo 1281959 2312543 := bstep (se 1 (by rfl) ⟨1734407, by rfl⟩ : syracuseStep 2312543 = 3468815) B3468815
theorem B12323177 : Blo 1281959 12323177 := bstep (se 2 (by rfl) ⟨4621191, by rfl⟩ : syracuseStep 12323177 = 9242383) B9242383
theorem B2885993 : Blo 1281959 2885993 := bstep (se 2 (by rfl) ⟨1082247, by rfl⟩ : syracuseStep 2885993 = 2164495) B2164495
theorem B1444315 : Blo 1281959 1444315 := bstep (se 1 (by rfl) ⟨1083236, by rfl⟩ : syracuseStep 1444315 = 2166473) B2166473
theorem B3246601 : Blo 1281959 3246601 := bstep (se 2 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 3246601 = 2434951) B2434951
theorem B5204519 : Blo 1281959 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B2165305 : Blo 1281959 2165305 := bstep (se 2 (by rfl) ⟨811989, by rfl⟩ : syracuseStep 2165305 = 1623979) B1623979
theorem B6933127 : Blo 1281959 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B2165447 : Blo 1281959 2165447 := bstep (se 1 (by rfl) ⟨1624085, by rfl⟩ : syracuseStep 2165447 = 3248171) B3248171
theorem B3082967 : Blo 1281959 3082967 := bstep (se 1 (by rfl) ⟨2312225, by rfl⟩ : syracuseStep 3082967 = 4624451) B4624451
theorem B13175581 : Blo 1281959 13175581 := bstep (se 3 (by rfl) ⟨2470421, by rfl⟩ : syracuseStep 13175581 = 4940843) B4940843
theorem B2165609 : Blo 1281959 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B2886587 : Blo 1281959 2886587 := bstep (se 1 (by rfl) ⟨2164940, by rfl⟩ : syracuseStep 2886587 = 4329881) B4329881
theorem B7908353 : Blo 1281959 7908353 := bstep (se 2 (by rfl) ⟨2965632, by rfl⟩ : syracuseStep 7908353 = 5931265) B5931265
theorem B2886713 : Blo 1281959 2886713 := bstep (se 2 (by rfl) ⟨1082517, by rfl⟩ : syracuseStep 2886713 = 2165035) B2165035
theorem B9874511 : Blo 1281959 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B49286231 : Blo 1281959 49286231 := bstep (se 1 (by rfl) ⟨36964673, by rfl⟩ : syracuseStep 49286231 = 73929347) B73929347
theorem B39529559 : Blo 1281959 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B6491339 : Blo 1281959 6491339 := bstep (se 1 (by rfl) ⟨4868504, by rfl⟩ : syracuseStep 6491339 = 9737009) B9737009
theorem B2166007 : Blo 1281959 2166007 := bstep (se 1 (by rfl) ⟨1624505, by rfl⟩ : syracuseStep 2166007 = 3249011) B3249011
theorem B4386059 : Blo 1281959 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B2887055 : Blo 1281959 2887055 := bstep (se 1 (by rfl) ⟨2165291, by rfl⟩ : syracuseStep 2887055 = 4330583) B4330583
theorem B2166203 : Blo 1281959 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B2166311 : Blo 1281959 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B31633019 : Blo 1281959 31633019 := bstep (se 1 (by rfl) ⟨23724764, by rfl⟩ : syracuseStep 31633019 = 47449529) B47449529
theorem B4869841 : Blo 1281959 4869841 := bstep (se 2 (by rfl) ⟨1826190, by rfl⟩ : syracuseStep 4869841 = 3652381) B3652381
theorem B2887379 : Blo 1281959 2887379 := bstep (se 1 (by rfl) ⟨2165534, by rfl⟩ : syracuseStep 2887379 = 4331069) B4331069
theorem B9252589 : Blo 1281959 9252589 := bstep (se 3 (by rfl) ⟨1734860, by rfl⟩ : syracuseStep 9252589 = 3469721) B3469721
theorem B4222793 : Blo 1281959 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B2166601 : Blo 1281959 2166601 := bstep (se 2 (by rfl) ⟨812475, by rfl⟩ : syracuseStep 2166601 = 1624951) B1624951
theorem B5853023 : Blo 1281959 5853023 := bstep (se 1 (by rfl) ⟨4389767, by rfl⟩ : syracuseStep 5853023 = 8779535) B8779535
theorem B2166635 : Blo 1281959 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B236900213 : Blo 1281959 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B7303031 : Blo 1281959 7303031 := bstep (se 1 (by rfl) ⟨5477273, by rfl⟩ : syracuseStep 7303031 = 10954547) B10954547
theorem B1281967 : Blo 1281959 1281967 := bstep (se 1 (by rfl) ⟨961475, by rfl⟩ : syracuseStep 1281967 = 1922951) B1922951
theorem B3248059 : Blo 1281959 3248059 := bstep (se 1 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 3248059 = 4872089) B4872089
theorem B1281991 : Blo 1281959 1281991 := bstep (se 1 (by rfl) ⟨961493, by rfl⟩ : syracuseStep 1281991 = 1922987) B1922987
theorem B1282011 : Blo 1281959 1282011 := bstep (se 1 (by rfl) ⟨961508, by rfl⟩ : syracuseStep 1282011 = 1923017) B1923017
theorem B4870145 : Blo 1281959 4870145 := bstep (se 2 (by rfl) ⟨1826304, by rfl⟩ : syracuseStep 4870145 = 3652609) B3652609
theorem B4624391 : Blo 1281959 4624391 := bstep (se 1 (by rfl) ⟨3468293, by rfl⟩ : syracuseStep 4624391 = 6936587) B6936587
theorem B2740243 : Blo 1281959 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1282087 : Blo 1281959 1282087 := bstep (se 1 (by rfl) ⟨961565, by rfl⟩ : syracuseStep 1282087 = 1923131) B1923131
theorem B1282127 : Blo 1281959 1282127 := bstep (se 1 (by rfl) ⟨961595, by rfl⟩ : syracuseStep 1282127 = 1923191) B1923191
theorem B2437199 : Blo 1281959 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B1282143 : Blo 1281959 1282143 := bstep (se 1 (by rfl) ⟨961607, by rfl⟩ : syracuseStep 1282143 = 1923215) B1923215
theorem B7303283 : Blo 1281959 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B1282171 : Blo 1281959 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B1282223 : Blo 1281959 1282223 := bstep (se 1 (by rfl) ⟨961667, by rfl⟩ : syracuseStep 1282223 = 1923335) B1923335
theorem B1282247 : Blo 1281959 1282247 := bstep (se 1 (by rfl) ⟨961685, by rfl⟩ : syracuseStep 1282247 = 1923371) B1923371
theorem B1282267 : Blo 1281959 1282267 := bstep (se 1 (by rfl) ⟨961700, by rfl⟩ : syracuseStep 1282267 = 1923401) B1923401
theorem B4329719 : Blo 1281959 4329719 := bstep (se 1 (by rfl) ⟨3247289, by rfl⟩ : syracuseStep 4329719 = 6494579) B6494579
theorem B4624651 : Blo 1281959 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B1282343 : Blo 1281959 1282343 := bstep (se 1 (by rfl) ⟨961757, by rfl⟩ : syracuseStep 1282343 = 1923515) B1923515
theorem B1282383 : Blo 1281959 1282383 := bstep (se 1 (by rfl) ⟨961787, by rfl⟩ : syracuseStep 1282383 = 1923575) B1923575
theorem B1282399 : Blo 1281959 1282399 := bstep (se 1 (by rfl) ⟨961799, by rfl⟩ : syracuseStep 1282399 = 1923599) B1923599
theorem B1282427 : Blo 1281959 1282427 := bstep (se 1 (by rfl) ⟨961820, by rfl⟩ : syracuseStep 1282427 = 1923641) B1923641
theorem B1282479 : Blo 1281959 1282479 := bstep (se 1 (by rfl) ⟨961859, by rfl⟩ : syracuseStep 1282479 = 1923719) B1923719
theorem B1282503 : Blo 1281959 1282503 := bstep (se 1 (by rfl) ⟨961877, by rfl⟩ : syracuseStep 1282503 = 1923755) B1923755
theorem B4870601 : Blo 1281959 4870601 := bstep (se 2 (by rfl) ⟨1826475, by rfl⟩ : syracuseStep 4870601 = 3652951) B3652951
theorem B1282523 : Blo 1281959 1282523 := bstep (se 1 (by rfl) ⟨961892, by rfl⟩ : syracuseStep 1282523 = 1923785) B1923785
theorem B4624883 : Blo 1281959 4624883 := bstep (se 1 (by rfl) ⟨3468662, by rfl⟩ : syracuseStep 4624883 = 6937325) B6937325
theorem B1282599 : Blo 1281959 1282599 := bstep (se 1 (by rfl) ⟨961949, by rfl⟩ : syracuseStep 1282599 = 1923899) B1923899
theorem B4330043 : Blo 1281959 4330043 := bstep (se 1 (by rfl) ⟨3247532, by rfl⟩ : syracuseStep 4330043 = 6495065) B6495065
theorem B1282639 : Blo 1281959 1282639 := bstep (se 1 (by rfl) ⟨961979, by rfl⟩ : syracuseStep 1282639 = 1923959) B1923959
theorem B1282655 : Blo 1281959 1282655 := bstep (se 1 (by rfl) ⟨961991, by rfl⟩ : syracuseStep 1282655 = 1923983) B1923983
theorem B1282683 : Blo 1281959 1282683 := bstep (se 1 (by rfl) ⟨962012, by rfl⟩ : syracuseStep 1282683 = 1924025) B1924025
theorem B2888315 : Blo 1281959 2888315 := bstep (se 1 (by rfl) ⟨2166236, by rfl⟩ : syracuseStep 2888315 = 4332473) B4332473
theorem B1282735 : Blo 1281959 1282735 := bstep (se 1 (by rfl) ⟨962051, by rfl⟩ : syracuseStep 1282735 = 1924103) B1924103
theorem B1282759 : Blo 1281959 1282759 := bstep (se 1 (by rfl) ⟨962069, by rfl⟩ : syracuseStep 1282759 = 1924139) B1924139
theorem B3470023 : Blo 1281959 3470023 := bstep (se 1 (by rfl) ⟨2602517, by rfl⟩ : syracuseStep 3470023 = 5205035) B5205035
theorem B10400467 : Blo 1281959 10400467 := bstep (se 1 (by rfl) ⟨7800350, by rfl⟩ : syracuseStep 10400467 = 15600701) B15600701
theorem B1282779 : Blo 1281959 1282779 := bstep (se 1 (by rfl) ⟨962084, by rfl⟩ : syracuseStep 1282779 = 1924169) B1924169
theorem B2888441 : Blo 1281959 2888441 := bstep (se 2 (by rfl) ⟨1083165, by rfl⟩ : syracuseStep 2888441 = 2166331) B2166331
theorem B1282855 : Blo 1281959 1282855 := bstep (se 1 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 1282855 = 1924283) B1924283
theorem B4330313 : Blo 1281959 4330313 := bstep (se 2 (by rfl) ⟨1623867, by rfl⟩ : syracuseStep 4330313 = 3247735) B3247735
theorem B1282895 : Blo 1281959 1282895 := bstep (se 1 (by rfl) ⟨962171, by rfl⟩ : syracuseStep 1282895 = 1924343) B1924343
theorem B1282911 : Blo 1281959 1282911 := bstep (se 1 (by rfl) ⟨962183, by rfl⟩ : syracuseStep 1282911 = 1924367) B1924367
theorem B1282939 : Blo 1281959 1282939 := bstep (se 1 (by rfl) ⟨962204, by rfl⟩ : syracuseStep 1282939 = 1924409) B1924409
theorem B4871087 : Blo 1281959 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B1282991 : Blo 1281959 1282991 := bstep (se 1 (by rfl) ⟨962243, by rfl⟩ : syracuseStep 1282991 = 1924487) B1924487
theorem B5346235 : Blo 1281959 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B1283015 : Blo 1281959 1283015 := bstep (se 1 (by rfl) ⟨962261, by rfl⟩ : syracuseStep 1283015 = 1924523) B1924523
theorem B1283035 : Blo 1281959 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B2888711 : Blo 1281959 2888711 := bstep (se 1 (by rfl) ⟨2166533, by rfl⟩ : syracuseStep 2888711 = 4333067) B4333067
theorem B1733671 : Blo 1281959 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B1283111 : Blo 1281959 1283111 := bstep (se 1 (by rfl) ⟨962333, by rfl⟩ : syracuseStep 1283111 = 1924667) B1924667
theorem B1283151 : Blo 1281959 1283151 := bstep (se 1 (by rfl) ⟨962363, by rfl⟩ : syracuseStep 1283151 = 1924727) B1924727
theorem B2602063 : Blo 1281959 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B2888783 : Blo 1281959 2888783 := bstep (se 1 (by rfl) ⟨2166587, by rfl⟩ : syracuseStep 2888783 = 4333175) B4333175
theorem B7312463 : Blo 1281959 7312463 := bstep (se 1 (by rfl) ⟨5484347, by rfl⟩ : syracuseStep 7312463 = 10968695) B10968695
theorem B1283167 : Blo 1281959 1283167 := bstep (se 1 (by rfl) ⟨962375, by rfl⟩ : syracuseStep 1283167 = 1924751) B1924751
theorem B1283195 : Blo 1281959 1283195 := bstep (se 1 (by rfl) ⟨962396, by rfl⟩ : syracuseStep 1283195 = 1924793) B1924793
theorem B5199005 : Blo 1281959 5199005 := bstep (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) B1949627
theorem B1283247 : Blo 1281959 1283247 := bstep (se 1 (by rfl) ⟨962435, by rfl⟩ : syracuseStep 1283247 = 1924871) B1924871
theorem B1283271 : Blo 1281959 1283271 := bstep (se 1 (by rfl) ⟨962453, by rfl⟩ : syracuseStep 1283271 = 1924907) B1924907
theorem B1283291 : Blo 1281959 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B9737495 : Blo 1281959 9737495 := bstep (se 1 (by rfl) ⟨7303121, by rfl⟩ : syracuseStep 9737495 = 14606243) B14606243
theorem B1283367 : Blo 1281959 1283367 := bstep (se 1 (by rfl) ⟨962525, by rfl⟩ : syracuseStep 1283367 = 1925051) B1925051
theorem B1283407 : Blo 1281959 1283407 := bstep (se 1 (by rfl) ⟨962555, by rfl⟩ : syracuseStep 1283407 = 1925111) B1925111
theorem B1283423 : Blo 1281959 1283423 := bstep (se 1 (by rfl) ⟨962567, by rfl⟩ : syracuseStep 1283423 = 1925135) B1925135
theorem B1283451 : Blo 1281959 1283451 := bstep (se 1 (by rfl) ⟨962588, by rfl⟩ : syracuseStep 1283451 = 1925177) B1925177
theorem B1283503 : Blo 1281959 1283503 := bstep (se 1 (by rfl) ⟨962627, by rfl⟩ : syracuseStep 1283503 = 1925255) B1925255
theorem B1283527 : Blo 1281959 1283527 := bstep (se 1 (by rfl) ⟨962645, by rfl⟩ : syracuseStep 1283527 = 1925291) B1925291
theorem B1283547 : Blo 1281959 1283547 := bstep (se 1 (by rfl) ⟨962660, by rfl⟩ : syracuseStep 1283547 = 1925321) B1925321
theorem B1283623 : Blo 1281959 1283623 := bstep (se 1 (by rfl) ⟨962717, by rfl⟩ : syracuseStep 1283623 = 1925435) B1925435
theorem B18044459 : Blo 1281959 18044459 := bstep (se 1 (by rfl) ⟨13533344, by rfl⟩ : syracuseStep 18044459 = 27066689) B27066689
theorem B1283663 : Blo 1281959 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B1283679 : Blo 1281959 1283679 := bstep (se 1 (by rfl) ⟨962759, by rfl⟩ : syracuseStep 1283679 = 1925519) B1925519
theorem B1283707 : Blo 1281959 1283707 := bstep (se 1 (by rfl) ⟨962780, by rfl⟩ : syracuseStep 1283707 = 1925561) B1925561
theorem B1283759 : Blo 1281959 1283759 := bstep (se 1 (by rfl) ⟨962819, by rfl⟩ : syracuseStep 1283759 = 1925639) B1925639
theorem B1283783 : Blo 1281959 1283783 := bstep (se 1 (by rfl) ⟨962837, by rfl⟩ : syracuseStep 1283783 = 1925675) B1925675
theorem B1283803 : Blo 1281959 1283803 := bstep (se 1 (by rfl) ⟨962852, by rfl⟩ : syracuseStep 1283803 = 1925705) B1925705
theorem B1283879 : Blo 1281959 1283879 := bstep (se 1 (by rfl) ⟨962909, by rfl⟩ : syracuseStep 1283879 = 1925819) B1925819
theorem B6166315 : Blo 1281959 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B7411499 : Blo 1281959 7411499 := bstep (se 1 (by rfl) ⟨5558624, by rfl⟩ : syracuseStep 7411499 = 11117249) B11117249
theorem B5551939 : Blo 1281959 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B9746243 : Blo 1281959 9746243 := bstep (se 1 (by rfl) ⟨7309682, by rfl⟩ : syracuseStep 9746243 = 14619365) B14619365
theorem B1283919 : Blo 1281959 1283919 := bstep (se 1 (by rfl) ⟨962939, by rfl⟩ : syracuseStep 1283919 = 1925879) B1925879
theorem B2193247 : Blo 1281959 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B1283935 : Blo 1281959 1283935 := bstep (se 1 (by rfl) ⟨962951, by rfl⟩ : syracuseStep 1283935 = 1925903) B1925903
theorem B8222573 : Blo 1281959 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B16897901 : Blo 1281959 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B2742191 : Blo 1281959 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B1922999 : Blo 1281959 1922999 := bstep (se 1 (by rfl) ⟨1442249, by rfl⟩ : syracuseStep 1922999 = 2884499) B2884499
theorem B4331447 : Blo 1281959 4331447 := bstep (se 1 (by rfl) ⟨3248585, by rfl⟩ : syracuseStep 4331447 = 6497171) B6497171
theorem B5552059 : Blo 1281959 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B26712017 : Blo 1281959 26712017 := bstep (se 2 (by rfl) ⟨10017006, by rfl⟩ : syracuseStep 26712017 = 20034013) B20034013
theorem B1923035 : Blo 1281959 1923035 := bstep (se 1 (by rfl) ⟨1442276, by rfl⟩ : syracuseStep 1923035 = 2884553) B2884553
theorem B4872271 : Blo 1281959 4872271 := bstep (se 1 (by rfl) ⟨3654203, by rfl⟩ : syracuseStep 4872271 = 7308407) B7308407
theorem B5200139 : Blo 1281959 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B1923503 : Blo 1281959 1923503 := bstep (se 1 (by rfl) ⟨1442627, by rfl⟩ : syracuseStep 1923503 = 2885255) B2885255
theorem B1923593 : Blo 1281959 1923593 := bstep (se 2 (by rfl) ⟨721347, by rfl⟩ : syracuseStep 1923593 = 1442695) B1442695
theorem B8223241 : Blo 1281959 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B4332041 : Blo 1281959 4332041 := bstep (se 2 (by rfl) ⟨1624515, by rfl⟩ : syracuseStep 4332041 = 3249031) B3249031
theorem B1923623 : Blo 1281959 1923623 := bstep (se 1 (by rfl) ⟨1442717, by rfl⟩ : syracuseStep 1923623 = 2885435) B2885435
theorem B4872743 : Blo 1281959 4872743 := bstep (se 1 (by rfl) ⟨3654557, by rfl⟩ : syracuseStep 4872743 = 7309115) B7309115
theorem B1923707 : Blo 1281959 1923707 := bstep (se 1 (by rfl) ⟨1442780, by rfl⟩ : syracuseStep 1923707 = 2885561) B2885561
theorem B9738953 : Blo 1281959 9738953 := bstep (se 2 (by rfl) ⟨3652107, by rfl⟩ : syracuseStep 9738953 = 7304215) B7304215
theorem B1923833 : Blo 1281959 1923833 := bstep (se 2 (by rfl) ⟨721437, by rfl⟩ : syracuseStep 1923833 = 1442875) B1442875
theorem B12327709 : Blo 1281959 12327709 := bstep (se 3 (by rfl) ⟨2311445, by rfl⟩ : syracuseStep 12327709 = 4622891) B4622891
theorem B1923935 : Blo 1281959 1923935 := bstep (se 1 (by rfl) ⟨1442951, by rfl⟩ : syracuseStep 1923935 = 2885903) B2885903
theorem B1923947 : Blo 1281959 1923947 := bstep (se 1 (by rfl) ⟨1442960, by rfl⟩ : syracuseStep 1923947 = 2885921) B2885921
theorem B4111211 : Blo 1281959 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B2636705 : Blo 1281959 2636705 := bstep (se 2 (by rfl) ⟨988764, by rfl⟩ : syracuseStep 2636705 = 1977529) B1977529
theorem B1924175 : Blo 1281959 1924175 := bstep (se 1 (by rfl) ⟨1443131, by rfl⟩ : syracuseStep 1924175 = 2886263) B2886263
theorem B1924295 : Blo 1281959 1924295 := bstep (se 1 (by rfl) ⟨1443221, by rfl⟩ : syracuseStep 1924295 = 2886443) B2886443
theorem B9248089 : Blo 1281959 9248089 := bstep (se 2 (by rfl) ⟨3468033, by rfl⟩ : syracuseStep 9248089 = 6936067) B6936067
theorem B1924457 : Blo 1281959 1924457 := bstep (se 2 (by rfl) ⟨721671, by rfl⟩ : syracuseStep 1924457 = 1443343) B1443343
theorem B4332905 : Blo 1281959 4332905 := bstep (se 2 (by rfl) ⟨1624839, by rfl⟩ : syracuseStep 4332905 = 3249679) B3249679
theorem B6167933 : Blo 1281959 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B1924535 : Blo 1281959 1924535 := bstep (se 1 (by rfl) ⟨1443401, by rfl⟩ : syracuseStep 1924535 = 2886803) B2886803
theorem B1924571 : Blo 1281959 1924571 := bstep (se 1 (by rfl) ⟨1443428, by rfl⟩ : syracuseStep 1924571 = 2886857) B2886857
theorem B4873715 : Blo 1281959 4873715 := bstep (se 1 (by rfl) ⟨3655286, by rfl⟩ : syracuseStep 4873715 = 7310573) B7310573
theorem B5480075 : Blo 1281959 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B1925039 : Blo 1281959 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B3653657 : Blo 1281959 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B6496361 : Blo 1281959 6496361 := bstep (se 2 (by rfl) ⟨2436135, by rfl⟩ : syracuseStep 6496361 = 4872271) B4872271
theorem B1925225 : Blo 1281959 1925225 := bstep (se 2 (by rfl) ⟨721959, by rfl⟩ : syracuseStep 1925225 = 1443919) B1443919
theorem B27754649 : Blo 1281959 27754649 := bstep (se 2 (by rfl) ⟨10407993, by rfl⟩ : syracuseStep 27754649 = 20815987) B20815987
theorem B13877669 : Blo 1281959 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B1925543 : Blo 1281959 1925543 := bstep (se 1 (by rfl) ⟨1444157, by rfl⟩ : syracuseStep 1925543 = 2888315) B2888315
theorem B1442299 : Blo 1281959 1442299 := bstep (se 1 (by rfl) ⟨1081724, by rfl⟩ : syracuseStep 1442299 = 2163449) B2163449
theorem B1925627 : Blo 1281959 1925627 := bstep (se 1 (by rfl) ⟨1444220, by rfl⟩ : syracuseStep 1925627 = 2888441) B2888441
theorem B2163307 : Blo 1281959 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B1925753 : Blo 1281959 1925753 := bstep (se 2 (by rfl) ⟨722157, by rfl⟩ : syracuseStep 1925753 = 1444315) B1444315
theorem B1442479 : Blo 1281959 1442479 := bstep (se 1 (by rfl) ⟨1081859, by rfl⟩ : syracuseStep 1442479 = 2163719) B2163719
theorem B1925807 : Blo 1281959 1925807 := bstep (se 1 (by rfl) ⟨1444355, by rfl⟩ : syracuseStep 1925807 = 2888711) B2888711
theorem B21922487 : Blo 1281959 21922487 := bstep (se 1 (by rfl) ⟨16441865, by rfl⟩ : syracuseStep 21922487 = 32883731) B32883731
theorem B1925855 : Blo 1281959 1925855 := bstep (se 1 (by rfl) ⟨1444391, by rfl⟩ : syracuseStep 1925855 = 2888783) B2888783
theorem B4874975 : Blo 1281959 4874975 := bstep (se 1 (by rfl) ⟨3656231, by rfl⟩ : syracuseStep 4874975 = 7312463) B7312463
theorem B3466003 : Blo 1281959 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B2163611 : Blo 1281959 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B1442767 : Blo 1281959 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B2884571 : Blo 1281959 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B3081179 : Blo 1281959 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B5850119 : Blo 1281959 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B18506789 : Blo 1281959 18506789 := bstep (se 4 (by rfl) ⟨1735011, by rfl⟩ : syracuseStep 18506789 = 3470023) B3470023
theorem B2884751 : Blo 1281959 2884751 := bstep (se 1 (by rfl) ⟨2163563, by rfl⟩ : syracuseStep 2884751 = 4327127) B4327127
theorem B3245255 : Blo 1281959 3245255 := bstep (se 1 (by rfl) ⟨2433941, by rfl⟩ : syracuseStep 3245255 = 4867883) B4867883
theorem B4940999 : Blo 1281959 4940999 := bstep (se 1 (by rfl) ⟨3705749, by rfl⟩ : syracuseStep 4940999 = 7411499) B7411499
theorem B6497495 : Blo 1281959 6497495 := bstep (se 1 (by rfl) ⟨4873121, by rfl⟩ : syracuseStep 6497495 = 9746243) B9746243
theorem B2884841 : Blo 1281959 2884841 := bstep (se 2 (by rfl) ⟨1081815, by rfl⟩ : syracuseStep 2884841 = 2163631) B2163631
theorem B3245305 : Blo 1281959 3245305 := bstep (se 2 (by rfl) ⟨1216989, by rfl⟩ : syracuseStep 3245305 = 2433979) B2433979
theorem B7128313 : Blo 1281959 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B2884895 : Blo 1281959 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B1828127 : Blo 1281959 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B4326695 : Blo 1281959 4326695 := bstep (se 1 (by rfl) ⟨3245021, by rfl⟩ : syracuseStep 4326695 = 6490043) B6490043
theorem B1443163 : Blo 1281959 1443163 := bstep (se 1 (by rfl) ⟨1082372, by rfl⟩ : syracuseStep 1443163 = 2164745) B2164745
theorem B2311561 : Blo 1281959 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B3900811 : Blo 1281959 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1443271 : Blo 1281959 1443271 := bstep (se 1 (by rfl) ⟨1082453, by rfl⟩ : syracuseStep 1443271 = 2164907) B2164907
theorem B1541695 : Blo 1281959 1541695 := bstep (se 1 (by rfl) ⟨1156271, by rfl⟩ : syracuseStep 1541695 = 2312543) B2312543
theorem B12330785 : Blo 1281959 12330785 := bstep (se 2 (by rfl) ⟨4624044, by rfl⟩ : syracuseStep 12330785 = 9248089) B9248089
theorem B2885417 : Blo 1281959 2885417 := bstep (se 2 (by rfl) ⟨1082031, by rfl⟩ : syracuseStep 2885417 = 2164063) B2164063
theorem B3082025 : Blo 1281959 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B1443631 : Blo 1281959 1443631 := bstep (se 1 (by rfl) ⟨1082723, by rfl⟩ : syracuseStep 1443631 = 2165447) B2165447
theorem B12322637 : Blo 1281959 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B3245953 : Blo 1281959 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B1443739 : Blo 1281959 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B4327559 : Blo 1281959 4327559 := bstep (se 1 (by rfl) ⟨3245669, by rfl⟩ : syracuseStep 4327559 = 6491339) B6491339
theorem B1444135 : Blo 1281959 1444135 := bstep (se 1 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 1444135 = 2166203) B2166203
theorem B1444207 : Blo 1281959 1444207 := bstep (se 1 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 1444207 = 2166311) B2166311
theorem B21088679 : Blo 1281959 21088679 := bstep (se 1 (by rfl) ⟨15816509, by rfl⟩ : syracuseStep 21088679 = 31633019) B31633019
theorem B3902015 : Blo 1281959 3902015 := bstep (se 1 (by rfl) ⟨2926511, by rfl⟩ : syracuseStep 3902015 = 5853023) B5853023
theorem B1444423 : Blo 1281959 1444423 := bstep (se 1 (by rfl) ⟨1083317, by rfl⟩ : syracuseStep 1444423 = 2166635) B2166635
theorem B4868687 : Blo 1281959 4868687 := bstep (se 1 (by rfl) ⟨3651515, by rfl⟩ : syracuseStep 4868687 = 7303031) B7303031
theorem B3246713 : Blo 1281959 3246713 := bstep (se 2 (by rfl) ⟨1217517, by rfl⟩ : syracuseStep 3246713 = 2435035) B2435035
theorem B3246763 : Blo 1281959 3246763 := bstep (se 1 (by rfl) ⟨2435072, by rfl⟩ : syracuseStep 3246763 = 4870145) B4870145
theorem B12331709 : Blo 1281959 12331709 := bstep (se 3 (by rfl) ⟨2312195, by rfl⟩ : syracuseStep 12331709 = 4624391) B4624391
theorem B1624799 : Blo 1281959 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B4868855 : Blo 1281959 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B2886479 : Blo 1281959 2886479 := bstep (se 1 (by rfl) ⟨2164859, by rfl⟩ : syracuseStep 2886479 = 4329719) B4329719
theorem B15600509 : Blo 1281959 15600509 := bstep (se 3 (by rfl) ⟨2925095, by rfl⟩ : syracuseStep 15600509 = 5850191) B5850191
theorem B3247067 : Blo 1281959 3247067 := bstep (se 1 (by rfl) ⟨2435300, by rfl⟩ : syracuseStep 3247067 = 4870601) B4870601
theorem B3083255 : Blo 1281959 3083255 := bstep (se 1 (by rfl) ⟨2312441, by rfl⟩ : syracuseStep 3083255 = 4624883) B4624883
theorem B2886695 : Blo 1281959 2886695 := bstep (se 1 (by rfl) ⟨2165021, by rfl⟩ : syracuseStep 2886695 = 4330043) B4330043
theorem B9874547 : Blo 1281959 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B2927759 : Blo 1281959 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B2886875 : Blo 1281959 2886875 := bstep (se 1 (by rfl) ⟨2165156, by rfl⟩ : syracuseStep 2886875 = 4330313) B4330313
theorem B3247391 : Blo 1281959 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B4328801 : Blo 1281959 4328801 := bstep (se 2 (by rfl) ⟨1623300, by rfl⟩ : syracuseStep 4328801 = 3246601) B3246601
theorem B10964321 : Blo 1281959 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B2887073 : Blo 1281959 2887073 := bstep (se 2 (by rfl) ⟨1082652, by rfl⟩ : syracuseStep 2887073 = 2165305) B2165305
theorem B9244169 : Blo 1281959 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B6491663 : Blo 1281959 6491663 := bstep (se 1 (by rfl) ⟨4868747, by rfl⟩ : syracuseStep 6491663 = 9737495) B9737495
theorem B12029639 : Blo 1281959 12029639 := bstep (se 1 (by rfl) ⟨9022229, by rfl⟩ : syracuseStep 12029639 = 18044459) B18044459
theorem B16436945 : Blo 1281959 16436945 := bstep (se 2 (by rfl) ⟨6163854, by rfl⟩ : syracuseStep 16436945 = 12327709) B12327709
theorem B17567441 : Blo 1281959 17567441 := bstep (se 2 (by rfl) ⟨6587790, by rfl⟩ : syracuseStep 17567441 = 13175581) B13175581
theorem B1281999 : Blo 1281959 1281999 := bstep (se 1 (by rfl) ⟨961499, by rfl⟩ : syracuseStep 1281999 = 1922999) B1922999
theorem B2887631 : Blo 1281959 2887631 := bstep (se 1 (by rfl) ⟨2165723, by rfl⟩ : syracuseStep 2887631 = 4331447) B4331447
theorem B1282023 : Blo 1281959 1282023 := bstep (se 1 (by rfl) ⟨961517, by rfl⟩ : syracuseStep 1282023 = 1923035) B1923035
theorem B1282335 : Blo 1281959 1282335 := bstep (se 1 (by rfl) ⟨961751, by rfl⟩ : syracuseStep 1282335 = 1923503) B1923503
theorem B2888009 : Blo 1281959 2888009 := bstep (se 2 (by rfl) ⟨1083003, by rfl⟩ : syracuseStep 2888009 = 2166007) B2166007
theorem B1282395 : Blo 1281959 1282395 := bstep (se 1 (by rfl) ⟨961796, by rfl⟩ : syracuseStep 1282395 = 1923593) B1923593
theorem B2888027 : Blo 1281959 2888027 := bstep (se 1 (by rfl) ⟨2166020, by rfl⟩ : syracuseStep 2888027 = 4332041) B4332041
theorem B1282415 : Blo 1281959 1282415 := bstep (se 1 (by rfl) ⟨961811, by rfl⟩ : syracuseStep 1282415 = 1923623) B1923623
theorem B3248495 : Blo 1281959 3248495 := bstep (se 1 (by rfl) ⟨2436371, by rfl⟩ : syracuseStep 3248495 = 4872743) B4872743
theorem B3469679 : Blo 1281959 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B1282471 : Blo 1281959 1282471 := bstep (se 1 (by rfl) ⟨961853, by rfl⟩ : syracuseStep 1282471 = 1923707) B1923707
theorem B6492635 : Blo 1281959 6492635 := bstep (se 1 (by rfl) ⟨4869476, by rfl⟩ : syracuseStep 6492635 = 9738953) B9738953
theorem B1282555 : Blo 1281959 1282555 := bstep (se 1 (by rfl) ⟨961916, by rfl⟩ : syracuseStep 1282555 = 1923833) B1923833
theorem B1282623 : Blo 1281959 1282623 := bstep (se 1 (by rfl) ⟨961967, by rfl⟩ : syracuseStep 1282623 = 1923935) B1923935
theorem B1282631 : Blo 1281959 1282631 := bstep (se 1 (by rfl) ⟨961973, by rfl⟩ : syracuseStep 1282631 = 1923947) B1923947
theorem B2740807 : Blo 1281959 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B1757803 : Blo 1281959 1757803 := bstep (se 1 (by rfl) ⟨1318352, by rfl⟩ : syracuseStep 1757803 = 2636705) B2636705
theorem B5272235 : Blo 1281959 5272235 := bstep (se 1 (by rfl) ⟨3954176, by rfl⟩ : syracuseStep 5272235 = 7908353) B7908353
theorem B1282783 : Blo 1281959 1282783 := bstep (se 1 (by rfl) ⟨962087, by rfl⟩ : syracuseStep 1282783 = 1924175) B1924175
theorem B6583007 : Blo 1281959 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B1282863 : Blo 1281959 1282863 := bstep (se 1 (by rfl) ⟨962147, by rfl⟩ : syracuseStep 1282863 = 1924295) B1924295
theorem B11260781 : Blo 1281959 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B1282971 : Blo 1281959 1282971 := bstep (se 1 (by rfl) ⟨962228, by rfl⟩ : syracuseStep 1282971 = 1924457) B1924457
theorem B2888603 : Blo 1281959 2888603 := bstep (se 1 (by rfl) ⟨2166452, by rfl⟩ : syracuseStep 2888603 = 4332905) B4332905
theorem B6493121 : Blo 1281959 6493121 := bstep (se 2 (by rfl) ⟨2434920, by rfl⟩ : syracuseStep 6493121 = 4869841) B4869841
theorem B21926861 : Blo 1281959 21926861 := bstep (se 3 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 21926861 = 8222573) B8222573
theorem B1283023 : Blo 1281959 1283023 := bstep (se 1 (by rfl) ⟨962267, by rfl⟩ : syracuseStep 1283023 = 1924535) B1924535
theorem B45061069 : Blo 1281959 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B1283047 : Blo 1281959 1283047 := bstep (se 1 (by rfl) ⟨962285, by rfl⟩ : syracuseStep 1283047 = 1924571) B1924571
theorem B3249143 : Blo 1281959 3249143 := bstep (se 1 (by rfl) ⟨2436857, by rfl⟩ : syracuseStep 3249143 = 4873715) B4873715
theorem B8221753 : Blo 1281959 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B7402585 : Blo 1281959 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B2888801 : Blo 1281959 2888801 := bstep (se 2 (by rfl) ⟨1083300, by rfl⟩ : syracuseStep 2888801 = 2166601) B2166601
theorem B7402745 : Blo 1281959 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B4330745 : Blo 1281959 4330745 := bstep (se 2 (by rfl) ⟨1624029, by rfl⟩ : syracuseStep 4330745 = 3248059) B3248059
theorem B1283359 : Blo 1281959 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B1283419 : Blo 1281959 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B1283439 : Blo 1281959 1283439 := bstep (se 1 (by rfl) ⟨962579, by rfl⟩ : syracuseStep 1283439 = 1925159) B1925159
theorem B2741627 : Blo 1281959 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B1283495 : Blo 1281959 1283495 := bstep (se 1 (by rfl) ⟨962621, by rfl⟩ : syracuseStep 1283495 = 1925243) B1925243
theorem B1283579 : Blo 1281959 1283579 := bstep (se 1 (by rfl) ⟨962684, by rfl⟩ : syracuseStep 1283579 = 1925369) B1925369
theorem B4331015 : Blo 1281959 4331015 := bstep (se 1 (by rfl) ⟨3248261, by rfl⟩ : syracuseStep 4331015 = 6496523) B6496523
theorem B7304741 : Blo 1281959 7304741 := bstep (se 4 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 7304741 = 1369639) B1369639
theorem B1283647 : Blo 1281959 1283647 := bstep (se 1 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 1283647 = 1925471) B1925471
theorem B1283655 : Blo 1281959 1283655 := bstep (se 1 (by rfl) ⟨962741, by rfl⟩ : syracuseStep 1283655 = 1925483) B1925483
theorem B12490379 : Blo 1281959 12490379 := bstep (se 1 (by rfl) ⟨9367784, by rfl⟩ : syracuseStep 12490379 = 18735569) B18735569
theorem B6166201 : Blo 1281959 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B1283807 : Blo 1281959 1283807 := bstep (se 1 (by rfl) ⟨962855, by rfl⟩ : syracuseStep 1283807 = 1925711) B1925711
theorem B1283887 : Blo 1281959 1283887 := bstep (se 1 (by rfl) ⟨962915, by rfl⟩ : syracuseStep 1283887 = 1925831) B1925831
theorem B1923023 : Blo 1281959 1923023 := bstep (se 1 (by rfl) ⟨1442267, by rfl⟩ : syracuseStep 1923023 = 2884535) B2884535
theorem B13867037 : Blo 1281959 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B13867289 : Blo 1281959 13867289 := bstep (se 2 (by rfl) ⟨5200233, by rfl⟩ : syracuseStep 13867289 = 10400467) B10400467
theorem B1923419 : Blo 1281959 1923419 := bstep (se 1 (by rfl) ⟨1442564, by rfl⟩ : syracuseStep 1923419 = 2885129) B2885129
theorem B4331987 : Blo 1281959 4331987 := bstep (se 1 (by rfl) ⟨3248990, by rfl⟩ : syracuseStep 4331987 = 6497981) B6497981
theorem B1923647 : Blo 1281959 1923647 := bstep (se 1 (by rfl) ⟨1442735, by rfl⟩ : syracuseStep 1923647 = 2885471) B2885471
theorem B4332095 : Blo 1281959 4332095 := bstep (se 1 (by rfl) ⟨3249071, by rfl⟩ : syracuseStep 4332095 = 6498143) B6498143
theorem B17808011 : Blo 1281959 17808011 := bstep (se 1 (by rfl) ⟨13356008, by rfl⟩ : syracuseStep 17808011 = 26712017) B26712017
theorem B1923767 : Blo 1281959 1923767 := bstep (se 1 (by rfl) ⟨1442825, by rfl⟩ : syracuseStep 1923767 = 2885651) B2885651
theorem B8215451 : Blo 1281959 8215451 := bstep (se 1 (by rfl) ⟨6161588, by rfl⟩ : syracuseStep 8215451 = 12323177) B12323177
theorem B1923995 : Blo 1281959 1923995 := bstep (se 1 (by rfl) ⟨1442996, by rfl⟩ : syracuseStep 1923995 = 2885993) B2885993
theorem B14613533 : Blo 1281959 14613533 := bstep (se 3 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 14613533 = 5480075) B5480075
theorem B2055311 : Blo 1281959 2055311 := bstep (se 1 (by rfl) ⟨1541483, by rfl⟩ : syracuseStep 2055311 = 3082967) B3082967
theorem B11697317 : Blo 1281959 11697317 := bstep (se 4 (by rfl) ⟨1096623, by rfl⟩ : syracuseStep 11697317 = 2193247) B2193247
theorem B1924391 : Blo 1281959 1924391 := bstep (se 1 (by rfl) ⟨1443293, by rfl⟩ : syracuseStep 1924391 = 2886587) B2886587
theorem B1924475 : Blo 1281959 1924475 := bstep (se 1 (by rfl) ⟨1443356, by rfl⟩ : syracuseStep 1924475 = 2886713) B2886713
theorem B32857487 : Blo 1281959 32857487 := bstep (se 1 (by rfl) ⟨24643115, by rfl⟩ : syracuseStep 32857487 = 49286231) B49286231
theorem B26353039 : Blo 1281959 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B1924601 : Blo 1281959 1924601 := bstep (se 2 (by rfl) ⟨721725, by rfl⟩ : syracuseStep 1924601 = 1443451) B1443451
theorem B2924039 : Blo 1281959 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B4111955 : Blo 1281959 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B1924703 : Blo 1281959 1924703 := bstep (se 1 (by rfl) ⟨1443527, by rfl⟩ : syracuseStep 1924703 = 2887055) B2887055
theorem B12336785 : Blo 1281959 12336785 := bstep (se 2 (by rfl) ⟨4626294, by rfl⟩ : syracuseStep 12336785 = 9252589) B9252589
theorem B41606945 : Blo 1281959 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1924919 : Blo 1281959 1924919 := bstep (se 1 (by rfl) ⟨1443689, by rfl⟩ : syracuseStep 1924919 = 2887379) B2887379
theorem B2776937 : Blo 1281959 2776937 := bstep (se 2 (by rfl) ⟨1041351, by rfl⟩ : syracuseStep 2776937 = 2082703) B2082703
theorem B157933475 : Blo 1281959 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B1925339 : Blo 1281959 1925339 := bstep (se 1 (by rfl) ⟨1444004, by rfl⟩ : syracuseStep 1925339 = 2888009) B2888009
theorem B1925351 : Blo 1281959 1925351 := bstep (se 1 (by rfl) ⟨1444013, by rfl⟩ : syracuseStep 1925351 = 2888027) B2888027
theorem B7807357 : Blo 1281959 7807357 := bstep (se 3 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 7807357 = 2927759) B2927759
theorem B1925513 : Blo 1281959 1925513 := bstep (se 2 (by rfl) ⟨722067, by rfl⟩ : syracuseStep 1925513 = 1444135) B1444135
theorem B3514823 : Blo 1281959 3514823 := bstep (se 1 (by rfl) ⟨2636117, by rfl⟩ : syracuseStep 3514823 = 5272235) B5272235
theorem B14614991 : Blo 1281959 14614991 := bstep (se 1 (by rfl) ⟨10961243, by rfl⟩ : syracuseStep 14614991 = 21922487) B21922487
theorem B1925609 : Blo 1281959 1925609 := bstep (se 2 (by rfl) ⟨722103, by rfl⟩ : syracuseStep 1925609 = 1444207) B1444207
theorem B1442407 : Blo 1281959 1442407 := bstep (se 1 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 1442407 = 2163611) B2163611
theorem B1925735 : Blo 1281959 1925735 := bstep (se 1 (by rfl) ⟨1444301, by rfl⟩ : syracuseStep 1925735 = 2888603) B2888603
theorem B3900079 : Blo 1281959 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B12337859 : Blo 1281959 12337859 := bstep (se 1 (by rfl) ⟨9253394, by rfl⟩ : syracuseStep 12337859 = 18506789) B18506789
theorem B1925867 : Blo 1281959 1925867 := bstep (se 1 (by rfl) ⟨1444400, by rfl⟩ : syracuseStep 1925867 = 2888801) B2888801
theorem B4875005 : Blo 1281959 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B3654409 : Blo 1281959 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B1925897 : Blo 1281959 1925897 := bstep (se 2 (by rfl) ⟨722211, by rfl⟩ : syracuseStep 1925897 = 1444423) B1444423
theorem B2163503 : Blo 1281959 2163503 := bstep (se 1 (by rfl) ⟨1622627, by rfl⟩ : syracuseStep 2163503 = 3245255) B3245255
theorem B3293999 : Blo 1281959 3293999 := bstep (se 1 (by rfl) ⟨2470499, by rfl⟩ : syracuseStep 3293999 = 4940999) B4940999
theorem B2884409 : Blo 1281959 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B2343737 : Blo 1281959 2343737 := bstep (se 2 (by rfl) ⟨878901, by rfl⟩ : syracuseStep 2343737 = 1757803) B1757803
theorem B2884463 : Blo 1281959 2884463 := bstep (se 1 (by rfl) ⟨2163347, by rfl⟩ : syracuseStep 2884463 = 4326695) B4326695
theorem B4621337 : Blo 1281959 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B60081425 : Blo 1281959 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B10962337 : Blo 1281959 10962337 := bstep (se 2 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 10962337 = 8221753) B8221753
theorem B2885039 : Blo 1281959 2885039 := bstep (se 1 (by rfl) ⟨2163779, by rfl⟩ : syracuseStep 2885039 = 4327559) B4327559
theorem B4327073 : Blo 1281959 4327073 := bstep (se 2 (by rfl) ⟨1622652, by rfl⟩ : syracuseStep 4327073 = 3245305) B3245305
theorem B3245791 : Blo 1281959 3245791 := bstep (se 1 (by rfl) ⟨2434343, by rfl⟩ : syracuseStep 3245791 = 4868687) B4868687
theorem B2164475 : Blo 1281959 2164475 := bstep (se 1 (by rfl) ⟨1623356, by rfl⟩ : syracuseStep 2164475 = 3246713) B3246713
theorem B11872007 : Blo 1281959 11872007 := bstep (se 1 (by rfl) ⟨8904005, by rfl⟩ : syracuseStep 11872007 = 17808011) B17808011
theorem B3245903 : Blo 1281959 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B35137385 : Blo 1281959 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B2164711 : Blo 1281959 2164711 := bstep (se 1 (by rfl) ⟨1623533, by rfl⟩ : syracuseStep 2164711 = 3247067) B3247067
theorem B9742355 : Blo 1281959 9742355 := bstep (se 1 (by rfl) ⟨7306766, by rfl⟩ : syracuseStep 9742355 = 14613533) B14613533
theorem B1370207 : Blo 1281959 1370207 := bstep (se 1 (by rfl) ⟨1027655, by rfl⟩ : syracuseStep 1370207 = 2055311) B2055311
theorem B2164927 : Blo 1281959 2164927 := bstep (se 1 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 2164927 = 3247391) B3247391
theorem B2885867 : Blo 1281959 2885867 := bstep (se 1 (by rfl) ⟨2164400, by rfl⟩ : syracuseStep 2885867 = 4328801) B4328801
theorem B7309547 : Blo 1281959 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B6162779 : Blo 1281959 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B4327775 : Blo 1281959 4327775 := bstep (se 1 (by rfl) ⟨3245831, by rfl⟩ : syracuseStep 4327775 = 6491663) B6491663
theorem B4327937 : Blo 1281959 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2435771 : Blo 1281959 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B2165663 : Blo 1281959 2165663 := bstep (se 1 (by rfl) ⟨1624247, by rfl⟩ : syracuseStep 2165663 = 3248495) B3248495
theorem B2313119 : Blo 1281959 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B4328423 : Blo 1281959 4328423 := bstep (se 1 (by rfl) ⟨3246317, by rfl⟩ : syracuseStep 4328423 = 6492635) B6492635
theorem B7507187 : Blo 1281959 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B4328747 : Blo 1281959 4328747 := bstep (se 1 (by rfl) ⟨3246560, by rfl⟩ : syracuseStep 4328747 = 6493121) B6493121
theorem B14617907 : Blo 1281959 14617907 := bstep (se 1 (by rfl) ⟨10963430, by rfl⟩ : syracuseStep 14617907 = 21926861) B21926861
theorem B2166095 : Blo 1281959 2166095 := bstep (se 1 (by rfl) ⟨1624571, by rfl⟩ : syracuseStep 2166095 = 3249143) B3249143
theorem B4935163 : Blo 1281959 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B2887163 : Blo 1281959 2887163 := bstep (se 1 (by rfl) ⟨2165372, by rfl⟩ : syracuseStep 2887163 = 4330745) B4330745
theorem B4329017 : Blo 1281959 4329017 := bstep (se 2 (by rfl) ⟨1623381, by rfl⟩ : syracuseStep 4329017 = 3246763) B3246763
theorem B7311005 : Blo 1281959 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B2887343 : Blo 1281959 2887343 := bstep (se 1 (by rfl) ⟨2165507, by rfl⟩ : syracuseStep 2887343 = 4331015) B4331015
theorem B4869827 : Blo 1281959 4869827 := bstep (se 1 (by rfl) ⟨3652370, by rfl⟩ : syracuseStep 4869827 = 7304741) B7304741
theorem B8326919 : Blo 1281959 8326919 := bstep (se 1 (by rfl) ⟨6245189, by rfl⟩ : syracuseStep 8326919 = 12490379) B12490379
theorem B37007117 : Blo 1281959 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B8220523 : Blo 1281959 8220523 := bstep (se 1 (by rfl) ⟨6165392, by rfl⟩ : syracuseStep 8220523 = 12330785) B12330785
theorem B1282015 : Blo 1281959 1282015 := bstep (se 1 (by rfl) ⟨961511, by rfl⟩ : syracuseStep 1282015 = 1923023) B1923023
theorem B9244691 : Blo 1281959 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B9244859 : Blo 1281959 9244859 := bstep (se 1 (by rfl) ⟨6933644, by rfl⟩ : syracuseStep 9244859 = 13867289) B13867289
theorem B1282279 : Blo 1281959 1282279 := bstep (se 1 (by rfl) ⟨961709, by rfl⟩ : syracuseStep 1282279 = 1923419) B1923419
theorem B2887991 : Blo 1281959 2887991 := bstep (se 1 (by rfl) ⟨2165993, by rfl⟩ : syracuseStep 2887991 = 4331987) B4331987
theorem B1282431 : Blo 1281959 1282431 := bstep (se 1 (by rfl) ⟨961823, by rfl⟩ : syracuseStep 1282431 = 1923647) B1923647
theorem B2601343 : Blo 1281959 2601343 := bstep (se 1 (by rfl) ⟨1951007, by rfl⟩ : syracuseStep 2601343 = 3902015) B3902015
theorem B2888063 : Blo 1281959 2888063 := bstep (se 1 (by rfl) ⟨2166047, by rfl⟩ : syracuseStep 2888063 = 4332095) B4332095
theorem B1282511 : Blo 1281959 1282511 := bstep (se 1 (by rfl) ⟨961883, by rfl⟩ : syracuseStep 1282511 = 1923767) B1923767
theorem B8221139 : Blo 1281959 8221139 := bstep (se 1 (by rfl) ⟨6165854, by rfl⟩ : syracuseStep 8221139 = 12331709) B12331709
theorem B10400339 : Blo 1281959 10400339 := bstep (se 1 (by rfl) ⟨7800254, by rfl⟩ : syracuseStep 10400339 = 15600509) B15600509
theorem B5476967 : Blo 1281959 5476967 := bstep (se 1 (by rfl) ⟨4107725, by rfl⟩ : syracuseStep 5476967 = 8215451) B8215451
theorem B1282663 : Blo 1281959 1282663 := bstep (se 1 (by rfl) ⟨961997, by rfl⟩ : syracuseStep 1282663 = 1923995) B1923995
theorem B6583031 : Blo 1281959 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B1282927 : Blo 1281959 1282927 := bstep (se 1 (by rfl) ⟨962195, by rfl⟩ : syracuseStep 1282927 = 1924391) B1924391
theorem B8221601 : Blo 1281959 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B1282983 : Blo 1281959 1282983 := bstep (se 1 (by rfl) ⟨962237, by rfl⟩ : syracuseStep 1282983 = 1924475) B1924475
theorem B1283067 : Blo 1281959 1283067 := bstep (se 1 (by rfl) ⟨962300, by rfl⟩ : syracuseStep 1283067 = 1924601) B1924601
theorem B2741303 : Blo 1281959 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B1283135 : Blo 1281959 1283135 := bstep (se 1 (by rfl) ⟨962351, by rfl⟩ : syracuseStep 1283135 = 1924703) B1924703
theorem B10957963 : Blo 1281959 10957963 := bstep (se 1 (by rfl) ⟨8218472, by rfl⟩ : syracuseStep 10957963 = 16436945) B16436945
theorem B11711627 : Blo 1281959 11711627 := bstep (se 1 (by rfl) ⟨8783720, by rfl⟩ : syracuseStep 11711627 = 17567441) B17567441
theorem B1283279 : Blo 1281959 1283279 := bstep (se 1 (by rfl) ⟨962459, by rfl⟩ : syracuseStep 1283279 = 1924919) B1924919
theorem B105288983 : Blo 1281959 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B4330907 : Blo 1281959 4330907 := bstep (se 1 (by rfl) ⟨3248180, by rfl⟩ : syracuseStep 4330907 = 6496361) B6496361
theorem B1283483 : Blo 1281959 1283483 := bstep (se 1 (by rfl) ⟨962612, by rfl⟩ : syracuseStep 1283483 = 1925225) B1925225
theorem B18503099 : Blo 1281959 18503099 := bstep (se 1 (by rfl) ⟨13877324, by rfl⟩ : syracuseStep 18503099 = 27754649) B27754649
theorem B1283695 : Blo 1281959 1283695 := bstep (se 1 (by rfl) ⟨962771, by rfl⟩ : syracuseStep 1283695 = 1925543) B1925543
theorem B1283751 : Blo 1281959 1283751 := bstep (se 1 (by rfl) ⟨962813, by rfl⟩ : syracuseStep 1283751 = 1925627) B1925627
theorem B1283835 : Blo 1281959 1283835 := bstep (se 1 (by rfl) ⟨962876, by rfl⟩ : syracuseStep 1283835 = 1925753) B1925753
theorem B1283871 : Blo 1281959 1283871 := bstep (se 1 (by rfl) ⟨962903, by rfl⟩ : syracuseStep 1283871 = 1925807) B1925807
theorem B4388671 : Blo 1281959 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B1283903 : Blo 1281959 1283903 := bstep (se 1 (by rfl) ⟨962927, by rfl⟩ : syracuseStep 1283903 = 1925855) B1925855
theorem B3249983 : Blo 1281959 3249983 := bstep (se 1 (by rfl) ⟨2437487, by rfl⟩ : syracuseStep 3249983 = 4874975) B4874975
theorem B1923047 : Blo 1281959 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B1923065 : Blo 1281959 1923065 := bstep (se 2 (by rfl) ⟨721149, by rfl⟩ : syracuseStep 1923065 = 1442299) B1442299
theorem B1923167 : Blo 1281959 1923167 := bstep (se 1 (by rfl) ⟨1442375, by rfl⟩ : syracuseStep 1923167 = 2884751) B2884751
theorem B4331663 : Blo 1281959 4331663 := bstep (se 1 (by rfl) ⟨3248747, by rfl⟩ : syracuseStep 4331663 = 6497495) B6497495
theorem B1923227 : Blo 1281959 1923227 := bstep (se 1 (by rfl) ⟨1442420, by rfl⟩ : syracuseStep 1923227 = 2884841) B2884841
theorem B1923263 : Blo 1281959 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B1923305 : Blo 1281959 1923305 := bstep (se 2 (by rfl) ⟨721239, by rfl⟩ : syracuseStep 1923305 = 1442479) B1442479
theorem B56236477 : Blo 1281959 56236477 := bstep (se 3 (by rfl) ⟨10544339, by rfl⟩ : syracuseStep 56236477 = 21088679) B21088679
theorem B1923611 : Blo 1281959 1923611 := bstep (se 1 (by rfl) ⟨1442708, by rfl⟩ : syracuseStep 1923611 = 2885417) B2885417
theorem B2054683 : Blo 1281959 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B8215091 : Blo 1281959 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B1923689 : Blo 1281959 1923689 := bstep (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) B1442767
theorem B38017669 : Blo 1281959 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B9870113 : Blo 1281959 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B1924217 : Blo 1281959 1924217 := bstep (se 2 (by rfl) ⟨721581, by rfl⟩ : syracuseStep 1924217 = 1443163) B1443163
theorem B5201081 : Blo 1281959 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B32079037 : Blo 1281959 32079037 := bstep (se 3 (by rfl) ⟨6014819, by rfl⟩ : syracuseStep 32079037 = 12029639) B12029639
theorem B1924319 : Blo 1281959 1924319 := bstep (se 1 (by rfl) ⟨1443239, by rfl⟩ : syracuseStep 1924319 = 2886479) B2886479
theorem B4332797 : Blo 1281959 4332797 := bstep (se 3 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 4332797 = 1624799) B1624799
theorem B1924361 : Blo 1281959 1924361 := bstep (se 2 (by rfl) ⟨721635, by rfl⟩ : syracuseStep 1924361 = 1443271) B1443271
theorem B2055503 : Blo 1281959 2055503 := bstep (se 1 (by rfl) ⟨1541627, by rfl⟩ : syracuseStep 2055503 = 3083255) B3083255
theorem B1924463 : Blo 1281959 1924463 := bstep (se 1 (by rfl) ⟨1443347, by rfl⟩ : syracuseStep 1924463 = 2886695) B2886695
theorem B12328325 : Blo 1281959 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B2055593 : Blo 1281959 2055593 := bstep (se 2 (by rfl) ⟨770847, by rfl⟩ : syracuseStep 2055593 = 1541695) B1541695
theorem B7798211 : Blo 1281959 7798211 := bstep (se 1 (by rfl) ⟨5848658, by rfl⟩ : syracuseStep 7798211 = 11697317) B11697317
theorem B1924583 : Blo 1281959 1924583 := bstep (se 1 (by rfl) ⟨1443437, by rfl⟩ : syracuseStep 1924583 = 2886875) B2886875
theorem B21904991 : Blo 1281959 21904991 := bstep (se 1 (by rfl) ⟨16428743, by rfl⟩ : syracuseStep 21904991 = 32857487) B32857487
theorem B1924715 : Blo 1281959 1924715 := bstep (se 1 (by rfl) ⟨1443536, by rfl⟩ : syracuseStep 1924715 = 2887073) B2887073
theorem B7405165 : Blo 1281959 7405165 := bstep (se 3 (by rfl) ⟨1388468, by rfl⟩ : syracuseStep 7405165 = 2776937) B2776937
theorem B1949359 : Blo 1281959 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B1924841 : Blo 1281959 1924841 := bstep (se 2 (by rfl) ⟨721815, by rfl⟩ : syracuseStep 1924841 = 1443631) B1443631
theorem B8224523 : Blo 1281959 8224523 := bstep (se 1 (by rfl) ⟨6168392, by rfl⟩ : syracuseStep 8224523 = 12336785) B12336785
theorem B27737963 : Blo 1281959 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B1924985 : Blo 1281959 1924985 := bstep (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) B1443739
theorem B8216477 : Blo 1281959 8216477 := bstep (se 3 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 8216477 = 3081179) B3081179
theorem B1925087 : Blo 1281959 1925087 := bstep (se 1 (by rfl) ⟨1443815, by rfl⟩ : syracuseStep 1925087 = 2887631) B2887631
theorem B1925327 : Blo 1281959 1925327 := bstep (se 1 (by rfl) ⟨1443995, by rfl⟩ : syracuseStep 1925327 = 2887991) B2887991
theorem B3653885 : Blo 1281959 3653885 := bstep (se 3 (by rfl) ⟨685103, by rfl⟩ : syracuseStep 3653885 = 1370207) B1370207
theorem B1925375 : Blo 1281959 1925375 := bstep (se 1 (by rfl) ⟨1444031, by rfl⟩ : syracuseStep 1925375 = 2888063) B2888063
theorem B5480759 : Blo 1281959 5480759 := bstep (se 1 (by rfl) ⟨4110569, by rfl⟩ : syracuseStep 5480759 = 8221139) B8221139
theorem B8225239 : Blo 1281959 8225239 := bstep (se 1 (by rfl) ⟨6168929, by rfl⟩ : syracuseStep 8225239 = 12337859) B12337859
theorem B1442335 : Blo 1281959 1442335 := bstep (se 1 (by rfl) ⟨1081751, by rfl⟩ : syracuseStep 1442335 = 2163503) B2163503
theorem B2195999 : Blo 1281959 2195999 := bstep (se 1 (by rfl) ⟨1646999, by rfl⟩ : syracuseStep 2195999 = 3293999) B3293999
theorem B39494213 : Blo 1281959 39494213 := bstep (se 4 (by rfl) ⟨3702582, by rfl⟩ : syracuseStep 39494213 = 7405165) B7405165
theorem B74981969 : Blo 1281959 74981969 := bstep (se 2 (by rfl) ⟨28118238, by rfl⟩ : syracuseStep 74981969 = 56236477) B56236477
theorem B5481067 : Blo 1281959 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B3080891 : Blo 1281959 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B1827535 : Blo 1281959 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B7807751 : Blo 1281959 7807751 := bstep (se 1 (by rfl) ⟨5855813, by rfl⟩ : syracuseStep 7807751 = 11711627) B11711627
theorem B5481341 : Blo 1281959 5481341 := bstep (se 3 (by rfl) ⟨1027751, by rfl⟩ : syracuseStep 5481341 = 2055503) B2055503
theorem B20800421 : Blo 1281959 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B2884715 : Blo 1281959 2884715 := bstep (se 1 (by rfl) ⟨2163536, by rfl⟩ : syracuseStep 2884715 = 4327073) B4327073
theorem B1442983 : Blo 1281959 1442983 := bstep (se 1 (by rfl) ⟨1082237, by rfl⟩ : syracuseStep 1442983 = 2164475) B2164475
theorem B7914671 : Blo 1281959 7914671 := bstep (se 1 (by rfl) ⟨5936003, by rfl⟩ : syracuseStep 7914671 = 11872007) B11872007
theorem B2163935 : Blo 1281959 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B2885183 : Blo 1281959 2885183 := bstep (se 1 (by rfl) ⟨2163887, by rfl⟩ : syracuseStep 2885183 = 4327775) B4327775
theorem B42772049 : Blo 1281959 42772049 := bstep (se 2 (by rfl) ⟨16039518, by rfl⟩ : syracuseStep 42772049 = 32079037) B32079037
theorem B23406245 : Blo 1281959 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B2885291 : Blo 1281959 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B6580075 : Blo 1281959 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B14616449 : Blo 1281959 14616449 := bstep (se 2 (by rfl) ⟨5481168, by rfl⟩ : syracuseStep 14616449 = 10962337) B10962337
theorem B1443775 : Blo 1281959 1443775 := bstep (se 1 (by rfl) ⟨1082831, by rfl⟩ : syracuseStep 1443775 = 2165663) B2165663
theorem B1542079 : Blo 1281959 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B2885615 : Blo 1281959 2885615 := bstep (se 1 (by rfl) ⟨2164211, by rfl⟩ : syracuseStep 2885615 = 4328423) B4328423
theorem B6580217 : Blo 1281959 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B3467387 : Blo 1281959 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B2885831 : Blo 1281959 2885831 := bstep (se 1 (by rfl) ⟨2164373, by rfl⟩ : syracuseStep 2885831 = 4328747) B4328747
theorem B1444063 : Blo 1281959 1444063 := bstep (se 1 (by rfl) ⟨1083047, by rfl⟩ : syracuseStep 1444063 = 2166095) B2166095
theorem B2599145 : Blo 1281959 2599145 := bstep (se 2 (by rfl) ⟨974679, by rfl⟩ : syracuseStep 2599145 = 1949359) B1949359
theorem B8218883 : Blo 1281959 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B1370395 : Blo 1281959 1370395 := bstep (se 1 (by rfl) ⟨1027796, by rfl⟩ : syracuseStep 1370395 = 2055593) B2055593
theorem B4327721 : Blo 1281959 4327721 := bstep (se 2 (by rfl) ⟨1622895, by rfl⟩ : syracuseStep 4327721 = 3245791) B3245791
theorem B2886011 : Blo 1281959 2886011 := bstep (se 1 (by rfl) ⟨2164508, by rfl⟩ : syracuseStep 2886011 = 4329017) B4329017
theorem B3246551 : Blo 1281959 3246551 := bstep (se 1 (by rfl) ⟨2434913, by rfl⟩ : syracuseStep 3246551 = 4869827) B4869827
theorem B5483015 : Blo 1281959 5483015 := bstep (se 1 (by rfl) ⟨4112261, by rfl⟩ : syracuseStep 5483015 = 8224523) B8224523
theorem B18491975 : Blo 1281959 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B2886281 : Blo 1281959 2886281 := bstep (se 2 (by rfl) ⟨1082355, by rfl⟩ : syracuseStep 2886281 = 2164711) B2164711
theorem B6163127 : Blo 1281959 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B2886569 : Blo 1281959 2886569 := bstep (se 2 (by rfl) ⟨1082463, by rfl⟩ : syracuseStep 2886569 = 2164927) B2164927
theorem B9743327 : Blo 1281959 9743327 := bstep (se 1 (by rfl) ⟨7307495, by rfl⟩ : syracuseStep 9743327 = 14614991) B14614991
theorem B24652957 : Blo 1281959 24652957 := bstep (se 3 (by rfl) ⟨4622429, by rfl⟩ : syracuseStep 24652957 = 9244859) B9244859
theorem B3468457 : Blo 1281959 3468457 := bstep (se 2 (by rfl) ⟨1300671, by rfl⟩ : syracuseStep 3468457 = 2601343) B2601343
theorem B2739577 : Blo 1281959 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B40054283 : Blo 1281959 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B70192655 : Blo 1281959 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B2887271 : Blo 1281959 2887271 := bstep (se 1 (by rfl) ⟨2165453, by rfl⟩ : syracuseStep 2887271 = 4330907) B4330907
theorem B2166655 : Blo 1281959 2166655 := bstep (se 1 (by rfl) ⟨1624991, by rfl⟩ : syracuseStep 2166655 = 3249983) B3249983
theorem B23424923 : Blo 1281959 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B1282031 : Blo 1281959 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B1282043 : Blo 1281959 1282043 := bstep (se 1 (by rfl) ⟨961532, by rfl⟩ : syracuseStep 1282043 = 1923065) B1923065
theorem B1282111 : Blo 1281959 1282111 := bstep (se 1 (by rfl) ⟨961583, by rfl⟩ : syracuseStep 1282111 = 1923167) B1923167
theorem B2887775 : Blo 1281959 2887775 := bstep (se 1 (by rfl) ⟨2165831, by rfl⟩ : syracuseStep 2887775 = 4331663) B4331663
theorem B1282151 : Blo 1281959 1282151 := bstep (se 1 (by rfl) ⟨961613, by rfl⟩ : syracuseStep 1282151 = 1923227) B1923227
theorem B1282175 : Blo 1281959 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B1282203 : Blo 1281959 1282203 := bstep (se 1 (by rfl) ⟨961652, by rfl⟩ : syracuseStep 1282203 = 1923305) B1923305
theorem B14610617 : Blo 1281959 14610617 := bstep (se 2 (by rfl) ⟨5478981, by rfl⟩ : syracuseStep 14610617 = 10957963) B10957963
theorem B27734237 : Blo 1281959 27734237 := bstep (se 3 (by rfl) ⟨5200169, by rfl⟩ : syracuseStep 27734237 = 10400339) B10400339
theorem B4108519 : Blo 1281959 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B1282407 : Blo 1281959 1282407 := bstep (se 1 (by rfl) ⟨961805, by rfl⟩ : syracuseStep 1282407 = 1923611) B1923611
theorem B5476727 : Blo 1281959 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B1282459 : Blo 1281959 1282459 := bstep (se 1 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 1282459 = 1923689) B1923689
theorem B22205117 : Blo 1281959 22205117 := bstep (se 3 (by rfl) ⟨4163459, by rfl⟩ : syracuseStep 22205117 = 8326919) B8326919
theorem B37491445 : Blo 1281959 37491445 := bstep (se 5 (by rfl) ⟨1757411, by rfl⟩ : syracuseStep 37491445 = 3514823) B3514823
theorem B1282811 : Blo 1281959 1282811 := bstep (se 1 (by rfl) ⟨962108, by rfl⟩ : syracuseStep 1282811 = 1924217) B1924217
theorem B1282879 : Blo 1281959 1282879 := bstep (se 1 (by rfl) ⟨962159, by rfl⟩ : syracuseStep 1282879 = 1924319) B1924319
theorem B2888531 : Blo 1281959 2888531 := bstep (se 1 (by rfl) ⟨2166398, by rfl⟩ : syracuseStep 2888531 = 4332797) B4332797
theorem B1282907 : Blo 1281959 1282907 := bstep (se 1 (by rfl) ⟨962180, by rfl⟩ : syracuseStep 1282907 = 1924361) B1924361
theorem B9745271 : Blo 1281959 9745271 := bstep (se 1 (by rfl) ⟨7308953, by rfl⟩ : syracuseStep 9745271 = 14617907) B14617907
theorem B1282975 : Blo 1281959 1282975 := bstep (se 1 (by rfl) ⟨962231, by rfl⟩ : syracuseStep 1282975 = 1924463) B1924463
theorem B5198807 : Blo 1281959 5198807 := bstep (se 1 (by rfl) ⟨3899105, by rfl⟩ : syracuseStep 5198807 = 7798211) B7798211
theorem B1283055 : Blo 1281959 1283055 := bstep (se 1 (by rfl) ⟨962291, by rfl⟩ : syracuseStep 1283055 = 1924583) B1924583
theorem B14603327 : Blo 1281959 14603327 := bstep (se 1 (by rfl) ⟨10952495, by rfl⟩ : syracuseStep 14603327 = 21904991) B21904991
theorem B1283143 : Blo 1281959 1283143 := bstep (se 1 (by rfl) ⟨962357, by rfl⟩ : syracuseStep 1283143 = 1924715) B1924715
theorem B1283227 : Blo 1281959 1283227 := bstep (se 1 (by rfl) ⟨962420, by rfl⟩ : syracuseStep 1283227 = 1924841) B1924841
theorem B24671411 : Blo 1281959 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B1283323 : Blo 1281959 1283323 := bstep (se 1 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 1283323 = 1924985) B1924985
theorem B5477651 : Blo 1281959 5477651 := bstep (se 1 (by rfl) ⟨4108238, by rfl⟩ : syracuseStep 5477651 = 8216477) B8216477
theorem B1283391 : Blo 1281959 1283391 := bstep (se 1 (by rfl) ⟨962543, by rfl⟩ : syracuseStep 1283391 = 1925087) B1925087
theorem B1283559 : Blo 1281959 1283559 := bstep (se 1 (by rfl) ⟨962669, by rfl⟩ : syracuseStep 1283559 = 1925339) B1925339
theorem B1283567 : Blo 1281959 1283567 := bstep (se 1 (by rfl) ⟨962675, by rfl⟩ : syracuseStep 1283567 = 1925351) B1925351
theorem B1283675 : Blo 1281959 1283675 := bstep (se 1 (by rfl) ⟨962756, by rfl⟩ : syracuseStep 1283675 = 1925513) B1925513
theorem B1283739 : Blo 1281959 1283739 := bstep (se 1 (by rfl) ⟨962804, by rfl⟩ : syracuseStep 1283739 = 1925609) B1925609
theorem B3651311 : Blo 1281959 3651311 := bstep (se 1 (by rfl) ⟨2738483, by rfl⟩ : syracuseStep 3651311 = 5476967) B5476967
theorem B1283823 : Blo 1281959 1283823 := bstep (se 1 (by rfl) ⟨962867, by rfl⟩ : syracuseStep 1283823 = 1925735) B1925735
theorem B1283911 : Blo 1281959 1283911 := bstep (se 1 (by rfl) ⟨962933, by rfl⟩ : syracuseStep 1283911 = 1925867) B1925867
theorem B4388687 : Blo 1281959 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B10409809 : Blo 1281959 10409809 := bstep (se 2 (by rfl) ⟨3903678, by rfl⟩ : syracuseStep 10409809 = 7807357) B7807357
theorem B3250003 : Blo 1281959 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B1283931 : Blo 1281959 1283931 := bstep (se 1 (by rfl) ⟨962948, by rfl⟩ : syracuseStep 1283931 = 1925897) B1925897
theorem B1922939 : Blo 1281959 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B1562491 : Blo 1281959 1562491 := bstep (se 1 (by rfl) ⟨1171868, by rfl⟩ : syracuseStep 1562491 = 2343737) B2343737
theorem B1922975 : Blo 1281959 1922975 := bstep (se 1 (by rfl) ⟨1442231, by rfl⟩ : syracuseStep 1922975 = 2884463) B2884463
theorem B1923209 : Blo 1281959 1923209 := bstep (se 2 (by rfl) ⟨721203, by rfl⟩ : syracuseStep 1923209 = 1442407) B1442407
theorem B50690225 : Blo 1281959 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B1923359 : Blo 1281959 1923359 := bstep (se 1 (by rfl) ⟨1442519, by rfl⟩ : syracuseStep 1923359 = 2885039) B2885039
theorem B12335399 : Blo 1281959 12335399 := bstep (se 1 (by rfl) ⟨9251549, by rfl⟩ : syracuseStep 12335399 = 18503099) B18503099
theorem B4872545 : Blo 1281959 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B6494903 : Blo 1281959 6494903 := bstep (se 1 (by rfl) ⟨4871177, by rfl⟩ : syracuseStep 6494903 = 9742355) B9742355
theorem B1923911 : Blo 1281959 1923911 := bstep (se 1 (by rfl) ⟨1442933, by rfl⟩ : syracuseStep 1923911 = 2885867) B2885867
theorem B4873031 : Blo 1281959 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B6495389 : Blo 1281959 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B5004791 : Blo 1281959 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B1924775 : Blo 1281959 1924775 := bstep (se 1 (by rfl) ⟨1443581, by rfl⟩ : syracuseStep 1924775 = 2887163) B2887163
theorem B4874003 : Blo 1281959 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1924895 : Blo 1281959 1924895 := bstep (se 1 (by rfl) ⟨1443671, by rfl⟩ : syracuseStep 1924895 = 2887343) B2887343
theorem B10960697 : Blo 1281959 10960697 := bstep (se 2 (by rfl) ⟨4110261, by rfl⟩ : syracuseStep 10960697 = 8220523) B8220523
theorem B1925183 : Blo 1281959 1925183 := bstep (se 1 (by rfl) ⟨1443887, by rfl⟩ : syracuseStep 1925183 = 2887775) B2887775
theorem B9740411 : Blo 1281959 9740411 := bstep (se 1 (by rfl) ⟨7305308, by rfl⟩ : syracuseStep 9740411 = 14610617) B14610617
theorem B18489491 : Blo 1281959 18489491 := bstep (se 1 (by rfl) ⟨13867118, by rfl⟩ : syracuseStep 18489491 = 27734237) B27734237
theorem B3653839 : Blo 1281959 3653839 := bstep (se 1 (by rfl) ⟨2740379, by rfl⟩ : syracuseStep 3653839 = 5480759) B5480759
theorem B1925417 : Blo 1281959 1925417 := bstep (se 2 (by rfl) ⟨722031, by rfl⟩ : syracuseStep 1925417 = 1444063) B1444063
theorem B1827193 : Blo 1281959 1827193 := bstep (se 2 (by rfl) ⟨685197, by rfl⟩ : syracuseStep 1827193 = 1370395) B1370395
theorem B26329475 : Blo 1281959 26329475 := bstep (se 1 (by rfl) ⟨19747106, by rfl⟩ : syracuseStep 26329475 = 39494213) B39494213
theorem B49987979 : Blo 1281959 49987979 := bstep (se 1 (by rfl) ⟨37490984, by rfl⟩ : syracuseStep 49987979 = 74981969) B74981969
theorem B14803411 : Blo 1281959 14803411 := bstep (se 1 (by rfl) ⟨11102558, by rfl⟩ : syracuseStep 14803411 = 22205117) B22205117
theorem B1925687 : Blo 1281959 1925687 := bstep (se 1 (by rfl) ⟨1444265, by rfl⟩ : syracuseStep 1925687 = 2888531) B2888531
theorem B6496847 : Blo 1281959 6496847 := bstep (se 1 (by rfl) ⟨4872635, by rfl⟩ : syracuseStep 6496847 = 9745271) B9745271
theorem B3654227 : Blo 1281959 3654227 := bstep (se 1 (by rfl) ⟨2740670, by rfl⟩ : syracuseStep 3654227 = 5481341) B5481341
theorem B3465871 : Blo 1281959 3465871 := bstep (se 1 (by rfl) ⟨2599403, by rfl⟩ : syracuseStep 3465871 = 5198807) B5198807
theorem B5276447 : Blo 1281959 5276447 := bstep (se 1 (by rfl) ⟨3957335, by rfl⟩ : syracuseStep 5276447 = 7914671) B7914671
theorem B7308089 : Blo 1281959 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B1442623 : Blo 1281959 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B49988593 : Blo 1281959 49988593 := bstep (se 2 (by rfl) ⟨18745722, by rfl⟩ : syracuseStep 49988593 = 37491445) B37491445
theorem B2434207 : Blo 1281959 2434207 := bstep (se 1 (by rfl) ⟨1825655, by rfl⟩ : syracuseStep 2434207 = 3651311) B3651311
theorem B2925791 : Blo 1281959 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B2311591 : Blo 1281959 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B33793483 : Blo 1281959 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B2885147 : Blo 1281959 2885147 := bstep (se 1 (by rfl) ⟨2163860, by rfl⟩ : syracuseStep 2885147 = 4327721) B4327721
theorem B2164367 : Blo 1281959 2164367 := bstep (se 1 (by rfl) ⟨1623275, by rfl⟩ : syracuseStep 2164367 = 3246551) B3246551
theorem B3655343 : Blo 1281959 3655343 := bstep (se 1 (by rfl) ⟨2741507, by rfl⟩ : syracuseStep 3655343 = 5483015) B5483015
theorem B3336527 : Blo 1281959 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B46795103 : Blo 1281959 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B62466461 : Blo 1281959 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B13879745 : Blo 1281959 13879745 := bstep (se 2 (by rfl) ⟨5204904, by rfl⟩ : syracuseStep 13879745 = 10409809) B10409809
theorem B2083321 : Blo 1281959 2083321 := bstep (se 2 (by rfl) ⟨781245, by rfl⟩ : syracuseStep 2083321 = 1562491) B1562491
theorem B2435923 : Blo 1281959 2435923 := bstep (se 1 (by rfl) ⟨1826942, by rfl⟩ : syracuseStep 2435923 = 3653885) B3653885
theorem B5205167 : Blo 1281959 5205167 := bstep (se 1 (by rfl) ⟨3903875, by rfl⟩ : syracuseStep 5205167 = 7807751) B7807751
theorem B9735551 : Blo 1281959 9735551 := bstep (se 1 (by rfl) ⟨7301663, by rfl⟩ : syracuseStep 9735551 = 14603327) B14603327
theorem B2436713 : Blo 1281959 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B1281959 : Blo 1281959 1281959 := bstep (se 1 (by rfl) ⟨961469, by rfl⟩ : syracuseStep 1281959 = 1922939) B1922939
theorem B9744299 : Blo 1281959 9744299 := bstep (se 1 (by rfl) ⟨7308224, by rfl⟩ : syracuseStep 9744299 = 14616449) B14616449
theorem B1281983 : Blo 1281959 1281983 := bstep (se 1 (by rfl) ⟨961487, by rfl⟩ : syracuseStep 1281983 = 1922975) B1922975
theorem B4386811 : Blo 1281959 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B1282139 : Blo 1281959 1282139 := bstep (se 1 (by rfl) ⟨961604, by rfl⟩ : syracuseStep 1282139 = 1923209) B1923209
theorem B1732763 : Blo 1281959 1732763 := bstep (se 1 (by rfl) ⟨1299572, by rfl⟩ : syracuseStep 1732763 = 2599145) B2599145
theorem B1282239 : Blo 1281959 1282239 := bstep (se 1 (by rfl) ⟨961679, by rfl⟩ : syracuseStep 1282239 = 1923359) B1923359
theorem B32870609 : Blo 1281959 32870609 := bstep (se 2 (by rfl) ⟨12326478, by rfl⟩ : syracuseStep 32870609 = 24652957) B24652957
theorem B4624609 : Blo 1281959 4624609 := bstep (se 2 (by rfl) ⟨1734228, by rfl⟩ : syracuseStep 4624609 = 3468457) B3468457
theorem B3248363 : Blo 1281959 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B4108751 : Blo 1281959 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B4329935 : Blo 1281959 4329935 := bstep (se 1 (by rfl) ⟨3247451, by rfl⟩ : syracuseStep 4329935 = 6494903) B6494903
theorem B1282607 : Blo 1281959 1282607 := bstep (se 1 (by rfl) ⟨961955, by rfl⟩ : syracuseStep 1282607 = 1923911) B1923911
theorem B3248687 : Blo 1281959 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B4330259 : Blo 1281959 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B26702855 : Blo 1281959 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B1283183 : Blo 1281959 1283183 := bstep (se 1 (by rfl) ⟨962387, by rfl⟩ : syracuseStep 1283183 = 1924775) B1924775
theorem B2888873 : Blo 1281959 2888873 := bstep (se 2 (by rfl) ⟨1083327, by rfl⟩ : syracuseStep 2888873 = 2166655) B2166655
theorem B3249335 : Blo 1281959 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B1283263 : Blo 1281959 1283263 := bstep (se 1 (by rfl) ⟨962447, by rfl⟩ : syracuseStep 1283263 = 1924895) B1924895
theorem B1283551 : Blo 1281959 1283551 := bstep (se 1 (by rfl) ⟨962663, by rfl⟩ : syracuseStep 1283551 = 1925327) B1925327
theorem B1283583 : Blo 1281959 1283583 := bstep (se 1 (by rfl) ⟨962687, by rfl⟩ : syracuseStep 1283583 = 1925375) B1925375
theorem B3651151 : Blo 1281959 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B5478025 : Blo 1281959 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B1463999 : Blo 1281959 1463999 := bstep (se 1 (by rfl) ⟨1097999, by rfl⟩ : syracuseStep 1463999 = 2195999) B2195999
theorem B2053927 : Blo 1281959 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B13866947 : Blo 1281959 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B10966985 : Blo 1281959 10966985 := bstep (se 2 (by rfl) ⟨4112619, by rfl⟩ : syracuseStep 10966985 = 8225239) B8225239
theorem B1923113 : Blo 1281959 1923113 := bstep (se 2 (by rfl) ⟨721167, by rfl⟩ : syracuseStep 1923113 = 1442335) B1442335
theorem B1923143 : Blo 1281959 1923143 := bstep (se 1 (by rfl) ⟨1442357, by rfl⟩ : syracuseStep 1923143 = 2884715) B2884715
theorem B16447607 : Blo 1281959 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B3651767 : Blo 1281959 3651767 := bstep (se 1 (by rfl) ⟨2738825, by rfl⟩ : syracuseStep 3651767 = 5477651) B5477651
theorem B1923455 : Blo 1281959 1923455 := bstep (se 1 (by rfl) ⟨1442591, by rfl⟩ : syracuseStep 1923455 = 2885183) B2885183
theorem B28514699 : Blo 1281959 28514699 := bstep (se 1 (by rfl) ⟨21386024, by rfl⟩ : syracuseStep 28514699 = 42772049) B42772049
theorem B15604163 : Blo 1281959 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B1923527 : Blo 1281959 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B1923743 : Blo 1281959 1923743 := bstep (se 1 (by rfl) ⟨1442807, by rfl⟩ : syracuseStep 1923743 = 2885615) B2885615
theorem B1923887 : Blo 1281959 1923887 := bstep (se 1 (by rfl) ⟨1442915, by rfl⟩ : syracuseStep 1923887 = 2885831) B2885831
theorem B5479255 : Blo 1281959 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B8223599 : Blo 1281959 8223599 := bstep (se 1 (by rfl) ⟨6167699, by rfl⟩ : syracuseStep 8223599 = 12335399) B12335399
theorem B1923977 : Blo 1281959 1923977 := bstep (se 2 (by rfl) ⟨721491, by rfl⟩ : syracuseStep 1923977 = 1442983) B1442983
theorem B1924007 : Blo 1281959 1924007 := bstep (se 1 (by rfl) ⟨1443005, by rfl⟩ : syracuseStep 1924007 = 2886011) B2886011
theorem B12327983 : Blo 1281959 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B1924187 : Blo 1281959 1924187 := bstep (se 1 (by rfl) ⟨1443140, by rfl⟩ : syracuseStep 1924187 = 2886281) B2886281
theorem B3652769 : Blo 1281959 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B1924379 : Blo 1281959 1924379 := bstep (se 1 (by rfl) ⟨1443284, by rfl⟩ : syracuseStep 1924379 = 2886569) B2886569
theorem B6495551 : Blo 1281959 6495551 := bstep (se 1 (by rfl) ⟨4871663, by rfl⟩ : syracuseStep 6495551 = 9743327) B9743327
theorem B1924847 : Blo 1281959 1924847 := bstep (se 1 (by rfl) ⟨1443635, by rfl⟩ : syracuseStep 1924847 = 2887271) B2887271
theorem B4333337 : Blo 1281959 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B8773433 : Blo 1281959 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B7307131 : Blo 1281959 7307131 := bstep (se 1 (by rfl) ⟨5480348, by rfl⟩ : syracuseStep 7307131 = 10960697) B10960697
theorem B1925033 : Blo 1281959 1925033 := bstep (se 2 (by rfl) ⟨721887, by rfl⟩ : syracuseStep 1925033 = 1443775) B1443775
theorem B2056105 : Blo 1281959 2056105 := bstep (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) B1542079
theorem B21913739 : Blo 1281959 21913739 := bstep (se 1 (by rfl) ⟨16435304, by rfl⟩ : syracuseStep 21913739 = 32870609) B32870609
theorem B33325319 : Blo 1281959 33325319 := bstep (se 1 (by rfl) ⟨24993989, by rfl⟩ : syracuseStep 33325319 = 49987979) B49987979
theorem B4620701 : Blo 1281959 4620701 := bstep (se 3 (by rfl) ⟨866381, by rfl⟩ : syracuseStep 4620701 = 1732763) B1732763
theorem B2777761 : Blo 1281959 2777761 := bstep (se 2 (by rfl) ⟨1041660, by rfl⟩ : syracuseStep 2777761 = 2083321) B2083321
theorem B17801903 : Blo 1281959 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B1925915 : Blo 1281959 1925915 := bstep (se 1 (by rfl) ⟨1444436, by rfl⟩ : syracuseStep 1925915 = 2888873) B2888873
theorem B1950527 : Blo 1281959 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B1442911 : Blo 1281959 1442911 := bstep (se 1 (by rfl) ⟨1082183, by rfl⟩ : syracuseStep 1442911 = 2164367) B2164367
theorem B66651457 : Blo 1281959 66651457 := bstep (se 2 (by rfl) ⟨24994296, by rfl⟩ : syracuseStep 66651457 = 49988593) B49988593
theorem B2434511 : Blo 1281959 2434511 := bstep (se 1 (by rfl) ⟨1825883, by rfl⟩ : syracuseStep 2434511 = 3651767) B3651767
theorem B3245609 : Blo 1281959 3245609 := bstep (se 2 (by rfl) ⟨1217103, by rfl⟩ : syracuseStep 3245609 = 2434207) B2434207
theorem B31196735 : Blo 1281959 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B3082121 : Blo 1281959 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B5482399 : Blo 1281959 5482399 := bstep (se 1 (by rfl) ⟨4111799, by rfl⟩ : syracuseStep 5482399 = 8223599) B8223599
theorem B45057977 : Blo 1281959 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B8218655 : Blo 1281959 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4868201 : Blo 1281959 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B2435179 : Blo 1281959 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B6490367 : Blo 1281959 6490367 := bstep (se 1 (by rfl) ⟨4867775, by rfl⟩ : syracuseStep 6490367 = 9735551) B9735551
theorem B2738569 : Blo 1281959 2738569 := bstep (se 2 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 2738569 = 2053927) B2053927
theorem B1624475 : Blo 1281959 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B9742841 : Blo 1281959 9742841 := bstep (se 2 (by rfl) ⟨3653565, by rfl⟩ : syracuseStep 9742841 = 7307131) B7307131
theorem B2165575 : Blo 1281959 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B2739167 : Blo 1281959 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B2886623 : Blo 1281959 2886623 := bstep (se 1 (by rfl) ⟨2164967, by rfl⟩ : syracuseStep 2886623 = 4329935) B4329935
theorem B2165791 : Blo 1281959 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B2436151 : Blo 1281959 2436151 := bstep (se 1 (by rfl) ⟨1827113, by rfl⟩ : syracuseStep 2436151 = 3654227) B3654227
theorem B2436257 : Blo 1281959 2436257 := bstep (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) B1827193
theorem B2886839 : Blo 1281959 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B3517631 : Blo 1281959 3517631 := bstep (se 1 (by rfl) ⟨2638223, by rfl⟩ : syracuseStep 3517631 = 5276447) B5276447
theorem B19737881 : Blo 1281959 19737881 := bstep (se 2 (by rfl) ⟨7401705, by rfl⟩ : syracuseStep 19737881 = 14803411) B14803411
theorem B18484645 : Blo 1281959 18484645 := bstep (se 4 (by rfl) ⟨1732935, by rfl⟩ : syracuseStep 18484645 = 3465871) B3465871
theorem B2166223 : Blo 1281959 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B3247897 : Blo 1281959 3247897 := bstep (se 2 (by rfl) ⟨1217961, by rfl⟩ : syracuseStep 3247897 = 2435923) B2435923
theorem B2436895 : Blo 1281959 2436895 := bstep (se 1 (by rfl) ⟨1827671, by rfl⟩ : syracuseStep 2436895 = 3655343) B3655343
theorem B9244631 : Blo 1281959 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B7311323 : Blo 1281959 7311323 := bstep (se 1 (by rfl) ⟨5483492, by rfl⟩ : syracuseStep 7311323 = 10966985) B10966985
theorem B1282075 : Blo 1281959 1282075 := bstep (se 1 (by rfl) ⟨961556, by rfl⟩ : syracuseStep 1282075 = 1923113) B1923113
theorem B1282095 : Blo 1281959 1282095 := bstep (se 1 (by rfl) ⟨961571, by rfl⟩ : syracuseStep 1282095 = 1923143) B1923143
theorem B10965071 : Blo 1281959 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B2224351 : Blo 1281959 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B1282303 : Blo 1281959 1282303 := bstep (se 1 (by rfl) ⟨961727, by rfl⟩ : syracuseStep 1282303 = 1923455) B1923455
theorem B19009799 : Blo 1281959 19009799 := bstep (se 1 (by rfl) ⟨14257349, by rfl⟩ : syracuseStep 19009799 = 28514699) B28514699
theorem B41644307 : Blo 1281959 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B9253163 : Blo 1281959 9253163 := bstep (se 1 (by rfl) ⟨6939872, by rfl⟩ : syracuseStep 9253163 = 13879745) B13879745
theorem B1282351 : Blo 1281959 1282351 := bstep (se 1 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 1282351 = 1923527) B1923527
theorem B1282495 : Blo 1281959 1282495 := bstep (se 1 (by rfl) ⟨961871, by rfl⟩ : syracuseStep 1282495 = 1923743) B1923743
theorem B3903997 : Blo 1281959 3903997 := bstep (se 3 (by rfl) ⟨731999, by rfl⟩ : syracuseStep 3903997 = 1463999) B1463999
theorem B1282591 : Blo 1281959 1282591 := bstep (se 1 (by rfl) ⟨961943, by rfl⟩ : syracuseStep 1282591 = 1923887) B1923887
theorem B1282651 : Blo 1281959 1282651 := bstep (se 1 (by rfl) ⟨961988, by rfl⟩ : syracuseStep 1282651 = 1923977) B1923977
theorem B1282671 : Blo 1281959 1282671 := bstep (se 1 (by rfl) ⟨962003, by rfl⟩ : syracuseStep 1282671 = 1924007) B1924007
theorem B1282791 : Blo 1281959 1282791 := bstep (se 1 (by rfl) ⟨962093, by rfl⟩ : syracuseStep 1282791 = 1924187) B1924187
theorem B3470111 : Blo 1281959 3470111 := bstep (se 1 (by rfl) ⟨2602583, by rfl⟩ : syracuseStep 3470111 = 5205167) B5205167
theorem B7304033 : Blo 1281959 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B1282919 : Blo 1281959 1282919 := bstep (se 1 (by rfl) ⟨962189, by rfl⟩ : syracuseStep 1282919 = 1924379) B1924379
theorem B4330367 : Blo 1281959 4330367 := bstep (se 1 (by rfl) ⟨3247775, by rfl⟩ : syracuseStep 4330367 = 6495551) B6495551
theorem B1283231 : Blo 1281959 1283231 := bstep (se 1 (by rfl) ⟨962423, by rfl⟩ : syracuseStep 1283231 = 1924847) B1924847
theorem B2888891 : Blo 1281959 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B2741473 : Blo 1281959 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B1283355 : Blo 1281959 1283355 := bstep (se 1 (by rfl) ⟨962516, by rfl⟩ : syracuseStep 1283355 = 1925033) B1925033
theorem B1283455 : Blo 1281959 1283455 := bstep (se 1 (by rfl) ⟨962591, by rfl⟩ : syracuseStep 1283455 = 1925183) B1925183
theorem B6493607 : Blo 1281959 6493607 := bstep (se 1 (by rfl) ⟨4870205, by rfl⟩ : syracuseStep 6493607 = 9740411) B9740411
theorem B12326327 : Blo 1281959 12326327 := bstep (se 1 (by rfl) ⟨9244745, by rfl⟩ : syracuseStep 12326327 = 18489491) B18489491
theorem B1283611 : Blo 1281959 1283611 := bstep (se 1 (by rfl) ⟨962708, by rfl⟩ : syracuseStep 1283611 = 1925417) B1925417
theorem B17552983 : Blo 1281959 17552983 := bstep (se 1 (by rfl) ⟨13164737, by rfl⟩ : syracuseStep 17552983 = 26329475) B26329475
theorem B4871785 : Blo 1281959 4871785 := bstep (se 2 (by rfl) ⟨1826919, by rfl⟩ : syracuseStep 4871785 = 3653839) B3653839
theorem B6166145 : Blo 1281959 6166145 := bstep (se 2 (by rfl) ⟨2312304, by rfl⟩ : syracuseStep 6166145 = 4624609) B4624609
theorem B1283791 : Blo 1281959 1283791 := bstep (se 1 (by rfl) ⟨962843, by rfl⟩ : syracuseStep 1283791 = 1925687) B1925687
theorem B4331231 : Blo 1281959 4331231 := bstep (se 1 (by rfl) ⟨3248423, by rfl⟩ : syracuseStep 4331231 = 6496847) B6496847
theorem B4872059 : Blo 1281959 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B1923431 : Blo 1281959 1923431 := bstep (se 1 (by rfl) ⟨1442573, by rfl⟩ : syracuseStep 1923431 = 2885147) B2885147
theorem B1923497 : Blo 1281959 1923497 := bstep (se 2 (by rfl) ⟨721311, by rfl⟩ : syracuseStep 1923497 = 1442623) B1442623
theorem B7305673 : Blo 1281959 7305673 := bstep (se 2 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 7305673 = 5479255) B5479255
theorem B10402775 : Blo 1281959 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B5848955 : Blo 1281959 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B6496199 : Blo 1281959 6496199 := bstep (se 1 (by rfl) ⟨4872149, by rfl⟩ : syracuseStep 6496199 = 9744299) B9744299
theorem B5849081 : Blo 1281959 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B22216879 : Blo 1281959 22216879 := bstep (se 1 (by rfl) ⟨16662659, by rfl⟩ : syracuseStep 22216879 = 33325319) B33325319
theorem B12673199 : Blo 1281959 12673199 := bstep (se 1 (by rfl) ⟨9504899, by rfl⟩ : syracuseStep 12673199 = 19009799) B19009799
theorem B27762871 : Blo 1281959 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B3080467 : Blo 1281959 3080467 := bstep (se 1 (by rfl) ⟨2310350, by rfl⟩ : syracuseStep 3080467 = 4620701) B4620701
theorem B2965801 : Blo 1281959 2965801 := bstep (se 2 (by rfl) ⟨1112175, by rfl⟩ : syracuseStep 2965801 = 2224351) B2224351
theorem B6496685 : Blo 1281959 6496685 := bstep (se 3 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 6496685 = 2436257) B2436257
theorem B9740897 : Blo 1281959 9740897 := bstep (se 2 (by rfl) ⟨3652836, by rfl⟩ : syracuseStep 9740897 = 7305673) B7305673
theorem B24675101 : Blo 1281959 24675101 := bstep (se 3 (by rfl) ⟨4626581, by rfl⟩ : syracuseStep 24675101 = 9253163) B9253163
theorem B1925927 : Blo 1281959 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B3703681 : Blo 1281959 3703681 := bstep (se 2 (by rfl) ⟨1388880, by rfl⟩ : syracuseStep 3703681 = 2777761) B2777761
theorem B8217551 : Blo 1281959 8217551 := bstep (se 1 (by rfl) ⟨6163163, by rfl⟩ : syracuseStep 8217551 = 12326327) B12326327
theorem B1623007 : Blo 1281959 1623007 := bstep (se 1 (by rfl) ⟨1217255, by rfl⟩ : syracuseStep 1623007 = 2434511) B2434511
theorem B2163739 : Blo 1281959 2163739 := bstep (se 1 (by rfl) ⟨1622804, by rfl⟩ : syracuseStep 2163739 = 3245609) B3245609
theorem B3245467 : Blo 1281959 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B4326911 : Blo 1281959 4326911 := bstep (se 1 (by rfl) ⟨3245183, by rfl⟩ : syracuseStep 4326911 = 6490367) B6490367
theorem B3655297 : Blo 1281959 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B88868609 : Blo 1281959 88868609 := bstep (se 2 (by rfl) ⟨33325728, by rfl⟩ : syracuseStep 88868609 = 66651457) B66651457
theorem B2345087 : Blo 1281959 2345087 := bstep (se 1 (by rfl) ⟨1758815, by rfl⟩ : syracuseStep 2345087 = 3517631) B3517631
theorem B13158587 : Blo 1281959 13158587 := bstep (se 1 (by rfl) ⟨9868940, by rfl⟩ : syracuseStep 13158587 = 19737881) B19737881
theorem B7309865 : Blo 1281959 7309865 := bstep (se 2 (by rfl) ⟨2741199, by rfl⟩ : syracuseStep 7309865 = 5482399) B5482399
theorem B6163087 : Blo 1281959 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B7310047 : Blo 1281959 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B14609159 : Blo 1281959 14609159 := bstep (se 1 (by rfl) ⟨10956869, by rfl⟩ : syracuseStep 14609159 = 21913739) B21913739
theorem B3246905 : Blo 1281959 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B2313407 : Blo 1281959 2313407 := bstep (se 1 (by rfl) ⟨1735055, by rfl⟩ : syracuseStep 2313407 = 3470111) B3470111
theorem B4869355 : Blo 1281959 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B2886911 : Blo 1281959 2886911 := bstep (se 1 (by rfl) ⟨2165183, by rfl⟩ : syracuseStep 2886911 = 4330367) B4330367
theorem B5205329 : Blo 1281959 5205329 := bstep (se 2 (by rfl) ⟨1951998, by rfl⟩ : syracuseStep 5205329 = 3903997) B3903997
theorem B4329071 : Blo 1281959 4329071 := bstep (se 1 (by rfl) ⟨3246803, by rfl⟩ : syracuseStep 4329071 = 6493607) B6493607
theorem B2887433 : Blo 1281959 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B2887487 : Blo 1281959 2887487 := bstep (se 1 (by rfl) ⟨2165615, by rfl⟩ : syracuseStep 2887487 = 4331231) B4331231
theorem B3248039 : Blo 1281959 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B2887721 : Blo 1281959 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B3248201 : Blo 1281959 3248201 := bstep (se 2 (by rfl) ⟨1218075, by rfl⟩ : syracuseStep 3248201 = 2436151) B2436151
theorem B1282287 : Blo 1281959 1282287 := bstep (se 1 (by rfl) ⟨961715, by rfl⟩ : syracuseStep 1282287 = 1923431) B1923431
theorem B1282331 : Blo 1281959 1282331 := bstep (se 1 (by rfl) ⟨961748, by rfl⟩ : syracuseStep 1282331 = 1923497) B1923497
theorem B24646193 : Blo 1281959 24646193 := bstep (se 2 (by rfl) ⟨9242322, by rfl⟩ : syracuseStep 24646193 = 18484645) B18484645
theorem B2888297 : Blo 1281959 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B6935183 : Blo 1281959 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B4330529 : Blo 1281959 4330529 := bstep (se 2 (by rfl) ⟨1623948, by rfl⟩ : syracuseStep 4330529 = 3247897) B3247897
theorem B3249193 : Blo 1281959 3249193 := bstep (se 2 (by rfl) ⟨1218447, by rfl⟩ : syracuseStep 3249193 = 2436895) B2436895
theorem B4330799 : Blo 1281959 4330799 := bstep (se 1 (by rfl) ⟨3248099, by rfl⟩ : syracuseStep 4330799 = 6496199) B6496199
theorem B3651425 : Blo 1281959 3651425 := bstep (se 2 (by rfl) ⟨1369284, by rfl⟩ : syracuseStep 3651425 = 2738569) B2738569
theorem B1283943 : Blo 1281959 1283943 := bstep (se 1 (by rfl) ⟨962957, by rfl⟩ : syracuseStep 1283943 = 1925915) B1925915
theorem B20797823 : Blo 1281959 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B4331933 : Blo 1281959 4331933 := bstep (se 3 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 4331933 = 1624475) B1624475
theorem B4110763 : Blo 1281959 4110763 := bstep (se 1 (by rfl) ⟨3083072, by rfl⟩ : syracuseStep 4110763 = 6166145) B6166145
theorem B2054747 : Blo 1281959 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B30038651 : Blo 1281959 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B5479103 : Blo 1281959 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B1923881 : Blo 1281959 1923881 := bstep (se 2 (by rfl) ⟨721455, by rfl⟩ : syracuseStep 1923881 = 1442911) B1442911
theorem B6495227 : Blo 1281959 6495227 := bstep (se 1 (by rfl) ⟨4871420, by rfl⟩ : syracuseStep 6495227 = 9742841) B9742841
theorem B47471741 : Blo 1281959 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B1826111 : Blo 1281959 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B1924415 : Blo 1281959 1924415 := bstep (se 1 (by rfl) ⟨1443311, by rfl⟩ : syracuseStep 1924415 = 2886623) B2886623
theorem B23403977 : Blo 1281959 23403977 := bstep (se 2 (by rfl) ⟨8776491, by rfl⟩ : syracuseStep 23403977 = 17552983) B17552983
theorem B1924559 : Blo 1281959 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B6495713 : Blo 1281959 6495713 := bstep (se 2 (by rfl) ⟨2435892, by rfl⟩ : syracuseStep 6495713 = 4871785) B4871785
theorem B5201405 : Blo 1281959 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B3899303 : Blo 1281959 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B4874215 : Blo 1281959 4874215 := bstep (se 1 (by rfl) ⟨3655661, by rfl⟩ : syracuseStep 4874215 = 7311323) B7311323
theorem B3899387 : Blo 1281959 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B1925147 : Blo 1281959 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B29622505 : Blo 1281959 29622505 := bstep (se 2 (by rfl) ⟨11108439, by rfl⟩ : syracuseStep 29622505 = 22216879) B22216879
theorem B1925531 : Blo 1281959 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B16450067 : Blo 1281959 16450067 := bstep (se 1 (by rfl) ⟨12337550, by rfl⟩ : syracuseStep 16450067 = 24675101) B24675101
theorem B5481017 : Blo 1281959 5481017 := bstep (se 2 (by rfl) ⟨2055381, by rfl⟩ : syracuseStep 5481017 = 4110763) B4110763
theorem B8217449 : Blo 1281959 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B2884607 : Blo 1281959 2884607 := bstep (se 1 (by rfl) ⟨2163455, by rfl⟩ : syracuseStep 2884607 = 4326911) B4326911
theorem B59245739 : Blo 1281959 59245739 := bstep (se 1 (by rfl) ⟨44434304, by rfl⟩ : syracuseStep 59245739 = 88868609) B88868609
theorem B2434283 : Blo 1281959 2434283 := bstep (se 1 (by rfl) ⟨1825712, by rfl⟩ : syracuseStep 2434283 = 3651425) B3651425
theorem B2164009 : Blo 1281959 2164009 := bstep (se 2 (by rfl) ⟨811503, by rfl⟩ : syracuseStep 2164009 = 1623007) B1623007
theorem B2884985 : Blo 1281959 2884985 := bstep (se 2 (by rfl) ⟨1081869, by rfl⟩ : syracuseStep 2884985 = 2163739) B2163739
theorem B4327289 : Blo 1281959 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B2164603 : Blo 1281959 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B31647827 : Blo 1281959 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B1542271 : Blo 1281959 1542271 := bstep (se 1 (by rfl) ⟨1156703, by rfl⟩ : syracuseStep 1542271 = 2313407) B2313407
theorem B3467603 : Blo 1281959 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B2886047 : Blo 1281959 2886047 := bstep (se 1 (by rfl) ⟨2164535, by rfl⟩ : syracuseStep 2886047 = 4329071) B4329071
theorem B2599535 : Blo 1281959 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B2165359 : Blo 1281959 2165359 := bstep (se 1 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 2165359 = 3248039) B3248039
theorem B6498953 : Blo 1281959 6498953 := bstep (se 2 (by rfl) ⟨2437107, by rfl⟩ : syracuseStep 6498953 = 4874215) B4874215
theorem B10398365 : Blo 1281959 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B2165467 : Blo 1281959 2165467 := bstep (se 1 (by rfl) ⟨1624100, by rfl⟩ : syracuseStep 2165467 = 3248201) B3248201
theorem B8448799 : Blo 1281959 8448799 := bstep (se 1 (by rfl) ⟨6336599, by rfl⟩ : syracuseStep 8448799 = 12673199) B12673199
theorem B4107289 : Blo 1281959 4107289 := bstep (se 2 (by rfl) ⟨1540233, by rfl⟩ : syracuseStep 4107289 = 3080467) B3080467
theorem B4623455 : Blo 1281959 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B2887019 : Blo 1281959 2887019 := bstep (se 1 (by rfl) ⟨2165264, by rfl⟩ : syracuseStep 2887019 = 4330529) B4330529
theorem B4869629 : Blo 1281959 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B2887199 : Blo 1281959 2887199 := bstep (se 1 (by rfl) ⟨2165399, by rfl⟩ : syracuseStep 2887199 = 4330799) B4330799
theorem B13865215 : Blo 1281959 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B2887955 : Blo 1281959 2887955 := bstep (se 1 (by rfl) ⟨2165966, by rfl⟩ : syracuseStep 2887955 = 4331933) B4331933
theorem B6492473 : Blo 1281959 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B20025767 : Blo 1281959 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B1282587 : Blo 1281959 1282587 := bstep (se 1 (by rfl) ⟨961940, by rfl⟩ : syracuseStep 1282587 = 1923881) B1923881
theorem B4330151 : Blo 1281959 4330151 := bstep (se 1 (by rfl) ⟨3247613, by rfl⟩ : syracuseStep 4330151 = 6495227) B6495227
theorem B1282943 : Blo 1281959 1282943 := bstep (se 1 (by rfl) ⟨962207, by rfl⟩ : syracuseStep 1282943 = 1924415) B1924415
theorem B3470219 : Blo 1281959 3470219 := bstep (se 1 (by rfl) ⟨2602664, by rfl⟩ : syracuseStep 3470219 = 5205329) B5205329
theorem B15602651 : Blo 1281959 15602651 := bstep (se 1 (by rfl) ⟨11701988, by rfl⟩ : syracuseStep 15602651 = 23403977) B23403977
theorem B1283039 : Blo 1281959 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B4330475 : Blo 1281959 4330475 := bstep (se 1 (by rfl) ⟨3247856, by rfl⟩ : syracuseStep 4330475 = 6495713) B6495713
theorem B37017161 : Blo 1281959 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B4331123 : Blo 1281959 4331123 := bstep (se 1 (by rfl) ⟨3248342, by rfl⟩ : syracuseStep 4331123 = 6496685) B6496685
theorem B16430795 : Blo 1281959 16430795 := bstep (se 1 (by rfl) ⟨12323096, by rfl⟩ : syracuseStep 16430795 = 24646193) B24646193
theorem B3954401 : Blo 1281959 3954401 := bstep (se 2 (by rfl) ⟨1482900, by rfl⟩ : syracuseStep 3954401 = 2965801) B2965801
theorem B6493931 : Blo 1281959 6493931 := bstep (se 1 (by rfl) ⟨4870448, by rfl⟩ : syracuseStep 6493931 = 9740897) B9740897
theorem B1283951 : Blo 1281959 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B5478367 : Blo 1281959 5478367 := bstep (se 1 (by rfl) ⟨4108775, by rfl⟩ : syracuseStep 5478367 = 8217551) B8217551
theorem B9746729 : Blo 1281959 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B4938241 : Blo 1281959 4938241 := bstep (se 2 (by rfl) ⟨1851840, by rfl⟩ : syracuseStep 4938241 = 3703681) B3703681
theorem B4332257 : Blo 1281959 4332257 := bstep (se 2 (by rfl) ⟨1624596, by rfl⟩ : syracuseStep 4332257 = 3249193) B3249193
theorem B1563391 : Blo 1281959 1563391 := bstep (se 1 (by rfl) ⟨1172543, by rfl⟩ : syracuseStep 1563391 = 2345087) B2345087
theorem B8772391 : Blo 1281959 8772391 := bstep (se 1 (by rfl) ⟨6579293, by rfl⟩ : syracuseStep 8772391 = 13158587) B13158587
theorem B5479325 : Blo 1281959 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B4873243 : Blo 1281959 4873243 := bstep (se 1 (by rfl) ⟨3654932, by rfl⟩ : syracuseStep 4873243 = 7309865) B7309865
theorem B3652735 : Blo 1281959 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B9739439 : Blo 1281959 9739439 := bstep (se 1 (by rfl) ⟨7304579, by rfl⟩ : syracuseStep 9739439 = 14609159) B14609159
theorem B1924607 : Blo 1281959 1924607 := bstep (se 1 (by rfl) ⟨1443455, by rfl⟩ : syracuseStep 1924607 = 2886911) B2886911
theorem B4873729 : Blo 1281959 4873729 := bstep (se 2 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 4873729 = 3655297) B3655297
theorem B1924955 : Blo 1281959 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B1924991 : Blo 1281959 1924991 := bstep (se 1 (by rfl) ⟨1443743, by rfl⟩ : syracuseStep 1924991 = 2887487) B2887487
theorem B2056361 : Blo 1281959 2056361 := bstep (se 2 (by rfl) ⟨771135, by rfl⟩ : syracuseStep 2056361 = 1542271) B1542271
theorem B1925303 : Blo 1281959 1925303 := bstep (se 1 (by rfl) ⟨1443977, by rfl⟩ : syracuseStep 1925303 = 2887955) B2887955
theorem B3654011 : Blo 1281959 3654011 := bstep (se 1 (by rfl) ⟨2740508, by rfl⟩ : syracuseStep 3654011 = 5481017) B5481017
theorem B1622855 : Blo 1281959 1622855 := bstep (se 1 (by rfl) ⟨1217141, by rfl⟩ : syracuseStep 1622855 = 2434283) B2434283
theorem B11265065 : Blo 1281959 11265065 := bstep (se 2 (by rfl) ⟨4224399, by rfl⟩ : syracuseStep 11265065 = 8448799) B8448799
theorem B10953863 : Blo 1281959 10953863 := bstep (se 1 (by rfl) ⟨8215397, by rfl⟩ : syracuseStep 10953863 = 16430795) B16430795
theorem B2884859 : Blo 1281959 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B6497657 : Blo 1281959 6497657 := bstep (se 2 (by rfl) ⟨2436621, by rfl⟩ : syracuseStep 6497657 = 4873243) B4873243
theorem B6497819 : Blo 1281959 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B2311735 : Blo 1281959 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B2885345 : Blo 1281959 2885345 := bstep (se 2 (by rfl) ⟨1082004, by rfl⟩ : syracuseStep 2885345 = 2164009) B2164009
theorem B6932243 : Blo 1281959 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B6498305 : Blo 1281959 6498305 := bstep (se 2 (by rfl) ⟨2436864, by rfl⟩ : syracuseStep 6498305 = 4873729) B4873729
theorem B3082303 : Blo 1281959 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B3246419 : Blo 1281959 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B2886137 : Blo 1281959 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B4328315 : Blo 1281959 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B39496673 : Blo 1281959 39496673 := bstep (se 2 (by rfl) ⟨14811252, by rfl⟩ : syracuseStep 39496673 = 29622505) B29622505
theorem B2886767 : Blo 1281959 2886767 := bstep (se 1 (by rfl) ⟨2165075, by rfl⟩ : syracuseStep 2886767 = 4330151) B4330151
theorem B2313479 : Blo 1281959 2313479 := bstep (se 1 (by rfl) ⟨1735109, by rfl⟩ : syracuseStep 2313479 = 3470219) B3470219
theorem B2886983 : Blo 1281959 2886983 := bstep (se 1 (by rfl) ⟨2165237, by rfl⟩ : syracuseStep 2886983 = 4330475) B4330475
theorem B39497159 : Blo 1281959 39497159 := bstep (se 1 (by rfl) ⟨29622869, by rfl⟩ : syracuseStep 39497159 = 59245739) B59245739
theorem B2887145 : Blo 1281959 2887145 := bstep (se 2 (by rfl) ⟨1082679, by rfl⟩ : syracuseStep 2887145 = 2165359) B2165359
theorem B2887289 : Blo 1281959 2887289 := bstep (se 2 (by rfl) ⟨1082733, by rfl⟩ : syracuseStep 2887289 = 2165467) B2165467
theorem B24678107 : Blo 1281959 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B2887415 : Blo 1281959 2887415 := bstep (se 1 (by rfl) ⟨2165561, by rfl⟩ : syracuseStep 2887415 = 4331123) B4331123
theorem B4329287 : Blo 1281959 4329287 := bstep (se 1 (by rfl) ⟨3246965, by rfl⟩ : syracuseStep 4329287 = 6493931) B6493931
theorem B5476385 : Blo 1281959 5476385 := bstep (se 2 (by rfl) ⟨2053644, by rfl⟩ : syracuseStep 5476385 = 4107289) B4107289
theorem B21098551 : Blo 1281959 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B4870313 : Blo 1281959 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B1733023 : Blo 1281959 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B2888171 : Blo 1281959 2888171 := bstep (se 1 (by rfl) ⟨2166128, by rfl⟩ : syracuseStep 2888171 = 4332257) B4332257
theorem B6492959 : Blo 1281959 6492959 := bstep (se 1 (by rfl) ⟨4869719, by rfl⟩ : syracuseStep 6492959 = 9739439) B9739439
theorem B1283071 : Blo 1281959 1283071 := bstep (se 1 (by rfl) ⟨962303, by rfl⟩ : syracuseStep 1283071 = 1924607) B1924607
theorem B1283303 : Blo 1281959 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B1283327 : Blo 1281959 1283327 := bstep (se 1 (by rfl) ⟨962495, by rfl⟩ : syracuseStep 1283327 = 1924991) B1924991
theorem B7304489 : Blo 1281959 7304489 := bstep (se 2 (by rfl) ⟨2739183, by rfl⟩ : syracuseStep 7304489 = 5478367) B5478367
theorem B1283431 : Blo 1281959 1283431 := bstep (se 1 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 1283431 = 1925147) B1925147
theorem B1283687 : Blo 1281959 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B13350511 : Blo 1281959 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B18486953 : Blo 1281959 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B10966711 : Blo 1281959 10966711 := bstep (se 1 (by rfl) ⟨8225033, by rfl⟩ : syracuseStep 10966711 = 16450067) B16450067
theorem B5478299 : Blo 1281959 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B10401767 : Blo 1281959 10401767 := bstep (se 1 (by rfl) ⟨7801325, by rfl⟩ : syracuseStep 10401767 = 15602651) B15602651
theorem B1923071 : Blo 1281959 1923071 := bstep (se 1 (by rfl) ⟨1442303, by rfl⟩ : syracuseStep 1923071 = 2884607) B2884607
theorem B6584321 : Blo 1281959 6584321 := bstep (se 2 (by rfl) ⟨2469120, by rfl⟩ : syracuseStep 6584321 = 4938241) B4938241
theorem B1923323 : Blo 1281959 1923323 := bstep (se 1 (by rfl) ⟨1442492, by rfl⟩ : syracuseStep 1923323 = 2884985) B2884985
theorem B11696521 : Blo 1281959 11696521 := bstep (se 2 (by rfl) ⟨4386195, by rfl⟩ : syracuseStep 11696521 = 8772391) B8772391
theorem B8338085 : Blo 1281959 8338085 := bstep (se 4 (by rfl) ⟨781695, by rfl⟩ : syracuseStep 8338085 = 1563391) B1563391
theorem B1924031 : Blo 1281959 1924031 := bstep (se 1 (by rfl) ⟨1443023, by rfl⟩ : syracuseStep 1924031 = 2886047) B2886047
theorem B4332635 : Blo 1281959 4332635 := bstep (se 1 (by rfl) ⟨3249476, by rfl⟩ : syracuseStep 4332635 = 6498953) B6498953
theorem B3652883 : Blo 1281959 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B1924679 : Blo 1281959 1924679 := bstep (se 1 (by rfl) ⟨1443509, by rfl⟩ : syracuseStep 1924679 = 2887019) B2887019
theorem B42180277 : Blo 1281959 42180277 := bstep (se 5 (by rfl) ⟨1977200, by rfl⟩ : syracuseStep 42180277 = 3954401) B3954401
theorem B1924799 : Blo 1281959 1924799 := bstep (se 1 (by rfl) ⟨1443599, by rfl⟩ : syracuseStep 1924799 = 2887199) B2887199
theorem B28131401 : Blo 1281959 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B1925447 : Blo 1281959 1925447 := bstep (se 1 (by rfl) ⟨1444085, by rfl⟩ : syracuseStep 1925447 = 2888171) B2888171
theorem B2310697 : Blo 1281959 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B6169277 : Blo 1281959 6169277 := bstep (se 3 (by rfl) ⟨1156739, by rfl⟩ : syracuseStep 6169277 = 2313479) B2313479
theorem B2164279 : Blo 1281959 2164279 := bstep (se 1 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 2164279 = 3246419) B3246419
theorem B2885543 : Blo 1281959 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B26331115 : Blo 1281959 26331115 := bstep (se 1 (by rfl) ⟨19748336, by rfl⟩ : syracuseStep 26331115 = 39496673) B39496673
theorem B3082313 : Blo 1281959 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B2435255 : Blo 1281959 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B4327613 : Blo 1281959 4327613 := bstep (se 3 (by rfl) ⟨811427, by rfl⟩ : syracuseStep 4327613 = 1622855) B1622855
theorem B56240369 : Blo 1281959 56240369 := bstep (se 2 (by rfl) ⟨21090138, by rfl⟩ : syracuseStep 56240369 = 42180277) B42180277
theorem B26331439 : Blo 1281959 26331439 := bstep (se 1 (by rfl) ⟨19748579, by rfl⟩ : syracuseStep 26331439 = 39497159) B39497159
theorem B16452071 : Blo 1281959 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B2886191 : Blo 1281959 2886191 := bstep (se 1 (by rfl) ⟨2164643, by rfl⟩ : syracuseStep 2886191 = 4329287) B4329287
theorem B3246875 : Blo 1281959 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B2436007 : Blo 1281959 2436007 := bstep (se 1 (by rfl) ⟨1827005, by rfl⟩ : syracuseStep 2436007 = 3654011) B3654011
theorem B5483629 : Blo 1281959 5483629 := bstep (se 3 (by rfl) ⟨1028180, by rfl⟩ : syracuseStep 5483629 = 2056361) B2056361
theorem B4328639 : Blo 1281959 4328639 := bstep (se 1 (by rfl) ⟨3246479, by rfl⟩ : syracuseStep 4328639 = 6492959) B6492959
theorem B7302575 : Blo 1281959 7302575 := bstep (se 1 (by rfl) ⟨5476931, by rfl⟩ : syracuseStep 7302575 = 10953863) B10953863
theorem B4869659 : Blo 1281959 4869659 := bstep (se 1 (by rfl) ⟨3652244, by rfl⟩ : syracuseStep 4869659 = 7304489) B7304489
theorem B12324635 : Blo 1281959 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B6934511 : Blo 1281959 6934511 := bstep (se 1 (by rfl) ⟨5200883, by rfl⟩ : syracuseStep 6934511 = 10401767) B10401767
theorem B1282047 : Blo 1281959 1282047 := bstep (se 1 (by rfl) ⟨961535, by rfl⟩ : syracuseStep 1282047 = 1923071) B1923071
theorem B1282215 : Blo 1281959 1282215 := bstep (se 1 (by rfl) ⟨961661, by rfl⟩ : syracuseStep 1282215 = 1923323) B1923323
theorem B5558723 : Blo 1281959 5558723 := bstep (se 1 (by rfl) ⟨4169042, by rfl⟩ : syracuseStep 5558723 = 8338085) B8338085
theorem B1282687 : Blo 1281959 1282687 := bstep (se 1 (by rfl) ⟨962015, by rfl⟩ : syracuseStep 1282687 = 1924031) B1924031
theorem B18485981 : Blo 1281959 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B2888423 : Blo 1281959 2888423 := bstep (se 1 (by rfl) ⟨2166317, by rfl⟩ : syracuseStep 2888423 = 4332635) B4332635
theorem B1283119 : Blo 1281959 1283119 := bstep (se 1 (by rfl) ⟨962339, by rfl⟩ : syracuseStep 1283119 = 1924679) B1924679
theorem B1283199 : Blo 1281959 1283199 := bstep (se 1 (by rfl) ⟨962399, by rfl⟩ : syracuseStep 1283199 = 1924799) B1924799
theorem B3650923 : Blo 1281959 3650923 := bstep (se 1 (by rfl) ⟨2738192, by rfl⟩ : syracuseStep 3650923 = 5476385) B5476385
theorem B1283535 : Blo 1281959 1283535 := bstep (se 1 (by rfl) ⟨962651, by rfl⟩ : syracuseStep 1283535 = 1925303) B1925303
theorem B16438949 : Blo 1281959 16438949 := bstep (se 4 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 16438949 = 3082303) B3082303
theorem B15595361 : Blo 1281959 15595361 := bstep (se 2 (by rfl) ⟨5848260, by rfl⟩ : syracuseStep 15595361 = 11696521) B11696521
theorem B7510043 : Blo 1281959 7510043 := bstep (se 1 (by rfl) ⟨5632532, by rfl⟩ : syracuseStep 7510043 = 11265065) B11265065
theorem B1923239 : Blo 1281959 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B4331771 : Blo 1281959 4331771 := bstep (se 1 (by rfl) ⟨3248828, by rfl⟩ : syracuseStep 4331771 = 6497657) B6497657
theorem B4331879 : Blo 1281959 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B1923563 : Blo 1281959 1923563 := bstep (se 1 (by rfl) ⟨1442672, by rfl⟩ : syracuseStep 1923563 = 2885345) B2885345
theorem B3652199 : Blo 1281959 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B4389547 : Blo 1281959 4389547 := bstep (se 1 (by rfl) ⟨3292160, by rfl⟩ : syracuseStep 4389547 = 6584321) B6584321
theorem B4332203 : Blo 1281959 4332203 := bstep (se 1 (by rfl) ⟨3249152, by rfl⟩ : syracuseStep 4332203 = 6498305) B6498305
theorem B1924091 : Blo 1281959 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B1924511 : Blo 1281959 1924511 := bstep (se 1 (by rfl) ⟨1443383, by rfl⟩ : syracuseStep 1924511 = 2886767) B2886767
theorem B17800681 : Blo 1281959 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B1924655 : Blo 1281959 1924655 := bstep (se 1 (by rfl) ⟨1443491, by rfl⟩ : syracuseStep 1924655 = 2886983) B2886983
theorem B14622281 : Blo 1281959 14622281 := bstep (se 2 (by rfl) ⟨5483355, by rfl⟩ : syracuseStep 14622281 = 10966711) B10966711
theorem B1924763 : Blo 1281959 1924763 := bstep (se 1 (by rfl) ⟨1443572, by rfl⟩ : syracuseStep 1924763 = 2887145) B2887145
theorem B1924859 : Blo 1281959 1924859 := bstep (se 1 (by rfl) ⟨1443644, by rfl⟩ : syracuseStep 1924859 = 2887289) B2887289
theorem B1924943 : Blo 1281959 1924943 := bstep (se 1 (by rfl) ⟨1443707, by rfl⟩ : syracuseStep 1924943 = 2887415) B2887415
theorem B4112851 : Blo 1281959 4112851 := bstep (se 1 (by rfl) ⟨3084638, by rfl⟩ : syracuseStep 4112851 = 6169277) B6169277
theorem B1925615 : Blo 1281959 1925615 := bstep (se 1 (by rfl) ⟨1444211, by rfl⟩ : syracuseStep 1925615 = 2888423) B2888423
theorem B3080929 : Blo 1281959 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B10396907 : Blo 1281959 10396907 := bstep (se 1 (by rfl) ⟨7797680, by rfl⟩ : syracuseStep 10396907 = 15595361) B15595361
theorem B1623503 : Blo 1281959 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B2885075 : Blo 1281959 2885075 := bstep (se 1 (by rfl) ⟨2163806, by rfl⟩ : syracuseStep 2885075 = 4327613) B4327613
theorem B2434799 : Blo 1281959 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B4867897 : Blo 1281959 4867897 := bstep (se 2 (by rfl) ⟨1825461, by rfl⟩ : syracuseStep 4867897 = 3650923) B3650923
theorem B2164583 : Blo 1281959 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B23734241 : Blo 1281959 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B2885705 : Blo 1281959 2885705 := bstep (se 2 (by rfl) ⟨1082139, by rfl⟩ : syracuseStep 2885705 = 2164279) B2164279
theorem B2885759 : Blo 1281959 2885759 := bstep (se 1 (by rfl) ⟨2164319, by rfl⟩ : syracuseStep 2885759 = 4328639) B4328639
theorem B4868383 : Blo 1281959 4868383 := bstep (se 1 (by rfl) ⟨3651287, by rfl⟩ : syracuseStep 4868383 = 7302575) B7302575
theorem B3246439 : Blo 1281959 3246439 := bstep (se 1 (by rfl) ⟨2434829, by rfl⟩ : syracuseStep 3246439 = 4869659) B4869659
theorem B4623007 : Blo 1281959 4623007 := bstep (se 1 (by rfl) ⟨3467255, by rfl⟩ : syracuseStep 4623007 = 6934511) B6934511
theorem B18754267 : Blo 1281959 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B3705815 : Blo 1281959 3705815 := bstep (se 1 (by rfl) ⟨2779361, by rfl⟩ : syracuseStep 3705815 = 5558723) B5558723
theorem B12323987 : Blo 1281959 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B5852729 : Blo 1281959 5852729 := bstep (se 2 (by rfl) ⟨2194773, by rfl⟩ : syracuseStep 5852729 = 4389547) B4389547
theorem B3248009 : Blo 1281959 3248009 := bstep (se 2 (by rfl) ⟨1218003, by rfl⟩ : syracuseStep 3248009 = 2436007) B2436007
theorem B1282159 : Blo 1281959 1282159 := bstep (se 1 (by rfl) ⟨961619, by rfl⟩ : syracuseStep 1282159 = 1923239) B1923239
theorem B7311505 : Blo 1281959 7311505 := bstep (se 2 (by rfl) ⟨2741814, by rfl⟩ : syracuseStep 7311505 = 5483629) B5483629
theorem B2887847 : Blo 1281959 2887847 := bstep (se 1 (by rfl) ⟨2165885, by rfl⟩ : syracuseStep 2887847 = 4331771) B4331771
theorem B2887919 : Blo 1281959 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B1282375 : Blo 1281959 1282375 := bstep (se 1 (by rfl) ⟨961781, by rfl⟩ : syracuseStep 1282375 = 1923563) B1923563
theorem B2888135 : Blo 1281959 2888135 := bstep (se 1 (by rfl) ⟨2166101, by rfl⟩ : syracuseStep 2888135 = 4332203) B4332203
theorem B1282727 : Blo 1281959 1282727 := bstep (se 1 (by rfl) ⟨962045, by rfl⟩ : syracuseStep 1282727 = 1924091) B1924091
theorem B1283007 : Blo 1281959 1283007 := bstep (se 1 (by rfl) ⟨962255, by rfl⟩ : syracuseStep 1283007 = 1924511) B1924511
theorem B1283103 : Blo 1281959 1283103 := bstep (se 1 (by rfl) ⟨962327, by rfl⟩ : syracuseStep 1283103 = 1924655) B1924655
theorem B1283175 : Blo 1281959 1283175 := bstep (se 1 (by rfl) ⟨962381, by rfl⟩ : syracuseStep 1283175 = 1924763) B1924763
theorem B1283239 : Blo 1281959 1283239 := bstep (se 1 (by rfl) ⟨962429, by rfl⟩ : syracuseStep 1283239 = 1924859) B1924859
theorem B1283295 : Blo 1281959 1283295 := bstep (se 1 (by rfl) ⟨962471, by rfl⟩ : syracuseStep 1283295 = 1924943) B1924943
theorem B35108153 : Blo 1281959 35108153 := bstep (se 2 (by rfl) ⟨13165557, by rfl⟩ : syracuseStep 35108153 = 26331115) B26331115
theorem B20026781 : Blo 1281959 20026781 := bstep (se 3 (by rfl) ⟨3755021, by rfl⟩ : syracuseStep 20026781 = 7510043) B7510043
theorem B1283631 : Blo 1281959 1283631 := bstep (se 1 (by rfl) ⟨962723, by rfl⟩ : syracuseStep 1283631 = 1925447) B1925447
theorem B35108585 : Blo 1281959 35108585 := bstep (se 2 (by rfl) ⟨13165719, by rfl⟩ : syracuseStep 35108585 = 26331439) B26331439
theorem B10959299 : Blo 1281959 10959299 := bstep (se 1 (by rfl) ⟨8219474, by rfl⟩ : syracuseStep 10959299 = 16438949) B16438949
theorem B1923695 : Blo 1281959 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B2054875 : Blo 1281959 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B37493579 : Blo 1281959 37493579 := bstep (se 1 (by rfl) ⟨28120184, by rfl⟩ : syracuseStep 37493579 = 56240369) B56240369
theorem B10968047 : Blo 1281959 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B1924127 : Blo 1281959 1924127 := bstep (se 1 (by rfl) ⟨1443095, by rfl⟩ : syracuseStep 1924127 = 2886191) B2886191
theorem B9748187 : Blo 1281959 9748187 := bstep (se 1 (by rfl) ⟨7311140, by rfl⟩ : syracuseStep 9748187 = 14622281) B14622281
theorem B8216423 : Blo 1281959 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B1925231 : Blo 1281959 1925231 := bstep (se 1 (by rfl) ⟨1443923, by rfl⟩ : syracuseStep 1925231 = 2887847) B2887847
theorem B1925279 : Blo 1281959 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B9748673 : Blo 1281959 9748673 := bstep (se 2 (by rfl) ⟨3655752, by rfl⟩ : syracuseStep 9748673 = 7311505) B7311505
theorem B1925423 : Blo 1281959 1925423 := bstep (se 1 (by rfl) ⟨1444067, by rfl⟩ : syracuseStep 1925423 = 2888135) B2888135
theorem B6931271 : Blo 1281959 6931271 := bstep (se 1 (by rfl) ⟨5198453, by rfl⟩ : syracuseStep 6931271 = 10396907) B10396907
theorem B23405435 : Blo 1281959 23405435 := bstep (se 1 (by rfl) ⟨17554076, by rfl⟩ : syracuseStep 23405435 = 35108153) B35108153
theorem B23405723 : Blo 1281959 23405723 := bstep (se 1 (by rfl) ⟨17554292, by rfl⟩ : syracuseStep 23405723 = 35108585) B35108585
theorem B1443055 : Blo 1281959 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B24995719 : Blo 1281959 24995719 := bstep (se 1 (by rfl) ⟨18746789, by rfl⟩ : syracuseStep 24995719 = 37493579) B37493579
theorem B3901819 : Blo 1281959 3901819 := bstep (se 1 (by rfl) ⟨2926364, by rfl⟩ : syracuseStep 3901819 = 5852729) B5852729
theorem B6490529 : Blo 1281959 6490529 := bstep (se 2 (by rfl) ⟨2433948, by rfl⟩ : syracuseStep 6490529 = 4867897) B4867897
theorem B6498791 : Blo 1281959 6498791 := bstep (se 1 (by rfl) ⟨4874093, by rfl⟩ : syracuseStep 6498791 = 9748187) B9748187
theorem B2165339 : Blo 1281959 2165339 := bstep (se 1 (by rfl) ⟨1624004, by rfl⟩ : syracuseStep 2165339 = 3248009) B3248009
theorem B6491177 : Blo 1281959 6491177 := bstep (se 2 (by rfl) ⟨2434191, by rfl⟩ : syracuseStep 6491177 = 4868383) B4868383
theorem B4328585 : Blo 1281959 4328585 := bstep (se 2 (by rfl) ⟨1623219, by rfl⟩ : syracuseStep 4328585 = 3246439) B3246439
theorem B5483801 : Blo 1281959 5483801 := bstep (se 2 (by rfl) ⟨2056425, by rfl⟩ : syracuseStep 5483801 = 4112851) B4112851
theorem B6164009 : Blo 1281959 6164009 := bstep (se 2 (by rfl) ⟨2311503, by rfl⟩ : syracuseStep 6164009 = 4623007) B4623007
theorem B2739833 : Blo 1281959 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B25005689 : Blo 1281959 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B4107905 : Blo 1281959 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B4329341 : Blo 1281959 4329341 := bstep (se 3 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 4329341 = 1623503) B1623503
theorem B15822827 : Blo 1281959 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B1282463 : Blo 1281959 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B6492797 : Blo 1281959 6492797 := bstep (se 3 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 6492797 = 2434799) B2434799
theorem B2470543 : Blo 1281959 2470543 := bstep (se 1 (by rfl) ⟨1852907, by rfl⟩ : syracuseStep 2470543 = 3705815) B3705815
theorem B7312031 : Blo 1281959 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B1282751 : Blo 1281959 1282751 := bstep (se 1 (by rfl) ⟨962063, by rfl⟩ : syracuseStep 1282751 = 1924127) B1924127
theorem B5477615 : Blo 1281959 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B1283743 : Blo 1281959 1283743 := bstep (se 1 (by rfl) ⟨962807, by rfl⟩ : syracuseStep 1283743 = 1925615) B1925615
theorem B13351187 : Blo 1281959 13351187 := bstep (se 1 (by rfl) ⟨10013390, by rfl⟩ : syracuseStep 13351187 = 20026781) B20026781
theorem B1923383 : Blo 1281959 1923383 := bstep (se 1 (by rfl) ⟨1442537, by rfl⟩ : syracuseStep 1923383 = 2885075) B2885075
theorem B1923803 : Blo 1281959 1923803 := bstep (se 1 (by rfl) ⟨1442852, by rfl⟩ : syracuseStep 1923803 = 2885705) B2885705
theorem B1923839 : Blo 1281959 1923839 := bstep (se 1 (by rfl) ⟨1442879, by rfl⟩ : syracuseStep 1923839 = 2885759) B2885759
theorem B7306199 : Blo 1281959 7306199 := bstep (se 1 (by rfl) ⟨5479649, by rfl⟩ : syracuseStep 7306199 = 10959299) B10959299
theorem B8215991 : Blo 1281959 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B4874687 : Blo 1281959 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B5202425 : Blo 1281959 5202425 := bstep (se 2 (by rfl) ⟨1950909, by rfl⟩ : syracuseStep 5202425 = 3901819) B3901819
theorem B4620847 : Blo 1281959 4620847 := bstep (se 1 (by rfl) ⟨3465635, by rfl⟩ : syracuseStep 4620847 = 6931271) B6931271
theorem B35603165 : Blo 1281959 35603165 := bstep (se 3 (by rfl) ⟨6675593, by rfl⟩ : syracuseStep 35603165 = 13351187) B13351187
theorem B4327019 : Blo 1281959 4327019 := bstep (se 1 (by rfl) ⟨3245264, by rfl⟩ : syracuseStep 4327019 = 6490529) B6490529
theorem B1443559 : Blo 1281959 1443559 := bstep (se 1 (by rfl) ⟨1082669, by rfl⟩ : syracuseStep 1443559 = 2165339) B2165339
theorem B4327451 : Blo 1281959 4327451 := bstep (se 1 (by rfl) ⟨3245588, by rfl⟩ : syracuseStep 4327451 = 6491177) B6491177
theorem B2885723 : Blo 1281959 2885723 := bstep (se 1 (by rfl) ⟨2164292, by rfl⟩ : syracuseStep 2885723 = 4328585) B4328585
theorem B3655867 : Blo 1281959 3655867 := bstep (se 1 (by rfl) ⟨2741900, by rfl⟩ : syracuseStep 3655867 = 5483801) B5483801
theorem B2738603 : Blo 1281959 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B33327625 : Blo 1281959 33327625 := bstep (se 2 (by rfl) ⟨12497859, by rfl⟩ : syracuseStep 33327625 = 24995719) B24995719
theorem B2886227 : Blo 1281959 2886227 := bstep (se 1 (by rfl) ⟨2164670, by rfl⟩ : syracuseStep 2886227 = 4329341) B4329341
theorem B6499115 : Blo 1281959 6499115 := bstep (se 1 (by rfl) ⟨4874336, by rfl⟩ : syracuseStep 6499115 = 9748673) B9748673
theorem B4328531 : Blo 1281959 4328531 := bstep (se 1 (by rfl) ⟨3246398, by rfl⟩ : syracuseStep 4328531 = 6492797) B6492797
theorem B13176229 : Blo 1281959 13176229 := bstep (se 4 (by rfl) ⟨1235271, by rfl⟩ : syracuseStep 13176229 = 2470543) B2470543
theorem B1282255 : Blo 1281959 1282255 := bstep (se 1 (by rfl) ⟨961691, by rfl⟩ : syracuseStep 1282255 = 1923383) B1923383
theorem B1282535 : Blo 1281959 1282535 := bstep (se 1 (by rfl) ⟨961901, by rfl⟩ : syracuseStep 1282535 = 1923803) B1923803
theorem B1282559 : Blo 1281959 1282559 := bstep (se 1 (by rfl) ⟨961919, by rfl⟩ : syracuseStep 1282559 = 1923839) B1923839
theorem B4870799 : Blo 1281959 4870799 := bstep (se 1 (by rfl) ⟨3653099, by rfl⟩ : syracuseStep 4870799 = 7306199) B7306199
theorem B5477327 : Blo 1281959 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B4109339 : Blo 1281959 4109339 := bstep (se 1 (by rfl) ⟨3082004, by rfl⟩ : syracuseStep 4109339 = 6164009) B6164009
theorem B10548551 : Blo 1281959 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B1283487 : Blo 1281959 1283487 := bstep (se 1 (by rfl) ⟨962615, by rfl⟩ : syracuseStep 1283487 = 1925231) B1925231
theorem B1283519 : Blo 1281959 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B1283615 : Blo 1281959 1283615 := bstep (se 1 (by rfl) ⟨962711, by rfl⟩ : syracuseStep 1283615 = 1925423) B1925423
theorem B15603623 : Blo 1281959 15603623 := bstep (se 1 (by rfl) ⟨11702717, by rfl⟩ : syracuseStep 15603623 = 23405435) B23405435
theorem B15603815 : Blo 1281959 15603815 := bstep (se 1 (by rfl) ⟨11702861, by rfl⟩ : syracuseStep 15603815 = 23405723) B23405723
theorem B3651743 : Blo 1281959 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B1924073 : Blo 1281959 1924073 := bstep (se 2 (by rfl) ⟨721527, by rfl⟩ : syracuseStep 1924073 = 1443055) B1443055
theorem B4332527 : Blo 1281959 4332527 := bstep (se 1 (by rfl) ⟨3249395, by rfl⟩ : syracuseStep 4332527 = 6498791) B6498791
theorem B1826555 : Blo 1281959 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B16670459 : Blo 1281959 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B4874489 : Blo 1281959 4874489 := bstep (se 2 (by rfl) ⟨1827933, by rfl⟩ : syracuseStep 4874489 = 3655867) B3655867
theorem B6161129 : Blo 1281959 6161129 := bstep (se 2 (by rfl) ⟨2310423, by rfl⟩ : syracuseStep 6161129 = 4620847) B4620847
theorem B2884679 : Blo 1281959 2884679 := bstep (se 1 (by rfl) ⟨2163509, by rfl⟩ : syracuseStep 2884679 = 4327019) B4327019
theorem B2884967 : Blo 1281959 2884967 := bstep (se 1 (by rfl) ⟨2163725, by rfl⟩ : syracuseStep 2884967 = 4327451) B4327451
theorem B2885687 : Blo 1281959 2885687 := bstep (se 1 (by rfl) ⟨2164265, by rfl⟩ : syracuseStep 2885687 = 4328531) B4328531
theorem B3247199 : Blo 1281959 3247199 := bstep (se 1 (by rfl) ⟨2435399, by rfl⟩ : syracuseStep 3247199 = 4870799) B4870799
theorem B23735443 : Blo 1281959 23735443 := bstep (se 1 (by rfl) ⟨17801582, by rfl⟩ : syracuseStep 23735443 = 35603165) B35603165
theorem B44436833 : Blo 1281959 44436833 := bstep (se 2 (by rfl) ⟨16663812, by rfl⟩ : syracuseStep 44436833 = 33327625) B33327625
theorem B7032367 : Blo 1281959 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B13873133 : Blo 1281959 13873133 := bstep (se 3 (by rfl) ⟨2601212, by rfl⟩ : syracuseStep 13873133 = 5202425) B5202425
theorem B17568305 : Blo 1281959 17568305 := bstep (se 2 (by rfl) ⟨6588114, by rfl⟩ : syracuseStep 17568305 = 13176229) B13176229
theorem B1282715 : Blo 1281959 1282715 := bstep (se 1 (by rfl) ⟨962036, by rfl⟩ : syracuseStep 1282715 = 1924073) B1924073
theorem B4870813 : Blo 1281959 4870813 := bstep (se 3 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 4870813 = 1826555) B1826555
theorem B44454557 : Blo 1281959 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B2888351 : Blo 1281959 2888351 := bstep (se 1 (by rfl) ⟨2166263, by rfl⟩ : syracuseStep 2888351 = 4332527) B4332527
theorem B10958237 : Blo 1281959 10958237 := bstep (se 3 (by rfl) ⟨2054669, by rfl⟩ : syracuseStep 10958237 = 4109339) B4109339
theorem B3249791 : Blo 1281959 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B9737981 : Blo 1281959 9737981 := bstep (se 3 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 9737981 = 3651743) B3651743
theorem B3651551 : Blo 1281959 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B10402415 : Blo 1281959 10402415 := bstep (se 1 (by rfl) ⟨7801811, by rfl⟩ : syracuseStep 10402415 = 15603623) B15603623
theorem B1923815 : Blo 1281959 1923815 := bstep (se 1 (by rfl) ⟨1442861, by rfl⟩ : syracuseStep 1923815 = 2885723) B2885723
theorem B10402543 : Blo 1281959 10402543 := bstep (se 1 (by rfl) ⟨7801907, by rfl⟩ : syracuseStep 10402543 = 15603815) B15603815
theorem B1825735 : Blo 1281959 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B1924151 : Blo 1281959 1924151 := bstep (se 1 (by rfl) ⟨1443113, by rfl⟩ : syracuseStep 1924151 = 2886227) B2886227
theorem B4332743 : Blo 1281959 4332743 := bstep (se 1 (by rfl) ⟨3249557, by rfl⟩ : syracuseStep 4332743 = 6499115) B6499115
theorem B1924745 : Blo 1281959 1924745 := bstep (se 2 (by rfl) ⟨721779, by rfl⟩ : syracuseStep 1924745 = 1443559) B1443559
theorem B1925567 : Blo 1281959 1925567 := bstep (se 1 (by rfl) ⟨1444175, by rfl⟩ : syracuseStep 1925567 = 2888351) B2888351
theorem B13870057 : Blo 1281959 13870057 := bstep (se 2 (by rfl) ⟨5201271, by rfl⟩ : syracuseStep 13870057 = 10402543) B10402543
theorem B2434313 : Blo 1281959 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B2434367 : Blo 1281959 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B31647257 : Blo 1281959 31647257 := bstep (se 2 (by rfl) ⟨11867721, by rfl⟩ : syracuseStep 31647257 = 23735443) B23735443
theorem B2164799 : Blo 1281959 2164799 := bstep (se 1 (by rfl) ⟨1623599, by rfl⟩ : syracuseStep 2164799 = 3247199) B3247199
theorem B29624555 : Blo 1281959 29624555 := bstep (se 1 (by rfl) ⟨22218416, by rfl⟩ : syracuseStep 29624555 = 44436833) B44436833
theorem B4107419 : Blo 1281959 4107419 := bstep (se 1 (by rfl) ⟨3080564, by rfl⟩ : syracuseStep 4107419 = 6161129) B6161129
theorem B2166527 : Blo 1281959 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B6491987 : Blo 1281959 6491987 := bstep (se 1 (by rfl) ⟨4868990, by rfl⟩ : syracuseStep 6491987 = 9737981) B9737981
theorem B6934943 : Blo 1281959 6934943 := bstep (se 1 (by rfl) ⟨5201207, by rfl⟩ : syracuseStep 6934943 = 10402415) B10402415
theorem B1282543 : Blo 1281959 1282543 := bstep (se 1 (by rfl) ⟨961907, by rfl⟩ : syracuseStep 1282543 = 1923815) B1923815
theorem B1282767 : Blo 1281959 1282767 := bstep (se 1 (by rfl) ⟨962075, by rfl⟩ : syracuseStep 1282767 = 1924151) B1924151
theorem B9376489 : Blo 1281959 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B2888495 : Blo 1281959 2888495 := bstep (se 1 (by rfl) ⟨2166371, by rfl⟩ : syracuseStep 2888495 = 4332743) B4332743
theorem B1283163 : Blo 1281959 1283163 := bstep (se 1 (by rfl) ⟨962372, by rfl⟩ : syracuseStep 1283163 = 1924745) B1924745
theorem B3249659 : Blo 1281959 3249659 := bstep (se 1 (by rfl) ⟨2437244, by rfl⟩ : syracuseStep 3249659 = 4874489) B4874489
theorem B11712203 : Blo 1281959 11712203 := bstep (se 1 (by rfl) ⟨8784152, by rfl⟩ : syracuseStep 11712203 = 17568305) B17568305
theorem B29636371 : Blo 1281959 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B1923119 : Blo 1281959 1923119 := bstep (se 1 (by rfl) ⟨1442339, by rfl⟩ : syracuseStep 1923119 = 2884679) B2884679
theorem B6494417 : Blo 1281959 6494417 := bstep (se 2 (by rfl) ⟨2435406, by rfl⟩ : syracuseStep 6494417 = 4870813) B4870813
theorem B1923311 : Blo 1281959 1923311 := bstep (se 1 (by rfl) ⟨1442483, by rfl⟩ : syracuseStep 1923311 = 2884967) B2884967
theorem B7305491 : Blo 1281959 7305491 := bstep (se 1 (by rfl) ⟨5479118, by rfl⟩ : syracuseStep 7305491 = 10958237) B10958237
theorem B1923791 : Blo 1281959 1923791 := bstep (se 1 (by rfl) ⟨1442843, by rfl⟩ : syracuseStep 1923791 = 2885687) B2885687
theorem B9248755 : Blo 1281959 9248755 := bstep (se 1 (by rfl) ⟨6936566, by rfl⟩ : syracuseStep 9248755 = 13873133) B13873133
theorem B1925663 : Blo 1281959 1925663 := bstep (se 1 (by rfl) ⟨1444247, by rfl⟩ : syracuseStep 1925663 = 2888495) B2888495
theorem B1622911 : Blo 1281959 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B7808135 : Blo 1281959 7808135 := bstep (se 1 (by rfl) ⟨5856101, by rfl⟩ : syracuseStep 7808135 = 11712203) B11712203
theorem B1443199 : Blo 1281959 1443199 := bstep (se 1 (by rfl) ⟨1082399, by rfl⟩ : syracuseStep 1443199 = 2164799) B2164799
theorem B2738279 : Blo 1281959 2738279 := bstep (se 1 (by rfl) ⟨2053709, by rfl⟩ : syracuseStep 2738279 = 4107419) B4107419
theorem B1444351 : Blo 1281959 1444351 := bstep (se 1 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 1444351 = 2166527) B2166527
theorem B4327991 : Blo 1281959 4327991 := bstep (se 1 (by rfl) ⟨3245993, by rfl⟩ : syracuseStep 4327991 = 6491987) B6491987
theorem B12331673 : Blo 1281959 12331673 := bstep (se 2 (by rfl) ⟨4624377, by rfl⟩ : syracuseStep 12331673 = 9248755) B9248755
theorem B6491501 : Blo 1281959 6491501 := bstep (se 3 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 6491501 = 2434313) B2434313
theorem B2166439 : Blo 1281959 2166439 := bstep (se 1 (by rfl) ⟨1624829, by rfl⟩ : syracuseStep 2166439 = 3249659) B3249659
theorem B21098171 : Blo 1281959 21098171 := bstep (se 1 (by rfl) ⟨15823628, by rfl⟩ : syracuseStep 21098171 = 31647257) B31647257
theorem B18493181 : Blo 1281959 18493181 := bstep (se 3 (by rfl) ⟨3467471, by rfl⟩ : syracuseStep 18493181 = 6934943) B6934943
theorem B50007941 : Blo 1281959 50007941 := bstep (se 4 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 50007941 = 9376489) B9376489
theorem B18493409 : Blo 1281959 18493409 := bstep (se 2 (by rfl) ⟨6935028, by rfl⟩ : syracuseStep 18493409 = 13870057) B13870057
theorem B1282079 : Blo 1281959 1282079 := bstep (se 1 (by rfl) ⟨961559, by rfl⟩ : syracuseStep 1282079 = 1923119) B1923119
theorem B4329611 : Blo 1281959 4329611 := bstep (se 1 (by rfl) ⟨3247208, by rfl⟩ : syracuseStep 4329611 = 6494417) B6494417
theorem B1282207 : Blo 1281959 1282207 := bstep (se 1 (by rfl) ⟨961655, by rfl⟩ : syracuseStep 1282207 = 1923311) B1923311
theorem B4870327 : Blo 1281959 4870327 := bstep (se 1 (by rfl) ⟨3652745, by rfl⟩ : syracuseStep 4870327 = 7305491) B7305491
theorem B1282527 : Blo 1281959 1282527 := bstep (se 1 (by rfl) ⟨961895, by rfl⟩ : syracuseStep 1282527 = 1923791) B1923791
theorem B39515161 : Blo 1281959 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B1283711 : Blo 1281959 1283711 := bstep (se 1 (by rfl) ⟨962783, by rfl⟩ : syracuseStep 1283711 = 1925567) B1925567
theorem B19749703 : Blo 1281959 19749703 := bstep (se 1 (by rfl) ⟨14812277, by rfl⟩ : syracuseStep 19749703 = 29624555) B29624555
theorem B1925801 : Blo 1281959 1925801 := bstep (se 2 (by rfl) ⟨722175, by rfl⟩ : syracuseStep 1925801 = 1444351) B1444351
theorem B2163881 : Blo 1281959 2163881 := bstep (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) B1622911
theorem B2885327 : Blo 1281959 2885327 := bstep (se 1 (by rfl) ⟨2163995, by rfl⟩ : syracuseStep 2885327 = 4327991) B4327991
theorem B4327667 : Blo 1281959 4327667 := bstep (se 1 (by rfl) ⟨3245750, by rfl⟩ : syracuseStep 4327667 = 6491501) B6491501
theorem B2886407 : Blo 1281959 2886407 := bstep (se 1 (by rfl) ⟨2164805, by rfl⟩ : syracuseStep 2886407 = 4329611) B4329611
theorem B26332937 : Blo 1281959 26332937 := bstep (se 2 (by rfl) ⟨9874851, by rfl⟩ : syracuseStep 26332937 = 19749703) B19749703
theorem B52686881 : Blo 1281959 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B8221115 : Blo 1281959 8221115 := bstep (se 1 (by rfl) ⟨6165836, by rfl⟩ : syracuseStep 8221115 = 12331673) B12331673
theorem B2888585 : Blo 1281959 2888585 := bstep (se 2 (by rfl) ⟨1083219, by rfl⟩ : syracuseStep 2888585 = 2166439) B2166439
theorem B33338627 : Blo 1281959 33338627 := bstep (se 1 (by rfl) ⟨25003970, by rfl⟩ : syracuseStep 33338627 = 50007941) B50007941
theorem B6493769 : Blo 1281959 6493769 := bstep (se 2 (by rfl) ⟨2435163, by rfl⟩ : syracuseStep 6493769 = 4870327) B4870327
theorem B20821693 : Blo 1281959 20821693 := bstep (se 3 (by rfl) ⟨3904067, by rfl⟩ : syracuseStep 20821693 = 7808135) B7808135
theorem B1283775 : Blo 1281959 1283775 := bstep (se 1 (by rfl) ⟨962831, by rfl⟩ : syracuseStep 1283775 = 1925663) B1925663
theorem B1825519 : Blo 1281959 1825519 := bstep (se 1 (by rfl) ⟨1369139, by rfl⟩ : syracuseStep 1825519 = 2738279) B2738279
theorem B1924265 : Blo 1281959 1924265 := bstep (se 2 (by rfl) ⟨721599, by rfl⟩ : syracuseStep 1924265 = 1443199) B1443199
theorem B14065447 : Blo 1281959 14065447 := bstep (se 1 (by rfl) ⟨10549085, by rfl⟩ : syracuseStep 14065447 = 21098171) B21098171
theorem B12328787 : Blo 1281959 12328787 := bstep (se 1 (by rfl) ⟨9246590, by rfl⟩ : syracuseStep 12328787 = 18493181) B18493181
theorem B12328939 : Blo 1281959 12328939 := bstep (se 1 (by rfl) ⟨9246704, by rfl⟩ : syracuseStep 12328939 = 18493409) B18493409
theorem B5480743 : Blo 1281959 5480743 := bstep (se 1 (by rfl) ⟨4110557, by rfl⟩ : syracuseStep 5480743 = 8221115) B8221115
theorem B1925723 : Blo 1281959 1925723 := bstep (se 1 (by rfl) ⟨1444292, by rfl⟩ : syracuseStep 1925723 = 2888585) B2888585
theorem B1442587 : Blo 1281959 1442587 := bstep (se 1 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 1442587 = 2163881) B2163881
theorem B22225751 : Blo 1281959 22225751 := bstep (se 1 (by rfl) ⟨16669313, by rfl⟩ : syracuseStep 22225751 = 33338627) B33338627
theorem B2434025 : Blo 1281959 2434025 := bstep (se 2 (by rfl) ⟨912759, by rfl⟩ : syracuseStep 2434025 = 1825519) B1825519
theorem B2885111 : Blo 1281959 2885111 := bstep (se 1 (by rfl) ⟨2163833, by rfl⟩ : syracuseStep 2885111 = 4327667) B4327667
theorem B18753929 : Blo 1281959 18753929 := bstep (se 2 (by rfl) ⟨7032723, by rfl⟩ : syracuseStep 18753929 = 14065447) B14065447
theorem B8219191 : Blo 1281959 8219191 := bstep (se 1 (by rfl) ⟨6164393, by rfl⟩ : syracuseStep 8219191 = 12328787) B12328787
theorem B4329179 : Blo 1281959 4329179 := bstep (se 1 (by rfl) ⟨3246884, by rfl⟩ : syracuseStep 4329179 = 6493769) B6493769
theorem B1282843 : Blo 1281959 1282843 := bstep (se 1 (by rfl) ⟨962132, by rfl⟩ : syracuseStep 1282843 = 1924265) B1924265
theorem B16438585 : Blo 1281959 16438585 := bstep (se 2 (by rfl) ⟨6164469, by rfl⟩ : syracuseStep 16438585 = 12328939) B12328939
theorem B35124587 : Blo 1281959 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B1283867 : Blo 1281959 1283867 := bstep (se 1 (by rfl) ⟨962900, by rfl⟩ : syracuseStep 1283867 = 1925801) B1925801
theorem B1923551 : Blo 1281959 1923551 := bstep (se 1 (by rfl) ⟨1442663, by rfl⟩ : syracuseStep 1923551 = 2885327) B2885327
theorem B1924271 : Blo 1281959 1924271 := bstep (se 1 (by rfl) ⟨1443203, by rfl⟩ : syracuseStep 1924271 = 2886407) B2886407
theorem B27762257 : Blo 1281959 27762257 := bstep (se 2 (by rfl) ⟨10410846, by rfl⟩ : syracuseStep 27762257 = 20821693) B20821693
theorem B17555291 : Blo 1281959 17555291 := bstep (se 1 (by rfl) ⟨13166468, by rfl⟩ : syracuseStep 17555291 = 26332937) B26332937
theorem B7307657 : Blo 1281959 7307657 := bstep (se 2 (by rfl) ⟨2740371, by rfl⟩ : syracuseStep 7307657 = 5480743) B5480743
theorem B1622683 : Blo 1281959 1622683 := bstep (se 1 (by rfl) ⟨1217012, by rfl⟩ : syracuseStep 1622683 = 2434025) B2434025
theorem B12502619 : Blo 1281959 12502619 := bstep (se 1 (by rfl) ⟨9376964, by rfl⟩ : syracuseStep 12502619 = 18753929) B18753929
theorem B18508171 : Blo 1281959 18508171 := bstep (se 1 (by rfl) ⟨13881128, by rfl⟩ : syracuseStep 18508171 = 27762257) B27762257
theorem B2886119 : Blo 1281959 2886119 := bstep (se 1 (by rfl) ⟨2164589, by rfl⟩ : syracuseStep 2886119 = 4329179) B4329179
theorem B23416391 : Blo 1281959 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B1282367 : Blo 1281959 1282367 := bstep (se 1 (by rfl) ⟨961775, by rfl⟩ : syracuseStep 1282367 = 1923551) B1923551
theorem B21918113 : Blo 1281959 21918113 := bstep (se 2 (by rfl) ⟨8219292, by rfl⟩ : syracuseStep 21918113 = 16438585) B16438585
theorem B1282847 : Blo 1281959 1282847 := bstep (se 1 (by rfl) ⟨962135, by rfl⟩ : syracuseStep 1282847 = 1924271) B1924271
theorem B11703527 : Blo 1281959 11703527 := bstep (se 1 (by rfl) ⟨8777645, by rfl⟩ : syracuseStep 11703527 = 17555291) B17555291
theorem B1283815 : Blo 1281959 1283815 := bstep (se 1 (by rfl) ⟨962861, by rfl⟩ : syracuseStep 1283815 = 1925723) B1925723
theorem B14817167 : Blo 1281959 14817167 := bstep (se 1 (by rfl) ⟨11112875, by rfl⟩ : syracuseStep 14817167 = 22225751) B22225751
theorem B10958921 : Blo 1281959 10958921 := bstep (se 2 (by rfl) ⟨4109595, by rfl⟩ : syracuseStep 10958921 = 8219191) B8219191
theorem B1923407 : Blo 1281959 1923407 := bstep (se 1 (by rfl) ⟨1442555, by rfl⟩ : syracuseStep 1923407 = 2885111) B2885111
theorem B1923449 : Blo 1281959 1923449 := bstep (se 2 (by rfl) ⟨721293, by rfl⟩ : syracuseStep 1923449 = 1442587) B1442587
theorem B2163577 : Blo 1281959 2163577 := bstep (se 2 (by rfl) ⟨811341, by rfl⟩ : syracuseStep 2163577 = 1622683) B1622683
theorem B24677561 : Blo 1281959 24677561 := bstep (se 2 (by rfl) ⟨9254085, by rfl⟩ : syracuseStep 24677561 = 18508171) B18508171
theorem B7802351 : Blo 1281959 7802351 := bstep (se 1 (by rfl) ⟨5851763, by rfl⟩ : syracuseStep 7802351 = 11703527) B11703527
theorem B8335079 : Blo 1281959 8335079 := bstep (se 1 (by rfl) ⟨6251309, by rfl⟩ : syracuseStep 8335079 = 12502619) B12502619
theorem B1282271 : Blo 1281959 1282271 := bstep (se 1 (by rfl) ⟨961703, by rfl⟩ : syracuseStep 1282271 = 1923407) B1923407
theorem B1282299 : Blo 1281959 1282299 := bstep (se 1 (by rfl) ⟨961724, by rfl⟩ : syracuseStep 1282299 = 1923449) B1923449
theorem B15610927 : Blo 1281959 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B4871771 : Blo 1281959 4871771 := bstep (se 1 (by rfl) ⟨3653828, by rfl⟩ : syracuseStep 4871771 = 7307657) B7307657
theorem B14612075 : Blo 1281959 14612075 := bstep (se 1 (by rfl) ⟨10959056, by rfl⟩ : syracuseStep 14612075 = 21918113) B21918113
theorem B9878111 : Blo 1281959 9878111 := bstep (se 1 (by rfl) ⟨7408583, by rfl⟩ : syracuseStep 9878111 = 14817167) B14817167
theorem B7305947 : Blo 1281959 7305947 := bstep (se 1 (by rfl) ⟨5479460, by rfl⟩ : syracuseStep 7305947 = 10958921) B10958921
theorem B1924079 : Blo 1281959 1924079 := bstep (se 1 (by rfl) ⟨1443059, by rfl⟩ : syracuseStep 1924079 = 2886119) B2886119
theorem B9741383 : Blo 1281959 9741383 := bstep (se 1 (by rfl) ⟨7306037, by rfl⟩ : syracuseStep 9741383 = 14612075) B14612075
theorem B2884769 : Blo 1281959 2884769 := bstep (se 2 (by rfl) ⟨1081788, by rfl⟩ : syracuseStep 2884769 = 2163577) B2163577
theorem B16451707 : Blo 1281959 16451707 := bstep (se 1 (by rfl) ⟨12338780, by rfl⟩ : syracuseStep 16451707 = 24677561) B24677561
theorem B5556719 : Blo 1281959 5556719 := bstep (se 1 (by rfl) ⟨4167539, by rfl⟩ : syracuseStep 5556719 = 8335079) B8335079
theorem B3247847 : Blo 1281959 3247847 := bstep (se 1 (by rfl) ⟨2435885, by rfl⟩ : syracuseStep 3247847 = 4871771) B4871771
theorem B4870631 : Blo 1281959 4870631 := bstep (se 1 (by rfl) ⟨3652973, by rfl⟩ : syracuseStep 4870631 = 7305947) B7305947
theorem B1282719 : Blo 1281959 1282719 := bstep (se 1 (by rfl) ⟨962039, by rfl⟩ : syracuseStep 1282719 = 1924079) B1924079
theorem B20814569 : Blo 1281959 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B6585407 : Blo 1281959 6585407 := bstep (se 1 (by rfl) ⟨4939055, by rfl⟩ : syracuseStep 6585407 = 9878111) B9878111
theorem B5201567 : Blo 1281959 5201567 := bstep (se 1 (by rfl) ⟨3901175, by rfl⟩ : syracuseStep 5201567 = 7802351) B7802351
theorem B3467711 : Blo 1281959 3467711 := bstep (se 1 (by rfl) ⟨2600783, by rfl⟩ : syracuseStep 3467711 = 5201567) B5201567
theorem B2165231 : Blo 1281959 2165231 := bstep (se 1 (by rfl) ⟨1623923, by rfl⟩ : syracuseStep 2165231 = 3247847) B3247847
theorem B3247087 : Blo 1281959 3247087 := bstep (se 1 (by rfl) ⟨2435315, by rfl⟩ : syracuseStep 3247087 = 4870631) B4870631
theorem B21935609 : Blo 1281959 21935609 := bstep (se 2 (by rfl) ⟨8225853, by rfl⟩ : syracuseStep 21935609 = 16451707) B16451707
theorem B6494255 : Blo 1281959 6494255 := bstep (se 1 (by rfl) ⟨4870691, by rfl⟩ : syracuseStep 6494255 = 9741383) B9741383
theorem B1923179 : Blo 1281959 1923179 := bstep (se 1 (by rfl) ⟨1442384, by rfl⟩ : syracuseStep 1923179 = 2884769) B2884769
theorem B14817917 : Blo 1281959 14817917 := bstep (se 3 (by rfl) ⟨2778359, by rfl⟩ : syracuseStep 14817917 = 5556719) B5556719
theorem B13876379 : Blo 1281959 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B4390271 : Blo 1281959 4390271 := bstep (se 1 (by rfl) ⟨3292703, by rfl⟩ : syracuseStep 4390271 = 6585407) B6585407
theorem B14623739 : Blo 1281959 14623739 := bstep (se 1 (by rfl) ⟨10967804, by rfl⟩ : syracuseStep 14623739 = 21935609) B21935609
theorem B1443487 : Blo 1281959 1443487 := bstep (se 1 (by rfl) ⟨1082615, by rfl⟩ : syracuseStep 1443487 = 2165231) B2165231
theorem B9250919 : Blo 1281959 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B2926847 : Blo 1281959 2926847 := bstep (se 1 (by rfl) ⟨2195135, by rfl⟩ : syracuseStep 2926847 = 4390271) B4390271
theorem B4329449 : Blo 1281959 4329449 := bstep (se 2 (by rfl) ⟨1623543, by rfl⟩ : syracuseStep 4329449 = 3247087) B3247087
theorem B4329503 : Blo 1281959 4329503 := bstep (se 1 (by rfl) ⟨3247127, by rfl⟩ : syracuseStep 4329503 = 6494255) B6494255
theorem B1282119 : Blo 1281959 1282119 := bstep (se 1 (by rfl) ⟨961589, by rfl⟩ : syracuseStep 1282119 = 1923179) B1923179
theorem B9247229 : Blo 1281959 9247229 := bstep (se 3 (by rfl) ⟨1733855, by rfl⟩ : syracuseStep 9247229 = 3467711) B3467711
theorem B9878611 : Blo 1281959 9878611 := bstep (se 1 (by rfl) ⟨7408958, by rfl⟩ : syracuseStep 9878611 = 14817917) B14817917
theorem B9749159 : Blo 1281959 9749159 := bstep (se 1 (by rfl) ⟨7311869, by rfl⟩ : syracuseStep 9749159 = 14623739) B14623739
theorem B2886299 : Blo 1281959 2886299 := bstep (se 1 (by rfl) ⟨2164724, by rfl⟩ : syracuseStep 2886299 = 4329449) B4329449
theorem B2886335 : Blo 1281959 2886335 := bstep (se 1 (by rfl) ⟨2164751, by rfl⟩ : syracuseStep 2886335 = 4329503) B4329503
theorem B6164819 : Blo 1281959 6164819 := bstep (se 1 (by rfl) ⟨4623614, by rfl⟩ : syracuseStep 6164819 = 9247229) B9247229
theorem B7804925 : Blo 1281959 7804925 := bstep (se 3 (by rfl) ⟨1463423, by rfl⟩ : syracuseStep 7804925 = 2926847) B2926847
theorem B6167279 : Blo 1281959 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B13171481 : Blo 1281959 13171481 := bstep (se 2 (by rfl) ⟨4939305, by rfl⟩ : syracuseStep 13171481 = 9878611) B9878611
theorem B1924649 : Blo 1281959 1924649 := bstep (se 2 (by rfl) ⟨721743, by rfl⟩ : syracuseStep 1924649 = 1443487) B1443487
theorem B5203283 : Blo 1281959 5203283 := bstep (se 1 (by rfl) ⟨3902462, by rfl⟩ : syracuseStep 5203283 = 7804925) B7804925
theorem B6499439 : Blo 1281959 6499439 := bstep (se 1 (by rfl) ⟨4874579, by rfl⟩ : syracuseStep 6499439 = 9749159) B9749159
theorem B1283099 : Blo 1281959 1283099 := bstep (se 1 (by rfl) ⟨962324, by rfl⟩ : syracuseStep 1283099 = 1924649) B1924649
theorem B4109879 : Blo 1281959 4109879 := bstep (se 1 (by rfl) ⟨3082409, by rfl⟩ : syracuseStep 4109879 = 6164819) B6164819
theorem B1924199 : Blo 1281959 1924199 := bstep (se 1 (by rfl) ⟨1443149, by rfl⟩ : syracuseStep 1924199 = 2886299) B2886299
theorem B1924223 : Blo 1281959 1924223 := bstep (se 1 (by rfl) ⟨1443167, by rfl⟩ : syracuseStep 1924223 = 2886335) B2886335
theorem B4111519 : Blo 1281959 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B8780987 : Blo 1281959 8780987 := bstep (se 1 (by rfl) ⟨6585740, by rfl⟩ : syracuseStep 8780987 = 13171481) B13171481
theorem B55501685 : Blo 1281959 55501685 := bstep (se 5 (by rfl) ⟨2601641, by rfl⟩ : syracuseStep 55501685 = 5203283) B5203283
theorem B5482025 : Blo 1281959 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B2739919 : Blo 1281959 2739919 := bstep (se 1 (by rfl) ⟨2054939, by rfl⟩ : syracuseStep 2739919 = 4109879) B4109879
theorem B1282799 : Blo 1281959 1282799 := bstep (se 1 (by rfl) ⟨962099, by rfl⟩ : syracuseStep 1282799 = 1924199) B1924199
theorem B1282815 : Blo 1281959 1282815 := bstep (se 1 (by rfl) ⟨962111, by rfl⟩ : syracuseStep 1282815 = 1924223) B1924223
theorem B5853991 : Blo 1281959 5853991 := bstep (se 1 (by rfl) ⟨4390493, by rfl⟩ : syracuseStep 5853991 = 8780987) B8780987
theorem B4332959 : Blo 1281959 4332959 := bstep (se 1 (by rfl) ⟨3249719, by rfl⟩ : syracuseStep 4332959 = 6499439) B6499439
theorem B3654683 : Blo 1281959 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B2888639 : Blo 1281959 2888639 := bstep (se 1 (by rfl) ⟨2166479, by rfl⟩ : syracuseStep 2888639 = 4332959) B4332959
theorem B37001123 : Blo 1281959 37001123 := bstep (se 1 (by rfl) ⟨27750842, by rfl⟩ : syracuseStep 37001123 = 55501685) B55501685
theorem B7805321 : Blo 1281959 7805321 := bstep (se 2 (by rfl) ⟨2926995, by rfl⟩ : syracuseStep 7805321 = 5853991) B5853991
theorem B3653225 : Blo 1281959 3653225 := bstep (se 2 (by rfl) ⟨1369959, by rfl⟩ : syracuseStep 3653225 = 2739919) B2739919
theorem B1925759 : Blo 1281959 1925759 := bstep (se 1 (by rfl) ⟨1444319, by rfl⟩ : syracuseStep 1925759 = 2888639) B2888639
theorem B24667415 : Blo 1281959 24667415 := bstep (se 1 (by rfl) ⟨18500561, by rfl⟩ : syracuseStep 24667415 = 37001123) B37001123
theorem B5203547 : Blo 1281959 5203547 := bstep (se 1 (by rfl) ⟨3902660, by rfl⟩ : syracuseStep 5203547 = 7805321) B7805321
theorem B2435483 : Blo 1281959 2435483 := bstep (se 1 (by rfl) ⟨1826612, by rfl⟩ : syracuseStep 2435483 = 3653225) B3653225
theorem B2436455 : Blo 1281959 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B1623655 : Blo 1281959 1623655 := bstep (se 1 (by rfl) ⟨1217741, by rfl⟩ : syracuseStep 1623655 = 2435483) B2435483
theorem B1624303 : Blo 1281959 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B16444943 : Blo 1281959 16444943 := bstep (se 1 (by rfl) ⟨12333707, by rfl⟩ : syracuseStep 16444943 = 24667415) B24667415
theorem B3469031 : Blo 1281959 3469031 := bstep (se 1 (by rfl) ⟨2601773, by rfl⟩ : syracuseStep 3469031 = 5203547) B5203547
theorem B1283839 : Blo 1281959 1283839 := bstep (se 1 (by rfl) ⟨962879, by rfl⟩ : syracuseStep 1283839 = 1925759) B1925759
theorem B2164873 : Blo 1281959 2164873 := bstep (se 2 (by rfl) ⟨811827, by rfl⟩ : syracuseStep 2164873 = 1623655) B1623655
theorem B10963295 : Blo 1281959 10963295 := bstep (se 1 (by rfl) ⟨8222471, by rfl⟩ : syracuseStep 10963295 = 16444943) B16444943
theorem B2312687 : Blo 1281959 2312687 := bstep (se 1 (by rfl) ⟨1734515, by rfl⟩ : syracuseStep 2312687 = 3469031) B3469031
theorem B2165737 : Blo 1281959 2165737 := bstep (se 2 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 2165737 = 1624303) B1624303
theorem B7308863 : Blo 1281959 7308863 := bstep (se 1 (by rfl) ⟨5481647, by rfl⟩ : syracuseStep 7308863 = 10963295) B10963295
theorem B1541791 : Blo 1281959 1541791 := bstep (se 1 (by rfl) ⟨1156343, by rfl⟩ : syracuseStep 1541791 = 2312687) B2312687
theorem B2886497 : Blo 1281959 2886497 := bstep (se 2 (by rfl) ⟨1082436, by rfl⟩ : syracuseStep 2886497 = 2164873) B2164873
theorem B2887649 : Blo 1281959 2887649 := bstep (se 2 (by rfl) ⟨1082868, by rfl⟩ : syracuseStep 2887649 = 2165737) B2165737
theorem B4872575 : Blo 1281959 4872575 := bstep (se 1 (by rfl) ⟨3654431, by rfl⟩ : syracuseStep 4872575 = 7308863) B7308863
theorem B1924331 : Blo 1281959 1924331 := bstep (se 1 (by rfl) ⟨1443248, by rfl⟩ : syracuseStep 1924331 = 2886497) B2886497
theorem B2055721 : Blo 1281959 2055721 := bstep (se 2 (by rfl) ⟨770895, by rfl⟩ : syracuseStep 2055721 = 1541791) B1541791
theorem B1925099 : Blo 1281959 1925099 := bstep (se 1 (by rfl) ⟨1443824, by rfl⟩ : syracuseStep 1925099 = 2887649) B2887649
theorem B3248383 : Blo 1281959 3248383 := bstep (se 1 (by rfl) ⟨2436287, by rfl⟩ : syracuseStep 3248383 = 4872575) B4872575
theorem B2740961 : Blo 1281959 2740961 := bstep (se 2 (by rfl) ⟨1027860, by rfl⟩ : syracuseStep 2740961 = 2055721) B2055721
theorem B1282887 : Blo 1281959 1282887 := bstep (se 1 (by rfl) ⟨962165, by rfl⟩ : syracuseStep 1282887 = 1924331) B1924331
theorem B1283399 : Blo 1281959 1283399 := bstep (se 1 (by rfl) ⟨962549, by rfl⟩ : syracuseStep 1283399 = 1925099) B1925099
theorem B1827307 : Blo 1281959 1827307 := bstep (se 1 (by rfl) ⟨1370480, by rfl⟩ : syracuseStep 1827307 = 2740961) B2740961
theorem B4331177 : Blo 1281959 4331177 := bstep (se 2 (by rfl) ⟨1624191, by rfl⟩ : syracuseStep 4331177 = 3248383) B3248383
theorem B2436409 : Blo 1281959 2436409 := bstep (se 2 (by rfl) ⟨913653, by rfl⟩ : syracuseStep 2436409 = 1827307) B1827307
theorem B2887451 : Blo 1281959 2887451 := bstep (se 1 (by rfl) ⟨2165588, by rfl⟩ : syracuseStep 2887451 = 4331177) B4331177
theorem B3248545 : Blo 1281959 3248545 := bstep (se 2 (by rfl) ⟨1218204, by rfl⟩ : syracuseStep 3248545 = 2436409) B2436409
theorem B1924967 : Blo 1281959 1924967 := bstep (se 1 (by rfl) ⟨1443725, by rfl⟩ : syracuseStep 1924967 = 2887451) B2887451
theorem B1283311 : Blo 1281959 1283311 := bstep (se 1 (by rfl) ⟨962483, by rfl⟩ : syracuseStep 1283311 = 1924967) B1924967
theorem B4331393 : Blo 1281959 4331393 := bstep (se 2 (by rfl) ⟨1624272, by rfl⟩ : syracuseStep 4331393 = 3248545) B3248545
theorem B2887595 : Blo 1281959 2887595 := bstep (se 1 (by rfl) ⟨2165696, by rfl⟩ : syracuseStep 2887595 = 4331393) B4331393
theorem B1925063 : Blo 1281959 1925063 := bstep (se 1 (by rfl) ⟨1443797, by rfl⟩ : syracuseStep 1925063 = 2887595) B2887595
theorem B1283375 : Blo 1281959 1283375 := bstep (se 1 (by rfl) ⟨962531, by rfl⟩ : syracuseStep 1283375 = 1925063) B1925063

theorem C0 (j : ℕ) (h1 : 320489 ≤ j) (h2 : j ≤ 320989) : Blo 1281959 (4 * j + 3) := by
  interval_cases j
  · exact B1281959
  · exact B1281963
  · exact B1281967
  · exact B1281971
  · exact B1281975
  · exact B1281979
  · exact B1281983
  · exact B1281987
  · exact B1281991
  · exact B1281995
  · exact B1281999
  · exact B1282003
  · exact B1282007
  · exact B1282011
  · exact B1282015
  · exact B1282019
  · exact B1282023
  · exact B1282027
  · exact B1282031
  · exact B1282035
  · exact B1282039
  · exact B1282043
  · exact B1282047
  · exact B1282051
  · exact B1282055
  · exact B1282059
  · exact B1282063
  · exact B1282067
  · exact B1282071
  · exact B1282075
  · exact B1282079
  · exact B1282083
  · exact B1282087
  · exact B1282091
  · exact B1282095
  · exact B1282099
  · exact B1282103
  · exact B1282107
  · exact B1282111
  · exact B1282115
  · exact B1282119
  · exact B1282123
  · exact B1282127
  · exact B1282131
  · exact B1282135
  · exact B1282139
  · exact B1282143
  · exact B1282147
  · exact B1282151
  · exact B1282155
  · exact B1282159
  · exact B1282163
  · exact B1282167
  · exact B1282171
  · exact B1282175
  · exact B1282179
  · exact B1282183
  · exact B1282187
  · exact B1282191
  · exact B1282195
  · exact B1282199
  · exact B1282203
  · exact B1282207
  · exact B1282211
  · exact B1282215
  · exact B1282219
  · exact B1282223
  · exact B1282227
  · exact B1282231
  · exact B1282235
  · exact B1282239
  · exact B1282243
  · exact B1282247
  · exact B1282251
  · exact B1282255
  · exact B1282259
  · exact B1282263
  · exact B1282267
  · exact B1282271
  · exact B1282275
  · exact B1282279
  · exact B1282283
  · exact B1282287
  · exact B1282291
  · exact B1282295
  · exact B1282299
  · exact B1282303
  · exact B1282307
  · exact B1282311
  · exact B1282315
  · exact B1282319
  · exact B1282323
  · exact B1282327
  · exact B1282331
  · exact B1282335
  · exact B1282339
  · exact B1282343
  · exact B1282347
  · exact B1282351
  · exact B1282355
  · exact B1282359
  · exact B1282363
  · exact B1282367
  · exact B1282371
  · exact B1282375
  · exact B1282379
  · exact B1282383
  · exact B1282387
  · exact B1282391
  · exact B1282395
  · exact B1282399
  · exact B1282403
  · exact B1282407
  · exact B1282411
  · exact B1282415
  · exact B1282419
  · exact B1282423
  · exact B1282427
  · exact B1282431
  · exact B1282435
  · exact B1282439
  · exact B1282443
  · exact B1282447
  · exact B1282451
  · exact B1282455
  · exact B1282459
  · exact B1282463
  · exact B1282467
  · exact B1282471
  · exact B1282475
  · exact B1282479
  · exact B1282483
  · exact B1282487
  · exact B1282491
  · exact B1282495
  · exact B1282499
  · exact B1282503
  · exact B1282507
  · exact B1282511
  · exact B1282515
  · exact B1282519
  · exact B1282523
  · exact B1282527
  · exact B1282531
  · exact B1282535
  · exact B1282539
  · exact B1282543
  · exact B1282547
  · exact B1282551
  · exact B1282555
  · exact B1282559
  · exact B1282563
  · exact B1282567
  · exact B1282571
  · exact B1282575
  · exact B1282579
  · exact B1282583
  · exact B1282587
  · exact B1282591
  · exact B1282595
  · exact B1282599
  · exact B1282603
  · exact B1282607
  · exact B1282611
  · exact B1282615
  · exact B1282619
  · exact B1282623
  · exact B1282627
  · exact B1282631
  · exact B1282635
  · exact B1282639
  · exact B1282643
  · exact B1282647
  · exact B1282651
  · exact B1282655
  · exact B1282659
  · exact B1282663
  · exact B1282667
  · exact B1282671
  · exact B1282675
  · exact B1282679
  · exact B1282683
  · exact B1282687
  · exact B1282691
  · exact B1282695
  · exact B1282699
  · exact B1282703
  · exact B1282707
  · exact B1282711
  · exact B1282715
  · exact B1282719
  · exact B1282723
  · exact B1282727
  · exact B1282731
  · exact B1282735
  · exact B1282739
  · exact B1282743
  · exact B1282747
  · exact B1282751
  · exact B1282755
  · exact B1282759
  · exact B1282763
  · exact B1282767
  · exact B1282771
  · exact B1282775
  · exact B1282779
  · exact B1282783
  · exact B1282787
  · exact B1282791
  · exact B1282795
  · exact B1282799
  · exact B1282803
  · exact B1282807
  · exact B1282811
  · exact B1282815
  · exact B1282819
  · exact B1282823
  · exact B1282827
  · exact B1282831
  · exact B1282835
  · exact B1282839
  · exact B1282843
  · exact B1282847
  · exact B1282851
  · exact B1282855
  · exact B1282859
  · exact B1282863
  · exact B1282867
  · exact B1282871
  · exact B1282875
  · exact B1282879
  · exact B1282883
  · exact B1282887
  · exact B1282891
  · exact B1282895
  · exact B1282899
  · exact B1282903
  · exact B1282907
  · exact B1282911
  · exact B1282915
  · exact B1282919
  · exact B1282923
  · exact B1282927
  · exact B1282931
  · exact B1282935
  · exact B1282939
  · exact B1282943
  · exact B1282947
  · exact B1282951
  · exact B1282955
  · exact B1282959
  · exact B1282963
  · exact B1282967
  · exact B1282971
  · exact B1282975
  · exact B1282979
  · exact B1282983
  · exact B1282987
  · exact B1282991
  · exact B1282995
  · exact B1282999
  · exact B1283003
  · exact B1283007
  · exact B1283011
  · exact B1283015
  · exact B1283019
  · exact B1283023
  · exact B1283027
  · exact B1283031
  · exact B1283035
  · exact B1283039
  · exact B1283043
  · exact B1283047
  · exact B1283051
  · exact B1283055
  · exact B1283059
  · exact B1283063
  · exact B1283067
  · exact B1283071
  · exact B1283075
  · exact B1283079
  · exact B1283083
  · exact B1283087
  · exact B1283091
  · exact B1283095
  · exact B1283099
  · exact B1283103
  · exact B1283107
  · exact B1283111
  · exact B1283115
  · exact B1283119
  · exact B1283123
  · exact B1283127
  · exact B1283131
  · exact B1283135
  · exact B1283139
  · exact B1283143
  · exact B1283147
  · exact B1283151
  · exact B1283155
  · exact B1283159
  · exact B1283163
  · exact B1283167
  · exact B1283171
  · exact B1283175
  · exact B1283179
  · exact B1283183
  · exact B1283187
  · exact B1283191
  · exact B1283195
  · exact B1283199
  · exact B1283203
  · exact B1283207
  · exact B1283211
  · exact B1283215
  · exact B1283219
  · exact B1283223
  · exact B1283227
  · exact B1283231
  · exact B1283235
  · exact B1283239
  · exact B1283243
  · exact B1283247
  · exact B1283251
  · exact B1283255
  · exact B1283259
  · exact B1283263
  · exact B1283267
  · exact B1283271
  · exact B1283275
  · exact B1283279
  · exact B1283283
  · exact B1283287
  · exact B1283291
  · exact B1283295
  · exact B1283299
  · exact B1283303
  · exact B1283307
  · exact B1283311
  · exact B1283315
  · exact B1283319
  · exact B1283323
  · exact B1283327
  · exact B1283331
  · exact B1283335
  · exact B1283339
  · exact B1283343
  · exact B1283347
  · exact B1283351
  · exact B1283355
  · exact B1283359
  · exact B1283363
  · exact B1283367
  · exact B1283371
  · exact B1283375
  · exact B1283379
  · exact B1283383
  · exact B1283387
  · exact B1283391
  · exact B1283395
  · exact B1283399
  · exact B1283403
  · exact B1283407
  · exact B1283411
  · exact B1283415
  · exact B1283419
  · exact B1283423
  · exact B1283427
  · exact B1283431
  · exact B1283435
  · exact B1283439
  · exact B1283443
  · exact B1283447
  · exact B1283451
  · exact B1283455
  · exact B1283459
  · exact B1283463
  · exact B1283467
  · exact B1283471
  · exact B1283475
  · exact B1283479
  · exact B1283483
  · exact B1283487
  · exact B1283491
  · exact B1283495
  · exact B1283499
  · exact B1283503
  · exact B1283507
  · exact B1283511
  · exact B1283515
  · exact B1283519
  · exact B1283523
  · exact B1283527
  · exact B1283531
  · exact B1283535
  · exact B1283539
  · exact B1283543
  · exact B1283547
  · exact B1283551
  · exact B1283555
  · exact B1283559
  · exact B1283563
  · exact B1283567
  · exact B1283571
  · exact B1283575
  · exact B1283579
  · exact B1283583
  · exact B1283587
  · exact B1283591
  · exact B1283595
  · exact B1283599
  · exact B1283603
  · exact B1283607
  · exact B1283611
  · exact B1283615
  · exact B1283619
  · exact B1283623
  · exact B1283627
  · exact B1283631
  · exact B1283635
  · exact B1283639
  · exact B1283643
  · exact B1283647
  · exact B1283651
  · exact B1283655
  · exact B1283659
  · exact B1283663
  · exact B1283667
  · exact B1283671
  · exact B1283675
  · exact B1283679
  · exact B1283683
  · exact B1283687
  · exact B1283691
  · exact B1283695
  · exact B1283699
  · exact B1283703
  · exact B1283707
  · exact B1283711
  · exact B1283715
  · exact B1283719
  · exact B1283723
  · exact B1283727
  · exact B1283731
  · exact B1283735
  · exact B1283739
  · exact B1283743
  · exact B1283747
  · exact B1283751
  · exact B1283755
  · exact B1283759
  · exact B1283763
  · exact B1283767
  · exact B1283771
  · exact B1283775
  · exact B1283779
  · exact B1283783
  · exact B1283787
  · exact B1283791
  · exact B1283795
  · exact B1283799
  · exact B1283803
  · exact B1283807
  · exact B1283811
  · exact B1283815
  · exact B1283819
  · exact B1283823
  · exact B1283827
  · exact B1283831
  · exact B1283835
  · exact B1283839
  · exact B1283843
  · exact B1283847
  · exact B1283851
  · exact B1283855
  · exact B1283859
  · exact B1283863
  · exact B1283867
  · exact B1283871
  · exact B1283875
  · exact B1283879
  · exact B1283883
  · exact B1283887
  · exact B1283891
  · exact B1283895
  · exact B1283899
  · exact B1283903
  · exact B1283907
  · exact B1283911
  · exact B1283915
  · exact B1283919
  · exact B1283923
  · exact B1283927
  · exact B1283931
  · exact B1283935
  · exact B1283939
  · exact B1283943
  · exact B1283947
  · exact B1283951
  · exact B1283955
  · exact B1283959

theorem solution (m : ℕ) (hlo : 1281959 ≤ m) (hhi : m ≤ 1283959) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 320489 ≤ j := by omega
    have hj2 : j ≤ 320989 := by omega
    have hb : Blo 1281959 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
