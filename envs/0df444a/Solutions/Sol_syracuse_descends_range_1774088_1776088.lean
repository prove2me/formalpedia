-- Prove2me | solution 1 for syracuse_descends_range_1774088_1776088
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:42:48.584631+00:00
-- url     : https://prove2.me/submissions/1ea710a4-20ee-4888-856e-8d1280b78dd3

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


theorem B2023445 : Blo 1774088 2023445 := bbase (se 6 (by rfl) ⟨47424, by rfl⟩ : syracuseStep 2023445 = 94849) (by norm_num)
theorem B2662421 : Blo 1774088 2662421 := bbase (se 6 (by rfl) ⟨62400, by rfl⟩ : syracuseStep 2662421 = 124801) (by norm_num)
theorem B2662445 : Blo 1774088 2662445 := bbase (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) (by norm_num)
theorem B2662469 : Blo 1774088 2662469 := bbase (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) (by norm_num)
theorem B5988437 : Blo 1774088 5988437 := bbase (se 8 (by rfl) ⟨35088, by rfl⟩ : syracuseStep 5988437 = 70177) (by norm_num)
theorem B2662493 : Blo 1774088 2662493 := bbase (se 3 (by rfl) ⟨499217, by rfl⟩ : syracuseStep 2662493 = 998435) (by norm_num)
theorem B2842733 : Blo 1774088 2842733 := bbase (se 3 (by rfl) ⟨533012, by rfl⟩ : syracuseStep 2842733 = 1066025) (by norm_num)
theorem B2662517 : Blo 1774088 2662517 := bbase (se 5 (by rfl) ⟨124805, by rfl⟩ : syracuseStep 2662517 = 249611) (by norm_num)
theorem B2662541 : Blo 1774088 2662541 := bbase (se 3 (by rfl) ⟨499226, by rfl⟩ : syracuseStep 2662541 = 998453) (by norm_num)
theorem B2662565 : Blo 1774088 2662565 := bbase (se 4 (by rfl) ⟨249615, by rfl⟩ : syracuseStep 2662565 = 499231) (by norm_num)
theorem B2662589 : Blo 1774088 2662589 := bbase (se 3 (by rfl) ⟨499235, by rfl⟩ : syracuseStep 2662589 = 998471) (by norm_num)
theorem B2662613 : Blo 1774088 2662613 := bbase (se 7 (by rfl) ⟨31202, by rfl⟩ : syracuseStep 2662613 = 62405) (by norm_num)
theorem B2842861 : Blo 1774088 2842861 := bbase (se 3 (by rfl) ⟨533036, by rfl⟩ : syracuseStep 2842861 = 1066073) (by norm_num)
theorem B2662637 : Blo 1774088 2662637 := bbase (se 3 (by rfl) ⟨499244, by rfl⟩ : syracuseStep 2662637 = 998489) (by norm_num)
theorem B2662661 : Blo 1774088 2662661 := bbase (se 4 (by rfl) ⟨249624, by rfl⟩ : syracuseStep 2662661 = 499249) (by norm_num)
theorem B2662685 : Blo 1774088 2662685 := bbase (se 3 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 2662685 = 998507) (by norm_num)
theorem B6832421 : Blo 1774088 6832421 := bbase (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) (by norm_num)
theorem B2662709 : Blo 1774088 2662709 := bbase (se 5 (by rfl) ⟨124814, by rfl⟩ : syracuseStep 2662709 = 249629) (by norm_num)
theorem B8986949 : Blo 1774088 8986949 := bbase (se 4 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 8986949 = 1685053) (by norm_num)
theorem B2662733 : Blo 1774088 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B2662757 : Blo 1774088 2662757 := bbase (se 4 (by rfl) ⟨249633, by rfl⟩ : syracuseStep 2662757 = 499267) (by norm_num)
theorem B2662781 : Blo 1774088 2662781 := bbase (se 3 (by rfl) ⟨499271, by rfl⟩ : syracuseStep 2662781 = 998543) (by norm_num)
theorem B2662805 : Blo 1774088 2662805 := bbase (se 6 (by rfl) ⟨62409, by rfl⟩ : syracuseStep 2662805 = 124819) (by norm_num)
theorem B2662829 : Blo 1774088 2662829 := bbase (se 3 (by rfl) ⟨499280, by rfl⟩ : syracuseStep 2662829 = 998561) (by norm_num)
theorem B2662853 : Blo 1774088 2662853 := bbase (se 4 (by rfl) ⟨249642, by rfl⟩ : syracuseStep 2662853 = 499285) (by norm_num)
theorem B2662877 : Blo 1774088 2662877 := bbase (se 3 (by rfl) ⟨499289, by rfl⟩ : syracuseStep 2662877 = 998579) (by norm_num)
theorem B2662901 : Blo 1774088 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B7586293 : Blo 1774088 7586293 := bbase (se 5 (by rfl) ⟨355607, by rfl⟩ : syracuseStep 7586293 = 711215) (by norm_num)
theorem B5988869 : Blo 1774088 5988869 := bbase (se 4 (by rfl) ⟨561456, by rfl⟩ : syracuseStep 5988869 = 1122913) (by norm_num)
theorem B2662925 : Blo 1774088 2662925 := bbase (se 3 (by rfl) ⟨499298, by rfl⟩ : syracuseStep 2662925 = 998597) (by norm_num)
theorem B2662949 : Blo 1774088 2662949 := bbase (se 4 (by rfl) ⟨249651, by rfl⟩ : syracuseStep 2662949 = 499303) (by norm_num)
theorem B2662973 : Blo 1774088 2662973 := bbase (se 3 (by rfl) ⟨499307, by rfl⟩ : syracuseStep 2662973 = 998615) (by norm_num)
theorem B2662997 : Blo 1774088 2662997 := bbase (se 8 (by rfl) ⟨15603, by rfl⟩ : syracuseStep 2662997 = 31207) (by norm_num)
theorem B2024029 : Blo 1774088 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B2663021 : Blo 1774088 2663021 := bbase (se 3 (by rfl) ⟨499316, by rfl⟩ : syracuseStep 2663021 = 998633) (by norm_num)
theorem B2663045 : Blo 1774088 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B2663069 : Blo 1774088 2663069 := bbase (se 3 (by rfl) ⟨499325, by rfl⟩ : syracuseStep 2663069 = 998651) (by norm_num)
theorem B2663093 : Blo 1774088 2663093 := bbase (se 5 (by rfl) ⟨124832, by rfl⟩ : syracuseStep 2663093 = 249665) (by norm_num)
theorem B2663117 : Blo 1774088 2663117 := bbase (se 3 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 2663117 = 998669) (by norm_num)
theorem B5055205 : Blo 1774088 5055205 := bbase (se 4 (by rfl) ⟨473925, by rfl⟩ : syracuseStep 5055205 = 947851) (by norm_num)
theorem B2663141 : Blo 1774088 2663141 := bbase (se 4 (by rfl) ⟨249669, by rfl⟩ : syracuseStep 2663141 = 499339) (by norm_num)
theorem B2663165 : Blo 1774088 2663165 := bbase (se 3 (by rfl) ⟨499343, by rfl⟩ : syracuseStep 2663165 = 998687) (by norm_num)
theorem B2663189 : Blo 1774088 2663189 := bbase (se 6 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 2663189 = 124837) (by norm_num)
theorem B2245421 : Blo 1774088 2245421 := bbase (se 3 (by rfl) ⟨421016, by rfl⟩ : syracuseStep 2245421 = 842033) (by norm_num)
theorem B2663213 : Blo 1774088 2663213 := bbase (se 3 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 2663213 = 998705) (by norm_num)
theorem B2663237 : Blo 1774088 2663237 := bbase (se 4 (by rfl) ⟨249678, by rfl⟩ : syracuseStep 2663237 = 499357) (by norm_num)
theorem B2663261 : Blo 1774088 2663261 := bbase (se 3 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 2663261 = 998723) (by norm_num)
theorem B2245477 : Blo 1774088 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B6742885 : Blo 1774088 6742885 := bbase (se 4 (by rfl) ⟨632145, by rfl⟩ : syracuseStep 6742885 = 1264291) (by norm_num)
theorem B2663285 : Blo 1774088 2663285 := bbase (se 5 (by rfl) ⟨124841, by rfl⟩ : syracuseStep 2663285 = 249683) (by norm_num)
theorem B5055365 : Blo 1774088 5055365 := bbase (se 4 (by rfl) ⟨473940, by rfl⟩ : syracuseStep 5055365 = 947881) (by norm_num)
theorem B2597765 : Blo 1774088 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B2663309 : Blo 1774088 2663309 := bbase (se 3 (by rfl) ⟨499370, by rfl⟩ : syracuseStep 2663309 = 998741) (by norm_num)
theorem B2737037 : Blo 1774088 2737037 := bbase (se 3 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 2737037 = 1026389) (by norm_num)
theorem B2024357 : Blo 1774088 2024357 := bbase (se 4 (by rfl) ⟨189783, by rfl⟩ : syracuseStep 2024357 = 379567) (by norm_num)
theorem B2663333 : Blo 1774088 2663333 := bbase (se 4 (by rfl) ⟨249687, by rfl⟩ : syracuseStep 2663333 = 499375) (by norm_num)
theorem B5989301 : Blo 1774088 5989301 := bbase (se 5 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 5989301 = 561497) (by norm_num)
theorem B2663357 : Blo 1774088 2663357 := bbase (se 3 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 2663357 = 998759) (by norm_num)
theorem B2245573 : Blo 1774088 2245573 := bbase (se 4 (by rfl) ⟨210522, by rfl⟩ : syracuseStep 2245573 = 421045) (by norm_num)
theorem B2663381 : Blo 1774088 2663381 := bbase (se 7 (by rfl) ⟨31211, by rfl⟩ : syracuseStep 2663381 = 62423) (by norm_num)
theorem B2663405 : Blo 1774088 2663405 := bbase (se 3 (by rfl) ⟨499388, by rfl⟩ : syracuseStep 2663405 = 998777) (by norm_num)
theorem B2663429 : Blo 1774088 2663429 := bbase (se 4 (by rfl) ⟨249696, by rfl⟩ : syracuseStep 2663429 = 499393) (by norm_num)
theorem B2663453 : Blo 1774088 2663453 := bbase (se 3 (by rfl) ⟨499397, by rfl⟩ : syracuseStep 2663453 = 998795) (by norm_num)
theorem B2663477 : Blo 1774088 2663477 := bbase (se 5 (by rfl) ⟨124850, by rfl⟩ : syracuseStep 2663477 = 249701) (by norm_num)
theorem B2663501 : Blo 1774088 2663501 := bbase (se 3 (by rfl) ⟨499406, by rfl⟩ : syracuseStep 2663501 = 998813) (by norm_num)
theorem B2663525 : Blo 1774088 2663525 := bbase (se 4 (by rfl) ⟨249705, by rfl⟩ : syracuseStep 2663525 = 499411) (by norm_num)
theorem B2245745 : Blo 1774088 2245745 := bbase (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) (by norm_num)
theorem B5055605 : Blo 1774088 5055605 := bbase (se 5 (by rfl) ⟨236981, by rfl⟩ : syracuseStep 5055605 = 473963) (by norm_num)
theorem B2663549 : Blo 1774088 2663549 := bbase (se 3 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 2663549 = 998831) (by norm_num)
theorem B2663573 : Blo 1774088 2663573 := bbase (se 6 (by rfl) ⟨62427, by rfl⟩ : syracuseStep 2663573 = 124855) (by norm_num)
theorem B6743189 : Blo 1774088 6743189 := bbase (se 6 (by rfl) ⟨158043, by rfl⟩ : syracuseStep 6743189 = 316087) (by norm_num)
theorem B2245801 : Blo 1774088 2245801 := bbase (se 2 (by rfl) ⟨842175, by rfl⟩ : syracuseStep 2245801 = 1684351) (by norm_num)
theorem B2663597 : Blo 1774088 2663597 := bbase (se 3 (by rfl) ⟨499424, by rfl⟩ : syracuseStep 2663597 = 998849) (by norm_num)
theorem B3368117 : Blo 1774088 3368117 := bbase (se 5 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 3368117 = 315761) (by norm_num)
theorem B2663621 : Blo 1774088 2663621 := bbase (se 4 (by rfl) ⟨249714, by rfl⟩ : syracuseStep 2663621 = 499429) (by norm_num)
theorem B2663645 : Blo 1774088 2663645 := bbase (se 3 (by rfl) ⟨499433, by rfl⟩ : syracuseStep 2663645 = 998867) (by norm_num)
theorem B2663669 : Blo 1774088 2663669 := bbase (se 5 (by rfl) ⟨124859, by rfl⟩ : syracuseStep 2663669 = 249719) (by norm_num)
theorem B2245897 : Blo 1774088 2245897 := bbase (se 2 (by rfl) ⟨842211, by rfl⟩ : syracuseStep 2245897 = 1684423) (by norm_num)
theorem B2663693 : Blo 1774088 2663693 := bbase (se 3 (by rfl) ⟨499442, by rfl⟩ : syracuseStep 2663693 = 998885) (by norm_num)
theorem B2663717 : Blo 1774088 2663717 := bbase (se 4 (by rfl) ⟨249723, by rfl⟩ : syracuseStep 2663717 = 499447) (by norm_num)
theorem B5055797 : Blo 1774088 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B2663741 : Blo 1774088 2663741 := bbase (se 3 (by rfl) ⟨499451, by rfl⟩ : syracuseStep 2663741 = 998903) (by norm_num)
theorem B2663765 : Blo 1774088 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B5989733 : Blo 1774088 5989733 := bbase (se 4 (by rfl) ⟨561537, by rfl⟩ : syracuseStep 5989733 = 1123075) (by norm_num)
theorem B2663789 : Blo 1774088 2663789 := bbase (se 3 (by rfl) ⟨499460, by rfl⟩ : syracuseStep 2663789 = 998921) (by norm_num)
theorem B5686645 : Blo 1774088 5686645 := bbase (se 5 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 5686645 = 533123) (by norm_num)
theorem B2663813 : Blo 1774088 2663813 := bbase (se 4 (by rfl) ⟨249732, by rfl⟩ : syracuseStep 2663813 = 499465) (by norm_num)
theorem B2663837 : Blo 1774088 2663837 := bbase (se 3 (by rfl) ⟨499469, by rfl⟩ : syracuseStep 2663837 = 998939) (by norm_num)
theorem B4105637 : Blo 1774088 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2246069 : Blo 1774088 2246069 := bbase (se 5 (by rfl) ⟨105284, by rfl⟩ : syracuseStep 2246069 = 210569) (by norm_num)
theorem B2663861 : Blo 1774088 2663861 := bbase (se 5 (by rfl) ⟨124868, by rfl⟩ : syracuseStep 2663861 = 249737) (by norm_num)
theorem B2663885 : Blo 1774088 2663885 := bbase (se 3 (by rfl) ⟨499478, by rfl⟩ : syracuseStep 2663885 = 998957) (by norm_num)
theorem B3368405 : Blo 1774088 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B5400037 : Blo 1774088 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B2663909 : Blo 1774088 2663909 := bbase (se 4 (by rfl) ⟨249741, by rfl⟩ : syracuseStep 2663909 = 499483) (by norm_num)
theorem B2246125 : Blo 1774088 2246125 := bbase (se 3 (by rfl) ⟨421148, by rfl⟩ : syracuseStep 2246125 = 842297) (by norm_num)
theorem B4490741 : Blo 1774088 4490741 := bbase (se 5 (by rfl) ⟨210503, by rfl⟩ : syracuseStep 4490741 = 421007) (by norm_num)
theorem B2663933 : Blo 1774088 2663933 := bbase (se 3 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 2663933 = 998975) (by norm_num)
theorem B2663957 : Blo 1774088 2663957 := bbase (se 6 (by rfl) ⟨62436, by rfl⟩ : syracuseStep 2663957 = 124873) (by norm_num)
theorem B2663981 : Blo 1774088 2663981 := bbase (se 3 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 2663981 = 998993) (by norm_num)
theorem B2664005 : Blo 1774088 2664005 := bbase (se 4 (by rfl) ⟨249750, by rfl⟩ : syracuseStep 2664005 = 499501) (by norm_num)
theorem B2246221 : Blo 1774088 2246221 := bbase (se 3 (by rfl) ⟨421166, by rfl⟩ : syracuseStep 2246221 = 842333) (by norm_num)
theorem B8988245 : Blo 1774088 8988245 := bbase (se 8 (by rfl) ⟨52665, by rfl⟩ : syracuseStep 8988245 = 105331) (by norm_num)
theorem B2844245 : Blo 1774088 2844245 := bbase (se 8 (by rfl) ⟨16665, by rfl⟩ : syracuseStep 2844245 = 33331) (by norm_num)
theorem B2664029 : Blo 1774088 2664029 := bbase (se 3 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 2664029 = 999011) (by norm_num)
theorem B3368557 : Blo 1774088 3368557 := bbase (se 3 (by rfl) ⟨631604, by rfl⟩ : syracuseStep 3368557 = 1263209) (by norm_num)
theorem B2664053 : Blo 1774088 2664053 := bbase (se 5 (by rfl) ⟨124877, by rfl⟩ : syracuseStep 2664053 = 249755) (by norm_num)
theorem B3597949 : Blo 1774088 3597949 := bbase (se 3 (by rfl) ⟨674615, by rfl⟩ : syracuseStep 3597949 = 1349231) (by norm_num)
theorem B2664077 : Blo 1774088 2664077 := bbase (se 3 (by rfl) ⟨499514, by rfl⟩ : syracuseStep 2664077 = 999029) (by norm_num)
theorem B3417749 : Blo 1774088 3417749 := bbase (se 6 (by rfl) ⟨80103, by rfl⟩ : syracuseStep 3417749 = 160207) (by norm_num)
theorem B2664101 : Blo 1774088 2664101 := bbase (se 4 (by rfl) ⟨249759, by rfl⟩ : syracuseStep 2664101 = 499519) (by norm_num)
theorem B2664125 : Blo 1774088 2664125 := bbase (se 3 (by rfl) ⟨499523, by rfl⟩ : syracuseStep 2664125 = 999047) (by norm_num)
theorem B2246393 : Blo 1774088 2246393 := bbase (se 2 (by rfl) ⟨842397, by rfl⟩ : syracuseStep 2246393 = 1684795) (by norm_num)
theorem B5990165 : Blo 1774088 5990165 := bbase (se 6 (by rfl) ⟨140394, by rfl⟩ : syracuseStep 5990165 = 280789) (by norm_num)
theorem B2246449 : Blo 1774088 2246449 := bbase (se 2 (by rfl) ⟨842418, by rfl⟩ : syracuseStep 2246449 = 1684837) (by norm_num)
theorem B4491085 : Blo 1774088 4491085 := bbase (se 3 (by rfl) ⟨842078, by rfl⟩ : syracuseStep 4491085 = 1684157) (by norm_num)
theorem B2246545 : Blo 1774088 2246545 := bbase (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) (by norm_num)
theorem B3368861 : Blo 1774088 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2131877 : Blo 1774088 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B4491197 : Blo 1774088 4491197 := bbase (se 3 (by rfl) ⟨842099, by rfl⟩ : syracuseStep 4491197 = 1684199) (by norm_num)
theorem B8529893 : Blo 1774088 8529893 := bbase (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) (by norm_num)
theorem B4556837 : Blo 1774088 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B2246717 : Blo 1774088 2246717 := bbase (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) (by norm_num)
theorem B2246773 : Blo 1774088 2246773 := bbase (se 5 (by rfl) ⟨105317, by rfl⟩ : syracuseStep 2246773 = 210635) (by norm_num)
theorem B4491389 : Blo 1774088 4491389 := bbase (se 3 (by rfl) ⟨842135, by rfl⟩ : syracuseStep 4491389 = 1684271) (by norm_num)
theorem B3991733 : Blo 1774088 3991733 := bbase (se 5 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 3991733 = 374225) (by norm_num)
theorem B3893429 : Blo 1774088 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B3197117 : Blo 1774088 3197117 := bbase (se 3 (by rfl) ⟨599459, by rfl⟩ : syracuseStep 3197117 = 1198919) (by norm_num)
theorem B5990597 : Blo 1774088 5990597 := bbase (se 4 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 5990597 = 1123237) (by norm_num)
theorem B2246869 : Blo 1774088 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B2132185 : Blo 1774088 2132185 := bbase (se 2 (by rfl) ⟨799569, by rfl⟩ : syracuseStep 2132185 = 1599139) (by norm_num)
theorem B3991805 : Blo 1774088 3991805 := bbase (se 3 (by rfl) ⟨748463, by rfl⟩ : syracuseStep 3991805 = 1496927) (by norm_num)
theorem B5056789 : Blo 1774088 5056789 := bbase (se 6 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 5056789 = 237037) (by norm_num)
theorem B2132281 : Blo 1774088 2132281 := bbase (se 2 (by rfl) ⟨799605, by rfl⟩ : syracuseStep 2132281 = 1599211) (by norm_num)
theorem B3991877 : Blo 1774088 3991877 := bbase (se 4 (by rfl) ⟨374238, by rfl⟩ : syracuseStep 3991877 = 748477) (by norm_num)
theorem B2247041 : Blo 1774088 2247041 := bbase (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) (by norm_num)
theorem B3991949 : Blo 1774088 3991949 := bbase (se 3 (by rfl) ⟨748490, by rfl⟩ : syracuseStep 3991949 = 1496981) (by norm_num)
theorem B2247097 : Blo 1774088 2247097 := bbase (se 2 (by rfl) ⟨842661, by rfl⟩ : syracuseStep 2247097 = 1685323) (by norm_num)
theorem B1894861 : Blo 1774088 1894861 := bbase (se 3 (by rfl) ⟨355286, by rfl⟩ : syracuseStep 1894861 = 710573) (by norm_num)
theorem B3992021 : Blo 1774088 3992021 := bbase (se 7 (by rfl) ⟨46781, by rfl⟩ : syracuseStep 3992021 = 93563) (by norm_num)
theorem B4491733 : Blo 1774088 4491733 := bbase (se 7 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 4491733 = 105275) (by norm_num)
theorem B1894933 : Blo 1774088 1894933 := bbase (se 6 (by rfl) ⟨44412, by rfl⟩ : syracuseStep 1894933 = 88825) (by norm_num)
theorem B2247193 : Blo 1774088 2247193 := bbase (se 2 (by rfl) ⟨842697, by rfl⟩ : syracuseStep 2247193 = 1685395) (by norm_num)
theorem B3992093 : Blo 1774088 3992093 := bbase (se 3 (by rfl) ⟨748517, by rfl⟩ : syracuseStep 3992093 = 1497035) (by norm_num)
theorem B2697781 : Blo 1774088 2697781 := bbase (se 5 (by rfl) ⟨126458, by rfl⟩ : syracuseStep 2697781 = 252917) (by norm_num)
theorem B4491845 : Blo 1774088 4491845 := bbase (se 4 (by rfl) ⟨421110, by rfl⟩ : syracuseStep 4491845 = 842221) (by norm_num)
theorem B2132569 : Blo 1774088 2132569 := bbase (se 2 (by rfl) ⟨799713, by rfl⟩ : syracuseStep 2132569 = 1599427) (by norm_num)
theorem B3992165 : Blo 1774088 3992165 := bbase (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) (by norm_num)
theorem B5991029 : Blo 1774088 5991029 := bbase (se 5 (by rfl) ⟨280829, by rfl⟩ : syracuseStep 5991029 = 561659) (by norm_num)
theorem B3369613 : Blo 1774088 3369613 := bbase (se 3 (by rfl) ⟨631802, by rfl⟩ : syracuseStep 3369613 = 1263605) (by norm_num)
theorem B3992237 : Blo 1774088 3992237 := bbase (se 3 (by rfl) ⟨748544, by rfl⟩ : syracuseStep 3992237 = 1497089) (by norm_num)
theorem B2247365 : Blo 1774088 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B1895113 : Blo 1774088 1895113 := bbase (se 2 (by rfl) ⟨710667, by rfl⟩ : syracuseStep 1895113 = 1421335) (by norm_num)
theorem B3992309 : Blo 1774088 3992309 := bbase (se 5 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 3992309 = 374279) (by norm_num)
theorem B2247421 : Blo 1774088 2247421 := bbase (se 3 (by rfl) ⟨421391, by rfl⟩ : syracuseStep 2247421 = 842783) (by norm_num)
theorem B4492037 : Blo 1774088 4492037 := bbase (se 4 (by rfl) ⟨421128, by rfl⟩ : syracuseStep 4492037 = 842257) (by norm_num)
theorem B4262669 : Blo 1774088 4262669 := bbase (se 3 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 4262669 = 1598501) (by norm_num)
theorem B2132761 : Blo 1774088 2132761 := bbase (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) (by norm_num)
theorem B3369757 : Blo 1774088 3369757 := bbase (se 3 (by rfl) ⟨631829, by rfl⟩ : syracuseStep 3369757 = 1263659) (by norm_num)
theorem B3992381 : Blo 1774088 3992381 := bbase (se 3 (by rfl) ⟨748571, by rfl⟩ : syracuseStep 3992381 = 1497143) (by norm_num)
theorem B2247517 : Blo 1774088 2247517 := bbase (se 3 (by rfl) ⟨421409, by rfl⟩ : syracuseStep 2247517 = 842819) (by norm_num)
theorem B8989541 : Blo 1774088 8989541 := bbase (se 4 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 8989541 = 1685539) (by norm_num)
theorem B3992453 : Blo 1774088 3992453 := bbase (se 4 (by rfl) ⟨374292, by rfl⟩ : syracuseStep 3992453 = 748585) (by norm_num)
theorem B3369917 : Blo 1774088 3369917 := bbase (se 3 (by rfl) ⟨631859, by rfl⟩ : syracuseStep 3369917 = 1263719) (by norm_num)
theorem B3992525 : Blo 1774088 3992525 := bbase (se 3 (by rfl) ⟨748598, by rfl⟩ : syracuseStep 3992525 = 1497197) (by norm_num)
theorem B2698205 : Blo 1774088 2698205 := bbase (se 3 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 2698205 = 1011827) (by norm_num)
theorem B7195637 : Blo 1774088 7195637 := bbase (se 5 (by rfl) ⟨337295, by rfl⟩ : syracuseStep 7195637 = 674591) (by norm_num)
theorem B2247689 : Blo 1774088 2247689 := bbase (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) (by norm_num)
theorem B3992597 : Blo 1774088 3992597 := bbase (se 6 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 3992597 = 187153) (by norm_num)
theorem B5991461 : Blo 1774088 5991461 := bbase (se 4 (by rfl) ⟨561699, by rfl⟩ : syracuseStep 5991461 = 1123399) (by norm_num)
theorem B2247745 : Blo 1774088 2247745 := bbase (se 2 (by rfl) ⟨842904, by rfl⟩ : syracuseStep 2247745 = 1685809) (by norm_num)
theorem B3370061 : Blo 1774088 3370061 := bbase (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) (by norm_num)
theorem B7195733 : Blo 1774088 7195733 := bbase (se 8 (by rfl) ⟨42162, by rfl⟩ : syracuseStep 7195733 = 84325) (by norm_num)
theorem B4263005 : Blo 1774088 4263005 := bbase (se 3 (by rfl) ⟨799313, by rfl⟩ : syracuseStep 4263005 = 1598627) (by norm_num)
theorem B3992669 : Blo 1774088 3992669 := bbase (se 3 (by rfl) ⟨748625, by rfl⟩ : syracuseStep 3992669 = 1497251) (by norm_num)
theorem B4492381 : Blo 1774088 4492381 := bbase (se 3 (by rfl) ⟨842321, by rfl⟩ : syracuseStep 4492381 = 1684643) (by norm_num)
theorem B1895557 : Blo 1774088 1895557 := bbase (se 4 (by rfl) ⟨177708, by rfl⟩ : syracuseStep 1895557 = 355417) (by norm_num)
theorem B2247841 : Blo 1774088 2247841 := bbase (se 2 (by rfl) ⟨842940, by rfl⟩ : syracuseStep 2247841 = 1685881) (by norm_num)
theorem B3992741 : Blo 1774088 3992741 := bbase (se 4 (by rfl) ⟨374319, by rfl⟩ : syracuseStep 3992741 = 748639) (by norm_num)
theorem B4263101 : Blo 1774088 4263101 := bbase (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) (by norm_num)
theorem B4492493 : Blo 1774088 4492493 := bbase (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) (by norm_num)
theorem B3992813 : Blo 1774088 3992813 := bbase (se 3 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 3992813 = 1497305) (by norm_num)
theorem B4050157 : Blo 1774088 4050157 := bbase (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) (by norm_num)
theorem B12791029 : Blo 1774088 12791029 := bbase (se 5 (by rfl) ⟨599579, by rfl⟩ : syracuseStep 12791029 = 1199159) (by norm_num)
theorem B15166709 : Blo 1774088 15166709 := bbase (se 5 (by rfl) ⟨710939, by rfl⟩ : syracuseStep 15166709 = 1421879) (by norm_num)
theorem B6073589 : Blo 1774088 6073589 := bbase (se 5 (by rfl) ⟨284699, by rfl⟩ : syracuseStep 6073589 = 569399) (by norm_num)
theorem B1895681 : Blo 1774088 1895681 := bbase (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) (by norm_num)
theorem B8981765 : Blo 1774088 8981765 := bbase (se 4 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 8981765 = 1684081) (by norm_num)
theorem B8531237 : Blo 1774088 8531237 := bbase (se 4 (by rfl) ⟨799803, by rfl⟩ : syracuseStep 8531237 = 1599607) (by norm_num)
theorem B2526509 : Blo 1774088 2526509 := bbase (se 3 (by rfl) ⟨473720, by rfl⟩ : syracuseStep 2526509 = 947441) (by norm_num)
theorem B3992885 : Blo 1774088 3992885 := bbase (se 5 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 3992885 = 374333) (by norm_num)
theorem B3599677 : Blo 1774088 3599677 := bbase (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) (by norm_num)
theorem B3370349 : Blo 1774088 3370349 := bbase (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) (by norm_num)
theorem B4263293 : Blo 1774088 4263293 := bbase (se 3 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 4263293 = 1598735) (by norm_num)
theorem B2526589 : Blo 1774088 2526589 := bbase (se 3 (by rfl) ⟨473735, by rfl⟩ : syracuseStep 2526589 = 947471) (by norm_num)
theorem B3992957 : Blo 1774088 3992957 := bbase (se 3 (by rfl) ⟨748679, by rfl⟩ : syracuseStep 3992957 = 1497359) (by norm_num)
theorem B3599741 : Blo 1774088 3599741 := bbase (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) (by norm_num)
theorem B4492685 : Blo 1774088 4492685 := bbase (se 3 (by rfl) ⟨842378, by rfl⟩ : syracuseStep 4492685 = 1684757) (by norm_num)
theorem B3993029 : Blo 1774088 3993029 := bbase (se 4 (by rfl) ⟨374346, by rfl⟩ : syracuseStep 3993029 = 748693) (by norm_num)
theorem B5991893 : Blo 1774088 5991893 := bbase (se 7 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 5991893 = 140435) (by norm_num)
theorem B2526709 : Blo 1774088 2526709 := bbase (se 5 (by rfl) ⟨118439, by rfl⟩ : syracuseStep 2526709 = 236879) (by norm_num)
theorem B1895933 : Blo 1774088 1895933 := bbase (se 3 (by rfl) ⟨355487, by rfl⟩ : syracuseStep 1895933 = 710975) (by norm_num)
theorem B3370501 : Blo 1774088 3370501 := bbase (se 4 (by rfl) ⟨315984, by rfl⟩ : syracuseStep 3370501 = 631969) (by norm_num)
theorem B3993101 : Blo 1774088 3993101 := bbase (se 3 (by rfl) ⟨748706, by rfl⟩ : syracuseStep 3993101 = 1497413) (by norm_num)
theorem B7581221 : Blo 1774088 7581221 := bbase (se 4 (by rfl) ⟨710739, by rfl⟩ : syracuseStep 7581221 = 1421479) (by norm_num)
theorem B2526805 : Blo 1774088 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B3993173 : Blo 1774088 3993173 := bbase (se 8 (by rfl) ⟨23397, by rfl⟩ : syracuseStep 3993173 = 46795) (by norm_num)
theorem B10112597 : Blo 1774088 10112597 := bbase (se 8 (by rfl) ⟨59253, by rfl⟩ : syracuseStep 10112597 = 118507) (by norm_num)
theorem B3198565 : Blo 1774088 3198565 := bbase (se 4 (by rfl) ⟨299865, by rfl⟩ : syracuseStep 3198565 = 599731) (by norm_num)
theorem B6737525 : Blo 1774088 6737525 := bbase (se 5 (by rfl) ⟨315821, by rfl⟩ : syracuseStep 6737525 = 631643) (by norm_num)
theorem B2133641 : Blo 1774088 2133641 := bbase (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) (by norm_num)
theorem B3993245 : Blo 1774088 3993245 := bbase (se 3 (by rfl) ⟨748733, by rfl⟩ : syracuseStep 3993245 = 1497467) (by norm_num)
theorem B2993861 : Blo 1774088 2993861 := bbase (se 4 (by rfl) ⟨280674, by rfl⟩ : syracuseStep 2993861 = 561349) (by norm_num)
theorem B10104533 : Blo 1774088 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B45493973 : Blo 1774088 45493973 := bbase (se 7 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 45493973 = 1066265) (by norm_num)
theorem B3993317 : Blo 1774088 3993317 := bbase (se 4 (by rfl) ⟨374373, by rfl⟩ : syracuseStep 3993317 = 748747) (by norm_num)
theorem B4493029 : Blo 1774088 4493029 := bbase (se 4 (by rfl) ⟨421221, by rfl⟩ : syracuseStep 4493029 = 842443) (by norm_num)
theorem B3993389 : Blo 1774088 3993389 := bbase (se 3 (by rfl) ⟨748760, by rfl⟩ : syracuseStep 3993389 = 1497521) (by norm_num)
theorem B3370805 : Blo 1774088 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B2993989 : Blo 1774088 2993989 := bbase (se 4 (by rfl) ⟨280686, by rfl⟩ : syracuseStep 2993989 = 561373) (by norm_num)
theorem B7581509 : Blo 1774088 7581509 := bbase (se 4 (by rfl) ⟨710766, by rfl⟩ : syracuseStep 7581509 = 1421533) (by norm_num)
theorem B4493141 : Blo 1774088 4493141 := bbase (se 9 (by rfl) ⟨13163, by rfl⟩ : syracuseStep 4493141 = 26327) (by norm_num)
theorem B3993461 : Blo 1774088 3993461 := bbase (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) (by norm_num)
theorem B5992325 : Blo 1774088 5992325 := bbase (se 4 (by rfl) ⟨561780, by rfl⟩ : syracuseStep 5992325 = 1123561) (by norm_num)
theorem B6737813 : Blo 1774088 6737813 := bbase (se 6 (by rfl) ⟨157917, by rfl⟩ : syracuseStep 6737813 = 315835) (by norm_num)
theorem B2994077 : Blo 1774088 2994077 := bbase (se 3 (by rfl) ⟨561389, by rfl⟩ : syracuseStep 2994077 = 1122779) (by norm_num)
theorem B1896377 : Blo 1774088 1896377 := bbase (se 2 (by rfl) ⟨711141, by rfl⟩ : syracuseStep 1896377 = 1422283) (by norm_num)
theorem B3993533 : Blo 1774088 3993533 := bbase (se 3 (by rfl) ⟨748787, by rfl⟩ : syracuseStep 3993533 = 1497575) (by norm_num)
theorem B3993605 : Blo 1774088 3993605 := bbase (se 4 (by rfl) ⟨374400, by rfl⟩ : syracuseStep 3993605 = 748801) (by norm_num)
theorem B4493333 : Blo 1774088 4493333 := bbase (se 6 (by rfl) ⟨105312, by rfl⟩ : syracuseStep 4493333 = 210625) (by norm_num)
theorem B2994205 : Blo 1774088 2994205 := bbase (se 3 (by rfl) ⟨561413, by rfl⟩ : syracuseStep 2994205 = 1122827) (by norm_num)
theorem B2527301 : Blo 1774088 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B3993677 : Blo 1774088 3993677 := bbase (se 3 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 3993677 = 1497629) (by norm_num)
theorem B2191469 : Blo 1774088 2191469 := bbase (se 3 (by rfl) ⟨410900, by rfl⟩ : syracuseStep 2191469 = 821801) (by norm_num)
theorem B2994293 : Blo 1774088 2994293 := bbase (se 5 (by rfl) ⟨140357, by rfl⟩ : syracuseStep 2994293 = 280715) (by norm_num)
theorem B8990837 : Blo 1774088 8990837 := bbase (se 5 (by rfl) ⟨421445, by rfl⟩ : syracuseStep 8990837 = 842891) (by norm_num)
theorem B3993749 : Blo 1774088 3993749 := bbase (se 6 (by rfl) ⟨93603, by rfl⟩ : syracuseStep 3993749 = 187207) (by norm_num)
theorem B1896625 : Blo 1774088 1896625 := bbase (se 2 (by rfl) ⟨711234, by rfl⟩ : syracuseStep 1896625 = 1422469) (by norm_num)
theorem B5689541 : Blo 1774088 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B3993821 : Blo 1774088 3993821 := bbase (se 3 (by rfl) ⟨748841, by rfl⟩ : syracuseStep 3993821 = 1497683) (by norm_num)
theorem B2994421 : Blo 1774088 2994421 := bbase (se 5 (by rfl) ⟨140363, by rfl⟩ : syracuseStep 2994421 = 280727) (by norm_num)
theorem B13480181 : Blo 1774088 13480181 := bbase (se 5 (by rfl) ⟨631883, by rfl⟩ : syracuseStep 13480181 = 1263767) (by norm_num)
theorem B3993893 : Blo 1774088 3993893 := bbase (se 4 (by rfl) ⟨374427, by rfl⟩ : syracuseStep 3993893 = 748855) (by norm_num)
theorem B5992757 : Blo 1774088 5992757 := bbase (se 5 (by rfl) ⟨280910, by rfl⟩ : syracuseStep 5992757 = 561821) (by norm_num)
theorem B2994509 : Blo 1774088 2994509 := bbase (se 3 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 2994509 = 1122941) (by norm_num)
theorem B2773333 : Blo 1774088 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B3993965 : Blo 1774088 3993965 := bbase (se 3 (by rfl) ⟨748868, by rfl⟩ : syracuseStep 3993965 = 1497737) (by norm_num)
theorem B4493677 : Blo 1774088 4493677 := bbase (se 3 (by rfl) ⟨842564, by rfl⟩ : syracuseStep 4493677 = 1685129) (by norm_num)
theorem B1798573 : Blo 1774088 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B3994037 : Blo 1774088 3994037 := bbase (se 5 (by rfl) ⟨187220, by rfl⟩ : syracuseStep 3994037 = 374441) (by norm_num)
theorem B2994637 : Blo 1774088 2994637 := bbase (se 3 (by rfl) ⟨561494, by rfl⟩ : syracuseStep 2994637 = 1122989) (by norm_num)
theorem B4493789 : Blo 1774088 4493789 := bbase (se 3 (by rfl) ⟨842585, by rfl⟩ : syracuseStep 4493789 = 1685171) (by norm_num)
theorem B4264445 : Blo 1774088 4264445 := bbase (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) (by norm_num)
theorem B3994109 : Blo 1774088 3994109 := bbase (se 3 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 3994109 = 1497791) (by norm_num)
theorem B8983061 : Blo 1774088 8983061 := bbase (se 6 (by rfl) ⟨210540, by rfl⟩ : syracuseStep 8983061 = 421081) (by norm_num)
theorem B2994725 : Blo 1774088 2994725 := bbase (se 4 (by rfl) ⟨280755, by rfl⟩ : syracuseStep 2994725 = 561511) (by norm_num)
theorem B3371557 : Blo 1774088 3371557 := bbase (se 4 (by rfl) ⟨316083, by rfl⟩ : syracuseStep 3371557 = 632167) (by norm_num)
theorem B7582261 : Blo 1774088 7582261 := bbase (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) (by norm_num)
theorem B3994181 : Blo 1774088 3994181 := bbase (se 4 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 3994181 = 748909) (by norm_num)
theorem B17052245 : Blo 1774088 17052245 := bbase (se 8 (by rfl) ⟨99915, by rfl⟩ : syracuseStep 17052245 = 199831) (by norm_num)
theorem B2527853 : Blo 1774088 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B6075013 : Blo 1774088 6075013 := bbase (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) (by norm_num)
theorem B3994253 : Blo 1774088 3994253 := bbase (se 3 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 3994253 = 1497845) (by norm_num)
theorem B13472405 : Blo 1774088 13472405 := bbase (se 6 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 13472405 = 631519) (by norm_num)
theorem B4493981 : Blo 1774088 4493981 := bbase (se 3 (by rfl) ⟨842621, by rfl⟩ : syracuseStep 4493981 = 1685243) (by norm_num)
theorem B2994853 : Blo 1774088 2994853 := bbase (se 4 (by rfl) ⟨280767, by rfl⟩ : syracuseStep 2994853 = 561535) (by norm_num)
theorem B12800693 : Blo 1774088 12800693 := bbase (se 5 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 12800693 = 1200065) (by norm_num)
theorem B3371701 : Blo 1774088 3371701 := bbase (se 5 (by rfl) ⟨158048, by rfl⟩ : syracuseStep 3371701 = 316097) (by norm_num)
theorem B1798853 : Blo 1774088 1798853 := bbase (se 4 (by rfl) ⟨168642, by rfl⟩ : syracuseStep 1798853 = 337285) (by norm_num)
theorem B3789517 : Blo 1774088 3789517 := bbase (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) (by norm_num)
theorem B3994325 : Blo 1774088 3994325 := bbase (se 7 (by rfl) ⟨46808, by rfl⟩ : syracuseStep 3994325 = 93617) (by norm_num)
theorem B5993189 : Blo 1774088 5993189 := bbase (se 4 (by rfl) ⟨561861, by rfl⟩ : syracuseStep 5993189 = 1123723) (by norm_num)
theorem B10113781 : Blo 1774088 10113781 := bbase (se 5 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 10113781 = 948167) (by norm_num)
theorem B2994941 : Blo 1774088 2994941 := bbase (se 3 (by rfl) ⟨561551, by rfl⟩ : syracuseStep 2994941 = 1123103) (by norm_num)
theorem B3994397 : Blo 1774088 3994397 := bbase (se 3 (by rfl) ⟨748949, by rfl⟩ : syracuseStep 3994397 = 1497899) (by norm_num)
theorem B3789661 : Blo 1774088 3789661 := bbase (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) (by norm_num)
theorem B3994469 : Blo 1774088 3994469 := bbase (se 4 (by rfl) ⟨374481, by rfl⟩ : syracuseStep 3994469 = 748963) (by norm_num)
theorem B2995069 : Blo 1774088 2995069 := bbase (se 3 (by rfl) ⟨561575, by rfl⟩ : syracuseStep 2995069 = 1123151) (by norm_num)
theorem B3240853 : Blo 1774088 3240853 := bbase (se 6 (by rfl) ⟨75957, by rfl⟩ : syracuseStep 3240853 = 151915) (by norm_num)
theorem B3994541 : Blo 1774088 3994541 := bbase (se 3 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 3994541 = 1497953) (by norm_num)
theorem B6157237 : Blo 1774088 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B3199949 : Blo 1774088 3199949 := bbase (se 3 (by rfl) ⟨599990, by rfl⟩ : syracuseStep 3199949 = 1199981) (by norm_num)
theorem B2995157 : Blo 1774088 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B3994613 : Blo 1774088 3994613 := bbase (se 5 (by rfl) ⟨187247, by rfl⟩ : syracuseStep 3994613 = 374495) (by norm_num)
theorem B4494325 : Blo 1774088 4494325 := bbase (se 5 (by rfl) ⟨210671, by rfl⟩ : syracuseStep 4494325 = 421343) (by norm_num)
theorem B6738997 : Blo 1774088 6738997 := bbase (se 5 (by rfl) ⟨315890, by rfl⟩ : syracuseStep 6738997 = 631781) (by norm_num)
theorem B3994685 : Blo 1774088 3994685 := bbase (se 3 (by rfl) ⟨749003, by rfl⟩ : syracuseStep 3994685 = 1498007) (by norm_num)
theorem B1995853 : Blo 1774088 1995853 := bbase (se 3 (by rfl) ⟨374222, by rfl⟩ : syracuseStep 1995853 = 748445) (by norm_num)
theorem B2995285 : Blo 1774088 2995285 := bbase (se 8 (by rfl) ⟨17550, by rfl⟩ : syracuseStep 2995285 = 35101) (by norm_num)
theorem B4494437 : Blo 1774088 4494437 := bbase (se 4 (by rfl) ⟨421353, by rfl⟩ : syracuseStep 4494437 = 842707) (by norm_num)
theorem B1995889 : Blo 1774088 1995889 := bbase (se 2 (by rfl) ⟨748458, by rfl⟩ : syracuseStep 1995889 = 1496917) (by norm_num)
theorem B3994757 : Blo 1774088 3994757 := bbase (se 4 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 3994757 = 749017) (by norm_num)
theorem B1995925 : Blo 1774088 1995925 := bbase (se 6 (by rfl) ⟨46779, by rfl⟩ : syracuseStep 1995925 = 93559) (by norm_num)
theorem B5993621 : Blo 1774088 5993621 := bbase (se 6 (by rfl) ⟨140475, by rfl⟩ : syracuseStep 5993621 = 280951) (by norm_num)
theorem B2995373 : Blo 1774088 2995373 := bbase (se 3 (by rfl) ⟨561632, by rfl⟩ : syracuseStep 2995373 = 1123265) (by norm_num)
theorem B1823921 : Blo 1774088 1823921 := bbase (se 2 (by rfl) ⟨683970, by rfl⟩ : syracuseStep 1823921 = 1367941) (by norm_num)
theorem B1922225 : Blo 1774088 1922225 := bbase (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) (by norm_num)
theorem B1995961 : Blo 1774088 1995961 := bbase (se 2 (by rfl) ⟨748485, by rfl⟩ : syracuseStep 1995961 = 1496971) (by norm_num)
theorem B3994829 : Blo 1774088 3994829 := bbase (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) (by norm_num)
theorem B3790037 : Blo 1774088 3790037 := bbase (se 7 (by rfl) ⟨44414, by rfl⟩ : syracuseStep 3790037 = 88829) (by norm_num)
theorem B1995997 : Blo 1774088 1995997 := bbase (se 3 (by rfl) ⟨374249, by rfl⟩ : syracuseStep 1995997 = 748499) (by norm_num)
theorem B1996033 : Blo 1774088 1996033 := bbase (se 2 (by rfl) ⟨748512, by rfl⟩ : syracuseStep 1996033 = 1497025) (by norm_num)
theorem B7582997 : Blo 1774088 7582997 := bbase (se 6 (by rfl) ⟨177726, by rfl⟩ : syracuseStep 7582997 = 355453) (by norm_num)
theorem B3994901 : Blo 1774088 3994901 := bbase (se 6 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 3994901 = 187261) (by norm_num)
theorem B1996069 : Blo 1774088 1996069 := bbase (se 4 (by rfl) ⟨187131, by rfl⟩ : syracuseStep 1996069 = 374263) (by norm_num)
theorem B4494629 : Blo 1774088 4494629 := bbase (se 4 (by rfl) ⟨421371, by rfl⟩ : syracuseStep 4494629 = 842743) (by norm_num)
theorem B2995501 : Blo 1774088 2995501 := bbase (se 3 (by rfl) ⟨561656, by rfl⟩ : syracuseStep 2995501 = 1123313) (by norm_num)
theorem B1996105 : Blo 1774088 1996105 := bbase (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) (by norm_num)
theorem B3994973 : Blo 1774088 3994973 := bbase (se 3 (by rfl) ⟨749057, by rfl⟩ : syracuseStep 3994973 = 1498115) (by norm_num)
theorem B2528605 : Blo 1774088 2528605 := bbase (se 3 (by rfl) ⟨474113, by rfl⟩ : syracuseStep 2528605 = 948227) (by norm_num)
theorem B6739301 : Blo 1774088 6739301 := bbase (se 4 (by rfl) ⟨631809, by rfl⟩ : syracuseStep 6739301 = 1263619) (by norm_num)
theorem B1996141 : Blo 1774088 1996141 := bbase (se 3 (by rfl) ⟨374276, by rfl⟩ : syracuseStep 1996141 = 748553) (by norm_num)
theorem B2995589 : Blo 1774088 2995589 := bbase (se 4 (by rfl) ⟨280836, by rfl⟩ : syracuseStep 2995589 = 561673) (by norm_num)
theorem B1996177 : Blo 1774088 1996177 := bbase (se 2 (by rfl) ⟨748566, by rfl⟩ : syracuseStep 1996177 = 1497133) (by norm_num)
theorem B3995045 : Blo 1774088 3995045 := bbase (se 4 (by rfl) ⟨374535, by rfl⟩ : syracuseStep 3995045 = 749071) (by norm_num)
theorem B1996213 : Blo 1774088 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B1996249 : Blo 1774088 1996249 := bbase (se 2 (by rfl) ⟨748593, by rfl⟩ : syracuseStep 1996249 = 1497187) (by norm_num)
theorem B3995117 : Blo 1774088 3995117 := bbase (se 3 (by rfl) ⟨749084, by rfl⟩ : syracuseStep 3995117 = 1498169) (by norm_num)
theorem B1996285 : Blo 1774088 1996285 := bbase (se 3 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 1996285 = 748607) (by norm_num)
theorem B2995717 : Blo 1774088 2995717 := bbase (se 4 (by rfl) ⟨280848, by rfl⟩ : syracuseStep 2995717 = 561697) (by norm_num)
theorem B1996321 : Blo 1774088 1996321 := bbase (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) (by norm_num)
theorem B4552237 : Blo 1774088 4552237 := bbase (se 3 (by rfl) ⟨853544, by rfl⟩ : syracuseStep 4552237 = 1707089) (by norm_num)
theorem B3995189 : Blo 1774088 3995189 := bbase (se 5 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 3995189 = 374549) (by norm_num)
theorem B2397757 : Blo 1774088 2397757 := bbase (se 3 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 2397757 = 899159) (by norm_num)
theorem B1996357 : Blo 1774088 1996357 := bbase (se 4 (by rfl) ⟨187158, by rfl⟩ : syracuseStep 1996357 = 374317) (by norm_num)
theorem B3790405 : Blo 1774088 3790405 := bbase (se 4 (by rfl) ⟨355350, by rfl⟩ : syracuseStep 3790405 = 710701) (by norm_num)
theorem B1799753 : Blo 1774088 1799753 := bbase (se 2 (by rfl) ⟨674907, by rfl⟩ : syracuseStep 1799753 = 1349815) (by norm_num)
theorem B5994053 : Blo 1774088 5994053 := bbase (se 4 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 5994053 = 1123885) (by norm_num)
theorem B2995805 : Blo 1774088 2995805 := bbase (se 3 (by rfl) ⟨561713, by rfl⟩ : syracuseStep 2995805 = 1123427) (by norm_num)
theorem B1799777 : Blo 1774088 1799777 := bbase (se 2 (by rfl) ⟨674916, by rfl⟩ : syracuseStep 1799777 = 1349833) (by norm_num)
theorem B1996393 : Blo 1774088 1996393 := bbase (se 2 (by rfl) ⟨748647, by rfl⟩ : syracuseStep 1996393 = 1497295) (by norm_num)
theorem B3995261 : Blo 1774088 3995261 := bbase (se 3 (by rfl) ⟨749111, by rfl⟩ : syracuseStep 3995261 = 1498223) (by norm_num)
theorem B4494973 : Blo 1774088 4494973 := bbase (se 3 (by rfl) ⟨842807, by rfl⟩ : syracuseStep 4494973 = 1685615) (by norm_num)
theorem B1996429 : Blo 1774088 1996429 := bbase (se 3 (by rfl) ⟨374330, by rfl⟩ : syracuseStep 1996429 = 748661) (by norm_num)
theorem B1996465 : Blo 1774088 1996465 := bbase (se 2 (by rfl) ⟨748674, by rfl⟩ : syracuseStep 1996465 = 1497349) (by norm_num)
theorem B8099509 : Blo 1774088 8099509 := bbase (se 5 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 8099509 = 759329) (by norm_num)
theorem B3995333 : Blo 1774088 3995333 := bbase (se 4 (by rfl) ⟨374562, by rfl⟩ : syracuseStep 3995333 = 749125) (by norm_num)
theorem B2307793 : Blo 1774088 2307793 := bbase (se 2 (by rfl) ⟨865422, by rfl⟩ : syracuseStep 2307793 = 1730845) (by norm_num)
theorem B1996501 : Blo 1774088 1996501 := bbase (se 7 (by rfl) ⟨23396, by rfl⟩ : syracuseStep 1996501 = 46793) (by norm_num)
theorem B2995933 : Blo 1774088 2995933 := bbase (se 3 (by rfl) ⟨561737, by rfl⟩ : syracuseStep 2995933 = 1123475) (by norm_num)
theorem B4495085 : Blo 1774088 4495085 := bbase (se 3 (by rfl) ⟨842828, by rfl⟩ : syracuseStep 4495085 = 1685657) (by norm_num)
theorem B8763125 : Blo 1774088 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B1996537 : Blo 1774088 1996537 := bbase (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) (by norm_num)
theorem B3995405 : Blo 1774088 3995405 := bbase (se 3 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 3995405 = 1498277) (by norm_num)
theorem B1996573 : Blo 1774088 1996573 := bbase (se 3 (by rfl) ⟨374357, by rfl⟩ : syracuseStep 1996573 = 748715) (by norm_num)
theorem B8984357 : Blo 1774088 8984357 := bbase (se 4 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 8984357 = 1684567) (by norm_num)
theorem B2996021 : Blo 1774088 2996021 := bbase (se 5 (by rfl) ⟨140438, by rfl⟩ : syracuseStep 2996021 = 280877) (by norm_num)
theorem B1996609 : Blo 1774088 1996609 := bbase (se 2 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 1996609 = 1497457) (by norm_num)
theorem B2398037 : Blo 1774088 2398037 := bbase (se 9 (by rfl) ⟨7025, by rfl⟩ : syracuseStep 2398037 = 14051) (by norm_num)
theorem B3995477 : Blo 1774088 3995477 := bbase (se 9 (by rfl) ⟨11705, by rfl⟩ : syracuseStep 3995477 = 23411) (by norm_num)
theorem B1996645 : Blo 1774088 1996645 := bbase (se 4 (by rfl) ⟨187185, by rfl⟩ : syracuseStep 1996645 = 374371) (by norm_num)
theorem B2160517 : Blo 1774088 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B1996681 : Blo 1774088 1996681 := bbase (se 2 (by rfl) ⟨748755, by rfl⟩ : syracuseStep 1996681 = 1497511) (by norm_num)
theorem B1800085 : Blo 1774088 1800085 := bbase (se 6 (by rfl) ⟨42189, by rfl⟩ : syracuseStep 1800085 = 84379) (by norm_num)
theorem B3995549 : Blo 1774088 3995549 := bbase (se 3 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 3995549 = 1498331) (by norm_num)
theorem B1800101 : Blo 1774088 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B1996717 : Blo 1774088 1996717 := bbase (se 3 (by rfl) ⟨374384, by rfl⟩ : syracuseStep 1996717 = 748769) (by norm_num)
theorem B4495277 : Blo 1774088 4495277 := bbase (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) (by norm_num)
theorem B2996149 : Blo 1774088 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B1996753 : Blo 1774088 1996753 := bbase (se 2 (by rfl) ⟨748782, by rfl⟩ : syracuseStep 1996753 = 1497565) (by norm_num)
theorem B6395861 : Blo 1774088 6395861 := bbase (se 7 (by rfl) ⟨74951, by rfl⟩ : syracuseStep 6395861 = 149903) (by norm_num)
theorem B3995621 : Blo 1774088 3995621 := bbase (se 4 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 3995621 = 749179) (by norm_num)
theorem B1996789 : Blo 1774088 1996789 := bbase (se 5 (by rfl) ⟨93599, by rfl⟩ : syracuseStep 1996789 = 187199) (by norm_num)
theorem B2996237 : Blo 1774088 2996237 := bbase (se 3 (by rfl) ⟨561794, by rfl⟩ : syracuseStep 2996237 = 1123589) (by norm_num)
theorem B1996825 : Blo 1774088 1996825 := bbase (se 2 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 1996825 = 1497619) (by norm_num)
theorem B3995693 : Blo 1774088 3995693 := bbase (se 3 (by rfl) ⟨749192, by rfl⟩ : syracuseStep 3995693 = 1498385) (by norm_num)
theorem B1996861 : Blo 1774088 1996861 := bbase (se 3 (by rfl) ⟨374411, by rfl⟩ : syracuseStep 1996861 = 748823) (by norm_num)
theorem B1996897 : Blo 1774088 1996897 := bbase (se 2 (by rfl) ⟨748836, by rfl⟩ : syracuseStep 1996897 = 1497673) (by norm_num)
theorem B3995765 : Blo 1774088 3995765 := bbase (se 5 (by rfl) ⟨187301, by rfl⟩ : syracuseStep 3995765 = 374603) (by norm_num)
theorem B1996933 : Blo 1774088 1996933 := bbase (se 4 (by rfl) ⟨187212, by rfl⟩ : syracuseStep 1996933 = 374425) (by norm_num)
theorem B2996365 : Blo 1774088 2996365 := bbase (se 3 (by rfl) ⟨561818, by rfl⟩ : syracuseStep 2996365 = 1123637) (by norm_num)
theorem B1996969 : Blo 1774088 1996969 := bbase (se 2 (by rfl) ⟨748863, by rfl⟩ : syracuseStep 1996969 = 1497727) (by norm_num)
theorem B3995837 : Blo 1774088 3995837 := bbase (se 3 (by rfl) ⟨749219, by rfl⟩ : syracuseStep 3995837 = 1498439) (by norm_num)
theorem B1997005 : Blo 1774088 1997005 := bbase (se 3 (by rfl) ⟨374438, by rfl⟩ : syracuseStep 1997005 = 748877) (by norm_num)
theorem B2996453 : Blo 1774088 2996453 := bbase (se 4 (by rfl) ⟨280917, by rfl⟩ : syracuseStep 2996453 = 561835) (by norm_num)
theorem B1997041 : Blo 1774088 1997041 := bbase (se 2 (by rfl) ⟨748890, by rfl⟩ : syracuseStep 1997041 = 1497781) (by norm_num)
theorem B3995909 : Blo 1774088 3995909 := bbase (se 4 (by rfl) ⟨374616, by rfl⟩ : syracuseStep 3995909 = 749233) (by norm_num)
theorem B4495621 : Blo 1774088 4495621 := bbase (se 4 (by rfl) ⟨421464, by rfl⟩ : syracuseStep 4495621 = 842929) (by norm_num)
theorem B1997077 : Blo 1774088 1997077 := bbase (se 6 (by rfl) ⟨46806, by rfl⟩ : syracuseStep 1997077 = 93613) (by norm_num)
theorem B4798757 : Blo 1774088 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B1997113 : Blo 1774088 1997113 := bbase (se 2 (by rfl) ⟨748917, by rfl⟩ : syracuseStep 1997113 = 1497835) (by norm_num)
theorem B3995981 : Blo 1774088 3995981 := bbase (se 3 (by rfl) ⟨749246, by rfl⟩ : syracuseStep 3995981 = 1498493) (by norm_num)
theorem B1997149 : Blo 1774088 1997149 := bbase (se 3 (by rfl) ⟨374465, by rfl⟩ : syracuseStep 1997149 = 748931) (by norm_num)
theorem B2996581 : Blo 1774088 2996581 := bbase (se 4 (by rfl) ⟨280929, by rfl⟩ : syracuseStep 2996581 = 561859) (by norm_num)
theorem B1997185 : Blo 1774088 1997185 := bbase (se 2 (by rfl) ⟨748944, by rfl⟩ : syracuseStep 1997185 = 1497889) (by norm_num)
theorem B2161037 : Blo 1774088 2161037 := bbase (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) (by norm_num)
theorem B7682453 : Blo 1774088 7682453 := bbase (se 6 (by rfl) ⟨180057, by rfl⟩ : syracuseStep 7682453 = 360115) (by norm_num)
theorem B3996053 : Blo 1774088 3996053 := bbase (se 6 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 3996053 = 187315) (by norm_num)
theorem B2398621 : Blo 1774088 2398621 := bbase (se 3 (by rfl) ⟨449741, by rfl⟩ : syracuseStep 2398621 = 899483) (by norm_num)
theorem B5683621 : Blo 1774088 5683621 := bbase (se 4 (by rfl) ⟨532839, by rfl⟩ : syracuseStep 5683621 = 1065679) (by norm_num)
theorem B1997221 : Blo 1774088 1997221 := bbase (se 4 (by rfl) ⟨187239, by rfl⟩ : syracuseStep 1997221 = 374479) (by norm_num)
theorem B2996669 : Blo 1774088 2996669 := bbase (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) (by norm_num)
theorem B1997257 : Blo 1774088 1997257 := bbase (se 2 (by rfl) ⟨748971, by rfl⟩ : syracuseStep 1997257 = 1497943) (by norm_num)
theorem B4266445 : Blo 1774088 4266445 := bbase (se 3 (by rfl) ⟨799958, by rfl⟩ : syracuseStep 4266445 = 1599917) (by norm_num)
theorem B3996125 : Blo 1774088 3996125 := bbase (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) (by norm_num)
theorem B1997293 : Blo 1774088 1997293 := bbase (se 3 (by rfl) ⟨374492, by rfl⟩ : syracuseStep 1997293 = 748985) (by norm_num)
theorem B1997329 : Blo 1774088 1997329 := bbase (se 2 (by rfl) ⟨748998, by rfl⟩ : syracuseStep 1997329 = 1497997) (by norm_num)
theorem B3996197 : Blo 1774088 3996197 := bbase (se 4 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 3996197 = 749287) (by norm_num)
theorem B4266541 : Blo 1774088 4266541 := bbase (se 3 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 4266541 = 1599953) (by norm_num)
theorem B1997365 : Blo 1774088 1997365 := bbase (se 5 (by rfl) ⟨93626, by rfl⟩ : syracuseStep 1997365 = 187253) (by norm_num)
theorem B2996797 : Blo 1774088 2996797 := bbase (se 3 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 2996797 = 1123799) (by norm_num)
theorem B2398789 : Blo 1774088 2398789 := bbase (se 4 (by rfl) ⟨224886, by rfl⟩ : syracuseStep 2398789 = 449773) (by norm_num)
theorem B1997401 : Blo 1774088 1997401 := bbase (se 2 (by rfl) ⟨749025, by rfl⟩ : syracuseStep 1997401 = 1498051) (by norm_num)
theorem B1997437 : Blo 1774088 1997437 := bbase (se 3 (by rfl) ⟨374519, by rfl⟩ : syracuseStep 1997437 = 749039) (by norm_num)
theorem B2161285 : Blo 1774088 2161285 := bbase (se 4 (by rfl) ⟨202620, by rfl⟩ : syracuseStep 2161285 = 405241) (by norm_num)
theorem B7199365 : Blo 1774088 7199365 := bbase (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) (by norm_num)
theorem B2996885 : Blo 1774088 2996885 := bbase (se 6 (by rfl) ⟨70239, by rfl⟩ : syracuseStep 2996885 = 140479) (by norm_num)
theorem B1997473 : Blo 1774088 1997473 := bbase (se 2 (by rfl) ⟨749052, by rfl⟩ : syracuseStep 1997473 = 1498105) (by norm_num)
theorem B1997509 : Blo 1774088 1997509 := bbase (se 4 (by rfl) ⟨187266, by rfl⟩ : syracuseStep 1997509 = 374533) (by norm_num)
theorem B4799189 : Blo 1774088 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B1997545 : Blo 1774088 1997545 := bbase (se 2 (by rfl) ⟨749079, by rfl⟩ : syracuseStep 1997545 = 1498159) (by norm_num)
theorem B1997581 : Blo 1774088 1997581 := bbase (se 3 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 1997581 = 749093) (by norm_num)
theorem B2997013 : Blo 1774088 2997013 := bbase (se 6 (by rfl) ⟨70242, by rfl⟩ : syracuseStep 2997013 = 140485) (by norm_num)
theorem B2661149 : Blo 1774088 2661149 := bbase (se 3 (by rfl) ⟨498965, by rfl⟩ : syracuseStep 2661149 = 997931) (by norm_num)
theorem B2161441 : Blo 1774088 2161441 := bbase (se 2 (by rfl) ⟨810540, by rfl⟩ : syracuseStep 2161441 = 1621081) (by norm_num)
theorem B1997617 : Blo 1774088 1997617 := bbase (se 2 (by rfl) ⟨749106, by rfl⟩ : syracuseStep 1997617 = 1498213) (by norm_num)
theorem B2661173 : Blo 1774088 2661173 := bbase (se 5 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 2661173 = 249485) (by norm_num)
theorem B2661197 : Blo 1774088 2661197 := bbase (se 3 (by rfl) ⟨498974, by rfl⟩ : syracuseStep 2661197 = 997949) (by norm_num)
theorem B1997653 : Blo 1774088 1997653 := bbase (se 9 (by rfl) ⟨5852, by rfl⟩ : syracuseStep 1997653 = 11705) (by norm_num)
theorem B11377493 : Blo 1774088 11377493 := bbase (se 9 (by rfl) ⟨33332, by rfl⟩ : syracuseStep 11377493 = 66665) (by norm_num)
theorem B2661221 : Blo 1774088 2661221 := bbase (se 4 (by rfl) ⟨249489, by rfl⟩ : syracuseStep 2661221 = 498979) (by norm_num)
theorem B2997101 : Blo 1774088 2997101 := bbase (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) (by norm_num)
theorem B1997689 : Blo 1774088 1997689 := bbase (se 2 (by rfl) ⟨749133, by rfl⟩ : syracuseStep 1997689 = 1498267) (by norm_num)
theorem B2661245 : Blo 1774088 2661245 := bbase (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) (by norm_num)
theorem B2661269 : Blo 1774088 2661269 := bbase (se 6 (by rfl) ⟨62373, by rfl⟩ : syracuseStep 2661269 = 124747) (by norm_num)
theorem B1997725 : Blo 1774088 1997725 := bbase (se 3 (by rfl) ⟨374573, by rfl⟩ : syracuseStep 1997725 = 749147) (by norm_num)
theorem B2661293 : Blo 1774088 2661293 := bbase (se 3 (by rfl) ⟨498992, by rfl⟩ : syracuseStep 2661293 = 997985) (by norm_num)
theorem B1997761 : Blo 1774088 1997761 := bbase (se 2 (by rfl) ⟨749160, by rfl⟩ : syracuseStep 1997761 = 1498321) (by norm_num)
theorem B2661317 : Blo 1774088 2661317 := bbase (se 4 (by rfl) ⟨249498, by rfl⟩ : syracuseStep 2661317 = 498997) (by norm_num)
theorem B2661341 : Blo 1774088 2661341 := bbase (se 3 (by rfl) ⟨499001, by rfl⟩ : syracuseStep 2661341 = 998003) (by norm_num)
theorem B1997797 : Blo 1774088 1997797 := bbase (se 4 (by rfl) ⟨187293, by rfl⟩ : syracuseStep 1997797 = 374587) (by norm_num)
theorem B2661365 : Blo 1774088 2661365 := bbase (se 5 (by rfl) ⟨124751, by rfl⟩ : syracuseStep 2661365 = 249503) (by norm_num)
theorem B1997833 : Blo 1774088 1997833 := bbase (se 2 (by rfl) ⟨749187, by rfl⟩ : syracuseStep 1997833 = 1498375) (by norm_num)
theorem B2661389 : Blo 1774088 2661389 := bbase (se 3 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 2661389 = 998021) (by norm_num)
theorem B2661413 : Blo 1774088 2661413 := bbase (se 4 (by rfl) ⟨249507, by rfl⟩ : syracuseStep 2661413 = 499015) (by norm_num)
theorem B3791909 : Blo 1774088 3791909 := bbase (se 4 (by rfl) ⟨355491, by rfl⟩ : syracuseStep 3791909 = 710983) (by norm_num)
theorem B1997869 : Blo 1774088 1997869 := bbase (se 3 (by rfl) ⟨374600, by rfl⟩ : syracuseStep 1997869 = 749201) (by norm_num)
theorem B8985653 : Blo 1774088 8985653 := bbase (se 5 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 8985653 = 842405) (by norm_num)
theorem B2661437 : Blo 1774088 2661437 := bbase (se 3 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 2661437 = 998039) (by norm_num)
theorem B1997905 : Blo 1774088 1997905 := bbase (se 2 (by rfl) ⟨749214, by rfl⟩ : syracuseStep 1997905 = 1498429) (by norm_num)
theorem B2661461 : Blo 1774088 2661461 := bbase (se 8 (by rfl) ⟨15594, by rfl⟩ : syracuseStep 2661461 = 31189) (by norm_num)
theorem B2661485 : Blo 1774088 2661485 := bbase (se 3 (by rfl) ⟨499028, by rfl⟩ : syracuseStep 2661485 = 998057) (by norm_num)
theorem B1997941 : Blo 1774088 1997941 := bbase (se 5 (by rfl) ⟨93653, by rfl⟩ : syracuseStep 1997941 = 187307) (by norm_num)
theorem B2661509 : Blo 1774088 2661509 := bbase (se 4 (by rfl) ⟨249516, by rfl⟩ : syracuseStep 2661509 = 499033) (by norm_num)
theorem B1997977 : Blo 1774088 1997977 := bbase (se 2 (by rfl) ⟨749241, by rfl⟩ : syracuseStep 1997977 = 1498483) (by norm_num)
theorem B2661533 : Blo 1774088 2661533 := bbase (se 3 (by rfl) ⟨499037, by rfl⟩ : syracuseStep 2661533 = 998075) (by norm_num)
theorem B2661557 : Blo 1774088 2661557 := bbase (se 5 (by rfl) ⟨124760, by rfl⟩ : syracuseStep 2661557 = 249521) (by norm_num)
theorem B12147893 : Blo 1774088 12147893 := bbase (se 5 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 12147893 = 1138865) (by norm_num)
theorem B3792053 : Blo 1774088 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B1998013 : Blo 1774088 1998013 := bbase (se 3 (by rfl) ⟨374627, by rfl⟩ : syracuseStep 1998013 = 749255) (by norm_num)
theorem B8527045 : Blo 1774088 8527045 := bbase (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) (by norm_num)
theorem B2661581 : Blo 1774088 2661581 := bbase (se 3 (by rfl) ⟨499046, by rfl⟩ : syracuseStep 2661581 = 998093) (by norm_num)
theorem B1998049 : Blo 1774088 1998049 := bbase (se 2 (by rfl) ⟨749268, by rfl⟩ : syracuseStep 1998049 = 1498537) (by norm_num)
theorem B2661605 : Blo 1774088 2661605 := bbase (se 4 (by rfl) ⟨249525, by rfl⟩ : syracuseStep 2661605 = 499051) (by norm_num)
theorem B5987573 : Blo 1774088 5987573 := bbase (se 5 (by rfl) ⟨280667, by rfl⟩ : syracuseStep 5987573 = 561335) (by norm_num)
theorem B2661629 : Blo 1774088 2661629 := bbase (se 3 (by rfl) ⟨499055, by rfl⟩ : syracuseStep 2661629 = 998111) (by norm_num)
theorem B1998085 : Blo 1774088 1998085 := bbase (se 4 (by rfl) ⟨187320, by rfl⟩ : syracuseStep 1998085 = 374641) (by norm_num)
theorem B2661653 : Blo 1774088 2661653 := bbase (se 6 (by rfl) ⟨62382, by rfl⟩ : syracuseStep 2661653 = 124765) (by norm_num)
theorem B2661677 : Blo 1774088 2661677 := bbase (se 3 (by rfl) ⟨499064, by rfl⟩ : syracuseStep 2661677 = 998129) (by norm_num)
theorem B2661701 : Blo 1774088 2661701 := bbase (se 4 (by rfl) ⟨249534, by rfl⟩ : syracuseStep 2661701 = 499069) (by norm_num)
theorem B2661725 : Blo 1774088 2661725 := bbase (se 3 (by rfl) ⟨499073, by rfl⟩ : syracuseStep 2661725 = 998147) (by norm_num)
theorem B2661749 : Blo 1774088 2661749 := bbase (se 5 (by rfl) ⟨124769, by rfl⟩ : syracuseStep 2661749 = 249539) (by norm_num)
theorem B2661773 : Blo 1774088 2661773 := bbase (se 3 (by rfl) ⟨499082, by rfl⟩ : syracuseStep 2661773 = 998165) (by norm_num)
theorem B2661797 : Blo 1774088 2661797 := bbase (se 4 (by rfl) ⟨249543, by rfl⟩ : syracuseStep 2661797 = 499087) (by norm_num)
theorem B6741413 : Blo 1774088 6741413 := bbase (se 4 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 6741413 = 1264015) (by norm_num)
theorem B3841453 : Blo 1774088 3841453 := bbase (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) (by norm_num)
theorem B2162093 : Blo 1774088 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B2661821 : Blo 1774088 2661821 := bbase (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) (by norm_num)
theorem B6831557 : Blo 1774088 6831557 := bbase (se 4 (by rfl) ⟨640458, by rfl⟩ : syracuseStep 6831557 = 1280917) (by norm_num)
theorem B2661845 : Blo 1774088 2661845 := bbase (se 7 (by rfl) ⟨31193, by rfl⟩ : syracuseStep 2661845 = 62387) (by norm_num)
theorem B2661869 : Blo 1774088 2661869 := bbase (se 3 (by rfl) ⟨499100, by rfl⟩ : syracuseStep 2661869 = 998201) (by norm_num)
theorem B2661893 : Blo 1774088 2661893 := bbase (se 4 (by rfl) ⟨249552, by rfl⟩ : syracuseStep 2661893 = 499105) (by norm_num)
theorem B2661917 : Blo 1774088 2661917 := bbase (se 3 (by rfl) ⟨499109, by rfl⟩ : syracuseStep 2661917 = 998219) (by norm_num)
theorem B3792413 : Blo 1774088 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B2661941 : Blo 1774088 2661941 := bbase (se 5 (by rfl) ⟨124778, by rfl⟩ : syracuseStep 2661941 = 249557) (by norm_num)
theorem B5054021 : Blo 1774088 5054021 := bbase (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) (by norm_num)
theorem B2661965 : Blo 1774088 2661965 := bbase (se 3 (by rfl) ⟨499118, by rfl⟩ : syracuseStep 2661965 = 998237) (by norm_num)
theorem B13663829 : Blo 1774088 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B2661989 : Blo 1774088 2661989 := bbase (se 4 (by rfl) ⟨249561, by rfl⟩ : syracuseStep 2661989 = 499123) (by norm_num)
theorem B2662013 : Blo 1774088 2662013 := bbase (se 3 (by rfl) ⟨499127, by rfl⟩ : syracuseStep 2662013 = 998255) (by norm_num)
theorem B2662037 : Blo 1774088 2662037 := bbase (se 6 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 2662037 = 124783) (by norm_num)
theorem B5988005 : Blo 1774088 5988005 := bbase (se 4 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 5988005 = 1122751) (by norm_num)
theorem B3415717 : Blo 1774088 3415717 := bbase (se 4 (by rfl) ⟨320223, by rfl⟩ : syracuseStep 3415717 = 640447) (by norm_num)
theorem B2662061 : Blo 1774088 2662061 := bbase (se 3 (by rfl) ⟨499136, by rfl⟩ : syracuseStep 2662061 = 998273) (by norm_num)
theorem B2662085 : Blo 1774088 2662085 := bbase (se 4 (by rfl) ⟨249570, by rfl⟩ : syracuseStep 2662085 = 499141) (by norm_num)
theorem B6741701 : Blo 1774088 6741701 := bbase (se 4 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 6741701 = 1264069) (by norm_num)
theorem B2662109 : Blo 1774088 2662109 := bbase (se 3 (by rfl) ⟨499145, by rfl⟩ : syracuseStep 2662109 = 998291) (by norm_num)
theorem B2662133 : Blo 1774088 2662133 := bbase (se 5 (by rfl) ⟨124787, by rfl⟩ : syracuseStep 2662133 = 249575) (by norm_num)
theorem B2662157 : Blo 1774088 2662157 := bbase (se 3 (by rfl) ⟨499154, by rfl⟩ : syracuseStep 2662157 = 998309) (by norm_num)
theorem B12975893 : Blo 1774088 12975893 := bbase (se 6 (by rfl) ⟨304122, by rfl⟩ : syracuseStep 12975893 = 608245) (by norm_num)
theorem B2662181 : Blo 1774088 2662181 := bbase (se 4 (by rfl) ⟨249579, by rfl⟩ : syracuseStep 2662181 = 499159) (by norm_num)
theorem B2662205 : Blo 1774088 2662205 := bbase (se 3 (by rfl) ⟨499163, by rfl⟩ : syracuseStep 2662205 = 998327) (by norm_num)
theorem B2662229 : Blo 1774088 2662229 := bbase (se 9 (by rfl) ⟨7799, by rfl⟩ : syracuseStep 2662229 = 15599) (by norm_num)
theorem B2662253 : Blo 1774088 2662253 := bbase (se 3 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 2662253 = 998345) (by norm_num)
theorem B2662277 : Blo 1774088 2662277 := bbase (se 4 (by rfl) ⟨249588, by rfl⟩ : syracuseStep 2662277 = 499177) (by norm_num)
theorem B2662301 : Blo 1774088 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B2662325 : Blo 1774088 2662325 := bbase (se 5 (by rfl) ⟨124796, by rfl⟩ : syracuseStep 2662325 = 249593) (by norm_num)
theorem B2662349 : Blo 1774088 2662349 := bbase (se 3 (by rfl) ⟨499190, by rfl⟩ : syracuseStep 2662349 = 998381) (by norm_num)
theorem B2662373 : Blo 1774088 2662373 := bbase (se 4 (by rfl) ⟨249597, by rfl⟩ : syracuseStep 2662373 = 499195) (by norm_num)
theorem B2662397 : Blo 1774088 2662397 := bbase (se 3 (by rfl) ⟨499199, by rfl⟩ : syracuseStep 2662397 = 998399) (by norm_num)
theorem B2662403 : Blo 1774088 2662403 := bstep (se 1 (by rfl) ⟨1996802, by rfl⟩ : syracuseStep 2662403 = 3993605) B3993605
theorem B2662433 : Blo 1774088 2662433 := bstep (se 2 (by rfl) ⟨998412, by rfl⟩ : syracuseStep 2662433 = 1996825) B1996825
theorem B2662451 : Blo 1774088 2662451 := bstep (se 1 (by rfl) ⟨1996838, by rfl⟩ : syracuseStep 2662451 = 3993677) B3993677
theorem B2662481 : Blo 1774088 2662481 := bstep (se 2 (by rfl) ⟨998430, by rfl⟩ : syracuseStep 2662481 = 1996861) B1996861
theorem B2662499 : Blo 1774088 2662499 := bstep (se 1 (by rfl) ⟨1996874, by rfl⟩ : syracuseStep 2662499 = 3993749) B3993749
theorem B2662529 : Blo 1774088 2662529 := bstep (se 2 (by rfl) ⟨998448, by rfl⟩ : syracuseStep 2662529 = 1996897) B1996897
theorem B2662547 : Blo 1774088 2662547 := bstep (se 1 (by rfl) ⟨1996910, by rfl⟩ : syracuseStep 2662547 = 3993821) B3993821
theorem B8986787 : Blo 1774088 8986787 := bstep (se 1 (by rfl) ⟨6740090, by rfl⟩ : syracuseStep 8986787 = 13480181) B13480181
theorem B2662577 : Blo 1774088 2662577 := bstep (se 2 (by rfl) ⟨998466, by rfl⟩ : syracuseStep 2662577 = 1996933) B1996933
theorem B2662595 : Blo 1774088 2662595 := bstep (se 1 (by rfl) ⟨1996946, by rfl⟩ : syracuseStep 2662595 = 3993893) B3993893
theorem B4554947 : Blo 1774088 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2662625 : Blo 1774088 2662625 := bstep (se 2 (by rfl) ⟨998484, by rfl⟩ : syracuseStep 2662625 = 1996969) B1996969
theorem B2662643 : Blo 1774088 2662643 := bstep (se 1 (by rfl) ⟨1996982, by rfl⟩ : syracuseStep 2662643 = 3993965) B3993965
theorem B2662673 : Blo 1774088 2662673 := bstep (se 2 (by rfl) ⟨998502, by rfl⟩ : syracuseStep 2662673 = 1997005) B1997005
theorem B2842913 : Blo 1774088 2842913 := bstep (se 2 (by rfl) ⟨1066092, by rfl⟩ : syracuseStep 2842913 = 2132185) B2132185
theorem B2662691 : Blo 1774088 2662691 := bstep (se 1 (by rfl) ⟨1997018, by rfl⟩ : syracuseStep 2662691 = 3994037) B3994037
theorem B5988653 : Blo 1774088 5988653 := bstep (se 3 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 5988653 = 2245745) B2245745
theorem B2662721 : Blo 1774088 2662721 := bstep (se 2 (by rfl) ⟨998520, by rfl⟩ : syracuseStep 2662721 = 1997041) B1997041
theorem B2662739 : Blo 1774088 2662739 := bstep (se 1 (by rfl) ⟨1997054, by rfl⟩ : syracuseStep 2662739 = 3994109) B3994109
theorem B5988707 : Blo 1774088 5988707 := bstep (se 1 (by rfl) ⟨4491530, by rfl⟩ : syracuseStep 5988707 = 8983061) B8983061
theorem B2662769 : Blo 1774088 2662769 := bstep (se 2 (by rfl) ⟨998538, by rfl⟩ : syracuseStep 2662769 = 1997077) B1997077
theorem B6742385 : Blo 1774088 6742385 := bstep (se 2 (by rfl) ⟨2528394, by rfl⟩ : syracuseStep 6742385 = 5056789) B5056789
theorem B2662787 : Blo 1774088 2662787 := bstep (se 1 (by rfl) ⟨1997090, by rfl⟩ : syracuseStep 2662787 = 3994181) B3994181
theorem B2843041 : Blo 1774088 2843041 := bstep (se 2 (by rfl) ⟨1066140, by rfl⟩ : syracuseStep 2843041 = 2132281) B2132281
theorem B2662817 : Blo 1774088 2662817 := bstep (se 2 (by rfl) ⟨998556, by rfl⟩ : syracuseStep 2662817 = 1997113) B1997113
theorem B2662835 : Blo 1774088 2662835 := bstep (se 1 (by rfl) ⟨1997126, by rfl⟩ : syracuseStep 2662835 = 3994253) B3994253
theorem B13476293 : Blo 1774088 13476293 := bstep (se 4 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 13476293 = 2526805) B2526805
theorem B2662865 : Blo 1774088 2662865 := bstep (se 2 (by rfl) ⟨998574, by rfl⟩ : syracuseStep 2662865 = 1997149) B1997149
theorem B2662883 : Blo 1774088 2662883 := bstep (se 1 (by rfl) ⟨1997162, by rfl⟩ : syracuseStep 2662883 = 3994325) B3994325
theorem B2662913 : Blo 1774088 2662913 := bstep (se 2 (by rfl) ⟨998592, by rfl⟩ : syracuseStep 2662913 = 1997185) B1997185
theorem B15172109 : Blo 1774088 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B2662931 : Blo 1774088 2662931 := bstep (se 1 (by rfl) ⟨1997198, by rfl⟩ : syracuseStep 2662931 = 3994397) B3994397
theorem B7578161 : Blo 1774088 7578161 := bstep (se 2 (by rfl) ⟨2841810, by rfl⟩ : syracuseStep 7578161 = 5683621) B5683621
theorem B2662961 : Blo 1774088 2662961 := bstep (se 2 (by rfl) ⟨998610, by rfl⟩ : syracuseStep 2662961 = 1997221) B1997221
theorem B2662979 : Blo 1774088 2662979 := bstep (se 1 (by rfl) ⟨1997234, by rfl⟩ : syracuseStep 2662979 = 3994469) B3994469
theorem B2663009 : Blo 1774088 2663009 := bstep (se 2 (by rfl) ⟨998628, by rfl⟩ : syracuseStep 2663009 = 1997257) B1997257
theorem B5988977 : Blo 1774088 5988977 := bstep (se 2 (by rfl) ⟨2245866, by rfl⟩ : syracuseStep 5988977 = 4491733) B4491733
theorem B2663027 : Blo 1774088 2663027 := bstep (se 1 (by rfl) ⟨1997270, by rfl⟩ : syracuseStep 2663027 = 3994541) B3994541
theorem B16196237 : Blo 1774088 16196237 := bstep (se 3 (by rfl) ⟨3036794, by rfl⟩ : syracuseStep 16196237 = 6073589) B6073589
theorem B2663057 : Blo 1774088 2663057 := bstep (se 2 (by rfl) ⟨998646, by rfl⟩ : syracuseStep 2663057 = 1997293) B1997293
theorem B2663075 : Blo 1774088 2663075 := bstep (se 1 (by rfl) ⟨1997306, by rfl⟩ : syracuseStep 2663075 = 3994613) B3994613
theorem B5055149 : Blo 1774088 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B2663105 : Blo 1774088 2663105 := bstep (se 2 (by rfl) ⟨998664, by rfl⟩ : syracuseStep 2663105 = 1997329) B1997329
theorem B2663123 : Blo 1774088 2663123 := bstep (se 1 (by rfl) ⟨1997342, by rfl⟩ : syracuseStep 2663123 = 3994685) B3994685
theorem B3597041 : Blo 1774088 3597041 := bstep (se 2 (by rfl) ⟨1348890, by rfl⟩ : syracuseStep 3597041 = 2697781) B2697781
theorem B10109681 : Blo 1774088 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B2663153 : Blo 1774088 2663153 := bstep (se 2 (by rfl) ⟨998682, by rfl⟩ : syracuseStep 2663153 = 1997365) B1997365
theorem B2663171 : Blo 1774088 2663171 := bstep (se 1 (by rfl) ⟨1997378, by rfl⟩ : syracuseStep 2663171 = 3994757) B3994757
theorem B2843425 : Blo 1774088 2843425 := bstep (se 2 (by rfl) ⟨1066284, by rfl⟩ : syracuseStep 2843425 = 2132569) B2132569
theorem B2663201 : Blo 1774088 2663201 := bstep (se 2 (by rfl) ⟨998700, by rfl⟩ : syracuseStep 2663201 = 1997401) B1997401
theorem B2245411 : Blo 1774088 2245411 := bstep (se 1 (by rfl) ⟨1684058, by rfl⟩ : syracuseStep 2245411 = 3368117) B3368117
theorem B2663219 : Blo 1774088 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B2663249 : Blo 1774088 2663249 := bstep (se 2 (by rfl) ⟨998718, by rfl⟩ : syracuseStep 2663249 = 1997437) B1997437
theorem B5055331 : Blo 1774088 5055331 := bstep (se 1 (by rfl) ⟨3791498, by rfl⟩ : syracuseStep 5055331 = 7582997) B7582997
theorem B2663267 : Blo 1774088 2663267 := bstep (se 1 (by rfl) ⟨1997450, by rfl⟩ : syracuseStep 2663267 = 3994901) B3994901
theorem B2663297 : Blo 1774088 2663297 := bstep (se 2 (by rfl) ⟨998736, by rfl⟩ : syracuseStep 2663297 = 1997473) B1997473
theorem B2663315 : Blo 1774088 2663315 := bstep (se 1 (by rfl) ⟨1997486, by rfl⟩ : syracuseStep 2663315 = 3994973) B3994973
theorem B2663345 : Blo 1774088 2663345 := bstep (se 2 (by rfl) ⟨998754, by rfl⟩ : syracuseStep 2663345 = 1997509) B1997509
theorem B2663363 : Blo 1774088 2663363 := bstep (se 1 (by rfl) ⟨1997522, by rfl⟩ : syracuseStep 2663363 = 3995045) B3995045
theorem B2737091 : Blo 1774088 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B8987597 : Blo 1774088 8987597 := bstep (se 3 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 8987597 = 3370349) B3370349
theorem B2663393 : Blo 1774088 2663393 := bstep (se 2 (by rfl) ⟨998772, by rfl⟩ : syracuseStep 2663393 = 1997545) B1997545
theorem B13485041 : Blo 1774088 13485041 := bstep (se 2 (by rfl) ⟨5056890, by rfl⟩ : syracuseStep 13485041 = 10113781) B10113781
theorem B2663411 : Blo 1774088 2663411 := bstep (se 1 (by rfl) ⟨1997558, by rfl⟩ : syracuseStep 2663411 = 3995117) B3995117
theorem B2663441 : Blo 1774088 2663441 := bstep (se 2 (by rfl) ⟨998790, by rfl⟩ : syracuseStep 2663441 = 1997581) B1997581
theorem B2843681 : Blo 1774088 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B2663459 : Blo 1774088 2663459 := bstep (se 1 (by rfl) ⟨1997594, by rfl⟩ : syracuseStep 2663459 = 3995189) B3995189
theorem B2663489 : Blo 1774088 2663489 := bstep (se 2 (by rfl) ⟨998808, by rfl⟩ : syracuseStep 2663489 = 1997617) B1997617
theorem B2663507 : Blo 1774088 2663507 := bstep (se 1 (by rfl) ⟨1997630, by rfl⟩ : syracuseStep 2663507 = 3995261) B3995261
theorem B2278499 : Blo 1774088 2278499 := bstep (se 1 (by rfl) ⟨1708874, by rfl⟩ : syracuseStep 2278499 = 3417749) B3417749
theorem B2663537 : Blo 1774088 2663537 := bstep (se 2 (by rfl) ⟨998826, by rfl⟩ : syracuseStep 2663537 = 1997653) B1997653
theorem B2663555 : Blo 1774088 2663555 := bstep (se 1 (by rfl) ⟨1997666, by rfl⟩ : syracuseStep 2663555 = 3995333) B3995333
theorem B5989517 : Blo 1774088 5989517 := bstep (se 3 (by rfl) ⟨1123034, by rfl⟩ : syracuseStep 5989517 = 2246069) B2246069
theorem B2663585 : Blo 1774088 2663585 := bstep (se 2 (by rfl) ⟨998844, by rfl⟩ : syracuseStep 2663585 = 1997689) B1997689
theorem B2663603 : Blo 1774088 2663603 := bstep (se 1 (by rfl) ⟨1997702, by rfl⟩ : syracuseStep 2663603 = 3995405) B3995405
theorem B5989571 : Blo 1774088 5989571 := bstep (se 1 (by rfl) ⟨4492178, by rfl⟩ : syracuseStep 5989571 = 8984357) B8984357
theorem B2663633 : Blo 1774088 2663633 := bstep (se 2 (by rfl) ⟨998862, by rfl⟩ : syracuseStep 2663633 = 1997725) B1997725
theorem B2663651 : Blo 1774088 2663651 := bstep (se 1 (by rfl) ⟨1997738, by rfl⟩ : syracuseStep 2663651 = 3995477) B3995477
theorem B8209649 : Blo 1774088 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B2663681 : Blo 1774088 2663681 := bstep (se 2 (by rfl) ⟨998880, by rfl⟩ : syracuseStep 2663681 = 1997761) B1997761
theorem B2245907 : Blo 1774088 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B2663699 : Blo 1774088 2663699 := bstep (se 1 (by rfl) ⟨1997774, by rfl⟩ : syracuseStep 2663699 = 3995549) B3995549
theorem B2663729 : Blo 1774088 2663729 := bstep (se 2 (by rfl) ⟨998898, by rfl⟩ : syracuseStep 2663729 = 1997797) B1997797
theorem B5686595 : Blo 1774088 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B2663747 : Blo 1774088 2663747 := bstep (se 1 (by rfl) ⟨1997810, by rfl⟩ : syracuseStep 2663747 = 3995621) B3995621
theorem B11371853 : Blo 1774088 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B5055821 : Blo 1774088 5055821 := bstep (se 3 (by rfl) ⟨947966, by rfl⟩ : syracuseStep 5055821 = 1895933) B1895933
theorem B2663777 : Blo 1774088 2663777 := bstep (se 2 (by rfl) ⟨998916, by rfl⟩ : syracuseStep 2663777 = 1997833) B1997833
theorem B2663795 : Blo 1774088 2663795 := bstep (se 1 (by rfl) ⟨1997846, by rfl⟩ : syracuseStep 2663795 = 3995693) B3995693
theorem B2663825 : Blo 1774088 2663825 := bstep (se 2 (by rfl) ⟨998934, by rfl⟩ : syracuseStep 2663825 = 1997869) B1997869
theorem B2663843 : Blo 1774088 2663843 := bstep (se 1 (by rfl) ⟨1997882, by rfl⟩ : syracuseStep 2663843 = 3995765) B3995765
theorem B2663873 : Blo 1774088 2663873 := bstep (se 2 (by rfl) ⟨998952, by rfl⟩ : syracuseStep 2663873 = 1997905) B1997905
theorem B5989841 : Blo 1774088 5989841 := bstep (se 2 (by rfl) ⟨2246190, by rfl⟩ : syracuseStep 5989841 = 4492381) B4492381
theorem B2663891 : Blo 1774088 2663891 := bstep (se 1 (by rfl) ⟨1997918, by rfl⟩ : syracuseStep 2663891 = 3995837) B3995837
theorem B2663921 : Blo 1774088 2663921 := bstep (se 2 (by rfl) ⟨998970, by rfl⟩ : syracuseStep 2663921 = 1997941) B1997941
theorem B2663939 : Blo 1774088 2663939 := bstep (se 1 (by rfl) ⟨1997954, by rfl⟩ : syracuseStep 2663939 = 3995909) B3995909
theorem B2663969 : Blo 1774088 2663969 := bstep (se 2 (by rfl) ⟨998988, by rfl⟩ : syracuseStep 2663969 = 1997977) B1997977
theorem B2663987 : Blo 1774088 2663987 := bstep (se 1 (by rfl) ⟨1997990, by rfl⟩ : syracuseStep 2663987 = 3995981) B3995981
theorem B2664017 : Blo 1774088 2664017 := bstep (se 2 (by rfl) ⟨999006, by rfl⟩ : syracuseStep 2664017 = 1998013) B1998013
theorem B5121635 : Blo 1774088 5121635 := bstep (se 1 (by rfl) ⟨3841226, by rfl⟩ : syracuseStep 5121635 = 7682453) B7682453
theorem B2664035 : Blo 1774088 2664035 := bstep (se 1 (by rfl) ⟨1998026, by rfl⟩ : syracuseStep 2664035 = 3996053) B3996053
theorem B2664065 : Blo 1774088 2664065 := bstep (se 2 (by rfl) ⟨999024, by rfl⟩ : syracuseStep 2664065 = 1998049) B1998049
theorem B5400209 : Blo 1774088 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B2664083 : Blo 1774088 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B2664113 : Blo 1774088 2664113 := bstep (se 2 (by rfl) ⟨999042, by rfl⟩ : syracuseStep 2664113 = 1998085) B1998085
theorem B2664131 : Blo 1774088 2664131 := bstep (se 1 (by rfl) ⟨1998098, by rfl⟩ : syracuseStep 2664131 = 3996197) B3996197
theorem B23062325 : Blo 1774088 23062325 := bstep (se 5 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 23062325 = 2162093) B2162093
theorem B3368785 : Blo 1774088 3368785 := bstep (se 2 (by rfl) ⟨1263294, by rfl⟩ : syracuseStep 3368785 = 2526589) B2526589
theorem B12797837 : Blo 1774088 12797837 := bstep (se 3 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 12797837 = 4799189) B4799189
theorem B5121937 : Blo 1774088 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B2246611 : Blo 1774088 2246611 := bstep (se 1 (by rfl) ⟨1684958, by rfl⟩ : syracuseStep 2246611 = 3369917) B3369917
theorem B5990381 : Blo 1774088 5990381 := bstep (se 3 (by rfl) ⟨1123196, by rfl⟩ : syracuseStep 5990381 = 2246393) B2246393
theorem B3368945 : Blo 1774088 3368945 := bstep (se 2 (by rfl) ⟨1263354, by rfl⟩ : syracuseStep 3368945 = 2526709) B2526709
theorem B5990435 : Blo 1774088 5990435 := bstep (se 1 (by rfl) ⟨4492826, by rfl⟩ : syracuseStep 5990435 = 8985653) B8985653
theorem B2246707 : Blo 1774088 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B3197009 : Blo 1774088 3197009 := bstep (se 2 (by rfl) ⟨1198878, by rfl⟩ : syracuseStep 3197009 = 2397757) B2397757
theorem B4491409 : Blo 1774088 4491409 := bstep (se 2 (by rfl) ⟨1684278, by rfl⟩ : syracuseStep 4491409 = 3368557) B3368557
theorem B3991715 : Blo 1774088 3991715 := bstep (se 1 (by rfl) ⟨2993786, by rfl⟩ : syracuseStep 3991715 = 5987573) B5987573
theorem B10111139 : Blo 1774088 10111139 := bstep (se 1 (by rfl) ⟨7583354, by rfl⟩ : syracuseStep 10111139 = 15166709) B15166709
theorem B5687491 : Blo 1774088 5687491 := bstep (se 1 (by rfl) ⟨4265618, by rfl⟩ : syracuseStep 5687491 = 8531237) B8531237
theorem B10799345 : Blo 1774088 10799345 := bstep (se 2 (by rfl) ⟨4049754, by rfl⟩ : syracuseStep 10799345 = 8099509) B8099509
theorem B5990705 : Blo 1774088 5990705 := bstep (se 2 (by rfl) ⟨2246514, by rfl⟩ : syracuseStep 5990705 = 4493029) B4493029
theorem B3369347 : Blo 1774088 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B4491683 : Blo 1774088 4491683 := bstep (se 1 (by rfl) ⟨3368762, by rfl⟩ : syracuseStep 4491683 = 6737525) B6737525
theorem B3991985 : Blo 1774088 3991985 := bstep (se 2 (by rfl) ⟨1496994, by rfl⟩ : syracuseStep 3991985 = 2993989) B2993989
theorem B3992003 : Blo 1774088 3992003 := bstep (se 1 (by rfl) ⟨2994002, by rfl⟩ : syracuseStep 3992003 = 5988005) B5988005
theorem B6736355 : Blo 1774088 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B30329315 : Blo 1774088 30329315 := bstep (se 1 (by rfl) ⟨22746986, by rfl⟩ : syracuseStep 30329315 = 45493973) B45493973
theorem B5057005 : Blo 1774088 5057005 := bstep (se 3 (by rfl) ⟨948188, by rfl⟩ : syracuseStep 5057005 = 1896377) B1896377
theorem B2247203 : Blo 1774088 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B7195213 : Blo 1774088 7195213 := bstep (se 3 (by rfl) ⟨1349102, by rfl⟩ : syracuseStep 7195213 = 2698205) B2698205
theorem B4491875 : Blo 1774088 4491875 := bstep (se 1 (by rfl) ⟨3368906, by rfl⟩ : syracuseStep 4491875 = 6737813) B6737813
theorem B3992273 : Blo 1774088 3992273 := bstep (se 2 (by rfl) ⟨1497102, by rfl⟩ : syracuseStep 3992273 = 2994205) B2994205
theorem B3992291 : Blo 1774088 3992291 := bstep (se 1 (by rfl) ⟨2994218, by rfl⟩ : syracuseStep 3992291 = 5988437) B5988437
theorem B12151565 : Blo 1774088 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B46107413 : Blo 1774088 46107413 := bstep (se 6 (by rfl) ⟨1080642, by rfl⟩ : syracuseStep 46107413 = 2161285) B2161285
theorem B5991245 : Blo 1774088 5991245 := bstep (se 3 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 5991245 = 2246717) B2246717
theorem B5991299 : Blo 1774088 5991299 := bstep (se 1 (by rfl) ⟨4493474, by rfl⟩ : syracuseStep 5991299 = 8986949) B8986949
theorem B7580621 : Blo 1774088 7580621 := bstep (se 3 (by rfl) ⟨1421366, by rfl⟩ : syracuseStep 7580621 = 2842733) B2842733
theorem B5843917 : Blo 1774088 5843917 := bstep (se 3 (by rfl) ⟨1095734, by rfl⟩ : syracuseStep 5843917 = 2191469) B2191469
theorem B3992561 : Blo 1774088 3992561 := bstep (se 2 (by rfl) ⟨1497210, by rfl⟩ : syracuseStep 3992561 = 2994421) B2994421
theorem B3992579 : Blo 1774088 3992579 := bstep (se 1 (by rfl) ⟨2994434, by rfl⟩ : syracuseStep 3992579 = 5988869) B5988869
theorem B8981603 : Blo 1774088 8981603 := bstep (se 1 (by rfl) ⟨6736202, by rfl⟩ : syracuseStep 8981603 = 13472405) B13472405
theorem B3697777 : Blo 1774088 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B10112141 : Blo 1774088 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B5991569 : Blo 1774088 5991569 := bstep (se 2 (by rfl) ⟨2246838, by rfl⟩ : syracuseStep 5991569 = 4493677) B4493677
theorem B3198161 : Blo 1774088 3198161 := bstep (se 2 (by rfl) ⟨1199310, by rfl⟩ : syracuseStep 3198161 = 2398621) B2398621
theorem B3370243 : Blo 1774088 3370243 := bstep (se 1 (by rfl) ⟨2527682, by rfl⟩ : syracuseStep 3370243 = 5055365) B5055365
theorem B2526481 : Blo 1774088 2526481 := bstep (se 2 (by rfl) ⟨947430, by rfl⟩ : syracuseStep 2526481 = 1894861) B1894861
theorem B3992849 : Blo 1774088 3992849 := bstep (se 2 (by rfl) ⟨1497318, by rfl⟩ : syracuseStep 3992849 = 2994637) B2994637
theorem B5688593 : Blo 1774088 5688593 := bstep (se 2 (by rfl) ⟨2133222, by rfl⟩ : syracuseStep 5688593 = 4266445) B4266445
theorem B3992867 : Blo 1774088 3992867 := bstep (se 1 (by rfl) ⟨2994650, by rfl⟩ : syracuseStep 3992867 = 5989301) B5989301
theorem B2133299 : Blo 1774088 2133299 := bstep (se 1 (by rfl) ⟨1599974, by rfl⟩ : syracuseStep 2133299 = 3199949) B3199949
theorem B5688721 : Blo 1774088 5688721 := bstep (se 2 (by rfl) ⟨2133270, by rfl⟩ : syracuseStep 5688721 = 4266541) B4266541
theorem B3370403 : Blo 1774088 3370403 := bstep (se 1 (by rfl) ⟨2527802, by rfl⟩ : syracuseStep 3370403 = 5055605) B5055605
theorem B3198385 : Blo 1774088 3198385 := bstep (se 2 (by rfl) ⟨1199394, by rfl⟩ : syracuseStep 3198385 = 2398789) B2398789
theorem B6737357 : Blo 1774088 6737357 := bstep (se 3 (by rfl) ⟨1263254, by rfl⟩ : syracuseStep 6737357 = 2526509) B2526509
theorem B2698705 : Blo 1774088 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B4492817 : Blo 1774088 4492817 := bstep (se 2 (by rfl) ⟨1684806, by rfl⟩ : syracuseStep 4492817 = 3369613) B3369613
theorem B3993137 : Blo 1774088 3993137 := bstep (se 2 (by rfl) ⟨1497426, by rfl⟩ : syracuseStep 3993137 = 2994853) B2994853
theorem B25579061 : Blo 1774088 25579061 := bstep (se 5 (by rfl) ⟨1199018, by rfl⟩ : syracuseStep 25579061 = 2398037) B2398037
theorem B3993155 : Blo 1774088 3993155 := bstep (se 1 (by rfl) ⟨2994866, by rfl⟩ : syracuseStep 3993155 = 5989733) B5989733
theorem B4492867 : Blo 1774088 4492867 := bstep (se 1 (by rfl) ⟨3369650, by rfl⟩ : syracuseStep 4492867 = 6739301) B6739301
theorem B2526817 : Blo 1774088 2526817 := bstep (se 2 (by rfl) ⟨947556, by rfl⟩ : syracuseStep 2526817 = 1895113) B1895113
theorem B2993827 : Blo 1774088 2993827 := bstep (se 1 (by rfl) ⟨2245370, by rfl⟩ : syracuseStep 2993827 = 4490741) B4490741
theorem B5992109 : Blo 1774088 5992109 := bstep (se 3 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 5992109 = 2247041) B2247041
theorem B5762765 : Blo 1774088 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B4493009 : Blo 1774088 4493009 := bstep (se 2 (by rfl) ⟨1684878, by rfl⟩ : syracuseStep 4493009 = 3369757) B3369757
theorem B5992163 : Blo 1774088 5992163 := bstep (se 1 (by rfl) ⟨4494122, by rfl⟩ : syracuseStep 5992163 = 8988245) B8988245
theorem B2993969 : Blo 1774088 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B8990513 : Blo 1774088 8990513 := bstep (se 2 (by rfl) ⟨3371442, by rfl⟩ : syracuseStep 8990513 = 6742885) B6742885
theorem B3993425 : Blo 1774088 3993425 := bstep (se 2 (by rfl) ⟨1497534, by rfl⟩ : syracuseStep 3993425 = 2995069) B2995069
theorem B3993443 : Blo 1774088 3993443 := bstep (se 1 (by rfl) ⟨2995082, by rfl⟩ : syracuseStep 3993443 = 5990165) B5990165
theorem B8982413 : Blo 1774088 8982413 := bstep (se 3 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 8982413 = 3368405) B3368405
theorem B2994097 : Blo 1774088 2994097 := bstep (se 2 (by rfl) ⟨1122786, by rfl⟩ : syracuseStep 2994097 = 2245573) B2245573
theorem B2994131 : Blo 1774088 2994131 := bstep (se 1 (by rfl) ⟨2245598, by rfl⟩ : syracuseStep 2994131 = 4491197) B4491197
theorem B5992433 : Blo 1774088 5992433 := bstep (se 2 (by rfl) ⟨2247162, by rfl⟩ : syracuseStep 5992433 = 4494325) B4494325
theorem B2994259 : Blo 1774088 2994259 := bstep (se 1 (by rfl) ⟨2245694, by rfl⟩ : syracuseStep 2994259 = 4491389) B4491389
theorem B3993713 : Blo 1774088 3993713 := bstep (se 2 (by rfl) ⟨1497642, by rfl⟩ : syracuseStep 3993713 = 2995285) B2995285
theorem B3993731 : Blo 1774088 3993731 := bstep (se 1 (by rfl) ⟨2995298, by rfl⟩ : syracuseStep 3993731 = 5990597) B5990597
theorem B2527409 : Blo 1774088 2527409 := bstep (se 2 (by rfl) ⟨947778, by rfl⟩ : syracuseStep 2527409 = 1895557) B1895557
theorem B3199171 : Blo 1774088 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B2994401 : Blo 1774088 2994401 := bstep (se 2 (by rfl) ⟨1122900, by rfl⟩ : syracuseStep 2994401 = 2245801) B2245801
theorem B2994529 : Blo 1774088 2994529 := bstep (se 2 (by rfl) ⟨1122948, by rfl⟩ : syracuseStep 2994529 = 2245897) B2245897
theorem B5689709 : Blo 1774088 5689709 := bstep (se 3 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 5689709 = 2133641) B2133641
theorem B2994563 : Blo 1774088 2994563 := bstep (se 1 (by rfl) ⟨2245922, by rfl⟩ : syracuseStep 2994563 = 4491845) B4491845
theorem B3994001 : Blo 1774088 3994001 := bstep (se 2 (by rfl) ⟨1497750, by rfl⟩ : syracuseStep 3994001 = 2995501) B2995501
theorem B3994019 : Blo 1774088 3994019 := bstep (se 1 (by rfl) ⟨2995514, by rfl⟩ : syracuseStep 3994019 = 5991029) B5991029
theorem B3371473 : Blo 1774088 3371473 := bstep (se 2 (by rfl) ⟨1264302, by rfl⟩ : syracuseStep 3371473 = 2528605) B2528605
theorem B7582193 : Blo 1774088 7582193 := bstep (se 2 (by rfl) ⟨2843322, by rfl⟩ : syracuseStep 7582193 = 5686645) B5686645
theorem B2994691 : Blo 1774088 2994691 := bstep (se 1 (by rfl) ⟨2246018, by rfl⟩ : syracuseStep 2994691 = 4492037) B4492037
theorem B4796941 : Blo 1774088 4796941 := bstep (se 3 (by rfl) ⟨899426, by rfl⟩ : syracuseStep 4796941 = 1798853) B1798853
theorem B5992973 : Blo 1774088 5992973 := bstep (se 3 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 5992973 = 2247365) B2247365
theorem B1774099 : Blo 1774088 1774099 := bstep (se 1 (by rfl) ⟨1330574, by rfl⟩ : syracuseStep 1774099 = 2661149) B2661149
theorem B1774115 : Blo 1774088 1774115 := bstep (se 1 (by rfl) ⟨1330586, by rfl⟩ : syracuseStep 1774115 = 2661173) B2661173
theorem B1774131 : Blo 1774088 1774131 := bstep (se 1 (by rfl) ⟨1330598, by rfl⟩ : syracuseStep 1774131 = 2661197) B2661197
theorem B1774147 : Blo 1774088 1774147 := bstep (se 1 (by rfl) ⟨1330610, by rfl⟩ : syracuseStep 1774147 = 2661221) B2661221
theorem B5993027 : Blo 1774088 5993027 := bstep (se 1 (by rfl) ⟨4494770, by rfl⟩ : syracuseStep 5993027 = 8989541) B8989541
theorem B1774163 : Blo 1774088 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1774179 : Blo 1774088 1774179 := bstep (se 1 (by rfl) ⟨1330634, by rfl⟩ : syracuseStep 1774179 = 2661269) B2661269
theorem B1774195 : Blo 1774088 1774195 := bstep (se 1 (by rfl) ⟨1330646, by rfl⟩ : syracuseStep 1774195 = 2661293) B2661293
theorem B1774211 : Blo 1774088 1774211 := bstep (se 1 (by rfl) ⟨1330658, by rfl⟩ : syracuseStep 1774211 = 2661317) B2661317
theorem B23368333 : Blo 1774088 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B2994833 : Blo 1774088 2994833 := bstep (se 2 (by rfl) ⟨1123062, by rfl⟩ : syracuseStep 2994833 = 2246125) B2246125
theorem B1774227 : Blo 1774088 1774227 := bstep (se 1 (by rfl) ⟨1330670, by rfl⟩ : syracuseStep 1774227 = 2661341) B2661341
theorem B1774243 : Blo 1774088 1774243 := bstep (se 1 (by rfl) ⟨1330682, by rfl⟩ : syracuseStep 1774243 = 2661365) B2661365
theorem B4797091 : Blo 1774088 4797091 := bstep (se 1 (by rfl) ⟨3597818, by rfl⟩ : syracuseStep 4797091 = 7195637) B7195637
theorem B3994289 : Blo 1774088 3994289 := bstep (se 2 (by rfl) ⟨1497858, by rfl⟩ : syracuseStep 3994289 = 2995717) B2995717
theorem B4494001 : Blo 1774088 4494001 := bstep (se 2 (by rfl) ⟨1685250, by rfl⟩ : syracuseStep 4494001 = 3370501) B3370501
theorem B1774259 : Blo 1774088 1774259 := bstep (se 1 (by rfl) ⟨1330694, by rfl⟩ : syracuseStep 1774259 = 2661389) B2661389
theorem B1774275 : Blo 1774088 1774275 := bstep (se 1 (by rfl) ⟨1330706, by rfl⟩ : syracuseStep 1774275 = 2661413) B2661413
theorem B3994307 : Blo 1774088 3994307 := bstep (se 1 (by rfl) ⟨2995730, by rfl⟩ : syracuseStep 3994307 = 5991461) B5991461
theorem B2527939 : Blo 1774088 2527939 := bstep (se 1 (by rfl) ⟨1895954, by rfl⟩ : syracuseStep 2527939 = 3791909) B3791909
theorem B1774291 : Blo 1774088 1774291 := bstep (se 1 (by rfl) ⟨1330718, by rfl⟩ : syracuseStep 1774291 = 2661437) B2661437
theorem B1774307 : Blo 1774088 1774307 := bstep (se 1 (by rfl) ⟨1330730, by rfl⟩ : syracuseStep 1774307 = 2661461) B2661461
theorem B4797155 : Blo 1774088 4797155 := bstep (se 1 (by rfl) ⟨3597866, by rfl⟩ : syracuseStep 4797155 = 7195733) B7195733
theorem B1774323 : Blo 1774088 1774323 := bstep (se 1 (by rfl) ⟨1330742, by rfl⟩ : syracuseStep 1774323 = 2661485) B2661485
theorem B1774339 : Blo 1774088 1774339 := bstep (se 1 (by rfl) ⟨1330754, by rfl⟩ : syracuseStep 1774339 = 2661509) B2661509
theorem B2994961 : Blo 1774088 2994961 := bstep (se 2 (by rfl) ⟨1123110, by rfl⟩ : syracuseStep 2994961 = 2246221) B2246221
theorem B1774355 : Blo 1774088 1774355 := bstep (se 1 (by rfl) ⟨1330766, by rfl⟩ : syracuseStep 1774355 = 2661533) B2661533
theorem B1774371 : Blo 1774088 1774371 := bstep (se 1 (by rfl) ⟨1330778, by rfl⟩ : syracuseStep 1774371 = 2661557) B2661557
theorem B8098595 : Blo 1774088 8098595 := bstep (se 1 (by rfl) ⟨6073946, by rfl⟩ : syracuseStep 8098595 = 12147893) B12147893
theorem B4264753 : Blo 1774088 4264753 := bstep (se 2 (by rfl) ⟨1599282, by rfl⟩ : syracuseStep 4264753 = 3198565) B3198565
theorem B1774387 : Blo 1774088 1774387 := bstep (se 1 (by rfl) ⟨1330790, by rfl⟩ : syracuseStep 1774387 = 2661581) B2661581
theorem B2994995 : Blo 1774088 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B1774403 : Blo 1774088 1774403 := bstep (se 1 (by rfl) ⟨1330802, by rfl⟩ : syracuseStep 1774403 = 2661605) B2661605
theorem B4797265 : Blo 1774088 4797265 := bstep (se 2 (by rfl) ⟨1798974, by rfl⟩ : syracuseStep 4797265 = 3597949) B3597949
theorem B5993297 : Blo 1774088 5993297 := bstep (se 2 (by rfl) ⟨2247486, by rfl⟩ : syracuseStep 5993297 = 4494973) B4494973
theorem B1774419 : Blo 1774088 1774419 := bstep (se 1 (by rfl) ⟨1330814, by rfl⟩ : syracuseStep 1774419 = 2661629) B2661629
theorem B1774435 : Blo 1774088 1774435 := bstep (se 1 (by rfl) ⟨1330826, by rfl⟩ : syracuseStep 1774435 = 2661653) B2661653
theorem B1774451 : Blo 1774088 1774451 := bstep (se 1 (by rfl) ⟨1330838, by rfl⟩ : syracuseStep 1774451 = 2661677) B2661677
theorem B1774467 : Blo 1774088 1774467 := bstep (se 1 (by rfl) ⟨1330850, by rfl⟩ : syracuseStep 1774467 = 2661701) B2661701
theorem B1774483 : Blo 1774088 1774483 := bstep (se 1 (by rfl) ⟨1330862, by rfl⟩ : syracuseStep 1774483 = 2661725) B2661725
theorem B1774499 : Blo 1774088 1774499 := bstep (se 1 (by rfl) ⟨1330874, by rfl⟩ : syracuseStep 1774499 = 2661749) B2661749
theorem B1774515 : Blo 1774088 1774515 := bstep (se 1 (by rfl) ⟨1330886, by rfl⟩ : syracuseStep 1774515 = 2661773) B2661773
theorem B2995123 : Blo 1774088 2995123 := bstep (se 1 (by rfl) ⟨2246342, by rfl⟩ : syracuseStep 2995123 = 4492685) B4492685
theorem B3077057 : Blo 1774088 3077057 := bstep (se 2 (by rfl) ⟨1153896, by rfl⟩ : syracuseStep 3077057 = 2307793) B2307793
theorem B1774531 : Blo 1774088 1774531 := bstep (se 1 (by rfl) ⟨1330898, by rfl⟩ : syracuseStep 1774531 = 2661797) B2661797
theorem B4494275 : Blo 1774088 4494275 := bstep (se 1 (by rfl) ⟨3370706, by rfl⟩ : syracuseStep 4494275 = 6741413) B6741413
theorem B3994577 : Blo 1774088 3994577 := bstep (se 2 (by rfl) ⟨1497966, by rfl⟩ : syracuseStep 3994577 = 2995933) B2995933
theorem B1774547 : Blo 1774088 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B1774563 : Blo 1774088 1774563 := bstep (se 1 (by rfl) ⟨1330922, by rfl⟩ : syracuseStep 1774563 = 2661845) B2661845
theorem B3994595 : Blo 1774088 3994595 := bstep (se 1 (by rfl) ⟨2995946, by rfl⟩ : syracuseStep 3994595 = 5991893) B5991893
theorem B1774579 : Blo 1774088 1774579 := bstep (se 1 (by rfl) ⟨1330934, by rfl⟩ : syracuseStep 1774579 = 2661869) B2661869
theorem B1774595 : Blo 1774088 1774595 := bstep (se 1 (by rfl) ⟨1330946, by rfl⟩ : syracuseStep 1774595 = 2661893) B2661893
theorem B6927373 : Blo 1774088 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B1774611 : Blo 1774088 1774611 := bstep (se 1 (by rfl) ⟨1330958, by rfl⟩ : syracuseStep 1774611 = 2661917) B2661917
theorem B2528275 : Blo 1774088 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B1774627 : Blo 1774088 1774627 := bstep (se 1 (by rfl) ⟨1330970, by rfl⟩ : syracuseStep 1774627 = 2661941) B2661941
theorem B1774643 : Blo 1774088 1774643 := bstep (se 1 (by rfl) ⟨1330982, by rfl⟩ : syracuseStep 1774643 = 2661965) B2661965
theorem B2995265 : Blo 1774088 2995265 := bstep (se 2 (by rfl) ⟨1123224, by rfl⟩ : syracuseStep 2995265 = 2246449) B2246449
theorem B1774659 : Blo 1774088 1774659 := bstep (se 1 (by rfl) ⟨1330994, by rfl⟩ : syracuseStep 1774659 = 2661989) B2661989
theorem B1774675 : Blo 1774088 1774675 := bstep (se 1 (by rfl) ⟨1331006, by rfl⟩ : syracuseStep 1774675 = 2662013) B2662013
theorem B1774691 : Blo 1774088 1774691 := bstep (se 1 (by rfl) ⟨1331018, by rfl⟩ : syracuseStep 1774691 = 2662037) B2662037
theorem B1774707 : Blo 1774088 1774707 := bstep (se 1 (by rfl) ⟨1331030, by rfl⟩ : syracuseStep 1774707 = 2662061) B2662061
theorem B1995907 : Blo 1774088 1995907 := bstep (se 1 (by rfl) ⟨1496930, by rfl⟩ : syracuseStep 1995907 = 2993861) B2993861
theorem B1774723 : Blo 1774088 1774723 := bstep (se 1 (by rfl) ⟨1331042, by rfl⟩ : syracuseStep 1774723 = 2662085) B2662085
theorem B4494467 : Blo 1774088 4494467 := bstep (se 1 (by rfl) ⟨3370850, by rfl⟩ : syracuseStep 4494467 = 6741701) B6741701
theorem B1774739 : Blo 1774088 1774739 := bstep (se 1 (by rfl) ⟨1331054, by rfl⟩ : syracuseStep 1774739 = 2662109) B2662109
theorem B1774755 : Blo 1774088 1774755 := bstep (se 1 (by rfl) ⟨1331066, by rfl⟩ : syracuseStep 1774755 = 2662133) B2662133
theorem B2880689 : Blo 1774088 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B1774771 : Blo 1774088 1774771 := bstep (se 1 (by rfl) ⟨1331078, by rfl⟩ : syracuseStep 1774771 = 2662157) B2662157
theorem B2995393 : Blo 1774088 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B1774787 : Blo 1774088 1774787 := bstep (se 1 (by rfl) ⟨1331090, by rfl⟩ : syracuseStep 1774787 = 2662181) B2662181
theorem B1774803 : Blo 1774088 1774803 := bstep (se 1 (by rfl) ⟨1331102, by rfl⟩ : syracuseStep 1774803 = 2662205) B2662205
theorem B1774819 : Blo 1774088 1774819 := bstep (se 1 (by rfl) ⟨1331114, by rfl⟩ : syracuseStep 1774819 = 2662229) B2662229
theorem B2995427 : Blo 1774088 2995427 := bstep (se 1 (by rfl) ⟨2246570, by rfl⟩ : syracuseStep 2995427 = 4493141) B4493141
theorem B3994865 : Blo 1774088 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B1774835 : Blo 1774088 1774835 := bstep (se 1 (by rfl) ⟨1331126, by rfl⟩ : syracuseStep 1774835 = 2662253) B2662253
theorem B1774851 : Blo 1774088 1774851 := bstep (se 1 (by rfl) ⟨1331138, by rfl⟩ : syracuseStep 1774851 = 2662277) B2662277
theorem B3994883 : Blo 1774088 3994883 := bstep (se 1 (by rfl) ⟨2996162, by rfl⟩ : syracuseStep 3994883 = 5992325) B5992325
theorem B1996051 : Blo 1774088 1996051 := bstep (se 1 (by rfl) ⟨1497038, by rfl⟩ : syracuseStep 1996051 = 2994077) B2994077
theorem B1774867 : Blo 1774088 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1774883 : Blo 1774088 1774883 := bstep (se 1 (by rfl) ⟨1331162, by rfl⟩ : syracuseStep 1774883 = 2662325) B2662325
theorem B1774899 : Blo 1774088 1774899 := bstep (se 1 (by rfl) ⟨1331174, by rfl⟩ : syracuseStep 1774899 = 2662349) B2662349
theorem B1774915 : Blo 1774088 1774915 := bstep (se 1 (by rfl) ⟨1331186, by rfl⟩ : syracuseStep 1774915 = 2662373) B2662373
theorem B1774931 : Blo 1774088 1774931 := bstep (se 1 (by rfl) ⟨1331198, by rfl⟩ : syracuseStep 1774931 = 2662397) B2662397
theorem B1774947 : Blo 1774088 1774947 := bstep (se 1 (by rfl) ⟨1331210, by rfl⟩ : syracuseStep 1774947 = 2662421) B2662421
theorem B2995555 : Blo 1774088 2995555 := bstep (se 1 (by rfl) ⟨2246666, by rfl⟩ : syracuseStep 2995555 = 4493333) B4493333
theorem B5993837 : Blo 1774088 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B1774963 : Blo 1774088 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B1774979 : Blo 1774088 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B5395853 : Blo 1774088 5395853 := bstep (se 3 (by rfl) ⟨1011722, by rfl⟩ : syracuseStep 5395853 = 2023445) B2023445
theorem B1774995 : Blo 1774088 1774995 := bstep (se 1 (by rfl) ⟨1331246, by rfl⟩ : syracuseStep 1774995 = 2662493) B2662493
theorem B1996195 : Blo 1774088 1996195 := bstep (se 1 (by rfl) ⟨1497146, by rfl⟩ : syracuseStep 1996195 = 2994293) B2994293
theorem B1775011 : Blo 1774088 1775011 := bstep (se 1 (by rfl) ⟨1331258, by rfl⟩ : syracuseStep 1775011 = 2662517) B2662517
theorem B5993891 : Blo 1774088 5993891 := bstep (se 1 (by rfl) ⟨4495418, by rfl⟩ : syracuseStep 5993891 = 8990837) B8990837
theorem B1775027 : Blo 1774088 1775027 := bstep (se 1 (by rfl) ⟨1331270, by rfl⟩ : syracuseStep 1775027 = 2662541) B2662541
theorem B1775043 : Blo 1774088 1775043 := bstep (se 1 (by rfl) ⟨1331282, by rfl⟩ : syracuseStep 1775043 = 2662565) B2662565
theorem B10106309 : Blo 1774088 10106309 := bstep (se 4 (by rfl) ⟨947466, by rfl⟩ : syracuseStep 10106309 = 1894933) B1894933
theorem B1775059 : Blo 1774088 1775059 := bstep (se 1 (by rfl) ⟨1331294, by rfl⟩ : syracuseStep 1775059 = 2662589) B2662589
theorem B1775075 : Blo 1774088 1775075 := bstep (se 1 (by rfl) ⟨1331306, by rfl⟩ : syracuseStep 1775075 = 2662613) B2662613
theorem B2995697 : Blo 1774088 2995697 := bstep (se 2 (by rfl) ⟨1123386, by rfl⟩ : syracuseStep 2995697 = 2246773) B2246773
theorem B1775091 : Blo 1774088 1775091 := bstep (se 1 (by rfl) ⟨1331318, by rfl⟩ : syracuseStep 1775091 = 2662637) B2662637
theorem B1775107 : Blo 1774088 1775107 := bstep (se 1 (by rfl) ⟨1331330, by rfl⟩ : syracuseStep 1775107 = 2662661) B2662661
theorem B6739469 : Blo 1774088 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B3995153 : Blo 1774088 3995153 := bstep (se 2 (by rfl) ⟨1498182, by rfl⟩ : syracuseStep 3995153 = 2996365) B2996365
theorem B1775123 : Blo 1774088 1775123 := bstep (se 1 (by rfl) ⟨1331342, by rfl⟩ : syracuseStep 1775123 = 2662685) B2662685
theorem B1775139 : Blo 1774088 1775139 := bstep (se 1 (by rfl) ⟨1331354, by rfl⟩ : syracuseStep 1775139 = 2662709) B2662709
theorem B3995171 : Blo 1774088 3995171 := bstep (se 1 (by rfl) ⟨2996378, by rfl⟩ : syracuseStep 3995171 = 5992757) B5992757
theorem B1996339 : Blo 1774088 1996339 := bstep (se 1 (by rfl) ⟨1497254, by rfl⟩ : syracuseStep 1996339 = 2994509) B2994509
theorem B1775155 : Blo 1774088 1775155 := bstep (se 1 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 1775155 = 2662733) B2662733
theorem B2528833 : Blo 1774088 2528833 := bstep (se 2 (by rfl) ⟨948312, by rfl⟩ : syracuseStep 2528833 = 1896625) B1896625
theorem B1775171 : Blo 1774088 1775171 := bstep (se 1 (by rfl) ⟨1331378, by rfl⟩ : syracuseStep 1775171 = 2662757) B2662757
theorem B1775187 : Blo 1774088 1775187 := bstep (se 1 (by rfl) ⟨1331390, by rfl⟩ : syracuseStep 1775187 = 2662781) B2662781
theorem B1775203 : Blo 1774088 1775203 := bstep (se 1 (by rfl) ⟨1331402, by rfl⟩ : syracuseStep 1775203 = 2662805) B2662805
theorem B2995825 : Blo 1774088 2995825 := bstep (se 2 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 2995825 = 2246869) B2246869
theorem B1775219 : Blo 1774088 1775219 := bstep (se 1 (by rfl) ⟨1331414, by rfl⟩ : syracuseStep 1775219 = 2662829) B2662829
theorem B1775235 : Blo 1774088 1775235 := bstep (se 1 (by rfl) ⟨1331426, by rfl⟩ : syracuseStep 1775235 = 2662853) B2662853
theorem B3790481 : Blo 1774088 3790481 := bstep (se 2 (by rfl) ⟨1421430, by rfl⟩ : syracuseStep 3790481 = 2842861) B2842861
theorem B1775251 : Blo 1774088 1775251 := bstep (se 1 (by rfl) ⟨1331438, by rfl⟩ : syracuseStep 1775251 = 2662877) B2662877
theorem B2995859 : Blo 1774088 2995859 := bstep (se 1 (by rfl) ⟨2246894, by rfl⟩ : syracuseStep 2995859 = 4493789) B4493789
theorem B1775267 : Blo 1774088 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B5994161 : Blo 1774088 5994161 := bstep (se 2 (by rfl) ⟨2247810, by rfl⟩ : syracuseStep 5994161 = 4495621) B4495621
theorem B1775283 : Blo 1774088 1775283 := bstep (se 1 (by rfl) ⟨1331462, by rfl⟩ : syracuseStep 1775283 = 2662925) B2662925
theorem B1996483 : Blo 1774088 1996483 := bstep (se 1 (by rfl) ⟨1497362, by rfl⟩ : syracuseStep 1996483 = 2994725) B2994725
theorem B1775299 : Blo 1774088 1775299 := bstep (se 1 (by rfl) ⟨1331474, by rfl⟩ : syracuseStep 1775299 = 2662949) B2662949
theorem B1775315 : Blo 1774088 1775315 := bstep (se 1 (by rfl) ⟨1331486, by rfl⟩ : syracuseStep 1775315 = 2662973) B2662973
theorem B11368163 : Blo 1774088 11368163 := bstep (se 1 (by rfl) ⟨8526122, by rfl⟩ : syracuseStep 11368163 = 17052245) B17052245
theorem B1775331 : Blo 1774088 1775331 := bstep (se 1 (by rfl) ⟨1331498, by rfl⟩ : syracuseStep 1775331 = 2662997) B2662997
theorem B1775347 : Blo 1774088 1775347 := bstep (se 1 (by rfl) ⟨1331510, by rfl⟩ : syracuseStep 1775347 = 2663021) B2663021
theorem B1775363 : Blo 1774088 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B1775379 : Blo 1774088 1775379 := bstep (se 1 (by rfl) ⟨1331534, by rfl⟩ : syracuseStep 1775379 = 2663069) B2663069
theorem B2995987 : Blo 1774088 2995987 := bstep (se 1 (by rfl) ⟨2246990, by rfl⟩ : syracuseStep 2995987 = 4493981) B4493981
theorem B1775395 : Blo 1774088 1775395 := bstep (se 1 (by rfl) ⟨1331546, by rfl⟩ : syracuseStep 1775395 = 2663093) B2663093
theorem B8533795 : Blo 1774088 8533795 := bstep (se 1 (by rfl) ⟨6400346, by rfl⟩ : syracuseStep 8533795 = 12800693) B12800693
theorem B5125933 : Blo 1774088 5125933 := bstep (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) B1922225
theorem B3995441 : Blo 1774088 3995441 := bstep (se 2 (by rfl) ⟨1498290, by rfl⟩ : syracuseStep 3995441 = 2996581) B2996581
theorem B1775411 : Blo 1774088 1775411 := bstep (se 1 (by rfl) ⟨1331558, by rfl⟩ : syracuseStep 1775411 = 2663117) B2663117
theorem B1775427 : Blo 1774088 1775427 := bstep (se 1 (by rfl) ⟨1331570, by rfl⟩ : syracuseStep 1775427 = 2663141) B2663141
theorem B3995459 : Blo 1774088 3995459 := bstep (se 1 (by rfl) ⟨2996594, by rfl⟩ : syracuseStep 3995459 = 5993189) B5993189
theorem B8525645 : Blo 1774088 8525645 := bstep (se 3 (by rfl) ⟨1598558, by rfl⟩ : syracuseStep 8525645 = 3197117) B3197117
theorem B1996627 : Blo 1774088 1996627 := bstep (se 1 (by rfl) ⟨1497470, by rfl⟩ : syracuseStep 1996627 = 2994941) B2994941
theorem B1775443 : Blo 1774088 1775443 := bstep (se 1 (by rfl) ⟨1331582, by rfl⟩ : syracuseStep 1775443 = 2663165) B2663165
theorem B1775459 : Blo 1774088 1775459 := bstep (se 1 (by rfl) ⟨1331594, by rfl⟩ : syracuseStep 1775459 = 2663189) B2663189
theorem B1775475 : Blo 1774088 1775475 := bstep (se 1 (by rfl) ⟨1331606, by rfl⟩ : syracuseStep 1775475 = 2663213) B2663213
theorem B1775491 : Blo 1774088 1775491 := bstep (se 1 (by rfl) ⟨1331618, by rfl⟩ : syracuseStep 1775491 = 2663237) B2663237
theorem B10106765 : Blo 1774088 10106765 := bstep (se 3 (by rfl) ⟨1895018, by rfl⟩ : syracuseStep 10106765 = 3790037) B3790037
theorem B2398097 : Blo 1774088 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B1775507 : Blo 1774088 1775507 := bstep (se 1 (by rfl) ⟨1331630, by rfl⟩ : syracuseStep 1775507 = 2663261) B2663261
theorem B2996129 : Blo 1774088 2996129 := bstep (se 2 (by rfl) ⟨1123548, by rfl⟩ : syracuseStep 2996129 = 2247097) B2247097
theorem B1775523 : Blo 1774088 1775523 := bstep (se 1 (by rfl) ⟨1331642, by rfl⟩ : syracuseStep 1775523 = 2663285) B2663285
theorem B1775539 : Blo 1774088 1775539 := bstep (se 1 (by rfl) ⟨1331654, by rfl⟩ : syracuseStep 1775539 = 2663309) B2663309
theorem B1824691 : Blo 1774088 1824691 := bstep (se 1 (by rfl) ⟨1368518, by rfl⟩ : syracuseStep 1824691 = 2737037) B2737037
theorem B1775555 : Blo 1774088 1775555 := bstep (se 1 (by rfl) ⟨1331666, by rfl⟩ : syracuseStep 1775555 = 2663333) B2663333
theorem B1775571 : Blo 1774088 1775571 := bstep (se 1 (by rfl) ⟨1331678, by rfl⟩ : syracuseStep 1775571 = 2663357) B2663357
theorem B1996771 : Blo 1774088 1996771 := bstep (se 1 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 1996771 = 2995157) B2995157
theorem B1775587 : Blo 1774088 1775587 := bstep (se 1 (by rfl) ⟨1331690, by rfl⟩ : syracuseStep 1775587 = 2663381) B2663381
theorem B10115057 : Blo 1774088 10115057 := bstep (se 2 (by rfl) ⟨3793146, by rfl⟩ : syracuseStep 10115057 = 7586293) B7586293
theorem B1775603 : Blo 1774088 1775603 := bstep (se 1 (by rfl) ⟨1331702, by rfl⟩ : syracuseStep 1775603 = 2663405) B2663405
theorem B1775619 : Blo 1774088 1775619 := bstep (se 1 (by rfl) ⟨1331714, by rfl⟩ : syracuseStep 1775619 = 2663429) B2663429
theorem B1775635 : Blo 1774088 1775635 := bstep (se 1 (by rfl) ⟨1331726, by rfl⟩ : syracuseStep 1775635 = 2663453) B2663453
theorem B2996257 : Blo 1774088 2996257 := bstep (se 2 (by rfl) ⟨1123596, by rfl⟩ : syracuseStep 2996257 = 2247193) B2247193
theorem B1775651 : Blo 1774088 1775651 := bstep (se 1 (by rfl) ⟨1331738, by rfl⟩ : syracuseStep 1775651 = 2663477) B2663477
theorem B4495409 : Blo 1774088 4495409 := bstep (se 2 (by rfl) ⟨1685778, by rfl⟩ : syracuseStep 4495409 = 3371557) B3371557
theorem B1775667 : Blo 1774088 1775667 := bstep (se 1 (by rfl) ⟨1331750, by rfl⟩ : syracuseStep 1775667 = 2663501) B2663501
theorem B2996291 : Blo 1774088 2996291 := bstep (se 1 (by rfl) ⟨2247218, by rfl⟩ : syracuseStep 2996291 = 4494437) B4494437
theorem B1775683 : Blo 1774088 1775683 := bstep (se 1 (by rfl) ⟨1331762, by rfl⟩ : syracuseStep 1775683 = 2663525) B2663525
theorem B3995729 : Blo 1774088 3995729 := bstep (se 2 (by rfl) ⟨1498398, by rfl⟩ : syracuseStep 3995729 = 2996797) B2996797
theorem B1775699 : Blo 1774088 1775699 := bstep (se 1 (by rfl) ⟨1331774, by rfl⟩ : syracuseStep 1775699 = 2663549) B2663549
theorem B1775715 : Blo 1774088 1775715 := bstep (se 1 (by rfl) ⟨1331786, by rfl⟩ : syracuseStep 1775715 = 2663573) B2663573
theorem B3995747 : Blo 1774088 3995747 := bstep (se 1 (by rfl) ⟨2996810, by rfl⟩ : syracuseStep 3995747 = 5993621) B5993621
theorem B4495459 : Blo 1774088 4495459 := bstep (se 1 (by rfl) ⟨3371594, by rfl⟩ : syracuseStep 4495459 = 6743189) B6743189
theorem B1996915 : Blo 1774088 1996915 := bstep (se 1 (by rfl) ⟨1497686, by rfl⟩ : syracuseStep 1996915 = 2995373) B2995373
theorem B1775731 : Blo 1774088 1775731 := bstep (se 1 (by rfl) ⟨1331798, by rfl⟩ : syracuseStep 1775731 = 2663597) B2663597
theorem B1775747 : Blo 1774088 1775747 := bstep (se 1 (by rfl) ⟨1331810, by rfl⟩ : syracuseStep 1775747 = 2663621) B2663621
theorem B13482125 : Blo 1774088 13482125 := bstep (se 3 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 13482125 = 5055797) B5055797
theorem B1775763 : Blo 1774088 1775763 := bstep (se 1 (by rfl) ⟨1331822, by rfl⟩ : syracuseStep 1775763 = 2663645) B2663645
theorem B1775779 : Blo 1774088 1775779 := bstep (se 1 (by rfl) ⟨1331834, by rfl⟩ : syracuseStep 1775779 = 2663669) B2663669
theorem B9599153 : Blo 1774088 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B8100017 : Blo 1774088 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B1775795 : Blo 1774088 1775795 := bstep (se 1 (by rfl) ⟨1331846, by rfl⟩ : syracuseStep 1775795 = 2663693) B2663693
theorem B2996419 : Blo 1774088 2996419 := bstep (se 1 (by rfl) ⟨2247314, by rfl⟩ : syracuseStep 2996419 = 4494629) B4494629
theorem B1775811 : Blo 1774088 1775811 := bstep (se 1 (by rfl) ⟨1331858, by rfl⟩ : syracuseStep 1775811 = 2663717) B2663717
theorem B1775827 : Blo 1774088 1775827 := bstep (se 1 (by rfl) ⟨1331870, by rfl⟩ : syracuseStep 1775827 = 2663741) B2663741
theorem B1775843 : Blo 1774088 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B4495601 : Blo 1774088 4495601 := bstep (se 2 (by rfl) ⟨1685850, by rfl⟩ : syracuseStep 4495601 = 3371701) B3371701
theorem B1775859 : Blo 1774088 1775859 := bstep (se 1 (by rfl) ⟨1331894, by rfl⟩ : syracuseStep 1775859 = 2663789) B2663789
theorem B1997059 : Blo 1774088 1997059 := bstep (se 1 (by rfl) ⟨1497794, by rfl⟩ : syracuseStep 1997059 = 2995589) B2995589
theorem B1775875 : Blo 1774088 1775875 := bstep (se 1 (by rfl) ⟨1331906, by rfl⟩ : syracuseStep 1775875 = 2663813) B2663813
theorem B5052689 : Blo 1774088 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B1775891 : Blo 1774088 1775891 := bstep (se 1 (by rfl) ⟨1331918, by rfl⟩ : syracuseStep 1775891 = 2663837) B2663837
theorem B1775907 : Blo 1774088 1775907 := bstep (se 1 (by rfl) ⟨1331930, by rfl⟩ : syracuseStep 1775907 = 2663861) B2663861
theorem B6740273 : Blo 1774088 6740273 := bstep (se 2 (by rfl) ⟨2527602, by rfl⟩ : syracuseStep 6740273 = 5055205) B5055205
theorem B1775923 : Blo 1774088 1775923 := bstep (se 1 (by rfl) ⟨1331942, by rfl⟩ : syracuseStep 1775923 = 2663885) B2663885
theorem B1775939 : Blo 1774088 1775939 := bstep (se 1 (by rfl) ⟨1331954, by rfl⟩ : syracuseStep 1775939 = 2663909) B2663909
theorem B9599309 : Blo 1774088 9599309 := bstep (se 3 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 9599309 = 3599741) B3599741
theorem B2996561 : Blo 1774088 2996561 := bstep (se 2 (by rfl) ⟨1123710, by rfl⟩ : syracuseStep 2996561 = 2247421) B2247421
theorem B1775955 : Blo 1774088 1775955 := bstep (se 1 (by rfl) ⟨1331966, by rfl⟩ : syracuseStep 1775955 = 2663933) B2663933
theorem B1775971 : Blo 1774088 1775971 := bstep (se 1 (by rfl) ⟨1331978, by rfl⟩ : syracuseStep 1775971 = 2663957) B2663957
theorem B3996017 : Blo 1774088 3996017 := bstep (se 2 (by rfl) ⟨1498506, by rfl⟩ : syracuseStep 3996017 = 2997013) B2997013
theorem B1775987 : Blo 1774088 1775987 := bstep (se 1 (by rfl) ⟨1331990, by rfl⟩ : syracuseStep 1775987 = 2663981) B2663981
theorem B2881921 : Blo 1774088 2881921 := bstep (se 2 (by rfl) ⟨1080720, by rfl⟩ : syracuseStep 2881921 = 2161441) B2161441
theorem B1776003 : Blo 1774088 1776003 := bstep (se 1 (by rfl) ⟨1332002, by rfl⟩ : syracuseStep 1776003 = 2664005) B2664005
theorem B3996035 : Blo 1774088 3996035 := bstep (se 1 (by rfl) ⟨2997026, by rfl⟩ : syracuseStep 3996035 = 5994053) B5994053
theorem B1997203 : Blo 1774088 1997203 := bstep (se 1 (by rfl) ⟨1497902, by rfl⟩ : syracuseStep 1997203 = 2995805) B2995805
theorem B1776019 : Blo 1774088 1776019 := bstep (se 1 (by rfl) ⟨1332014, by rfl⟩ : syracuseStep 1776019 = 2664029) B2664029
theorem B1776035 : Blo 1774088 1776035 := bstep (se 1 (by rfl) ⟨1332026, by rfl⟩ : syracuseStep 1776035 = 2664053) B2664053
theorem B1776051 : Blo 1774088 1776051 := bstep (se 1 (by rfl) ⟨1332038, by rfl⟩ : syracuseStep 1776051 = 2664077) B2664077
theorem B1776067 : Blo 1774088 1776067 := bstep (se 1 (by rfl) ⟨1332050, by rfl⟩ : syracuseStep 1776067 = 2664101) B2664101
theorem B5052881 : Blo 1774088 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B2996689 : Blo 1774088 2996689 := bstep (se 2 (by rfl) ⟨1123758, by rfl⟩ : syracuseStep 2996689 = 2247517) B2247517
theorem B1776083 : Blo 1774088 1776083 := bstep (se 1 (by rfl) ⟨1332062, by rfl⟩ : syracuseStep 1776083 = 2664125) B2664125
theorem B2996723 : Blo 1774088 2996723 := bstep (se 1 (by rfl) ⟨2247542, by rfl⟩ : syracuseStep 2996723 = 4495085) B4495085
theorem B1997347 : Blo 1774088 1997347 := bstep (se 1 (by rfl) ⟨1498010, by rfl⟩ : syracuseStep 1997347 = 2996021) B2996021
theorem B2996851 : Blo 1774088 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B1997491 : Blo 1774088 1997491 := bstep (se 1 (by rfl) ⟨1498118, by rfl⟩ : syracuseStep 1997491 = 2996237) B2996237
theorem B8985329 : Blo 1774088 8985329 := bstep (se 2 (by rfl) ⟨3369498, by rfl⟩ : syracuseStep 8985329 = 6738997) B6738997
theorem B2996993 : Blo 1774088 2996993 := bstep (se 2 (by rfl) ⟨1123872, by rfl⟩ : syracuseStep 2996993 = 2247745) B2247745
theorem B2661137 : Blo 1774088 2661137 := bstep (se 2 (by rfl) ⟨997926, by rfl⟩ : syracuseStep 2661137 = 1995853) B1995853
theorem B2661155 : Blo 1774088 2661155 := bstep (se 1 (by rfl) ⟨1995866, by rfl⟩ : syracuseStep 2661155 = 3991733) B3991733
theorem B2595619 : Blo 1774088 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B2661185 : Blo 1774088 2661185 := bstep (se 2 (by rfl) ⟨997944, by rfl⟩ : syracuseStep 2661185 = 1995889) B1995889
theorem B1997635 : Blo 1774088 1997635 := bstep (se 1 (by rfl) ⟨1498226, by rfl⟩ : syracuseStep 1997635 = 2996453) B2996453
theorem B2661203 : Blo 1774088 2661203 := bstep (se 1 (by rfl) ⟨1995902, by rfl⟩ : syracuseStep 2661203 = 3991805) B3991805
theorem B4799341 : Blo 1774088 4799341 := bstep (se 3 (by rfl) ⟨899876, by rfl⟩ : syracuseStep 4799341 = 1799753) B1799753
theorem B2661233 : Blo 1774088 2661233 := bstep (se 2 (by rfl) ⟨997962, by rfl⟩ : syracuseStep 2661233 = 1995925) B1995925
theorem B2997121 : Blo 1774088 2997121 := bstep (se 2 (by rfl) ⟨1123920, by rfl⟩ : syracuseStep 2997121 = 2247841) B2247841
theorem B2661251 : Blo 1774088 2661251 := bstep (se 1 (by rfl) ⟨1995938, by rfl⟩ : syracuseStep 2661251 = 3991877) B3991877
theorem B36436877 : Blo 1774088 36436877 := bstep (se 3 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 36436877 = 13663829) B13663829
theorem B7584653 : Blo 1774088 7584653 := bstep (se 3 (by rfl) ⟨1422122, by rfl⟩ : syracuseStep 7584653 = 2844245) B2844245
theorem B2661281 : Blo 1774088 2661281 := bstep (se 2 (by rfl) ⟨997980, by rfl⟩ : syracuseStep 2661281 = 1995961) B1995961
theorem B4799405 : Blo 1774088 4799405 := bstep (se 3 (by rfl) ⟨899888, by rfl⟩ : syracuseStep 4799405 = 1799777) B1799777
theorem B11369393 : Blo 1774088 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B2661299 : Blo 1774088 2661299 := bstep (se 1 (by rfl) ⟨1995974, by rfl⟩ : syracuseStep 2661299 = 3991949) B3991949
theorem B6740941 : Blo 1774088 6740941 := bstep (se 3 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 6740941 = 2527853) B2527853
theorem B2661329 : Blo 1774088 2661329 := bstep (se 2 (by rfl) ⟨997998, by rfl⟩ : syracuseStep 2661329 = 1995997) B1995997
theorem B1997779 : Blo 1774088 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B2661347 : Blo 1774088 2661347 := bstep (se 1 (by rfl) ⟨1996010, by rfl⟩ : syracuseStep 2661347 = 3992021) B3992021
theorem B17054705 : Blo 1774088 17054705 := bstep (se 2 (by rfl) ⟨6395514, by rfl⟩ : syracuseStep 17054705 = 12791029) B12791029
theorem B2661377 : Blo 1774088 2661377 := bstep (se 2 (by rfl) ⟨998016, by rfl⟩ : syracuseStep 2661377 = 1996033) B1996033
theorem B2661395 : Blo 1774088 2661395 := bstep (se 1 (by rfl) ⟨1996046, by rfl⟩ : syracuseStep 2661395 = 3992093) B3992093
theorem B2661425 : Blo 1774088 2661425 := bstep (se 2 (by rfl) ⟨998034, by rfl⟩ : syracuseStep 2661425 = 1996069) B1996069
theorem B21593141 : Blo 1774088 21593141 := bstep (se 5 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 21593141 = 2024357) B2024357
theorem B2661443 : Blo 1774088 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B4799569 : Blo 1774088 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B2661473 : Blo 1774088 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B1997923 : Blo 1774088 1997923 := bstep (se 1 (by rfl) ⟨1498442, by rfl⟩ : syracuseStep 1997923 = 2996885) B2996885
theorem B2661491 : Blo 1774088 2661491 := bstep (se 1 (by rfl) ⟨1996118, by rfl⟩ : syracuseStep 2661491 = 3992237) B3992237
theorem B2661521 : Blo 1774088 2661521 := bstep (se 2 (by rfl) ⟨998070, by rfl⟩ : syracuseStep 2661521 = 1996141) B1996141
theorem B2661539 : Blo 1774088 2661539 := bstep (se 1 (by rfl) ⟨1996154, by rfl⟩ : syracuseStep 2661539 = 3992309) B3992309
theorem B2841779 : Blo 1774088 2841779 := bstep (se 1 (by rfl) ⟨2131334, by rfl⟩ : syracuseStep 2841779 = 4262669) B4262669
theorem B19455157 : Blo 1774088 19455157 := bstep (se 5 (by rfl) ⟨911960, by rfl⟩ : syracuseStep 19455157 = 1823921) B1823921
theorem B2661569 : Blo 1774088 2661569 := bstep (se 2 (by rfl) ⟨998088, by rfl⟩ : syracuseStep 2661569 = 1996177) B1996177
theorem B2661587 : Blo 1774088 2661587 := bstep (se 1 (by rfl) ⟨1996190, by rfl⟩ : syracuseStep 2661587 = 3992381) B3992381
theorem B7584995 : Blo 1774088 7584995 := bstep (se 1 (by rfl) ⟨5688746, by rfl⟩ : syracuseStep 7584995 = 11377493) B11377493
theorem B2661617 : Blo 1774088 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B1998067 : Blo 1774088 1998067 := bstep (se 1 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 1998067 = 2997101) B2997101
theorem B2661635 : Blo 1774088 2661635 := bstep (se 1 (by rfl) ⟨1996226, by rfl⟩ : syracuseStep 2661635 = 3992453) B3992453
theorem B2661665 : Blo 1774088 2661665 := bstep (se 2 (by rfl) ⟨998124, by rfl⟩ : syracuseStep 2661665 = 1996249) B1996249
theorem B7200049 : Blo 1774088 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B2661683 : Blo 1774088 2661683 := bstep (se 1 (by rfl) ⟨1996262, by rfl⟩ : syracuseStep 2661683 = 3992525) B3992525
theorem B2661713 : Blo 1774088 2661713 := bstep (se 2 (by rfl) ⟨998142, by rfl⟩ : syracuseStep 2661713 = 1996285) B1996285
theorem B2661731 : Blo 1774088 2661731 := bstep (se 1 (by rfl) ⟨1996298, by rfl⟩ : syracuseStep 2661731 = 3992597) B3992597
theorem B2661761 : Blo 1774088 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B6069649 : Blo 1774088 6069649 := bstep (se 2 (by rfl) ⟨2276118, by rfl⟩ : syracuseStep 6069649 = 4552237) B4552237
theorem B2842003 : Blo 1774088 2842003 := bstep (se 1 (by rfl) ⟨2131502, by rfl⟩ : syracuseStep 2842003 = 4263005) B4263005
theorem B2661779 : Blo 1774088 2661779 := bstep (se 1 (by rfl) ⟨1996334, by rfl⟩ : syracuseStep 2661779 = 3992669) B3992669
theorem B2661809 : Blo 1774088 2661809 := bstep (se 2 (by rfl) ⟨998178, by rfl⟩ : syracuseStep 2661809 = 1996357) B1996357
theorem B5053873 : Blo 1774088 5053873 := bstep (se 2 (by rfl) ⟨1895202, by rfl⟩ : syracuseStep 5053873 = 3790405) B3790405
theorem B2661827 : Blo 1774088 2661827 := bstep (se 1 (by rfl) ⟨1996370, by rfl⟩ : syracuseStep 2661827 = 3992741) B3992741
theorem B17284549 : Blo 1774088 17284549 := bstep (se 4 (by rfl) ⟨1620426, by rfl⟩ : syracuseStep 17284549 = 3240853) B3240853
theorem B5987789 : Blo 1774088 5987789 := bstep (se 3 (by rfl) ⟨1122710, by rfl⟩ : syracuseStep 5987789 = 2245421) B2245421
theorem B2842067 : Blo 1774088 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B2661857 : Blo 1774088 2661857 := bstep (se 2 (by rfl) ⟨998196, by rfl⟩ : syracuseStep 2661857 = 1996393) B1996393
theorem B2661875 : Blo 1774088 2661875 := bstep (se 1 (by rfl) ⟨1996406, by rfl⟩ : syracuseStep 2661875 = 3992813) B3992813
theorem B5987843 : Blo 1774088 5987843 := bstep (se 1 (by rfl) ⟨4490882, by rfl⟩ : syracuseStep 5987843 = 8981765) B8981765
theorem B2661905 : Blo 1774088 2661905 := bstep (se 2 (by rfl) ⟨998214, by rfl⟩ : syracuseStep 2661905 = 1996429) B1996429
theorem B2661923 : Blo 1774088 2661923 := bstep (se 1 (by rfl) ⟨1996442, by rfl⟩ : syracuseStep 2661923 = 3992885) B3992885
theorem B4554289 : Blo 1774088 4554289 := bstep (se 2 (by rfl) ⟨1707858, by rfl⟩ : syracuseStep 4554289 = 3415717) B3415717
theorem B2661953 : Blo 1774088 2661953 := bstep (se 2 (by rfl) ⟨998232, by rfl⟩ : syracuseStep 2661953 = 1996465) B1996465
theorem B2842195 : Blo 1774088 2842195 := bstep (se 1 (by rfl) ⟨2131646, by rfl⟩ : syracuseStep 2842195 = 4263293) B4263293
theorem B2661971 : Blo 1774088 2661971 := bstep (se 1 (by rfl) ⟨1996478, by rfl⟩ : syracuseStep 2661971 = 3992957) B3992957
theorem B2662001 : Blo 1774088 2662001 := bstep (se 2 (by rfl) ⟨998250, by rfl⟩ : syracuseStep 2662001 = 1996501) B1996501
theorem B2662019 : Blo 1774088 2662019 := bstep (se 1 (by rfl) ⟨1996514, by rfl⟩ : syracuseStep 2662019 = 3993029) B3993029
theorem B4554371 : Blo 1774088 4554371 := bstep (se 1 (by rfl) ⟨3415778, by rfl⟩ : syracuseStep 4554371 = 6831557) B6831557
theorem B2662049 : Blo 1774088 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B2662067 : Blo 1774088 2662067 := bstep (se 1 (by rfl) ⟨1996550, by rfl⟩ : syracuseStep 2662067 = 3993101) B3993101
theorem B5054147 : Blo 1774088 5054147 := bstep (se 1 (by rfl) ⟨3790610, by rfl⟩ : syracuseStep 5054147 = 7581221) B7581221
theorem B2662097 : Blo 1774088 2662097 := bstep (se 2 (by rfl) ⟨998286, by rfl⟩ : syracuseStep 2662097 = 1996573) B1996573
theorem B2662115 : Blo 1774088 2662115 := bstep (se 1 (by rfl) ⟨1996586, by rfl⟩ : syracuseStep 2662115 = 3993173) B3993173
theorem B6741731 : Blo 1774088 6741731 := bstep (se 1 (by rfl) ⟨5056298, by rfl⟩ : syracuseStep 6741731 = 10112597) B10112597
theorem B2662145 : Blo 1774088 2662145 := bstep (se 2 (by rfl) ⟨998304, by rfl⟩ : syracuseStep 2662145 = 1996609) B1996609
theorem B5685005 : Blo 1774088 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B4800269 : Blo 1774088 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B5988113 : Blo 1774088 5988113 := bstep (se 2 (by rfl) ⟨2245542, by rfl⟩ : syracuseStep 5988113 = 4491085) B4491085
theorem B2662163 : Blo 1774088 2662163 := bstep (se 1 (by rfl) ⟨1996622, by rfl⟩ : syracuseStep 2662163 = 3993245) B3993245
theorem B2662193 : Blo 1774088 2662193 := bstep (se 2 (by rfl) ⟨998322, by rfl⟩ : syracuseStep 2662193 = 1996645) B1996645
theorem B2662211 : Blo 1774088 2662211 := bstep (se 1 (by rfl) ⟨1996658, by rfl⟩ : syracuseStep 2662211 = 3993317) B3993317
theorem B2662241 : Blo 1774088 2662241 := bstep (se 2 (by rfl) ⟨998340, by rfl⟩ : syracuseStep 2662241 = 1996681) B1996681
theorem B8650595 : Blo 1774088 8650595 := bstep (se 1 (by rfl) ⟨6487946, by rfl⟩ : syracuseStep 8650595 = 12975893) B12975893
theorem B2400113 : Blo 1774088 2400113 := bstep (se 2 (by rfl) ⟨900042, by rfl⟩ : syracuseStep 2400113 = 1800085) B1800085
theorem B2662259 : Blo 1774088 2662259 := bstep (se 1 (by rfl) ⟨1996694, by rfl⟩ : syracuseStep 2662259 = 3993389) B3993389
theorem B5054339 : Blo 1774088 5054339 := bstep (se 1 (by rfl) ⟨3790754, by rfl⟩ : syracuseStep 5054339 = 7581509) B7581509
theorem B17055629 : Blo 1774088 17055629 := bstep (se 3 (by rfl) ⟨3197930, by rfl⟩ : syracuseStep 17055629 = 6395861) B6395861
theorem B2662289 : Blo 1774088 2662289 := bstep (se 2 (by rfl) ⟨998358, by rfl⟩ : syracuseStep 2662289 = 1996717) B1996717
theorem B2662307 : Blo 1774088 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B2662337 : Blo 1774088 2662337 := bstep (se 2 (by rfl) ⟨998376, by rfl⟩ : syracuseStep 2662337 = 1996753) B1996753
theorem B2662355 : Blo 1774088 2662355 := bstep (se 1 (by rfl) ⟨1996766, by rfl⟩ : syracuseStep 2662355 = 3993533) B3993533
theorem B2662385 : Blo 1774088 2662385 := bstep (se 2 (by rfl) ⟨998394, by rfl⟩ : syracuseStep 2662385 = 1996789) B1996789
theorem B2662475 : Blo 1774088 2662475 := bstep (se 1 (by rfl) ⟨1996856, by rfl⟩ : syracuseStep 2662475 = 3993713) B3993713
theorem B2662487 : Blo 1774088 2662487 := bstep (se 1 (by rfl) ⟨1996865, by rfl⟩ : syracuseStep 2662487 = 3993731) B3993731
theorem B2662553 : Blo 1774088 2662553 := bstep (se 2 (by rfl) ⟨998457, by rfl⟩ : syracuseStep 2662553 = 1996915) B1996915
theorem B5988545 : Blo 1774088 5988545 := bstep (se 2 (by rfl) ⟨2245704, by rfl⟩ : syracuseStep 5988545 = 4491409) B4491409
theorem B3793139 : Blo 1774088 3793139 := bstep (se 1 (by rfl) ⟨2844854, by rfl⟩ : syracuseStep 3793139 = 5689709) B5689709
theorem B24289541 : Blo 1774088 24289541 := bstep (se 4 (by rfl) ⟨2277144, by rfl⟩ : syracuseStep 24289541 = 4554289) B4554289
theorem B2662667 : Blo 1774088 2662667 := bstep (se 1 (by rfl) ⟨1997000, by rfl⟩ : syracuseStep 2662667 = 3994001) B3994001
theorem B2662679 : Blo 1774088 2662679 := bstep (se 1 (by rfl) ⟨1997009, by rfl⟩ : syracuseStep 2662679 = 3994019) B3994019
theorem B5054795 : Blo 1774088 5054795 := bstep (se 1 (by rfl) ⟨3791096, by rfl⟩ : syracuseStep 5054795 = 7582193) B7582193
theorem B2662745 : Blo 1774088 2662745 := bstep (se 2 (by rfl) ⟨998529, by rfl⟩ : syracuseStep 2662745 = 1997059) B1997059
theorem B10797491 : Blo 1774088 10797491 := bstep (se 1 (by rfl) ⟨8098118, by rfl⟩ : syracuseStep 10797491 = 16196237) B16196237
theorem B2662859 : Blo 1774088 2662859 := bstep (se 1 (by rfl) ⟨1997144, by rfl⟩ : syracuseStep 2662859 = 3994289) B3994289
theorem B2662871 : Blo 1774088 2662871 := bstep (se 1 (by rfl) ⟨1997153, by rfl⟩ : syracuseStep 2662871 = 3994307) B3994307
theorem B3842561 : Blo 1774088 3842561 := bstep (se 2 (by rfl) ⟨1440960, by rfl⟩ : syracuseStep 3842561 = 2881921) B2881921
theorem B5399063 : Blo 1774088 5399063 := bstep (se 1 (by rfl) ⟨4049297, by rfl⟩ : syracuseStep 5399063 = 8098595) B8098595
theorem B2662937 : Blo 1774088 2662937 := bstep (se 2 (by rfl) ⟨998601, by rfl⟩ : syracuseStep 2662937 = 1997203) B1997203
theorem B8528429 : Blo 1774088 8528429 := bstep (se 3 (by rfl) ⟨1599080, by rfl⟩ : syracuseStep 8528429 = 3198161) B3198161
theorem B245998133 : Blo 1774088 245998133 := bstep (se 5 (by rfl) ⟨11531162, by rfl⟩ : syracuseStep 245998133 = 23062325) B23062325
theorem B2663051 : Blo 1774088 2663051 := bstep (se 1 (by rfl) ⟨1997288, by rfl⟩ : syracuseStep 2663051 = 3994577) B3994577
theorem B6742673 : Blo 1774088 6742673 := bstep (se 2 (by rfl) ⟨2528502, by rfl⟩ : syracuseStep 6742673 = 5057005) B5057005
theorem B2663063 : Blo 1774088 2663063 := bstep (se 1 (by rfl) ⟨1997297, by rfl⟩ : syracuseStep 2663063 = 3994595) B3994595
theorem B2663129 : Blo 1774088 2663129 := bstep (se 2 (by rfl) ⟨998673, by rfl⟩ : syracuseStep 2663129 = 1997347) B1997347
theorem B5989085 : Blo 1774088 5989085 := bstep (se 3 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 5989085 = 2245907) B2245907
theorem B2663243 : Blo 1774088 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B5473099 : Blo 1774088 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B2663255 : Blo 1774088 2663255 := bstep (se 1 (by rfl) ⟨1997441, by rfl⟩ : syracuseStep 2663255 = 3994883) B3994883
theorem B2663321 : Blo 1774088 2663321 := bstep (se 2 (by rfl) ⟨998745, by rfl⟩ : syracuseStep 2663321 = 1997491) B1997491
theorem B2663435 : Blo 1774088 2663435 := bstep (se 1 (by rfl) ⟨1997576, by rfl⟩ : syracuseStep 2663435 = 3995153) B3995153
theorem B2663447 : Blo 1774088 2663447 := bstep (se 1 (by rfl) ⟨1997585, by rfl⟩ : syracuseStep 2663447 = 3995171) B3995171
theorem B5686337 : Blo 1774088 5686337 := bstep (se 2 (by rfl) ⟨2132376, by rfl⟩ : syracuseStep 5686337 = 4264753) B4264753
theorem B2663513 : Blo 1774088 2663513 := bstep (se 2 (by rfl) ⟨998817, by rfl⟩ : syracuseStep 2663513 = 1997635) B1997635
theorem B6399121 : Blo 1774088 6399121 := bstep (se 2 (by rfl) ⟨2399670, by rfl⟩ : syracuseStep 6399121 = 4799341) B4799341
theorem B7578775 : Blo 1774088 7578775 := bstep (se 1 (by rfl) ⟨5684081, by rfl⟩ : syracuseStep 7578775 = 11368163) B11368163
theorem B2663627 : Blo 1774088 2663627 := bstep (se 1 (by rfl) ⟨1997720, by rfl⟩ : syracuseStep 2663627 = 3995441) B3995441
theorem B2663639 : Blo 1774088 2663639 := bstep (se 1 (by rfl) ⟨1997729, by rfl⟩ : syracuseStep 2663639 = 3995459) B3995459
theorem B7578845 : Blo 1774088 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B7791889 : Blo 1774088 7791889 := bstep (se 2 (by rfl) ⟨2921958, by rfl⟩ : syracuseStep 7791889 = 5843917) B5843917
theorem B8987921 : Blo 1774088 8987921 := bstep (se 2 (by rfl) ⟨3370470, by rfl⟩ : syracuseStep 8987921 = 6740941) B6740941
theorem B2663705 : Blo 1774088 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B2245963 : Blo 1774088 2245963 := bstep (se 1 (by rfl) ⟨1684472, by rfl⟩ : syracuseStep 2245963 = 3368945) B3368945
theorem B6743371 : Blo 1774088 6743371 := bstep (se 1 (by rfl) ⟨5057528, by rfl⟩ : syracuseStep 6743371 = 10115057) B10115057
theorem B2131339 : Blo 1774088 2131339 := bstep (se 1 (by rfl) ⟨1598504, by rfl⟩ : syracuseStep 2131339 = 3197009) B3197009
theorem B2663819 : Blo 1774088 2663819 := bstep (se 1 (by rfl) ⟨1997864, by rfl⟩ : syracuseStep 2663819 = 3995729) B3995729
theorem B2663831 : Blo 1774088 2663831 := bstep (se 1 (by rfl) ⟨1997873, by rfl⟩ : syracuseStep 2663831 = 3995747) B3995747
theorem B8988083 : Blo 1774088 8988083 := bstep (se 1 (by rfl) ⟨6741062, by rfl⟩ : syracuseStep 8988083 = 13482125) B13482125
theorem B6399425 : Blo 1774088 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B5400011 : Blo 1774088 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B2663897 : Blo 1774088 2663897 := bstep (se 2 (by rfl) ⟨998961, by rfl⟩ : syracuseStep 2663897 = 1997923) B1997923
theorem B3368459 : Blo 1774088 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B6399539 : Blo 1774088 6399539 := bstep (se 1 (by rfl) ⟨4799654, by rfl⟩ : syracuseStep 6399539 = 9599309) B9599309
theorem B2664011 : Blo 1774088 2664011 := bstep (se 1 (by rfl) ⟨1998008, by rfl⟩ : syracuseStep 2664011 = 3996017) B3996017
theorem B2246231 : Blo 1774088 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B2664023 : Blo 1774088 2664023 := bstep (se 1 (by rfl) ⟨1998017, by rfl⟩ : syracuseStep 2664023 = 3996035) B3996035
theorem B4490903 : Blo 1774088 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B20219543 : Blo 1774088 20219543 := bstep (se 1 (by rfl) ⟨15164657, by rfl⟩ : syracuseStep 20219543 = 30329315) B30329315
theorem B2664089 : Blo 1774088 2664089 := bstep (se 2 (by rfl) ⟨999033, by rfl⟩ : syracuseStep 2664089 = 1998067) B1998067
theorem B3368641 : Blo 1774088 3368641 := bstep (se 2 (by rfl) ⟨1263240, by rfl⟩ : syracuseStep 3368641 = 2526481) B2526481
theorem B5990219 : Blo 1774088 5990219 := bstep (se 1 (by rfl) ⟨4492664, by rfl⟩ : syracuseStep 5990219 = 8985329) B8985329
theorem B30738275 : Blo 1774088 30738275 := bstep (se 1 (by rfl) ⟨23053706, by rfl⟩ : syracuseStep 30738275 = 46107413) B46107413
theorem B23046065 : Blo 1774088 23046065 := bstep (se 2 (by rfl) ⟨8642274, by rfl⟩ : syracuseStep 23046065 = 17284549) B17284549
theorem B24291251 : Blo 1774088 24291251 := bstep (se 1 (by rfl) ⟨18218438, by rfl⟩ : syracuseStep 24291251 = 36436877) B36436877
theorem B5056435 : Blo 1774088 5056435 := bstep (se 1 (by rfl) ⟨3792326, by rfl⟩ : syracuseStep 5056435 = 7584653) B7584653
theorem B3598273 : Blo 1774088 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B7579595 : Blo 1774088 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B14395427 : Blo 1774088 14395427 := bstep (se 1 (by rfl) ⟨10796570, by rfl⟩ : syracuseStep 14395427 = 21593141) B21593141
theorem B5990489 : Blo 1774088 5990489 := bstep (se 2 (by rfl) ⟨2246433, by rfl⟩ : syracuseStep 5990489 = 4492867) B4492867
theorem B1894519 : Blo 1774088 1894519 := bstep (se 1 (by rfl) ⟨1420889, by rfl⟩ : syracuseStep 1894519 = 2841779) B2841779
theorem B3369089 : Blo 1774088 3369089 := bstep (se 2 (by rfl) ⟨1263408, by rfl⟩ : syracuseStep 3369089 = 2526817) B2526817
theorem B5056663 : Blo 1774088 5056663 := bstep (se 1 (by rfl) ⟨3792497, by rfl⟩ : syracuseStep 5056663 = 7584995) B7584995
theorem B3991769 : Blo 1774088 3991769 := bstep (se 2 (by rfl) ⟨1496913, by rfl⟩ : syracuseStep 3991769 = 2993827) B2993827
theorem B17058053 : Blo 1774088 17058053 := bstep (se 4 (by rfl) ⟨1599192, by rfl⟩ : syracuseStep 17058053 = 3198385) B3198385
theorem B2246935 : Blo 1774088 2246935 := bstep (se 1 (by rfl) ⟨1685201, by rfl⟩ : syracuseStep 2246935 = 3370403) B3370403
theorem B6400301 : Blo 1774088 6400301 := bstep (se 3 (by rfl) ⟨1200056, by rfl⟩ : syracuseStep 6400301 = 2400113) B2400113
theorem B3991859 : Blo 1774088 3991859 := bstep (se 1 (by rfl) ⟨2993894, by rfl⟩ : syracuseStep 3991859 = 5987789) B5987789
theorem B4491571 : Blo 1774088 4491571 := bstep (se 1 (by rfl) ⟨3368678, by rfl⟩ : syracuseStep 4491571 = 6737357) B6737357
theorem B3991895 : Blo 1774088 3991895 := bstep (se 1 (by rfl) ⟨2993921, by rfl⟩ : syracuseStep 3991895 = 5987843) B5987843
theorem B13478237 : Blo 1774088 13478237 := bstep (se 3 (by rfl) ⟨2527169, by rfl⟩ : syracuseStep 13478237 = 5054339) B5054339
theorem B6834577 : Blo 1774088 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B4491713 : Blo 1774088 4491713 := bstep (se 2 (by rfl) ⟨1684392, by rfl⟩ : syracuseStep 4491713 = 3368785) B3368785
theorem B3369431 : Blo 1774088 3369431 := bstep (se 1 (by rfl) ⟨2527073, by rfl⟩ : syracuseStep 3369431 = 5054147) B5054147
theorem B3992075 : Blo 1774088 3992075 := bstep (se 1 (by rfl) ⟨2994056, by rfl⟩ : syracuseStep 3992075 = 5988113) B5988113
theorem B3992129 : Blo 1774088 3992129 := bstep (se 2 (by rfl) ⟨1497048, by rfl⟩ : syracuseStep 3992129 = 2994097) B2994097
theorem B5991191 : Blo 1774088 5991191 := bstep (se 1 (by rfl) ⟨4493393, by rfl⟩ : syracuseStep 5991191 = 8986787) B8986787
theorem B3992345 : Blo 1774088 3992345 := bstep (se 2 (by rfl) ⟨1497129, by rfl⟩ : syracuseStep 3992345 = 2994259) B2994259
theorem B1895275 : Blo 1774088 1895275 := bstep (se 1 (by rfl) ⟨1421456, by rfl⟩ : syracuseStep 1895275 = 2842913) B2842913
theorem B3992435 : Blo 1774088 3992435 := bstep (se 1 (by rfl) ⟨2994326, by rfl⟩ : syracuseStep 3992435 = 5988653) B5988653
theorem B3992471 : Blo 1774088 3992471 := bstep (se 1 (by rfl) ⟨2994353, by rfl⟩ : syracuseStep 3992471 = 5988707) B5988707
theorem B38374469 : Blo 1774088 38374469 := bstep (se 4 (by rfl) ⟨3597606, by rfl⟩ : syracuseStep 38374469 = 7195213) B7195213
theorem B3992651 : Blo 1774088 3992651 := bstep (se 1 (by rfl) ⟨2994488, by rfl⟩ : syracuseStep 3992651 = 5988977) B5988977
theorem B3370099 : Blo 1774088 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B3992705 : Blo 1774088 3992705 := bstep (se 2 (by rfl) ⟨1497264, by rfl⟩ : syracuseStep 3992705 = 2994529) B2994529
theorem B19721477 : Blo 1774088 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B2051371 : Blo 1774088 2051371 := bstep (se 1 (by rfl) ⟨1538528, by rfl⟩ : syracuseStep 2051371 = 3077057) B3077057
theorem B5991731 : Blo 1774088 5991731 := bstep (se 1 (by rfl) ⟨4493798, by rfl⟩ : syracuseStep 5991731 = 8987597) B8987597
theorem B8990027 : Blo 1774088 8990027 := bstep (se 1 (by rfl) ⟨6742520, by rfl⟩ : syracuseStep 8990027 = 13485041) B13485041
theorem B3992921 : Blo 1774088 3992921 := bstep (se 2 (by rfl) ⟨1497345, by rfl⟩ : syracuseStep 3992921 = 2994691) B2994691
theorem B3993011 : Blo 1774088 3993011 := bstep (se 1 (by rfl) ⟨2994758, by rfl⟩ : syracuseStep 3993011 = 5989517) B5989517
theorem B3993047 : Blo 1774088 3993047 := bstep (se 1 (by rfl) ⟨2994785, by rfl⟩ : syracuseStep 3993047 = 5989571) B5989571
theorem B5688797 : Blo 1774088 5688797 := bstep (se 3 (by rfl) ⟨1066649, by rfl⟩ : syracuseStep 5688797 = 2133299) B2133299
theorem B31157777 : Blo 1774088 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B3370547 : Blo 1774088 3370547 := bstep (se 1 (by rfl) ⟨2527910, by rfl⟩ : syracuseStep 3370547 = 5055821) B5055821
theorem B5992001 : Blo 1774088 5992001 := bstep (se 2 (by rfl) ⟨2247000, by rfl⟩ : syracuseStep 5992001 = 4494001) B4494001
theorem B3370585 : Blo 1774088 3370585 := bstep (se 2 (by rfl) ⟨1263969, by rfl⟩ : syracuseStep 3370585 = 2527939) B2527939
theorem B6737539 : Blo 1774088 6737539 := bstep (se 1 (by rfl) ⟨5053154, by rfl⟩ : syracuseStep 6737539 = 10106309) B10106309
theorem B3993227 : Blo 1774088 3993227 := bstep (se 1 (by rfl) ⟨2994920, by rfl⟩ : syracuseStep 3993227 = 5989841) B5989841
theorem B4492979 : Blo 1774088 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B3993281 : Blo 1774088 3993281 := bstep (se 2 (by rfl) ⟨1497480, by rfl⟩ : syracuseStep 3993281 = 2994961) B2994961
theorem B14388941 : Blo 1774088 14388941 := bstep (se 3 (by rfl) ⟨2697926, by rfl⟩ : syracuseStep 14388941 = 5395853) B5395853
theorem B2993881 : Blo 1774088 2993881 := bstep (se 2 (by rfl) ⟨1122705, by rfl⟩ : syracuseStep 2993881 = 2245411) B2245411
theorem B3460825 : Blo 1774088 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B3600139 : Blo 1774088 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B3993497 : Blo 1774088 3993497 := bstep (se 2 (by rfl) ⟨1497561, by rfl⟩ : syracuseStep 3993497 = 2995123) B2995123
theorem B6737843 : Blo 1774088 6737843 := bstep (se 1 (by rfl) ⟨5053382, by rfl⟩ : syracuseStep 6737843 = 10106765) B10106765
theorem B8531891 : Blo 1774088 8531891 := bstep (se 1 (by rfl) ⟨6398918, by rfl⟩ : syracuseStep 8531891 = 12797837) B12797837
theorem B3993587 : Blo 1774088 3993587 := bstep (se 1 (by rfl) ⟨2995190, by rfl⟩ : syracuseStep 3993587 = 5990381) B5990381
theorem B9236497 : Blo 1774088 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B3993623 : Blo 1774088 3993623 := bstep (se 1 (by rfl) ⟨2995217, by rfl⟩ : syracuseStep 3993623 = 5990435) B5990435
theorem B3371033 : Blo 1774088 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B5992541 : Blo 1774088 5992541 := bstep (se 3 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 5992541 = 2247203) B2247203
theorem B3993803 : Blo 1774088 3993803 := bstep (se 1 (by rfl) ⟨2995352, by rfl⟩ : syracuseStep 3993803 = 5990705) B5990705
theorem B4493515 : Blo 1774088 4493515 := bstep (se 1 (by rfl) ⟨3370136, by rfl⟩ : syracuseStep 4493515 = 6740273) B6740273
theorem B25940209 : Blo 1774088 25940209 := bstep (se 2 (by rfl) ⟨9727578, by rfl⟩ : syracuseStep 25940209 = 19455157) B19455157
theorem B3993857 : Blo 1774088 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B2994455 : Blo 1774088 2994455 := bstep (se 1 (by rfl) ⟨2245841, by rfl⟩ : syracuseStep 2994455 = 4491683) B4491683
theorem B4493657 : Blo 1774088 4493657 := bstep (se 2 (by rfl) ⟨1685121, by rfl⟩ : syracuseStep 4493657 = 3370243) B3370243
theorem B2994583 : Blo 1774088 2994583 := bstep (se 1 (by rfl) ⟨2245937, by rfl⟩ : syracuseStep 2994583 = 4491875) B4491875
theorem B3994073 : Blo 1774088 3994073 := bstep (se 2 (by rfl) ⟨1497777, by rfl⟩ : syracuseStep 3994073 = 2995555) B2995555
theorem B1774091 : Blo 1774088 1774091 := bstep (se 1 (by rfl) ⟨1330568, by rfl⟩ : syracuseStep 1774091 = 2661137) B2661137
theorem B1774103 : Blo 1774088 1774103 := bstep (se 1 (by rfl) ⟨1330577, by rfl⟩ : syracuseStep 1774103 = 2661155) B2661155
theorem B3789337 : Blo 1774088 3789337 := bstep (se 2 (by rfl) ⟨1421001, by rfl⟩ : syracuseStep 3789337 = 2842003) B2842003
theorem B1774123 : Blo 1774088 1774123 := bstep (se 1 (by rfl) ⟨1330592, by rfl⟩ : syracuseStep 1774123 = 2661185) B2661185
theorem B3994163 : Blo 1774088 3994163 := bstep (se 1 (by rfl) ⟨2995622, by rfl⟩ : syracuseStep 3994163 = 5991245) B5991245
theorem B1774135 : Blo 1774088 1774135 := bstep (se 1 (by rfl) ⟨1330601, by rfl⟩ : syracuseStep 1774135 = 2661203) B2661203
theorem B6738497 : Blo 1774088 6738497 := bstep (se 2 (by rfl) ⟨2526936, by rfl⟩ : syracuseStep 6738497 = 5053873) B5053873
theorem B1774155 : Blo 1774088 1774155 := bstep (se 1 (by rfl) ⟨1330616, by rfl⟩ : syracuseStep 1774155 = 2661233) B2661233
theorem B1774167 : Blo 1774088 1774167 := bstep (se 1 (by rfl) ⟨1330625, by rfl⟩ : syracuseStep 1774167 = 2661251) B2661251
theorem B3994199 : Blo 1774088 3994199 := bstep (se 1 (by rfl) ⟨2995649, by rfl⟩ : syracuseStep 3994199 = 5991299) B5991299
theorem B12792413 : Blo 1774088 12792413 := bstep (se 3 (by rfl) ⟨2398577, by rfl⟩ : syracuseStep 12792413 = 4797155) B4797155
theorem B1774187 : Blo 1774088 1774187 := bstep (se 1 (by rfl) ⟨1330640, by rfl⟩ : syracuseStep 1774187 = 2661281) B2661281
theorem B3199603 : Blo 1774088 3199603 := bstep (se 1 (by rfl) ⟨2399702, by rfl⟩ : syracuseStep 3199603 = 4799405) B4799405
theorem B1774199 : Blo 1774088 1774199 := bstep (se 1 (by rfl) ⟨1330649, by rfl⟩ : syracuseStep 1774199 = 2661299) B2661299
theorem B1774219 : Blo 1774088 1774219 := bstep (se 1 (by rfl) ⟨1330664, by rfl⟩ : syracuseStep 1774219 = 2661329) B2661329
theorem B1774231 : Blo 1774088 1774231 := bstep (se 1 (by rfl) ⟨1330673, by rfl⟩ : syracuseStep 1774231 = 2661347) B2661347
theorem B1774251 : Blo 1774088 1774251 := bstep (se 1 (by rfl) ⟨1330688, by rfl⟩ : syracuseStep 1774251 = 2661377) B2661377
theorem B1774263 : Blo 1774088 1774263 := bstep (se 1 (by rfl) ⟨1330697, by rfl⟩ : syracuseStep 1774263 = 2661395) B2661395
theorem B1774283 : Blo 1774088 1774283 := bstep (se 1 (by rfl) ⟨1330712, by rfl⟩ : syracuseStep 1774283 = 2661425) B2661425
theorem B12800717 : Blo 1774088 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B1774295 : Blo 1774088 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1774315 : Blo 1774088 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B1774327 : Blo 1774088 1774327 := bstep (se 1 (by rfl) ⟨1330745, by rfl⟩ : syracuseStep 1774327 = 2661491) B2661491
theorem B3371777 : Blo 1774088 3371777 := bstep (se 2 (by rfl) ⟨1264416, by rfl⟩ : syracuseStep 3371777 = 2528833) B2528833
theorem B27316997 : Blo 1774088 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1774347 : Blo 1774088 1774347 := bstep (se 1 (by rfl) ⟨1330760, by rfl⟩ : syracuseStep 1774347 = 2661521) B2661521
theorem B3994379 : Blo 1774088 3994379 := bstep (se 1 (by rfl) ⟨2995784, by rfl⟩ : syracuseStep 3994379 = 5991569) B5991569
theorem B1774359 : Blo 1774088 1774359 := bstep (se 1 (by rfl) ⟨1330769, by rfl⟩ : syracuseStep 1774359 = 2661539) B2661539
theorem B3789593 : Blo 1774088 3789593 := bstep (se 2 (by rfl) ⟨1421097, by rfl⟩ : syracuseStep 3789593 = 2842195) B2842195
theorem B1774379 : Blo 1774088 1774379 := bstep (se 1 (by rfl) ⟨1330784, by rfl⟩ : syracuseStep 1774379 = 2661569) B2661569
theorem B1774391 : Blo 1774088 1774391 := bstep (se 1 (by rfl) ⟨1330793, by rfl⟩ : syracuseStep 1774391 = 2661587) B2661587
theorem B3994433 : Blo 1774088 3994433 := bstep (se 2 (by rfl) ⟨1497912, by rfl⟩ : syracuseStep 3994433 = 2995825) B2995825
theorem B1774411 : Blo 1774088 1774411 := bstep (se 1 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 1774411 = 2661617) B2661617
theorem B1774423 : Blo 1774088 1774423 := bstep (se 1 (by rfl) ⟨1330817, by rfl⟩ : syracuseStep 1774423 = 2661635) B2661635
theorem B1774443 : Blo 1774088 1774443 := bstep (se 1 (by rfl) ⟨1330832, by rfl⟩ : syracuseStep 1774443 = 2661665) B2661665
theorem B1774455 : Blo 1774088 1774455 := bstep (se 1 (by rfl) ⟨1330841, by rfl⟩ : syracuseStep 1774455 = 2661683) B2661683
theorem B1774475 : Blo 1774088 1774475 := bstep (se 1 (by rfl) ⟨1330856, by rfl⟩ : syracuseStep 1774475 = 2661713) B2661713
theorem B1774487 : Blo 1774088 1774487 := bstep (se 1 (by rfl) ⟨1330865, by rfl⟩ : syracuseStep 1774487 = 2661731) B2661731
theorem B1774507 : Blo 1774088 1774507 := bstep (se 1 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 1774507 = 2661761) B2661761
theorem B1774519 : Blo 1774088 1774519 := bstep (se 1 (by rfl) ⟨1330889, by rfl⟩ : syracuseStep 1774519 = 2661779) B2661779
theorem B1774539 : Blo 1774088 1774539 := bstep (se 1 (by rfl) ⟨1330904, by rfl⟩ : syracuseStep 1774539 = 2661809) B2661809
theorem B1774551 : Blo 1774088 1774551 := bstep (se 1 (by rfl) ⟨1330913, by rfl⟩ : syracuseStep 1774551 = 2661827) B2661827
theorem B1774571 : Blo 1774088 1774571 := bstep (se 1 (by rfl) ⟨1330928, by rfl⟩ : syracuseStep 1774571 = 2661857) B2661857
theorem B1774583 : Blo 1774088 1774583 := bstep (se 1 (by rfl) ⟨1330937, by rfl⟩ : syracuseStep 1774583 = 2661875) B2661875
theorem B1774603 : Blo 1774088 1774603 := bstep (se 1 (by rfl) ⟨1330952, by rfl⟩ : syracuseStep 1774603 = 2661905) B2661905
theorem B2995211 : Blo 1774088 2995211 := bstep (se 1 (by rfl) ⟨2246408, by rfl⟩ : syracuseStep 2995211 = 4492817) B4492817
theorem B1774615 : Blo 1774088 1774615 := bstep (se 1 (by rfl) ⟨1330961, by rfl⟩ : syracuseStep 1774615 = 2661923) B2661923
theorem B3994649 : Blo 1774088 3994649 := bstep (se 2 (by rfl) ⟨1497993, by rfl⟩ : syracuseStep 3994649 = 2995987) B2995987
theorem B17052707 : Blo 1774088 17052707 := bstep (se 1 (by rfl) ⟨12789530, by rfl⟩ : syracuseStep 17052707 = 25579061) B25579061
theorem B1774635 : Blo 1774088 1774635 := bstep (se 1 (by rfl) ⟨1330976, by rfl⟩ : syracuseStep 1774635 = 2661953) B2661953
theorem B6394925 : Blo 1774088 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B1774647 : Blo 1774088 1774647 := bstep (se 1 (by rfl) ⟨1330985, by rfl⟩ : syracuseStep 1774647 = 2661971) B2661971
theorem B1774667 : Blo 1774088 1774667 := bstep (se 1 (by rfl) ⟨1331000, by rfl⟩ : syracuseStep 1774667 = 2662001) B2662001
theorem B1774679 : Blo 1774088 1774679 := bstep (se 1 (by rfl) ⟨1331009, by rfl⟩ : syracuseStep 1774679 = 2662019) B2662019
theorem B3036247 : Blo 1774088 3036247 := bstep (se 1 (by rfl) ⟨2277185, by rfl⟩ : syracuseStep 3036247 = 4554371) B4554371
theorem B1774699 : Blo 1774088 1774699 := bstep (se 1 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 1774699 = 2662049) B2662049
theorem B3994739 : Blo 1774088 3994739 := bstep (se 1 (by rfl) ⟨2996054, by rfl⟩ : syracuseStep 3994739 = 5992109) B5992109
theorem B1774711 : Blo 1774088 1774711 := bstep (se 1 (by rfl) ⟨1331033, by rfl⟩ : syracuseStep 1774711 = 2662067) B2662067
theorem B1774731 : Blo 1774088 1774731 := bstep (se 1 (by rfl) ⟨1331048, by rfl⟩ : syracuseStep 1774731 = 2662097) B2662097
theorem B2995339 : Blo 1774088 2995339 := bstep (se 1 (by rfl) ⟨2246504, by rfl⟩ : syracuseStep 2995339 = 4493009) B4493009
theorem B1774743 : Blo 1774088 1774743 := bstep (se 1 (by rfl) ⟨1331057, by rfl⟩ : syracuseStep 1774743 = 2662115) B2662115
theorem B3994775 : Blo 1774088 3994775 := bstep (se 1 (by rfl) ⟨2996081, by rfl⟩ : syracuseStep 3994775 = 5992163) B5992163
theorem B4494487 : Blo 1774088 4494487 := bstep (se 1 (by rfl) ⟨3370865, by rfl⟩ : syracuseStep 4494487 = 6741731) B6741731
theorem B1774763 : Blo 1774088 1774763 := bstep (se 1 (by rfl) ⟨1331072, by rfl⟩ : syracuseStep 1774763 = 2662145) B2662145
theorem B3790003 : Blo 1774088 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B1774775 : Blo 1774088 1774775 := bstep (se 1 (by rfl) ⟨1331081, by rfl⟩ : syracuseStep 1774775 = 2662163) B2662163
theorem B1995979 : Blo 1774088 1995979 := bstep (se 1 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 1995979 = 2993969) B2993969
theorem B1774795 : Blo 1774088 1774795 := bstep (se 1 (by rfl) ⟨1331096, by rfl⟩ : syracuseStep 1774795 = 2662193) B2662193
theorem B5993675 : Blo 1774088 5993675 := bstep (se 1 (by rfl) ⟨4495256, by rfl⟩ : syracuseStep 5993675 = 8990513) B8990513
theorem B1774807 : Blo 1774088 1774807 := bstep (se 1 (by rfl) ⟨1331105, by rfl⟩ : syracuseStep 1774807 = 2662211) B2662211
theorem B1774827 : Blo 1774088 1774827 := bstep (se 1 (by rfl) ⟨1331120, by rfl⟩ : syracuseStep 1774827 = 2662241) B2662241
theorem B1774839 : Blo 1774088 1774839 := bstep (se 1 (by rfl) ⟨1331129, by rfl⟩ : syracuseStep 1774839 = 2662259) B2662259
theorem B1774859 : Blo 1774088 1774859 := bstep (se 1 (by rfl) ⟨1331144, by rfl⟩ : syracuseStep 1774859 = 2662289) B2662289
theorem B1774871 : Blo 1774088 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B2995481 : Blo 1774088 2995481 := bstep (se 2 (by rfl) ⟨1123305, by rfl⟩ : syracuseStep 2995481 = 2246611) B2246611
theorem B1774891 : Blo 1774088 1774891 := bstep (se 1 (by rfl) ⟨1331168, by rfl⟩ : syracuseStep 1774891 = 2662337) B2662337
theorem B1996087 : Blo 1774088 1996087 := bstep (se 1 (by rfl) ⟨1497065, by rfl⟩ : syracuseStep 1996087 = 2994131) B2994131
theorem B1774903 : Blo 1774088 1774903 := bstep (se 1 (by rfl) ⟨1331177, by rfl⟩ : syracuseStep 1774903 = 2662355) B2662355
theorem B1774923 : Blo 1774088 1774923 := bstep (se 1 (by rfl) ⟨1331192, by rfl⟩ : syracuseStep 1774923 = 2662385) B2662385
theorem B3994955 : Blo 1774088 3994955 := bstep (se 1 (by rfl) ⟨2996216, by rfl⟩ : syracuseStep 3994955 = 5992433) B5992433
theorem B1774935 : Blo 1774088 1774935 := bstep (se 1 (by rfl) ⟨1331201, by rfl⟩ : syracuseStep 1774935 = 2662403) B2662403
theorem B1774955 : Blo 1774088 1774955 := bstep (se 1 (by rfl) ⟨1331216, by rfl⟩ : syracuseStep 1774955 = 2662433) B2662433
theorem B1774967 : Blo 1774088 1774967 := bstep (se 1 (by rfl) ⟨1331225, by rfl⟩ : syracuseStep 1774967 = 2662451) B2662451
theorem B3995009 : Blo 1774088 3995009 := bstep (se 2 (by rfl) ⟨1498128, by rfl⟩ : syracuseStep 3995009 = 2996257) B2996257
theorem B1774987 : Blo 1774088 1774987 := bstep (se 1 (by rfl) ⟨1331240, by rfl⟩ : syracuseStep 1774987 = 2662481) B2662481
theorem B1774999 : Blo 1774088 1774999 := bstep (se 1 (by rfl) ⟨1331249, by rfl⟩ : syracuseStep 1774999 = 2662499) B2662499
theorem B2995609 : Blo 1774088 2995609 := bstep (se 2 (by rfl) ⟨1123353, by rfl⟩ : syracuseStep 2995609 = 2246707) B2246707
theorem B1775019 : Blo 1774088 1775019 := bstep (se 1 (by rfl) ⟨1331264, by rfl⟩ : syracuseStep 1775019 = 2662529) B2662529
theorem B7583149 : Blo 1774088 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B1775031 : Blo 1774088 1775031 := bstep (se 1 (by rfl) ⟨1331273, by rfl⟩ : syracuseStep 1775031 = 2662547) B2662547
theorem B1775051 : Blo 1774088 1775051 := bstep (se 1 (by rfl) ⟨1331288, by rfl⟩ : syracuseStep 1775051 = 2662577) B2662577
theorem B1775063 : Blo 1774088 1775063 := bstep (se 1 (by rfl) ⟨1331297, by rfl⟩ : syracuseStep 1775063 = 2662595) B2662595
theorem B3036631 : Blo 1774088 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B5993945 : Blo 1774088 5993945 := bstep (se 2 (by rfl) ⟨2247729, by rfl⟩ : syracuseStep 5993945 = 4495459) B4495459
theorem B1996267 : Blo 1774088 1996267 := bstep (se 1 (by rfl) ⟨1497200, by rfl⟩ : syracuseStep 1996267 = 2994401) B2994401
theorem B1775083 : Blo 1774088 1775083 := bstep (se 1 (by rfl) ⟨1331312, by rfl⟩ : syracuseStep 1775083 = 2662625) B2662625
theorem B1775095 : Blo 1774088 1775095 := bstep (se 1 (by rfl) ⟨1331321, by rfl⟩ : syracuseStep 1775095 = 2662643) B2662643
theorem B1775115 : Blo 1774088 1775115 := bstep (se 1 (by rfl) ⟨1331336, by rfl⟩ : syracuseStep 1775115 = 2662673) B2662673
theorem B1775127 : Blo 1774088 1775127 := bstep (se 1 (by rfl) ⟨1331345, by rfl⟩ : syracuseStep 1775127 = 2662691) B2662691
theorem B1775147 : Blo 1774088 1775147 := bstep (se 1 (by rfl) ⟨1331360, by rfl⟩ : syracuseStep 1775147 = 2662721) B2662721
theorem B1775159 : Blo 1774088 1775159 := bstep (se 1 (by rfl) ⟨1331369, by rfl⟩ : syracuseStep 1775159 = 2662739) B2662739
theorem B1775179 : Blo 1774088 1775179 := bstep (se 1 (by rfl) ⟨1331384, by rfl⟩ : syracuseStep 1775179 = 2662769) B2662769
theorem B4494923 : Blo 1774088 4494923 := bstep (se 1 (by rfl) ⟨3371192, by rfl⟩ : syracuseStep 4494923 = 6742385) B6742385
theorem B1996375 : Blo 1774088 1996375 := bstep (se 1 (by rfl) ⟨1497281, by rfl⟩ : syracuseStep 1996375 = 2994563) B2994563
theorem B1775191 : Blo 1774088 1775191 := bstep (se 1 (by rfl) ⟨1331393, by rfl⟩ : syracuseStep 1775191 = 2662787) B2662787
theorem B4265561 : Blo 1774088 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B7583321 : Blo 1774088 7583321 := bstep (se 2 (by rfl) ⟨2843745, by rfl⟩ : syracuseStep 7583321 = 5687491) B5687491
theorem B3995225 : Blo 1774088 3995225 := bstep (se 2 (by rfl) ⟨1498209, by rfl⟩ : syracuseStep 3995225 = 2996419) B2996419
theorem B1775211 : Blo 1774088 1775211 := bstep (se 1 (by rfl) ⟨1331408, by rfl⟩ : syracuseStep 1775211 = 2662817) B2662817
theorem B1775223 : Blo 1774088 1775223 := bstep (se 1 (by rfl) ⟨1331417, by rfl⟩ : syracuseStep 1775223 = 2662835) B2662835
theorem B8984195 : Blo 1774088 8984195 := bstep (se 1 (by rfl) ⟨6738146, by rfl⟩ : syracuseStep 8984195 = 13476293) B13476293
theorem B1775243 : Blo 1774088 1775243 := bstep (se 1 (by rfl) ⟨1331432, by rfl⟩ : syracuseStep 1775243 = 2662865) B2662865
theorem B1775255 : Blo 1774088 1775255 := bstep (se 1 (by rfl) ⟨1331441, by rfl⟩ : syracuseStep 1775255 = 2662883) B2662883
theorem B1775275 : Blo 1774088 1775275 := bstep (se 1 (by rfl) ⟨1331456, by rfl⟩ : syracuseStep 1775275 = 2662913) B2662913
theorem B3995315 : Blo 1774088 3995315 := bstep (se 1 (by rfl) ⟨2996486, by rfl⟩ : syracuseStep 3995315 = 5992973) B5992973
theorem B10114739 : Blo 1774088 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B1775287 : Blo 1774088 1775287 := bstep (se 1 (by rfl) ⟨1331465, by rfl⟩ : syracuseStep 1775287 = 2662931) B2662931
theorem B5052107 : Blo 1774088 5052107 := bstep (se 1 (by rfl) ⟨3789080, by rfl⟩ : syracuseStep 5052107 = 7578161) B7578161
theorem B1775307 : Blo 1774088 1775307 := bstep (se 1 (by rfl) ⟨1331480, by rfl⟩ : syracuseStep 1775307 = 2662961) B2662961
theorem B1775319 : Blo 1774088 1775319 := bstep (se 1 (by rfl) ⟨1331489, by rfl⟩ : syracuseStep 1775319 = 2662979) B2662979
theorem B3995351 : Blo 1774088 3995351 := bstep (se 1 (by rfl) ⟨2996513, by rfl⟩ : syracuseStep 3995351 = 5993027) B5993027
theorem B1775339 : Blo 1774088 1775339 := bstep (se 1 (by rfl) ⟨1331504, by rfl⟩ : syracuseStep 1775339 = 2663009) B2663009
theorem B1775351 : Blo 1774088 1775351 := bstep (se 1 (by rfl) ⟨1331513, by rfl⟩ : syracuseStep 1775351 = 2663027) B2663027
theorem B1996555 : Blo 1774088 1996555 := bstep (se 1 (by rfl) ⟨1497416, by rfl⟩ : syracuseStep 1996555 = 2994833) B2994833
theorem B1775371 : Blo 1774088 1775371 := bstep (se 1 (by rfl) ⟨1331528, by rfl⟩ : syracuseStep 1775371 = 2663057) B2663057
theorem B1775383 : Blo 1774088 1775383 := bstep (se 1 (by rfl) ⟨1331537, by rfl⟩ : syracuseStep 1775383 = 2663075) B2663075
theorem B1775403 : Blo 1774088 1775403 := bstep (se 1 (by rfl) ⟨1331552, by rfl⟩ : syracuseStep 1775403 = 2663105) B2663105
theorem B6739757 : Blo 1774088 6739757 := bstep (se 3 (by rfl) ⟨1263704, by rfl⟩ : syracuseStep 6739757 = 2527409) B2527409
theorem B1775415 : Blo 1774088 1775415 := bstep (se 1 (by rfl) ⟨1331561, by rfl⟩ : syracuseStep 1775415 = 2663123) B2663123
theorem B2398027 : Blo 1774088 2398027 := bstep (se 1 (by rfl) ⟨1798520, by rfl⟩ : syracuseStep 2398027 = 3597041) B3597041
theorem B6739787 : Blo 1774088 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B1775435 : Blo 1774088 1775435 := bstep (se 1 (by rfl) ⟨1331576, by rfl⟩ : syracuseStep 1775435 = 2663153) B2663153
theorem B1775447 : Blo 1774088 1775447 := bstep (se 1 (by rfl) ⟨1331585, by rfl⟩ : syracuseStep 1775447 = 2663171) B2663171
theorem B1775467 : Blo 1774088 1775467 := bstep (se 1 (by rfl) ⟨1331600, by rfl⟩ : syracuseStep 1775467 = 2663201) B2663201
theorem B1996663 : Blo 1774088 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B1775479 : Blo 1774088 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B3790721 : Blo 1774088 3790721 := bstep (se 2 (by rfl) ⟨1421520, by rfl⟩ : syracuseStep 3790721 = 2843041) B2843041
theorem B1775499 : Blo 1774088 1775499 := bstep (se 1 (by rfl) ⟨1331624, by rfl⟩ : syracuseStep 1775499 = 2663249) B2663249
theorem B3995531 : Blo 1774088 3995531 := bstep (se 1 (by rfl) ⟨2996648, by rfl⟩ : syracuseStep 3995531 = 5993297) B5993297
theorem B1775511 : Blo 1774088 1775511 := bstep (se 1 (by rfl) ⟨1331633, by rfl⟩ : syracuseStep 1775511 = 2663267) B2663267
theorem B1775531 : Blo 1774088 1775531 := bstep (se 1 (by rfl) ⟨1331648, by rfl⟩ : syracuseStep 1775531 = 2663297) B2663297
theorem B1775543 : Blo 1774088 1775543 := bstep (se 1 (by rfl) ⟨1331657, by rfl⟩ : syracuseStep 1775543 = 2663315) B2663315
theorem B3995585 : Blo 1774088 3995585 := bstep (se 2 (by rfl) ⟨1498344, by rfl⟩ : syracuseStep 3995585 = 2996689) B2996689
theorem B4495297 : Blo 1774088 4495297 := bstep (se 2 (by rfl) ⟨1685736, by rfl⟩ : syracuseStep 4495297 = 3371473) B3371473
theorem B1775563 : Blo 1774088 1775563 := bstep (se 1 (by rfl) ⟨1331672, by rfl⟩ : syracuseStep 1775563 = 2663345) B2663345
theorem B2996183 : Blo 1774088 2996183 := bstep (se 1 (by rfl) ⟨2247137, by rfl⟩ : syracuseStep 2996183 = 4494275) B4494275
theorem B1775575 : Blo 1774088 1775575 := bstep (se 1 (by rfl) ⟨1331681, by rfl⟩ : syracuseStep 1775575 = 2663363) B2663363
theorem B1775595 : Blo 1774088 1775595 := bstep (se 1 (by rfl) ⟨1331696, by rfl⟩ : syracuseStep 1775595 = 2663393) B2663393
theorem B1775607 : Blo 1774088 1775607 := bstep (se 1 (by rfl) ⟨1331705, by rfl⟩ : syracuseStep 1775607 = 2663411) B2663411
theorem B1775627 : Blo 1774088 1775627 := bstep (se 1 (by rfl) ⟨1331720, by rfl⟩ : syracuseStep 1775627 = 2663441) B2663441
theorem B6395921 : Blo 1774088 6395921 := bstep (se 2 (by rfl) ⟨2398470, by rfl⟩ : syracuseStep 6395921 = 4796941) B4796941
theorem B1775639 : Blo 1774088 1775639 := bstep (se 1 (by rfl) ⟨1331729, by rfl⟩ : syracuseStep 1775639 = 2663459) B2663459
theorem B1996843 : Blo 1774088 1996843 := bstep (se 1 (by rfl) ⟨1497632, by rfl⟩ : syracuseStep 1996843 = 2995265) B2995265
theorem B1775659 : Blo 1774088 1775659 := bstep (se 1 (by rfl) ⟨1331744, by rfl⟩ : syracuseStep 1775659 = 2663489) B2663489
theorem B1775671 : Blo 1774088 1775671 := bstep (se 1 (by rfl) ⟨1331753, by rfl⟩ : syracuseStep 1775671 = 2663507) B2663507
theorem B1775691 : Blo 1774088 1775691 := bstep (se 1 (by rfl) ⟨1331768, by rfl⟩ : syracuseStep 1775691 = 2663537) B2663537
theorem B2996311 : Blo 1774088 2996311 := bstep (se 1 (by rfl) ⟨2247233, by rfl⟩ : syracuseStep 2996311 = 4494467) B4494467
theorem B1775703 : Blo 1774088 1775703 := bstep (se 1 (by rfl) ⟨1331777, by rfl⟩ : syracuseStep 1775703 = 2663555) B2663555
theorem B1775723 : Blo 1774088 1775723 := bstep (se 1 (by rfl) ⟨1331792, by rfl⟩ : syracuseStep 1775723 = 2663585) B2663585
theorem B1775735 : Blo 1774088 1775735 := bstep (se 1 (by rfl) ⟨1331801, by rfl⟩ : syracuseStep 1775735 = 2663603) B2663603
theorem B1775755 : Blo 1774088 1775755 := bstep (se 1 (by rfl) ⟨1331816, by rfl⟩ : syracuseStep 1775755 = 2663633) B2663633
theorem B1996951 : Blo 1774088 1996951 := bstep (se 1 (by rfl) ⟨1497713, by rfl⟩ : syracuseStep 1996951 = 2995427) B2995427
theorem B1775767 : Blo 1774088 1775767 := bstep (se 1 (by rfl) ⟨1331825, by rfl⟩ : syracuseStep 1775767 = 2663651) B2663651
theorem B3995801 : Blo 1774088 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B1775787 : Blo 1774088 1775787 := bstep (se 1 (by rfl) ⟨1331840, by rfl⟩ : syracuseStep 1775787 = 2663681) B2663681
theorem B1775799 : Blo 1774088 1775799 := bstep (se 1 (by rfl) ⟨1331849, by rfl⟩ : syracuseStep 1775799 = 2663699) B2663699
theorem B1775819 : Blo 1774088 1775819 := bstep (se 1 (by rfl) ⟨1331864, by rfl⟩ : syracuseStep 1775819 = 2663729) B2663729
theorem B30324941 : Blo 1774088 30324941 := bstep (se 3 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 30324941 = 11371853) B11371853
theorem B3791063 : Blo 1774088 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B6396121 : Blo 1774088 6396121 := bstep (se 2 (by rfl) ⟨2398545, by rfl⟩ : syracuseStep 6396121 = 4797091) B4797091
theorem B1775831 : Blo 1774088 1775831 := bstep (se 1 (by rfl) ⟨1331873, by rfl⟩ : syracuseStep 1775831 = 2663747) B2663747
theorem B1775851 : Blo 1774088 1775851 := bstep (se 1 (by rfl) ⟨1331888, by rfl⟩ : syracuseStep 1775851 = 2663777) B2663777
theorem B3995891 : Blo 1774088 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B1775863 : Blo 1774088 1775863 := bstep (se 1 (by rfl) ⟨1331897, by rfl⟩ : syracuseStep 1775863 = 2663795) B2663795
theorem B1775883 : Blo 1774088 1775883 := bstep (se 1 (by rfl) ⟨1331912, by rfl⟩ : syracuseStep 1775883 = 2663825) B2663825
theorem B1775895 : Blo 1774088 1775895 := bstep (se 1 (by rfl) ⟨1331921, by rfl⟩ : syracuseStep 1775895 = 2663843) B2663843
theorem B3995927 : Blo 1774088 3995927 := bstep (se 1 (by rfl) ⟨2996945, by rfl⟩ : syracuseStep 3995927 = 5993891) B5993891
theorem B1775915 : Blo 1774088 1775915 := bstep (se 1 (by rfl) ⟨1331936, by rfl⟩ : syracuseStep 1775915 = 2663873) B2663873
theorem B1775927 : Blo 1774088 1775927 := bstep (se 1 (by rfl) ⟨1331945, by rfl⟩ : syracuseStep 1775927 = 2663891) B2663891
theorem B1997131 : Blo 1774088 1997131 := bstep (se 1 (by rfl) ⟨1497848, by rfl⟩ : syracuseStep 1997131 = 2995697) B2995697
theorem B1775947 : Blo 1774088 1775947 := bstep (se 1 (by rfl) ⟨1331960, by rfl⟩ : syracuseStep 1775947 = 2663921) B2663921
theorem B1775959 : Blo 1774088 1775959 := bstep (se 1 (by rfl) ⟨1331969, by rfl⟩ : syracuseStep 1775959 = 2663939) B2663939
theorem B1775979 : Blo 1774088 1775979 := bstep (se 1 (by rfl) ⟨1331984, by rfl⟩ : syracuseStep 1775979 = 2663969) B2663969
theorem B54630773 : Blo 1774088 54630773 := bstep (se 5 (by rfl) ⟨2560817, by rfl⟩ : syracuseStep 54630773 = 5121635) B5121635
theorem B24303989 : Blo 1774088 24303989 := bstep (se 5 (by rfl) ⟨1139249, by rfl⟩ : syracuseStep 24303989 = 2278499) B2278499
theorem B1775991 : Blo 1774088 1775991 := bstep (se 1 (by rfl) ⟨1331993, by rfl⟩ : syracuseStep 1775991 = 2663987) B2663987
theorem B3791233 : Blo 1774088 3791233 := bstep (se 2 (by rfl) ⟨1421712, by rfl⟩ : syracuseStep 3791233 = 2843425) B2843425
theorem B1776011 : Blo 1774088 1776011 := bstep (se 1 (by rfl) ⟨1332008, by rfl⟩ : syracuseStep 1776011 = 2664017) B2664017
theorem B1776023 : Blo 1774088 1776023 := bstep (se 1 (by rfl) ⟨1332017, by rfl⟩ : syracuseStep 1776023 = 2664035) B2664035
theorem B1776043 : Blo 1774088 1776043 := bstep (se 1 (by rfl) ⟨1332032, by rfl⟩ : syracuseStep 1776043 = 2664065) B2664065
theorem B1997239 : Blo 1774088 1997239 := bstep (se 1 (by rfl) ⟨1497929, by rfl⟩ : syracuseStep 1997239 = 2995859) B2995859
theorem B1776055 : Blo 1774088 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B6396353 : Blo 1774088 6396353 := bstep (se 2 (by rfl) ⟨2398632, by rfl⟩ : syracuseStep 6396353 = 4797265) B4797265
theorem B3996107 : Blo 1774088 3996107 := bstep (se 1 (by rfl) ⟨2997080, by rfl⟩ : syracuseStep 3996107 = 5994161) B5994161
theorem B1776075 : Blo 1774088 1776075 := bstep (se 1 (by rfl) ⟨1332056, by rfl⟩ : syracuseStep 1776075 = 2664113) B2664113
theorem B1776087 : Blo 1774088 1776087 := bstep (se 1 (by rfl) ⟨1332065, by rfl⟩ : syracuseStep 1776087 = 2664131) B2664131
theorem B6740441 : Blo 1774088 6740441 := bstep (se 2 (by rfl) ⟨2527665, by rfl⟩ : syracuseStep 6740441 = 5055331) B5055331
theorem B3996161 : Blo 1774088 3996161 := bstep (se 2 (by rfl) ⟨1498560, by rfl⟩ : syracuseStep 3996161 = 2997121) B2997121
theorem B13474349 : Blo 1774088 13474349 := bstep (se 3 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 13474349 = 5052881) B5052881
theorem B5683763 : Blo 1774088 5683763 := bstep (se 1 (by rfl) ⟨4262822, by rfl⟩ : syracuseStep 5683763 = 8525645) B8525645
theorem B1997419 : Blo 1774088 1997419 := bstep (se 1 (by rfl) ⟨1498064, by rfl⟩ : syracuseStep 1997419 = 2996129) B2996129
theorem B2996939 : Blo 1774088 2996939 := bstep (se 1 (by rfl) ⟨2247704, by rfl⟩ : syracuseStep 2996939 = 4495409) B4495409
theorem B1997527 : Blo 1774088 1997527 := bstep (se 1 (by rfl) ⟨1498145, by rfl⟩ : syracuseStep 1997527 = 2996291) B2996291
theorem B2661143 : Blo 1774088 2661143 := bstep (se 1 (by rfl) ⟨1995857, by rfl⟩ : syracuseStep 2661143 = 3991715) B3991715
theorem B6740759 : Blo 1774088 6740759 := bstep (se 1 (by rfl) ⟨5055569, by rfl⟩ : syracuseStep 6740759 = 10111139) B10111139
theorem B7199563 : Blo 1774088 7199563 := bstep (se 1 (by rfl) ⟨5399672, by rfl⟩ : syracuseStep 7199563 = 10799345) B10799345
theorem B2997067 : Blo 1774088 2997067 := bstep (se 1 (by rfl) ⟨2247800, by rfl⟩ : syracuseStep 2997067 = 4495601) B4495601
theorem B2661209 : Blo 1774088 2661209 := bstep (se 2 (by rfl) ⟨997953, by rfl⟩ : syracuseStep 2661209 = 1995907) B1995907
theorem B1997707 : Blo 1774088 1997707 := bstep (se 1 (by rfl) ⟨1498280, by rfl⟩ : syracuseStep 1997707 = 2996561) B2996561
theorem B2661323 : Blo 1774088 2661323 := bstep (se 1 (by rfl) ⟨1995992, by rfl⟩ : syracuseStep 2661323 = 3991985) B3991985
theorem B2661335 : Blo 1774088 2661335 := bstep (se 1 (by rfl) ⟨1996001, by rfl⟩ : syracuseStep 2661335 = 3992003) B3992003
theorem B1997815 : Blo 1774088 1997815 := bstep (se 1 (by rfl) ⟨1498361, by rfl⟩ : syracuseStep 1997815 = 2996723) B2996723
theorem B2661401 : Blo 1774088 2661401 := bstep (se 2 (by rfl) ⟨998025, by rfl⟩ : syracuseStep 2661401 = 1996051) B1996051
theorem B10107949 : Blo 1774088 10107949 := bstep (se 3 (by rfl) ⟨1895240, by rfl⟩ : syracuseStep 10107949 = 3790481) B3790481
theorem B9600065 : Blo 1774088 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B2661515 : Blo 1774088 2661515 := bstep (se 1 (by rfl) ⟨1996136, by rfl⟩ : syracuseStep 2661515 = 3992273) B3992273
theorem B2661527 : Blo 1774088 2661527 := bstep (se 1 (by rfl) ⟨1996145, by rfl⟩ : syracuseStep 2661527 = 3992291) B3992291
theorem B1997995 : Blo 1774088 1997995 := bstep (se 1 (by rfl) ⟨1498496, by rfl⟩ : syracuseStep 1997995 = 2996993) B2996993
theorem B8101043 : Blo 1774088 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B30727349 : Blo 1774088 30727349 := bstep (se 5 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 30727349 = 2880689) B2880689
theorem B102390965 : Blo 1774088 102390965 := bstep (se 5 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 102390965 = 9599153) B9599153
theorem B8092865 : Blo 1774088 8092865 := bstep (se 2 (by rfl) ⟨3034824, by rfl⟩ : syracuseStep 8092865 = 6069649) B6069649
theorem B7584961 : Blo 1774088 7584961 := bstep (se 2 (by rfl) ⟨2844360, by rfl⟩ : syracuseStep 7584961 = 5688721) B5688721
theorem B2661593 : Blo 1774088 2661593 := bstep (se 2 (by rfl) ⟨998097, by rfl⟩ : syracuseStep 2661593 = 1996195) B1996195
theorem B5053747 : Blo 1774088 5053747 := bstep (se 1 (by rfl) ⟨3790310, by rfl⟩ : syracuseStep 5053747 = 7580621) B7580621
theorem B2661707 : Blo 1774088 2661707 := bstep (se 1 (by rfl) ⟨1996280, by rfl⟩ : syracuseStep 2661707 = 3992561) B3992561
theorem B11369803 : Blo 1774088 11369803 := bstep (se 1 (by rfl) ⟨8527352, by rfl⟩ : syracuseStep 11369803 = 17054705) B17054705
theorem B2661719 : Blo 1774088 2661719 := bstep (se 1 (by rfl) ⟨1996289, by rfl⟩ : syracuseStep 2661719 = 3992579) B3992579
theorem B5987735 : Blo 1774088 5987735 := bstep (se 1 (by rfl) ⟨4490801, by rfl⟩ : syracuseStep 5987735 = 8981603) B8981603
theorem B2661785 : Blo 1774088 2661785 := bstep (se 2 (by rfl) ⟨998169, by rfl⟩ : syracuseStep 2661785 = 1996339) B1996339
theorem B6741427 : Blo 1774088 6741427 := bstep (se 1 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 6741427 = 10112141) B10112141
theorem B2661899 : Blo 1774088 2661899 := bstep (se 1 (by rfl) ⟨1996424, by rfl⟩ : syracuseStep 2661899 = 3992849) B3992849
theorem B3792395 : Blo 1774088 3792395 := bstep (se 1 (by rfl) ⟨2844296, by rfl⟩ : syracuseStep 3792395 = 5688593) B5688593
theorem B2661911 : Blo 1774088 2661911 := bstep (se 1 (by rfl) ⟨1996433, by rfl⟩ : syracuseStep 2661911 = 3992867) B3992867
theorem B2661977 : Blo 1774088 2661977 := bstep (se 2 (by rfl) ⟨998241, by rfl⟩ : syracuseStep 2661977 = 1996483) B1996483
theorem B23068253 : Blo 1774088 23068253 := bstep (se 3 (by rfl) ⟨4325297, by rfl⟩ : syracuseStep 23068253 = 8650595) B8650595
theorem B2662091 : Blo 1774088 2662091 := bstep (se 1 (by rfl) ⟨1996568, by rfl⟩ : syracuseStep 2662091 = 3993137) B3993137
theorem B2662103 : Blo 1774088 2662103 := bstep (se 1 (by rfl) ⟨1996577, by rfl⟩ : syracuseStep 2662103 = 3993155) B3993155
theorem B11378393 : Blo 1774088 11378393 := bstep (se 2 (by rfl) ⟨4266897, by rfl⟩ : syracuseStep 11378393 = 8533795) B8533795
theorem B2662169 : Blo 1774088 2662169 := bstep (se 2 (by rfl) ⟨998313, by rfl⟩ : syracuseStep 2662169 = 1996627) B1996627
theorem B3841843 : Blo 1774088 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B7298909 : Blo 1774088 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B2662283 : Blo 1774088 2662283 := bstep (se 1 (by rfl) ⟨1996712, by rfl⟩ : syracuseStep 2662283 = 3993425) B3993425
theorem B2662295 : Blo 1774088 2662295 := bstep (se 1 (by rfl) ⟨1996721, by rfl⟩ : syracuseStep 2662295 = 3993443) B3993443
theorem B2432921 : Blo 1774088 2432921 := bstep (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) B1824691
theorem B5988275 : Blo 1774088 5988275 := bstep (se 1 (by rfl) ⟨4491206, by rfl⟩ : syracuseStep 5988275 = 8982413) B8982413
theorem B11370419 : Blo 1774088 11370419 := bstep (se 1 (by rfl) ⟨8527814, by rfl⟩ : syracuseStep 11370419 = 17055629) B17055629
theorem B2662361 : Blo 1774088 2662361 := bstep (se 2 (by rfl) ⟨998385, by rfl⟩ : syracuseStep 2662361 = 1996771) B1996771
theorem B2662415 : Blo 1774088 2662415 := bstep (se 1 (by rfl) ⟨1996811, by rfl⟩ : syracuseStep 2662415 = 3993623) B3993623
theorem B2662457 : Blo 1774088 2662457 := bstep (se 2 (by rfl) ⟨998421, by rfl⟩ : syracuseStep 2662457 = 1996843) B1996843
theorem B2662535 : Blo 1774088 2662535 := bstep (se 1 (by rfl) ⟨1996901, by rfl⟩ : syracuseStep 2662535 = 3993803) B3993803
theorem B2662571 : Blo 1774088 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B2662601 : Blo 1774088 2662601 := bstep (se 2 (by rfl) ⟨998475, by rfl⟩ : syracuseStep 2662601 = 1996951) B1996951
theorem B6742217 : Blo 1774088 6742217 := bstep (se 2 (by rfl) ⟨2528331, by rfl⟩ : syracuseStep 6742217 = 5056663) B5056663
theorem B8528161 : Blo 1774088 8528161 := bstep (se 2 (by rfl) ⟨3198060, by rfl⟩ : syracuseStep 8528161 = 6396121) B6396121
theorem B2662715 : Blo 1774088 2662715 := bstep (se 1 (by rfl) ⟨1997036, by rfl⟩ : syracuseStep 2662715 = 3994073) B3994073
theorem B34586945 : Blo 1774088 34586945 := bstep (se 2 (by rfl) ⟨12970104, by rfl⟩ : syracuseStep 34586945 = 25940209) B25940209
theorem B2662775 : Blo 1774088 2662775 := bstep (se 1 (by rfl) ⟨1997081, by rfl⟩ : syracuseStep 2662775 = 3994163) B3994163
theorem B2662799 : Blo 1774088 2662799 := bstep (se 1 (by rfl) ⟨1997099, by rfl⟩ : syracuseStep 2662799 = 3994199) B3994199
theorem B8528275 : Blo 1774088 8528275 := bstep (se 1 (by rfl) ⟨6396206, by rfl⟩ : syracuseStep 8528275 = 12792413) B12792413
theorem B5988761 : Blo 1774088 5988761 := bstep (se 2 (by rfl) ⟨2245785, by rfl⟩ : syracuseStep 5988761 = 4491571) B4491571
theorem B2662841 : Blo 1774088 2662841 := bstep (se 2 (by rfl) ⟨998565, by rfl⟩ : syracuseStep 2662841 = 1997131) B1997131
theorem B5054977 : Blo 1774088 5054977 := bstep (se 2 (by rfl) ⟨1895616, by rfl⟩ : syracuseStep 5054977 = 3791233) B3791233
theorem B18211331 : Blo 1774088 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B2662919 : Blo 1774088 2662919 := bstep (se 1 (by rfl) ⟨1997189, by rfl⟩ : syracuseStep 2662919 = 3994379) B3994379
theorem B2662955 : Blo 1774088 2662955 := bstep (se 1 (by rfl) ⟨1997216, by rfl⟩ : syracuseStep 2662955 = 3994433) B3994433
theorem B2662985 : Blo 1774088 2662985 := bstep (se 2 (by rfl) ⟨998619, by rfl⟩ : syracuseStep 2662985 = 1997239) B1997239
theorem B2663099 : Blo 1774088 2663099 := bstep (se 1 (by rfl) ⟨1997324, by rfl⟩ : syracuseStep 2663099 = 3994649) B3994649
theorem B2663159 : Blo 1774088 2663159 := bstep (se 1 (by rfl) ⟨1997369, by rfl⟩ : syracuseStep 2663159 = 3994739) B3994739
theorem B2663183 : Blo 1774088 2663183 := bstep (se 1 (by rfl) ⟨1997387, by rfl⟩ : syracuseStep 2663183 = 3994775) B3994775
theorem B2663225 : Blo 1774088 2663225 := bstep (se 2 (by rfl) ⟨998709, by rfl⟩ : syracuseStep 2663225 = 1997419) B1997419
theorem B2663303 : Blo 1774088 2663303 := bstep (se 1 (by rfl) ⟨1997477, by rfl⟩ : syracuseStep 2663303 = 3994955) B3994955
theorem B2663339 : Blo 1774088 2663339 := bstep (se 1 (by rfl) ⟨1997504, by rfl⟩ : syracuseStep 2663339 = 3995009) B3995009
theorem B2663369 : Blo 1774088 2663369 := bstep (se 2 (by rfl) ⟨998763, by rfl⟩ : syracuseStep 2663369 = 1997527) B1997527
theorem B2245639 : Blo 1774088 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B5055547 : Blo 1774088 5055547 := bstep (se 1 (by rfl) ⟨3791660, by rfl⟩ : syracuseStep 5055547 = 7583321) B7583321
theorem B2663483 : Blo 1774088 2663483 := bstep (se 1 (by rfl) ⟨1997612, by rfl⟩ : syracuseStep 2663483 = 3995225) B3995225
theorem B5989463 : Blo 1774088 5989463 := bstep (se 1 (by rfl) ⟨4492097, by rfl⟩ : syracuseStep 5989463 = 8984195) B8984195
theorem B2663543 : Blo 1774088 2663543 := bstep (se 1 (by rfl) ⟨1997657, by rfl⟩ : syracuseStep 2663543 = 3995315) B3995315
theorem B6743159 : Blo 1774088 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B18457733 : Blo 1774088 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B3368071 : Blo 1774088 3368071 := bstep (se 1 (by rfl) ⟨2526053, by rfl⟩ : syracuseStep 3368071 = 5052107) B5052107
theorem B2663567 : Blo 1774088 2663567 := bstep (se 1 (by rfl) ⟨1997675, by rfl⟩ : syracuseStep 2663567 = 3995351) B3995351
theorem B2663609 : Blo 1774088 2663609 := bstep (se 2 (by rfl) ⟨998853, by rfl⟩ : syracuseStep 2663609 = 1997707) B1997707
theorem B2663687 : Blo 1774088 2663687 := bstep (se 1 (by rfl) ⟨1997765, by rfl⟩ : syracuseStep 2663687 = 3995531) B3995531
theorem B2663723 : Blo 1774088 2663723 := bstep (se 1 (by rfl) ⟨1997792, by rfl⟩ : syracuseStep 2663723 = 3995585) B3995585
theorem B2663753 : Blo 1774088 2663753 := bstep (se 2 (by rfl) ⟨998907, by rfl⟩ : syracuseStep 2663753 = 1997815) B1997815
theorem B13477265 : Blo 1774088 13477265 := bstep (se 2 (by rfl) ⟨5053974, by rfl⟩ : syracuseStep 13477265 = 10107949) B10107949
theorem B2246059 : Blo 1774088 2246059 := bstep (se 1 (by rfl) ⟨1684544, by rfl⟩ : syracuseStep 2246059 = 3369089) B3369089
theorem B2663867 : Blo 1774088 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B22742477 : Blo 1774088 22742477 := bstep (se 3 (by rfl) ⟨4264214, by rfl⟩ : syracuseStep 22742477 = 8528429) B8528429
theorem B2663927 : Blo 1774088 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B11372035 : Blo 1774088 11372035 := bstep (se 1 (by rfl) ⟨8529026, by rfl⟩ : syracuseStep 11372035 = 17058053) B17058053
theorem B2663951 : Blo 1774088 2663951 := bstep (se 1 (by rfl) ⟨1997963, by rfl⟩ : syracuseStep 2663951 = 3995927) B3995927
theorem B2663993 : Blo 1774088 2663993 := bstep (se 2 (by rfl) ⟨998997, by rfl⟩ : syracuseStep 2663993 = 1997995) B1997995
theorem B5989949 : Blo 1774088 5989949 := bstep (se 3 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 5989949 = 2246231) B2246231
theorem B2664071 : Blo 1774088 2664071 := bstep (se 1 (by rfl) ⟨1998053, by rfl⟩ : syracuseStep 2664071 = 3996107) B3996107
theorem B2246287 : Blo 1774088 2246287 := bstep (se 1 (by rfl) ⟨1684715, by rfl⟩ : syracuseStep 2246287 = 3369431) B3369431
theorem B2664107 : Blo 1774088 2664107 := bstep (se 1 (by rfl) ⟨1998080, by rfl⟩ : syracuseStep 2664107 = 3996161) B3996161
theorem B10389185 : Blo 1774088 10389185 := bstep (se 2 (by rfl) ⟨3895944, by rfl⟩ : syracuseStep 10389185 = 7791889) B7791889
theorem B10110865 : Blo 1774088 10110865 := bstep (se 2 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 10110865 = 7583149) B7583149
theorem B8988569 : Blo 1774088 8988569 := bstep (se 2 (by rfl) ⟨3370713, by rfl⟩ : syracuseStep 8988569 = 6741427) B6741427
theorem B4048841 : Blo 1774088 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B6400043 : Blo 1774088 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B5400695 : Blo 1774088 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B4491521 : Blo 1774088 4491521 := bstep (se 2 (by rfl) ⟨1684320, by rfl⟩ : syracuseStep 4491521 = 3368641) B3368641
theorem B3991823 : Blo 1774088 3991823 := bstep (se 1 (by rfl) ⟨2993867, by rfl⟩ : syracuseStep 3991823 = 5987735) B5987735
theorem B3991841 : Blo 1774088 3991841 := bstep (se 2 (by rfl) ⟨1496940, by rfl⟩ : syracuseStep 3991841 = 2993881) B2993881
theorem B2247031 : Blo 1774088 2247031 := bstep (se 1 (by rfl) ⟨1685273, by rfl⟩ : syracuseStep 2247031 = 3370547) B3370547
theorem B15378835 : Blo 1774088 15378835 := bstep (se 1 (by rfl) ⟨11534126, by rfl⟩ : syracuseStep 15378835 = 23068253) B23068253
theorem B5122457 : Blo 1774088 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B3197369 : Blo 1774088 3197369 := bstep (se 2 (by rfl) ⟨1199013, by rfl⟩ : syracuseStep 3197369 = 2398027) B2398027
theorem B20212253 : Blo 1774088 20212253 := bstep (se 3 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 20212253 = 7579595) B7579595
theorem B3992183 : Blo 1774088 3992183 := bstep (se 1 (by rfl) ⟨2994137, by rfl⟩ : syracuseStep 3992183 = 5988275) B5988275
theorem B4491895 : Blo 1774088 4491895 := bstep (se 1 (by rfl) ⟨3368921, by rfl⟩ : syracuseStep 4491895 = 6737843) B6737843
theorem B7580279 : Blo 1774088 7580279 := bstep (se 1 (by rfl) ⟨5685209, by rfl⟩ : syracuseStep 7580279 = 11370419) B11370419
theorem B5687927 : Blo 1774088 5687927 := bstep (se 1 (by rfl) ⟨4265945, by rfl⟩ : syracuseStep 5687927 = 8531891) B8531891
theorem B2247355 : Blo 1774088 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B12315329 : Blo 1774088 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B3992363 : Blo 1774088 3992363 := bstep (se 1 (by rfl) ⟨2994272, by rfl⟩ : syracuseStep 3992363 = 5988545) B5988545
theorem B3369863 : Blo 1774088 3369863 := bstep (se 1 (by rfl) ⟨2527397, by rfl⟩ : syracuseStep 3369863 = 5054795) B5054795
theorem B5991353 : Blo 1774088 5991353 := bstep (se 2 (by rfl) ⟨2246757, by rfl⟩ : syracuseStep 5991353 = 4493515) B4493515
theorem B3599375 : Blo 1774088 3599375 := bstep (se 1 (by rfl) ⟨2699531, by rfl⟩ : syracuseStep 3599375 = 5399063) B5399063
theorem B163998755 : Blo 1774088 163998755 := bstep (se 1 (by rfl) ⟨122999066, by rfl⟩ : syracuseStep 163998755 = 245998133) B245998133
theorem B4492331 : Blo 1774088 4492331 := bstep (se 1 (by rfl) ⟨3369248, by rfl⟩ : syracuseStep 4492331 = 6738497) B6738497
theorem B3992723 : Blo 1774088 3992723 := bstep (se 1 (by rfl) ⟨2994542, by rfl⟩ : syracuseStep 3992723 = 5989085) B5989085
theorem B2247851 : Blo 1774088 2247851 := bstep (se 1 (by rfl) ⟨1685888, by rfl⟩ : syracuseStep 2247851 = 3371777) B3371777
theorem B2526395 : Blo 1774088 2526395 := bstep (se 1 (by rfl) ⟨1894796, by rfl⟩ : syracuseStep 2526395 = 3789593) B3789593
theorem B9112769 : Blo 1774088 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B3992777 : Blo 1774088 3992777 := bstep (se 2 (by rfl) ⟨1497291, by rfl⟩ : syracuseStep 3992777 = 2994583) B2994583
theorem B10104101 : Blo 1774088 10104101 := bstep (se 4 (by rfl) ⟨947259, by rfl⟩ : syracuseStep 10104101 = 1894519) B1894519
theorem B4263283 : Blo 1774088 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B17067469 : Blo 1774088 17067469 := bstep (se 3 (by rfl) ⟨3200150, by rfl⟩ : syracuseStep 17067469 = 6400301) B6400301
theorem B5991947 : Blo 1774088 5991947 := bstep (se 1 (by rfl) ⟨4493960, by rfl⟩ : syracuseStep 5991947 = 8987921) B8987921
theorem B5992055 : Blo 1774088 5992055 := bstep (se 1 (by rfl) ⟨4494041, by rfl⟩ : syracuseStep 5992055 = 8988083) B8988083
theorem B3600007 : Blo 1774088 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B64810637 : Blo 1774088 64810637 := bstep (se 3 (by rfl) ⟨12151994, by rfl⟩ : syracuseStep 64810637 = 24303989) B24303989
theorem B2993935 : Blo 1774088 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B13479695 : Blo 1774088 13479695 := bstep (se 1 (by rfl) ⟨10109771, by rfl⟩ : syracuseStep 13479695 = 20219543) B20219543
theorem B2527033 : Blo 1774088 2527033 := bstep (se 2 (by rfl) ⟨947637, by rfl⟩ : syracuseStep 2527033 = 1895275) B1895275
theorem B4493171 : Blo 1774088 4493171 := bstep (se 1 (by rfl) ⟨3369878, by rfl⟩ : syracuseStep 4493171 = 6739757) B6739757
theorem B3993479 : Blo 1774088 3993479 := bstep (se 1 (by rfl) ⟨2995109, by rfl⟩ : syracuseStep 3993479 = 5990219) B5990219
theorem B4493191 : Blo 1774088 4493191 := bstep (se 1 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 4493191 = 6739787) B6739787
theorem B20492183 : Blo 1774088 20492183 := bstep (se 1 (by rfl) ⟨15369137, by rfl⟩ : syracuseStep 20492183 = 30738275) B30738275
theorem B2527147 : Blo 1774088 2527147 := bstep (se 1 (by rfl) ⟨1895360, by rfl⟩ : syracuseStep 2527147 = 3790721) B3790721
theorem B15364043 : Blo 1774088 15364043 := bstep (se 1 (by rfl) ⟨11523032, by rfl⟩ : syracuseStep 15364043 = 23046065) B23046065
theorem B4263947 : Blo 1774088 4263947 := bstep (se 1 (by rfl) ⟨3197960, by rfl⟩ : syracuseStep 4263947 = 6395921) B6395921
theorem B9596951 : Blo 1774088 9596951 := bstep (se 1 (by rfl) ⟨7197713, by rfl⟩ : syracuseStep 9596951 = 14395427) B14395427
theorem B3993659 : Blo 1774088 3993659 := bstep (se 1 (by rfl) ⟨2995244, by rfl⟩ : syracuseStep 3993659 = 5990489) B5990489
theorem B2527375 : Blo 1774088 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B4493465 : Blo 1774088 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B3993785 : Blo 1774088 3993785 := bstep (se 2 (by rfl) ⟨1497669, by rfl⟩ : syracuseStep 3993785 = 2995339) B2995339
theorem B8532161 : Blo 1774088 8532161 := bstep (se 2 (by rfl) ⟨3199560, by rfl⟩ : syracuseStep 8532161 = 6399121) B6399121
theorem B10105033 : Blo 1774088 10105033 := bstep (se 2 (by rfl) ⟨3789387, by rfl⟩ : syracuseStep 10105033 = 7578775) B7578775
theorem B5992649 : Blo 1774088 5992649 := bstep (se 2 (by rfl) ⟨2247243, by rfl⟩ : syracuseStep 5992649 = 4494487) B4494487
theorem B10940645 : Blo 1774088 10940645 := bstep (se 4 (by rfl) ⟨1025685, by rfl⟩ : syracuseStep 10940645 = 2051371) B2051371
theorem B11374829 : Blo 1774088 11374829 := bstep (se 3 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 11374829 = 4265561) B4265561
theorem B10113281 : Blo 1774088 10113281 := bstep (se 2 (by rfl) ⟨3792480, by rfl⟩ : syracuseStep 10113281 = 7584961) B7584961
theorem B2994475 : Blo 1774088 2994475 := bstep (se 1 (by rfl) ⟨2245856, by rfl⟩ : syracuseStep 2994475 = 4491713) B4491713
theorem B4264235 : Blo 1774088 4264235 := bstep (se 1 (by rfl) ⟨3198176, by rfl⟩ : syracuseStep 4264235 = 6396353) B6396353
theorem B4493627 : Blo 1774088 4493627 := bstep (se 1 (by rfl) ⟨3370220, by rfl⟩ : syracuseStep 4493627 = 6740441) B6740441
theorem B8982899 : Blo 1774088 8982899 := bstep (se 1 (by rfl) ⟨6737174, by rfl⟩ : syracuseStep 8982899 = 13474349) B13474349
theorem B3789175 : Blo 1774088 3789175 := bstep (se 1 (by rfl) ⟨2841881, by rfl⟩ : syracuseStep 3789175 = 5683763) B5683763
theorem B6738329 : Blo 1774088 6738329 := bstep (se 2 (by rfl) ⟨2526873, by rfl⟩ : syracuseStep 6738329 = 5053747) B5053747
theorem B15159737 : Blo 1774088 15159737 := bstep (se 2 (by rfl) ⟨5684901, by rfl⟩ : syracuseStep 15159737 = 11369803) B11369803
theorem B2994617 : Blo 1774088 2994617 := bstep (se 2 (by rfl) ⟨1122981, by rfl⟩ : syracuseStep 2994617 = 2245963) B2245963
theorem B8991161 : Blo 1774088 8991161 := bstep (se 2 (by rfl) ⟨3371685, by rfl⟩ : syracuseStep 8991161 = 6743371) B6743371
theorem B1774095 : Blo 1774088 1774095 := bstep (se 1 (by rfl) ⟨1330571, by rfl⟩ : syracuseStep 1774095 = 2661143) B2661143
theorem B3994127 : Blo 1774088 3994127 := bstep (se 1 (by rfl) ⟨2995595, by rfl⟩ : syracuseStep 3994127 = 5991191) B5991191
theorem B4493839 : Blo 1774088 4493839 := bstep (se 1 (by rfl) ⟨3370379, by rfl⟩ : syracuseStep 4493839 = 6740759) B6740759
theorem B3994145 : Blo 1774088 3994145 := bstep (se 2 (by rfl) ⟨1497804, by rfl⟩ : syracuseStep 3994145 = 2995609) B2995609
theorem B1774139 : Blo 1774088 1774139 := bstep (se 1 (by rfl) ⟨1330604, by rfl⟩ : syracuseStep 1774139 = 2661209) B2661209
theorem B1774215 : Blo 1774088 1774215 := bstep (se 1 (by rfl) ⟨1330661, by rfl⟩ : syracuseStep 1774215 = 2661323) B2661323
theorem B1774223 : Blo 1774088 1774223 := bstep (se 1 (by rfl) ⟨1330667, by rfl⟩ : syracuseStep 1774223 = 2661335) B2661335
theorem B1774267 : Blo 1774088 1774267 := bstep (se 1 (by rfl) ⟨1330700, by rfl⟩ : syracuseStep 1774267 = 2661401) B2661401
theorem B1774343 : Blo 1774088 1774343 := bstep (se 1 (by rfl) ⟨1330757, by rfl⟩ : syracuseStep 1774343 = 2661515) B2661515
theorem B1774351 : Blo 1774088 1774351 := bstep (se 1 (by rfl) ⟨1330763, by rfl⟩ : syracuseStep 1774351 = 2661527) B2661527
theorem B4494113 : Blo 1774088 4494113 := bstep (se 2 (by rfl) ⟨1685292, by rfl⟩ : syracuseStep 4494113 = 3370585) B3370585
theorem B20484899 : Blo 1774088 20484899 := bstep (se 1 (by rfl) ⟨15363674, by rfl⟩ : syracuseStep 20484899 = 30727349) B30727349
theorem B68260643 : Blo 1774088 68260643 := bstep (se 1 (by rfl) ⟨51195482, by rfl⟩ : syracuseStep 68260643 = 102390965) B102390965
theorem B5395243 : Blo 1774088 5395243 := bstep (se 1 (by rfl) ⟨4046432, by rfl⟩ : syracuseStep 5395243 = 8092865) B8092865
theorem B1774395 : Blo 1774088 1774395 := bstep (se 1 (by rfl) ⟨1330796, by rfl⟩ : syracuseStep 1774395 = 2661593) B2661593
theorem B8983385 : Blo 1774088 8983385 := bstep (se 2 (by rfl) ⟨3368769, by rfl⟩ : syracuseStep 8983385 = 6737539) B6737539
theorem B3994487 : Blo 1774088 3994487 := bstep (se 1 (by rfl) ⟨2995865, by rfl⟩ : syracuseStep 3994487 = 5991731) B5991731
theorem B1774471 : Blo 1774088 1774471 := bstep (se 1 (by rfl) ⟨1330853, by rfl⟩ : syracuseStep 1774471 = 2661707) B2661707
theorem B5993351 : Blo 1774088 5993351 := bstep (se 1 (by rfl) ⟨4495013, by rfl⟩ : syracuseStep 5993351 = 8990027) B8990027
theorem B1774479 : Blo 1774088 1774479 := bstep (se 1 (by rfl) ⟨1330859, by rfl⟩ : syracuseStep 1774479 = 2661719) B2661719
theorem B1774523 : Blo 1774088 1774523 := bstep (se 1 (by rfl) ⟨1330892, by rfl⟩ : syracuseStep 1774523 = 2661785) B2661785
theorem B19190789 : Blo 1774088 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B1774599 : Blo 1774088 1774599 := bstep (se 1 (by rfl) ⟨1330949, by rfl⟩ : syracuseStep 1774599 = 2661899) B2661899
theorem B2528263 : Blo 1774088 2528263 := bstep (se 1 (by rfl) ⟨1896197, by rfl⟩ : syracuseStep 2528263 = 3792395) B3792395
theorem B20771851 : Blo 1774088 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B1774607 : Blo 1774088 1774607 := bstep (se 1 (by rfl) ⟨1330955, by rfl⟩ : syracuseStep 1774607 = 2661911) B2661911
theorem B3994667 : Blo 1774088 3994667 := bstep (se 1 (by rfl) ⟨2996000, by rfl⟩ : syracuseStep 3994667 = 5992001) B5992001
theorem B1774651 : Blo 1774088 1774651 := bstep (se 1 (by rfl) ⟨1330988, by rfl⟩ : syracuseStep 1774651 = 2661977) B2661977
theorem B2995319 : Blo 1774088 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B1774727 : Blo 1774088 1774727 := bstep (se 1 (by rfl) ⟨1331045, by rfl⟩ : syracuseStep 1774727 = 2662091) B2662091
theorem B1774735 : Blo 1774088 1774735 := bstep (se 1 (by rfl) ⟨1331051, by rfl⟩ : syracuseStep 1774735 = 2662103) B2662103
theorem B1774779 : Blo 1774088 1774779 := bstep (se 1 (by rfl) ⟨1331084, by rfl⟩ : syracuseStep 1774779 = 2662169) B2662169
theorem B5993729 : Blo 1774088 5993729 := bstep (se 2 (by rfl) ⟨2247648, by rfl⟩ : syracuseStep 5993729 = 4495297) B4495297
theorem B1774855 : Blo 1774088 1774855 := bstep (se 1 (by rfl) ⟨1331141, by rfl⟩ : syracuseStep 1774855 = 2662283) B2662283
theorem B1774863 : Blo 1774088 1774863 := bstep (se 1 (by rfl) ⟨1331147, by rfl⟩ : syracuseStep 1774863 = 2662295) B2662295
theorem B1774907 : Blo 1774088 1774907 := bstep (se 1 (by rfl) ⟨1331180, by rfl⟩ : syracuseStep 1774907 = 2662361) B2662361
theorem B1774983 : Blo 1774088 1774983 := bstep (se 1 (by rfl) ⟨1331237, by rfl⟩ : syracuseStep 1774983 = 2662475) B2662475
theorem B1774991 : Blo 1774088 1774991 := bstep (se 1 (by rfl) ⟨1331243, by rfl⟩ : syracuseStep 1774991 = 2662487) B2662487
theorem B3995027 : Blo 1774088 3995027 := bstep (se 1 (by rfl) ⟨2996270, by rfl⟩ : syracuseStep 3995027 = 5992541) B5992541
theorem B1775035 : Blo 1774088 1775035 := bstep (se 1 (by rfl) ⟨1331276, by rfl⟩ : syracuseStep 1775035 = 2662553) B2662553
theorem B3995081 : Blo 1774088 3995081 := bstep (se 2 (by rfl) ⟨1498155, by rfl⟩ : syracuseStep 3995081 = 2996311) B2996311
theorem B2528759 : Blo 1774088 2528759 := bstep (se 1 (by rfl) ⟨1896569, by rfl⟩ : syracuseStep 2528759 = 3793139) B3793139
theorem B16193027 : Blo 1774088 16193027 := bstep (se 1 (by rfl) ⟨12144770, by rfl⟩ : syracuseStep 16193027 = 24289541) B24289541
theorem B1775111 : Blo 1774088 1775111 := bstep (se 1 (by rfl) ⟨1331333, by rfl⟩ : syracuseStep 1775111 = 2662667) B2662667
theorem B1996303 : Blo 1774088 1996303 := bstep (se 1 (by rfl) ⟨1497227, by rfl⟩ : syracuseStep 1996303 = 2994455) B2994455
theorem B1775119 : Blo 1774088 1775119 := bstep (se 1 (by rfl) ⟨1331339, by rfl⟩ : syracuseStep 1775119 = 2662679) B2662679
theorem B1775163 : Blo 1774088 1775163 := bstep (se 1 (by rfl) ⟨1331372, by rfl⟩ : syracuseStep 1775163 = 2662745) B2662745
theorem B2995771 : Blo 1774088 2995771 := bstep (se 1 (by rfl) ⟨2246828, by rfl⟩ : syracuseStep 2995771 = 4493657) B4493657
theorem B7198327 : Blo 1774088 7198327 := bstep (se 1 (by rfl) ⟨5398745, by rfl⟩ : syracuseStep 7198327 = 10797491) B10797491
theorem B1775239 : Blo 1774088 1775239 := bstep (se 1 (by rfl) ⟨1331429, by rfl⟩ : syracuseStep 1775239 = 2662859) B2662859
theorem B1775247 : Blo 1774088 1775247 := bstep (se 1 (by rfl) ⟨1331435, by rfl⟩ : syracuseStep 1775247 = 2662871) B2662871
theorem B2561707 : Blo 1774088 2561707 := bstep (se 1 (by rfl) ⟨1921280, by rfl⟩ : syracuseStep 2561707 = 3842561) B3842561
theorem B1775291 : Blo 1774088 1775291 := bstep (se 1 (by rfl) ⟨1331468, by rfl⟩ : syracuseStep 1775291 = 2662937) B2662937
theorem B2995913 : Blo 1774088 2995913 := bstep (se 2 (by rfl) ⟨1123467, by rfl⟩ : syracuseStep 2995913 = 2246935) B2246935
theorem B1775367 : Blo 1774088 1775367 := bstep (se 1 (by rfl) ⟨1331525, by rfl⟩ : syracuseStep 1775367 = 2663051) B2663051
theorem B4495115 : Blo 1774088 4495115 := bstep (se 1 (by rfl) ⟨3371336, by rfl⟩ : syracuseStep 4495115 = 6742673) B6742673
theorem B1775375 : Blo 1774088 1775375 := bstep (se 1 (by rfl) ⟨1331531, by rfl⟩ : syracuseStep 1775375 = 2663063) B2663063
theorem B8533811 : Blo 1774088 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B1775419 : Blo 1774088 1775419 := bstep (se 1 (by rfl) ⟨1331564, by rfl⟩ : syracuseStep 1775419 = 2663129) B2663129
theorem B1775495 : Blo 1774088 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B1775503 : Blo 1774088 1775503 := bstep (se 1 (by rfl) ⟨1331627, by rfl⟩ : syracuseStep 1775503 = 2663255) B2663255
theorem B1775547 : Blo 1774088 1775547 := bstep (se 1 (by rfl) ⟨1331660, by rfl⟩ : syracuseStep 1775547 = 2663321) B2663321
theorem B1996807 : Blo 1774088 1996807 := bstep (se 1 (by rfl) ⟨1497605, by rfl⟩ : syracuseStep 1996807 = 2995211) B2995211
theorem B1775623 : Blo 1774088 1775623 := bstep (se 1 (by rfl) ⟨1331717, by rfl⟩ : syracuseStep 1775623 = 2663435) B2663435
theorem B1775631 : Blo 1774088 1775631 := bstep (se 1 (by rfl) ⟨1331723, by rfl⟩ : syracuseStep 1775631 = 2663447) B2663447
theorem B11368471 : Blo 1774088 11368471 := bstep (se 1 (by rfl) ⟨8526353, by rfl⟩ : syracuseStep 11368471 = 17052707) B17052707
theorem B5052449 : Blo 1774088 5052449 := bstep (se 2 (by rfl) ⟨1894668, by rfl⟩ : syracuseStep 5052449 = 3789337) B3789337
theorem B3790891 : Blo 1774088 3790891 := bstep (se 1 (by rfl) ⟨2843168, by rfl⟩ : syracuseStep 3790891 = 5686337) B5686337
theorem B1775675 : Blo 1774088 1775675 := bstep (se 1 (by rfl) ⟨1331756, by rfl⟩ : syracuseStep 1775675 = 2663513) B2663513
theorem B1775751 : Blo 1774088 1775751 := bstep (se 1 (by rfl) ⟨1331813, by rfl⟩ : syracuseStep 1775751 = 2663627) B2663627
theorem B3995783 : Blo 1774088 3995783 := bstep (se 1 (by rfl) ⟨2996837, by rfl⟩ : syracuseStep 3995783 = 5993675) B5993675
theorem B1775759 : Blo 1774088 1775759 := bstep (se 1 (by rfl) ⟨1331819, by rfl⟩ : syracuseStep 1775759 = 2663639) B2663639
theorem B5052563 : Blo 1774088 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B4266137 : Blo 1774088 4266137 := bstep (se 2 (by rfl) ⟨1599801, by rfl⟩ : syracuseStep 4266137 = 3199603) B3199603
theorem B1996987 : Blo 1774088 1996987 := bstep (se 1 (by rfl) ⟨1497740, by rfl⟩ : syracuseStep 1996987 = 2995481) B2995481
theorem B1775803 : Blo 1774088 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B1775879 : Blo 1774088 1775879 := bstep (se 1 (by rfl) ⟨1331909, by rfl⟩ : syracuseStep 1775879 = 2663819) B2663819
theorem B1775887 : Blo 1774088 1775887 := bstep (se 1 (by rfl) ⟨1331915, by rfl⟩ : syracuseStep 1775887 = 2663831) B2663831
theorem B4266283 : Blo 1774088 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B1775931 : Blo 1774088 1775931 := bstep (se 1 (by rfl) ⟨1331948, by rfl⟩ : syracuseStep 1775931 = 2663897) B2663897
theorem B3995963 : Blo 1774088 3995963 := bstep (se 1 (by rfl) ⟨2996972, by rfl⟩ : syracuseStep 3995963 = 5993945) B5993945
theorem B4266359 : Blo 1774088 4266359 := bstep (se 1 (by rfl) ⟨3199769, by rfl⟩ : syracuseStep 4266359 = 6399539) B6399539
theorem B2996615 : Blo 1774088 2996615 := bstep (se 1 (by rfl) ⟨2247461, by rfl⟩ : syracuseStep 2996615 = 4494923) B4494923
theorem B1776007 : Blo 1774088 1776007 := bstep (se 1 (by rfl) ⟨1332005, by rfl⟩ : syracuseStep 1776007 = 2664011) B2664011
theorem B1776015 : Blo 1774088 1776015 := bstep (se 1 (by rfl) ⟨1332011, by rfl⟩ : syracuseStep 1776015 = 2664023) B2664023
theorem B7297465 : Blo 1774088 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B9599417 : Blo 1774088 9599417 := bstep (se 2 (by rfl) ⟨3599781, by rfl⟩ : syracuseStep 9599417 = 7199563) B7199563
theorem B3996089 : Blo 1774088 3996089 := bstep (se 2 (by rfl) ⟨1498533, by rfl⟩ : syracuseStep 3996089 = 2997067) B2997067
theorem B1776059 : Blo 1774088 1776059 := bstep (se 1 (by rfl) ⟨1332044, by rfl⟩ : syracuseStep 1776059 = 2664089) B2664089
theorem B15170125 : Blo 1774088 15170125 := bstep (se 3 (by rfl) ⟨2844398, by rfl⟩ : syracuseStep 15170125 = 5688797) B5688797
theorem B16194167 : Blo 1774088 16194167 := bstep (se 1 (by rfl) ⟨12145625, by rfl⟩ : syracuseStep 16194167 = 24291251) B24291251
theorem B1997455 : Blo 1774088 1997455 := bstep (se 1 (by rfl) ⟨1498091, by rfl⟩ : syracuseStep 1997455 = 2996183) B2996183
theorem B20216627 : Blo 1774088 20216627 := bstep (se 1 (by rfl) ⟨15162470, by rfl⟩ : syracuseStep 20216627 = 30324941) B30324941
theorem B2661179 : Blo 1774088 2661179 := bstep (se 1 (by rfl) ⟨1995884, by rfl⟩ : syracuseStep 2661179 = 3991769) B3991769
theorem B2661239 : Blo 1774088 2661239 := bstep (se 1 (by rfl) ⟨1995929, by rfl⟩ : syracuseStep 2661239 = 3991859) B3991859
theorem B2661263 : Blo 1774088 2661263 := bstep (se 1 (by rfl) ⟨1995947, by rfl⟩ : syracuseStep 2661263 = 3991895) B3991895
theorem B8985491 : Blo 1774088 8985491 := bstep (se 1 (by rfl) ⟨6739118, by rfl⟩ : syracuseStep 8985491 = 13478237) B13478237
theorem B5053337 : Blo 1774088 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B36420515 : Blo 1774088 36420515 := bstep (se 1 (by rfl) ⟨27315386, by rfl⟩ : syracuseStep 36420515 = 54630773) B54630773
theorem B2661305 : Blo 1774088 2661305 := bstep (se 2 (by rfl) ⟨997989, by rfl⟩ : syracuseStep 2661305 = 1995979) B1995979
theorem B2661383 : Blo 1774088 2661383 := bstep (se 1 (by rfl) ⟨1996037, by rfl⟩ : syracuseStep 2661383 = 3992075) B3992075
theorem B2661419 : Blo 1774088 2661419 := bstep (se 1 (by rfl) ⟨1996064, by rfl⟩ : syracuseStep 2661419 = 3992129) B3992129
theorem B2661449 : Blo 1774088 2661449 := bstep (se 2 (by rfl) ⟨998043, by rfl⟩ : syracuseStep 2661449 = 1996087) B1996087
theorem B1997959 : Blo 1774088 1997959 := bstep (se 1 (by rfl) ⟨1498469, by rfl⟩ : syracuseStep 1997959 = 2996939) B2996939
theorem B64773269 : Blo 1774088 64773269 := bstep (se 6 (by rfl) ⟨1518123, by rfl⟩ : syracuseStep 64773269 = 3036247) B3036247
theorem B2841785 : Blo 1774088 2841785 := bstep (se 2 (by rfl) ⟨1065669, by rfl⟩ : syracuseStep 2841785 = 2131339) B2131339
theorem B2661563 : Blo 1774088 2661563 := bstep (se 1 (by rfl) ⟨1996172, by rfl⟩ : syracuseStep 2661563 = 3992345) B3992345
theorem B2661623 : Blo 1774088 2661623 := bstep (se 1 (by rfl) ⟨1996217, by rfl⟩ : syracuseStep 2661623 = 3992435) B3992435
theorem B2661647 : Blo 1774088 2661647 := bstep (se 1 (by rfl) ⟨1996235, by rfl⟩ : syracuseStep 2661647 = 3992471) B3992471
theorem B2661689 : Blo 1774088 2661689 := bstep (se 2 (by rfl) ⟨998133, by rfl⟩ : syracuseStep 2661689 = 1996267) B1996267
theorem B25582979 : Blo 1774088 25582979 := bstep (se 1 (by rfl) ⟨19187234, by rfl⟩ : syracuseStep 25582979 = 38374469) B38374469
theorem B2661767 : Blo 1774088 2661767 := bstep (se 1 (by rfl) ⟨1996325, by rfl⟩ : syracuseStep 2661767 = 3992651) B3992651
theorem B2661803 : Blo 1774088 2661803 := bstep (se 1 (by rfl) ⟨1996352, by rfl⟩ : syracuseStep 2661803 = 3992705) B3992705
theorem B2661833 : Blo 1774088 2661833 := bstep (se 2 (by rfl) ⟨998187, by rfl⟩ : syracuseStep 2661833 = 1996375) B1996375
theorem B13147651 : Blo 1774088 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B2661947 : Blo 1774088 2661947 := bstep (se 1 (by rfl) ⟨1996460, by rfl⟩ : syracuseStep 2661947 = 3992921) B3992921
theorem B2662007 : Blo 1774088 2662007 := bstep (se 1 (by rfl) ⟨1996505, by rfl⟩ : syracuseStep 2662007 = 3993011) B3993011
theorem B2662031 : Blo 1774088 2662031 := bstep (se 1 (by rfl) ⟨1996523, by rfl⟩ : syracuseStep 2662031 = 3993047) B3993047
theorem B2662073 : Blo 1774088 2662073 := bstep (se 2 (by rfl) ⟨998277, by rfl⟩ : syracuseStep 2662073 = 1996555) B1996555
theorem B4800185 : Blo 1774088 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B6487789 : Blo 1774088 6487789 := bstep (se 3 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 6487789 = 2432921) B2432921
theorem B2662151 : Blo 1774088 2662151 := bstep (se 1 (by rfl) ⟨1996613, by rfl⟩ : syracuseStep 2662151 = 3993227) B3993227
theorem B2662187 : Blo 1774088 2662187 := bstep (se 1 (by rfl) ⟨1996640, by rfl⟩ : syracuseStep 2662187 = 3993281) B3993281
theorem B9592627 : Blo 1774088 9592627 := bstep (se 1 (by rfl) ⟨7194470, by rfl⟩ : syracuseStep 9592627 = 14388941) B14388941
theorem B7585595 : Blo 1774088 7585595 := bstep (se 1 (by rfl) ⟨5689196, by rfl⟩ : syracuseStep 7585595 = 11378393) B11378393
theorem B2662217 : Blo 1774088 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B4865939 : Blo 1774088 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B6741913 : Blo 1774088 6741913 := bstep (se 2 (by rfl) ⟨2528217, by rfl⟩ : syracuseStep 6741913 = 5056435) B5056435
theorem B2662331 : Blo 1774088 2662331 := bstep (se 1 (by rfl) ⟨1996748, by rfl⟩ : syracuseStep 2662331 = 3993497) B3993497
theorem B2662391 : Blo 1774088 2662391 := bstep (se 1 (by rfl) ⟨1996793, by rfl⟩ : syracuseStep 2662391 = 3993587) B3993587
theorem B2842631 : Blo 1774088 2842631 := bstep (se 1 (by rfl) ⟨2131973, by rfl⟩ : syracuseStep 2842631 = 4263947) B4263947
theorem B2662409 : Blo 1774088 2662409 := bstep (se 2 (by rfl) ⟨998403, by rfl⟩ : syracuseStep 2662409 = 1996807) B1996807
theorem B6397967 : Blo 1774088 6397967 := bstep (se 1 (by rfl) ⟨4798475, by rfl⟩ : syracuseStep 6397967 = 9596951) B9596951
theorem B13484069 : Blo 1774088 13484069 := bstep (se 4 (by rfl) ⟨1264131, by rfl⟩ : syracuseStep 13484069 = 2528263) B2528263
theorem B2662439 : Blo 1774088 2662439 := bstep (se 1 (by rfl) ⟨1996829, by rfl⟩ : syracuseStep 2662439 = 3993659) B3993659
theorem B2662523 : Blo 1774088 2662523 := bstep (se 1 (by rfl) ⟨1996892, by rfl⟩ : syracuseStep 2662523 = 3993785) B3993785
theorem B76800149 : Blo 1774088 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B6742187 : Blo 1774088 6742187 := bstep (se 1 (by rfl) ⟨5056640, by rfl⟩ : syracuseStep 6742187 = 10113281) B10113281
theorem B2842823 : Blo 1774088 2842823 := bstep (se 1 (by rfl) ⟨2132117, by rfl⟩ : syracuseStep 2842823 = 4264235) B4264235
theorem B20218085 : Blo 1774088 20218085 := bstep (se 4 (by rfl) ⟨1895445, by rfl⟩ : syracuseStep 20218085 = 3790891) B3790891
theorem B5988599 : Blo 1774088 5988599 := bstep (se 1 (by rfl) ⟨4491449, by rfl⟩ : syracuseStep 5988599 = 8982899) B8982899
theorem B2662649 : Blo 1774088 2662649 := bstep (se 2 (by rfl) ⟨998493, by rfl⟩ : syracuseStep 2662649 = 1996987) B1996987
theorem B12140887 : Blo 1774088 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B2662751 : Blo 1774088 2662751 := bstep (se 1 (by rfl) ⟨1997063, by rfl⟩ : syracuseStep 2662751 = 3994127) B3994127
theorem B2662763 : Blo 1774088 2662763 := bstep (se 1 (by rfl) ⟨1997072, by rfl⟩ : syracuseStep 2662763 = 3994145) B3994145
theorem B11370881 : Blo 1774088 11370881 := bstep (se 2 (by rfl) ⟨4264080, by rfl⟩ : syracuseStep 11370881 = 8528161) B8528161
theorem B13656599 : Blo 1774088 13656599 := bstep (se 1 (by rfl) ⟨10242449, by rfl⟩ : syracuseStep 13656599 = 20484899) B20484899
theorem B11371033 : Blo 1774088 11371033 := bstep (se 2 (by rfl) ⟨4264137, by rfl⟩ : syracuseStep 11371033 = 8528275) B8528275
theorem B45507095 : Blo 1774088 45507095 := bstep (se 1 (by rfl) ⟨34130321, by rfl⟩ : syracuseStep 45507095 = 68260643) B68260643
theorem B20505113 : Blo 1774088 20505113 := bstep (se 2 (by rfl) ⟨7689417, by rfl⟩ : syracuseStep 20505113 = 15378835) B15378835
theorem B5988923 : Blo 1774088 5988923 := bstep (se 1 (by rfl) ⟨4491692, by rfl⟩ : syracuseStep 5988923 = 8983385) B8983385
theorem B2662991 : Blo 1774088 2662991 := bstep (se 1 (by rfl) ⟨1997243, by rfl⟩ : syracuseStep 2662991 = 3994487) B3994487
theorem B2663111 : Blo 1774088 2663111 := bstep (se 1 (by rfl) ⟨1997333, by rfl⟩ : syracuseStep 2663111 = 3994667) B3994667
theorem B20226833 : Blo 1774088 20226833 := bstep (se 2 (by rfl) ⟨7585062, by rfl⟩ : syracuseStep 20226833 = 15170125) B15170125
theorem B5989193 : Blo 1774088 5989193 := bstep (se 2 (by rfl) ⟨2245947, by rfl⟩ : syracuseStep 5989193 = 4491895) B4491895
theorem B2663273 : Blo 1774088 2663273 := bstep (se 2 (by rfl) ⟨998727, by rfl⟩ : syracuseStep 2663273 = 1997455) B1997455
theorem B2663351 : Blo 1774088 2663351 := bstep (se 1 (by rfl) ⟨1997513, by rfl⟩ : syracuseStep 2663351 = 3995027) B3995027
theorem B2663387 : Blo 1774088 2663387 := bstep (se 1 (by rfl) ⟨1997540, by rfl⟩ : syracuseStep 2663387 = 3995081) B3995081
theorem B7193657 : Blo 1774088 7193657 := bstep (se 2 (by rfl) ⟨2697621, by rfl⟩ : syracuseStep 7193657 = 5395243) B5395243
theorem B6743357 : Blo 1774088 6743357 := bstep (se 3 (by rfl) ⟨1264379, by rfl⟩ : syracuseStep 6743357 = 2528759) B2528759
theorem B3368299 : Blo 1774088 3368299 := bstep (se 1 (by rfl) ⟨2526224, by rfl⟩ : syracuseStep 3368299 = 5052449) B5052449
theorem B2663855 : Blo 1774088 2663855 := bstep (se 1 (by rfl) ⟨1997891, by rfl⟩ : syracuseStep 2663855 = 3995783) B3995783
theorem B3368375 : Blo 1774088 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B2844091 : Blo 1774088 2844091 := bstep (se 1 (by rfl) ⟨2133068, by rfl⟩ : syracuseStep 2844091 = 4266137) B4266137
theorem B4490761 : Blo 1774088 4490761 := bstep (se 2 (by rfl) ⟨1684035, by rfl⟩ : syracuseStep 4490761 = 3368071) B3368071
theorem B2663945 : Blo 1774088 2663945 := bstep (se 2 (by rfl) ⟨998979, by rfl⟩ : syracuseStep 2663945 = 1997959) B1997959
theorem B2663975 : Blo 1774088 2663975 := bstep (se 1 (by rfl) ⟨1997981, by rfl⟩ : syracuseStep 2663975 = 3995963) B3995963
theorem B2844239 : Blo 1774088 2844239 := bstep (se 1 (by rfl) ⟨2133179, by rfl⟩ : syracuseStep 2844239 = 4266359) B4266359
theorem B2131579 : Blo 1774088 2131579 := bstep (se 1 (by rfl) ⟨1598684, by rfl⟩ : syracuseStep 2131579 = 3197369) B3197369
theorem B6399611 : Blo 1774088 6399611 := bstep (se 1 (by rfl) ⟨4799708, by rfl⟩ : syracuseStep 6399611 = 9599417) B9599417
theorem B2664059 : Blo 1774088 2664059 := bstep (se 1 (by rfl) ⟨1998044, by rfl⟩ : syracuseStep 2664059 = 3996089) B3996089
theorem B8210219 : Blo 1774088 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B13477751 : Blo 1774088 13477751 := bstep (se 1 (by rfl) ⟨10108313, by rfl⟩ : syracuseStep 13477751 = 20216627) B20216627
theorem B5990327 : Blo 1774088 5990327 := bstep (se 1 (by rfl) ⟨4492745, by rfl⟩ : syracuseStep 5990327 = 8985491) B8985491
theorem B3368891 : Blo 1774088 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B109332503 : Blo 1774088 109332503 := bstep (se 1 (by rfl) ⟨81999377, by rfl⟩ : syracuseStep 109332503 = 163998755) B163998755
theorem B43182179 : Blo 1774088 43182179 := bstep (se 1 (by rfl) ⟨32386634, by rfl⟩ : syracuseStep 43182179 = 64773269) B64773269
theorem B1894523 : Blo 1774088 1894523 := bstep (se 1 (by rfl) ⟨1420892, by rfl⟩ : syracuseStep 1894523 = 2841785) B2841785
theorem B6736067 : Blo 1774088 6736067 := bstep (se 1 (by rfl) ⟨5052050, by rfl⟩ : syracuseStep 6736067 = 10104101) B10104101
theorem B3991913 : Blo 1774088 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B12790169 : Blo 1774088 12790169 := bstep (se 2 (by rfl) ⟨4796313, by rfl⟩ : syracuseStep 12790169 = 9592627) B9592627
theorem B3369377 : Blo 1774088 3369377 := bstep (se 2 (by rfl) ⟨1263516, by rfl⟩ : syracuseStep 3369377 = 2527033) B2527033
theorem B43207091 : Blo 1774088 43207091 := bstep (se 1 (by rfl) ⟨32405318, by rfl⟩ : syracuseStep 43207091 = 64810637) B64810637
theorem B5990921 : Blo 1774088 5990921 := bstep (se 2 (by rfl) ⟨2246595, by rfl⟩ : syracuseStep 5990921 = 4493191) B4493191
theorem B8989217 : Blo 1774088 8989217 := bstep (se 2 (by rfl) ⟨3370956, by rfl⟩ : syracuseStep 8989217 = 6741913) B6741913
theorem B5057063 : Blo 1774088 5057063 := bstep (se 1 (by rfl) ⟨3792797, by rfl⟩ : syracuseStep 5057063 = 7585595) B7585595
theorem B3369529 : Blo 1774088 3369529 := bstep (se 2 (by rfl) ⟨1263573, by rfl⟩ : syracuseStep 3369529 = 2527147) B2527147
theorem B10242695 : Blo 1774088 10242695 := bstep (se 1 (by rfl) ⟨7682021, by rfl⟩ : syracuseStep 10242695 = 15364043) B15364043
theorem B15157961 : Blo 1774088 15157961 := bstep (se 2 (by rfl) ⟨5684235, by rfl⟩ : syracuseStep 15157961 = 11368471) B11368471
theorem B5688107 : Blo 1774088 5688107 := bstep (se 1 (by rfl) ⟨4266080, by rfl⟩ : syracuseStep 5688107 = 8532161) B8532161
theorem B7293763 : Blo 1774088 7293763 := bstep (se 1 (by rfl) ⟨5470322, by rfl⟩ : syracuseStep 7293763 = 10940645) B10940645
theorem B3369833 : Blo 1774088 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B3992507 : Blo 1774088 3992507 := bstep (se 1 (by rfl) ⟨2994380, by rfl⟩ : syracuseStep 3992507 = 5988761) B5988761
theorem B4492219 : Blo 1774088 4492219 := bstep (se 1 (by rfl) ⟨3369164, by rfl⟩ : syracuseStep 4492219 = 6738329) B6738329
theorem B49220621 : Blo 1774088 49220621 := bstep (se 3 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 49220621 = 18457733) B18457733
theorem B3992633 : Blo 1774088 3992633 := bstep (se 2 (by rfl) ⟨1497237, by rfl⟩ : syracuseStep 3992633 = 2994475) B2994475
theorem B5688377 : Blo 1774088 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B6737053 : Blo 1774088 6737053 := bstep (se 3 (by rfl) ⟨1263197, by rfl⟩ : syracuseStep 6737053 = 2526395) B2526395
theorem B38391077 : Blo 1774088 38391077 := bstep (se 4 (by rfl) ⟨3599163, by rfl⟩ : syracuseStep 38391077 = 7198327) B7198327
theorem B5991785 : Blo 1774088 5991785 := bstep (se 2 (by rfl) ⟨2246919, by rfl⟩ : syracuseStep 5991785 = 4493839) B4493839
theorem B3992975 : Blo 1774088 3992975 := bstep (se 1 (by rfl) ⟨2994731, by rfl⟩ : syracuseStep 3992975 = 5989463) B5989463
theorem B3993299 : Blo 1774088 3993299 := bstep (se 1 (by rfl) ⟨2994974, by rfl⟩ : syracuseStep 3993299 = 5989949) B5989949
theorem B6926123 : Blo 1774088 6926123 := bstep (se 1 (by rfl) ⟨5194592, by rfl⟩ : syracuseStep 6926123 = 10389185) B10389185
theorem B5689207 : Blo 1774088 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B5992379 : Blo 1774088 5992379 := bstep (se 1 (by rfl) ⟨4494284, by rfl⟩ : syracuseStep 5992379 = 8988569) B8988569
theorem B2699227 : Blo 1774088 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2994185 : Blo 1774088 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B3600463 : Blo 1774088 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B2994347 : Blo 1774088 2994347 := bstep (se 1 (by rfl) ⟨2245760, by rfl⟩ : syracuseStep 2994347 = 4491521) B4491521
theorem B1774119 : Blo 1774088 1774119 := bstep (se 1 (by rfl) ⟨1330589, by rfl⟩ : syracuseStep 1774119 = 2661179) B2661179
theorem B2994745 : Blo 1774088 2994745 := bstep (se 2 (by rfl) ⟨1123029, by rfl⟩ : syracuseStep 2994745 = 2246059) B2246059
theorem B1774159 : Blo 1774088 1774159 := bstep (se 1 (by rfl) ⟨1330619, by rfl⟩ : syracuseStep 1774159 = 2661239) B2661239
theorem B1774175 : Blo 1774088 1774175 := bstep (se 1 (by rfl) ⟨1330631, by rfl⟩ : syracuseStep 1774175 = 2661263) B2661263
theorem B22737509 : Blo 1774088 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B1774203 : Blo 1774088 1774203 := bstep (se 1 (by rfl) ⟨1330652, by rfl⟩ : syracuseStep 1774203 = 2661305) B2661305
theorem B3994235 : Blo 1774088 3994235 := bstep (se 1 (by rfl) ⟨2995676, by rfl⟩ : syracuseStep 3994235 = 5991353) B5991353
theorem B1774255 : Blo 1774088 1774255 := bstep (se 1 (by rfl) ⟨1330691, by rfl⟩ : syracuseStep 1774255 = 2661383) B2661383
theorem B1774279 : Blo 1774088 1774279 := bstep (se 1 (by rfl) ⟨1330709, by rfl⟩ : syracuseStep 1774279 = 2661419) B2661419
theorem B2994887 : Blo 1774088 2994887 := bstep (se 1 (by rfl) ⟨2246165, by rfl⟩ : syracuseStep 2994887 = 4492331) B4492331
theorem B1774299 : Blo 1774088 1774299 := bstep (se 1 (by rfl) ⟨1330724, by rfl⟩ : syracuseStep 1774299 = 2661449) B2661449
theorem B3994361 : Blo 1774088 3994361 := bstep (se 2 (by rfl) ⟨1497885, by rfl⟩ : syracuseStep 3994361 = 2995771) B2995771
theorem B1774375 : Blo 1774088 1774375 := bstep (se 1 (by rfl) ⟨1330781, by rfl⟩ : syracuseStep 1774375 = 2661563) B2661563
theorem B6075179 : Blo 1774088 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B1774415 : Blo 1774088 1774415 := bstep (se 1 (by rfl) ⟨1330811, by rfl⟩ : syracuseStep 1774415 = 2661623) B2661623
theorem B1774431 : Blo 1774088 1774431 := bstep (se 1 (by rfl) ⟨1330823, by rfl⟩ : syracuseStep 1774431 = 2661647) B2661647
theorem B2995049 : Blo 1774088 2995049 := bstep (se 2 (by rfl) ⟨1123143, by rfl⟩ : syracuseStep 2995049 = 2246287) B2246287
theorem B1774459 : Blo 1774088 1774459 := bstep (se 1 (by rfl) ⟨1330844, by rfl⟩ : syracuseStep 1774459 = 2661689) B2661689
theorem B1774511 : Blo 1774088 1774511 := bstep (se 1 (by rfl) ⟨1330883, by rfl⟩ : syracuseStep 1774511 = 2661767) B2661767
theorem B1774535 : Blo 1774088 1774535 := bstep (se 1 (by rfl) ⟨1330901, by rfl⟩ : syracuseStep 1774535 = 2661803) B2661803
theorem B1774555 : Blo 1774088 1774555 := bstep (se 1 (by rfl) ⟨1330916, by rfl⟩ : syracuseStep 1774555 = 2661833) B2661833
theorem B3994631 : Blo 1774088 3994631 := bstep (se 1 (by rfl) ⟨2995973, by rfl⟩ : syracuseStep 3994631 = 5991947) B5991947
theorem B1774631 : Blo 1774088 1774631 := bstep (se 1 (by rfl) ⟨1330973, by rfl⟩ : syracuseStep 1774631 = 2661947) B2661947
theorem B1774671 : Blo 1774088 1774671 := bstep (se 1 (by rfl) ⟨1331003, by rfl⟩ : syracuseStep 1774671 = 2662007) B2662007
theorem B3994703 : Blo 1774088 3994703 := bstep (se 1 (by rfl) ⟨2996027, by rfl⟩ : syracuseStep 3994703 = 5992055) B5992055
theorem B1774687 : Blo 1774088 1774687 := bstep (se 1 (by rfl) ⟨1331015, by rfl⟩ : syracuseStep 1774687 = 2662031) B2662031
theorem B1774715 : Blo 1774088 1774715 := bstep (se 1 (by rfl) ⟨1331036, by rfl⟩ : syracuseStep 1774715 = 2662073) B2662073
theorem B3200123 : Blo 1774088 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B1774767 : Blo 1774088 1774767 := bstep (se 1 (by rfl) ⟨1331075, by rfl⟩ : syracuseStep 1774767 = 2662151) B2662151
theorem B13481153 : Blo 1774088 13481153 := bstep (se 2 (by rfl) ⟨5055432, by rfl⟩ : syracuseStep 13481153 = 10110865) B10110865
theorem B1774791 : Blo 1774088 1774791 := bstep (se 1 (by rfl) ⟨1331093, by rfl⟩ : syracuseStep 1774791 = 2662187) B2662187
theorem B1774811 : Blo 1774088 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B2995447 : Blo 1774088 2995447 := bstep (se 1 (by rfl) ⟨2246585, by rfl⟩ : syracuseStep 2995447 = 4493171) B4493171
theorem B13661455 : Blo 1774088 13661455 := bstep (se 1 (by rfl) ⟨10246091, by rfl⟩ : syracuseStep 13661455 = 20492183) B20492183
theorem B1774887 : Blo 1774088 1774887 := bstep (se 1 (by rfl) ⟨1331165, by rfl⟩ : syracuseStep 1774887 = 2662331) B2662331
theorem B1774927 : Blo 1774088 1774927 := bstep (se 1 (by rfl) ⟨1331195, by rfl⟩ : syracuseStep 1774927 = 2662391) B2662391
theorem B1774943 : Blo 1774088 1774943 := bstep (se 1 (by rfl) ⟨1331207, by rfl⟩ : syracuseStep 1774943 = 2662415) B2662415
theorem B1774971 : Blo 1774088 1774971 := bstep (se 1 (by rfl) ⟨1331228, by rfl⟩ : syracuseStep 1774971 = 2662457) B2662457
theorem B9598333 : Blo 1774088 9598333 := bstep (se 3 (by rfl) ⟨1799687, by rfl⟩ : syracuseStep 9598333 = 3599375) B3599375
theorem B1775023 : Blo 1774088 1775023 := bstep (se 1 (by rfl) ⟨1331267, by rfl⟩ : syracuseStep 1775023 = 2662535) B2662535
theorem B2995643 : Blo 1774088 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1775047 : Blo 1774088 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B1775067 : Blo 1774088 1775067 := bstep (se 1 (by rfl) ⟨1331300, by rfl⟩ : syracuseStep 1775067 = 2662601) B2662601
theorem B3995099 : Blo 1774088 3995099 := bstep (se 1 (by rfl) ⟨2996324, by rfl⟩ : syracuseStep 3995099 = 5992649) B5992649
theorem B4494811 : Blo 1774088 4494811 := bstep (se 1 (by rfl) ⟨3371108, by rfl⟩ : syracuseStep 4494811 = 6742217) B6742217
theorem B7583219 : Blo 1774088 7583219 := bstep (se 1 (by rfl) ⟨5687414, by rfl⟩ : syracuseStep 7583219 = 11374829) B11374829
theorem B1775143 : Blo 1774088 1775143 := bstep (se 1 (by rfl) ⟨1331357, by rfl⟩ : syracuseStep 1775143 = 2662715) B2662715
theorem B2995751 : Blo 1774088 2995751 := bstep (se 1 (by rfl) ⟨2246813, by rfl⟩ : syracuseStep 2995751 = 4493627) B4493627
theorem B23057963 : Blo 1774088 23057963 := bstep (se 1 (by rfl) ⟨17293472, by rfl⟩ : syracuseStep 23057963 = 34586945) B34586945
theorem B1775183 : Blo 1774088 1775183 := bstep (se 1 (by rfl) ⟨1331387, by rfl⟩ : syracuseStep 1775183 = 2662775) B2662775
theorem B1775199 : Blo 1774088 1775199 := bstep (se 1 (by rfl) ⟨1331399, by rfl⟩ : syracuseStep 1775199 = 2662799) B2662799
theorem B13473377 : Blo 1774088 13473377 := bstep (se 2 (by rfl) ⟨5052516, by rfl⟩ : syracuseStep 13473377 = 10105033) B10105033
theorem B10106491 : Blo 1774088 10106491 := bstep (se 1 (by rfl) ⟨7579868, by rfl⟩ : syracuseStep 10106491 = 15159737) B15159737
theorem B1996411 : Blo 1774088 1996411 := bstep (se 1 (by rfl) ⟨1497308, by rfl⟩ : syracuseStep 1996411 = 2994617) B2994617
theorem B1775227 : Blo 1774088 1775227 := bstep (se 1 (by rfl) ⟨1331420, by rfl⟩ : syracuseStep 1775227 = 2662841) B2662841
theorem B5994107 : Blo 1774088 5994107 := bstep (se 1 (by rfl) ⟨4495580, by rfl⟩ : syracuseStep 5994107 = 8991161) B8991161
theorem B1775279 : Blo 1774088 1775279 := bstep (se 1 (by rfl) ⟨1331459, by rfl⟩ : syracuseStep 1775279 = 2662919) B2662919
theorem B1775303 : Blo 1774088 1775303 := bstep (se 1 (by rfl) ⟨1331477, by rfl⟩ : syracuseStep 1775303 = 2662955) B2662955
theorem B1775323 : Blo 1774088 1775323 := bstep (se 1 (by rfl) ⟨1331492, by rfl⟩ : syracuseStep 1775323 = 2662985) B2662985
theorem B5994269 : Blo 1774088 5994269 := bstep (se 3 (by rfl) ⟨1123925, by rfl⟩ : syracuseStep 5994269 = 2247851) B2247851
theorem B1775399 : Blo 1774088 1775399 := bstep (se 1 (by rfl) ⟨1331549, by rfl⟩ : syracuseStep 1775399 = 2663099) B2663099
theorem B5052233 : Blo 1774088 5052233 := bstep (se 2 (by rfl) ⟨1894587, by rfl⟩ : syracuseStep 5052233 = 3789175) B3789175
theorem B2996041 : Blo 1774088 2996041 := bstep (se 2 (by rfl) ⟨1123515, by rfl⟩ : syracuseStep 2996041 = 2247031) B2247031
theorem B1775439 : Blo 1774088 1775439 := bstep (se 1 (by rfl) ⟨1331579, by rfl⟩ : syracuseStep 1775439 = 2663159) B2663159
theorem B1775455 : Blo 1774088 1775455 := bstep (se 1 (by rfl) ⟨1331591, by rfl⟩ : syracuseStep 1775455 = 2663183) B2663183
theorem B2996075 : Blo 1774088 2996075 := bstep (se 1 (by rfl) ⟨2247056, by rfl⟩ : syracuseStep 2996075 = 4494113) B4494113
theorem B1775483 : Blo 1774088 1775483 := bstep (se 1 (by rfl) ⟨1331612, by rfl⟩ : syracuseStep 1775483 = 2663225) B2663225
theorem B9729953 : Blo 1774088 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B1775535 : Blo 1774088 1775535 := bstep (se 1 (by rfl) ⟨1331651, by rfl⟩ : syracuseStep 1775535 = 2663303) B2663303
theorem B3995567 : Blo 1774088 3995567 := bstep (se 1 (by rfl) ⟨2996675, by rfl⟩ : syracuseStep 3995567 = 5993351) B5993351
theorem B1775559 : Blo 1774088 1775559 := bstep (se 1 (by rfl) ⟨1331669, by rfl⟩ : syracuseStep 1775559 = 2663339) B2663339
theorem B1775579 : Blo 1774088 1775579 := bstep (se 1 (by rfl) ⟨1331684, by rfl⟩ : syracuseStep 1775579 = 2663369) B2663369
theorem B6739969 : Blo 1774088 6739969 := bstep (se 2 (by rfl) ⟨2527488, by rfl⟩ : syracuseStep 6739969 = 5054977) B5054977
theorem B12793859 : Blo 1774088 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B1775655 : Blo 1774088 1775655 := bstep (se 1 (by rfl) ⟨1331741, by rfl⟩ : syracuseStep 1775655 = 2663483) B2663483
theorem B1996879 : Blo 1774088 1996879 := bstep (se 1 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 1996879 = 2995319) B2995319
theorem B1775695 : Blo 1774088 1775695 := bstep (se 1 (by rfl) ⟨1331771, by rfl⟩ : syracuseStep 1775695 = 2663543) B2663543
theorem B4495439 : Blo 1774088 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B1775711 : Blo 1774088 1775711 := bstep (se 1 (by rfl) ⟨1331783, by rfl⟩ : syracuseStep 1775711 = 2663567) B2663567
theorem B1775739 : Blo 1774088 1775739 := bstep (se 1 (by rfl) ⟨1331804, by rfl⟩ : syracuseStep 1775739 = 2663609) B2663609
theorem B3995819 : Blo 1774088 3995819 := bstep (se 1 (by rfl) ⟨2996864, by rfl⟩ : syracuseStep 3995819 = 5993729) B5993729
theorem B1775791 : Blo 1774088 1775791 := bstep (se 1 (by rfl) ⟨1331843, by rfl⟩ : syracuseStep 1775791 = 2663687) B2663687
theorem B1775815 : Blo 1774088 1775815 := bstep (se 1 (by rfl) ⟨1331861, by rfl⟩ : syracuseStep 1775815 = 2663723) B2663723
theorem B1775835 : Blo 1774088 1775835 := bstep (se 1 (by rfl) ⟨1331876, by rfl⟩ : syracuseStep 1775835 = 2663753) B2663753
theorem B13662437 : Blo 1774088 13662437 := bstep (se 4 (by rfl) ⟨1280853, by rfl⟩ : syracuseStep 13662437 = 2561707) B2561707
theorem B2996473 : Blo 1774088 2996473 := bstep (se 2 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 2996473 = 2247355) B2247355
theorem B8984843 : Blo 1774088 8984843 := bstep (se 1 (by rfl) ⟨6738632, by rfl⟩ : syracuseStep 8984843 = 13477265) B13477265
theorem B1775911 : Blo 1774088 1775911 := bstep (se 1 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 1775911 = 2663867) B2663867
theorem B15161651 : Blo 1774088 15161651 := bstep (se 1 (by rfl) ⟨11371238, by rfl⟩ : syracuseStep 15161651 = 22742477) B22742477
theorem B1775951 : Blo 1774088 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B10795351 : Blo 1774088 10795351 := bstep (se 1 (by rfl) ⟨8096513, by rfl⟩ : syracuseStep 10795351 = 16193027) B16193027
theorem B68221277 : Blo 1774088 68221277 := bstep (se 3 (by rfl) ⟨12791489, by rfl⟩ : syracuseStep 68221277 = 25582979) B25582979
theorem B1775967 : Blo 1774088 1775967 := bstep (se 1 (by rfl) ⟨1331975, by rfl⟩ : syracuseStep 1775967 = 2663951) B2663951
theorem B1775995 : Blo 1774088 1775995 := bstep (se 1 (by rfl) ⟨1331996, by rfl⟩ : syracuseStep 1775995 = 2663993) B2663993
theorem B1776047 : Blo 1774088 1776047 := bstep (se 1 (by rfl) ⟨1332035, by rfl⟩ : syracuseStep 1776047 = 2664071) B2664071
theorem B1776071 : Blo 1774088 1776071 := bstep (se 1 (by rfl) ⟨1332053, by rfl⟩ : syracuseStep 1776071 = 2664107) B2664107
theorem B1997275 : Blo 1774088 1997275 := bstep (se 1 (by rfl) ⟨1497956, by rfl⟩ : syracuseStep 1997275 = 2995913) B2995913
theorem B2996743 : Blo 1774088 2996743 := bstep (se 1 (by rfl) ⟨2247557, by rfl⟩ : syracuseStep 2996743 = 4495115) B4495115
theorem B27695801 : Blo 1774088 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B4266695 : Blo 1774088 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B6740729 : Blo 1774088 6740729 := bstep (se 2 (by rfl) ⟨2527773, by rfl⟩ : syracuseStep 6740729 = 5055547) B5055547
theorem B2661215 : Blo 1774088 2661215 := bstep (se 1 (by rfl) ⟨1995911, by rfl⟩ : syracuseStep 2661215 = 3991823) B3991823
theorem B2661227 : Blo 1774088 2661227 := bstep (se 1 (by rfl) ⟨1995920, by rfl⟩ : syracuseStep 2661227 = 3991841) B3991841
theorem B1997743 : Blo 1774088 1997743 := bstep (se 1 (by rfl) ⟨1498307, by rfl⟩ : syracuseStep 1997743 = 2996615) B2996615
theorem B3414971 : Blo 1774088 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B13474835 : Blo 1774088 13474835 := bstep (se 1 (by rfl) ⟨10106126, by rfl⟩ : syracuseStep 13474835 = 20212253) B20212253
theorem B2661455 : Blo 1774088 2661455 := bstep (se 1 (by rfl) ⟨1996091, by rfl⟩ : syracuseStep 2661455 = 3992183) B3992183
theorem B5053519 : Blo 1774088 5053519 := bstep (se 1 (by rfl) ⟨3790139, by rfl⟩ : syracuseStep 5053519 = 7580279) B7580279
theorem B10796111 : Blo 1774088 10796111 := bstep (se 1 (by rfl) ⟨8097083, by rfl⟩ : syracuseStep 10796111 = 16194167) B16194167
theorem B3791951 : Blo 1774088 3791951 := bstep (se 1 (by rfl) ⟨2843963, by rfl⟩ : syracuseStep 3791951 = 5687927) B5687927
theorem B2661575 : Blo 1774088 2661575 := bstep (se 1 (by rfl) ⟨1996181, by rfl⟩ : syracuseStep 2661575 = 3992363) B3992363
theorem B22756625 : Blo 1774088 22756625 := bstep (se 2 (by rfl) ⟨8533734, by rfl⟩ : syracuseStep 22756625 = 17067469) B17067469
theorem B24280343 : Blo 1774088 24280343 := bstep (se 1 (by rfl) ⟨18210257, by rfl⟩ : syracuseStep 24280343 = 36420515) B36420515
theorem B15162713 : Blo 1774088 15162713 := bstep (se 2 (by rfl) ⟨5686017, by rfl⟩ : syracuseStep 15162713 = 11372035) B11372035
theorem B17530201 : Blo 1774088 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B2661737 : Blo 1774088 2661737 := bstep (se 2 (by rfl) ⟨998151, by rfl⟩ : syracuseStep 2661737 = 1996303) B1996303
theorem B2661815 : Blo 1774088 2661815 := bstep (se 1 (by rfl) ⟨1996361, by rfl⟩ : syracuseStep 2661815 = 3992723) B3992723
theorem B2661851 : Blo 1774088 2661851 := bstep (se 1 (by rfl) ⟨1996388, by rfl⟩ : syracuseStep 2661851 = 3992777) B3992777
theorem B8650385 : Blo 1774088 8650385 := bstep (se 2 (by rfl) ⟨3243894, by rfl⟩ : syracuseStep 8650385 = 6487789) B6487789
theorem B8986301 : Blo 1774088 8986301 := bstep (se 3 (by rfl) ⟨1684931, by rfl⟩ : syracuseStep 8986301 = 3369863) B3369863
theorem B8986463 : Blo 1774088 8986463 := bstep (se 1 (by rfl) ⟨6739847, by rfl⟩ : syracuseStep 8986463 = 13479695) B13479695
theorem B2662319 : Blo 1774088 2662319 := bstep (se 1 (by rfl) ⟨1996739, by rfl⟩ : syracuseStep 2662319 = 3993479) B3993479
theorem B3243959 : Blo 1774088 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B8986625 : Blo 1774088 8986625 := bstep (se 2 (by rfl) ⟨3369984, by rfl⟩ : syracuseStep 8986625 = 6739969) B6739969
theorem B51200099 : Blo 1774088 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B2662505 : Blo 1774088 2662505 := bstep (se 2 (by rfl) ⟨998439, by rfl⟩ : syracuseStep 2662505 = 1996879) B1996879
theorem B4800617 : Blo 1774088 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B2662823 : Blo 1774088 2662823 := bstep (se 1 (by rfl) ⟨1997117, by rfl⟩ : syracuseStep 2662823 = 3994235) B3994235
theorem B16187849 : Blo 1774088 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B14393801 : Blo 1774088 14393801 := bstep (se 2 (by rfl) ⟨5397675, by rfl⟩ : syracuseStep 14393801 = 10795351) B10795351
theorem B2662907 : Blo 1774088 2662907 := bstep (se 1 (by rfl) ⟨1997180, by rfl⟩ : syracuseStep 2662907 = 3994361) B3994361
theorem B13484555 : Blo 1774088 13484555 := bstep (se 1 (by rfl) ⟨10113416, by rfl⟩ : syracuseStep 13484555 = 20226833) B20226833
theorem B2663033 : Blo 1774088 2663033 := bstep (se 2 (by rfl) ⟨998637, by rfl⟩ : syracuseStep 2663033 = 1997275) B1997275
theorem B2663087 : Blo 1774088 2663087 := bstep (se 1 (by rfl) ⟨1997315, by rfl⟩ : syracuseStep 2663087 = 3994631) B3994631
theorem B2663135 : Blo 1774088 2663135 := bstep (se 1 (by rfl) ⟨1997351, by rfl⟩ : syracuseStep 2663135 = 3994703) B3994703
theorem B8987435 : Blo 1774088 8987435 := bstep (se 1 (by rfl) ⟨6740576, by rfl⟩ : syracuseStep 8987435 = 13481153) B13481153
theorem B2245583 : Blo 1774088 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B2663399 : Blo 1774088 2663399 := bstep (se 1 (by rfl) ⟨1997549, by rfl⟩ : syracuseStep 2663399 = 3995099) B3995099
theorem B5055479 : Blo 1774088 5055479 := bstep (se 1 (by rfl) ⟨3791609, by rfl⟩ : syracuseStep 5055479 = 7583219) B7583219
theorem B9725017 : Blo 1774088 9725017 := bstep (se 2 (by rfl) ⟨3646881, by rfl⟩ : syracuseStep 9725017 = 7293763) B7293763
theorem B3368155 : Blo 1774088 3368155 := bstep (se 1 (by rfl) ⟨2526116, by rfl⟩ : syracuseStep 3368155 = 5052233) B5052233
theorem B2663657 : Blo 1774088 2663657 := bstep (se 2 (by rfl) ⟨998871, by rfl⟩ : syracuseStep 2663657 = 1997743) B1997743
theorem B5989625 : Blo 1774088 5989625 := bstep (se 2 (by rfl) ⟨2246109, by rfl⟩ : syracuseStep 5989625 = 4492219) B4492219
theorem B2663711 : Blo 1774088 2663711 := bstep (se 1 (by rfl) ⟨1997783, by rfl⟩ : syracuseStep 2663711 = 3995567) B3995567
theorem B8529239 : Blo 1774088 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B28788119 : Blo 1774088 28788119 := bstep (se 1 (by rfl) ⟨21591089, by rfl⟩ : syracuseStep 28788119 = 43182179) B43182179
theorem B2663879 : Blo 1774088 2663879 := bstep (se 1 (by rfl) ⟨1997909, by rfl⟩ : syracuseStep 2663879 = 3995819) B3995819
theorem B4490711 : Blo 1774088 4490711 := bstep (se 1 (by rfl) ⟨3368033, by rfl⟩ : syracuseStep 4490711 = 6736067) B6736067
theorem B5989895 : Blo 1774088 5989895 := bstep (se 1 (by rfl) ⟨4492421, by rfl⟩ : syracuseStep 5989895 = 8984843) B8984843
theorem B28804727 : Blo 1774088 28804727 := bstep (se 1 (by rfl) ⟨21603545, by rfl⟩ : syracuseStep 28804727 = 43207091) B43207091
theorem B27313853 : Blo 1774088 27313853 := bstep (se 3 (by rfl) ⟨5121347, by rfl⟩ : syracuseStep 27313853 = 10242695) B10242695
theorem B4491065 : Blo 1774088 4491065 := bstep (se 2 (by rfl) ⟨1684149, by rfl⟩ : syracuseStep 4491065 = 3368299) B3368299
theorem B12797777 : Blo 1774088 12797777 := bstep (se 2 (by rfl) ⟨4799166, by rfl⟩ : syracuseStep 12797777 = 9598333) B9598333
theorem B2246555 : Blo 1774088 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B25594051 : Blo 1774088 25594051 := bstep (se 1 (by rfl) ⟨19195538, by rfl⟩ : syracuseStep 25594051 = 38391077) B38391077
theorem B5990867 : Blo 1774088 5990867 := bstep (se 1 (by rfl) ⟨4493150, by rfl⟩ : syracuseStep 5990867 = 8986301) B8986301
theorem B14395877 : Blo 1774088 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B5990975 : Blo 1774088 5990975 := bstep (se 1 (by rfl) ⟨4493231, by rfl⟩ : syracuseStep 5990975 = 8986463) B8986463
theorem B1895087 : Blo 1774088 1895087 := bstep (se 1 (by rfl) ⟨1421315, by rfl⟩ : syracuseStep 1895087 = 2842631) B2842631
theorem B8989379 : Blo 1774088 8989379 := bstep (se 1 (by rfl) ⟨6742034, by rfl⟩ : syracuseStep 8989379 = 13484069) B13484069
theorem B13478723 : Blo 1774088 13478723 := bstep (se 1 (by rfl) ⟨10109042, by rfl⟩ : syracuseStep 13478723 = 20218085) B20218085
theorem B3992399 : Blo 1774088 3992399 := bstep (se 1 (by rfl) ⟨2994299, by rfl⟩ : syracuseStep 3992399 = 5988599) B5988599
theorem B7580587 : Blo 1774088 7580587 := bstep (se 1 (by rfl) ⟨5685440, by rfl⟩ : syracuseStep 7580587 = 11370881) B11370881
theorem B9104399 : Blo 1774088 9104399 := bstep (se 1 (by rfl) ⟨6828299, by rfl⟩ : syracuseStep 9104399 = 13656599) B13656599
theorem B30338063 : Blo 1774088 30338063 := bstep (se 1 (by rfl) ⟨22753547, by rfl⟩ : syracuseStep 30338063 = 45507095) B45507095
theorem B3992615 : Blo 1774088 3992615 := bstep (se 1 (by rfl) ⟨2994461, by rfl⟩ : syracuseStep 3992615 = 5988923) B5988923
theorem B15158339 : Blo 1774088 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B7580861 : Blo 1774088 7580861 := bstep (se 3 (by rfl) ⟨1421411, by rfl⟩ : syracuseStep 7580861 = 2842823) B2842823
theorem B4050119 : Blo 1774088 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B3992795 : Blo 1774088 3992795 := bstep (se 1 (by rfl) ⟨2994596, by rfl⟩ : syracuseStep 3992795 = 5989193) B5989193
theorem B36433165 : Blo 1774088 36433165 := bstep (se 3 (by rfl) ⟨6831218, by rfl⟩ : syracuseStep 36433165 = 13662437) B13662437
theorem B4795771 : Blo 1774088 4795771 := bstep (se 1 (by rfl) ⟨3596828, by rfl⟩ : syracuseStep 4795771 = 7193657) B7193657
theorem B3992993 : Blo 1774088 3992993 := bstep (se 2 (by rfl) ⟨1497372, by rfl⟩ : syracuseStep 3992993 = 2994745) B2994745
theorem B4492705 : Blo 1774088 4492705 := bstep (se 2 (by rfl) ⟨1684764, by rfl⟩ : syracuseStep 4492705 = 3369529) B3369529
theorem B2133415 : Blo 1774088 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B15371975 : Blo 1774088 15371975 := bstep (se 1 (by rfl) ⟨11528981, by rfl⟩ : syracuseStep 15371975 = 23057963) B23057963
theorem B8982251 : Blo 1774088 8982251 := bstep (se 1 (by rfl) ⟨6736688, by rfl⟩ : syracuseStep 8982251 = 13473377) B13473377
theorem B3993551 : Blo 1774088 3993551 := bstep (se 1 (by rfl) ⟨2995163, by rfl⟩ : syracuseStep 3993551 = 5990327) B5990327
theorem B72888335 : Blo 1774088 72888335 := bstep (se 1 (by rfl) ⟨54666251, by rfl⟩ : syracuseStep 72888335 = 109332503) B109332503
theorem B6738025 : Blo 1774088 6738025 := bstep (se 2 (by rfl) ⟨2526759, by rfl⟩ : syracuseStep 6738025 = 5053519) B5053519
theorem B8982737 : Blo 1774088 8982737 := bstep (se 2 (by rfl) ⟨3368526, by rfl⟩ : syracuseStep 8982737 = 6737053) B6737053
theorem B3993929 : Blo 1774088 3993929 := bstep (se 2 (by rfl) ⟨1497723, by rfl⟩ : syracuseStep 3993929 = 2995447) B2995447
theorem B3993947 : Blo 1774088 3993947 := bstep (se 1 (by rfl) ⟨2995460, by rfl⟩ : syracuseStep 3993947 = 5990921) B5990921
theorem B18215273 : Blo 1774088 18215273 := bstep (se 2 (by rfl) ⟨6830727, by rfl⟩ : syracuseStep 18215273 = 13661455) B13661455
theorem B5992811 : Blo 1774088 5992811 := bstep (se 1 (by rfl) ⟨4494608, by rfl⟩ : syracuseStep 5992811 = 8989217) B8989217
theorem B3371375 : Blo 1774088 3371375 := bstep (se 1 (by rfl) ⟨2528531, by rfl⟩ : syracuseStep 3371375 = 5057063) B5057063
theorem B10105307 : Blo 1774088 10105307 := bstep (se 1 (by rfl) ⟨7578980, by rfl⟩ : syracuseStep 10105307 = 15157961) B15157961
theorem B73855469 : Blo 1774088 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B4493819 : Blo 1774088 4493819 := bstep (se 1 (by rfl) ⟨3370364, by rfl⟩ : syracuseStep 4493819 = 6740729) B6740729
theorem B1774143 : Blo 1774088 1774143 := bstep (se 1 (by rfl) ⟨1330607, by rfl⟩ : syracuseStep 1774143 = 2661215) B2661215
theorem B1774151 : Blo 1774088 1774151 := bstep (se 1 (by rfl) ⟨1330613, by rfl⟩ : syracuseStep 1774151 = 2661227) B2661227
theorem B5993081 : Blo 1774088 5993081 := bstep (se 2 (by rfl) ⟨2247405, by rfl⟩ : syracuseStep 5993081 = 4494811) B4494811
theorem B32813747 : Blo 1774088 32813747 := bstep (se 1 (by rfl) ⟨24610310, by rfl⟩ : syracuseStep 32813747 = 49220621) B49220621
theorem B8983223 : Blo 1774088 8983223 := bstep (se 1 (by rfl) ⟨6737417, by rfl⟩ : syracuseStep 8983223 = 13474835) B13474835
theorem B1774303 : Blo 1774088 1774303 := bstep (se 1 (by rfl) ⟨1330727, by rfl⟩ : syracuseStep 1774303 = 2661455) B2661455
theorem B7197407 : Blo 1774088 7197407 := bstep (se 1 (by rfl) ⟨5398055, by rfl⟩ : syracuseStep 7197407 = 10796111) B10796111
theorem B2527967 : Blo 1774088 2527967 := bstep (se 1 (by rfl) ⟨1895975, by rfl⟩ : syracuseStep 2527967 = 3791951) B3791951
theorem B21893917 : Blo 1774088 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B1774383 : Blo 1774088 1774383 := bstep (se 1 (by rfl) ⟨1330787, by rfl⟩ : syracuseStep 1774383 = 2661575) B2661575
theorem B1774491 : Blo 1774088 1774491 := bstep (se 1 (by rfl) ⟨1330868, by rfl⟩ : syracuseStep 1774491 = 2661737) B2661737
theorem B3994523 : Blo 1774088 3994523 := bstep (se 1 (by rfl) ⟨2995892, by rfl⟩ : syracuseStep 3994523 = 5991785) B5991785
theorem B1774543 : Blo 1774088 1774543 := bstep (se 1 (by rfl) ⟨1330907, by rfl⟩ : syracuseStep 1774543 = 2661815) B2661815
theorem B15168485 : Blo 1774088 15168485 := bstep (se 4 (by rfl) ⟨1422045, by rfl⟩ : syracuseStep 15168485 = 2844091) B2844091
theorem B1774567 : Blo 1774088 1774567 := bstep (se 1 (by rfl) ⟨1330925, by rfl⟩ : syracuseStep 1774567 = 2661851) B2661851
theorem B3994721 : Blo 1774088 3994721 := bstep (se 2 (by rfl) ⟨1498020, by rfl⟩ : syracuseStep 3994721 = 2996041) B2996041
theorem B8983709 : Blo 1774088 8983709 := bstep (se 3 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 8983709 = 3368891) B3368891
theorem B9106589 : Blo 1774088 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B4617415 : Blo 1774088 4617415 := bstep (se 1 (by rfl) ⟨3463061, by rfl⟩ : syracuseStep 4617415 = 6926123) B6926123
theorem B1774879 : Blo 1774088 1774879 := bstep (se 1 (by rfl) ⟨1331159, by rfl⟩ : syracuseStep 1774879 = 2662319) B2662319
theorem B3994919 : Blo 1774088 3994919 := bstep (se 1 (by rfl) ⟨2996189, by rfl⟩ : syracuseStep 3994919 = 5992379) B5992379
theorem B1996123 : Blo 1774088 1996123 := bstep (se 1 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 1996123 = 2994185) B2994185
theorem B1774939 : Blo 1774088 1774939 := bstep (se 1 (by rfl) ⟨1331204, by rfl⟩ : syracuseStep 1774939 = 2662409) B2662409
theorem B4265311 : Blo 1774088 4265311 := bstep (se 1 (by rfl) ⟨3198983, by rfl⟩ : syracuseStep 4265311 = 6397967) B6397967
theorem B1774959 : Blo 1774088 1774959 := bstep (se 1 (by rfl) ⟨1331219, by rfl⟩ : syracuseStep 1774959 = 2662439) B2662439
theorem B1775015 : Blo 1774088 1775015 := bstep (se 1 (by rfl) ⟨1331261, by rfl⟩ : syracuseStep 1775015 = 2662523) B2662523
theorem B1996231 : Blo 1774088 1996231 := bstep (se 1 (by rfl) ⟨1497173, by rfl⟩ : syracuseStep 1996231 = 2994347) B2994347
theorem B4494791 : Blo 1774088 4494791 := bstep (se 1 (by rfl) ⟨3371093, by rfl⟩ : syracuseStep 4494791 = 6742187) B6742187
theorem B1775099 : Blo 1774088 1775099 := bstep (se 1 (by rfl) ⟨1331324, by rfl⟩ : syracuseStep 1775099 = 2662649) B2662649
theorem B1775167 : Blo 1774088 1775167 := bstep (se 1 (by rfl) ⟨1331375, by rfl⟩ : syracuseStep 1775167 = 2662751) B2662751
theorem B1775175 : Blo 1774088 1775175 := bstep (se 1 (by rfl) ⟨1331381, by rfl⟩ : syracuseStep 1775175 = 2662763) B2662763
theorem B5052061 : Blo 1774088 5052061 := bstep (se 3 (by rfl) ⟨947261, by rfl⟩ : syracuseStep 5052061 = 1894523) B1894523
theorem B3995297 : Blo 1774088 3995297 := bstep (se 2 (by rfl) ⟨1498236, by rfl⟩ : syracuseStep 3995297 = 2996473) B2996473
theorem B13670075 : Blo 1774088 13670075 := bstep (se 1 (by rfl) ⟨10252556, by rfl⟩ : syracuseStep 13670075 = 20505113) B20505113
theorem B1775327 : Blo 1774088 1775327 := bstep (se 1 (by rfl) ⟨1331495, by rfl⟩ : syracuseStep 1775327 = 2662991) B2662991
theorem B1996591 : Blo 1774088 1996591 := bstep (se 1 (by rfl) ⟨1497443, by rfl⟩ : syracuseStep 1996591 = 2994887) B2994887
theorem B1775407 : Blo 1774088 1775407 := bstep (se 1 (by rfl) ⟨1331555, by rfl⟩ : syracuseStep 1775407 = 2663111) B2663111
theorem B1996699 : Blo 1774088 1996699 := bstep (se 1 (by rfl) ⟨1497524, by rfl⟩ : syracuseStep 1996699 = 2995049) B2995049
theorem B1775515 : Blo 1774088 1775515 := bstep (se 1 (by rfl) ⟨1331636, by rfl⟩ : syracuseStep 1775515 = 2663273) B2663273
theorem B1775567 : Blo 1774088 1775567 := bstep (se 1 (by rfl) ⟨1331675, by rfl⟩ : syracuseStep 1775567 = 2663351) B2663351
theorem B11368421 : Blo 1774088 11368421 := bstep (se 4 (by rfl) ⟨1065789, by rfl⟩ : syracuseStep 11368421 = 2131579) B2131579
theorem B1775591 : Blo 1774088 1775591 := bstep (se 1 (by rfl) ⟨1331693, by rfl⟩ : syracuseStep 1775591 = 2663387) B2663387
theorem B3995657 : Blo 1774088 3995657 := bstep (se 2 (by rfl) ⟨1498371, by rfl⟩ : syracuseStep 3995657 = 2996743) B2996743
theorem B15161377 : Blo 1774088 15161377 := bstep (se 2 (by rfl) ⟨5685516, by rfl⟩ : syracuseStep 15161377 = 11371033) B11371033
theorem B4495571 : Blo 1774088 4495571 := bstep (se 1 (by rfl) ⟨3371678, by rfl⟩ : syracuseStep 4495571 = 6743357) B6743357
theorem B1775903 : Blo 1774088 1775903 := bstep (se 1 (by rfl) ⟨1331927, by rfl⟩ : syracuseStep 1775903 = 2663855) B2663855
theorem B1997095 : Blo 1774088 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B1775963 : Blo 1774088 1775963 := bstep (se 1 (by rfl) ⟨1331972, by rfl⟩ : syracuseStep 1775963 = 2663945) B2663945
theorem B1997167 : Blo 1774088 1997167 := bstep (se 1 (by rfl) ⟨1497875, by rfl⟩ : syracuseStep 1997167 = 2995751) B2995751
theorem B1775983 : Blo 1774088 1775983 := bstep (se 1 (by rfl) ⟨1331987, by rfl⟩ : syracuseStep 1775983 = 2663975) B2663975
theorem B4266407 : Blo 1774088 4266407 := bstep (se 1 (by rfl) ⟨3199805, by rfl⟩ : syracuseStep 4266407 = 6399611) B6399611
theorem B3996071 : Blo 1774088 3996071 := bstep (se 1 (by rfl) ⟨2997053, by rfl⟩ : syracuseStep 3996071 = 5994107) B5994107
theorem B1776039 : Blo 1774088 1776039 := bstep (se 1 (by rfl) ⟨1332029, by rfl⟩ : syracuseStep 1776039 = 2664059) B2664059
theorem B8985005 : Blo 1774088 8985005 := bstep (se 3 (by rfl) ⟨1684688, by rfl⟩ : syracuseStep 8985005 = 3369377) B3369377
theorem B3996179 : Blo 1774088 3996179 := bstep (se 1 (by rfl) ⟨2997134, by rfl⟩ : syracuseStep 3996179 = 5994269) B5994269
theorem B1997383 : Blo 1774088 1997383 := bstep (se 1 (by rfl) ⟨1498037, by rfl⟩ : syracuseStep 1997383 = 2996075) B2996075
theorem B8985167 : Blo 1774088 8985167 := bstep (se 1 (by rfl) ⟨6738875, by rfl⟩ : syracuseStep 8985167 = 13477751) B13477751
theorem B6486635 : Blo 1774088 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B2996959 : Blo 1774088 2996959 := bstep (se 1 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 2996959 = 4495439) B4495439
theorem B10107767 : Blo 1774088 10107767 := bstep (se 1 (by rfl) ⟨7580825, by rfl⟩ : syracuseStep 10107767 = 15161651) B15161651
theorem B7584637 : Blo 1774088 7584637 := bstep (se 3 (by rfl) ⟨1422119, by rfl⟩ : syracuseStep 7584637 = 2844239) B2844239
theorem B45480851 : Blo 1774088 45480851 := bstep (se 1 (by rfl) ⟨34110638, by rfl⟩ : syracuseStep 45480851 = 68221277) B68221277
theorem B2661275 : Blo 1774088 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B8526779 : Blo 1774088 8526779 := bstep (se 1 (by rfl) ⟨6395084, by rfl⟩ : syracuseStep 8526779 = 12790169) B12790169
theorem B93494405 : Blo 1774088 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B11377853 : Blo 1774088 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B3792071 : Blo 1774088 3792071 := bstep (se 1 (by rfl) ⟨2844053, by rfl⟩ : syracuseStep 3792071 = 5688107) B5688107
theorem B30342437 : Blo 1774088 30342437 := bstep (se 4 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 30342437 = 5689207) B5689207
theorem B2661671 : Blo 1774088 2661671 := bstep (se 1 (by rfl) ⟨1996253, by rfl⟩ : syracuseStep 2661671 = 3992507) B3992507
theorem B5987681 : Blo 1774088 5987681 := bstep (se 2 (by rfl) ⟨2245380, by rfl⟩ : syracuseStep 5987681 = 4490761) B4490761
theorem B2661755 : Blo 1774088 2661755 := bstep (se 1 (by rfl) ⟨1996316, by rfl⟩ : syracuseStep 2661755 = 3992633) B3992633
theorem B3792251 : Blo 1774088 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B13475321 : Blo 1774088 13475321 := bstep (se 2 (by rfl) ⟨5053245, by rfl⟩ : syracuseStep 13475321 = 10106491) B10106491
theorem B2661881 : Blo 1774088 2661881 := bstep (se 2 (by rfl) ⟨998205, by rfl⟩ : syracuseStep 2661881 = 1996411) B1996411
theorem B15171083 : Blo 1774088 15171083 := bstep (se 1 (by rfl) ⟨11378312, by rfl⟩ : syracuseStep 15171083 = 22756625) B22756625
theorem B16186895 : Blo 1774088 16186895 := bstep (se 1 (by rfl) ⟨12140171, by rfl⟩ : syracuseStep 16186895 = 24280343) B24280343
theorem B10108475 : Blo 1774088 10108475 := bstep (se 1 (by rfl) ⟨7581356, by rfl⟩ : syracuseStep 10108475 = 15162713) B15162713
theorem B2661983 : Blo 1774088 2661983 := bstep (se 1 (by rfl) ⟨1996487, by rfl⟩ : syracuseStep 2661983 = 3992975) B3992975
theorem B5766923 : Blo 1774088 5766923 := bstep (se 1 (by rfl) ⟨4325192, by rfl⟩ : syracuseStep 5766923 = 8650385) B8650385
theorem B2662199 : Blo 1774088 2662199 := bstep (se 1 (by rfl) ⟨1996649, by rfl⟩ : syracuseStep 2662199 = 3993299) B3993299
theorem B2162639 : Blo 1774088 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B5988491 : Blo 1774088 5988491 := bstep (se 1 (by rfl) ⟨4491368, by rfl⟩ : syracuseStep 5988491 = 8982737) B8982737
theorem B2662619 : Blo 1774088 2662619 := bstep (se 1 (by rfl) ⟨1996964, by rfl⟩ : syracuseStep 2662619 = 3993929) B3993929
theorem B2662631 : Blo 1774088 2662631 := bstep (se 1 (by rfl) ⟨1996973, by rfl⟩ : syracuseStep 2662631 = 3993947) B3993947
theorem B2662793 : Blo 1774088 2662793 := bstep (se 2 (by rfl) ⟨998547, by rfl⟩ : syracuseStep 2662793 = 1997095) B1997095
theorem B5988815 : Blo 1774088 5988815 := bstep (se 1 (by rfl) ⟨4491611, by rfl⟩ : syracuseStep 5988815 = 8983223) B8983223
theorem B2662889 : Blo 1774088 2662889 := bstep (se 2 (by rfl) ⟨998583, by rfl⟩ : syracuseStep 2662889 = 1997167) B1997167
theorem B2663015 : Blo 1774088 2663015 := bstep (se 1 (by rfl) ⟨1997261, by rfl⟩ : syracuseStep 2663015 = 3994523) B3994523
theorem B2663147 : Blo 1774088 2663147 := bstep (se 1 (by rfl) ⟨1997360, by rfl⟩ : syracuseStep 2663147 = 3994721) B3994721
theorem B2663177 : Blo 1774088 2663177 := bstep (se 2 (by rfl) ⟨998691, by rfl⟩ : syracuseStep 2663177 = 1997383) B1997383
theorem B5989139 : Blo 1774088 5989139 := bstep (se 1 (by rfl) ⟨4491854, by rfl⟩ : syracuseStep 5989139 = 8983709) B8983709
theorem B6071059 : Blo 1774088 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B2663279 : Blo 1774088 2663279 := bstep (se 1 (by rfl) ⟨1997459, by rfl⟩ : syracuseStep 2663279 = 3994919) B3994919
theorem B5686159 : Blo 1774088 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B24626213 : Blo 1774088 24626213 := bstep (se 4 (by rfl) ⟨2308707, by rfl⟩ : syracuseStep 24626213 = 4617415) B4617415
theorem B19203151 : Blo 1774088 19203151 := bstep (se 1 (by rfl) ⟨14402363, by rfl⟩ : syracuseStep 19203151 = 28804727) B28804727
theorem B2663531 : Blo 1774088 2663531 := bstep (se 1 (by rfl) ⟨1997648, by rfl⟩ : syracuseStep 2663531 = 3995297) B3995297
theorem B7578947 : Blo 1774088 7578947 := bstep (se 1 (by rfl) ⟨5684210, by rfl⟩ : syracuseStep 7578947 = 11368421) B11368421
theorem B2663771 : Blo 1774088 2663771 := bstep (se 1 (by rfl) ⟨1997828, by rfl⟩ : syracuseStep 2663771 = 3995657) B3995657
theorem B2844271 : Blo 1774088 2844271 := bstep (se 1 (by rfl) ⟨2133203, by rfl⟩ : syracuseStep 2844271 = 4266407) B4266407
theorem B2664047 : Blo 1774088 2664047 := bstep (se 1 (by rfl) ⟨1998035, by rfl⟩ : syracuseStep 2664047 = 3996071) B3996071
theorem B5990003 : Blo 1774088 5990003 := bstep (se 1 (by rfl) ⟨4492502, by rfl⟩ : syracuseStep 5990003 = 8985005) B8985005
theorem B4490873 : Blo 1774088 4490873 := bstep (se 2 (by rfl) ⟨1684077, by rfl⟩ : syracuseStep 4490873 = 3368155) B3368155
theorem B2664119 : Blo 1774088 2664119 := bstep (se 1 (by rfl) ⟨1998089, by rfl⟩ : syracuseStep 2664119 = 3996179) B3996179
theorem B5990111 : Blo 1774088 5990111 := bstep (se 1 (by rfl) ⟨4492583, by rfl⟩ : syracuseStep 5990111 = 8985167) B8985167
theorem B5687081 : Blo 1774088 5687081 := bstep (se 2 (by rfl) ⟨2132655, by rfl⟩ : syracuseStep 5687081 = 4265311) B4265311
theorem B5990273 : Blo 1774088 5990273 := bstep (se 2 (by rfl) ⟨2246352, by rfl⟩ : syracuseStep 5990273 = 4492705) B4492705
theorem B2844553 : Blo 1774088 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B30320567 : Blo 1774088 30320567 := bstep (se 1 (by rfl) ⟨22740425, by rfl⟩ : syracuseStep 30320567 = 45480851) B45480851
theorem B15378461 : Blo 1774088 15378461 := bstep (se 3 (by rfl) ⟨2883461, by rfl⟩ : syracuseStep 15378461 = 5766923) B5766923
theorem B20228291 : Blo 1774088 20228291 := bstep (se 1 (by rfl) ⟨15171218, by rfl⟩ : syracuseStep 20228291 = 30342437) B30342437
theorem B6736081 : Blo 1774088 6736081 := bstep (se 2 (by rfl) ⟨2526030, by rfl⟩ : syracuseStep 6736081 = 5052061) B5052061
theorem B3991787 : Blo 1774088 3991787 := bstep (se 1 (by rfl) ⟨2993840, by rfl⟩ : syracuseStep 3991787 = 5987681) B5987681
theorem B10791263 : Blo 1774088 10791263 := bstep (se 1 (by rfl) ⟨8093447, by rfl⟩ : syracuseStep 10791263 = 16186895) B16186895
theorem B5990813 : Blo 1774088 5990813 := bstep (se 3 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 5990813 = 2246555) B2246555
theorem B5991083 : Blo 1774088 5991083 := bstep (se 1 (by rfl) ⟨4493312, by rfl⟩ : syracuseStep 5991083 = 8986625) B8986625
theorem B12143515 : Blo 1774088 12143515 := bstep (se 1 (by rfl) ⟨9107636, by rfl⟩ : syracuseStep 12143515 = 18215273) B18215273
theorem B2247583 : Blo 1774088 2247583 := bstep (se 1 (by rfl) ⟨1685687, by rfl⟩ : syracuseStep 2247583 = 3371375) B3371375
theorem B10791899 : Blo 1774088 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B6736871 : Blo 1774088 6736871 := bstep (se 1 (by rfl) ⟨5052653, by rfl⟩ : syracuseStep 6736871 = 10105307) B10105307
theorem B49236979 : Blo 1774088 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B8989703 : Blo 1774088 8989703 := bstep (se 1 (by rfl) ⟨6742277, by rfl⟩ : syracuseStep 8989703 = 13484555) B13484555
theorem B21875831 : Blo 1774088 21875831 := bstep (se 1 (by rfl) ⟨16406873, by rfl⟩ : syracuseStep 21875831 = 32813747) B32813747
theorem B10800317 : Blo 1774088 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B5991623 : Blo 1774088 5991623 := bstep (se 1 (by rfl) ⟨4493717, by rfl⟩ : syracuseStep 5991623 = 8987435) B8987435
theorem B10112323 : Blo 1774088 10112323 := bstep (se 1 (by rfl) ⟨7584242, by rfl⟩ : syracuseStep 10112323 = 15168485) B15168485
theorem B3370319 : Blo 1774088 3370319 := bstep (se 1 (by rfl) ⟨2527739, by rfl⟩ : syracuseStep 3370319 = 5055479) B5055479
theorem B3993083 : Blo 1774088 3993083 := bstep (se 1 (by rfl) ⟨2994812, by rfl⟩ : syracuseStep 3993083 = 5989625) B5989625
theorem B2993807 : Blo 1774088 2993807 := bstep (se 1 (by rfl) ⟨2245355, by rfl⟩ : syracuseStep 2993807 = 4490711) B4490711
theorem B3993263 : Blo 1774088 3993263 := bstep (se 1 (by rfl) ⟨2994947, by rfl⟩ : syracuseStep 3993263 = 5989895) B5989895
theorem B29191889 : Blo 1774088 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B9113383 : Blo 1774088 9113383 := bstep (se 1 (by rfl) ⟨6835037, by rfl⟩ : syracuseStep 9113383 = 13670075) B13670075
theorem B10112849 : Blo 1774088 10112849 := bstep (se 2 (by rfl) ⟨3792318, by rfl⟩ : syracuseStep 10112849 = 7584637) B7584637
theorem B38383469 : Blo 1774088 38383469 := bstep (se 3 (by rfl) ⟨7196900, by rfl⟩ : syracuseStep 38383469 = 14393801) B14393801
theorem B2994043 : Blo 1774088 2994043 := bstep (se 1 (by rfl) ⟨2245532, by rfl⟩ : syracuseStep 2994043 = 4491065) B4491065
theorem B3993911 : Blo 1774088 3993911 := bstep (se 1 (by rfl) ⟨2995433, by rfl⟩ : syracuseStep 3993911 = 5990867) B5990867
theorem B9597251 : Blo 1774088 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B3993983 : Blo 1774088 3993983 := bstep (se 1 (by rfl) ⟨2995487, by rfl⟩ : syracuseStep 3993983 = 5990975) B5990975
theorem B5992919 : Blo 1774088 5992919 := bstep (se 1 (by rfl) ⟨4494689, by rfl⟩ : syracuseStep 5992919 = 8989379) B8989379
theorem B6394361 : Blo 1774088 6394361 := bstep (se 2 (by rfl) ⟨2397885, by rfl⟩ : syracuseStep 6394361 = 4795771) B4795771
theorem B6738511 : Blo 1774088 6738511 := bstep (se 1 (by rfl) ⟨5053883, by rfl⟩ : syracuseStep 6738511 = 10107767) B10107767
theorem B1774183 : Blo 1774088 1774183 := bstep (se 1 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 1774183 = 2661275) B2661275
theorem B10105559 : Blo 1774088 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B62329603 : Blo 1774088 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B2528047 : Blo 1774088 2528047 := bstep (se 1 (by rfl) ⟨1896035, by rfl⟩ : syracuseStep 2528047 = 3792071) B3792071
theorem B1774447 : Blo 1774088 1774447 := bstep (se 1 (by rfl) ⟨1330835, by rfl⟩ : syracuseStep 1774447 = 2661671) B2661671
theorem B1774503 : Blo 1774088 1774503 := bstep (se 1 (by rfl) ⟨1330877, by rfl⟩ : syracuseStep 1774503 = 2661755) B2661755
theorem B2528167 : Blo 1774088 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B8983547 : Blo 1774088 8983547 := bstep (se 1 (by rfl) ⟨6737660, by rfl⟩ : syracuseStep 8983547 = 13475321) B13475321
theorem B1774587 : Blo 1774088 1774587 := bstep (se 1 (by rfl) ⟨1330940, by rfl⟩ : syracuseStep 1774587 = 2661881) B2661881
theorem B10114055 : Blo 1774088 10114055 := bstep (se 1 (by rfl) ⟨7585541, by rfl⟩ : syracuseStep 10114055 = 15171083) B15171083
theorem B6738983 : Blo 1774088 6738983 := bstep (se 1 (by rfl) ⟨5054237, by rfl⟩ : syracuseStep 6738983 = 10108475) B10108475
theorem B1774655 : Blo 1774088 1774655 := bstep (se 1 (by rfl) ⟨1330991, by rfl⟩ : syracuseStep 1774655 = 2661983) B2661983
theorem B1774799 : Blo 1774088 1774799 := bstep (se 1 (by rfl) ⟨1331099, by rfl⟩ : syracuseStep 1774799 = 2662199) B2662199
theorem B48592223 : Blo 1774088 48592223 := bstep (se 1 (by rfl) ⟨36444167, by rfl⟩ : syracuseStep 48592223 = 72888335) B72888335
theorem B20215169 : Blo 1774088 20215169 := bstep (se 2 (by rfl) ⟨7580688, by rfl⟩ : syracuseStep 20215169 = 15161377) B15161377
theorem B34133399 : Blo 1774088 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B1775003 : Blo 1774088 1775003 := bstep (se 1 (by rfl) ⟨1331252, by rfl⟩ : syracuseStep 1775003 = 2662505) B2662505
theorem B3200411 : Blo 1774088 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B8984033 : Blo 1774088 8984033 := bstep (se 2 (by rfl) ⟨3369012, by rfl⟩ : syracuseStep 8984033 = 6738025) B6738025
theorem B3995207 : Blo 1774088 3995207 := bstep (se 1 (by rfl) ⟨2996405, by rfl⟩ : syracuseStep 3995207 = 5992811) B5992811
theorem B34125401 : Blo 1774088 34125401 := bstep (se 2 (by rfl) ⟨12797025, by rfl⟩ : syracuseStep 34125401 = 25594051) B25594051
theorem B1775215 : Blo 1774088 1775215 := bstep (se 1 (by rfl) ⟨1331411, by rfl⟩ : syracuseStep 1775215 = 2662823) B2662823
theorem B1775271 : Blo 1774088 1775271 := bstep (se 1 (by rfl) ⟨1331453, by rfl⟩ : syracuseStep 1775271 = 2662907) B2662907
theorem B2995879 : Blo 1774088 2995879 := bstep (se 1 (by rfl) ⟨2246909, by rfl⟩ : syracuseStep 2995879 = 4493819) B4493819
theorem B1775355 : Blo 1774088 1775355 := bstep (se 1 (by rfl) ⟨1331516, by rfl⟩ : syracuseStep 1775355 = 2663033) B2663033
theorem B3995387 : Blo 1774088 3995387 := bstep (se 1 (by rfl) ⟨2996540, by rfl⟩ : syracuseStep 3995387 = 5993081) B5993081
theorem B1775391 : Blo 1774088 1775391 := bstep (se 1 (by rfl) ⟨1331543, by rfl⟩ : syracuseStep 1775391 = 2663087) B2663087
theorem B4798271 : Blo 1774088 4798271 := bstep (se 1 (by rfl) ⟨3598703, by rfl⟩ : syracuseStep 4798271 = 7197407) B7197407
theorem B1775423 : Blo 1774088 1775423 := bstep (se 1 (by rfl) ⟨1331567, by rfl⟩ : syracuseStep 1775423 = 2663135) B2663135
theorem B1775599 : Blo 1774088 1775599 := bstep (se 1 (by rfl) ⟨1331699, by rfl⟩ : syracuseStep 1775599 = 2663399) B2663399
theorem B1775771 : Blo 1774088 1775771 := bstep (se 1 (by rfl) ⟨1331828, by rfl⟩ : syracuseStep 1775771 = 2663657) B2663657
theorem B1775807 : Blo 1774088 1775807 := bstep (se 1 (by rfl) ⟨1331855, by rfl⟩ : syracuseStep 1775807 = 2663711) B2663711
theorem B19192079 : Blo 1774088 19192079 := bstep (se 1 (by rfl) ⟨14394059, by rfl⟩ : syracuseStep 19192079 = 28788119) B28788119
theorem B3995945 : Blo 1774088 3995945 := bstep (se 2 (by rfl) ⟨1498479, by rfl⟩ : syracuseStep 3995945 = 2996959) B2996959
theorem B2996527 : Blo 1774088 2996527 := bstep (se 1 (by rfl) ⟨2247395, by rfl⟩ : syracuseStep 2996527 = 4494791) B4494791
theorem B1775919 : Blo 1774088 1775919 := bstep (se 1 (by rfl) ⟨1331939, by rfl⟩ : syracuseStep 1775919 = 2663879) B2663879
theorem B10107449 : Blo 1774088 10107449 := bstep (se 2 (by rfl) ⟨3790293, by rfl⟩ : syracuseStep 10107449 = 7580587) B7580587
theorem B12966689 : Blo 1774088 12966689 := bstep (se 2 (by rfl) ⟨4862508, by rfl⟩ : syracuseStep 12966689 = 9725017) B9725017
theorem B2997047 : Blo 1774088 2997047 := bstep (se 1 (by rfl) ⟨2247785, by rfl⟩ : syracuseStep 2997047 = 4495571) B4495571
theorem B48577553 : Blo 1774088 48577553 := bstep (se 2 (by rfl) ⟨18216582, by rfl⟩ : syracuseStep 48577553 = 36433165) B36433165
theorem B4324423 : Blo 1774088 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B2661497 : Blo 1774088 2661497 := bstep (se 2 (by rfl) ⟨998061, by rfl⟩ : syracuseStep 2661497 = 1996123) B1996123
theorem B5053565 : Blo 1774088 5053565 := bstep (se 3 (by rfl) ⟨947543, by rfl⟩ : syracuseStep 5053565 = 1895087) B1895087
theorem B40991933 : Blo 1774088 40991933 := bstep (se 3 (by rfl) ⟨7685987, by rfl⟩ : syracuseStep 40991933 = 15371975) B15371975
theorem B8985815 : Blo 1774088 8985815 := bstep (se 1 (by rfl) ⟨6739361, by rfl⟩ : syracuseStep 8985815 = 13478723) B13478723
theorem B2661599 : Blo 1774088 2661599 := bstep (se 1 (by rfl) ⟨1996199, by rfl⟩ : syracuseStep 2661599 = 3992399) B3992399
theorem B6741245 : Blo 1774088 6741245 := bstep (se 3 (by rfl) ⟨1263983, by rfl⟩ : syracuseStep 6741245 = 2527967) B2527967
theorem B2661641 : Blo 1774088 2661641 := bstep (se 2 (by rfl) ⟨998115, by rfl⟩ : syracuseStep 2661641 = 1996231) B1996231
theorem B5684519 : Blo 1774088 5684519 := bstep (se 1 (by rfl) ⟨4263389, by rfl⟩ : syracuseStep 5684519 = 8526779) B8526779
theorem B291347765 : Blo 1774088 291347765 := bstep (se 5 (by rfl) ⟨13656926, by rfl⟩ : syracuseStep 291347765 = 27313853) B27313853
theorem B6069599 : Blo 1774088 6069599 := bstep (se 1 (by rfl) ⟨4552199, by rfl⟩ : syracuseStep 6069599 = 9104399) B9104399
theorem B20225375 : Blo 1774088 20225375 := bstep (se 1 (by rfl) ⟨15169031, by rfl⟩ : syracuseStep 20225375 = 30338063) B30338063
theorem B2661743 : Blo 1774088 2661743 := bstep (se 1 (by rfl) ⟨1996307, by rfl⟩ : syracuseStep 2661743 = 3992615) B3992615
theorem B5053907 : Blo 1774088 5053907 := bstep (se 1 (by rfl) ⟨3790430, by rfl⟩ : syracuseStep 5053907 = 7580861) B7580861
theorem B7585235 : Blo 1774088 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B2661863 : Blo 1774088 2661863 := bstep (se 1 (by rfl) ⟨1996397, by rfl⟩ : syracuseStep 2661863 = 3992795) B3992795
theorem B34127405 : Blo 1774088 34127405 := bstep (se 3 (by rfl) ⟨6398888, by rfl⟩ : syracuseStep 34127405 = 12797777) B12797777
theorem B2661995 : Blo 1774088 2661995 := bstep (se 1 (by rfl) ⟨1996496, by rfl⟩ : syracuseStep 2661995 = 3992993) B3992993
theorem B2662121 : Blo 1774088 2662121 := bstep (se 2 (by rfl) ⟨998295, by rfl⟩ : syracuseStep 2662121 = 1996591) B1996591
theorem B5988167 : Blo 1774088 5988167 := bstep (se 1 (by rfl) ⟨4491125, by rfl⟩ : syracuseStep 5988167 = 8982251) B8982251
theorem B2662265 : Blo 1774088 2662265 := bstep (se 2 (by rfl) ⟨998349, by rfl⟩ : syracuseStep 2662265 = 1996699) B1996699
theorem B5988221 : Blo 1774088 5988221 := bstep (se 3 (by rfl) ⟨1122791, by rfl⟩ : syracuseStep 5988221 = 2245583) B2245583
theorem B5767037 : Blo 1774088 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B2662367 : Blo 1774088 2662367 := bstep (se 1 (by rfl) ⟨1996775, by rfl⟩ : syracuseStep 2662367 = 3993551) B3993551
theorem B2662607 : Blo 1774088 2662607 := bstep (se 1 (by rfl) ⟨1996955, by rfl⟩ : syracuseStep 2662607 = 3993911) B3993911
theorem B2662655 : Blo 1774088 2662655 := bstep (se 1 (by rfl) ⟨1996991, by rfl⟩ : syracuseStep 2662655 = 3993983) B3993983
theorem B5989031 : Blo 1774088 5989031 := bstep (se 1 (by rfl) ⟨4491773, by rfl⟩ : syracuseStep 5989031 = 8983547) B8983547
theorem B6742703 : Blo 1774088 6742703 := bstep (se 1 (by rfl) ⟨5057027, by rfl⟩ : syracuseStep 6742703 = 10114055) B10114055
theorem B16417475 : Blo 1774088 16417475 := bstep (se 1 (by rfl) ⟨12313106, by rfl⟩ : syracuseStep 16417475 = 24626213) B24626213
theorem B25592669 : Blo 1774088 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B13476779 : Blo 1774088 13476779 := bstep (se 1 (by rfl) ⟨10107584, by rfl⟩ : syracuseStep 13476779 = 20215169) B20215169
theorem B5989355 : Blo 1774088 5989355 := bstep (se 1 (by rfl) ⟨4492016, by rfl⟩ : syracuseStep 5989355 = 8984033) B8984033
theorem B8094745 : Blo 1774088 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B2663471 : Blo 1774088 2663471 := bstep (se 1 (by rfl) ⟨1997603, by rfl⟩ : syracuseStep 2663471 = 3995207) B3995207
theorem B22750267 : Blo 1774088 22750267 := bstep (se 1 (by rfl) ⟨17062700, by rfl⟩ : syracuseStep 22750267 = 34125401) B34125401
theorem B2663591 : Blo 1774088 2663591 := bstep (se 1 (by rfl) ⟨1997693, by rfl⟩ : syracuseStep 2663591 = 3995387) B3995387
theorem B13485527 : Blo 1774088 13485527 := bstep (se 1 (by rfl) ⟨10114145, by rfl⟩ : syracuseStep 13485527 = 20228291) B20228291
theorem B2663963 : Blo 1774088 2663963 := bstep (se 1 (by rfl) ⟨1997972, by rfl⟩ : syracuseStep 2663963 = 3995945) B3995945
theorem B7194599 : Blo 1774088 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B4491247 : Blo 1774088 4491247 := bstep (se 1 (by rfl) ⟨3368435, by rfl⟩ : syracuseStep 4491247 = 6736871) B6736871
theorem B32385035 : Blo 1774088 32385035 := bstep (se 1 (by rfl) ⟨24288776, by rfl⟩ : syracuseStep 32385035 = 48577553) B48577553
theorem B14583887 : Blo 1774088 14583887 := bstep (se 1 (by rfl) ⟨10937915, by rfl⟩ : syracuseStep 14583887 = 21875831) B21875831
theorem B3369043 : Blo 1774088 3369043 := bstep (se 1 (by rfl) ⟨2526782, by rfl⟩ : syracuseStep 3369043 = 5053565) B5053565
theorem B5990543 : Blo 1774088 5990543 := bstep (se 1 (by rfl) ⟨4492907, by rfl⟩ : syracuseStep 5990543 = 8985815) B8985815
theorem B2246879 : Blo 1774088 2246879 := bstep (se 1 (by rfl) ⟨1685159, by rfl⟩ : syracuseStep 2246879 = 3370319) B3370319
theorem B3369271 : Blo 1774088 3369271 := bstep (se 1 (by rfl) ⟨2526953, by rfl⟩ : syracuseStep 3369271 = 5053907) B5053907
theorem B5056823 : Blo 1774088 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B22751603 : Blo 1774088 22751603 := bstep (se 1 (by rfl) ⟨17063702, by rfl⟩ : syracuseStep 22751603 = 34127405) B34127405
theorem B12151177 : Blo 1774088 12151177 := bstep (se 2 (by rfl) ⟨4556691, by rfl⟩ : syracuseStep 12151177 = 9113383) B9113383
theorem B3992057 : Blo 1774088 3992057 := bstep (se 2 (by rfl) ⟨1497021, by rfl⟩ : syracuseStep 3992057 = 2994043) B2994043
theorem B3992111 : Blo 1774088 3992111 := bstep (se 1 (by rfl) ⟨2994083, by rfl⟩ : syracuseStep 3992111 = 5988167) B5988167
theorem B3992147 : Blo 1774088 3992147 := bstep (se 1 (by rfl) ⟨2994110, by rfl⟩ : syracuseStep 3992147 = 5988221) B5988221
theorem B3844691 : Blo 1774088 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B3992327 : Blo 1774088 3992327 := bstep (se 1 (by rfl) ⟨2994245, by rfl⟩ : syracuseStep 3992327 = 5988491) B5988491
theorem B8981441 : Blo 1774088 8981441 := bstep (se 2 (by rfl) ⟨3368040, by rfl⟩ : syracuseStep 8981441 = 6736081) B6736081
theorem B3992543 : Blo 1774088 3992543 := bstep (se 1 (by rfl) ⟨2994407, by rfl⟩ : syracuseStep 3992543 = 5988815) B5988815
theorem B6737039 : Blo 1774088 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B3992759 : Blo 1774088 3992759 := bstep (se 1 (by rfl) ⟨2994569, by rfl⟩ : syracuseStep 3992759 = 5989139) B5989139
theorem B4492655 : Blo 1774088 4492655 := bstep (se 1 (by rfl) ⟨3369491, by rfl⟩ : syracuseStep 4492655 = 6738983) B6738983
theorem B51178877 : Blo 1774088 51178877 := bstep (se 3 (by rfl) ⟨9596039, by rfl⟩ : syracuseStep 51178877 = 19192079) B19192079
theorem B32394815 : Blo 1774088 32394815 := bstep (se 1 (by rfl) ⟨24296111, by rfl⟩ : syracuseStep 32394815 = 48592223) B48592223
theorem B2133607 : Blo 1774088 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B3370729 : Blo 1774088 3370729 := bstep (se 2 (by rfl) ⟨1264023, by rfl⟩ : syracuseStep 3370729 = 2528047) B2528047
theorem B3993335 : Blo 1774088 3993335 := bstep (se 1 (by rfl) ⟨2995001, by rfl⟩ : syracuseStep 3993335 = 5990003) B5990003
theorem B2993915 : Blo 1774088 2993915 := bstep (se 1 (by rfl) ⟨2245436, by rfl⟩ : syracuseStep 2993915 = 4490873) B4490873
theorem B3993407 : Blo 1774088 3993407 := bstep (se 1 (by rfl) ⟨2995055, by rfl⟩ : syracuseStep 3993407 = 5990111) B5990111
theorem B7581545 : Blo 1774088 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B16191353 : Blo 1774088 16191353 := bstep (se 2 (by rfl) ⟨6071757, by rfl⟩ : syracuseStep 16191353 = 12143515) B12143515
theorem B3198847 : Blo 1774088 3198847 := bstep (se 1 (by rfl) ⟨2399135, by rfl⟩ : syracuseStep 3198847 = 4798271) B4798271
theorem B3370889 : Blo 1774088 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B3993515 : Blo 1774088 3993515 := bstep (se 1 (by rfl) ⟨2995136, by rfl⟩ : syracuseStep 3993515 = 5990273) B5990273
theorem B20213711 : Blo 1774088 20213711 := bstep (se 1 (by rfl) ⟨15160283, by rfl⟩ : syracuseStep 20213711 = 30320567) B30320567
theorem B17051629 : Blo 1774088 17051629 := bstep (se 3 (by rfl) ⟨3197180, by rfl⟩ : syracuseStep 17051629 = 6394361) B6394361
theorem B10252307 : Blo 1774088 10252307 := bstep (se 1 (by rfl) ⟨7689230, by rfl⟩ : syracuseStep 10252307 = 15378461) B15378461
theorem B25604201 : Blo 1774088 25604201 := bstep (se 2 (by rfl) ⟨9601575, by rfl⟩ : syracuseStep 25604201 = 19203151) B19203151
theorem B3993875 : Blo 1774088 3993875 := bstep (se 1 (by rfl) ⟨2995406, by rfl⟩ : syracuseStep 3993875 = 5990813) B5990813
theorem B6738299 : Blo 1774088 6738299 := bstep (se 1 (by rfl) ⟨5053724, by rfl⟩ : syracuseStep 6738299 = 10107449) B10107449
theorem B3994055 : Blo 1774088 3994055 := bstep (se 1 (by rfl) ⟨2995541, by rfl⟩ : syracuseStep 3994055 = 5991083) B5991083
theorem B5993135 : Blo 1774088 5993135 := bstep (se 1 (by rfl) ⟨4494851, by rfl⟩ : syracuseStep 5993135 = 8989703) B8989703
theorem B1774331 : Blo 1774088 1774331 := bstep (se 1 (by rfl) ⟨1330748, by rfl⟩ : syracuseStep 1774331 = 2661497) B2661497
theorem B3994415 : Blo 1774088 3994415 := bstep (se 1 (by rfl) ⟨2995811, by rfl⟩ : syracuseStep 3994415 = 5991623) B5991623
theorem B1774399 : Blo 1774088 1774399 := bstep (se 1 (by rfl) ⟨1330799, by rfl⟩ : syracuseStep 1774399 = 2661599) B2661599
theorem B4494163 : Blo 1774088 4494163 := bstep (se 1 (by rfl) ⟨3370622, by rfl⟩ : syracuseStep 4494163 = 6741245) B6741245
theorem B1774427 : Blo 1774088 1774427 := bstep (se 1 (by rfl) ⟨1330820, by rfl⟩ : syracuseStep 1774427 = 2661641) B2661641
theorem B3789679 : Blo 1774088 3789679 := bstep (se 1 (by rfl) ⟨2842259, by rfl⟩ : syracuseStep 3789679 = 5684519) B5684519
theorem B3994505 : Blo 1774088 3994505 := bstep (se 2 (by rfl) ⟨1497939, by rfl⟩ : syracuseStep 3994505 = 2995879) B2995879
theorem B1774495 : Blo 1774088 1774495 := bstep (se 1 (by rfl) ⟨1330871, by rfl⟩ : syracuseStep 1774495 = 2661743) B2661743
theorem B1774575 : Blo 1774088 1774575 := bstep (se 1 (by rfl) ⟨1330931, by rfl⟩ : syracuseStep 1774575 = 2661863) B2661863
theorem B1774663 : Blo 1774088 1774663 := bstep (se 1 (by rfl) ⟨1330997, by rfl⟩ : syracuseStep 1774663 = 2661995) B2661995
theorem B1995871 : Blo 1774088 1995871 := bstep (se 1 (by rfl) ⟨1496903, by rfl⟩ : syracuseStep 1995871 = 2993807) B2993807
theorem B19461259 : Blo 1774088 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B1774747 : Blo 1774088 1774747 := bstep (se 1 (by rfl) ⟨1331060, by rfl⟩ : syracuseStep 1774747 = 2662121) B2662121
theorem B25588979 : Blo 1774088 25588979 := bstep (se 1 (by rfl) ⟨19191734, by rfl⟩ : syracuseStep 25588979 = 38383469) B38383469
theorem B1774843 : Blo 1774088 1774843 := bstep (se 1 (by rfl) ⟨1331132, by rfl⟩ : syracuseStep 1774843 = 2662265) B2662265
theorem B1774911 : Blo 1774088 1774911 := bstep (se 1 (by rfl) ⟨1331183, by rfl⟩ : syracuseStep 1774911 = 2662367) B2662367
theorem B1775079 : Blo 1774088 1775079 := bstep (se 1 (by rfl) ⟨1331309, by rfl⟩ : syracuseStep 1775079 = 2662619) B2662619
theorem B1775087 : Blo 1774088 1775087 := bstep (se 1 (by rfl) ⟨1331315, by rfl⟩ : syracuseStep 1775087 = 2662631) B2662631
theorem B1775195 : Blo 1774088 1775195 := bstep (se 1 (by rfl) ⟨1331396, by rfl⟩ : syracuseStep 1775195 = 2662793) B2662793
theorem B3995279 : Blo 1774088 3995279 := bstep (se 1 (by rfl) ⟨2996459, by rfl⟩ : syracuseStep 3995279 = 5992919) B5992919
theorem B1775259 : Blo 1774088 1775259 := bstep (se 1 (by rfl) ⟨1331444, by rfl⟩ : syracuseStep 1775259 = 2662889) B2662889
theorem B3995369 : Blo 1774088 3995369 := bstep (se 2 (by rfl) ⟨1498263, by rfl⟩ : syracuseStep 3995369 = 2996527) B2996527
theorem B1775343 : Blo 1774088 1775343 := bstep (se 1 (by rfl) ⟨1331507, by rfl⟩ : syracuseStep 1775343 = 2663015) B2663015
theorem B1775431 : Blo 1774088 1775431 := bstep (se 1 (by rfl) ⟨1331573, by rfl⟩ : syracuseStep 1775431 = 2663147) B2663147
theorem B28800845 : Blo 1774088 28800845 := bstep (se 3 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 28800845 = 10800317) B10800317
theorem B1775451 : Blo 1774088 1775451 := bstep (se 1 (by rfl) ⟨1331588, by rfl⟩ : syracuseStep 1775451 = 2663177) B2663177
theorem B1775519 : Blo 1774088 1775519 := bstep (se 1 (by rfl) ⟨1331639, by rfl⟩ : syracuseStep 1775519 = 2663279) B2663279
theorem B1775687 : Blo 1774088 1775687 := bstep (se 1 (by rfl) ⟨1331765, by rfl⟩ : syracuseStep 1775687 = 2663531) B2663531
theorem B8984681 : Blo 1774088 8984681 := bstep (se 2 (by rfl) ⟨3369255, by rfl⟩ : syracuseStep 8984681 = 6738511) B6738511
theorem B5052631 : Blo 1774088 5052631 := bstep (se 1 (by rfl) ⟨3789473, by rfl⟩ : syracuseStep 5052631 = 7578947) B7578947
theorem B1775847 : Blo 1774088 1775847 := bstep (se 1 (by rfl) ⟨1331885, by rfl⟩ : syracuseStep 1775847 = 2663771) B2663771
theorem B28776701 : Blo 1774088 28776701 := bstep (se 3 (by rfl) ⟨5395631, by rfl⟩ : syracuseStep 28776701 = 10791263) B10791263
theorem B22755599 : Blo 1774088 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B83106137 : Blo 1774088 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B1776031 : Blo 1774088 1776031 := bstep (se 1 (by rfl) ⟨1332023, by rfl⟩ : syracuseStep 1776031 = 2664047) B2664047
theorem B1776079 : Blo 1774088 1776079 := bstep (se 1 (by rfl) ⟨1332059, by rfl⟩ : syracuseStep 1776079 = 2664119) B2664119
theorem B3791387 : Blo 1774088 3791387 := bstep (se 1 (by rfl) ⟨2843540, by rfl⟩ : syracuseStep 3791387 = 5687081) B5687081
theorem B2996777 : Blo 1774088 2996777 := bstep (se 2 (by rfl) ⟨1123791, by rfl⟩ : syracuseStep 2996777 = 2247583) B2247583
theorem B65649305 : Blo 1774088 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B5765897 : Blo 1774088 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B2661191 : Blo 1774088 2661191 := bstep (se 1 (by rfl) ⟨1995893, by rfl⟩ : syracuseStep 2661191 = 3991787) B3991787
theorem B13483097 : Blo 1774088 13483097 := bstep (se 2 (by rfl) ⟨5056161, by rfl⟩ : syracuseStep 13483097 = 10112323) B10112323
theorem B1998031 : Blo 1774088 1998031 := bstep (se 1 (by rfl) ⟨1498523, by rfl⟩ : syracuseStep 1998031 = 2997047) B2997047
theorem B34577837 : Blo 1774088 34577837 := bstep (se 3 (by rfl) ⟨6483344, by rfl⟩ : syracuseStep 34577837 = 12966689) B12966689
theorem B27327955 : Blo 1774088 27327955 := bstep (se 1 (by rfl) ⟨20495966, by rfl⟩ : syracuseStep 27327955 = 40991933) B40991933
theorem B3792361 : Blo 1774088 3792361 := bstep (se 2 (by rfl) ⟨1422135, by rfl⟩ : syracuseStep 3792361 = 2844271) B2844271
theorem B194231843 : Blo 1774088 194231843 := bstep (se 1 (by rfl) ⟨145673882, by rfl⟩ : syracuseStep 194231843 = 291347765) B291347765
theorem B4046399 : Blo 1774088 4046399 := bstep (se 1 (by rfl) ⟨3034799, by rfl⟩ : syracuseStep 4046399 = 6069599) B6069599
theorem B13483583 : Blo 1774088 13483583 := bstep (se 1 (by rfl) ⟨10112687, by rfl⟩ : syracuseStep 13483583 = 20225375) B20225375
theorem B2662055 : Blo 1774088 2662055 := bstep (se 1 (by rfl) ⟨1996541, by rfl⟩ : syracuseStep 2662055 = 3993083) B3993083
theorem B2662175 : Blo 1774088 2662175 := bstep (se 1 (by rfl) ⟨1996631, by rfl⟩ : syracuseStep 2662175 = 3993263) B3993263
theorem B3792737 : Blo 1774088 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B6741899 : Blo 1774088 6741899 := bstep (se 1 (by rfl) ⟨5056424, by rfl⟩ : syracuseStep 6741899 = 10112849) B10112849
theorem B43171973 : Blo 1774088 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B2662583 : Blo 1774088 2662583 := bstep (se 1 (by rfl) ⟨1996937, by rfl⟩ : syracuseStep 2662583 = 3993875) B3993875
theorem B2662703 : Blo 1774088 2662703 := bstep (se 1 (by rfl) ⟨1997027, by rfl⟩ : syracuseStep 2662703 = 3994055) B3994055
theorem B10944983 : Blo 1774088 10944983 := bstep (se 1 (by rfl) ⟨8208737, by rfl⟩ : syracuseStep 10944983 = 16417475) B16417475
theorem B2662943 : Blo 1774088 2662943 := bstep (se 1 (by rfl) ⟨1997207, by rfl⟩ : syracuseStep 2662943 = 3994415) B3994415
theorem B2663003 : Blo 1774088 2663003 := bstep (se 1 (by rfl) ⟨1997252, by rfl⟩ : syracuseStep 2663003 = 3994505) B3994505
theorem B2663519 : Blo 1774088 2663519 := bstep (se 1 (by rfl) ⟨1997639, by rfl⟩ : syracuseStep 2663519 = 3995279) B3995279
theorem B2663579 : Blo 1774088 2663579 := bstep (se 1 (by rfl) ⟨1997684, by rfl⟩ : syracuseStep 2663579 = 3995369) B3995369
theorem B5989787 : Blo 1774088 5989787 := bstep (se 1 (by rfl) ⟨4492340, by rfl⟩ : syracuseStep 5989787 = 8984681) B8984681
theorem B10110365 : Blo 1774088 10110365 := bstep (se 3 (by rfl) ⟨1895693, by rfl⟩ : syracuseStep 10110365 = 3791387) B3791387
theorem B55404091 : Blo 1774088 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B2664041 : Blo 1774088 2664041 := bstep (se 2 (by rfl) ⟨999015, by rfl⟩ : syracuseStep 2664041 = 1998031) B1998031
theorem B3843931 : Blo 1774088 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B5056481 : Blo 1774088 5056481 := bstep (se 2 (by rfl) ⟨1896180, by rfl⟩ : syracuseStep 5056481 = 3792361) B3792361
theorem B8988731 : Blo 1774088 8988731 := bstep (se 1 (by rfl) ⟨6741548, by rfl⟩ : syracuseStep 8988731 = 13483097) B13483097
theorem B4491359 : Blo 1774088 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B2844809 : Blo 1774088 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B2697599 : Blo 1774088 2697599 := bstep (se 1 (by rfl) ⟨2023199, by rfl⟩ : syracuseStep 2697599 = 4046399) B4046399
theorem B21596543 : Blo 1774088 21596543 := bstep (se 1 (by rfl) ⟨16197407, by rfl⟩ : syracuseStep 21596543 = 32394815) B32394815
theorem B8989055 : Blo 1774088 8989055 := bstep (se 1 (by rfl) ⟨6741791, by rfl⟩ : syracuseStep 8989055 = 13483583) B13483583
theorem B2247259 : Blo 1774088 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B22735505 : Blo 1774088 22735505 := bstep (se 2 (by rfl) ⟨8525814, by rfl⟩ : syracuseStep 22735505 = 17051629) B17051629
theorem B6834871 : Blo 1774088 6834871 := bstep (se 1 (by rfl) ⟨5126153, by rfl⟩ : syracuseStep 6834871 = 10252307) B10252307
theorem B4492057 : Blo 1774088 4492057 := bstep (se 2 (by rfl) ⟨1684521, by rfl⟩ : syracuseStep 4492057 = 3369043) B3369043
theorem B4492199 : Blo 1774088 4492199 := bstep (se 1 (by rfl) ⟨3369149, by rfl⟩ : syracuseStep 4492199 = 6738299) B6738299
theorem B6736841 : Blo 1774088 6736841 := bstep (se 2 (by rfl) ⟨2526315, by rfl⟩ : syracuseStep 6736841 = 5052631) B5052631
theorem B4492361 : Blo 1774088 4492361 := bstep (se 2 (by rfl) ⟨1684635, by rfl⟩ : syracuseStep 4492361 = 3369271) B3369271
theorem B3992687 : Blo 1774088 3992687 := bstep (se 1 (by rfl) ⟨2994515, by rfl⟩ : syracuseStep 3992687 = 5989031) B5989031
theorem B5991677 : Blo 1774088 5991677 := bstep (se 3 (by rfl) ⟨1123439, by rfl⟩ : syracuseStep 5991677 = 2246879) B2246879
theorem B3992903 : Blo 1774088 3992903 := bstep (se 1 (by rfl) ⟨2994677, by rfl⟩ : syracuseStep 3992903 = 5989355) B5989355
theorem B17059319 : Blo 1774088 17059319 := bstep (se 1 (by rfl) ⟨12794489, by rfl⟩ : syracuseStep 17059319 = 25588979) B25588979
theorem B8990351 : Blo 1774088 8990351 := bstep (se 1 (by rfl) ⟨6742763, by rfl⟩ : syracuseStep 8990351 = 13485527) B13485527
theorem B5992217 : Blo 1774088 5992217 := bstep (se 2 (by rfl) ⟨2247081, by rfl⟩ : syracuseStep 5992217 = 4494163) B4494163
theorem B4796399 : Blo 1774088 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B21590023 : Blo 1774088 21590023 := bstep (se 1 (by rfl) ⟨16192517, by rfl⟩ : syracuseStep 21590023 = 32385035) B32385035
theorem B3993695 : Blo 1774088 3993695 := bstep (se 1 (by rfl) ⟨2995271, by rfl⟩ : syracuseStep 3993695 = 5990543) B5990543
theorem B25948345 : Blo 1774088 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B3371215 : Blo 1774088 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B15167735 : Blo 1774088 15167735 := bstep (se 1 (by rfl) ⟨11375801, by rfl⟩ : syracuseStep 15167735 = 22751603) B22751603
theorem B43766203 : Blo 1774088 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B1774127 : Blo 1774088 1774127 := bstep (se 1 (by rfl) ⟨1330595, by rfl⟩ : syracuseStep 1774127 = 2661191) B2661191
theorem B2995103 : Blo 1774088 2995103 := bstep (se 1 (by rfl) ⟨2246327, by rfl⟩ : syracuseStep 2995103 = 4492655) B4492655
theorem B4494305 : Blo 1774088 4494305 := bstep (se 2 (by rfl) ⟨1685364, by rfl⟩ : syracuseStep 4494305 = 3370729) B3370729
theorem B129487895 : Blo 1774088 129487895 := bstep (se 1 (by rfl) ⟨97115921, by rfl⟩ : syracuseStep 129487895 = 194231843) B194231843
theorem B1774703 : Blo 1774088 1774703 := bstep (se 1 (by rfl) ⟨1331027, by rfl⟩ : syracuseStep 1774703 = 2662055) B2662055
theorem B1995943 : Blo 1774088 1995943 := bstep (se 1 (by rfl) ⟨1496957, by rfl⟩ : syracuseStep 1995943 = 2993915) B2993915
theorem B4265129 : Blo 1774088 4265129 := bstep (se 2 (by rfl) ⟨1599423, by rfl⟩ : syracuseStep 4265129 = 3198847) B3198847
theorem B1774783 : Blo 1774088 1774783 := bstep (se 1 (by rfl) ⟨1331087, by rfl⟩ : syracuseStep 1774783 = 2662175) B2662175
theorem B2528491 : Blo 1774088 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B10794235 : Blo 1774088 10794235 := bstep (se 1 (by rfl) ⟨8095676, by rfl⟩ : syracuseStep 10794235 = 16191353) B16191353
theorem B4494599 : Blo 1774088 4494599 := bstep (se 1 (by rfl) ⟨3370949, by rfl⟩ : syracuseStep 4494599 = 6741899) B6741899
theorem B17069467 : Blo 1774088 17069467 := bstep (se 1 (by rfl) ⟨12802100, by rfl⟩ : syracuseStep 17069467 = 25604201) B25604201
theorem B1775071 : Blo 1774088 1775071 := bstep (se 1 (by rfl) ⟨1331303, by rfl⟩ : syracuseStep 1775071 = 2662607) B2662607
theorem B1775103 : Blo 1774088 1775103 := bstep (se 1 (by rfl) ⟨1331327, by rfl⟩ : syracuseStep 1775103 = 2662655) B2662655
theorem B3995423 : Blo 1774088 3995423 := bstep (se 1 (by rfl) ⟨2996567, by rfl⟩ : syracuseStep 3995423 = 5993135) B5993135
theorem B4495135 : Blo 1774088 4495135 := bstep (se 1 (by rfl) ⟨3371351, by rfl⟩ : syracuseStep 4495135 = 6742703) B6742703
theorem B17061779 : Blo 1774088 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B8984519 : Blo 1774088 8984519 := bstep (se 1 (by rfl) ⟨6738389, by rfl⟩ : syracuseStep 8984519 = 13476779) B13476779
theorem B1775647 : Blo 1774088 1775647 := bstep (se 1 (by rfl) ⟨1331735, by rfl⟩ : syracuseStep 1775647 = 2663471) B2663471
theorem B1775727 : Blo 1774088 1775727 := bstep (se 1 (by rfl) ⟨1331795, by rfl⟩ : syracuseStep 1775727 = 2663591) B2663591
theorem B1775975 : Blo 1774088 1775975 := bstep (se 1 (by rfl) ⟨1331981, by rfl⟩ : syracuseStep 1775975 = 2663963) B2663963
theorem B5052905 : Blo 1774088 5052905 := bstep (se 2 (by rfl) ⟨1894839, by rfl⟩ : syracuseStep 5052905 = 3789679) B3789679
theorem B19200563 : Blo 1774088 19200563 := bstep (se 1 (by rfl) ⟨14400422, by rfl⟩ : syracuseStep 19200563 = 28800845) B28800845
theorem B9722591 : Blo 1774088 9722591 := bstep (se 1 (by rfl) ⟨7291943, by rfl⟩ : syracuseStep 9722591 = 14583887) B14583887
theorem B30333689 : Blo 1774088 30333689 := bstep (se 2 (by rfl) ⟨11375133, by rfl⟩ : syracuseStep 30333689 = 22750267) B22750267
theorem B2661161 : Blo 1774088 2661161 := bstep (se 2 (by rfl) ⟨997935, by rfl⟩ : syracuseStep 2661161 = 1995871) B1995871
theorem B19184467 : Blo 1774088 19184467 := bstep (se 1 (by rfl) ⟨14388350, by rfl⟩ : syracuseStep 19184467 = 28776701) B28776701
theorem B15170399 : Blo 1774088 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B2661371 : Blo 1774088 2661371 := bstep (se 1 (by rfl) ⟨1996028, by rfl⟩ : syracuseStep 2661371 = 3992057) B3992057
theorem B1997851 : Blo 1774088 1997851 := bstep (se 1 (by rfl) ⟨1498388, by rfl⟩ : syracuseStep 1997851 = 2996777) B2996777
theorem B2661407 : Blo 1774088 2661407 := bstep (se 1 (by rfl) ⟨1996055, by rfl⟩ : syracuseStep 2661407 = 3992111) B3992111
theorem B2661431 : Blo 1774088 2661431 := bstep (se 1 (by rfl) ⟨1996073, by rfl⟩ : syracuseStep 2661431 = 3992147) B3992147
theorem B2563127 : Blo 1774088 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B2661551 : Blo 1774088 2661551 := bstep (se 1 (by rfl) ⟨1996163, by rfl⟩ : syracuseStep 2661551 = 3992327) B3992327
theorem B36437273 : Blo 1774088 36437273 := bstep (se 2 (by rfl) ⟨13663977, by rfl⟩ : syracuseStep 36437273 = 27327955) B27327955
theorem B5987627 : Blo 1774088 5987627 := bstep (se 1 (by rfl) ⟨4490720, by rfl⟩ : syracuseStep 5987627 = 8981441) B8981441
theorem B2661695 : Blo 1774088 2661695 := bstep (se 1 (by rfl) ⟨1996271, by rfl⟩ : syracuseStep 2661695 = 3992543) B3992543
theorem B64806277 : Blo 1774088 64806277 := bstep (se 4 (by rfl) ⟨6075588, by rfl⟩ : syracuseStep 64806277 = 12151177) B12151177
theorem B2661839 : Blo 1774088 2661839 := bstep (se 1 (by rfl) ⟨1996379, by rfl⟩ : syracuseStep 2661839 = 3992759) B3992759
theorem B34119251 : Blo 1774088 34119251 := bstep (se 1 (by rfl) ⟨25589438, by rfl⟩ : syracuseStep 34119251 = 51178877) B51178877
theorem B23051891 : Blo 1774088 23051891 := bstep (se 1 (by rfl) ⟨17288918, by rfl⟩ : syracuseStep 23051891 = 34577837) B34577837
theorem B2662223 : Blo 1774088 2662223 := bstep (se 1 (by rfl) ⟨1996667, by rfl⟩ : syracuseStep 2662223 = 3993335) B3993335
theorem B2662271 : Blo 1774088 2662271 := bstep (se 1 (by rfl) ⟨1996703, by rfl⟩ : syracuseStep 2662271 = 3993407) B3993407
theorem B5054363 : Blo 1774088 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B2662343 : Blo 1774088 2662343 := bstep (se 1 (by rfl) ⟨1996757, by rfl⟩ : syracuseStep 2662343 = 3993515) B3993515
theorem B13475807 : Blo 1774088 13475807 := bstep (se 1 (by rfl) ⟨10106855, by rfl⟩ : syracuseStep 13475807 = 20213711) B20213711
theorem B5988329 : Blo 1774088 5988329 := bstep (se 2 (by rfl) ⟨2245623, by rfl⟩ : syracuseStep 5988329 = 4491247) B4491247
theorem B28786697 : Blo 1774088 28786697 := bstep (se 2 (by rfl) ⟨10795011, by rfl⟩ : syracuseStep 28786697 = 21590023) B21590023
theorem B2662463 : Blo 1774088 2662463 := bstep (se 1 (by rfl) ⟨1996847, by rfl⟩ : syracuseStep 2662463 = 3993695) B3993695
theorem B2843419 : Blo 1774088 2843419 := bstep (se 1 (by rfl) ⟨2132564, by rfl⟩ : syracuseStep 2843419 = 4265129) B4265129
theorem B5989409 : Blo 1774088 5989409 := bstep (se 2 (by rfl) ⟨2246028, by rfl⟩ : syracuseStep 5989409 = 4492057) B4492057
theorem B2663615 : Blo 1774088 2663615 := bstep (se 1 (by rfl) ⟨1997711, by rfl⟩ : syracuseStep 2663615 = 3995423) B3995423
theorem B5989679 : Blo 1774088 5989679 := bstep (se 1 (by rfl) ⟨4492259, by rfl⟩ : syracuseStep 5989679 = 8984519) B8984519
theorem B2663801 : Blo 1774088 2663801 := bstep (se 2 (by rfl) ⟨998925, by rfl⟩ : syracuseStep 2663801 = 1997851) B1997851
theorem B3368603 : Blo 1774088 3368603 := bstep (se 1 (by rfl) ⟨2526452, by rfl⟩ : syracuseStep 3368603 = 5052905) B5052905
theorem B15157003 : Blo 1774088 15157003 := bstep (se 1 (by rfl) ⟨11367752, by rfl⟩ : syracuseStep 15157003 = 22735505) B22735505
theorem B6481727 : Blo 1774088 6481727 := bstep (se 1 (by rfl) ⟨4861295, by rfl⟩ : syracuseStep 6481727 = 9722591) B9722591
theorem B22759289 : Blo 1774088 22759289 := bstep (se 2 (by rfl) ⟨8534733, by rfl⟩ : syracuseStep 22759289 = 17069467) B17069467
theorem B4491227 : Blo 1774088 4491227 := bstep (se 1 (by rfl) ⟨3368420, by rfl⟩ : syracuseStep 4491227 = 6736841) B6736841
theorem B24291515 : Blo 1774088 24291515 := bstep (se 1 (by rfl) ⟨18218636, by rfl⟩ : syracuseStep 24291515 = 36437273) B36437273
theorem B3991751 : Blo 1774088 3991751 := bstep (se 1 (by rfl) ⟨2993813, by rfl⟩ : syracuseStep 3991751 = 5987627) B5987627
theorem B11372879 : Blo 1774088 11372879 := bstep (se 1 (by rfl) ⟨8529659, by rfl⟩ : syracuseStep 11372879 = 17059319) B17059319
theorem B3369575 : Blo 1774088 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B3992219 : Blo 1774088 3992219 := bstep (se 1 (by rfl) ⟨2994164, by rfl⟩ : syracuseStep 3992219 = 5988329) B5988329
theorem B3197599 : Blo 1774088 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B28781315 : Blo 1774088 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B10111823 : Blo 1774088 10111823 := bstep (se 1 (by rfl) ⟨7583867, by rfl⟩ : syracuseStep 10111823 = 15167735) B15167735
theorem B34597793 : Blo 1774088 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B27340021 : Blo 1774088 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B58354937 : Blo 1774088 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B9113161 : Blo 1774088 9113161 := bstep (se 2 (by rfl) ⟨3417435, by rfl⟩ : syracuseStep 9113161 = 6834871) B6834871
theorem B3993191 : Blo 1774088 3993191 := bstep (se 1 (by rfl) ⟨2994893, by rfl⟩ : syracuseStep 3993191 = 5989787) B5989787
theorem B25579289 : Blo 1774088 25579289 := bstep (se 2 (by rfl) ⟨9592233, by rfl⟩ : syracuseStep 25579289 = 19184467) B19184467
theorem B11374519 : Blo 1774088 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B3370987 : Blo 1774088 3370987 := bstep (se 1 (by rfl) ⟨2528240, by rfl⟩ : syracuseStep 3370987 = 5056481) B5056481
theorem B5992487 : Blo 1774088 5992487 := bstep (se 1 (by rfl) ⟨4494365, by rfl⟩ : syracuseStep 5992487 = 8988731) B8988731
theorem B2994239 : Blo 1774088 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B1896539 : Blo 1774088 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1798399 : Blo 1774088 1798399 := bstep (se 1 (by rfl) ⟨1348799, by rfl⟩ : syracuseStep 1798399 = 2697599) B2697599
theorem B14397695 : Blo 1774088 14397695 := bstep (se 1 (by rfl) ⟨10798271, by rfl⟩ : syracuseStep 14397695 = 21596543) B21596543
theorem B5992703 : Blo 1774088 5992703 := bstep (se 1 (by rfl) ⟨4494527, by rfl⟩ : syracuseStep 5992703 = 8989055) B8989055
theorem B3371321 : Blo 1774088 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B12800375 : Blo 1774088 12800375 := bstep (se 1 (by rfl) ⟨9600281, by rfl⟩ : syracuseStep 12800375 = 19200563) B19200563
theorem B20222459 : Blo 1774088 20222459 := bstep (se 1 (by rfl) ⟨15166844, by rfl⟩ : syracuseStep 20222459 = 30333689) B30333689
theorem B1774107 : Blo 1774088 1774107 := bstep (se 1 (by rfl) ⟨1330580, by rfl⟩ : syracuseStep 1774107 = 2661161) B2661161
theorem B10113599 : Blo 1774088 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B2994799 : Blo 1774088 2994799 := bstep (se 1 (by rfl) ⟨2246099, by rfl⟩ : syracuseStep 2994799 = 4492199) B4492199
theorem B1774247 : Blo 1774088 1774247 := bstep (se 1 (by rfl) ⟨1330685, by rfl⟩ : syracuseStep 1774247 = 2661371) B2661371
theorem B1774271 : Blo 1774088 1774271 := bstep (se 1 (by rfl) ⟨1330703, by rfl⟩ : syracuseStep 1774271 = 2661407) B2661407
theorem B1774287 : Blo 1774088 1774287 := bstep (se 1 (by rfl) ⟨1330715, by rfl⟩ : syracuseStep 1774287 = 2661431) B2661431
theorem B2994907 : Blo 1774088 2994907 := bstep (se 1 (by rfl) ⟨2246180, by rfl⟩ : syracuseStep 2994907 = 4492361) B4492361
theorem B73872121 : Blo 1774088 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B1774367 : Blo 1774088 1774367 := bstep (se 1 (by rfl) ⟨1330775, by rfl⟩ : syracuseStep 1774367 = 2661551) B2661551
theorem B3994451 : Blo 1774088 3994451 := bstep (se 1 (by rfl) ⟨2995838, by rfl⟩ : syracuseStep 3994451 = 5991677) B5991677
theorem B1774463 : Blo 1774088 1774463 := bstep (se 1 (by rfl) ⟨1330847, by rfl⟩ : syracuseStep 1774463 = 2661695) B2661695
theorem B1774559 : Blo 1774088 1774559 := bstep (se 1 (by rfl) ⟨1330919, by rfl⟩ : syracuseStep 1774559 = 2661839) B2661839
theorem B5993513 : Blo 1774088 5993513 := bstep (se 2 (by rfl) ⟨2247567, by rfl⟩ : syracuseStep 5993513 = 4495135) B4495135
theorem B22746167 : Blo 1774088 22746167 := bstep (se 1 (by rfl) ⟨17059625, by rfl⟩ : syracuseStep 22746167 = 34119251) B34119251
theorem B5993567 : Blo 1774088 5993567 := bstep (se 1 (by rfl) ⟨4495175, by rfl⟩ : syracuseStep 5993567 = 8990351) B8990351
theorem B5125241 : Blo 1774088 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B3994811 : Blo 1774088 3994811 := bstep (se 1 (by rfl) ⟨2996108, by rfl⟩ : syracuseStep 3994811 = 5992217) B5992217
theorem B1774815 : Blo 1774088 1774815 := bstep (se 1 (by rfl) ⟨1331111, by rfl⟩ : syracuseStep 1774815 = 2662223) B2662223
theorem B1774847 : Blo 1774088 1774847 := bstep (se 1 (by rfl) ⟨1331135, by rfl⟩ : syracuseStep 1774847 = 2662271) B2662271
theorem B1774895 : Blo 1774088 1774895 := bstep (se 1 (by rfl) ⟨1331171, by rfl⟩ : syracuseStep 1774895 = 2662343) B2662343
theorem B8983871 : Blo 1774088 8983871 := bstep (se 1 (by rfl) ⟨6737903, by rfl⟩ : syracuseStep 8983871 = 13475807) B13475807
theorem B1775055 : Blo 1774088 1775055 := bstep (se 1 (by rfl) ⟨1331291, by rfl⟩ : syracuseStep 1775055 = 2662583) B2662583
theorem B1775135 : Blo 1774088 1775135 := bstep (se 1 (by rfl) ⟨1331351, by rfl⟩ : syracuseStep 1775135 = 2662703) B2662703
theorem B4494953 : Blo 1774088 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B7296655 : Blo 1774088 7296655 := bstep (se 1 (by rfl) ⟨5472491, by rfl⟩ : syracuseStep 7296655 = 10944983) B10944983
theorem B1775295 : Blo 1774088 1775295 := bstep (se 1 (by rfl) ⟨1331471, by rfl⟩ : syracuseStep 1775295 = 2662943) B2662943
theorem B1775335 : Blo 1774088 1775335 := bstep (se 1 (by rfl) ⟨1331501, by rfl⟩ : syracuseStep 1775335 = 2663003) B2663003
theorem B1996735 : Blo 1774088 1996735 := bstep (se 1 (by rfl) ⟨1497551, by rfl⟩ : syracuseStep 1996735 = 2995103) B2995103
theorem B2996203 : Blo 1774088 2996203 := bstep (se 1 (by rfl) ⟨2247152, by rfl⟩ : syracuseStep 2996203 = 4494305) B4494305
theorem B86325263 : Blo 1774088 86325263 := bstep (se 1 (by rfl) ⟨64743947, by rfl⟩ : syracuseStep 86325263 = 129487895) B129487895
theorem B1775679 : Blo 1774088 1775679 := bstep (se 1 (by rfl) ⟨1331759, by rfl⟩ : syracuseStep 1775679 = 2663519) B2663519
theorem B1775719 : Blo 1774088 1775719 := bstep (se 1 (by rfl) ⟨1331789, by rfl⟩ : syracuseStep 1775719 = 2663579) B2663579
theorem B2996345 : Blo 1774088 2996345 := bstep (se 2 (by rfl) ⟨1123629, by rfl⟩ : syracuseStep 2996345 = 2247259) B2247259
theorem B2996399 : Blo 1774088 2996399 := bstep (se 1 (by rfl) ⟨2247299, by rfl⟩ : syracuseStep 2996399 = 4494599) B4494599
theorem B6740243 : Blo 1774088 6740243 := bstep (se 1 (by rfl) ⟨5055182, by rfl⟩ : syracuseStep 6740243 = 10110365) B10110365
theorem B1776027 : Blo 1774088 1776027 := bstep (se 1 (by rfl) ⟨1332020, by rfl⟩ : syracuseStep 1776027 = 2664041) B2664041
theorem B2661257 : Blo 1774088 2661257 := bstep (se 2 (by rfl) ⟨997971, by rfl⟩ : syracuseStep 2661257 = 1995943) B1995943
theorem B14392313 : Blo 1774088 14392313 := bstep (se 2 (by rfl) ⟨5397117, by rfl⟩ : syracuseStep 14392313 = 10794235) B10794235
theorem B86408369 : Blo 1774088 86408369 := bstep (se 2 (by rfl) ⟨32403138, by rfl⟩ : syracuseStep 86408369 = 64806277) B64806277
theorem B2661791 : Blo 1774088 2661791 := bstep (se 1 (by rfl) ⟨1996343, by rfl⟩ : syracuseStep 2661791 = 3992687) B3992687
theorem B2661935 : Blo 1774088 2661935 := bstep (se 1 (by rfl) ⟨1996451, by rfl⟩ : syracuseStep 2661935 = 3992903) B3992903
theorem B15367927 : Blo 1774088 15367927 := bstep (se 1 (by rfl) ⟨11525945, by rfl⟩ : syracuseStep 15367927 = 23051891) B23051891
theorem B6742399 : Blo 1774088 6742399 := bstep (se 1 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 6742399 = 10113599) B10113599
theorem B2662967 : Blo 1774088 2662967 := bstep (se 1 (by rfl) ⟨1997225, by rfl⟩ : syracuseStep 2662967 = 3994451) B3994451
theorem B15164111 : Blo 1774088 15164111 := bstep (se 1 (by rfl) ⟨11373083, by rfl⟩ : syracuseStep 15164111 = 22746167) B22746167
theorem B3416827 : Blo 1774088 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B2663207 : Blo 1774088 2663207 := bstep (se 1 (by rfl) ⟨1997405, by rfl⟩ : syracuseStep 2663207 = 3994811) B3994811
theorem B5989247 : Blo 1774088 5989247 := bstep (se 1 (by rfl) ⟨4491935, by rfl⟩ : syracuseStep 5989247 = 8983871) B8983871
theorem B2245735 : Blo 1774088 2245735 := bstep (se 1 (by rfl) ⟨1684301, by rfl⟩ : syracuseStep 2245735 = 3368603) B3368603
theorem B15172859 : Blo 1774088 15172859 := bstep (se 1 (by rfl) ⟨11379644, by rfl⟩ : syracuseStep 15172859 = 22759289) B22759289
theorem B57550175 : Blo 1774088 57550175 := bstep (se 1 (by rfl) ⟨43162631, by rfl⟩ : syracuseStep 57550175 = 86325263) B86325263
theorem B2246383 : Blo 1774088 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B19187543 : Blo 1774088 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B9594875 : Blo 1774088 9594875 := bstep (se 1 (by rfl) ⟨7196156, by rfl⟩ : syracuseStep 9594875 = 14392313) B14392313
theorem B12150881 : Blo 1774088 12150881 := bstep (se 2 (by rfl) ⟨4556580, by rfl⟩ : syracuseStep 12150881 = 9113161) B9113161
theorem B20490569 : Blo 1774088 20490569 := bstep (se 2 (by rfl) ⟨7683963, by rfl⟩ : syracuseStep 20490569 = 15367927) B15367927
theorem B15166025 : Blo 1774088 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B3992939 : Blo 1774088 3992939 := bstep (se 1 (by rfl) ⟨2994704, by rfl⟩ : syracuseStep 3992939 = 5989409) B5989409
theorem B3993065 : Blo 1774088 3993065 := bstep (se 2 (by rfl) ⟨1497399, by rfl⟩ : syracuseStep 3993065 = 2994799) B2994799
theorem B8990189 : Blo 1774088 8990189 := bstep (se 3 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 8990189 = 3371321) B3371321
theorem B3993119 : Blo 1774088 3993119 := bstep (se 1 (by rfl) ⟨2994839, by rfl⟩ : syracuseStep 3993119 = 5989679) B5989679
theorem B20229749 : Blo 1774088 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B3993209 : Blo 1774088 3993209 := bstep (se 2 (by rfl) ⟨1497453, by rfl⟩ : syracuseStep 3993209 = 2994907) B2994907
theorem B98496161 : Blo 1774088 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B4321151 : Blo 1774088 4321151 := bstep (se 1 (by rfl) ⟨3240863, by rfl⟩ : syracuseStep 4321151 = 6481727) B6481727
theorem B2994151 : Blo 1774088 2994151 := bstep (se 1 (by rfl) ⟨2245613, by rfl⟩ : syracuseStep 2994151 = 4491227) B4491227
theorem B4493495 : Blo 1774088 4493495 := bstep (se 1 (by rfl) ⟨3370121, by rfl⟩ : syracuseStep 4493495 = 6740243) B6740243
theorem B7581919 : Blo 1774088 7581919 := bstep (se 1 (by rfl) ⟨5686439, by rfl⟩ : syracuseStep 7581919 = 11372879) B11372879
theorem B1774171 : Blo 1774088 1774171 := bstep (se 1 (by rfl) ⟨1330628, by rfl⟩ : syracuseStep 1774171 = 2661257) B2661257
theorem B23065195 : Blo 1774088 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B9728873 : Blo 1774088 9728873 := bstep (se 2 (by rfl) ⟨3648327, by rfl⟩ : syracuseStep 9728873 = 7296655) B7296655
theorem B1774527 : Blo 1774088 1774527 := bstep (se 1 (by rfl) ⟨1330895, by rfl⟩ : syracuseStep 1774527 = 2661791) B2661791
theorem B1774623 : Blo 1774088 1774623 := bstep (se 1 (by rfl) ⟨1330967, by rfl⟩ : syracuseStep 1774623 = 2661935) B2661935
theorem B17052859 : Blo 1774088 17052859 := bstep (se 1 (by rfl) ⟨12789644, by rfl⟩ : syracuseStep 17052859 = 25579289) B25579289
theorem B3994937 : Blo 1774088 3994937 := bstep (se 2 (by rfl) ⟨1498101, by rfl⟩ : syracuseStep 3994937 = 2996203) B2996203
theorem B4494649 : Blo 1774088 4494649 := bstep (se 2 (by rfl) ⟨1685493, by rfl⟩ : syracuseStep 4494649 = 3370987) B3370987
theorem B19191131 : Blo 1774088 19191131 := bstep (se 1 (by rfl) ⟨14393348, by rfl⟩ : syracuseStep 19191131 = 28786697) B28786697
theorem B3994991 : Blo 1774088 3994991 := bstep (se 1 (by rfl) ⟨2996243, by rfl⟩ : syracuseStep 3994991 = 5992487) B5992487
theorem B1996159 : Blo 1774088 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B1774975 : Blo 1774088 1774975 := bstep (se 1 (by rfl) ⟨1331231, by rfl⟩ : syracuseStep 1774975 = 2662463) B2662463
theorem B9598463 : Blo 1774088 9598463 := bstep (se 1 (by rfl) ⟨7198847, by rfl⟩ : syracuseStep 9598463 = 14397695) B14397695
theorem B3995135 : Blo 1774088 3995135 := bstep (se 1 (by rfl) ⟨2996351, by rfl⟩ : syracuseStep 3995135 = 5992703) B5992703
theorem B8533583 : Blo 1774088 8533583 := bstep (se 1 (by rfl) ⟨6400187, by rfl⟩ : syracuseStep 8533583 = 12800375) B12800375
theorem B2397865 : Blo 1774088 2397865 := bstep (se 2 (by rfl) ⟨899199, by rfl⟩ : syracuseStep 2397865 = 1798399) B1798399
theorem B13481639 : Blo 1774088 13481639 := bstep (se 1 (by rfl) ⟨10111229, by rfl⟩ : syracuseStep 13481639 = 20222459) B20222459
theorem B3995675 : Blo 1774088 3995675 := bstep (se 1 (by rfl) ⟨2996756, by rfl⟩ : syracuseStep 3995675 = 5993513) B5993513
theorem B3995711 : Blo 1774088 3995711 := bstep (se 1 (by rfl) ⟨2996783, by rfl⟩ : syracuseStep 3995711 = 5993567) B5993567
theorem B1775743 : Blo 1774088 1775743 := bstep (se 1 (by rfl) ⟨1331807, by rfl⟩ : syracuseStep 1775743 = 2663615) B2663615
theorem B17053861 : Blo 1774088 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B1775867 : Blo 1774088 1775867 := bstep (se 1 (by rfl) ⟨1331900, by rfl⟩ : syracuseStep 1775867 = 2663801) B2663801
theorem B3791225 : Blo 1774088 3791225 := bstep (se 2 (by rfl) ⟨1421709, by rfl⟩ : syracuseStep 3791225 = 2843419) B2843419
theorem B2996635 : Blo 1774088 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B1997563 : Blo 1774088 1997563 := bstep (se 1 (by rfl) ⟨1498172, by rfl⟩ : syracuseStep 1997563 = 2996345) B2996345
theorem B1997599 : Blo 1774088 1997599 := bstep (se 1 (by rfl) ⟨1498199, by rfl⟩ : syracuseStep 1997599 = 2996399) B2996399
theorem B16194343 : Blo 1774088 16194343 := bstep (se 1 (by rfl) ⟨12145757, by rfl⟩ : syracuseStep 16194343 = 24291515) B24291515
theorem B2661167 : Blo 1774088 2661167 := bstep (se 1 (by rfl) ⟨1995875, by rfl⟩ : syracuseStep 2661167 = 3991751) B3991751
theorem B36453361 : Blo 1774088 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B2661479 : Blo 1774088 2661479 := bstep (se 1 (by rfl) ⟨1996109, by rfl⟩ : syracuseStep 2661479 = 3992219) B3992219
theorem B6741215 : Blo 1774088 6741215 := bstep (se 1 (by rfl) ⟨5055911, by rfl⟩ : syracuseStep 6741215 = 10111823) B10111823
theorem B57605579 : Blo 1774088 57605579 := bstep (se 1 (by rfl) ⟨43204184, by rfl⟩ : syracuseStep 57605579 = 86408369) B86408369
theorem B38903291 : Blo 1774088 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B20209337 : Blo 1774088 20209337 := bstep (se 2 (by rfl) ⟨7578501, by rfl⟩ : syracuseStep 20209337 = 15157003) B15157003
theorem B2662127 : Blo 1774088 2662127 := bstep (se 1 (by rfl) ⟨1996595, by rfl⟩ : syracuseStep 2662127 = 3993191) B3993191
theorem B2662313 : Blo 1774088 2662313 := bstep (se 2 (by rfl) ⟨998367, by rfl⟩ : syracuseStep 2662313 = 1996735) B1996735
theorem B10109225 : Blo 1774088 10109225 := bstep (se 2 (by rfl) ⟨3790959, by rfl⟩ : syracuseStep 10109225 = 7581919) B7581919
theorem B10109407 : Blo 1774088 10109407 := bstep (se 1 (by rfl) ⟨7582055, by rfl⟩ : syracuseStep 10109407 = 15164111) B15164111
theorem B30753593 : Blo 1774088 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B2663291 : Blo 1774088 2663291 := bstep (se 1 (by rfl) ⟨1997468, by rfl⟩ : syracuseStep 2663291 = 3994937) B3994937
theorem B2663327 : Blo 1774088 2663327 := bstep (se 1 (by rfl) ⟨1997495, by rfl⟩ : syracuseStep 2663327 = 3994991) B3994991
theorem B10109933 : Blo 1774088 10109933 := bstep (se 3 (by rfl) ⟨1895612, by rfl⟩ : syracuseStep 10109933 = 3791225) B3791225
theorem B4555769 : Blo 1774088 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B2663417 : Blo 1774088 2663417 := bstep (se 2 (by rfl) ⟨998781, by rfl⟩ : syracuseStep 2663417 = 1997563) B1997563
theorem B6398975 : Blo 1774088 6398975 := bstep (se 1 (by rfl) ⟨4799231, by rfl⟩ : syracuseStep 6398975 = 9598463) B9598463
theorem B2663423 : Blo 1774088 2663423 := bstep (se 1 (by rfl) ⟨1997567, by rfl⟩ : syracuseStep 2663423 = 3995135) B3995135
theorem B2663465 : Blo 1774088 2663465 := bstep (se 2 (by rfl) ⟨998799, by rfl⟩ : syracuseStep 2663465 = 1997599) B1997599
theorem B8987759 : Blo 1774088 8987759 := bstep (se 1 (by rfl) ⟨6740819, by rfl⟩ : syracuseStep 8987759 = 13481639) B13481639
theorem B48604481 : Blo 1774088 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B2663783 : Blo 1774088 2663783 := bstep (se 1 (by rfl) ⟨1997837, by rfl⟩ : syracuseStep 2663783 = 3995675) B3995675
theorem B2663807 : Blo 1774088 2663807 := bstep (se 1 (by rfl) ⟨1997855, by rfl⟩ : syracuseStep 2663807 = 3995711) B3995711
theorem B10110683 : Blo 1774088 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B3197153 : Blo 1774088 3197153 := bstep (se 2 (by rfl) ⟨1198932, by rfl⟩ : syracuseStep 3197153 = 2397865) B2397865
theorem B13486499 : Blo 1774088 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B3992201 : Blo 1774088 3992201 := bstep (se 2 (by rfl) ⟨1497075, by rfl⟩ : syracuseStep 3992201 = 2994151) B2994151
theorem B8989865 : Blo 1774088 8989865 := bstep (se 2 (by rfl) ⟨3371199, by rfl⟩ : syracuseStep 8989865 = 6742399) B6742399
theorem B3992831 : Blo 1774088 3992831 := bstep (se 1 (by rfl) ⟨2994623, by rfl⟩ : syracuseStep 3992831 = 5989247) B5989247
theorem B38366783 : Blo 1774088 38366783 := bstep (se 1 (by rfl) ⟨28775087, by rfl⟩ : syracuseStep 38366783 = 57550175) B57550175
theorem B5689055 : Blo 1774088 5689055 := bstep (se 1 (by rfl) ⟨4266791, by rfl⟩ : syracuseStep 5689055 = 8533583) B8533583
theorem B12791695 : Blo 1774088 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B2994313 : Blo 1774088 2994313 := bstep (se 2 (by rfl) ⟨1122867, by rfl⟩ : syracuseStep 2994313 = 2245735) B2245735
theorem B13660379 : Blo 1774088 13660379 := bstep (se 1 (by rfl) ⟨10245284, by rfl⟩ : syracuseStep 13660379 = 20490569) B20490569
theorem B22737145 : Blo 1774088 22737145 := bstep (se 2 (by rfl) ⟨8526429, by rfl⟩ : syracuseStep 22737145 = 17052859) B17052859
theorem B5992865 : Blo 1774088 5992865 := bstep (se 2 (by rfl) ⟨2247324, by rfl⟩ : syracuseStep 5992865 = 4494649) B4494649
theorem B1774111 : Blo 1774088 1774111 := bstep (se 1 (by rfl) ⟨1330583, by rfl⟩ : syracuseStep 1774111 = 2661167) B2661167
theorem B1774319 : Blo 1774088 1774319 := bstep (se 1 (by rfl) ⟨1330739, by rfl⟩ : syracuseStep 1774319 = 2661479) B2661479
theorem B4494143 : Blo 1774088 4494143 := bstep (se 1 (by rfl) ⟨3370607, by rfl⟩ : syracuseStep 4494143 = 6741215) B6741215
theorem B2995177 : Blo 1774088 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B5993459 : Blo 1774088 5993459 := bstep (se 1 (by rfl) ⟨4495094, by rfl⟩ : syracuseStep 5993459 = 8990189) B8990189
theorem B65664107 : Blo 1774088 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B13472891 : Blo 1774088 13472891 := bstep (se 1 (by rfl) ⟨10104668, by rfl⟩ : syracuseStep 13472891 = 20209337) B20209337
theorem B1774751 : Blo 1774088 1774751 := bstep (se 1 (by rfl) ⟨1331063, by rfl⟩ : syracuseStep 1774751 = 2662127) B2662127
theorem B2880767 : Blo 1774088 2880767 := bstep (se 1 (by rfl) ⟨2160575, by rfl⟩ : syracuseStep 2880767 = 4321151) B4321151
theorem B1774875 : Blo 1774088 1774875 := bstep (se 1 (by rfl) ⟨1331156, by rfl⟩ : syracuseStep 1774875 = 2662313) B2662313
theorem B2995663 : Blo 1774088 2995663 := bstep (se 1 (by rfl) ⟨2246747, by rfl⟩ : syracuseStep 2995663 = 4493495) B4493495
theorem B22738481 : Blo 1774088 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B1775311 : Blo 1774088 1775311 := bstep (se 1 (by rfl) ⟨1331483, by rfl⟩ : syracuseStep 1775311 = 2662967) B2662967
theorem B1775471 : Blo 1774088 1775471 := bstep (se 1 (by rfl) ⟨1331603, by rfl⟩ : syracuseStep 1775471 = 2663207) B2663207
theorem B3995513 : Blo 1774088 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B6485915 : Blo 1774088 6485915 := bstep (se 1 (by rfl) ⟨4864436, by rfl⟩ : syracuseStep 6485915 = 9728873) B9728873
theorem B10115239 : Blo 1774088 10115239 := bstep (se 1 (by rfl) ⟨7586429, by rfl⟩ : syracuseStep 10115239 = 15172859) B15172859
theorem B12794087 : Blo 1774088 12794087 := bstep (se 1 (by rfl) ⟨9595565, by rfl⟩ : syracuseStep 12794087 = 19191131) B19191131
theorem B21592457 : Blo 1774088 21592457 := bstep (se 2 (by rfl) ⟨8097171, by rfl⟩ : syracuseStep 21592457 = 16194343) B16194343
theorem B6396583 : Blo 1774088 6396583 := bstep (se 1 (by rfl) ⟨4797437, by rfl⟩ : syracuseStep 6396583 = 9594875) B9594875
theorem B8100587 : Blo 1774088 8100587 := bstep (se 1 (by rfl) ⟨6075440, by rfl⟩ : syracuseStep 8100587 = 12150881) B12150881
theorem B2661545 : Blo 1774088 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B2661959 : Blo 1774088 2661959 := bstep (se 1 (by rfl) ⟨1996469, by rfl⟩ : syracuseStep 2661959 = 3992939) B3992939
theorem B38403719 : Blo 1774088 38403719 := bstep (se 1 (by rfl) ⟨28802789, by rfl⟩ : syracuseStep 38403719 = 57605579) B57605579
theorem B2662043 : Blo 1774088 2662043 := bstep (se 1 (by rfl) ⟨1996532, by rfl⟩ : syracuseStep 2662043 = 3993065) B3993065
theorem B25935527 : Blo 1774088 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B2662079 : Blo 1774088 2662079 := bstep (se 1 (by rfl) ⟨1996559, by rfl⟩ : syracuseStep 2662079 = 3993119) B3993119
theorem B2662139 : Blo 1774088 2662139 := bstep (se 1 (by rfl) ⟨1996604, by rfl⟩ : syracuseStep 2662139 = 3993209) B3993209
theorem B8528777 : Blo 1774088 8528777 := bstep (se 2 (by rfl) ⟨3198291, by rfl⟩ : syracuseStep 8528777 = 6396583) B6396583
theorem B2663675 : Blo 1774088 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B2131435 : Blo 1774088 2131435 := bstep (se 1 (by rfl) ⟨1598576, by rfl⟩ : syracuseStep 2131435 = 3197153) B3197153
theorem B8529391 : Blo 1774088 8529391 := bstep (se 1 (by rfl) ⟨6397043, by rfl⟩ : syracuseStep 8529391 = 12794087) B12794087
theorem B14394971 : Blo 1774088 14394971 := bstep (se 1 (by rfl) ⟨10796228, by rfl⟩ : syracuseStep 14394971 = 21592457) B21592457
theorem B5400391 : Blo 1774088 5400391 := bstep (se 1 (by rfl) ⟨4050293, by rfl⟩ : syracuseStep 5400391 = 8100587) B8100587
theorem B25577855 : Blo 1774088 25577855 := bstep (se 1 (by rfl) ⟨19183391, by rfl⟩ : syracuseStep 25577855 = 38366783) B38366783
theorem B25602479 : Blo 1774088 25602479 := bstep (se 1 (by rfl) ⟨19201859, by rfl⟩ : syracuseStep 25602479 = 38403719) B38403719
theorem B3992417 : Blo 1774088 3992417 := bstep (se 2 (by rfl) ⟨1497156, by rfl⟩ : syracuseStep 3992417 = 2994313) B2994313
theorem B13486985 : Blo 1774088 13486985 := bstep (se 2 (by rfl) ⟨5057619, by rfl⟩ : syracuseStep 13486985 = 10115239) B10115239
theorem B13479209 : Blo 1774088 13479209 := bstep (se 2 (by rfl) ⟨5054703, by rfl⟩ : syracuseStep 13479209 = 10109407) B10109407
theorem B5991839 : Blo 1774088 5991839 := bstep (se 1 (by rfl) ⟨4493879, by rfl⟩ : syracuseStep 5991839 = 8987759) B8987759
theorem B8981927 : Blo 1774088 8981927 := bstep (se 1 (by rfl) ⟨6736445, by rfl⟩ : syracuseStep 8981927 = 13472891) B13472891
theorem B1920511 : Blo 1774088 1920511 := bstep (se 1 (by rfl) ⟨1440383, by rfl⟩ : syracuseStep 1920511 = 2880767) B2880767
theorem B32402987 : Blo 1774088 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B15158987 : Blo 1774088 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B3993569 : Blo 1774088 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B8990999 : Blo 1774088 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B3994217 : Blo 1774088 3994217 := bstep (se 2 (by rfl) ⟨1497831, by rfl⟩ : syracuseStep 3994217 = 2995663) B2995663
theorem B1774363 : Blo 1774088 1774363 := bstep (se 1 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 1774363 = 2661545) B2661545
theorem B5993243 : Blo 1774088 5993243 := bstep (se 1 (by rfl) ⟨4494932, by rfl⟩ : syracuseStep 5993243 = 8989865) B8989865
theorem B1774639 : Blo 1774088 1774639 := bstep (se 1 (by rfl) ⟨1330979, by rfl⟩ : syracuseStep 1774639 = 2661959) B2661959
theorem B1774695 : Blo 1774088 1774695 := bstep (se 1 (by rfl) ⟨1331021, by rfl⟩ : syracuseStep 1774695 = 2662043) B2662043
theorem B17290351 : Blo 1774088 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B1774719 : Blo 1774088 1774719 := bstep (se 1 (by rfl) ⟨1331039, by rfl⟩ : syracuseStep 1774719 = 2662079) B2662079
theorem B1774759 : Blo 1774088 1774759 := bstep (se 1 (by rfl) ⟨1331069, by rfl⟩ : syracuseStep 1774759 = 2662139) B2662139
theorem B9106919 : Blo 1774088 9106919 := bstep (se 1 (by rfl) ⟨6830189, by rfl⟩ : syracuseStep 9106919 = 13660379) B13660379
theorem B6739483 : Blo 1774088 6739483 := bstep (se 1 (by rfl) ⟨5054612, by rfl⟩ : syracuseStep 6739483 = 10109225) B10109225
theorem B3995243 : Blo 1774088 3995243 := bstep (se 1 (by rfl) ⟨2996432, by rfl⟩ : syracuseStep 3995243 = 5992865) B5992865
theorem B30316193 : Blo 1774088 30316193 := bstep (se 2 (by rfl) ⟨11368572, by rfl⟩ : syracuseStep 30316193 = 22737145) B22737145
theorem B20502395 : Blo 1774088 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B2996095 : Blo 1774088 2996095 := bstep (se 1 (by rfl) ⟨2247071, by rfl⟩ : syracuseStep 2996095 = 4494143) B4494143
theorem B1775527 : Blo 1774088 1775527 := bstep (se 1 (by rfl) ⟨1331645, by rfl⟩ : syracuseStep 1775527 = 2663291) B2663291
theorem B1775551 : Blo 1774088 1775551 := bstep (se 1 (by rfl) ⟨1331663, by rfl⟩ : syracuseStep 1775551 = 2663327) B2663327
theorem B6739955 : Blo 1774088 6739955 := bstep (se 1 (by rfl) ⟨5054966, by rfl⟩ : syracuseStep 6739955 = 10109933) B10109933
theorem B3995639 : Blo 1774088 3995639 := bstep (se 1 (by rfl) ⟨2996729, by rfl⟩ : syracuseStep 3995639 = 5993459) B5993459
theorem B1775611 : Blo 1774088 1775611 := bstep (se 1 (by rfl) ⟨1331708, by rfl⟩ : syracuseStep 1775611 = 2663417) B2663417
theorem B4265983 : Blo 1774088 4265983 := bstep (se 1 (by rfl) ⟨3199487, by rfl⟩ : syracuseStep 4265983 = 6398975) B6398975
theorem B1775615 : Blo 1774088 1775615 := bstep (se 1 (by rfl) ⟨1331711, by rfl⟩ : syracuseStep 1775615 = 2663423) B2663423
theorem B1775643 : Blo 1774088 1775643 := bstep (se 1 (by rfl) ⟨1331732, by rfl⟩ : syracuseStep 1775643 = 2663465) B2663465
theorem B43776071 : Blo 1774088 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B1775855 : Blo 1774088 1775855 := bstep (se 1 (by rfl) ⟨1331891, by rfl⟩ : syracuseStep 1775855 = 2663783) B2663783
theorem B1775871 : Blo 1774088 1775871 := bstep (se 1 (by rfl) ⟨1331903, by rfl⟩ : syracuseStep 1775871 = 2663807) B2663807
theorem B6740455 : Blo 1774088 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B4323943 : Blo 1774088 4323943 := bstep (se 1 (by rfl) ⟨3242957, by rfl⟩ : syracuseStep 4323943 = 6485915) B6485915
theorem B2661467 : Blo 1774088 2661467 := bstep (se 1 (by rfl) ⟨1996100, by rfl⟩ : syracuseStep 2661467 = 3992201) B3992201
theorem B2661887 : Blo 1774088 2661887 := bstep (se 1 (by rfl) ⟨1996415, by rfl⟩ : syracuseStep 2661887 = 3992831) B3992831
theorem B3792703 : Blo 1774088 3792703 := bstep (se 1 (by rfl) ⟨2844527, by rfl⟩ : syracuseStep 3792703 = 5689055) B5689055
theorem B17055593 : Blo 1774088 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B12148717 : Blo 1774088 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B2662811 : Blo 1774088 2662811 := bstep (se 1 (by rfl) ⟨1997108, by rfl⟩ : syracuseStep 2662811 = 3994217) B3994217
theorem B5685851 : Blo 1774088 5685851 := bstep (se 1 (by rfl) ⟨4264388, by rfl⟩ : syracuseStep 5685851 = 8528777) B8528777
theorem B8987273 : Blo 1774088 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B6071279 : Blo 1774088 6071279 := bstep (se 1 (by rfl) ⟨4553459, by rfl⟩ : syracuseStep 6071279 = 9106919) B9106919
theorem B2663495 : Blo 1774088 2663495 := bstep (se 1 (by rfl) ⟨1997621, by rfl⟩ : syracuseStep 2663495 = 3995243) B3995243
theorem B20210795 : Blo 1774088 20210795 := bstep (se 1 (by rfl) ⟨15158096, by rfl⟩ : syracuseStep 20210795 = 30316193) B30316193
theorem B2663759 : Blo 1774088 2663759 := bstep (se 1 (by rfl) ⟨1997819, by rfl⟩ : syracuseStep 2663759 = 3995639) B3995639
theorem B11372521 : Blo 1774088 11372521 := bstep (se 2 (by rfl) ⟨4264695, by rfl⟩ : syracuseStep 11372521 = 8529391) B8529391
theorem B5056937 : Blo 1774088 5056937 := bstep (se 2 (by rfl) ⟨1896351, by rfl⟩ : syracuseStep 5056937 = 3792703) B3792703
theorem B16198289 : Blo 1774088 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B5687977 : Blo 1774088 5687977 := bstep (se 2 (by rfl) ⟨2132991, by rfl⟩ : syracuseStep 5687977 = 4265983) B4265983
theorem B9596647 : Blo 1774088 9596647 := bstep (se 1 (by rfl) ⟨7197485, by rfl⟩ : syracuseStep 9596647 = 14394971) B14394971
theorem B13668263 : Blo 1774088 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B4493303 : Blo 1774088 4493303 := bstep (se 1 (by rfl) ⟨3369977, by rfl⟩ : syracuseStep 4493303 = 6739955) B6739955
theorem B29184047 : Blo 1774088 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B17051903 : Blo 1774088 17051903 := bstep (se 1 (by rfl) ⟨12788927, by rfl⟩ : syracuseStep 17051903 = 25577855) B25577855
theorem B17068319 : Blo 1774088 17068319 := bstep (se 1 (by rfl) ⟨12801239, by rfl⟩ : syracuseStep 17068319 = 25602479) B25602479
theorem B8991323 : Blo 1774088 8991323 := bstep (se 1 (by rfl) ⟨6743492, by rfl⟩ : syracuseStep 8991323 = 13486985) B13486985
theorem B2560681 : Blo 1774088 2560681 := bstep (se 2 (by rfl) ⟨960255, by rfl⟩ : syracuseStep 2560681 = 1920511) B1920511
theorem B1774311 : Blo 1774088 1774311 := bstep (se 1 (by rfl) ⟨1330733, by rfl⟩ : syracuseStep 1774311 = 2661467) B2661467
theorem B3994559 : Blo 1774088 3994559 := bstep (se 1 (by rfl) ⟨2995919, by rfl⟩ : syracuseStep 3994559 = 5991839) B5991839
theorem B1774591 : Blo 1774088 1774591 := bstep (se 1 (by rfl) ⟨1330943, by rfl⟩ : syracuseStep 1774591 = 2661887) B2661887
theorem B10105991 : Blo 1774088 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B3994793 : Blo 1774088 3994793 := bstep (se 2 (by rfl) ⟨1498047, by rfl⟩ : syracuseStep 3994793 = 2996095) B2996095
theorem B5993999 : Blo 1774088 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B3995495 : Blo 1774088 3995495 := bstep (se 1 (by rfl) ⟨2996621, by rfl⟩ : syracuseStep 3995495 = 5993243) B5993243
theorem B92215205 : Blo 1774088 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B5765257 : Blo 1774088 5765257 := bstep (se 2 (by rfl) ⟨2161971, by rfl⟩ : syracuseStep 5765257 = 4323943) B4323943
theorem B1775783 : Blo 1774088 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B2661611 : Blo 1774088 2661611 := bstep (se 1 (by rfl) ⟨1996208, by rfl⟩ : syracuseStep 2661611 = 3992417) B3992417
theorem B2841913 : Blo 1774088 2841913 := bstep (se 2 (by rfl) ⟨1065717, by rfl⟩ : syracuseStep 2841913 = 2131435) B2131435
theorem B8985977 : Blo 1774088 8985977 := bstep (se 2 (by rfl) ⟨3369741, by rfl⟩ : syracuseStep 8985977 = 6739483) B6739483
theorem B8986139 : Blo 1774088 8986139 := bstep (se 1 (by rfl) ⟨6739604, by rfl⟩ : syracuseStep 8986139 = 13479209) B13479209
theorem B5987951 : Blo 1774088 5987951 := bstep (se 1 (by rfl) ⟨4490963, by rfl⟩ : syracuseStep 5987951 = 8981927) B8981927
theorem B21601991 : Blo 1774088 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B7200521 : Blo 1774088 7200521 := bstep (se 2 (by rfl) ⟨2700195, by rfl⟩ : syracuseStep 7200521 = 5400391) B5400391
theorem B11370395 : Blo 1774088 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B2662379 : Blo 1774088 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B19456031 : Blo 1774088 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B11378879 : Blo 1774088 11378879 := bstep (se 1 (by rfl) ⟨8534159, by rfl⟩ : syracuseStep 11378879 = 17068319) B17068319
theorem B2663039 : Blo 1774088 2663039 := bstep (se 1 (by rfl) ⟨1997279, by rfl⟩ : syracuseStep 2663039 = 3994559) B3994559
theorem B2663195 : Blo 1774088 2663195 := bstep (se 1 (by rfl) ⟨1997396, by rfl⟩ : syracuseStep 2663195 = 3994793) B3994793
theorem B2663663 : Blo 1774088 2663663 := bstep (se 1 (by rfl) ⟨1997747, by rfl⟩ : syracuseStep 2663663 = 3995495) B3995495
theorem B10798859 : Blo 1774088 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B5990651 : Blo 1774088 5990651 := bstep (se 1 (by rfl) ⟨4492988, by rfl⟩ : syracuseStep 5990651 = 8985977) B8985977
theorem B5990759 : Blo 1774088 5990759 := bstep (se 1 (by rfl) ⟨4493069, by rfl⟩ : syracuseStep 5990759 = 8986139) B8986139
theorem B3991967 : Blo 1774088 3991967 := bstep (se 1 (by rfl) ⟨2993975, by rfl⟩ : syracuseStep 3991967 = 5987951) B5987951
theorem B7580263 : Blo 1774088 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B9112175 : Blo 1774088 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B16190077 : Blo 1774088 16190077 := bstep (se 3 (by rfl) ⟨3035639, by rfl⟩ : syracuseStep 16190077 = 6071279) B6071279
theorem B7687009 : Blo 1774088 7687009 := bstep (se 2 (by rfl) ⟨2882628, by rfl⟩ : syracuseStep 7687009 = 5765257) B5765257
theorem B5991515 : Blo 1774088 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B6737327 : Blo 1774088 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B61476803 : Blo 1774088 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B3371291 : Blo 1774088 3371291 := bstep (se 1 (by rfl) ⟨2528468, by rfl⟩ : syracuseStep 3371291 = 5056937) B5056937
theorem B3789217 : Blo 1774088 3789217 := bstep (se 2 (by rfl) ⟨1420956, by rfl⟩ : syracuseStep 3789217 = 2841913) B2841913
theorem B1774407 : Blo 1774088 1774407 := bstep (se 1 (by rfl) ⟨1330805, by rfl⟩ : syracuseStep 1774407 = 2661611) B2661611
theorem B1774919 : Blo 1774088 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B2995535 : Blo 1774088 2995535 := bstep (se 1 (by rfl) ⟨2246651, by rfl⟩ : syracuseStep 2995535 = 4493303) B4493303
theorem B11367935 : Blo 1774088 11367935 := bstep (se 1 (by rfl) ⟨8525951, by rfl⟩ : syracuseStep 11367935 = 17051903) B17051903
theorem B1775207 : Blo 1774088 1775207 := bstep (se 1 (by rfl) ⟨1331405, by rfl⟩ : syracuseStep 1775207 = 2662811) B2662811
theorem B3790567 : Blo 1774088 3790567 := bstep (se 1 (by rfl) ⟨2842925, by rfl⟩ : syracuseStep 3790567 = 5685851) B5685851
theorem B5994215 : Blo 1774088 5994215 := bstep (se 1 (by rfl) ⟨4495661, by rfl⟩ : syracuseStep 5994215 = 8991323) B8991323
theorem B1775663 : Blo 1774088 1775663 := bstep (se 1 (by rfl) ⟨1331747, by rfl⟩ : syracuseStep 1775663 = 2663495) B2663495
theorem B13473863 : Blo 1774088 13473863 := bstep (se 1 (by rfl) ⟨10105397, by rfl⟩ : syracuseStep 13473863 = 20210795) B20210795
theorem B1775839 : Blo 1774088 1775839 := bstep (se 1 (by rfl) ⟨1331879, by rfl⟩ : syracuseStep 1775839 = 2663759) B2663759
theorem B3414241 : Blo 1774088 3414241 := bstep (se 2 (by rfl) ⟨1280340, by rfl⟩ : syracuseStep 3414241 = 2560681) B2560681
theorem B7583969 : Blo 1774088 7583969 := bstep (se 2 (by rfl) ⟨2843988, by rfl⟩ : syracuseStep 7583969 = 5687977) B5687977
theorem B3995999 : Blo 1774088 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B12795529 : Blo 1774088 12795529 := bstep (se 2 (by rfl) ⟨4798323, by rfl⟩ : syracuseStep 12795529 = 9596647) B9596647
theorem B14401327 : Blo 1774088 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B4800347 : Blo 1774088 4800347 := bstep (se 1 (by rfl) ⟨3600260, by rfl⟩ : syracuseStep 4800347 = 7200521) B7200521
theorem B15163361 : Blo 1774088 15163361 := bstep (se 2 (by rfl) ⟨5686260, by rfl⟩ : syracuseStep 15163361 = 11372521) B11372521
theorem B7585919 : Blo 1774088 7585919 := bstep (se 1 (by rfl) ⟨5689439, by rfl⟩ : syracuseStep 7585919 = 11378879) B11378879
theorem B21586769 : Blo 1774088 21586769 := bstep (se 2 (by rfl) ⟨8095038, by rfl⟩ : syracuseStep 21586769 = 16190077) B16190077
theorem B7578623 : Blo 1774088 7578623 := bstep (se 1 (by rfl) ⟨5683967, by rfl⟩ : syracuseStep 7578623 = 11367935) B11367935
theorem B10249345 : Blo 1774088 10249345 := bstep (se 2 (by rfl) ⟨3843504, by rfl⟩ : syracuseStep 10249345 = 7687009) B7687009
theorem B2663999 : Blo 1774088 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B4491551 : Blo 1774088 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B12970687 : Blo 1774088 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B2247527 : Blo 1774088 2247527 := bstep (se 1 (by rfl) ⟨1685645, by rfl⟩ : syracuseStep 2247527 = 3371291) B3371291
theorem B8982575 : Blo 1774088 8982575 := bstep (se 1 (by rfl) ⟨6736931, by rfl⟩ : syracuseStep 8982575 = 13473863) B13473863
theorem B3993767 : Blo 1774088 3993767 := bstep (se 1 (by rfl) ⟨2995325, by rfl⟩ : syracuseStep 3993767 = 5990651) B5990651
theorem B3993839 : Blo 1774088 3993839 := bstep (se 1 (by rfl) ⟨2995379, by rfl⟩ : syracuseStep 3993839 = 5990759) B5990759
theorem B6074783 : Blo 1774088 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B3994343 : Blo 1774088 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B17060705 : Blo 1774088 17060705 := bstep (se 2 (by rfl) ⟨6397764, by rfl⟩ : syracuseStep 17060705 = 12795529) B12795529
theorem B3200231 : Blo 1774088 3200231 := bstep (se 1 (by rfl) ⟨2400173, by rfl⟩ : syracuseStep 3200231 = 4800347) B4800347
theorem B4552321 : Blo 1774088 4552321 := bstep (se 2 (by rfl) ⟨1707120, by rfl⟩ : syracuseStep 4552321 = 3414241) B3414241
theorem B1775359 : Blo 1774088 1775359 := bstep (se 1 (by rfl) ⟨1331519, by rfl⟩ : syracuseStep 1775359 = 2663039) B2663039
theorem B1775463 : Blo 1774088 1775463 := bstep (se 1 (by rfl) ⟨1331597, by rfl⟩ : syracuseStep 1775463 = 2663195) B2663195
theorem B5052289 : Blo 1774088 5052289 := bstep (se 2 (by rfl) ⟨1894608, by rfl⟩ : syracuseStep 5052289 = 3789217) B3789217
theorem B20223917 : Blo 1774088 20223917 := bstep (se 3 (by rfl) ⟨3791984, by rfl⟩ : syracuseStep 20223917 = 7583969) B7583969
theorem B10107017 : Blo 1774088 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B1775775 : Blo 1774088 1775775 := bstep (se 1 (by rfl) ⟨1331831, by rfl⟩ : syracuseStep 1775775 = 2663663) B2663663
theorem B1997023 : Blo 1774088 1997023 := bstep (se 1 (by rfl) ⟨1497767, by rfl⟩ : syracuseStep 1997023 = 2995535) B2995535
theorem B3996143 : Blo 1774088 3996143 := bstep (se 1 (by rfl) ⟨2997107, by rfl⟩ : syracuseStep 3996143 = 5994215) B5994215
theorem B7199239 : Blo 1774088 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B2661311 : Blo 1774088 2661311 := bstep (se 1 (by rfl) ⟨1995983, by rfl⟩ : syracuseStep 2661311 = 3991967) B3991967
theorem B5054089 : Blo 1774088 5054089 := bstep (se 2 (by rfl) ⟨1895283, by rfl⟩ : syracuseStep 5054089 = 3790567) B3790567
theorem B19201769 : Blo 1774088 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B40984535 : Blo 1774088 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B10108907 : Blo 1774088 10108907 := bstep (se 1 (by rfl) ⟨7581680, by rfl⟩ : syracuseStep 10108907 = 15163361) B15163361
theorem B5988383 : Blo 1774088 5988383 := bstep (se 1 (by rfl) ⟨4491287, by rfl⟩ : syracuseStep 5988383 = 8982575) B8982575
theorem B2662511 : Blo 1774088 2662511 := bstep (se 1 (by rfl) ⟨1996883, by rfl⟩ : syracuseStep 2662511 = 3993767) B3993767
theorem B2662559 : Blo 1774088 2662559 := bstep (se 1 (by rfl) ⟨1996919, by rfl⟩ : syracuseStep 2662559 = 3993839) B3993839
theorem B2662697 : Blo 1774088 2662697 := bstep (se 2 (by rfl) ⟨998511, by rfl⟩ : syracuseStep 2662697 = 1997023) B1997023
theorem B2662895 : Blo 1774088 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B17294249 : Blo 1774088 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B2664095 : Blo 1774088 2664095 := bstep (se 1 (by rfl) ⟨1998071, by rfl⟩ : syracuseStep 2664095 = 3996143) B3996143
theorem B6736385 : Blo 1774088 6736385 := bstep (se 2 (by rfl) ⟨2526144, by rfl⟩ : syracuseStep 6736385 = 5052289) B5052289
theorem B27323023 : Blo 1774088 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B5057279 : Blo 1774088 5057279 := bstep (se 1 (by rfl) ⟨3792959, by rfl⟩ : syracuseStep 5057279 = 7585919) B7585919
theorem B4049855 : Blo 1774088 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B11373803 : Blo 1774088 11373803 := bstep (se 1 (by rfl) ⟨8530352, by rfl⟩ : syracuseStep 11373803 = 17060705) B17060705
theorem B2133487 : Blo 1774088 2133487 := bstep (se 1 (by rfl) ⟨1600115, by rfl⟩ : syracuseStep 2133487 = 3200231) B3200231
theorem B6738011 : Blo 1774088 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B2994367 : Blo 1774088 2994367 := bstep (se 1 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 2994367 = 4491551) B4491551
theorem B1774207 : Blo 1774088 1774207 := bstep (se 1 (by rfl) ⟨1330655, by rfl⟩ : syracuseStep 1774207 = 2661311) B2661311
theorem B6738785 : Blo 1774088 6738785 := bstep (se 2 (by rfl) ⟨2527044, by rfl⟩ : syracuseStep 6738785 = 5054089) B5054089
theorem B5993405 : Blo 1774088 5993405 := bstep (se 3 (by rfl) ⟨1123763, by rfl⟩ : syracuseStep 5993405 = 2247527) B2247527
theorem B12801179 : Blo 1774088 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B6739271 : Blo 1774088 6739271 := bstep (se 1 (by rfl) ⟨5054453, by rfl⟩ : syracuseStep 6739271 = 10108907) B10108907
theorem B14391179 : Blo 1774088 14391179 := bstep (se 1 (by rfl) ⟨10793384, by rfl⟩ : syracuseStep 14391179 = 21586769) B21586769
theorem B5052415 : Blo 1774088 5052415 := bstep (se 1 (by rfl) ⟨3789311, by rfl⟩ : syracuseStep 5052415 = 7578623) B7578623
theorem B54663173 : Blo 1774088 54663173 := bstep (se 4 (by rfl) ⟨5124672, by rfl⟩ : syracuseStep 54663173 = 10249345) B10249345
theorem B9598985 : Blo 1774088 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B1775999 : Blo 1774088 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B13482611 : Blo 1774088 13482611 := bstep (se 1 (by rfl) ⟨10111958, by rfl⟩ : syracuseStep 13482611 = 20223917) B20223917
theorem B6069761 : Blo 1774088 6069761 := bstep (se 2 (by rfl) ⟨2276160, by rfl⟩ : syracuseStep 6069761 = 4552321) B4552321
theorem B36430697 : Blo 1774088 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B9594119 : Blo 1774088 9594119 := bstep (se 1 (by rfl) ⟨7195589, by rfl⟩ : syracuseStep 9594119 = 14391179) B14391179
theorem B6399323 : Blo 1774088 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B4490923 : Blo 1774088 4490923 := bstep (se 1 (by rfl) ⟨3368192, by rfl⟩ : syracuseStep 4490923 = 6736385) B6736385
theorem B8988407 : Blo 1774088 8988407 := bstep (se 1 (by rfl) ⟨6741305, by rfl⟩ : syracuseStep 8988407 = 13482611) B13482611
theorem B2844649 : Blo 1774088 2844649 := bstep (se 2 (by rfl) ⟨1066743, by rfl⟩ : syracuseStep 2844649 = 2133487) B2133487
theorem B6736553 : Blo 1774088 6736553 := bstep (se 2 (by rfl) ⟨2526207, by rfl⟩ : syracuseStep 6736553 = 5052415) B5052415
theorem B3992255 : Blo 1774088 3992255 := bstep (se 1 (by rfl) ⟨2994191, by rfl⟩ : syracuseStep 3992255 = 5988383) B5988383
theorem B4492007 : Blo 1774088 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B3992489 : Blo 1774088 3992489 := bstep (se 2 (by rfl) ⟨1497183, by rfl⟩ : syracuseStep 3992489 = 2994367) B2994367
theorem B4492523 : Blo 1774088 4492523 := bstep (se 1 (by rfl) ⟨3369392, by rfl⟩ : syracuseStep 4492523 = 6738785) B6738785
theorem B4492847 : Blo 1774088 4492847 := bstep (se 1 (by rfl) ⟨3369635, by rfl⟩ : syracuseStep 4492847 = 6739271) B6739271
theorem B36442115 : Blo 1774088 36442115 := bstep (se 1 (by rfl) ⟨27331586, by rfl⟩ : syracuseStep 36442115 = 54663173) B54663173
theorem B3371519 : Blo 1774088 3371519 := bstep (se 1 (by rfl) ⟨2528639, by rfl⟩ : syracuseStep 3371519 = 5057279) B5057279
theorem B2699903 : Blo 1774088 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B7582535 : Blo 1774088 7582535 := bstep (se 1 (by rfl) ⟨5686901, by rfl⟩ : syracuseStep 7582535 = 11373803) B11373803
theorem B46117997 : Blo 1774088 46117997 := bstep (se 3 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 46117997 = 17294249) B17294249
theorem B1775007 : Blo 1774088 1775007 := bstep (se 1 (by rfl) ⟨1331255, by rfl⟩ : syracuseStep 1775007 = 2662511) B2662511
theorem B1775039 : Blo 1774088 1775039 := bstep (se 1 (by rfl) ⟨1331279, by rfl⟩ : syracuseStep 1775039 = 2662559) B2662559
theorem B1775131 : Blo 1774088 1775131 := bstep (se 1 (by rfl) ⟨1331348, by rfl⟩ : syracuseStep 1775131 = 2662697) B2662697
theorem B1775263 : Blo 1774088 1775263 := bstep (se 1 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 1775263 = 2662895) B2662895
theorem B3995603 : Blo 1774088 3995603 := bstep (se 1 (by rfl) ⟨2996702, by rfl⟩ : syracuseStep 3995603 = 5993405) B5993405
theorem B8534119 : Blo 1774088 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B1776063 : Blo 1774088 1776063 := bstep (se 1 (by rfl) ⟨1332047, by rfl⟩ : syracuseStep 1776063 = 2664095) B2664095
theorem B4046507 : Blo 1774088 4046507 := bstep (se 1 (by rfl) ⟨3034880, by rfl⟩ : syracuseStep 4046507 = 6069761) B6069761
theorem B11378825 : Blo 1774088 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B5055023 : Blo 1774088 5055023 := bstep (se 1 (by rfl) ⟨3791267, by rfl⟩ : syracuseStep 5055023 = 7582535) B7582535
theorem B30745331 : Blo 1774088 30745331 := bstep (se 1 (by rfl) ⟨23058998, by rfl⟩ : syracuseStep 30745331 = 46117997) B46117997
theorem B2663735 : Blo 1774088 2663735 := bstep (se 1 (by rfl) ⟨1997801, by rfl⟩ : syracuseStep 2663735 = 3995603) B3995603
theorem B4491035 : Blo 1774088 4491035 := bstep (se 1 (by rfl) ⟨3368276, by rfl⟩ : syracuseStep 4491035 = 6736553) B6736553
theorem B2697671 : Blo 1774088 2697671 := bstep (se 1 (by rfl) ⟨2023253, by rfl⟩ : syracuseStep 2697671 = 4046507) B4046507
theorem B2247679 : Blo 1774088 2247679 := bstep (se 1 (by rfl) ⟨1685759, by rfl⟩ : syracuseStep 2247679 = 3371519) B3371519
theorem B5992271 : Blo 1774088 5992271 := bstep (se 1 (by rfl) ⟨4494203, by rfl⟩ : syracuseStep 5992271 = 8988407) B8988407
theorem B2994671 : Blo 1774088 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B2995015 : Blo 1774088 2995015 := bstep (se 1 (by rfl) ⟨2246261, by rfl⟩ : syracuseStep 2995015 = 4492523) B4492523
theorem B2995231 : Blo 1774088 2995231 := bstep (se 1 (by rfl) ⟨2246423, by rfl⟩ : syracuseStep 2995231 = 4492847) B4492847
theorem B24294743 : Blo 1774088 24294743 := bstep (se 1 (by rfl) ⟨18221057, by rfl⟩ : syracuseStep 24294743 = 36442115) B36442115
theorem B24287131 : Blo 1774088 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B6396079 : Blo 1774088 6396079 := bstep (se 1 (by rfl) ⟨4797059, by rfl⟩ : syracuseStep 6396079 = 9594119) B9594119
theorem B4266215 : Blo 1774088 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B7199741 : Blo 1774088 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B2661503 : Blo 1774088 2661503 := bstep (se 1 (by rfl) ⟨1996127, by rfl⟩ : syracuseStep 2661503 = 3992255) B3992255
theorem B2661659 : Blo 1774088 2661659 := bstep (se 1 (by rfl) ⟨1996244, by rfl⟩ : syracuseStep 2661659 = 3992489) B3992489
theorem B5987897 : Blo 1774088 5987897 := bstep (se 2 (by rfl) ⟨2245461, by rfl⟩ : syracuseStep 5987897 = 4490923) B4490923
theorem B15171461 : Blo 1774088 15171461 := bstep (se 4 (by rfl) ⟨1422324, by rfl⟩ : syracuseStep 15171461 = 2844649) B2844649
theorem B7585883 : Blo 1774088 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B8528105 : Blo 1774088 8528105 := bstep (se 2 (by rfl) ⟨3198039, by rfl⟩ : syracuseStep 8528105 = 6396079) B6396079
theorem B20496887 : Blo 1774088 20496887 := bstep (se 1 (by rfl) ⟨15372665, by rfl⟩ : syracuseStep 20496887 = 30745331) B30745331
theorem B16196495 : Blo 1774088 16196495 := bstep (se 1 (by rfl) ⟨12147371, by rfl⟩ : syracuseStep 16196495 = 24294743) B24294743
theorem B2844143 : Blo 1774088 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B3991931 : Blo 1774088 3991931 := bstep (se 1 (by rfl) ⟨2993948, by rfl⟩ : syracuseStep 3991931 = 5987897) B5987897
theorem B3370015 : Blo 1774088 3370015 := bstep (se 1 (by rfl) ⟨2527511, by rfl⟩ : syracuseStep 3370015 = 5055023) B5055023
theorem B3993353 : Blo 1774088 3993353 := bstep (se 2 (by rfl) ⟨1497507, by rfl⟩ : syracuseStep 3993353 = 2995015) B2995015
theorem B2994023 : Blo 1774088 2994023 := bstep (se 1 (by rfl) ⟨2245517, by rfl⟩ : syracuseStep 2994023 = 4491035) B4491035
theorem B3993641 : Blo 1774088 3993641 := bstep (se 2 (by rfl) ⟨1497615, by rfl⟩ : syracuseStep 3993641 = 2995231) B2995231
theorem B1798447 : Blo 1774088 1798447 := bstep (se 1 (by rfl) ⟨1348835, by rfl⟩ : syracuseStep 1798447 = 2697671) B2697671
theorem B1774335 : Blo 1774088 1774335 := bstep (se 1 (by rfl) ⟨1330751, by rfl⟩ : syracuseStep 1774335 = 2661503) B2661503
theorem B1774439 : Blo 1774088 1774439 := bstep (se 1 (by rfl) ⟨1330829, by rfl⟩ : syracuseStep 1774439 = 2661659) B2661659
theorem B3994847 : Blo 1774088 3994847 := bstep (se 1 (by rfl) ⟨2996135, by rfl⟩ : syracuseStep 3994847 = 5992271) B5992271
theorem B10114307 : Blo 1774088 10114307 := bstep (se 1 (by rfl) ⟨7585730, by rfl⟩ : syracuseStep 10114307 = 15171461) B15171461
theorem B1996447 : Blo 1774088 1996447 := bstep (se 1 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 1996447 = 2994671) B2994671
theorem B1775823 : Blo 1774088 1775823 := bstep (se 1 (by rfl) ⟨1331867, by rfl⟩ : syracuseStep 1775823 = 2663735) B2663735
theorem B2996905 : Blo 1774088 2996905 := bstep (se 2 (by rfl) ⟨1123839, by rfl⟩ : syracuseStep 2996905 = 2247679) B2247679
theorem B4799827 : Blo 1774088 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B32382841 : Blo 1774088 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B2662427 : Blo 1774088 2662427 := bstep (se 1 (by rfl) ⟨1996820, by rfl⟩ : syracuseStep 2662427 = 3993641) B3993641
theorem B5685403 : Blo 1774088 5685403 := bstep (se 1 (by rfl) ⟨4264052, by rfl⟩ : syracuseStep 5685403 = 8528105) B8528105
theorem B13664591 : Blo 1774088 13664591 := bstep (se 1 (by rfl) ⟨10248443, by rfl⟩ : syracuseStep 13664591 = 20496887) B20496887
theorem B2663231 : Blo 1774088 2663231 := bstep (se 1 (by rfl) ⟨1997423, by rfl⟩ : syracuseStep 2663231 = 3994847) B3994847
theorem B6742871 : Blo 1774088 6742871 := bstep (se 1 (by rfl) ⟨5057153, by rfl⟩ : syracuseStep 6742871 = 10114307) B10114307
theorem B43190653 : Blo 1774088 43190653 := bstep (se 3 (by rfl) ⟨8098247, by rfl⟩ : syracuseStep 43190653 = 16196495) B16196495
theorem B5057255 : Blo 1774088 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B1896095 : Blo 1774088 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B4493353 : Blo 1774088 4493353 := bstep (se 2 (by rfl) ⟨1685007, by rfl⟩ : syracuseStep 4493353 = 3370015) B3370015
theorem B43177121 : Blo 1774088 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B1996015 : Blo 1774088 1996015 := bstep (se 1 (by rfl) ⟨1497011, by rfl⟩ : syracuseStep 1996015 = 2994023) B2994023
theorem B2397929 : Blo 1774088 2397929 := bstep (se 2 (by rfl) ⟨899223, by rfl⟩ : syracuseStep 2397929 = 1798447) B1798447
theorem B3995873 : Blo 1774088 3995873 := bstep (se 2 (by rfl) ⟨1498452, by rfl⟩ : syracuseStep 3995873 = 2996905) B2996905
theorem B2661287 : Blo 1774088 2661287 := bstep (se 1 (by rfl) ⟨1995965, by rfl⟩ : syracuseStep 2661287 = 3991931) B3991931
theorem B25599077 : Blo 1774088 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B2661929 : Blo 1774088 2661929 := bstep (se 2 (by rfl) ⟨998223, by rfl⟩ : syracuseStep 2661929 = 1996447) B1996447
theorem B2662235 : Blo 1774088 2662235 := bstep (se 1 (by rfl) ⟨1996676, by rfl⟩ : syracuseStep 2662235 = 3993353) B3993353
theorem B9109727 : Blo 1774088 9109727 := bstep (se 1 (by rfl) ⟨6832295, by rfl⟩ : syracuseStep 9109727 = 13664591) B13664591
theorem B2663915 : Blo 1774088 2663915 := bstep (se 1 (by rfl) ⟨1997936, by rfl⟩ : syracuseStep 2663915 = 3995873) B3995873
theorem B5056253 : Blo 1774088 5056253 := bstep (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) B1896095
theorem B13486013 : Blo 1774088 13486013 := bstep (se 3 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 13486013 = 5057255) B5057255
theorem B17066051 : Blo 1774088 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B5991137 : Blo 1774088 5991137 := bstep (se 2 (by rfl) ⟨2246676, by rfl⟩ : syracuseStep 5991137 = 4493353) B4493353
theorem B7580537 : Blo 1774088 7580537 := bstep (se 2 (by rfl) ⟨2842701, by rfl⟩ : syracuseStep 7580537 = 5685403) B5685403
theorem B6394477 : Blo 1774088 6394477 := bstep (se 3 (by rfl) ⟨1198964, by rfl⟩ : syracuseStep 6394477 = 2397929) B2397929
theorem B1774191 : Blo 1774088 1774191 := bstep (se 1 (by rfl) ⟨1330643, by rfl⟩ : syracuseStep 1774191 = 2661287) B2661287
theorem B1774619 : Blo 1774088 1774619 := bstep (se 1 (by rfl) ⟨1330964, by rfl⟩ : syracuseStep 1774619 = 2661929) B2661929
theorem B1774823 : Blo 1774088 1774823 := bstep (se 1 (by rfl) ⟨1331117, by rfl⟩ : syracuseStep 1774823 = 2662235) B2662235
theorem B1774951 : Blo 1774088 1774951 := bstep (se 1 (by rfl) ⟨1331213, by rfl⟩ : syracuseStep 1774951 = 2662427) B2662427
theorem B57587537 : Blo 1774088 57587537 := bstep (se 2 (by rfl) ⟨21595326, by rfl⟩ : syracuseStep 57587537 = 43190653) B43190653
theorem B1775487 : Blo 1774088 1775487 := bstep (se 1 (by rfl) ⟨1331615, by rfl⟩ : syracuseStep 1775487 = 2663231) B2663231
theorem B4495247 : Blo 1774088 4495247 := bstep (se 1 (by rfl) ⟨3371435, by rfl⟩ : syracuseStep 4495247 = 6742871) B6742871
theorem B28784747 : Blo 1774088 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B2661353 : Blo 1774088 2661353 := bstep (se 2 (by rfl) ⟨998007, by rfl⟩ : syracuseStep 2661353 = 1996015) B1996015
theorem B76759325 : Blo 1774088 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B6073151 : Blo 1774088 6073151 := bstep (se 1 (by rfl) ⟨4554863, by rfl⟩ : syracuseStep 6073151 = 9109727) B9109727
theorem B3370835 : Blo 1774088 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B38391691 : Blo 1774088 38391691 := bstep (se 1 (by rfl) ⟨28793768, by rfl⟩ : syracuseStep 38391691 = 57587537) B57587537
theorem B8990675 : Blo 1774088 8990675 := bstep (se 1 (by rfl) ⟨6743006, by rfl⟩ : syracuseStep 8990675 = 13486013) B13486013
theorem B3994091 : Blo 1774088 3994091 := bstep (se 1 (by rfl) ⟨2995568, by rfl⟩ : syracuseStep 3994091 = 5991137) B5991137
theorem B1774235 : Blo 1774088 1774235 := bstep (se 1 (by rfl) ⟨1330676, by rfl⟩ : syracuseStep 1774235 = 2661353) B2661353
theorem B8525969 : Blo 1774088 8525969 := bstep (se 2 (by rfl) ⟨3197238, by rfl⟩ : syracuseStep 8525969 = 6394477) B6394477
theorem B1775943 : Blo 1774088 1775943 := bstep (se 1 (by rfl) ⟨1331957, by rfl⟩ : syracuseStep 1775943 = 2663915) B2663915
theorem B2996831 : Blo 1774088 2996831 := bstep (se 1 (by rfl) ⟨2247623, by rfl⟩ : syracuseStep 2996831 = 4495247) B4495247
theorem B11377367 : Blo 1774088 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B5053691 : Blo 1774088 5053691 := bstep (se 1 (by rfl) ⟨3790268, by rfl⟩ : syracuseStep 5053691 = 7580537) B7580537
theorem B2662727 : Blo 1774088 2662727 := bstep (se 1 (by rfl) ⟨1997045, by rfl⟩ : syracuseStep 2662727 = 3994091) B3994091
theorem B3369127 : Blo 1774088 3369127 := bstep (se 1 (by rfl) ⟨2526845, by rfl⟩ : syracuseStep 3369127 = 5053691) B5053691
theorem B8988893 : Blo 1774088 8988893 := bstep (se 3 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 8988893 = 3370835) B3370835
theorem B51188921 : Blo 1774088 51188921 := bstep (se 2 (by rfl) ⟨19195845, by rfl⟩ : syracuseStep 51188921 = 38391691) B38391691
theorem B5993783 : Blo 1774088 5993783 := bstep (se 1 (by rfl) ⟨4495337, by rfl⟩ : syracuseStep 5993783 = 8990675) B8990675
theorem B51172883 : Blo 1774088 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B5683979 : Blo 1774088 5683979 := bstep (se 1 (by rfl) ⟨4262984, by rfl⟩ : syracuseStep 5683979 = 8525969) B8525969
theorem B1997887 : Blo 1774088 1997887 := bstep (se 1 (by rfl) ⟨1498415, by rfl⟩ : syracuseStep 1997887 = 2996831) B2996831
theorem B7584911 : Blo 1774088 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B16195069 : Blo 1774088 16195069 := bstep (se 3 (by rfl) ⟨3036575, by rfl⟩ : syracuseStep 16195069 = 6073151) B6073151
theorem B2663849 : Blo 1774088 2663849 := bstep (se 2 (by rfl) ⟨998943, by rfl⟩ : syracuseStep 2663849 = 1997887) B1997887
theorem B15157277 : Blo 1774088 15157277 := bstep (se 3 (by rfl) ⟨2841989, by rfl⟩ : syracuseStep 15157277 = 5683979) B5683979
theorem B5056607 : Blo 1774088 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B4492169 : Blo 1774088 4492169 := bstep (se 2 (by rfl) ⟨1684563, by rfl⟩ : syracuseStep 4492169 = 3369127) B3369127
theorem B34115255 : Blo 1774088 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B5992595 : Blo 1774088 5992595 := bstep (se 1 (by rfl) ⟨4494446, by rfl⟩ : syracuseStep 5992595 = 8988893) B8988893
theorem B1775151 : Blo 1774088 1775151 := bstep (se 1 (by rfl) ⟨1331363, by rfl⟩ : syracuseStep 1775151 = 2662727) B2662727
theorem B34125947 : Blo 1774088 34125947 := bstep (se 1 (by rfl) ⟨25594460, by rfl⟩ : syracuseStep 34125947 = 51188921) B51188921
theorem B3995855 : Blo 1774088 3995855 := bstep (se 1 (by rfl) ⟨2996891, by rfl⟩ : syracuseStep 3995855 = 5993783) B5993783
theorem B21593425 : Blo 1774088 21593425 := bstep (se 2 (by rfl) ⟨8097534, by rfl⟩ : syracuseStep 21593425 = 16195069) B16195069
theorem B22750631 : Blo 1774088 22750631 := bstep (se 1 (by rfl) ⟨17062973, by rfl⟩ : syracuseStep 22750631 = 34125947) B34125947
theorem B2663903 : Blo 1774088 2663903 := bstep (se 1 (by rfl) ⟨1997927, by rfl⟩ : syracuseStep 2663903 = 3995855) B3995855
theorem B22743503 : Blo 1774088 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B10104851 : Blo 1774088 10104851 := bstep (se 1 (by rfl) ⟨7578638, by rfl⟩ : syracuseStep 10104851 = 15157277) B15157277
theorem B3371071 : Blo 1774088 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B28791233 : Blo 1774088 28791233 := bstep (se 2 (by rfl) ⟨10796712, by rfl⟩ : syracuseStep 28791233 = 21593425) B21593425
theorem B2994779 : Blo 1774088 2994779 := bstep (se 1 (by rfl) ⟨2246084, by rfl⟩ : syracuseStep 2994779 = 4492169) B4492169
theorem B3995063 : Blo 1774088 3995063 := bstep (se 1 (by rfl) ⟨2996297, by rfl⟩ : syracuseStep 3995063 = 5992595) B5992595
theorem B1775899 : Blo 1774088 1775899 := bstep (se 1 (by rfl) ⟨1331924, by rfl⟩ : syracuseStep 1775899 = 2663849) B2663849
theorem B19194155 : Blo 1774088 19194155 := bstep (se 1 (by rfl) ⟨14395616, by rfl⟩ : syracuseStep 19194155 = 28791233) B28791233
theorem B2663375 : Blo 1774088 2663375 := bstep (se 1 (by rfl) ⟨1997531, by rfl⟩ : syracuseStep 2663375 = 3995063) B3995063
theorem B6736567 : Blo 1774088 6736567 := bstep (se 1 (by rfl) ⟨5052425, by rfl⟩ : syracuseStep 6736567 = 10104851) B10104851
theorem B15167087 : Blo 1774088 15167087 := bstep (se 1 (by rfl) ⟨11375315, by rfl⟩ : syracuseStep 15167087 = 22750631) B22750631
theorem B4494761 : Blo 1774088 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B1996519 : Blo 1774088 1996519 := bstep (se 1 (by rfl) ⟨1497389, by rfl⟩ : syracuseStep 1996519 = 2994779) B2994779
theorem B1775935 : Blo 1774088 1775935 := bstep (se 1 (by rfl) ⟨1331951, by rfl⟩ : syracuseStep 1775935 = 2663903) B2663903
theorem B15162335 : Blo 1774088 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B12796103 : Blo 1774088 12796103 := bstep (se 1 (by rfl) ⟨9597077, by rfl⟩ : syracuseStep 12796103 = 19194155) B19194155
theorem B10111391 : Blo 1774088 10111391 := bstep (se 1 (by rfl) ⟨7583543, by rfl⟩ : syracuseStep 10111391 = 15167087) B15167087
theorem B8982089 : Blo 1774088 8982089 := bstep (se 2 (by rfl) ⟨3368283, by rfl⟩ : syracuseStep 8982089 = 6736567) B6736567
theorem B1775583 : Blo 1774088 1775583 := bstep (se 1 (by rfl) ⟨1331687, by rfl⟩ : syracuseStep 1775583 = 2663375) B2663375
theorem B2996507 : Blo 1774088 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B10108223 : Blo 1774088 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B2662025 : Blo 1774088 2662025 := bstep (se 2 (by rfl) ⟨998259, by rfl⟩ : syracuseStep 2662025 = 1996519) B1996519
theorem B34122941 : Blo 1774088 34122941 := bstep (se 3 (by rfl) ⟨6398051, by rfl⟩ : syracuseStep 34122941 = 12796103) B12796103
theorem B6738815 : Blo 1774088 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B1774683 : Blo 1774088 1774683 := bstep (se 1 (by rfl) ⟨1331012, by rfl⟩ : syracuseStep 1774683 = 2662025) B2662025
theorem B1997671 : Blo 1774088 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B6740927 : Blo 1774088 6740927 := bstep (se 1 (by rfl) ⟨5055695, by rfl⟩ : syracuseStep 6740927 = 10111391) B10111391
theorem B5988059 : Blo 1774088 5988059 := bstep (se 1 (by rfl) ⟨4491044, by rfl⟩ : syracuseStep 5988059 = 8982089) B8982089
theorem B2663561 : Blo 1774088 2663561 := bstep (se 2 (by rfl) ⟨998835, by rfl⟩ : syracuseStep 2663561 = 1997671) B1997671
theorem B3992039 : Blo 1774088 3992039 := bstep (se 1 (by rfl) ⟨2994029, by rfl⟩ : syracuseStep 3992039 = 5988059) B5988059
theorem B4492543 : Blo 1774088 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B4493951 : Blo 1774088 4493951 := bstep (se 1 (by rfl) ⟨3370463, by rfl⟩ : syracuseStep 4493951 = 6740927) B6740927
theorem B22748627 : Blo 1774088 22748627 := bstep (se 1 (by rfl) ⟨17061470, by rfl⟩ : syracuseStep 22748627 = 34122941) B34122941
theorem B5990057 : Blo 1774088 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B15165751 : Blo 1774088 15165751 := bstep (se 1 (by rfl) ⟨11374313, by rfl⟩ : syracuseStep 15165751 = 22748627) B22748627
theorem B2995967 : Blo 1774088 2995967 := bstep (se 1 (by rfl) ⟨2246975, by rfl⟩ : syracuseStep 2995967 = 4493951) B4493951
theorem B1775707 : Blo 1774088 1775707 := bstep (se 1 (by rfl) ⟨1331780, by rfl⟩ : syracuseStep 1775707 = 2663561) B2663561
theorem B2661359 : Blo 1774088 2661359 := bstep (se 1 (by rfl) ⟨1996019, by rfl⟩ : syracuseStep 2661359 = 3992039) B3992039
theorem B20221001 : Blo 1774088 20221001 := bstep (se 2 (by rfl) ⟨7582875, by rfl⟩ : syracuseStep 20221001 = 15165751) B15165751
theorem B3993371 : Blo 1774088 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B1774239 : Blo 1774088 1774239 := bstep (se 1 (by rfl) ⟨1330679, by rfl⟩ : syracuseStep 1774239 = 2661359) B2661359
theorem B1997311 : Blo 1774088 1997311 := bstep (se 1 (by rfl) ⟨1497983, by rfl⟩ : syracuseStep 1997311 = 2995967) B2995967
theorem B2663081 : Blo 1774088 2663081 := bstep (se 2 (by rfl) ⟨998655, by rfl⟩ : syracuseStep 2663081 = 1997311) B1997311
theorem B13480667 : Blo 1774088 13480667 := bstep (se 1 (by rfl) ⟨10110500, by rfl⟩ : syracuseStep 13480667 = 20221001) B20221001
theorem B2662247 : Blo 1774088 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B8987111 : Blo 1774088 8987111 := bstep (se 1 (by rfl) ⟨6740333, by rfl⟩ : syracuseStep 8987111 = 13480667) B13480667
theorem B1774831 : Blo 1774088 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B1775387 : Blo 1774088 1775387 := bstep (se 1 (by rfl) ⟨1331540, by rfl⟩ : syracuseStep 1775387 = 2663081) B2663081
theorem B5991407 : Blo 1774088 5991407 := bstep (se 1 (by rfl) ⟨4493555, by rfl⟩ : syracuseStep 5991407 = 8987111) B8987111
theorem B3994271 : Blo 1774088 3994271 := bstep (se 1 (by rfl) ⟨2995703, by rfl⟩ : syracuseStep 3994271 = 5991407) B5991407
theorem B2662847 : Blo 1774088 2662847 := bstep (se 1 (by rfl) ⟨1997135, by rfl⟩ : syracuseStep 2662847 = 3994271) B3994271
theorem B1775231 : Blo 1774088 1775231 := bstep (se 1 (by rfl) ⟨1331423, by rfl⟩ : syracuseStep 1775231 = 2662847) B2662847

theorem C0 (j : ℕ) (h1 : 443522 ≤ j) (h2 : j ≤ 444021) : Blo 1774088 (4 * j + 3) := by
  interval_cases j
  · exact B1774091
  · exact B1774095
  · exact B1774099
  · exact B1774103
  · exact B1774107
  · exact B1774111
  · exact B1774115
  · exact B1774119
  · exact B1774123
  · exact B1774127
  · exact B1774131
  · exact B1774135
  · exact B1774139
  · exact B1774143
  · exact B1774147
  · exact B1774151
  · exact B1774155
  · exact B1774159
  · exact B1774163
  · exact B1774167
  · exact B1774171
  · exact B1774175
  · exact B1774179
  · exact B1774183
  · exact B1774187
  · exact B1774191
  · exact B1774195
  · exact B1774199
  · exact B1774203
  · exact B1774207
  · exact B1774211
  · exact B1774215
  · exact B1774219
  · exact B1774223
  · exact B1774227
  · exact B1774231
  · exact B1774235
  · exact B1774239
  · exact B1774243
  · exact B1774247
  · exact B1774251
  · exact B1774255
  · exact B1774259
  · exact B1774263
  · exact B1774267
  · exact B1774271
  · exact B1774275
  · exact B1774279
  · exact B1774283
  · exact B1774287
  · exact B1774291
  · exact B1774295
  · exact B1774299
  · exact B1774303
  · exact B1774307
  · exact B1774311
  · exact B1774315
  · exact B1774319
  · exact B1774323
  · exact B1774327
  · exact B1774331
  · exact B1774335
  · exact B1774339
  · exact B1774343
  · exact B1774347
  · exact B1774351
  · exact B1774355
  · exact B1774359
  · exact B1774363
  · exact B1774367
  · exact B1774371
  · exact B1774375
  · exact B1774379
  · exact B1774383
  · exact B1774387
  · exact B1774391
  · exact B1774395
  · exact B1774399
  · exact B1774403
  · exact B1774407
  · exact B1774411
  · exact B1774415
  · exact B1774419
  · exact B1774423
  · exact B1774427
  · exact B1774431
  · exact B1774435
  · exact B1774439
  · exact B1774443
  · exact B1774447
  · exact B1774451
  · exact B1774455
  · exact B1774459
  · exact B1774463
  · exact B1774467
  · exact B1774471
  · exact B1774475
  · exact B1774479
  · exact B1774483
  · exact B1774487
  · exact B1774491
  · exact B1774495
  · exact B1774499
  · exact B1774503
  · exact B1774507
  · exact B1774511
  · exact B1774515
  · exact B1774519
  · exact B1774523
  · exact B1774527
  · exact B1774531
  · exact B1774535
  · exact B1774539
  · exact B1774543
  · exact B1774547
  · exact B1774551
  · exact B1774555
  · exact B1774559
  · exact B1774563
  · exact B1774567
  · exact B1774571
  · exact B1774575
  · exact B1774579
  · exact B1774583
  · exact B1774587
  · exact B1774591
  · exact B1774595
  · exact B1774599
  · exact B1774603
  · exact B1774607
  · exact B1774611
  · exact B1774615
  · exact B1774619
  · exact B1774623
  · exact B1774627
  · exact B1774631
  · exact B1774635
  · exact B1774639
  · exact B1774643
  · exact B1774647
  · exact B1774651
  · exact B1774655
  · exact B1774659
  · exact B1774663
  · exact B1774667
  · exact B1774671
  · exact B1774675
  · exact B1774679
  · exact B1774683
  · exact B1774687
  · exact B1774691
  · exact B1774695
  · exact B1774699
  · exact B1774703
  · exact B1774707
  · exact B1774711
  · exact B1774715
  · exact B1774719
  · exact B1774723
  · exact B1774727
  · exact B1774731
  · exact B1774735
  · exact B1774739
  · exact B1774743
  · exact B1774747
  · exact B1774751
  · exact B1774755
  · exact B1774759
  · exact B1774763
  · exact B1774767
  · exact B1774771
  · exact B1774775
  · exact B1774779
  · exact B1774783
  · exact B1774787
  · exact B1774791
  · exact B1774795
  · exact B1774799
  · exact B1774803
  · exact B1774807
  · exact B1774811
  · exact B1774815
  · exact B1774819
  · exact B1774823
  · exact B1774827
  · exact B1774831
  · exact B1774835
  · exact B1774839
  · exact B1774843
  · exact B1774847
  · exact B1774851
  · exact B1774855
  · exact B1774859
  · exact B1774863
  · exact B1774867
  · exact B1774871
  · exact B1774875
  · exact B1774879
  · exact B1774883
  · exact B1774887
  · exact B1774891
  · exact B1774895
  · exact B1774899
  · exact B1774903
  · exact B1774907
  · exact B1774911
  · exact B1774915
  · exact B1774919
  · exact B1774923
  · exact B1774927
  · exact B1774931
  · exact B1774935
  · exact B1774939
  · exact B1774943
  · exact B1774947
  · exact B1774951
  · exact B1774955
  · exact B1774959
  · exact B1774963
  · exact B1774967
  · exact B1774971
  · exact B1774975
  · exact B1774979
  · exact B1774983
  · exact B1774987
  · exact B1774991
  · exact B1774995
  · exact B1774999
  · exact B1775003
  · exact B1775007
  · exact B1775011
  · exact B1775015
  · exact B1775019
  · exact B1775023
  · exact B1775027
  · exact B1775031
  · exact B1775035
  · exact B1775039
  · exact B1775043
  · exact B1775047
  · exact B1775051
  · exact B1775055
  · exact B1775059
  · exact B1775063
  · exact B1775067
  · exact B1775071
  · exact B1775075
  · exact B1775079
  · exact B1775083
  · exact B1775087
  · exact B1775091
  · exact B1775095
  · exact B1775099
  · exact B1775103
  · exact B1775107
  · exact B1775111
  · exact B1775115
  · exact B1775119
  · exact B1775123
  · exact B1775127
  · exact B1775131
  · exact B1775135
  · exact B1775139
  · exact B1775143
  · exact B1775147
  · exact B1775151
  · exact B1775155
  · exact B1775159
  · exact B1775163
  · exact B1775167
  · exact B1775171
  · exact B1775175
  · exact B1775179
  · exact B1775183
  · exact B1775187
  · exact B1775191
  · exact B1775195
  · exact B1775199
  · exact B1775203
  · exact B1775207
  · exact B1775211
  · exact B1775215
  · exact B1775219
  · exact B1775223
  · exact B1775227
  · exact B1775231
  · exact B1775235
  · exact B1775239
  · exact B1775243
  · exact B1775247
  · exact B1775251
  · exact B1775255
  · exact B1775259
  · exact B1775263
  · exact B1775267
  · exact B1775271
  · exact B1775275
  · exact B1775279
  · exact B1775283
  · exact B1775287
  · exact B1775291
  · exact B1775295
  · exact B1775299
  · exact B1775303
  · exact B1775307
  · exact B1775311
  · exact B1775315
  · exact B1775319
  · exact B1775323
  · exact B1775327
  · exact B1775331
  · exact B1775335
  · exact B1775339
  · exact B1775343
  · exact B1775347
  · exact B1775351
  · exact B1775355
  · exact B1775359
  · exact B1775363
  · exact B1775367
  · exact B1775371
  · exact B1775375
  · exact B1775379
  · exact B1775383
  · exact B1775387
  · exact B1775391
  · exact B1775395
  · exact B1775399
  · exact B1775403
  · exact B1775407
  · exact B1775411
  · exact B1775415
  · exact B1775419
  · exact B1775423
  · exact B1775427
  · exact B1775431
  · exact B1775435
  · exact B1775439
  · exact B1775443
  · exact B1775447
  · exact B1775451
  · exact B1775455
  · exact B1775459
  · exact B1775463
  · exact B1775467
  · exact B1775471
  · exact B1775475
  · exact B1775479
  · exact B1775483
  · exact B1775487
  · exact B1775491
  · exact B1775495
  · exact B1775499
  · exact B1775503
  · exact B1775507
  · exact B1775511
  · exact B1775515
  · exact B1775519
  · exact B1775523
  · exact B1775527
  · exact B1775531
  · exact B1775535
  · exact B1775539
  · exact B1775543
  · exact B1775547
  · exact B1775551
  · exact B1775555
  · exact B1775559
  · exact B1775563
  · exact B1775567
  · exact B1775571
  · exact B1775575
  · exact B1775579
  · exact B1775583
  · exact B1775587
  · exact B1775591
  · exact B1775595
  · exact B1775599
  · exact B1775603
  · exact B1775607
  · exact B1775611
  · exact B1775615
  · exact B1775619
  · exact B1775623
  · exact B1775627
  · exact B1775631
  · exact B1775635
  · exact B1775639
  · exact B1775643
  · exact B1775647
  · exact B1775651
  · exact B1775655
  · exact B1775659
  · exact B1775663
  · exact B1775667
  · exact B1775671
  · exact B1775675
  · exact B1775679
  · exact B1775683
  · exact B1775687
  · exact B1775691
  · exact B1775695
  · exact B1775699
  · exact B1775703
  · exact B1775707
  · exact B1775711
  · exact B1775715
  · exact B1775719
  · exact B1775723
  · exact B1775727
  · exact B1775731
  · exact B1775735
  · exact B1775739
  · exact B1775743
  · exact B1775747
  · exact B1775751
  · exact B1775755
  · exact B1775759
  · exact B1775763
  · exact B1775767
  · exact B1775771
  · exact B1775775
  · exact B1775779
  · exact B1775783
  · exact B1775787
  · exact B1775791
  · exact B1775795
  · exact B1775799
  · exact B1775803
  · exact B1775807
  · exact B1775811
  · exact B1775815
  · exact B1775819
  · exact B1775823
  · exact B1775827
  · exact B1775831
  · exact B1775835
  · exact B1775839
  · exact B1775843
  · exact B1775847
  · exact B1775851
  · exact B1775855
  · exact B1775859
  · exact B1775863
  · exact B1775867
  · exact B1775871
  · exact B1775875
  · exact B1775879
  · exact B1775883
  · exact B1775887
  · exact B1775891
  · exact B1775895
  · exact B1775899
  · exact B1775903
  · exact B1775907
  · exact B1775911
  · exact B1775915
  · exact B1775919
  · exact B1775923
  · exact B1775927
  · exact B1775931
  · exact B1775935
  · exact B1775939
  · exact B1775943
  · exact B1775947
  · exact B1775951
  · exact B1775955
  · exact B1775959
  · exact B1775963
  · exact B1775967
  · exact B1775971
  · exact B1775975
  · exact B1775979
  · exact B1775983
  · exact B1775987
  · exact B1775991
  · exact B1775995
  · exact B1775999
  · exact B1776003
  · exact B1776007
  · exact B1776011
  · exact B1776015
  · exact B1776019
  · exact B1776023
  · exact B1776027
  · exact B1776031
  · exact B1776035
  · exact B1776039
  · exact B1776043
  · exact B1776047
  · exact B1776051
  · exact B1776055
  · exact B1776059
  · exact B1776063
  · exact B1776067
  · exact B1776071
  · exact B1776075
  · exact B1776079
  · exact B1776083
  · exact B1776087

theorem solution (m : ℕ) (hlo : 1774088 ≤ m) (hhi : m ≤ 1776088) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 443522 ≤ j := by omega
    have hj2 : j ≤ 444021 := by omega
    have hb : Blo 1774088 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
