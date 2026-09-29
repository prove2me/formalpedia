-- Prove2me | solution 1 for syracuse_descends_range_1869636_1871636
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:13:34.485002+00:00
-- url     : https://prove2.me/submissions/7ee61cb7-6688-4533-8f2d-24437b1b6f74

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


theorem B2105365 : Blo 1869636 2105365 := bbase (se 6 (by rfl) ⟨49344, by rfl⟩ : syracuseStep 2105365 = 98689) (by norm_num)
theorem B2105401 : Blo 1869636 2105401 := bbase (se 2 (by rfl) ⟨789525, by rfl⟩ : syracuseStep 2105401 = 1579051) (by norm_num)
theorem B4735037 : Blo 1869636 4735037 := bbase (se 3 (by rfl) ⟨887819, by rfl⟩ : syracuseStep 4735037 = 1775639) (by norm_num)
theorem B4210757 : Blo 1869636 4210757 := bbase (se 4 (by rfl) ⟨394758, by rfl⟩ : syracuseStep 4210757 = 789517) (by norm_num)
theorem B2367569 : Blo 1869636 2367569 := bbase (se 2 (by rfl) ⟨887838, by rfl⟩ : syracuseStep 2367569 = 1775677) (by norm_num)
theorem B4268117 : Blo 1869636 4268117 := bbase (se 8 (by rfl) ⟨25008, by rfl⟩ : syracuseStep 4268117 = 50017) (by norm_num)
theorem B2105437 : Blo 1869636 2105437 := bbase (se 3 (by rfl) ⟨394769, by rfl⟩ : syracuseStep 2105437 = 789539) (by norm_num)
theorem B2105473 : Blo 1869636 2105473 := bbase (se 2 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 2105473 = 1579105) (by norm_num)
theorem B2367625 : Blo 1869636 2367625 := bbase (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) (by norm_num)
theorem B4210829 : Blo 1869636 4210829 := bbase (se 3 (by rfl) ⟨789530, by rfl⟩ : syracuseStep 4210829 = 1579061) (by norm_num)
theorem B2105509 : Blo 1869636 2105509 := bbase (se 4 (by rfl) ⟨197391, by rfl⟩ : syracuseStep 2105509 = 394783) (by norm_num)
theorem B2105545 : Blo 1869636 2105545 := bbase (se 2 (by rfl) ⟨789579, by rfl⟩ : syracuseStep 2105545 = 1579159) (by norm_num)
theorem B5398741 : Blo 1869636 5398741 := bbase (se 7 (by rfl) ⟨63266, by rfl⟩ : syracuseStep 5398741 = 126533) (by norm_num)
theorem B4210901 : Blo 1869636 4210901 := bbase (se 7 (by rfl) ⟨49346, by rfl⟩ : syracuseStep 4210901 = 98693) (by norm_num)
theorem B2367721 : Blo 1869636 2367721 := bbase (se 2 (by rfl) ⟨887895, by rfl⟩ : syracuseStep 2367721 = 1775791) (by norm_num)
theorem B2105581 : Blo 1869636 2105581 := bbase (se 3 (by rfl) ⟨394796, by rfl⟩ : syracuseStep 2105581 = 789593) (by norm_num)
theorem B5325061 : Blo 1869636 5325061 := bbase (se 4 (by rfl) ⟨499224, by rfl⟩ : syracuseStep 5325061 = 998449) (by norm_num)
theorem B14401813 : Blo 1869636 14401813 := bbase (se 6 (by rfl) ⟨337542, by rfl⟩ : syracuseStep 14401813 = 675085) (by norm_num)
theorem B4210973 : Blo 1869636 4210973 := bbase (se 3 (by rfl) ⟨789557, by rfl⟩ : syracuseStep 4210973 = 1579115) (by norm_num)
theorem B6832421 : Blo 1869636 6832421 := bbase (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) (by norm_num)
theorem B6316325 : Blo 1869636 6316325 := bbase (se 4 (by rfl) ⟨592155, by rfl⟩ : syracuseStep 6316325 = 1184311) (by norm_num)
theorem B11985205 : Blo 1869636 11985205 := bbase (se 5 (by rfl) ⟨561806, by rfl⟩ : syracuseStep 11985205 = 1123613) (by norm_num)
theorem B15171893 : Blo 1869636 15171893 := bbase (se 5 (by rfl) ⟨711182, by rfl⟩ : syracuseStep 15171893 = 1422365) (by norm_num)
theorem B2662741 : Blo 1869636 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B4211045 : Blo 1869636 4211045 := bbase (se 4 (by rfl) ⟨394785, by rfl⟩ : syracuseStep 4211045 = 789571) (by norm_num)
theorem B9470357 : Blo 1869636 9470357 := bbase (se 6 (by rfl) ⟨221961, by rfl⟩ : syracuseStep 9470357 = 443923) (by norm_num)
theorem B4735381 : Blo 1869636 4735381 := bbase (se 6 (by rfl) ⟨110985, by rfl⟩ : syracuseStep 4735381 = 221971) (by norm_num)
theorem B2367893 : Blo 1869636 2367893 := bbase (se 6 (by rfl) ⟨55497, by rfl⟩ : syracuseStep 2367893 = 110995) (by norm_num)
theorem B4211117 : Blo 1869636 4211117 := bbase (se 3 (by rfl) ⟨789584, by rfl⟩ : syracuseStep 4211117 = 1579169) (by norm_num)
theorem B2277829 : Blo 1869636 2277829 := bbase (se 4 (by rfl) ⟨213546, by rfl⟩ : syracuseStep 2277829 = 427093) (by norm_num)
theorem B2367949 : Blo 1869636 2367949 := bbase (se 3 (by rfl) ⟨443990, by rfl⟩ : syracuseStep 2367949 = 887981) (by norm_num)
theorem B2466289 : Blo 1869636 2466289 := bbase (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) (by norm_num)
theorem B4735493 : Blo 1869636 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B7102997 : Blo 1869636 7102997 := bbase (se 6 (by rfl) ⟨166476, by rfl⟩ : syracuseStep 7102997 = 332953) (by norm_num)
theorem B25960981 : Blo 1869636 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B2368045 : Blo 1869636 2368045 := bbase (se 3 (by rfl) ⟨444008, by rfl⟩ : syracuseStep 2368045 = 888017) (by norm_num)
theorem B2277985 : Blo 1869636 2277985 := bbase (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) (by norm_num)
theorem B4735685 : Blo 1869636 4735685 := bbase (se 4 (by rfl) ⟨443970, by rfl⟩ : syracuseStep 4735685 = 887941) (by norm_num)
theorem B10650325 : Blo 1869636 10650325 := bbase (se 7 (by rfl) ⟨124808, by rfl⟩ : syracuseStep 10650325 = 249617) (by norm_num)
theorem B6316757 : Blo 1869636 6316757 := bbase (se 7 (by rfl) ⟨74024, by rfl⟩ : syracuseStep 6316757 = 148049) (by norm_num)
theorem B2368217 : Blo 1869636 2368217 := bbase (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) (by norm_num)
theorem B2368273 : Blo 1869636 2368273 := bbase (se 2 (by rfl) ⟨888102, by rfl⟩ : syracuseStep 2368273 = 1776205) (by norm_num)
theorem B7103285 : Blo 1869636 7103285 := bbase (se 5 (by rfl) ⟨332966, by rfl⟩ : syracuseStep 7103285 = 665933) (by norm_num)
theorem B207496021 : Blo 1869636 207496021 := bbase (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) (by norm_num)
theorem B2368369 : Blo 1869636 2368369 := bbase (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) (by norm_num)
theorem B2597765 : Blo 1869636 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B4932485 : Blo 1869636 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B14599061 : Blo 1869636 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B2532269 : Blo 1869636 2532269 := bbase (se 3 (by rfl) ⟨474800, by rfl⟩ : syracuseStep 2532269 = 949601) (by norm_num)
theorem B4736029 : Blo 1869636 4736029 := bbase (se 3 (by rfl) ⟨888005, by rfl⟩ : syracuseStep 4736029 = 1776011) (by norm_num)
theorem B2368541 : Blo 1869636 2368541 := bbase (se 3 (by rfl) ⟨444101, by rfl⟩ : syracuseStep 2368541 = 888203) (by norm_num)
theorem B4047941 : Blo 1869636 4047941 := bbase (se 4 (by rfl) ⟨379494, by rfl⟩ : syracuseStep 4047941 = 758989) (by norm_num)
theorem B2368597 : Blo 1869636 2368597 := bbase (se 8 (by rfl) ⟨13878, by rfl⟩ : syracuseStep 2368597 = 27757) (by norm_num)
theorem B2663533 : Blo 1869636 2663533 := bbase (se 3 (by rfl) ⟨499412, by rfl⟩ : syracuseStep 2663533 = 998825) (by norm_num)
theorem B4736141 : Blo 1869636 4736141 := bbase (se 3 (by rfl) ⟨888026, by rfl⟩ : syracuseStep 4736141 = 1776053) (by norm_num)
theorem B13477013 : Blo 1869636 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B3155125 : Blo 1869636 3155125 := bbase (se 5 (by rfl) ⟨147896, by rfl⟩ : syracuseStep 3155125 = 295793) (by norm_num)
theorem B2368693 : Blo 1869636 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B5686517 : Blo 1869636 5686517 := bbase (se 5 (by rfl) ⟨266555, by rfl⟩ : syracuseStep 5686517 = 533111) (by norm_num)
theorem B3155213 : Blo 1869636 3155213 := bbase (se 3 (by rfl) ⟨591602, by rfl⟩ : syracuseStep 3155213 = 1183205) (by norm_num)
theorem B4736333 : Blo 1869636 4736333 := bbase (se 3 (by rfl) ⟨888062, by rfl⟩ : syracuseStep 4736333 = 1776125) (by norm_num)
theorem B5326165 : Blo 1869636 5326165 := bbase (se 12 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 5326165 = 3901) (by norm_num)
theorem B5989733 : Blo 1869636 5989733 := bbase (se 4 (by rfl) ⟨561537, by rfl⟩ : syracuseStep 5989733 = 1123075) (by norm_num)
theorem B3155341 : Blo 1869636 3155341 := bbase (se 3 (by rfl) ⟨591626, by rfl⟩ : syracuseStep 3155341 = 1183253) (by norm_num)
theorem B2024885 : Blo 1869636 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B2663869 : Blo 1869636 2663869 := bbase (se 3 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 2663869 = 998951) (by norm_num)
theorem B3155429 : Blo 1869636 3155429 := bbase (se 4 (by rfl) ⟨295821, by rfl⟩ : syracuseStep 3155429 = 591643) (by norm_num)
theorem B4802125 : Blo 1869636 4802125 := bbase (se 3 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 4802125 = 1800797) (by norm_num)
theorem B3155557 : Blo 1869636 3155557 := bbase (se 4 (by rfl) ⟨295833, by rfl⟩ : syracuseStep 3155557 = 591667) (by norm_num)
theorem B2664085 : Blo 1869636 2664085 := bbase (se 6 (by rfl) ⟨62439, by rfl⟩ : syracuseStep 2664085 = 124879) (by norm_num)
theorem B9471653 : Blo 1869636 9471653 := bbase (se 4 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 9471653 = 1775935) (by norm_num)
theorem B4736677 : Blo 1869636 4736677 := bbase (se 4 (by rfl) ⟨444063, by rfl⟩ : syracuseStep 4736677 = 888127) (by norm_num)
theorem B3155645 : Blo 1869636 3155645 := bbase (se 3 (by rfl) ⟨591683, by rfl⟩ : syracuseStep 3155645 = 1183367) (by norm_num)
theorem B4736789 : Blo 1869636 4736789 := bbase (se 6 (by rfl) ⟨111018, by rfl⟩ : syracuseStep 4736789 = 222037) (by norm_num)
theorem B3155773 : Blo 1869636 3155773 := bbase (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) (by norm_num)
theorem B15976277 : Blo 1869636 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B3155861 : Blo 1869636 3155861 := bbase (se 6 (by rfl) ⟨73965, by rfl⟩ : syracuseStep 3155861 = 147931) (by norm_num)
theorem B2246573 : Blo 1869636 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B7104469 : Blo 1869636 7104469 := bbase (se 7 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 7104469 = 166511) (by norm_num)
theorem B4736981 : Blo 1869636 4736981 := bbase (se 7 (by rfl) ⟨55511, by rfl⟩ : syracuseStep 4736981 = 111023) (by norm_num)
theorem B2664461 : Blo 1869636 2664461 := bbase (se 3 (by rfl) ⟨499586, by rfl⟩ : syracuseStep 2664461 = 999173) (by norm_num)
theorem B3155989 : Blo 1869636 3155989 := bbase (se 6 (by rfl) ⟨73968, by rfl⟩ : syracuseStep 3155989 = 147937) (by norm_num)
theorem B6490165 : Blo 1869636 6490165 := bbase (se 5 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 6490165 = 608453) (by norm_num)
theorem B2025533 : Blo 1869636 2025533 := bbase (se 3 (by rfl) ⟨379787, by rfl⟩ : syracuseStep 2025533 = 759575) (by norm_num)
theorem B7989317 : Blo 1869636 7989317 := bbase (se 4 (by rfl) ⟨748998, by rfl⟩ : syracuseStep 7989317 = 1497997) (by norm_num)
theorem B3844181 : Blo 1869636 3844181 := bbase (se 8 (by rfl) ⟨22524, by rfl⟩ : syracuseStep 3844181 = 45049) (by norm_num)
theorem B3156077 : Blo 1869636 3156077 := bbase (se 3 (by rfl) ⟨591764, by rfl⟩ : syracuseStep 3156077 = 1183529) (by norm_num)
theorem B2844877 : Blo 1869636 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B2246881 : Blo 1869636 2246881 := bbase (se 2 (by rfl) ⟨842580, by rfl⟩ : syracuseStep 2246881 = 1685161) (by norm_num)
theorem B3156205 : Blo 1869636 3156205 := bbase (se 3 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 3156205 = 1183577) (by norm_num)
theorem B7588085 : Blo 1869636 7588085 := bbase (se 5 (by rfl) ⟨355691, by rfl⟩ : syracuseStep 7588085 = 711383) (by norm_num)
theorem B7104773 : Blo 1869636 7104773 := bbase (se 4 (by rfl) ⟨666072, by rfl⟩ : syracuseStep 7104773 = 1332145) (by norm_num)
theorem B8988965 : Blo 1869636 8988965 := bbase (se 4 (by rfl) ⟨842715, by rfl⟩ : syracuseStep 8988965 = 1685431) (by norm_num)
theorem B4737325 : Blo 1869636 4737325 := bbase (se 3 (by rfl) ⟨888248, by rfl⟩ : syracuseStep 4737325 = 1776497) (by norm_num)
theorem B3156293 : Blo 1869636 3156293 := bbase (se 4 (by rfl) ⟨295902, by rfl⟩ : syracuseStep 3156293 = 591805) (by norm_num)
theorem B6310277 : Blo 1869636 6310277 := bbase (se 4 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 6310277 = 1183177) (by norm_num)
theorem B2247049 : Blo 1869636 2247049 := bbase (se 2 (by rfl) ⟨842643, by rfl⟩ : syracuseStep 2247049 = 1685287) (by norm_num)
theorem B4737437 : Blo 1869636 4737437 := bbase (se 3 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 4737437 = 1776539) (by norm_num)
theorem B11372981 : Blo 1869636 11372981 := bbase (se 5 (by rfl) ⟨533108, by rfl⟩ : syracuseStep 11372981 = 1066217) (by norm_num)
theorem B3156421 : Blo 1869636 3156421 := bbase (se 4 (by rfl) ⟨295914, by rfl⟩ : syracuseStep 3156421 = 591829) (by norm_num)
theorem B3549653 : Blo 1869636 3549653 := bbase (se 7 (by rfl) ⟨41597, by rfl⟩ : syracuseStep 3549653 = 83195) (by norm_num)
theorem B3156509 : Blo 1869636 3156509 := bbase (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) (by norm_num)
theorem B2247245 : Blo 1869636 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B5991013 : Blo 1869636 5991013 := bbase (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) (by norm_num)
theorem B10652309 : Blo 1869636 10652309 := bbase (se 6 (by rfl) ⟨249663, by rfl⟩ : syracuseStep 10652309 = 499327) (by norm_num)
theorem B3156637 : Blo 1869636 3156637 := bbase (se 3 (by rfl) ⟨591869, by rfl⟩ : syracuseStep 3156637 = 1183739) (by norm_num)
theorem B3156725 : Blo 1869636 3156725 := bbase (se 5 (by rfl) ⟨147971, by rfl⟩ : syracuseStep 3156725 = 295943) (by norm_num)
theorem B2804477 : Blo 1869636 2804477 := bbase (se 3 (by rfl) ⟨525839, by rfl⟩ : syracuseStep 2804477 = 1051679) (by norm_num)
theorem B2804501 : Blo 1869636 2804501 := bbase (se 6 (by rfl) ⟨65730, by rfl⟩ : syracuseStep 2804501 = 131461) (by norm_num)
theorem B2804525 : Blo 1869636 2804525 := bbase (se 3 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 2804525 = 1051697) (by norm_num)
theorem B6310709 : Blo 1869636 6310709 := bbase (se 5 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 6310709 = 591629) (by norm_num)
theorem B5327669 : Blo 1869636 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B2804549 : Blo 1869636 2804549 := bbase (se 4 (by rfl) ⟨262926, by rfl⟩ : syracuseStep 2804549 = 525853) (by norm_num)
theorem B2804573 : Blo 1869636 2804573 := bbase (se 3 (by rfl) ⟨525857, by rfl⟩ : syracuseStep 2804573 = 1051715) (by norm_num)
theorem B2804597 : Blo 1869636 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B3156853 : Blo 1869636 3156853 := bbase (se 5 (by rfl) ⟨147977, by rfl⟩ : syracuseStep 3156853 = 295955) (by norm_num)
theorem B2804621 : Blo 1869636 2804621 := bbase (se 3 (by rfl) ⟨525866, by rfl⟩ : syracuseStep 2804621 = 1051733) (by norm_num)
theorem B2804645 : Blo 1869636 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B4492205 : Blo 1869636 4492205 := bbase (se 3 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 4492205 = 1684577) (by norm_num)
theorem B9472949 : Blo 1869636 9472949 := bbase (se 5 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 9472949 = 888089) (by norm_num)
theorem B2804669 : Blo 1869636 2804669 := bbase (se 3 (by rfl) ⟨525875, by rfl⟩ : syracuseStep 2804669 = 1051751) (by norm_num)
theorem B3156941 : Blo 1869636 3156941 := bbase (se 3 (by rfl) ⟨591926, by rfl⟩ : syracuseStep 3156941 = 1183853) (by norm_num)
theorem B2804693 : Blo 1869636 2804693 := bbase (se 7 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 2804693 = 65735) (by norm_num)
theorem B4492253 : Blo 1869636 4492253 := bbase (se 3 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 4492253 = 1684595) (by norm_num)
theorem B2804717 : Blo 1869636 2804717 := bbase (se 3 (by rfl) ⟨525884, by rfl⟩ : syracuseStep 2804717 = 1051769) (by norm_num)
theorem B2804741 : Blo 1869636 2804741 := bbase (se 4 (by rfl) ⟨262944, by rfl⟩ : syracuseStep 2804741 = 525889) (by norm_num)
theorem B2804765 : Blo 1869636 2804765 := bbase (se 3 (by rfl) ⟨525893, by rfl⟩ : syracuseStep 2804765 = 1051787) (by norm_num)
theorem B2804789 : Blo 1869636 2804789 := bbase (se 5 (by rfl) ⟨131474, by rfl⟩ : syracuseStep 2804789 = 262949) (by norm_num)
theorem B2804813 : Blo 1869636 2804813 := bbase (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) (by norm_num)
theorem B3370061 : Blo 1869636 3370061 := bbase (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) (by norm_num)
theorem B3157069 : Blo 1869636 3157069 := bbase (se 3 (by rfl) ⟨591950, by rfl⟩ : syracuseStep 3157069 = 1183901) (by norm_num)
theorem B2804837 : Blo 1869636 2804837 := bbase (se 4 (by rfl) ⟨262953, by rfl⟩ : syracuseStep 2804837 = 525907) (by norm_num)
theorem B2133101 : Blo 1869636 2133101 := bbase (se 3 (by rfl) ⟨399956, by rfl⟩ : syracuseStep 2133101 = 799913) (by norm_num)
theorem B2804861 : Blo 1869636 2804861 := bbase (se 3 (by rfl) ⟨525911, by rfl⟩ : syracuseStep 2804861 = 1051823) (by norm_num)
theorem B2804885 : Blo 1869636 2804885 := bbase (se 6 (by rfl) ⟨65739, by rfl⟩ : syracuseStep 2804885 = 131479) (by norm_num)
theorem B3370133 : Blo 1869636 3370133 := bbase (se 6 (by rfl) ⟨78987, by rfl⟩ : syracuseStep 3370133 = 157975) (by norm_num)
theorem B3157157 : Blo 1869636 3157157 := bbase (se 4 (by rfl) ⟨295983, by rfl⟩ : syracuseStep 3157157 = 591967) (by norm_num)
theorem B2804909 : Blo 1869636 2804909 := bbase (se 3 (by rfl) ⟨525920, by rfl⟩ : syracuseStep 2804909 = 1051841) (by norm_num)
theorem B2804933 : Blo 1869636 2804933 := bbase (se 4 (by rfl) ⟨262962, by rfl⟩ : syracuseStep 2804933 = 525925) (by norm_num)
theorem B3550405 : Blo 1869636 3550405 := bbase (se 4 (by rfl) ⟨332850, by rfl⟩ : syracuseStep 3550405 = 665701) (by norm_num)
theorem B40438997 : Blo 1869636 40438997 := bbase (se 7 (by rfl) ⟨473894, by rfl⟩ : syracuseStep 40438997 = 947789) (by norm_num)
theorem B2804957 : Blo 1869636 2804957 := bbase (se 3 (by rfl) ⟨525929, by rfl⟩ : syracuseStep 2804957 = 1051859) (by norm_num)
theorem B6311141 : Blo 1869636 6311141 := bbase (se 4 (by rfl) ⟨591669, by rfl⟩ : syracuseStep 6311141 = 1183339) (by norm_num)
theorem B2804981 : Blo 1869636 2804981 := bbase (se 5 (by rfl) ⟨131483, by rfl⟩ : syracuseStep 2804981 = 262967) (by norm_num)
theorem B2805005 : Blo 1869636 2805005 := bbase (se 3 (by rfl) ⟨525938, by rfl⟩ : syracuseStep 2805005 = 1051877) (by norm_num)
theorem B2805029 : Blo 1869636 2805029 := bbase (se 4 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 2805029 = 525943) (by norm_num)
theorem B8531237 : Blo 1869636 8531237 := bbase (se 4 (by rfl) ⟨799803, by rfl⟩ : syracuseStep 8531237 = 1599607) (by norm_num)
theorem B3157285 : Blo 1869636 3157285 := bbase (se 4 (by rfl) ⟨295995, by rfl⟩ : syracuseStep 3157285 = 591991) (by norm_num)
theorem B2805053 : Blo 1869636 2805053 := bbase (se 3 (by rfl) ⟨525947, by rfl⟩ : syracuseStep 2805053 = 1051895) (by norm_num)
theorem B9465173 : Blo 1869636 9465173 := bbase (se 11 (by rfl) ⟨6932, by rfl⟩ : syracuseStep 9465173 = 13865) (by norm_num)
theorem B2805077 : Blo 1869636 2805077 := bbase (se 11 (by rfl) ⟨2054, by rfl⟩ : syracuseStep 2805077 = 4109) (by norm_num)
theorem B3550549 : Blo 1869636 3550549 := bbase (se 11 (by rfl) ⟨2600, by rfl⟩ : syracuseStep 3550549 = 5201) (by norm_num)
theorem B2805101 : Blo 1869636 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B1895789 : Blo 1869636 1895789 := bbase (se 3 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 1895789 = 710921) (by norm_num)
theorem B3157373 : Blo 1869636 3157373 := bbase (se 3 (by rfl) ⟨592007, by rfl⟩ : syracuseStep 3157373 = 1184015) (by norm_num)
theorem B2805125 : Blo 1869636 2805125 := bbase (se 4 (by rfl) ⟨262980, by rfl⟩ : syracuseStep 2805125 = 525961) (by norm_num)
theorem B2805149 : Blo 1869636 2805149 := bbase (se 3 (by rfl) ⟨525965, by rfl⟩ : syracuseStep 2805149 = 1051931) (by norm_num)
theorem B2805173 : Blo 1869636 2805173 := bbase (se 5 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 2805173 = 262985) (by norm_num)
theorem B2805197 : Blo 1869636 2805197 := bbase (se 3 (by rfl) ⟨525974, by rfl⟩ : syracuseStep 2805197 = 1051949) (by norm_num)
theorem B4050389 : Blo 1869636 4050389 := bbase (se 7 (by rfl) ⟨47465, by rfl⟩ : syracuseStep 4050389 = 94931) (by norm_num)
theorem B2805221 : Blo 1869636 2805221 := bbase (se 4 (by rfl) ⟨262989, by rfl⟩ : syracuseStep 2805221 = 525979) (by norm_num)
theorem B3550709 : Blo 1869636 3550709 := bbase (se 5 (by rfl) ⟨166439, by rfl⟩ : syracuseStep 3550709 = 332879) (by norm_num)
theorem B2805245 : Blo 1869636 2805245 := bbase (se 3 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 2805245 = 1051967) (by norm_num)
theorem B3157501 : Blo 1869636 3157501 := bbase (se 3 (by rfl) ⟨592031, by rfl⟩ : syracuseStep 3157501 = 1184063) (by norm_num)
theorem B2805269 : Blo 1869636 2805269 := bbase (se 6 (by rfl) ⟨65748, by rfl⟩ : syracuseStep 2805269 = 131497) (by norm_num)
theorem B8097317 : Blo 1869636 8097317 := bbase (se 4 (by rfl) ⟨759123, by rfl⟩ : syracuseStep 8097317 = 1518247) (by norm_num)
theorem B2805293 : Blo 1869636 2805293 := bbase (se 3 (by rfl) ⟨525992, by rfl⟩ : syracuseStep 2805293 = 1051985) (by norm_num)
theorem B2805317 : Blo 1869636 2805317 := bbase (se 4 (by rfl) ⟨262998, by rfl⟩ : syracuseStep 2805317 = 525997) (by norm_num)
theorem B3157589 : Blo 1869636 3157589 := bbase (se 8 (by rfl) ⟨18501, by rfl⟩ : syracuseStep 3157589 = 37003) (by norm_num)
theorem B2805341 : Blo 1869636 2805341 := bbase (se 3 (by rfl) ⟨526001, by rfl⟩ : syracuseStep 2805341 = 1052003) (by norm_num)
theorem B2805365 : Blo 1869636 2805365 := bbase (se 5 (by rfl) ⟨131501, by rfl⟩ : syracuseStep 2805365 = 263003) (by norm_num)
theorem B3649141 : Blo 1869636 3649141 := bbase (se 5 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 3649141 = 342107) (by norm_num)
theorem B3550853 : Blo 1869636 3550853 := bbase (se 4 (by rfl) ⟨332892, by rfl⟩ : syracuseStep 3550853 = 665785) (by norm_num)
theorem B2805389 : Blo 1869636 2805389 := bbase (se 3 (by rfl) ⟨526010, by rfl⟩ : syracuseStep 2805389 = 1052021) (by norm_num)
theorem B3370637 : Blo 1869636 3370637 := bbase (se 3 (by rfl) ⟨631994, by rfl⟩ : syracuseStep 3370637 = 1263989) (by norm_num)
theorem B6311573 : Blo 1869636 6311573 := bbase (se 6 (by rfl) ⟨147927, by rfl⟩ : syracuseStep 6311573 = 295855) (by norm_num)
theorem B2805413 : Blo 1869636 2805413 := bbase (se 4 (by rfl) ⟨263007, by rfl⟩ : syracuseStep 2805413 = 526015) (by norm_num)
theorem B2805437 : Blo 1869636 2805437 := bbase (se 3 (by rfl) ⟨526019, by rfl⟩ : syracuseStep 2805437 = 1052039) (by norm_num)
theorem B2805461 : Blo 1869636 2805461 := bbase (se 7 (by rfl) ⟨32876, by rfl⟩ : syracuseStep 2805461 = 65753) (by norm_num)
theorem B3157717 : Blo 1869636 3157717 := bbase (se 7 (by rfl) ⟨37004, by rfl⟩ : syracuseStep 3157717 = 74009) (by norm_num)
theorem B2805485 : Blo 1869636 2805485 := bbase (se 3 (by rfl) ⟨526028, by rfl⟩ : syracuseStep 2805485 = 1052057) (by norm_num)
theorem B2805509 : Blo 1869636 2805509 := bbase (se 4 (by rfl) ⟨263016, by rfl⟩ : syracuseStep 2805509 = 526033) (by norm_num)
theorem B2805533 : Blo 1869636 2805533 := bbase (se 3 (by rfl) ⟨526037, by rfl⟩ : syracuseStep 2805533 = 1052075) (by norm_num)
theorem B3157805 : Blo 1869636 3157805 := bbase (se 3 (by rfl) ⟨592088, by rfl⟩ : syracuseStep 3157805 = 1184177) (by norm_num)
theorem B2805557 : Blo 1869636 2805557 := bbase (se 5 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 2805557 = 263021) (by norm_num)
theorem B2805581 : Blo 1869636 2805581 := bbase (se 3 (by rfl) ⟨526046, by rfl⟩ : syracuseStep 2805581 = 1052093) (by norm_num)
theorem B2805605 : Blo 1869636 2805605 := bbase (se 4 (by rfl) ⟨263025, by rfl⟩ : syracuseStep 2805605 = 526051) (by norm_num)
theorem B5689205 : Blo 1869636 5689205 := bbase (se 5 (by rfl) ⟨266681, by rfl⟩ : syracuseStep 5689205 = 533363) (by norm_num)
theorem B2805629 : Blo 1869636 2805629 := bbase (se 3 (by rfl) ⟨526055, by rfl⟩ : syracuseStep 2805629 = 1052111) (by norm_num)
theorem B2805653 : Blo 1869636 2805653 := bbase (se 6 (by rfl) ⟨65757, by rfl⟩ : syracuseStep 2805653 = 131515) (by norm_num)
theorem B3551141 : Blo 1869636 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B2805677 : Blo 1869636 2805677 := bbase (se 3 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 2805677 = 1052129) (by norm_num)
theorem B3157933 : Blo 1869636 3157933 := bbase (se 3 (by rfl) ⟨592112, by rfl⟩ : syracuseStep 3157933 = 1184225) (by norm_num)
theorem B5992373 : Blo 1869636 5992373 := bbase (se 5 (by rfl) ⟨280892, by rfl⟩ : syracuseStep 5992373 = 561785) (by norm_num)
theorem B2805701 : Blo 1869636 2805701 := bbase (se 4 (by rfl) ⟨263034, by rfl⟩ : syracuseStep 2805701 = 526069) (by norm_num)
theorem B3993565 : Blo 1869636 3993565 := bbase (se 3 (by rfl) ⟨748793, by rfl⟩ : syracuseStep 3993565 = 1497587) (by norm_num)
theorem B2805725 : Blo 1869636 2805725 := bbase (se 3 (by rfl) ⟨526073, by rfl⟩ : syracuseStep 2805725 = 1052147) (by norm_num)
theorem B2805749 : Blo 1869636 2805749 := bbase (se 5 (by rfl) ⟨131519, by rfl⟩ : syracuseStep 2805749 = 263039) (by norm_num)
theorem B3158021 : Blo 1869636 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B2805773 : Blo 1869636 2805773 := bbase (se 3 (by rfl) ⟨526082, by rfl⟩ : syracuseStep 2805773 = 1052165) (by norm_num)
theorem B2805797 : Blo 1869636 2805797 := bbase (se 4 (by rfl) ⟨263043, by rfl⟩ : syracuseStep 2805797 = 526087) (by norm_num)
theorem B5992501 : Blo 1869636 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B2805821 : Blo 1869636 2805821 := bbase (se 3 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 2805821 = 1052183) (by norm_num)
theorem B3551293 : Blo 1869636 3551293 := bbase (se 3 (by rfl) ⟨665867, by rfl⟩ : syracuseStep 3551293 = 1331735) (by norm_num)
theorem B6312005 : Blo 1869636 6312005 := bbase (se 4 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 6312005 = 1183501) (by norm_num)
theorem B2805845 : Blo 1869636 2805845 := bbase (se 8 (by rfl) ⟨16440, by rfl⟩ : syracuseStep 2805845 = 32881) (by norm_num)
theorem B2805869 : Blo 1869636 2805869 := bbase (se 3 (by rfl) ⟨526100, by rfl⟩ : syracuseStep 2805869 = 1052201) (by norm_num)
theorem B4206725 : Blo 1869636 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B2805893 : Blo 1869636 2805893 := bbase (se 4 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 2805893 = 526105) (by norm_num)
theorem B3158149 : Blo 1869636 3158149 := bbase (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) (by norm_num)
theorem B2805917 : Blo 1869636 2805917 := bbase (se 3 (by rfl) ⟨526109, by rfl⟩ : syracuseStep 2805917 = 1052219) (by norm_num)
theorem B2805941 : Blo 1869636 2805941 := bbase (se 5 (by rfl) ⟨131528, by rfl⟩ : syracuseStep 2805941 = 263057) (by norm_num)
theorem B1896629 : Blo 1869636 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B9474245 : Blo 1869636 9474245 := bbase (se 4 (by rfl) ⟨888210, by rfl⟩ : syracuseStep 9474245 = 1776421) (by norm_num)
theorem B4206797 : Blo 1869636 4206797 := bbase (se 3 (by rfl) ⟨788774, by rfl⟩ : syracuseStep 4206797 = 1577549) (by norm_num)
theorem B2805965 : Blo 1869636 2805965 := bbase (se 3 (by rfl) ⟨526118, by rfl⟩ : syracuseStep 2805965 = 1052237) (by norm_num)
theorem B1896661 : Blo 1869636 1896661 := bbase (se 7 (by rfl) ⟨22226, by rfl⟩ : syracuseStep 1896661 = 44453) (by norm_num)
theorem B4264157 : Blo 1869636 4264157 := bbase (se 3 (by rfl) ⟨799529, by rfl⟩ : syracuseStep 4264157 = 1599059) (by norm_num)
theorem B3158237 : Blo 1869636 3158237 := bbase (se 3 (by rfl) ⟨592169, by rfl⟩ : syracuseStep 3158237 = 1184339) (by norm_num)
theorem B2805989 : Blo 1869636 2805989 := bbase (se 4 (by rfl) ⟨263061, by rfl⟩ : syracuseStep 2805989 = 526123) (by norm_num)
theorem B2806013 : Blo 1869636 2806013 := bbase (se 3 (by rfl) ⟨526127, by rfl⟩ : syracuseStep 2806013 = 1052255) (by norm_num)
theorem B4206869 : Blo 1869636 4206869 := bbase (se 6 (by rfl) ⟨98598, by rfl⟩ : syracuseStep 4206869 = 197197) (by norm_num)
theorem B2806037 : Blo 1869636 2806037 := bbase (se 6 (by rfl) ⟨65766, by rfl⟩ : syracuseStep 2806037 = 131533) (by norm_num)
theorem B2806061 : Blo 1869636 2806061 := bbase (se 3 (by rfl) ⟨526136, by rfl⟩ : syracuseStep 2806061 = 1052273) (by norm_num)
theorem B5992757 : Blo 1869636 5992757 := bbase (se 5 (by rfl) ⟨280910, by rfl⟩ : syracuseStep 5992757 = 561821) (by norm_num)
theorem B2806085 : Blo 1869636 2806085 := bbase (se 4 (by rfl) ⟨263070, by rfl⟩ : syracuseStep 2806085 = 526141) (by norm_num)
theorem B4493645 : Blo 1869636 4493645 := bbase (se 3 (by rfl) ⟨842558, by rfl⟩ : syracuseStep 4493645 = 1685117) (by norm_num)
theorem B3993941 : Blo 1869636 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B4206941 : Blo 1869636 4206941 := bbase (se 3 (by rfl) ⟨788801, by rfl⟩ : syracuseStep 4206941 = 1577603) (by norm_num)
theorem B2806109 : Blo 1869636 2806109 := bbase (se 3 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 2806109 = 1052291) (by norm_num)
theorem B3158365 : Blo 1869636 3158365 := bbase (se 3 (by rfl) ⟨592193, by rfl⟩ : syracuseStep 3158365 = 1184387) (by norm_num)
theorem B5329253 : Blo 1869636 5329253 := bbase (se 4 (by rfl) ⟨499617, by rfl⟩ : syracuseStep 5329253 = 999235) (by norm_num)
theorem B3551597 : Blo 1869636 3551597 := bbase (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) (by norm_num)
theorem B2806133 : Blo 1869636 2806133 := bbase (se 5 (by rfl) ⟨131537, by rfl⟩ : syracuseStep 2806133 = 263075) (by norm_num)
theorem B2806157 : Blo 1869636 2806157 := bbase (se 3 (by rfl) ⟨526154, by rfl⟩ : syracuseStep 2806157 = 1052309) (by norm_num)
theorem B34132373 : Blo 1869636 34132373 := bbase (se 6 (by rfl) ⟨799977, by rfl⟩ : syracuseStep 34132373 = 1599955) (by norm_num)
theorem B4207013 : Blo 1869636 4207013 := bbase (se 4 (by rfl) ⟨394407, by rfl⟩ : syracuseStep 4207013 = 788815) (by norm_num)
theorem B2806181 : Blo 1869636 2806181 := bbase (se 4 (by rfl) ⟨263079, by rfl⟩ : syracuseStep 2806181 = 526159) (by norm_num)
theorem B2806205 : Blo 1869636 2806205 := bbase (se 3 (by rfl) ⟨526163, by rfl⟩ : syracuseStep 2806205 = 1052327) (by norm_num)
theorem B2806229 : Blo 1869636 2806229 := bbase (se 7 (by rfl) ⟨32885, by rfl⟩ : syracuseStep 2806229 = 65771) (by norm_num)
theorem B4207085 : Blo 1869636 4207085 := bbase (se 3 (by rfl) ⟨788828, by rfl⟩ : syracuseStep 4207085 = 1577657) (by norm_num)
theorem B2806253 : Blo 1869636 2806253 := bbase (se 3 (by rfl) ⟨526172, by rfl⟩ : syracuseStep 2806253 = 1052345) (by norm_num)
theorem B6312437 : Blo 1869636 6312437 := bbase (se 5 (by rfl) ⟨295895, by rfl⟩ : syracuseStep 6312437 = 591791) (by norm_num)
theorem B2806277 : Blo 1869636 2806277 := bbase (se 4 (by rfl) ⟨263088, by rfl⟩ : syracuseStep 2806277 = 526177) (by norm_num)
theorem B4493837 : Blo 1869636 4493837 := bbase (se 3 (by rfl) ⟨842594, by rfl⟩ : syracuseStep 4493837 = 1685189) (by norm_num)
theorem B2806301 : Blo 1869636 2806301 := bbase (se 3 (by rfl) ⟨526181, by rfl⟩ : syracuseStep 2806301 = 1052363) (by norm_num)
theorem B4207157 : Blo 1869636 4207157 := bbase (se 5 (by rfl) ⟨197210, by rfl⟩ : syracuseStep 4207157 = 394421) (by norm_num)
theorem B2806325 : Blo 1869636 2806325 := bbase (se 5 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 2806325 = 263093) (by norm_num)
theorem B2806349 : Blo 1869636 2806349 := bbase (se 3 (by rfl) ⟨526190, by rfl⟩ : syracuseStep 2806349 = 1052381) (by norm_num)
theorem B9466469 : Blo 1869636 9466469 := bbase (se 4 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 9466469 = 1774963) (by norm_num)
theorem B2806373 : Blo 1869636 2806373 := bbase (se 4 (by rfl) ⟨263097, by rfl⟩ : syracuseStep 2806373 = 526195) (by norm_num)
theorem B4207229 : Blo 1869636 4207229 := bbase (se 3 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 4207229 = 1577711) (by norm_num)
theorem B2806397 : Blo 1869636 2806397 := bbase (se 3 (by rfl) ⟨526199, by rfl⟩ : syracuseStep 2806397 = 1052399) (by norm_num)
theorem B2806421 : Blo 1869636 2806421 := bbase (se 6 (by rfl) ⟨65775, by rfl⟩ : syracuseStep 2806421 = 131551) (by norm_num)
theorem B6402725 : Blo 1869636 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B2806445 : Blo 1869636 2806445 := bbase (se 3 (by rfl) ⟨526208, by rfl⟩ : syracuseStep 2806445 = 1052417) (by norm_num)
theorem B4207301 : Blo 1869636 4207301 := bbase (se 4 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 4207301 = 788869) (by norm_num)
theorem B2806469 : Blo 1869636 2806469 := bbase (se 4 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 2806469 = 526213) (by norm_num)
theorem B2527957 : Blo 1869636 2527957 := bbase (se 7 (by rfl) ⟨29624, by rfl⟩ : syracuseStep 2527957 = 59249) (by norm_num)
theorem B2806493 : Blo 1869636 2806493 := bbase (se 3 (by rfl) ⟨526217, by rfl⟩ : syracuseStep 2806493 = 1052435) (by norm_num)
theorem B7099109 : Blo 1869636 7099109 := bbase (se 4 (by rfl) ⟨665541, by rfl⟩ : syracuseStep 7099109 = 1331083) (by norm_num)
theorem B2806517 : Blo 1869636 2806517 := bbase (se 5 (by rfl) ⟨131555, by rfl⟩ : syracuseStep 2806517 = 263111) (by norm_num)
theorem B4207373 : Blo 1869636 4207373 := bbase (se 3 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 4207373 = 1577765) (by norm_num)
theorem B2806541 : Blo 1869636 2806541 := bbase (se 3 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 2806541 = 1052453) (by norm_num)
theorem B2806565 : Blo 1869636 2806565 := bbase (se 4 (by rfl) ⟨263115, by rfl⟩ : syracuseStep 2806565 = 526231) (by norm_num)
theorem B10654517 : Blo 1869636 10654517 := bbase (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) (by norm_num)
theorem B2806589 : Blo 1869636 2806589 := bbase (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) (by norm_num)
theorem B4207445 : Blo 1869636 4207445 := bbase (se 9 (by rfl) ⟨12326, by rfl⟩ : syracuseStep 4207445 = 24653) (by norm_num)
theorem B2806613 : Blo 1869636 2806613 := bbase (se 9 (by rfl) ⟨8222, by rfl⟩ : syracuseStep 2806613 = 16445) (by norm_num)
theorem B2806637 : Blo 1869636 2806637 := bbase (se 3 (by rfl) ⟨526244, by rfl⟩ : syracuseStep 2806637 = 1052489) (by norm_num)
theorem B2700157 : Blo 1869636 2700157 := bbase (se 3 (by rfl) ⟨506279, by rfl⟩ : syracuseStep 2700157 = 1012559) (by norm_num)
theorem B2806661 : Blo 1869636 2806661 := bbase (se 4 (by rfl) ⟨263124, by rfl⟩ : syracuseStep 2806661 = 526249) (by norm_num)
theorem B4207517 : Blo 1869636 4207517 := bbase (se 3 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 4207517 = 1577819) (by norm_num)
theorem B2806685 : Blo 1869636 2806685 := bbase (se 3 (by rfl) ⟨526253, by rfl⟩ : syracuseStep 2806685 = 1052507) (by norm_num)
theorem B6312869 : Blo 1869636 6312869 := bbase (se 4 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 6312869 = 1183663) (by norm_num)
theorem B2806709 : Blo 1869636 2806709 := bbase (se 5 (by rfl) ⟨131564, by rfl⟩ : syracuseStep 2806709 = 263129) (by norm_num)
theorem B3601349 : Blo 1869636 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B2806733 : Blo 1869636 2806733 := bbase (se 3 (by rfl) ⟨526262, by rfl⟩ : syracuseStep 2806733 = 1052525) (by norm_num)
theorem B4207589 : Blo 1869636 4207589 := bbase (se 4 (by rfl) ⟨394461, by rfl⟩ : syracuseStep 4207589 = 788923) (by norm_num)
theorem B2806757 : Blo 1869636 2806757 := bbase (se 4 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 2806757 = 526267) (by norm_num)
theorem B2806781 : Blo 1869636 2806781 := bbase (se 3 (by rfl) ⟨526271, by rfl⟩ : syracuseStep 2806781 = 1052543) (by norm_num)
theorem B7099397 : Blo 1869636 7099397 := bbase (se 4 (by rfl) ⟨665568, by rfl⟩ : syracuseStep 7099397 = 1331137) (by norm_num)
theorem B8991749 : Blo 1869636 8991749 := bbase (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) (by norm_num)
theorem B2995213 : Blo 1869636 2995213 := bbase (se 3 (by rfl) ⟨561602, by rfl⟩ : syracuseStep 2995213 = 1123205) (by norm_num)
theorem B2806805 : Blo 1869636 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B4207661 : Blo 1869636 4207661 := bbase (se 3 (by rfl) ⟨788936, by rfl⟩ : syracuseStep 4207661 = 1577873) (by norm_num)
theorem B2806829 : Blo 1869636 2806829 := bbase (se 3 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 2806829 = 1052561) (by norm_num)
theorem B2806853 : Blo 1869636 2806853 := bbase (se 4 (by rfl) ⟨263142, by rfl⟩ : syracuseStep 2806853 = 526285) (by norm_num)
theorem B3552349 : Blo 1869636 3552349 := bbase (se 3 (by rfl) ⟨666065, by rfl⟩ : syracuseStep 3552349 = 1332131) (by norm_num)
theorem B2806877 : Blo 1869636 2806877 := bbase (se 3 (by rfl) ⟨526289, by rfl⟩ : syracuseStep 2806877 = 1052579) (by norm_num)
theorem B4207733 : Blo 1869636 4207733 := bbase (se 5 (by rfl) ⟨197237, by rfl⟩ : syracuseStep 4207733 = 394475) (by norm_num)
theorem B2806901 : Blo 1869636 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B2806925 : Blo 1869636 2806925 := bbase (se 3 (by rfl) ⟨526298, by rfl⟩ : syracuseStep 2806925 = 1052597) (by norm_num)
theorem B2806949 : Blo 1869636 2806949 := bbase (se 4 (by rfl) ⟨263151, by rfl⟩ : syracuseStep 2806949 = 526303) (by norm_num)
theorem B5690533 : Blo 1869636 5690533 := bbase (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) (by norm_num)
theorem B11982005 : Blo 1869636 11982005 := bbase (se 5 (by rfl) ⟨561656, by rfl⟩ : syracuseStep 11982005 = 1123313) (by norm_num)
theorem B4207805 : Blo 1869636 4207805 := bbase (se 3 (by rfl) ⟨788963, by rfl⟩ : syracuseStep 4207805 = 1577927) (by norm_num)
theorem B2806973 : Blo 1869636 2806973 := bbase (se 3 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 2806973 = 1052615) (by norm_num)
theorem B2806997 : Blo 1869636 2806997 := bbase (se 7 (by rfl) ⟨32894, by rfl⟩ : syracuseStep 2806997 = 65789) (by norm_num)
theorem B3552493 : Blo 1869636 3552493 := bbase (se 3 (by rfl) ⟨666092, by rfl⟩ : syracuseStep 3552493 = 1332185) (by norm_num)
theorem B2807021 : Blo 1869636 2807021 := bbase (se 3 (by rfl) ⟨526316, by rfl⟩ : syracuseStep 2807021 = 1052633) (by norm_num)
theorem B4207877 : Blo 1869636 4207877 := bbase (se 4 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 4207877 = 788977) (by norm_num)
theorem B2807045 : Blo 1869636 2807045 := bbase (se 4 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 2807045 = 526321) (by norm_num)
theorem B2995469 : Blo 1869636 2995469 := bbase (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) (by norm_num)
theorem B2807069 : Blo 1869636 2807069 := bbase (se 3 (by rfl) ⟨526325, by rfl⟩ : syracuseStep 2807069 = 1052651) (by norm_num)
theorem B2807093 : Blo 1869636 2807093 := bbase (se 5 (by rfl) ⟨131582, by rfl⟩ : syracuseStep 2807093 = 263165) (by norm_num)
theorem B4207949 : Blo 1869636 4207949 := bbase (se 3 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 4207949 = 1577981) (by norm_num)
theorem B2807117 : Blo 1869636 2807117 := bbase (se 3 (by rfl) ⟨526334, by rfl⟩ : syracuseStep 2807117 = 1052669) (by norm_num)
theorem B6313301 : Blo 1869636 6313301 := bbase (se 16 (by rfl) ⟨144, by rfl⟩ : syracuseStep 6313301 = 289) (by norm_num)
theorem B6739301 : Blo 1869636 6739301 := bbase (se 4 (by rfl) ⟨631809, by rfl⟩ : syracuseStep 6739301 = 1263619) (by norm_num)
theorem B2807141 : Blo 1869636 2807141 := bbase (se 4 (by rfl) ⟨263169, by rfl⟩ : syracuseStep 2807141 = 526339) (by norm_num)
theorem B2807165 : Blo 1869636 2807165 := bbase (se 3 (by rfl) ⟨526343, by rfl⟩ : syracuseStep 2807165 = 1052687) (by norm_num)
theorem B3552653 : Blo 1869636 3552653 := bbase (se 3 (by rfl) ⟨666122, by rfl⟩ : syracuseStep 3552653 = 1332245) (by norm_num)
theorem B4208021 : Blo 1869636 4208021 := bbase (se 6 (by rfl) ⟨98625, by rfl⟩ : syracuseStep 4208021 = 197251) (by norm_num)
theorem B2807189 : Blo 1869636 2807189 := bbase (se 6 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 2807189 = 131587) (by norm_num)
theorem B2807213 : Blo 1869636 2807213 := bbase (se 3 (by rfl) ⟨526352, by rfl⟩ : syracuseStep 2807213 = 1052705) (by norm_num)
theorem B2807237 : Blo 1869636 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B2528725 : Blo 1869636 2528725 := bbase (se 7 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 2528725 = 59267) (by norm_num)
theorem B19207637 : Blo 1869636 19207637 := bbase (se 7 (by rfl) ⟨225089, by rfl⟩ : syracuseStep 19207637 = 450179) (by norm_num)
theorem B4208093 : Blo 1869636 4208093 := bbase (se 3 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 4208093 = 1578035) (by norm_num)
theorem B2807261 : Blo 1869636 2807261 := bbase (se 3 (by rfl) ⟨526361, by rfl⟩ : syracuseStep 2807261 = 1052723) (by norm_num)
theorem B6739429 : Blo 1869636 6739429 := bbase (se 4 (by rfl) ⟨631821, by rfl⟩ : syracuseStep 6739429 = 1263643) (by norm_num)
theorem B2807285 : Blo 1869636 2807285 := bbase (se 5 (by rfl) ⟨131591, by rfl⟩ : syracuseStep 2807285 = 263183) (by norm_num)
theorem B2807309 : Blo 1869636 2807309 := bbase (se 3 (by rfl) ⟨526370, by rfl⟩ : syracuseStep 2807309 = 1052741) (by norm_num)
theorem B3552797 : Blo 1869636 3552797 := bbase (se 3 (by rfl) ⟨666149, by rfl⟩ : syracuseStep 3552797 = 1332299) (by norm_num)
theorem B4208165 : Blo 1869636 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B2807333 : Blo 1869636 2807333 := bbase (se 4 (by rfl) ⟨263187, by rfl⟩ : syracuseStep 2807333 = 526375) (by norm_num)
theorem B1922617 : Blo 1869636 1922617 := bbase (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) (by norm_num)
theorem B2807357 : Blo 1869636 2807357 := bbase (se 3 (by rfl) ⟨526379, by rfl⟩ : syracuseStep 2807357 = 1052759) (by norm_num)
theorem B2807381 : Blo 1869636 2807381 := bbase (se 8 (by rfl) ⟨16449, by rfl⟩ : syracuseStep 2807381 = 32899) (by norm_num)
theorem B4208237 : Blo 1869636 4208237 := bbase (se 3 (by rfl) ⟨789044, by rfl⟩ : syracuseStep 4208237 = 1578089) (by norm_num)
theorem B2807405 : Blo 1869636 2807405 := bbase (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) (by norm_num)
theorem B2807429 : Blo 1869636 2807429 := bbase (se 4 (by rfl) ⟨263196, by rfl⟩ : syracuseStep 2807429 = 526393) (by norm_num)
theorem B3790493 : Blo 1869636 3790493 := bbase (se 3 (by rfl) ⟨710717, by rfl⟩ : syracuseStep 3790493 = 1421435) (by norm_num)
theorem B2807453 : Blo 1869636 2807453 := bbase (se 3 (by rfl) ⟨526397, by rfl⟩ : syracuseStep 2807453 = 1052795) (by norm_num)
theorem B4208309 : Blo 1869636 4208309 := bbase (se 5 (by rfl) ⟨197264, by rfl⟩ : syracuseStep 4208309 = 394529) (by norm_num)
theorem B4208381 : Blo 1869636 4208381 := bbase (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) (by norm_num)
theorem B6313733 : Blo 1869636 6313733 := bbase (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) (by norm_num)
theorem B3553085 : Blo 1869636 3553085 := bbase (se 3 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 3553085 = 1332407) (by norm_num)
theorem B4208453 : Blo 1869636 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B3790669 : Blo 1869636 3790669 := bbase (se 3 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 3790669 = 1421501) (by norm_num)
theorem B4732789 : Blo 1869636 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B9467765 : Blo 1869636 9467765 := bbase (se 5 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 9467765 = 887603) (by norm_num)
theorem B4208525 : Blo 1869636 4208525 := bbase (se 3 (by rfl) ⟨789098, by rfl⟩ : syracuseStep 4208525 = 1578197) (by norm_num)
theorem B1996697 : Blo 1869636 1996697 := bbase (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) (by norm_num)
theorem B3995581 : Blo 1869636 3995581 := bbase (se 3 (by rfl) ⟨749171, by rfl⟩ : syracuseStep 3995581 = 1498343) (by norm_num)
theorem B2996173 : Blo 1869636 2996173 := bbase (se 3 (by rfl) ⟨561782, by rfl⟩ : syracuseStep 2996173 = 1123565) (by norm_num)
theorem B4208597 : Blo 1869636 4208597 := bbase (se 7 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 4208597 = 98639) (by norm_num)
theorem B4732901 : Blo 1869636 4732901 := bbase (se 4 (by rfl) ⟨443709, by rfl⟩ : syracuseStep 4732901 = 887419) (by norm_num)
theorem B3201005 : Blo 1869636 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B7993349 : Blo 1869636 7993349 := bbase (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) (by norm_num)
theorem B4208669 : Blo 1869636 4208669 := bbase (se 3 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 4208669 = 1578251) (by norm_num)
theorem B4266029 : Blo 1869636 4266029 := bbase (se 3 (by rfl) ⟨799880, by rfl⟩ : syracuseStep 4266029 = 1599761) (by norm_num)
theorem B2103349 : Blo 1869636 2103349 := bbase (se 5 (by rfl) ⟨98594, by rfl⟩ : syracuseStep 2103349 = 197189) (by norm_num)
theorem B14211125 : Blo 1869636 14211125 := bbase (se 5 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 14211125 = 1332293) (by norm_num)
theorem B3037253 : Blo 1869636 3037253 := bbase (se 4 (by rfl) ⟨284742, by rfl⟩ : syracuseStep 3037253 = 569485) (by norm_num)
theorem B2103385 : Blo 1869636 2103385 := bbase (se 2 (by rfl) ⟨788769, by rfl⟩ : syracuseStep 2103385 = 1577539) (by norm_num)
theorem B4208741 : Blo 1869636 4208741 := bbase (se 4 (by rfl) ⟨394569, by rfl⟩ : syracuseStep 4208741 = 789139) (by norm_num)
theorem B2103421 : Blo 1869636 2103421 := bbase (se 3 (by rfl) ⟨394391, by rfl⟩ : syracuseStep 2103421 = 788783) (by norm_num)
theorem B2103457 : Blo 1869636 2103457 := bbase (se 2 (by rfl) ⟨788796, by rfl⟩ : syracuseStep 2103457 = 1577593) (by norm_num)
theorem B4733093 : Blo 1869636 4733093 := bbase (se 4 (by rfl) ⟨443727, by rfl⟩ : syracuseStep 4733093 = 887455) (by norm_num)
theorem B7100581 : Blo 1869636 7100581 := bbase (se 4 (by rfl) ⟨665679, by rfl⟩ : syracuseStep 7100581 = 1331359) (by norm_num)
theorem B4208813 : Blo 1869636 4208813 := bbase (se 3 (by rfl) ⟨789152, by rfl⟩ : syracuseStep 4208813 = 1578305) (by norm_num)
theorem B6314165 : Blo 1869636 6314165 := bbase (se 5 (by rfl) ⟨295976, by rfl⟩ : syracuseStep 6314165 = 591953) (by norm_num)
theorem B2103493 : Blo 1869636 2103493 := bbase (se 4 (by rfl) ⟨197202, by rfl⟩ : syracuseStep 2103493 = 394405) (by norm_num)
theorem B10115285 : Blo 1869636 10115285 := bbase (se 7 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 10115285 = 237077) (by norm_num)
theorem B11991253 : Blo 1869636 11991253 := bbase (se 7 (by rfl) ⟨140522, by rfl⟩ : syracuseStep 11991253 = 281045) (by norm_num)
theorem B2103529 : Blo 1869636 2103529 := bbase (se 2 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 2103529 = 1577647) (by norm_num)
theorem B4208885 : Blo 1869636 4208885 := bbase (se 5 (by rfl) ⟨197291, by rfl⟩ : syracuseStep 4208885 = 394583) (by norm_num)
theorem B8534261 : Blo 1869636 8534261 := bbase (se 5 (by rfl) ⟨400043, by rfl⟩ : syracuseStep 8534261 = 800087) (by norm_num)
theorem B2103565 : Blo 1869636 2103565 := bbase (se 3 (by rfl) ⟨394418, by rfl⟩ : syracuseStep 2103565 = 788837) (by norm_num)
theorem B2103601 : Blo 1869636 2103601 := bbase (se 2 (by rfl) ⟨788850, by rfl⟩ : syracuseStep 2103601 = 1577701) (by norm_num)
theorem B4208957 : Blo 1869636 4208957 := bbase (se 3 (by rfl) ⟨789179, by rfl⟩ : syracuseStep 4208957 = 1578359) (by norm_num)
theorem B2103637 : Blo 1869636 2103637 := bbase (se 10 (by rfl) ⟨3081, by rfl⟩ : syracuseStep 2103637 = 6163) (by norm_num)
theorem B1997141 : Blo 1869636 1997141 := bbase (se 10 (by rfl) ⟨2925, by rfl⟩ : syracuseStep 1997141 = 5851) (by norm_num)
theorem B2996597 : Blo 1869636 2996597 := bbase (se 5 (by rfl) ⟨140465, by rfl⟩ : syracuseStep 2996597 = 280931) (by norm_num)
theorem B2103673 : Blo 1869636 2103673 := bbase (se 2 (by rfl) ⟨788877, by rfl⟩ : syracuseStep 2103673 = 1577755) (by norm_num)
theorem B4209029 : Blo 1869636 4209029 := bbase (se 4 (by rfl) ⟨394596, by rfl⟩ : syracuseStep 4209029 = 789193) (by norm_num)
theorem B2103709 : Blo 1869636 2103709 := bbase (se 3 (by rfl) ⟨394445, by rfl⟩ : syracuseStep 2103709 = 788891) (by norm_num)
theorem B2103745 : Blo 1869636 2103745 := bbase (se 2 (by rfl) ⟨788904, by rfl⟩ : syracuseStep 2103745 = 1577809) (by norm_num)
theorem B4209101 : Blo 1869636 4209101 := bbase (se 3 (by rfl) ⟨789206, by rfl⟩ : syracuseStep 4209101 = 1578413) (by norm_num)
theorem B7100885 : Blo 1869636 7100885 := bbase (se 7 (by rfl) ⟨83213, by rfl⟩ : syracuseStep 7100885 = 166427) (by norm_num)
theorem B4323797 : Blo 1869636 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B14203349 : Blo 1869636 14203349 := bbase (se 7 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 14203349 = 332891) (by norm_num)
theorem B4495837 : Blo 1869636 4495837 := bbase (se 3 (by rfl) ⟨842969, by rfl⟩ : syracuseStep 4495837 = 1685939) (by norm_num)
theorem B2103781 : Blo 1869636 2103781 := bbase (se 4 (by rfl) ⟨197229, by rfl⟩ : syracuseStep 2103781 = 394459) (by norm_num)
theorem B4733437 : Blo 1869636 4733437 := bbase (se 3 (by rfl) ⟨887519, by rfl⟩ : syracuseStep 4733437 = 1775039) (by norm_num)
theorem B2103817 : Blo 1869636 2103817 := bbase (se 2 (by rfl) ⟨788931, by rfl⟩ : syracuseStep 2103817 = 1577863) (by norm_num)
theorem B4209173 : Blo 1869636 4209173 := bbase (se 6 (by rfl) ⟨98652, by rfl⟩ : syracuseStep 4209173 = 197305) (by norm_num)
theorem B3897877 : Blo 1869636 3897877 := bbase (se 6 (by rfl) ⟨91356, by rfl⟩ : syracuseStep 3897877 = 182713) (by norm_num)
theorem B2103853 : Blo 1869636 2103853 := bbase (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) (by norm_num)
theorem B1997389 : Blo 1869636 1997389 := bbase (se 3 (by rfl) ⟨374510, by rfl⟩ : syracuseStep 1997389 = 749021) (by norm_num)
theorem B2103889 : Blo 1869636 2103889 := bbase (se 2 (by rfl) ⟨788958, by rfl⟩ : syracuseStep 2103889 = 1577917) (by norm_num)
theorem B4209245 : Blo 1869636 4209245 := bbase (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) (by norm_num)
theorem B6314597 : Blo 1869636 6314597 := bbase (se 4 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 6314597 = 1183987) (by norm_num)
theorem B4733549 : Blo 1869636 4733549 := bbase (se 3 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 4733549 = 1775081) (by norm_num)
theorem B2103925 : Blo 1869636 2103925 := bbase (se 5 (by rfl) ⟨98621, by rfl⟩ : syracuseStep 2103925 = 197243) (by norm_num)
theorem B2996885 : Blo 1869636 2996885 := bbase (se 6 (by rfl) ⟨70239, by rfl⟩ : syracuseStep 2996885 = 140479) (by norm_num)
theorem B2103961 : Blo 1869636 2103961 := bbase (se 2 (by rfl) ⟨788985, by rfl⟩ : syracuseStep 2103961 = 1577971) (by norm_num)
theorem B4209317 : Blo 1869636 4209317 := bbase (se 4 (by rfl) ⟨394623, by rfl⟩ : syracuseStep 4209317 = 789247) (by norm_num)
theorem B10115765 : Blo 1869636 10115765 := bbase (se 5 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 10115765 = 948353) (by norm_num)
theorem B2103997 : Blo 1869636 2103997 := bbase (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) (by norm_num)
theorem B5995205 : Blo 1869636 5995205 := bbase (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) (by norm_num)
theorem B2104033 : Blo 1869636 2104033 := bbase (se 2 (by rfl) ⟨789012, by rfl⟩ : syracuseStep 2104033 = 1578025) (by norm_num)
theorem B4209389 : Blo 1869636 4209389 := bbase (se 3 (by rfl) ⟨789260, by rfl⟩ : syracuseStep 4209389 = 1578521) (by norm_num)
theorem B2104069 : Blo 1869636 2104069 := bbase (se 4 (by rfl) ⟨197256, by rfl⟩ : syracuseStep 2104069 = 394513) (by norm_num)
theorem B2104105 : Blo 1869636 2104105 := bbase (se 2 (by rfl) ⟨789039, by rfl⟩ : syracuseStep 2104105 = 1578079) (by norm_num)
theorem B4733741 : Blo 1869636 4733741 := bbase (se 3 (by rfl) ⟨887576, by rfl⟩ : syracuseStep 4733741 = 1775153) (by norm_num)
theorem B4209461 : Blo 1869636 4209461 := bbase (se 5 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 4209461 = 394637) (by norm_num)
theorem B3996469 : Blo 1869636 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B2366273 : Blo 1869636 2366273 := bbase (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) (by norm_num)
theorem B2104141 : Blo 1869636 2104141 := bbase (se 3 (by rfl) ⟨394526, by rfl⟩ : syracuseStep 2104141 = 789053) (by norm_num)
theorem B2104177 : Blo 1869636 2104177 := bbase (se 2 (by rfl) ⟨789066, by rfl⟩ : syracuseStep 2104177 = 1578133) (by norm_num)
theorem B2997109 : Blo 1869636 2997109 := bbase (se 5 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 2997109 = 280979) (by norm_num)
theorem B2366329 : Blo 1869636 2366329 := bbase (se 2 (by rfl) ⟨887373, by rfl⟩ : syracuseStep 2366329 = 1774747) (by norm_num)
theorem B4209533 : Blo 1869636 4209533 := bbase (se 3 (by rfl) ⟨789287, by rfl⟩ : syracuseStep 4209533 = 1578575) (by norm_num)
theorem B2104213 : Blo 1869636 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B15973301 : Blo 1869636 15973301 := bbase (se 5 (by rfl) ⟨748748, by rfl⟩ : syracuseStep 15973301 = 1497497) (by norm_num)
theorem B2104249 : Blo 1869636 2104249 := bbase (se 2 (by rfl) ⟨789093, by rfl⟩ : syracuseStep 2104249 = 1578187) (by norm_num)
theorem B4209605 : Blo 1869636 4209605 := bbase (se 4 (by rfl) ⟨394650, by rfl⟩ : syracuseStep 4209605 = 789301) (by norm_num)
theorem B2366425 : Blo 1869636 2366425 := bbase (se 2 (by rfl) ⟨887409, by rfl⟩ : syracuseStep 2366425 = 1774819) (by norm_num)
theorem B2104285 : Blo 1869636 2104285 := bbase (se 3 (by rfl) ⟨394553, by rfl⟩ : syracuseStep 2104285 = 789107) (by norm_num)
theorem B1997821 : Blo 1869636 1997821 := bbase (se 3 (by rfl) ⟨374591, by rfl⟩ : syracuseStep 1997821 = 749183) (by norm_num)
theorem B2104321 : Blo 1869636 2104321 := bbase (se 2 (by rfl) ⟨789120, by rfl⟩ : syracuseStep 2104321 = 1578241) (by norm_num)
theorem B4209677 : Blo 1869636 4209677 := bbase (se 3 (by rfl) ⟨789314, by rfl⟩ : syracuseStep 4209677 = 1578629) (by norm_num)
theorem B6315029 : Blo 1869636 6315029 := bbase (se 6 (by rfl) ⟨148008, by rfl⟩ : syracuseStep 6315029 = 296017) (by norm_num)
theorem B4496413 : Blo 1869636 4496413 := bbase (se 3 (by rfl) ⟨843077, by rfl⟩ : syracuseStep 4496413 = 1686155) (by norm_num)
theorem B2104357 : Blo 1869636 2104357 := bbase (se 4 (by rfl) ⟨197283, by rfl⟩ : syracuseStep 2104357 = 394567) (by norm_num)
theorem B1997893 : Blo 1869636 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B2104393 : Blo 1869636 2104393 := bbase (se 2 (by rfl) ⟨789147, by rfl⟩ : syracuseStep 2104393 = 1578295) (by norm_num)
theorem B4209749 : Blo 1869636 4209749 := bbase (se 8 (by rfl) ⟨24666, by rfl⟩ : syracuseStep 4209749 = 49333) (by norm_num)
theorem B2104429 : Blo 1869636 2104429 := bbase (se 3 (by rfl) ⟨394580, by rfl⟩ : syracuseStep 2104429 = 789161) (by norm_num)
theorem B2366597 : Blo 1869636 2366597 := bbase (se 4 (by rfl) ⟨221868, by rfl⟩ : syracuseStep 2366597 = 443737) (by norm_num)
theorem B4734085 : Blo 1869636 4734085 := bbase (se 4 (by rfl) ⟨443820, by rfl⟩ : syracuseStep 4734085 = 887641) (by norm_num)
theorem B9469061 : Blo 1869636 9469061 := bbase (se 4 (by rfl) ⟨887724, by rfl⟩ : syracuseStep 9469061 = 1775449) (by norm_num)
theorem B2104465 : Blo 1869636 2104465 := bbase (se 2 (by rfl) ⟨789174, by rfl⟩ : syracuseStep 2104465 = 1578349) (by norm_num)
theorem B4209821 : Blo 1869636 4209821 := bbase (se 3 (by rfl) ⟨789341, by rfl⟩ : syracuseStep 4209821 = 1578683) (by norm_num)
theorem B2104501 : Blo 1869636 2104501 := bbase (se 5 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 2104501 = 197297) (by norm_num)
theorem B2366653 : Blo 1869636 2366653 := bbase (se 3 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 2366653 = 887495) (by norm_num)
theorem B2104537 : Blo 1869636 2104537 := bbase (se 2 (by rfl) ⟨789201, by rfl⟩ : syracuseStep 2104537 = 1578403) (by norm_num)
theorem B3038429 : Blo 1869636 3038429 := bbase (se 3 (by rfl) ⟨569705, by rfl⟩ : syracuseStep 3038429 = 1139411) (by norm_num)
theorem B8985829 : Blo 1869636 8985829 := bbase (se 4 (by rfl) ⟨842421, by rfl⟩ : syracuseStep 8985829 = 1684843) (by norm_num)
theorem B4209893 : Blo 1869636 4209893 := bbase (se 4 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 4209893 = 789355) (by norm_num)
theorem B4734197 : Blo 1869636 4734197 := bbase (se 5 (by rfl) ⟨221915, by rfl⟩ : syracuseStep 4734197 = 443831) (by norm_num)
theorem B2104573 : Blo 1869636 2104573 := bbase (se 3 (by rfl) ⟨394607, by rfl⟩ : syracuseStep 2104573 = 789215) (by norm_num)
theorem B2366749 : Blo 1869636 2366749 := bbase (se 3 (by rfl) ⟨443765, by rfl⟩ : syracuseStep 2366749 = 887531) (by norm_num)
theorem B2104609 : Blo 1869636 2104609 := bbase (se 2 (by rfl) ⟨789228, by rfl⟩ : syracuseStep 2104609 = 1578457) (by norm_num)
theorem B3996965 : Blo 1869636 3996965 := bbase (se 4 (by rfl) ⟨374715, by rfl⟩ : syracuseStep 3996965 = 749431) (by norm_num)
theorem B4209965 : Blo 1869636 4209965 := bbase (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) (by norm_num)
theorem B2104645 : Blo 1869636 2104645 := bbase (se 4 (by rfl) ⟨197310, by rfl⟩ : syracuseStep 2104645 = 394621) (by norm_num)
theorem B4496741 : Blo 1869636 4496741 := bbase (se 4 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 4496741 = 843139) (by norm_num)
theorem B2104681 : Blo 1869636 2104681 := bbase (se 2 (by rfl) ⟨789255, by rfl⟩ : syracuseStep 2104681 = 1578511) (by norm_num)
theorem B4210037 : Blo 1869636 4210037 := bbase (se 5 (by rfl) ⟨197345, by rfl⟩ : syracuseStep 4210037 = 394691) (by norm_num)
theorem B9600389 : Blo 1869636 9600389 := bbase (se 4 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 9600389 = 1800073) (by norm_num)
theorem B2104717 : Blo 1869636 2104717 := bbase (se 3 (by rfl) ⟨394634, by rfl⟩ : syracuseStep 2104717 = 789269) (by norm_num)
theorem B4496797 : Blo 1869636 4496797 := bbase (se 3 (by rfl) ⟨843149, by rfl⟩ : syracuseStep 4496797 = 1686299) (by norm_num)
theorem B2104753 : Blo 1869636 2104753 := bbase (se 2 (by rfl) ⟨789282, by rfl⟩ : syracuseStep 2104753 = 1578565) (by norm_num)
theorem B4734389 : Blo 1869636 4734389 := bbase (se 5 (by rfl) ⟨221924, by rfl⟩ : syracuseStep 4734389 = 443849) (by norm_num)
theorem B1998265 : Blo 1869636 1998265 := bbase (se 2 (by rfl) ⟨749349, by rfl⟩ : syracuseStep 1998265 = 1498699) (by norm_num)
theorem B4210109 : Blo 1869636 4210109 := bbase (se 3 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 4210109 = 1578791) (by norm_num)
theorem B6315461 : Blo 1869636 6315461 := bbase (se 4 (by rfl) ⟨592074, by rfl⟩ : syracuseStep 6315461 = 1184149) (by norm_num)
theorem B2366921 : Blo 1869636 2366921 := bbase (se 2 (by rfl) ⟨887595, by rfl⟩ : syracuseStep 2366921 = 1775191) (by norm_num)
theorem B2104789 : Blo 1869636 2104789 := bbase (se 7 (by rfl) ⟨24665, by rfl⟩ : syracuseStep 2104789 = 49331) (by norm_num)
theorem B2104825 : Blo 1869636 2104825 := bbase (se 2 (by rfl) ⟨789309, by rfl⟩ : syracuseStep 2104825 = 1578619) (by norm_num)
theorem B2366977 : Blo 1869636 2366977 := bbase (se 2 (by rfl) ⟨887616, by rfl⟩ : syracuseStep 2366977 = 1775233) (by norm_num)
theorem B4210181 : Blo 1869636 4210181 := bbase (se 4 (by rfl) ⟨394704, by rfl⟩ : syracuseStep 4210181 = 789409) (by norm_num)
theorem B2104861 : Blo 1869636 2104861 := bbase (se 3 (by rfl) ⟨394661, by rfl⟩ : syracuseStep 2104861 = 789323) (by norm_num)
theorem B10649141 : Blo 1869636 10649141 := bbase (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) (by norm_num)
theorem B2104897 : Blo 1869636 2104897 := bbase (se 2 (by rfl) ⟨789336, by rfl⟩ : syracuseStep 2104897 = 1578673) (by norm_num)
theorem B4210253 : Blo 1869636 4210253 := bbase (se 3 (by rfl) ⟨789422, by rfl⟩ : syracuseStep 4210253 = 1578845) (by norm_num)
theorem B2367073 : Blo 1869636 2367073 := bbase (se 2 (by rfl) ⟨887652, by rfl⟩ : syracuseStep 2367073 = 1775305) (by norm_num)
theorem B2104933 : Blo 1869636 2104933 := bbase (se 4 (by rfl) ⟨197337, by rfl⟩ : syracuseStep 2104933 = 394675) (by norm_num)
theorem B2104969 : Blo 1869636 2104969 := bbase (se 2 (by rfl) ⟨789363, by rfl⟩ : syracuseStep 2104969 = 1578727) (by norm_num)
theorem B4210325 : Blo 1869636 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B2105005 : Blo 1869636 2105005 := bbase (se 3 (by rfl) ⟨394688, by rfl⟩ : syracuseStep 2105005 = 789377) (by norm_num)
theorem B2105041 : Blo 1869636 2105041 := bbase (se 2 (by rfl) ⟨789390, by rfl⟩ : syracuseStep 2105041 = 1578781) (by norm_num)
theorem B4210397 : Blo 1869636 4210397 := bbase (se 3 (by rfl) ⟨789449, by rfl⟩ : syracuseStep 4210397 = 1578899) (by norm_num)
theorem B2277097 : Blo 1869636 2277097 := bbase (se 2 (by rfl) ⟨853911, by rfl⟩ : syracuseStep 2277097 = 1707823) (by norm_num)
theorem B2105077 : Blo 1869636 2105077 := bbase (se 5 (by rfl) ⟨98675, by rfl⟩ : syracuseStep 2105077 = 197351) (by norm_num)
theorem B2367245 : Blo 1869636 2367245 := bbase (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) (by norm_num)
theorem B4734733 : Blo 1869636 4734733 := bbase (se 3 (by rfl) ⟨887762, by rfl⟩ : syracuseStep 4734733 = 1775525) (by norm_num)
theorem B2105113 : Blo 1869636 2105113 := bbase (se 2 (by rfl) ⟨789417, by rfl⟩ : syracuseStep 2105113 = 1578835) (by norm_num)
theorem B4210469 : Blo 1869636 4210469 := bbase (se 4 (by rfl) ⟨394731, by rfl⟩ : syracuseStep 4210469 = 789463) (by norm_num)
theorem B1998641 : Blo 1869636 1998641 := bbase (se 2 (by rfl) ⟨749490, by rfl⟩ : syracuseStep 1998641 = 1498981) (by norm_num)
theorem B2105149 : Blo 1869636 2105149 := bbase (se 3 (by rfl) ⟨394715, by rfl⟩ : syracuseStep 2105149 = 789431) (by norm_num)
theorem B2367301 : Blo 1869636 2367301 := bbase (se 4 (by rfl) ⟨221934, by rfl⟩ : syracuseStep 2367301 = 443869) (by norm_num)
theorem B2400077 : Blo 1869636 2400077 := bbase (se 3 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 2400077 = 900029) (by norm_num)
theorem B2105185 : Blo 1869636 2105185 := bbase (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) (by norm_num)
theorem B7987045 : Blo 1869636 7987045 := bbase (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) (by norm_num)
theorem B4210541 : Blo 1869636 4210541 := bbase (se 3 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 4210541 = 1578953) (by norm_num)
theorem B7987061 : Blo 1869636 7987061 := bbase (se 5 (by rfl) ⟨374393, by rfl⟩ : syracuseStep 7987061 = 748787) (by norm_num)
theorem B6315893 : Blo 1869636 6315893 := bbase (se 5 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 6315893 = 592115) (by norm_num)
theorem B4734845 : Blo 1869636 4734845 := bbase (se 3 (by rfl) ⟨887783, by rfl⟩ : syracuseStep 4734845 = 1775567) (by norm_num)
theorem B2105221 : Blo 1869636 2105221 := bbase (se 4 (by rfl) ⟨197364, by rfl⟩ : syracuseStep 2105221 = 394729) (by norm_num)
theorem B2367397 : Blo 1869636 2367397 := bbase (se 4 (by rfl) ⟨221943, by rfl⟩ : syracuseStep 2367397 = 443887) (by norm_num)
theorem B2105257 : Blo 1869636 2105257 := bbase (se 2 (by rfl) ⟨789471, by rfl⟩ : syracuseStep 2105257 = 1578943) (by norm_num)
theorem B4210613 : Blo 1869636 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B2105293 : Blo 1869636 2105293 := bbase (se 3 (by rfl) ⟨394742, by rfl⟩ : syracuseStep 2105293 = 789485) (by norm_num)
theorem B2105329 : Blo 1869636 2105329 := bbase (se 2 (by rfl) ⟨789498, by rfl⟩ : syracuseStep 2105329 = 1578997) (by norm_num)
theorem B4210685 : Blo 1869636 4210685 := bbase (se 3 (by rfl) ⟨789503, by rfl⟩ : syracuseStep 4210685 = 1579007) (by norm_num)
theorem B2105347 : Blo 1869636 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B6316109 : Blo 1869636 6316109 := bstep (se 3 (by rfl) ⟨1184270, by rfl⟩ : syracuseStep 6316109 = 2368541) B2368541
theorem B4735057 : Blo 1869636 4735057 := bstep (se 2 (by rfl) ⟨1775646, by rfl⟩ : syracuseStep 4735057 = 3551293) B3551293
theorem B6316163 : Blo 1869636 6316163 := bstep (se 1 (by rfl) ⟨4737122, by rfl⟩ : syracuseStep 6316163 = 9474245) B9474245
theorem B2105491 : Blo 1869636 2105491 := bstep (se 1 (by rfl) ⟨1579118, by rfl⟩ : syracuseStep 2105491 = 3158237) B3158237
theorem B4210865 : Blo 1869636 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B4554947 : Blo 1869636 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B4210883 : Blo 1869636 4210883 := bstep (se 1 (by rfl) ⟨3158162, by rfl⟩ : syracuseStep 4210883 = 6316325) B6316325
theorem B2662627 : Blo 1869636 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B2367731 : Blo 1869636 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B3793169 : Blo 1869636 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B4735331 : Blo 1869636 4735331 := bstep (se 1 (by rfl) ⟨3551498, by rfl⟩ : syracuseStep 4735331 = 7102997) B7102997
theorem B19202417 : Blo 1869636 19202417 := bstep (se 2 (by rfl) ⟨7200906, by rfl⟩ : syracuseStep 19202417 = 14401813) B14401813
theorem B8987021 : Blo 1869636 8987021 := bstep (se 3 (by rfl) ⟨1685066, by rfl⟩ : syracuseStep 8987021 = 3370133) B3370133
theorem B6316433 : Blo 1869636 6316433 := bstep (se 2 (by rfl) ⟨2368662, by rfl⟩ : syracuseStep 6316433 = 4737325) B4737325
theorem B4268483 : Blo 1869636 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B4211153 : Blo 1869636 4211153 := bstep (se 2 (by rfl) ⟨1579182, by rfl⟩ : syracuseStep 4211153 = 3158365) B3158365
theorem B4211171 : Blo 1869636 4211171 := bstep (se 1 (by rfl) ⟨3158378, by rfl⟩ : syracuseStep 4211171 = 6316757) B6316757
theorem B7103011 : Blo 1869636 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B4735523 : Blo 1869636 4735523 := bstep (se 1 (by rfl) ⟨3551642, by rfl⟩ : syracuseStep 4735523 = 7103285) B7103285
theorem B11371085 : Blo 1869636 11371085 := bstep (se 3 (by rfl) ⟨2132078, by rfl⟩ : syracuseStep 11371085 = 4264157) B4264157
theorem B8102477 : Blo 1869636 8102477 := bstep (se 3 (by rfl) ⟨1519214, by rfl⟩ : syracuseStep 8102477 = 3038429) B3038429
theorem B9732707 : Blo 1869636 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B2400899 : Blo 1869636 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B22758029 : Blo 1869636 22758029 := bstep (se 3 (by rfl) ⟨4267130, by rfl⟩ : syracuseStep 22758029 = 8534261) B8534261
theorem B10658573 : Blo 1869636 10658573 := bstep (se 3 (by rfl) ⟨1998482, by rfl⟩ : syracuseStep 10658573 = 3996965) B3996965
theorem B7988003 : Blo 1869636 7988003 := bstep (se 1 (by rfl) ⟨5991002, by rfl⟩ : syracuseStep 7988003 = 11982005) B11982005
theorem B23970613 : Blo 1869636 23970613 := bstep (se 5 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 23970613 = 2247245) B2247245
theorem B2368435 : Blo 1869636 2368435 := bstep (se 1 (by rfl) ⟨1776326, by rfl⟩ : syracuseStep 2368435 = 3552653) B3552653
theorem B5055437 : Blo 1869636 5055437 := bstep (se 3 (by rfl) ⟨947894, by rfl⟩ : syracuseStep 5055437 = 1895789) B1895789
theorem B12805091 : Blo 1869636 12805091 := bstep (se 1 (by rfl) ⟨9603818, by rfl⟩ : syracuseStep 12805091 = 19207637) B19207637
theorem B2368531 : Blo 1869636 2368531 := bstep (se 1 (by rfl) ⟨1776398, by rfl⟩ : syracuseStep 2368531 = 3552797) B3552797
theorem B276661361 : Blo 1869636 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B30327949 : Blo 1869636 30327949 := bstep (se 3 (by rfl) ⟨5686490, by rfl⟩ : syracuseStep 30327949 = 11372981) B11372981
theorem B5399693 : Blo 1869636 5399693 := bstep (se 3 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 5399693 = 2024885) B2024885
theorem B3155105 : Blo 1869636 3155105 := bstep (se 2 (by rfl) ⟨1183164, by rfl⟩ : syracuseStep 3155105 = 2366329) B2366329
theorem B10650851 : Blo 1869636 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B3155233 : Blo 1869636 3155233 := bstep (se 2 (by rfl) ⟨1183212, by rfl⟩ : syracuseStep 3155233 = 2366425) B2366425
theorem B3155267 : Blo 1869636 3155267 := bstep (se 1 (by rfl) ⟨2366450, by rfl⟩ : syracuseStep 3155267 = 4732901) B4732901
theorem B2663761 : Blo 1869636 2663761 := bstep (se 2 (by rfl) ⟨998910, by rfl⟩ : syracuseStep 2663761 = 1997821) B1997821
theorem B2844019 : Blo 1869636 2844019 := bstep (se 1 (by rfl) ⟨2133014, by rfl⟩ : syracuseStep 2844019 = 4266029) B4266029
theorem B5326211 : Blo 1869636 5326211 := bstep (se 1 (by rfl) ⟨3994658, by rfl⟩ : syracuseStep 5326211 = 7989317) B7989317
theorem B2663857 : Blo 1869636 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B3155395 : Blo 1869636 3155395 := bstep (se 1 (by rfl) ⟨2366546, by rfl⟩ : syracuseStep 3155395 = 4733093) B4733093
theorem B4736465 : Blo 1869636 4736465 := bstep (se 2 (by rfl) ⟨1776174, by rfl⟩ : syracuseStep 4736465 = 3552349) B3552349
theorem B4736515 : Blo 1869636 4736515 := bstep (se 1 (by rfl) ⟨3552386, by rfl⟩ : syracuseStep 4736515 = 7104773) B7104773
theorem B7587377 : Blo 1869636 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B3155537 : Blo 1869636 3155537 := bstep (se 2 (by rfl) ⟨1183326, by rfl⟩ : syracuseStep 3155537 = 2366653) B2366653
theorem B4736657 : Blo 1869636 4736657 := bstep (se 2 (by rfl) ⟨1776246, by rfl⟩ : syracuseStep 4736657 = 3552493) B3552493
theorem B8988365 : Blo 1869636 8988365 := bstep (se 3 (by rfl) ⟨1685318, by rfl⟩ : syracuseStep 8988365 = 3370637) B3370637
theorem B3155665 : Blo 1869636 3155665 := bstep (se 2 (by rfl) ⟨1183374, by rfl⟩ : syracuseStep 3155665 = 2366749) B2366749
theorem B3155699 : Blo 1869636 3155699 := bstep (se 1 (by rfl) ⟨2366774, by rfl⟩ : syracuseStep 3155699 = 4733549) B4733549
theorem B6743843 : Blo 1869636 6743843 := bstep (se 1 (by rfl) ⟨5057882, by rfl⟩ : syracuseStep 6743843 = 10115765) B10115765
theorem B1869651 : Blo 1869636 1869651 := bstep (se 1 (by rfl) ⟨1402238, by rfl⟩ : syracuseStep 1869651 = 2804477) B2804477
theorem B1869667 : Blo 1869636 1869667 := bstep (se 1 (by rfl) ⟨1402250, by rfl⟩ : syracuseStep 1869667 = 2804501) B2804501
theorem B1869683 : Blo 1869636 1869683 := bstep (se 1 (by rfl) ⟨1402262, by rfl⟩ : syracuseStep 1869683 = 2804525) B2804525
theorem B3155827 : Blo 1869636 3155827 := bstep (se 1 (by rfl) ⟨2366870, by rfl⟩ : syracuseStep 3155827 = 4733741) B4733741
theorem B1869699 : Blo 1869636 1869699 := bstep (se 1 (by rfl) ⟨1402274, by rfl⟩ : syracuseStep 1869699 = 2804549) B2804549
theorem B1869715 : Blo 1869636 1869715 := bstep (se 1 (by rfl) ⟨1402286, by rfl⟩ : syracuseStep 1869715 = 2804573) B2804573
theorem B2664353 : Blo 1869636 2664353 := bstep (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) B1998265
theorem B1869731 : Blo 1869636 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B1869747 : Blo 1869636 1869747 := bstep (se 1 (by rfl) ⟨1402310, by rfl⟩ : syracuseStep 1869747 = 2804621) B2804621
theorem B1869763 : Blo 1869636 1869763 := bstep (se 1 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 1869763 = 2804645) B2804645
theorem B1869779 : Blo 1869636 1869779 := bstep (se 1 (by rfl) ⟨1402334, by rfl⟩ : syracuseStep 1869779 = 2804669) B2804669
theorem B1869795 : Blo 1869636 1869795 := bstep (se 1 (by rfl) ⟨1402346, by rfl⟩ : syracuseStep 1869795 = 2804693) B2804693
theorem B1869811 : Blo 1869636 1869811 := bstep (se 1 (by rfl) ⟨1402358, by rfl⟩ : syracuseStep 1869811 = 2804717) B2804717
theorem B3155969 : Blo 1869636 3155969 := bstep (se 2 (by rfl) ⟨1183488, by rfl⟩ : syracuseStep 3155969 = 2366977) B2366977
theorem B1869827 : Blo 1869636 1869827 := bstep (se 1 (by rfl) ⟨1402370, by rfl⟩ : syracuseStep 1869827 = 2804741) B2804741
theorem B1869843 : Blo 1869636 1869843 := bstep (se 1 (by rfl) ⟨1402382, by rfl⟩ : syracuseStep 1869843 = 2804765) B2804765
theorem B1869859 : Blo 1869636 1869859 := bstep (se 1 (by rfl) ⟨1402394, by rfl⟩ : syracuseStep 1869859 = 2804789) B2804789
theorem B1869875 : Blo 1869636 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B2246707 : Blo 1869636 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B1869891 : Blo 1869636 1869891 := bstep (se 1 (by rfl) ⟨1402418, by rfl⟩ : syracuseStep 1869891 = 2804837) B2804837
theorem B1869907 : Blo 1869636 1869907 := bstep (se 1 (by rfl) ⟨1402430, by rfl⟩ : syracuseStep 1869907 = 2804861) B2804861
theorem B1869923 : Blo 1869636 1869923 := bstep (se 1 (by rfl) ⟨1402442, by rfl⟩ : syracuseStep 1869923 = 2804885) B2804885
theorem B1869939 : Blo 1869636 1869939 := bstep (se 1 (by rfl) ⟨1402454, by rfl⟩ : syracuseStep 1869939 = 2804909) B2804909
theorem B3156097 : Blo 1869636 3156097 := bstep (se 2 (by rfl) ⟨1183536, by rfl⟩ : syracuseStep 3156097 = 2367073) B2367073
theorem B1869955 : Blo 1869636 1869955 := bstep (se 1 (by rfl) ⟨1402466, by rfl⟩ : syracuseStep 1869955 = 2804933) B2804933
theorem B1869971 : Blo 1869636 1869971 := bstep (se 1 (by rfl) ⟨1402478, by rfl⟩ : syracuseStep 1869971 = 2804957) B2804957
theorem B1869987 : Blo 1869636 1869987 := bstep (se 1 (by rfl) ⟨1402490, by rfl⟩ : syracuseStep 1869987 = 2804981) B2804981
theorem B3156131 : Blo 1869636 3156131 := bstep (se 1 (by rfl) ⟨2367098, by rfl⟩ : syracuseStep 3156131 = 4734197) B4734197
theorem B6310061 : Blo 1869636 6310061 := bstep (se 3 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 6310061 = 2366273) B2366273
theorem B1870003 : Blo 1869636 1870003 := bstep (se 1 (by rfl) ⟨1402502, by rfl⟩ : syracuseStep 1870003 = 2805005) B2805005
theorem B1870019 : Blo 1869636 1870019 := bstep (se 1 (by rfl) ⟨1402514, by rfl⟩ : syracuseStep 1870019 = 2805029) B2805029
theorem B5687491 : Blo 1869636 5687491 := bstep (se 1 (by rfl) ⟨4265618, by rfl⟩ : syracuseStep 5687491 = 8531237) B8531237
theorem B6400205 : Blo 1869636 6400205 := bstep (se 3 (by rfl) ⟨1200038, by rfl⟩ : syracuseStep 6400205 = 2400077) B2400077
theorem B1870035 : Blo 1869636 1870035 := bstep (se 1 (by rfl) ⟨1402526, by rfl⟩ : syracuseStep 1870035 = 2805053) B2805053
theorem B6310115 : Blo 1869636 6310115 := bstep (se 1 (by rfl) ⟨4732586, by rfl⟩ : syracuseStep 6310115 = 9465173) B9465173
theorem B1870051 : Blo 1869636 1870051 := bstep (se 1 (by rfl) ⟨1402538, by rfl⟩ : syracuseStep 1870051 = 2805077) B2805077
theorem B1870067 : Blo 1869636 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1870083 : Blo 1869636 1870083 := bstep (se 1 (by rfl) ⟨1402562, by rfl⟩ : syracuseStep 1870083 = 2805125) B2805125
theorem B6400259 : Blo 1869636 6400259 := bstep (se 1 (by rfl) ⟨4800194, by rfl⟩ : syracuseStep 6400259 = 9600389) B9600389
theorem B1870099 : Blo 1869636 1870099 := bstep (se 1 (by rfl) ⟨1402574, by rfl⟩ : syracuseStep 1870099 = 2805149) B2805149
theorem B1870115 : Blo 1869636 1870115 := bstep (se 1 (by rfl) ⟨1402586, by rfl⟩ : syracuseStep 1870115 = 2805173) B2805173
theorem B3156259 : Blo 1869636 3156259 := bstep (se 1 (by rfl) ⟨2367194, by rfl⟩ : syracuseStep 3156259 = 4734389) B4734389
theorem B1870131 : Blo 1869636 1870131 := bstep (se 1 (by rfl) ⟨1402598, by rfl⟩ : syracuseStep 1870131 = 2805197) B2805197
theorem B1870147 : Blo 1869636 1870147 := bstep (se 1 (by rfl) ⟨1402610, by rfl⟩ : syracuseStep 1870147 = 2805221) B2805221
theorem B1870163 : Blo 1869636 1870163 := bstep (se 1 (by rfl) ⟨1402622, by rfl⟩ : syracuseStep 1870163 = 2805245) B2805245
theorem B1870179 : Blo 1869636 1870179 := bstep (se 1 (by rfl) ⟨1402634, by rfl⟩ : syracuseStep 1870179 = 2805269) B2805269
theorem B1870195 : Blo 1869636 1870195 := bstep (se 1 (by rfl) ⟨1402646, by rfl⟩ : syracuseStep 1870195 = 2805293) B2805293
theorem B1870211 : Blo 1869636 1870211 := bstep (se 1 (by rfl) ⟨1402658, by rfl⟩ : syracuseStep 1870211 = 2805317) B2805317
theorem B1870227 : Blo 1869636 1870227 := bstep (se 1 (by rfl) ⟨1402670, by rfl⟩ : syracuseStep 1870227 = 2805341) B2805341
theorem B1870243 : Blo 1869636 1870243 := bstep (se 1 (by rfl) ⟨1402682, by rfl⟩ : syracuseStep 1870243 = 2805365) B2805365
theorem B3156401 : Blo 1869636 3156401 := bstep (se 2 (by rfl) ⟨1183650, by rfl⟩ : syracuseStep 3156401 = 2367301) B2367301
theorem B1870259 : Blo 1869636 1870259 := bstep (se 1 (by rfl) ⟨1402694, by rfl⟩ : syracuseStep 1870259 = 2805389) B2805389
theorem B1870275 : Blo 1869636 1870275 := bstep (se 1 (by rfl) ⟨1402706, by rfl⟩ : syracuseStep 1870275 = 2805413) B2805413
theorem B6752717 : Blo 1869636 6752717 := bstep (se 3 (by rfl) ⟨1266134, by rfl⟩ : syracuseStep 6752717 = 2532269) B2532269
theorem B5990861 : Blo 1869636 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B1870291 : Blo 1869636 1870291 := bstep (se 1 (by rfl) ⟨1402718, by rfl⟩ : syracuseStep 1870291 = 2805437) B2805437
theorem B1870307 : Blo 1869636 1870307 := bstep (se 1 (by rfl) ⟨1402730, by rfl⟩ : syracuseStep 1870307 = 2805461) B2805461
theorem B6310385 : Blo 1869636 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B1870323 : Blo 1869636 1870323 := bstep (se 1 (by rfl) ⟨1402742, by rfl⟩ : syracuseStep 1870323 = 2805485) B2805485
theorem B1870339 : Blo 1869636 1870339 := bstep (se 1 (by rfl) ⟨1402754, by rfl⟩ : syracuseStep 1870339 = 2805509) B2805509
theorem B1870355 : Blo 1869636 1870355 := bstep (se 1 (by rfl) ⟨1402766, by rfl⟩ : syracuseStep 1870355 = 2805533) B2805533
theorem B1870371 : Blo 1869636 1870371 := bstep (se 1 (by rfl) ⟨1402778, by rfl⟩ : syracuseStep 1870371 = 2805557) B2805557
theorem B3156529 : Blo 1869636 3156529 := bstep (se 2 (by rfl) ⟨1183698, by rfl⟩ : syracuseStep 3156529 = 2367397) B2367397
theorem B1870387 : Blo 1869636 1870387 := bstep (se 1 (by rfl) ⟨1402790, by rfl⟩ : syracuseStep 1870387 = 2805581) B2805581
theorem B80939573 : Blo 1869636 80939573 := bstep (se 5 (by rfl) ⟨3794042, by rfl⟩ : syracuseStep 80939573 = 7588085) B7588085
theorem B1870403 : Blo 1869636 1870403 := bstep (se 1 (by rfl) ⟨1402802, by rfl⟩ : syracuseStep 1870403 = 2805605) B2805605
theorem B5327441 : Blo 1869636 5327441 := bstep (se 2 (by rfl) ⟨1997790, by rfl⟩ : syracuseStep 5327441 = 3995581) B3995581
theorem B1870419 : Blo 1869636 1870419 := bstep (se 1 (by rfl) ⟨1402814, by rfl⟩ : syracuseStep 1870419 = 2805629) B2805629
theorem B3156563 : Blo 1869636 3156563 := bstep (se 1 (by rfl) ⟨2367422, by rfl⟩ : syracuseStep 3156563 = 4734845) B4734845
theorem B1870435 : Blo 1869636 1870435 := bstep (se 1 (by rfl) ⟨1402826, by rfl⟩ : syracuseStep 1870435 = 2805653) B2805653
theorem B9472625 : Blo 1869636 9472625 := bstep (se 2 (by rfl) ⟨3552234, by rfl⟩ : syracuseStep 9472625 = 7104469) B7104469
theorem B1870451 : Blo 1869636 1870451 := bstep (se 1 (by rfl) ⟨1402838, by rfl⟩ : syracuseStep 1870451 = 2805677) B2805677
theorem B1870467 : Blo 1869636 1870467 := bstep (se 1 (by rfl) ⟨1402850, by rfl⟩ : syracuseStep 1870467 = 2805701) B2805701
theorem B1870483 : Blo 1869636 1870483 := bstep (se 1 (by rfl) ⟨1402862, by rfl⟩ : syracuseStep 1870483 = 2805725) B2805725
theorem B1870499 : Blo 1869636 1870499 := bstep (se 1 (by rfl) ⟨1402874, by rfl⟩ : syracuseStep 1870499 = 2805749) B2805749
theorem B1870515 : Blo 1869636 1870515 := bstep (se 1 (by rfl) ⟨1402886, by rfl⟩ : syracuseStep 1870515 = 2805773) B2805773
theorem B1870531 : Blo 1869636 1870531 := bstep (se 1 (by rfl) ⟨1402898, by rfl⟩ : syracuseStep 1870531 = 2805797) B2805797
theorem B7105229 : Blo 1869636 7105229 := bstep (se 3 (by rfl) ⟨1332230, by rfl⟩ : syracuseStep 7105229 = 2664461) B2664461
theorem B1870547 : Blo 1869636 1870547 := bstep (se 1 (by rfl) ⟨1402910, by rfl⟩ : syracuseStep 1870547 = 2805821) B2805821
theorem B3156691 : Blo 1869636 3156691 := bstep (se 1 (by rfl) ⟨2367518, by rfl⟩ : syracuseStep 3156691 = 4735037) B4735037
theorem B1870563 : Blo 1869636 1870563 := bstep (se 1 (by rfl) ⟨1402922, by rfl⟩ : syracuseStep 1870563 = 2805845) B2805845
theorem B2845411 : Blo 1869636 2845411 := bstep (se 1 (by rfl) ⟨2134058, by rfl⟩ : syracuseStep 2845411 = 4268117) B4268117
theorem B2804465 : Blo 1869636 2804465 := bstep (se 2 (by rfl) ⟨1051674, by rfl⟩ : syracuseStep 2804465 = 2103349) B2103349
theorem B7990001 : Blo 1869636 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B1870579 : Blo 1869636 1870579 := bstep (se 1 (by rfl) ⟨1402934, by rfl⟩ : syracuseStep 1870579 = 2805869) B2805869
theorem B8653553 : Blo 1869636 8653553 := bstep (se 2 (by rfl) ⟨3245082, by rfl⟩ : syracuseStep 8653553 = 6490165) B6490165
theorem B2804483 : Blo 1869636 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B1870595 : Blo 1869636 1870595 := bstep (se 1 (by rfl) ⟨1402946, by rfl⟩ : syracuseStep 1870595 = 2805893) B2805893
theorem B1870611 : Blo 1869636 1870611 := bstep (se 1 (by rfl) ⟨1402958, by rfl⟩ : syracuseStep 1870611 = 2805917) B2805917
theorem B2804513 : Blo 1869636 2804513 := bstep (se 2 (by rfl) ⟨1051692, by rfl⟩ : syracuseStep 2804513 = 2103385) B2103385
theorem B1870627 : Blo 1869636 1870627 := bstep (se 1 (by rfl) ⟨1402970, by rfl⟩ : syracuseStep 1870627 = 2805941) B2805941
theorem B2804531 : Blo 1869636 2804531 := bstep (se 1 (by rfl) ⟨2103398, by rfl⟩ : syracuseStep 2804531 = 4206797) B4206797
theorem B1870643 : Blo 1869636 1870643 := bstep (se 1 (by rfl) ⟨1402982, by rfl⟩ : syracuseStep 1870643 = 2805965) B2805965
theorem B1870659 : Blo 1869636 1870659 := bstep (se 1 (by rfl) ⟨1402994, by rfl⟩ : syracuseStep 1870659 = 2805989) B2805989
theorem B5401421 : Blo 1869636 5401421 := bstep (se 3 (by rfl) ⟨1012766, by rfl⟩ : syracuseStep 5401421 = 2025533) B2025533
theorem B2804561 : Blo 1869636 2804561 := bstep (se 2 (by rfl) ⟨1051710, by rfl⟩ : syracuseStep 2804561 = 2103421) B2103421
theorem B1870675 : Blo 1869636 1870675 := bstep (se 1 (by rfl) ⟨1403006, by rfl⟩ : syracuseStep 1870675 = 2806013) B2806013
theorem B3156833 : Blo 1869636 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B2804579 : Blo 1869636 2804579 := bstep (se 1 (by rfl) ⟨2103434, by rfl⟩ : syracuseStep 2804579 = 4206869) B4206869
theorem B1870691 : Blo 1869636 1870691 := bstep (se 1 (by rfl) ⟨1403018, by rfl⟩ : syracuseStep 1870691 = 2806037) B2806037
theorem B1870707 : Blo 1869636 1870707 := bstep (se 1 (by rfl) ⟨1403030, by rfl⟩ : syracuseStep 1870707 = 2806061) B2806061
theorem B2804609 : Blo 1869636 2804609 := bstep (se 2 (by rfl) ⟨1051728, by rfl⟩ : syracuseStep 2804609 = 2103457) B2103457
theorem B1870723 : Blo 1869636 1870723 := bstep (se 1 (by rfl) ⟨1403042, by rfl⟩ : syracuseStep 1870723 = 2806085) B2806085
theorem B2804627 : Blo 1869636 2804627 := bstep (se 1 (by rfl) ⟨2103470, by rfl⟩ : syracuseStep 2804627 = 4206941) B4206941
theorem B1870739 : Blo 1869636 1870739 := bstep (se 1 (by rfl) ⟨1403054, by rfl⟩ : syracuseStep 1870739 = 2806109) B2806109
theorem B1870755 : Blo 1869636 1870755 := bstep (se 1 (by rfl) ⟨1403066, by rfl⟩ : syracuseStep 1870755 = 2806133) B2806133
theorem B2804657 : Blo 1869636 2804657 := bstep (se 2 (by rfl) ⟨1051746, by rfl⟩ : syracuseStep 2804657 = 2103493) B2103493
theorem B1870771 : Blo 1869636 1870771 := bstep (se 1 (by rfl) ⟨1403078, by rfl⟩ : syracuseStep 1870771 = 2806157) B2806157
theorem B2804675 : Blo 1869636 2804675 := bstep (se 1 (by rfl) ⟨2103506, by rfl⟩ : syracuseStep 2804675 = 4207013) B4207013
theorem B1870787 : Blo 1869636 1870787 := bstep (se 1 (by rfl) ⟨1403090, by rfl⟩ : syracuseStep 1870787 = 2806181) B2806181
theorem B5688269 : Blo 1869636 5688269 := bstep (se 3 (by rfl) ⟨1066550, by rfl⟩ : syracuseStep 5688269 = 2133101) B2133101
theorem B1870803 : Blo 1869636 1870803 := bstep (se 1 (by rfl) ⟨1403102, by rfl⟩ : syracuseStep 1870803 = 2806205) B2806205
theorem B2804705 : Blo 1869636 2804705 := bstep (se 2 (by rfl) ⟨1051764, by rfl⟩ : syracuseStep 2804705 = 2103529) B2103529
theorem B3156961 : Blo 1869636 3156961 := bstep (se 2 (by rfl) ⟨1183860, by rfl⟩ : syracuseStep 3156961 = 2367721) B2367721
theorem B1870819 : Blo 1869636 1870819 := bstep (se 1 (by rfl) ⟨1403114, by rfl⟩ : syracuseStep 1870819 = 2806229) B2806229
theorem B2804723 : Blo 1869636 2804723 := bstep (se 1 (by rfl) ⟨2103542, by rfl⟩ : syracuseStep 2804723 = 4207085) B4207085
theorem B1870835 : Blo 1869636 1870835 := bstep (se 1 (by rfl) ⟨1403126, by rfl⟩ : syracuseStep 1870835 = 2806253) B2806253
theorem B3156995 : Blo 1869636 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B1870851 : Blo 1869636 1870851 := bstep (se 1 (by rfl) ⟨1403138, by rfl⟩ : syracuseStep 1870851 = 2806277) B2806277
theorem B6310925 : Blo 1869636 6310925 := bstep (se 3 (by rfl) ⟨1183298, by rfl⟩ : syracuseStep 6310925 = 2366597) B2366597
theorem B2804753 : Blo 1869636 2804753 := bstep (se 2 (by rfl) ⟨1051782, by rfl⟩ : syracuseStep 2804753 = 2103565) B2103565
theorem B1870867 : Blo 1869636 1870867 := bstep (se 1 (by rfl) ⟨1403150, by rfl⟩ : syracuseStep 1870867 = 2806301) B2806301
theorem B2804771 : Blo 1869636 2804771 := bstep (se 1 (by rfl) ⟨2103578, by rfl⟩ : syracuseStep 2804771 = 4207157) B4207157
theorem B1870883 : Blo 1869636 1870883 := bstep (se 1 (by rfl) ⟨1403162, by rfl⟩ : syracuseStep 1870883 = 2806325) B2806325
theorem B1870899 : Blo 1869636 1870899 := bstep (se 1 (by rfl) ⟨1403174, by rfl⟩ : syracuseStep 1870899 = 2806349) B2806349
theorem B2804801 : Blo 1869636 2804801 := bstep (se 2 (by rfl) ⟨1051800, by rfl⟩ : syracuseStep 2804801 = 2103601) B2103601
theorem B6310979 : Blo 1869636 6310979 := bstep (se 1 (by rfl) ⟨4733234, by rfl⟩ : syracuseStep 6310979 = 9466469) B9466469
theorem B1870915 : Blo 1869636 1870915 := bstep (se 1 (by rfl) ⟨1403186, by rfl⟩ : syracuseStep 1870915 = 2806373) B2806373
theorem B10652741 : Blo 1869636 10652741 := bstep (se 4 (by rfl) ⟨998694, by rfl⟩ : syracuseStep 10652741 = 1997389) B1997389
theorem B2804819 : Blo 1869636 2804819 := bstep (se 1 (by rfl) ⟨2103614, by rfl⟩ : syracuseStep 2804819 = 4207229) B4207229
theorem B1870931 : Blo 1869636 1870931 := bstep (se 1 (by rfl) ⟨1403198, by rfl⟩ : syracuseStep 1870931 = 2806397) B2806397
theorem B1870947 : Blo 1869636 1870947 := bstep (se 1 (by rfl) ⟨1403210, by rfl⟩ : syracuseStep 1870947 = 2806421) B2806421
theorem B2804849 : Blo 1869636 2804849 := bstep (se 2 (by rfl) ⟨1051818, by rfl⟩ : syracuseStep 2804849 = 2103637) B2103637
theorem B3550321 : Blo 1869636 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B1870963 : Blo 1869636 1870963 := bstep (se 1 (by rfl) ⟨1403222, by rfl⟩ : syracuseStep 1870963 = 2806445) B2806445
theorem B2804867 : Blo 1869636 2804867 := bstep (se 1 (by rfl) ⟨2103650, by rfl⟩ : syracuseStep 2804867 = 4207301) B4207301
theorem B3157123 : Blo 1869636 3157123 := bstep (se 1 (by rfl) ⟨2367842, by rfl⟩ : syracuseStep 3157123 = 4735685) B4735685
theorem B1870979 : Blo 1869636 1870979 := bstep (se 1 (by rfl) ⟨1403234, by rfl⟩ : syracuseStep 1870979 = 2806469) B2806469
theorem B5057677 : Blo 1869636 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B1870995 : Blo 1869636 1870995 := bstep (se 1 (by rfl) ⟨1403246, by rfl⟩ : syracuseStep 1870995 = 2806493) B2806493
theorem B2804897 : Blo 1869636 2804897 := bstep (se 2 (by rfl) ⟨1051836, by rfl⟩ : syracuseStep 2804897 = 2103673) B2103673
theorem B1871011 : Blo 1869636 1871011 := bstep (se 1 (by rfl) ⟨1403258, by rfl⟩ : syracuseStep 1871011 = 2806517) B2806517
theorem B2804915 : Blo 1869636 2804915 := bstep (se 1 (by rfl) ⟨2103686, by rfl⟩ : syracuseStep 2804915 = 4207373) B4207373
theorem B1871027 : Blo 1869636 1871027 := bstep (se 1 (by rfl) ⟨1403270, by rfl⟩ : syracuseStep 1871027 = 2806541) B2806541
theorem B1871043 : Blo 1869636 1871043 := bstep (se 1 (by rfl) ⟨1403282, by rfl⟩ : syracuseStep 1871043 = 2806565) B2806565
theorem B31952069 : Blo 1869636 31952069 := bstep (se 4 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 31952069 = 5991013) B5991013
theorem B2804945 : Blo 1869636 2804945 := bstep (se 2 (by rfl) ⟨1051854, by rfl⟩ : syracuseStep 2804945 = 2103709) B2103709
theorem B1871059 : Blo 1869636 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B2804963 : Blo 1869636 2804963 := bstep (se 1 (by rfl) ⟨2103722, by rfl⟩ : syracuseStep 2804963 = 4207445) B4207445
theorem B1871075 : Blo 1869636 1871075 := bstep (se 1 (by rfl) ⟨1403306, by rfl⟩ : syracuseStep 1871075 = 2806613) B2806613
theorem B1871091 : Blo 1869636 1871091 := bstep (se 1 (by rfl) ⟨1403318, by rfl⟩ : syracuseStep 1871091 = 2806637) B2806637
theorem B2804993 : Blo 1869636 2804993 := bstep (se 2 (by rfl) ⟨1051872, by rfl⟩ : syracuseStep 2804993 = 2103745) B2103745
theorem B3288323 : Blo 1869636 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B1871107 : Blo 1869636 1871107 := bstep (se 1 (by rfl) ⟨1403330, by rfl⟩ : syracuseStep 1871107 = 2806661) B2806661
theorem B3157265 : Blo 1869636 3157265 := bstep (se 2 (by rfl) ⟨1183974, by rfl⟩ : syracuseStep 3157265 = 2367949) B2367949
theorem B2805011 : Blo 1869636 2805011 := bstep (se 1 (by rfl) ⟨2103758, by rfl⟩ : syracuseStep 2805011 = 4207517) B4207517
theorem B1871123 : Blo 1869636 1871123 := bstep (se 1 (by rfl) ⟨1403342, by rfl⟩ : syracuseStep 1871123 = 2806685) B2806685
theorem B1871139 : Blo 1869636 1871139 := bstep (se 1 (by rfl) ⟨1403354, by rfl⟩ : syracuseStep 1871139 = 2806709) B2806709
theorem B2805041 : Blo 1869636 2805041 := bstep (se 2 (by rfl) ⟨1051890, by rfl⟩ : syracuseStep 2805041 = 2103781) B2103781
theorem B1871155 : Blo 1869636 1871155 := bstep (se 1 (by rfl) ⟨1403366, by rfl⟩ : syracuseStep 1871155 = 2806733) B2806733
theorem B3288385 : Blo 1869636 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2805059 : Blo 1869636 2805059 := bstep (se 1 (by rfl) ⟨2103794, by rfl⟩ : syracuseStep 2805059 = 4207589) B4207589
theorem B1871171 : Blo 1869636 1871171 := bstep (se 1 (by rfl) ⟨1403378, by rfl⟩ : syracuseStep 1871171 = 2806757) B2806757
theorem B6311249 : Blo 1869636 6311249 := bstep (se 2 (by rfl) ⟨2366718, by rfl⟩ : syracuseStep 6311249 = 4733437) B4733437
theorem B1871187 : Blo 1869636 1871187 := bstep (se 1 (by rfl) ⟨1403390, by rfl⟩ : syracuseStep 1871187 = 2806781) B2806781
theorem B2805089 : Blo 1869636 2805089 := bstep (se 2 (by rfl) ⟨1051908, by rfl⟩ : syracuseStep 2805089 = 2103817) B2103817
theorem B1871203 : Blo 1869636 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B5197169 : Blo 1869636 5197169 := bstep (se 2 (by rfl) ⟨1948938, by rfl⟩ : syracuseStep 5197169 = 3897877) B3897877
theorem B34614641 : Blo 1869636 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B2805107 : Blo 1869636 2805107 := bstep (se 1 (by rfl) ⟨2103830, by rfl⟩ : syracuseStep 2805107 = 4207661) B4207661
theorem B1871219 : Blo 1869636 1871219 := bstep (se 1 (by rfl) ⟨1403414, by rfl⟩ : syracuseStep 1871219 = 2806829) B2806829
theorem B1871235 : Blo 1869636 1871235 := bstep (se 1 (by rfl) ⟨1403426, by rfl⟩ : syracuseStep 1871235 = 2806853) B2806853
theorem B2805137 : Blo 1869636 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B3157393 : Blo 1869636 3157393 := bstep (se 2 (by rfl) ⟨1184022, by rfl⟩ : syracuseStep 3157393 = 2368045) B2368045
theorem B1871251 : Blo 1869636 1871251 := bstep (se 1 (by rfl) ⟨1403438, by rfl⟩ : syracuseStep 1871251 = 2806877) B2806877
theorem B2805155 : Blo 1869636 2805155 := bstep (se 1 (by rfl) ⟨2103866, by rfl⟩ : syracuseStep 2805155 = 4207733) B4207733
theorem B1871267 : Blo 1869636 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B3157427 : Blo 1869636 3157427 := bstep (se 1 (by rfl) ⟨2368070, by rfl⟩ : syracuseStep 3157427 = 4736141) B4736141
theorem B1871283 : Blo 1869636 1871283 := bstep (se 1 (by rfl) ⟨1403462, by rfl⟩ : syracuseStep 1871283 = 2806925) B2806925
theorem B2805185 : Blo 1869636 2805185 := bstep (se 2 (by rfl) ⟨1051944, by rfl⟩ : syracuseStep 2805185 = 2103889) B2103889
theorem B1871299 : Blo 1869636 1871299 := bstep (se 1 (by rfl) ⟨1403474, by rfl⟩ : syracuseStep 1871299 = 2806949) B2806949
theorem B2805203 : Blo 1869636 2805203 := bstep (se 1 (by rfl) ⟨2103902, by rfl⟩ : syracuseStep 2805203 = 4207805) B4207805
theorem B1871315 : Blo 1869636 1871315 := bstep (se 1 (by rfl) ⟨1403486, by rfl⟩ : syracuseStep 1871315 = 2806973) B2806973
theorem B1871331 : Blo 1869636 1871331 := bstep (se 1 (by rfl) ⟨1403498, by rfl⟩ : syracuseStep 1871331 = 2806997) B2806997
theorem B2805233 : Blo 1869636 2805233 := bstep (se 2 (by rfl) ⟨1051962, by rfl⟩ : syracuseStep 2805233 = 2103925) B2103925
theorem B1871347 : Blo 1869636 1871347 := bstep (se 1 (by rfl) ⟨1403510, by rfl⟩ : syracuseStep 1871347 = 2807021) B2807021
theorem B2805251 : Blo 1869636 2805251 := bstep (se 1 (by rfl) ⟨2103938, by rfl⟩ : syracuseStep 2805251 = 4207877) B4207877
theorem B1871363 : Blo 1869636 1871363 := bstep (se 1 (by rfl) ⟨1403522, by rfl⟩ : syracuseStep 1871363 = 2807045) B2807045
theorem B1871379 : Blo 1869636 1871379 := bstep (se 1 (by rfl) ⟨1403534, by rfl⟩ : syracuseStep 1871379 = 2807069) B2807069
theorem B2805281 : Blo 1869636 2805281 := bstep (se 2 (by rfl) ⟨1051980, by rfl⟩ : syracuseStep 2805281 = 2103961) B2103961
theorem B1871395 : Blo 1869636 1871395 := bstep (se 1 (by rfl) ⟨1403546, by rfl⟩ : syracuseStep 1871395 = 2807093) B2807093
theorem B2805299 : Blo 1869636 2805299 := bstep (se 1 (by rfl) ⟨2103974, by rfl⟩ : syracuseStep 2805299 = 4207949) B4207949
theorem B3157555 : Blo 1869636 3157555 := bstep (se 1 (by rfl) ⟨2368166, by rfl⟩ : syracuseStep 3157555 = 4736333) B4736333
theorem B21302837 : Blo 1869636 21302837 := bstep (se 5 (by rfl) ⟨998570, by rfl⟩ : syracuseStep 21302837 = 1997141) B1997141
theorem B1871411 : Blo 1869636 1871411 := bstep (se 1 (by rfl) ⟨1403558, by rfl⟩ : syracuseStep 1871411 = 2807117) B2807117
theorem B3993155 : Blo 1869636 3993155 := bstep (se 1 (by rfl) ⟨2994866, by rfl⟩ : syracuseStep 3993155 = 5989733) B5989733
theorem B1871427 : Blo 1869636 1871427 := bstep (se 1 (by rfl) ⟨1403570, by rfl⟩ : syracuseStep 1871427 = 2807141) B2807141
theorem B2805329 : Blo 1869636 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B1871443 : Blo 1869636 1871443 := bstep (se 1 (by rfl) ⟨1403582, by rfl⟩ : syracuseStep 1871443 = 2807165) B2807165
theorem B2805347 : Blo 1869636 2805347 := bstep (se 1 (by rfl) ⟨2104010, by rfl⟩ : syracuseStep 2805347 = 4208021) B4208021
theorem B1871459 : Blo 1869636 1871459 := bstep (se 1 (by rfl) ⟨1403594, by rfl⟩ : syracuseStep 1871459 = 2807189) B2807189
theorem B14200433 : Blo 1869636 14200433 := bstep (se 2 (by rfl) ⟨5325162, by rfl⟩ : syracuseStep 14200433 = 10650325) B10650325
theorem B3370609 : Blo 1869636 3370609 := bstep (se 2 (by rfl) ⟨1263978, by rfl⟩ : syracuseStep 3370609 = 2527957) B2527957
theorem B1871475 : Blo 1869636 1871475 := bstep (se 1 (by rfl) ⟨1403606, by rfl⟩ : syracuseStep 1871475 = 2807213) B2807213
theorem B2805377 : Blo 1869636 2805377 := bstep (se 2 (by rfl) ⟨1052016, by rfl⟩ : syracuseStep 2805377 = 2104033) B2104033
theorem B1871491 : Blo 1869636 1871491 := bstep (se 1 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 1871491 = 2807237) B2807237
theorem B2805395 : Blo 1869636 2805395 := bstep (se 1 (by rfl) ⟨2104046, by rfl⟩ : syracuseStep 2805395 = 4208093) B4208093
theorem B1871507 : Blo 1869636 1871507 := bstep (se 1 (by rfl) ⟨1403630, by rfl⟩ : syracuseStep 1871507 = 2807261) B2807261
theorem B1871523 : Blo 1869636 1871523 := bstep (se 1 (by rfl) ⟨1403642, by rfl⟩ : syracuseStep 1871523 = 2807285) B2807285
theorem B2805425 : Blo 1869636 2805425 := bstep (se 2 (by rfl) ⟨1052034, by rfl⟩ : syracuseStep 2805425 = 2104069) B2104069
theorem B1871539 : Blo 1869636 1871539 := bstep (se 1 (by rfl) ⟨1403654, by rfl⟩ : syracuseStep 1871539 = 2807309) B2807309
theorem B3157697 : Blo 1869636 3157697 := bstep (se 2 (by rfl) ⟨1184136, by rfl⟩ : syracuseStep 3157697 = 2368273) B2368273
theorem B2805443 : Blo 1869636 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B1871555 : Blo 1869636 1871555 := bstep (se 1 (by rfl) ⟨1403666, by rfl⟩ : syracuseStep 1871555 = 2807333) B2807333
theorem B1871571 : Blo 1869636 1871571 := bstep (se 1 (by rfl) ⟨1403678, by rfl⟩ : syracuseStep 1871571 = 2807357) B2807357
theorem B2805473 : Blo 1869636 2805473 := bstep (se 2 (by rfl) ⟨1052052, by rfl⟩ : syracuseStep 2805473 = 2104105) B2104105
theorem B1871587 : Blo 1869636 1871587 := bstep (se 1 (by rfl) ⟨1403690, by rfl⟩ : syracuseStep 1871587 = 2807381) B2807381
theorem B2805491 : Blo 1869636 2805491 := bstep (se 1 (by rfl) ⟨2104118, by rfl⟩ : syracuseStep 2805491 = 4208237) B4208237
theorem B1871603 : Blo 1869636 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B1871619 : Blo 1869636 1871619 := bstep (se 1 (by rfl) ⟨1403714, by rfl⟩ : syracuseStep 1871619 = 2807429) B2807429
theorem B2805521 : Blo 1869636 2805521 := bstep (se 2 (by rfl) ⟨1052070, by rfl⟩ : syracuseStep 2805521 = 2104141) B2104141
theorem B2526995 : Blo 1869636 2526995 := bstep (se 1 (by rfl) ⟨1895246, by rfl⟩ : syracuseStep 2526995 = 3790493) B3790493
theorem B1871635 : Blo 1869636 1871635 := bstep (se 1 (by rfl) ⟨1403726, by rfl⟩ : syracuseStep 1871635 = 2807453) B2807453
theorem B2805539 : Blo 1869636 2805539 := bstep (se 1 (by rfl) ⟨2104154, by rfl⟩ : syracuseStep 2805539 = 4208309) B4208309
theorem B2805569 : Blo 1869636 2805569 := bstep (se 2 (by rfl) ⟨1052088, by rfl⟩ : syracuseStep 2805569 = 2104177) B2104177
theorem B3157825 : Blo 1869636 3157825 := bstep (se 2 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 3157825 = 2368369) B2368369
theorem B3600209 : Blo 1869636 3600209 := bstep (se 2 (by rfl) ⟨1350078, by rfl⟩ : syracuseStep 3600209 = 2700157) B2700157
theorem B2805587 : Blo 1869636 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B3157859 : Blo 1869636 3157859 := bstep (se 1 (by rfl) ⟨2368394, by rfl⟩ : syracuseStep 3157859 = 4736789) B4736789
theorem B6311789 : Blo 1869636 6311789 := bstep (se 3 (by rfl) ⟨1183460, by rfl⟩ : syracuseStep 6311789 = 2366921) B2366921
theorem B2805617 : Blo 1869636 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B2805635 : Blo 1869636 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B10801037 : Blo 1869636 10801037 := bstep (se 3 (by rfl) ⟨2025194, by rfl⟩ : syracuseStep 10801037 = 4050389) B4050389
theorem B2805665 : Blo 1869636 2805665 := bstep (se 2 (by rfl) ⟨1052124, by rfl⟩ : syracuseStep 2805665 = 2104249) B2104249
theorem B6311843 : Blo 1869636 6311843 := bstep (se 1 (by rfl) ⟨4733882, by rfl⟩ : syracuseStep 6311843 = 9467765) B9467765
theorem B2805683 : Blo 1869636 2805683 := bstep (se 1 (by rfl) ⟨2104262, by rfl⟩ : syracuseStep 2805683 = 4208525) B4208525
theorem B2805713 : Blo 1869636 2805713 := bstep (se 2 (by rfl) ⟨1052142, by rfl⟩ : syracuseStep 2805713 = 2104285) B2104285
theorem B2805731 : Blo 1869636 2805731 := bstep (se 1 (by rfl) ⟨2104298, by rfl⟩ : syracuseStep 2805731 = 4208597) B4208597
theorem B3157987 : Blo 1869636 3157987 := bstep (se 1 (by rfl) ⟨2368490, by rfl⟩ : syracuseStep 3157987 = 4736981) B4736981
theorem B2805761 : Blo 1869636 2805761 := bstep (se 2 (by rfl) ⟨1052160, by rfl⟩ : syracuseStep 2805761 = 2104321) B2104321
theorem B5328899 : Blo 1869636 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B3993617 : Blo 1869636 3993617 := bstep (se 2 (by rfl) ⟨1497606, by rfl⟩ : syracuseStep 3993617 = 2995213) B2995213
theorem B2805779 : Blo 1869636 2805779 := bstep (se 1 (by rfl) ⟨2104334, by rfl⟩ : syracuseStep 2805779 = 4208669) B4208669
theorem B9474083 : Blo 1869636 9474083 := bstep (se 1 (by rfl) ⟨7105562, by rfl⟩ : syracuseStep 9474083 = 14211125) B14211125
theorem B2805809 : Blo 1869636 2805809 := bstep (se 2 (by rfl) ⟨1052178, by rfl⟩ : syracuseStep 2805809 = 2104357) B2104357
theorem B2805827 : Blo 1869636 2805827 := bstep (se 1 (by rfl) ⟨2104370, by rfl⟩ : syracuseStep 2805827 = 4208741) B4208741
theorem B2805857 : Blo 1869636 2805857 := bstep (se 2 (by rfl) ⟨1052196, by rfl⟩ : syracuseStep 2805857 = 2104393) B2104393
theorem B3158129 : Blo 1869636 3158129 := bstep (se 2 (by rfl) ⟨1184298, by rfl⟩ : syracuseStep 3158129 = 2368597) B2368597
theorem B2805875 : Blo 1869636 2805875 := bstep (se 1 (by rfl) ⟨2104406, by rfl⟩ : syracuseStep 2805875 = 4208813) B4208813
theorem B2805905 : Blo 1869636 2805905 := bstep (se 2 (by rfl) ⟨1052214, by rfl⟩ : syracuseStep 2805905 = 2104429) B2104429
theorem B3551377 : Blo 1869636 3551377 := bstep (se 2 (by rfl) ⟨1331766, by rfl⟩ : syracuseStep 3551377 = 2663533) B2663533
theorem B2805923 : Blo 1869636 2805923 := bstep (se 1 (by rfl) ⟨2104442, by rfl⟩ : syracuseStep 2805923 = 4208885) B4208885
theorem B6312113 : Blo 1869636 6312113 := bstep (se 2 (by rfl) ⟨2367042, by rfl⟩ : syracuseStep 6312113 = 4734085) B4734085
theorem B2805953 : Blo 1869636 2805953 := bstep (se 2 (by rfl) ⟨1052232, by rfl⟩ : syracuseStep 2805953 = 2104465) B2104465
theorem B5992643 : Blo 1869636 5992643 := bstep (se 1 (by rfl) ⟨4494482, by rfl⟩ : syracuseStep 5992643 = 8988965) B8988965
theorem B2805971 : Blo 1869636 2805971 := bstep (se 1 (by rfl) ⟨2104478, by rfl⟩ : syracuseStep 2805971 = 4208957) B4208957
theorem B4206833 : Blo 1869636 4206833 := bstep (se 2 (by rfl) ⟨1577562, by rfl⟩ : syracuseStep 4206833 = 3155125) B3155125
theorem B2806001 : Blo 1869636 2806001 := bstep (se 2 (by rfl) ⟨1052250, by rfl⟩ : syracuseStep 2806001 = 2104501) B2104501
theorem B3158257 : Blo 1869636 3158257 := bstep (se 2 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 3158257 = 2368693) B2368693
theorem B4206851 : Blo 1869636 4206851 := bstep (se 1 (by rfl) ⟨3155138, by rfl⟩ : syracuseStep 4206851 = 6310277) B6310277
theorem B2806019 : Blo 1869636 2806019 := bstep (se 1 (by rfl) ⟨2104514, by rfl⟩ : syracuseStep 2806019 = 4209029) B4209029
theorem B3158291 : Blo 1869636 3158291 := bstep (se 1 (by rfl) ⟨2368718, by rfl⟩ : syracuseStep 3158291 = 4737437) B4737437
theorem B80867605 : Blo 1869636 80867605 := bstep (se 6 (by rfl) ⟨1895334, by rfl⟩ : syracuseStep 80867605 = 3790669) B3790669
theorem B2806049 : Blo 1869636 2806049 := bstep (se 2 (by rfl) ⟨1052268, by rfl⟩ : syracuseStep 2806049 = 2104537) B2104537
theorem B11981105 : Blo 1869636 11981105 := bstep (se 2 (by rfl) ⟨4492914, by rfl⟩ : syracuseStep 11981105 = 8985829) B8985829
theorem B2806067 : Blo 1869636 2806067 := bstep (se 1 (by rfl) ⟨2104550, by rfl⟩ : syracuseStep 2806067 = 4209101) B4209101
theorem B2806097 : Blo 1869636 2806097 := bstep (se 2 (by rfl) ⟨1052286, by rfl⟩ : syracuseStep 2806097 = 2104573) B2104573
theorem B2806115 : Blo 1869636 2806115 := bstep (se 1 (by rfl) ⟨2104586, by rfl⟩ : syracuseStep 2806115 = 4209173) B4209173
theorem B2806145 : Blo 1869636 2806145 := bstep (se 2 (by rfl) ⟨1052304, by rfl⟩ : syracuseStep 2806145 = 2104609) B2104609
theorem B7991693 : Blo 1869636 7991693 := bstep (se 3 (by rfl) ⟨1498442, by rfl⟩ : syracuseStep 7991693 = 2996885) B2996885
theorem B2806163 : Blo 1869636 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B2806193 : Blo 1869636 2806193 := bstep (se 2 (by rfl) ⟨1052322, by rfl⟩ : syracuseStep 2806193 = 2104645) B2104645
theorem B2806211 : Blo 1869636 2806211 := bstep (se 1 (by rfl) ⟨2104658, by rfl⟩ : syracuseStep 2806211 = 4209317) B4209317
theorem B2806241 : Blo 1869636 2806241 := bstep (se 2 (by rfl) ⟨1052340, by rfl⟩ : syracuseStep 2806241 = 2104681) B2104681
theorem B2806259 : Blo 1869636 2806259 := bstep (se 1 (by rfl) ⟨2104694, by rfl⟩ : syracuseStep 2806259 = 4209389) B4209389
theorem B4207121 : Blo 1869636 4207121 := bstep (se 2 (by rfl) ⟨1577670, by rfl⟩ : syracuseStep 4207121 = 3155341) B3155341
theorem B2806289 : Blo 1869636 2806289 := bstep (se 2 (by rfl) ⟨1052358, by rfl⟩ : syracuseStep 2806289 = 2104717) B2104717
theorem B4207139 : Blo 1869636 4207139 := bstep (se 1 (by rfl) ⟨3155354, by rfl⟩ : syracuseStep 4207139 = 6310709) B6310709
theorem B2806307 : Blo 1869636 2806307 := bstep (se 1 (by rfl) ⟨2104730, by rfl⟩ : syracuseStep 2806307 = 4209461) B4209461
theorem B3551779 : Blo 1869636 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B2806337 : Blo 1869636 2806337 := bstep (se 2 (by rfl) ⟨1052376, by rfl⟩ : syracuseStep 2806337 = 2104753) B2104753
theorem B3551825 : Blo 1869636 3551825 := bstep (se 2 (by rfl) ⟨1331934, by rfl⟩ : syracuseStep 3551825 = 2663869) B2663869
theorem B2806355 : Blo 1869636 2806355 := bstep (se 1 (by rfl) ⟨2104766, by rfl⟩ : syracuseStep 2806355 = 4209533) B4209533
theorem B2806385 : Blo 1869636 2806385 := bstep (se 2 (by rfl) ⟨1052394, by rfl⟩ : syracuseStep 2806385 = 2104789) B2104789
theorem B3371633 : Blo 1869636 3371633 := bstep (se 2 (by rfl) ⟨1264362, by rfl⟩ : syracuseStep 3371633 = 2528725) B2528725
theorem B2994803 : Blo 1869636 2994803 := bstep (se 1 (by rfl) ⟨2246102, by rfl⟩ : syracuseStep 2994803 = 4492205) B4492205
theorem B2806403 : Blo 1869636 2806403 := bstep (se 1 (by rfl) ⟨2104802, by rfl⟩ : syracuseStep 2806403 = 4209605) B4209605
theorem B2994835 : Blo 1869636 2994835 := bstep (se 1 (by rfl) ⟨2246126, by rfl⟩ : syracuseStep 2994835 = 4492253) B4492253
theorem B2806433 : Blo 1869636 2806433 := bstep (se 2 (by rfl) ⟨1052412, by rfl⟩ : syracuseStep 2806433 = 2104825) B2104825
theorem B2806451 : Blo 1869636 2806451 := bstep (se 1 (by rfl) ⟨2104838, by rfl⟩ : syracuseStep 2806451 = 4209677) B4209677
theorem B6312653 : Blo 1869636 6312653 := bstep (se 3 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 6312653 = 2367245) B2367245
theorem B2806481 : Blo 1869636 2806481 := bstep (se 2 (by rfl) ⟨1052430, by rfl⟩ : syracuseStep 2806481 = 2104861) B2104861
theorem B2806499 : Blo 1869636 2806499 := bstep (se 1 (by rfl) ⟨2104874, by rfl⟩ : syracuseStep 2806499 = 4209749) B4209749
theorem B2806529 : Blo 1869636 2806529 := bstep (se 2 (by rfl) ⟨1052448, by rfl⟩ : syracuseStep 2806529 = 2104897) B2104897
theorem B6312707 : Blo 1869636 6312707 := bstep (se 1 (by rfl) ⟨4734530, by rfl⟩ : syracuseStep 6312707 = 9469061) B9469061
theorem B6402833 : Blo 1869636 6402833 := bstep (se 2 (by rfl) ⟨2401062, by rfl⟩ : syracuseStep 6402833 = 4802125) B4802125
theorem B2806547 : Blo 1869636 2806547 := bstep (se 1 (by rfl) ⟨2104910, by rfl⟩ : syracuseStep 2806547 = 4209821) B4209821
theorem B5329709 : Blo 1869636 5329709 := bstep (se 3 (by rfl) ⟨999320, by rfl⟩ : syracuseStep 5329709 = 1998641) B1998641
theorem B4207409 : Blo 1869636 4207409 := bstep (se 2 (by rfl) ⟨1577778, by rfl⟩ : syracuseStep 4207409 = 3155557) B3155557
theorem B2806577 : Blo 1869636 2806577 := bstep (se 2 (by rfl) ⟨1052466, by rfl⟩ : syracuseStep 2806577 = 2104933) B2104933
theorem B4207427 : Blo 1869636 4207427 := bstep (se 1 (by rfl) ⟨3155570, by rfl⟩ : syracuseStep 4207427 = 6311141) B6311141
theorem B2806595 : Blo 1869636 2806595 := bstep (se 1 (by rfl) ⟨2104946, by rfl⟩ : syracuseStep 2806595 = 4209893) B4209893
theorem B9474893 : Blo 1869636 9474893 := bstep (se 3 (by rfl) ⟨1776542, by rfl⟩ : syracuseStep 9474893 = 3553085) B3553085
theorem B2806625 : Blo 1869636 2806625 := bstep (se 2 (by rfl) ⟨1052484, by rfl⟩ : syracuseStep 2806625 = 2104969) B2104969
theorem B3552113 : Blo 1869636 3552113 := bstep (se 2 (by rfl) ⟨1332042, by rfl⟩ : syracuseStep 3552113 = 2664085) B2664085
theorem B2806643 : Blo 1869636 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B2806673 : Blo 1869636 2806673 := bstep (se 2 (by rfl) ⟨1052502, by rfl⟩ : syracuseStep 2806673 = 2105005) B2105005
theorem B2806691 : Blo 1869636 2806691 := bstep (se 1 (by rfl) ⟨2105018, by rfl⟩ : syracuseStep 2806691 = 4210037) B4210037
theorem B2806721 : Blo 1869636 2806721 := bstep (se 2 (by rfl) ⟨1052520, by rfl⟩ : syracuseStep 2806721 = 2105041) B2105041
theorem B2806739 : Blo 1869636 2806739 := bstep (se 1 (by rfl) ⟨2105054, by rfl⟩ : syracuseStep 2806739 = 4210109) B4210109
theorem B2806769 : Blo 1869636 2806769 := bstep (se 2 (by rfl) ⟨1052538, by rfl⟩ : syracuseStep 2806769 = 2105077) B2105077
theorem B2806787 : Blo 1869636 2806787 := bstep (se 1 (by rfl) ⟨2105090, by rfl⟩ : syracuseStep 2806787 = 4210181) B4210181
theorem B6927373 : Blo 1869636 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B6312977 : Blo 1869636 6312977 := bstep (se 2 (by rfl) ⟨2367366, by rfl⟩ : syracuseStep 6312977 = 4734733) B4734733
theorem B2806817 : Blo 1869636 2806817 := bstep (se 2 (by rfl) ⟨1052556, by rfl⟩ : syracuseStep 2806817 = 2105113) B2105113
theorem B7099427 : Blo 1869636 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B2806835 : Blo 1869636 2806835 := bstep (se 1 (by rfl) ⟨2105126, by rfl⟩ : syracuseStep 2806835 = 4210253) B4210253
theorem B15979589 : Blo 1869636 15979589 := bstep (se 4 (by rfl) ⟨1498086, by rfl⟩ : syracuseStep 15979589 = 2996173) B2996173
theorem B4207697 : Blo 1869636 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B2806865 : Blo 1869636 2806865 := bstep (se 2 (by rfl) ⟨1052574, by rfl⟩ : syracuseStep 2806865 = 2105149) B2105149
theorem B4207715 : Blo 1869636 4207715 := bstep (se 1 (by rfl) ⟨3155786, by rfl⟩ : syracuseStep 4207715 = 6311573) B6311573
theorem B2806883 : Blo 1869636 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B2806913 : Blo 1869636 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B2806931 : Blo 1869636 2806931 := bstep (se 1 (by rfl) ⟨2105198, by rfl⟩ : syracuseStep 2806931 = 4210397) B4210397
theorem B2806961 : Blo 1869636 2806961 := bstep (se 2 (by rfl) ⟨1052610, by rfl⟩ : syracuseStep 2806961 = 2105221) B2105221
theorem B2806979 : Blo 1869636 2806979 := bstep (se 1 (by rfl) ⟨2105234, by rfl⟩ : syracuseStep 2806979 = 4210469) B4210469
theorem B2807009 : Blo 1869636 2807009 := bstep (se 2 (by rfl) ⟨1052628, by rfl⟩ : syracuseStep 2807009 = 2105257) B2105257
theorem B2807027 : Blo 1869636 2807027 := bstep (se 1 (by rfl) ⟨2105270, by rfl⟩ : syracuseStep 2807027 = 4210541) B4210541
theorem B2807057 : Blo 1869636 2807057 := bstep (se 2 (by rfl) ⟨1052646, by rfl⟩ : syracuseStep 2807057 = 2105293) B2105293
theorem B3994915 : Blo 1869636 3994915 := bstep (se 1 (by rfl) ⟨2996186, by rfl⟩ : syracuseStep 3994915 = 5992373) B5992373
theorem B2807075 : Blo 1869636 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B2807105 : Blo 1869636 2807105 := bstep (se 2 (by rfl) ⟨1052664, by rfl⟩ : syracuseStep 2807105 = 2105329) B2105329
theorem B2807123 : Blo 1869636 2807123 := bstep (se 1 (by rfl) ⟨2105342, by rfl⟩ : syracuseStep 2807123 = 4210685) B4210685
theorem B4207985 : Blo 1869636 4207985 := bstep (se 2 (by rfl) ⟨1577994, by rfl⟩ : syracuseStep 4207985 = 3155989) B3155989
theorem B2807153 : Blo 1869636 2807153 := bstep (se 2 (by rfl) ⟨1052682, by rfl⟩ : syracuseStep 2807153 = 2105365) B2105365
theorem B4208003 : Blo 1869636 4208003 := bstep (se 1 (by rfl) ⟨3156002, by rfl⟩ : syracuseStep 4208003 = 6312005) B6312005
theorem B2807171 : Blo 1869636 2807171 := bstep (se 1 (by rfl) ⟨2105378, by rfl⟩ : syracuseStep 2807171 = 4210757) B4210757
theorem B2807201 : Blo 1869636 2807201 := bstep (se 2 (by rfl) ⟨1052700, by rfl⟩ : syracuseStep 2807201 = 2105401) B2105401
theorem B2807219 : Blo 1869636 2807219 := bstep (se 1 (by rfl) ⟨2105414, by rfl⟩ : syracuseStep 2807219 = 4210829) B4210829
theorem B2807249 : Blo 1869636 2807249 := bstep (se 2 (by rfl) ⟨1052718, by rfl⟩ : syracuseStep 2807249 = 2105437) B2105437
theorem B2807267 : Blo 1869636 2807267 := bstep (se 1 (by rfl) ⟨2105450, by rfl⟩ : syracuseStep 2807267 = 4210901) B4210901
theorem B2807297 : Blo 1869636 2807297 := bstep (se 2 (by rfl) ⟨1052736, by rfl⟩ : syracuseStep 2807297 = 2105473) B2105473
theorem B10794509 : Blo 1869636 10794509 := bstep (se 3 (by rfl) ⟨2023970, by rfl⟩ : syracuseStep 10794509 = 4047941) B4047941
theorem B8099341 : Blo 1869636 8099341 := bstep (se 3 (by rfl) ⟨1518626, by rfl⟩ : syracuseStep 8099341 = 3037253) B3037253
theorem B2807315 : Blo 1869636 2807315 := bstep (se 1 (by rfl) ⟨2105486, by rfl⟩ : syracuseStep 2807315 = 4210973) B4210973
theorem B3995171 : Blo 1869636 3995171 := bstep (se 1 (by rfl) ⟨2996378, by rfl⟩ : syracuseStep 3995171 = 5992757) B5992757
theorem B10114595 : Blo 1869636 10114595 := bstep (se 1 (by rfl) ⟨7585946, by rfl⟩ : syracuseStep 10114595 = 15171893) B15171893
theorem B6313517 : Blo 1869636 6313517 := bstep (se 3 (by rfl) ⟨1183784, by rfl⟩ : syracuseStep 6313517 = 2367569) B2367569
theorem B9467441 : Blo 1869636 9467441 := bstep (se 2 (by rfl) ⟨3550290, by rfl⟩ : syracuseStep 9467441 = 7100581) B7100581
theorem B2807345 : Blo 1869636 2807345 := bstep (se 2 (by rfl) ⟨1052754, by rfl⟩ : syracuseStep 2807345 = 2105509) B2105509
theorem B2995763 : Blo 1869636 2995763 := bstep (se 1 (by rfl) ⟨2246822, by rfl⟩ : syracuseStep 2995763 = 4493645) B4493645
theorem B3552835 : Blo 1869636 3552835 := bstep (se 1 (by rfl) ⟨2664626, by rfl⟩ : syracuseStep 3552835 = 5329253) B5329253
theorem B2807363 : Blo 1869636 2807363 := bstep (se 1 (by rfl) ⟨2105522, by rfl⟩ : syracuseStep 2807363 = 4211045) B4211045
theorem B2807393 : Blo 1869636 2807393 := bstep (se 2 (by rfl) ⟨1052772, by rfl⟩ : syracuseStep 2807393 = 2105545) B2105545
theorem B6313571 : Blo 1869636 6313571 := bstep (se 1 (by rfl) ⟨4735178, by rfl⟩ : syracuseStep 6313571 = 9470357) B9470357
theorem B22754915 : Blo 1869636 22754915 := bstep (se 1 (by rfl) ⟨17066186, by rfl⟩ : syracuseStep 22754915 = 34132373) B34132373
theorem B7198321 : Blo 1869636 7198321 := bstep (se 2 (by rfl) ⟨2699370, by rfl⟩ : syracuseStep 7198321 = 5398741) B5398741
theorem B15988337 : Blo 1869636 15988337 := bstep (se 2 (by rfl) ⟨5995626, by rfl⟩ : syracuseStep 15988337 = 11991253) B11991253
theorem B2807411 : Blo 1869636 2807411 := bstep (se 1 (by rfl) ⟨2105558, by rfl⟩ : syracuseStep 2807411 = 4211117) B4211117
theorem B2995841 : Blo 1869636 2995841 := bstep (se 2 (by rfl) ⟨1123440, by rfl⟩ : syracuseStep 2995841 = 2246881) B2246881
theorem B4208273 : Blo 1869636 4208273 := bstep (se 2 (by rfl) ⟨1578102, by rfl⟩ : syracuseStep 4208273 = 3156205) B3156205
theorem B2807441 : Blo 1869636 2807441 := bstep (se 2 (by rfl) ⟨1052790, by rfl⟩ : syracuseStep 2807441 = 2105581) B2105581
theorem B4208291 : Blo 1869636 4208291 := bstep (se 1 (by rfl) ⟨3156218, by rfl⟩ : syracuseStep 4208291 = 6312437) B6312437
theorem B7100081 : Blo 1869636 7100081 := bstep (se 2 (by rfl) ⟨2662530, by rfl⟩ : syracuseStep 7100081 = 5325061) B5325061
theorem B15980273 : Blo 1869636 15980273 := bstep (se 2 (by rfl) ⟨5992602, by rfl⟩ : syracuseStep 15980273 = 11985205) B11985205
theorem B4732739 : Blo 1869636 4732739 := bstep (se 1 (by rfl) ⟨3549554, by rfl⟩ : syracuseStep 4732739 = 7099109) B7099109
theorem B2996065 : Blo 1869636 2996065 := bstep (se 2 (by rfl) ⟨1123524, by rfl⟩ : syracuseStep 2996065 = 2247049) B2247049
theorem B6313841 : Blo 1869636 6313841 := bstep (se 2 (by rfl) ⟨2367690, by rfl⟩ : syracuseStep 6313841 = 4735381) B4735381
theorem B26974093 : Blo 1869636 26974093 := bstep (se 3 (by rfl) ⟨5057642, by rfl⟩ : syracuseStep 26974093 = 10115285) B10115285
theorem B4208561 : Blo 1869636 4208561 := bstep (se 2 (by rfl) ⟨1578210, by rfl⟩ : syracuseStep 4208561 = 3156421) B3156421
theorem B3037105 : Blo 1869636 3037105 := bstep (se 2 (by rfl) ⟨1138914, by rfl⟩ : syracuseStep 3037105 = 2277829) B2277829
theorem B4208579 : Blo 1869636 4208579 := bstep (se 1 (by rfl) ⟨3156434, by rfl⟩ : syracuseStep 4208579 = 6312869) B6312869
theorem B5994449 : Blo 1869636 5994449 := bstep (se 2 (by rfl) ⟨2247918, by rfl⟩ : syracuseStep 5994449 = 4495837) B4495837
theorem B4732931 : Blo 1869636 4732931 := bstep (se 1 (by rfl) ⟨3549698, by rfl⟩ : syracuseStep 4732931 = 7099397) B7099397
theorem B5994499 : Blo 1869636 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B8984675 : Blo 1869636 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B3037313 : Blo 1869636 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B3791011 : Blo 1869636 3791011 := bstep (se 1 (by rfl) ⟨2843258, by rfl⟩ : syracuseStep 3791011 = 5686517) B5686517
theorem B2103475 : Blo 1869636 2103475 := bstep (se 1 (by rfl) ⟨1577606, by rfl⟩ : syracuseStep 2103475 = 3155213) B3155213
theorem B1996979 : Blo 1869636 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B4208849 : Blo 1869636 4208849 := bstep (se 2 (by rfl) ⟨1578318, by rfl⟩ : syracuseStep 4208849 = 3156637) B3156637
theorem B4208867 : Blo 1869636 4208867 := bstep (se 1 (by rfl) ⟨3156650, by rfl⟩ : syracuseStep 4208867 = 6313301) B6313301
theorem B17971469 : Blo 1869636 17971469 := bstep (se 3 (by rfl) ⟨3369650, by rfl⟩ : syracuseStep 17971469 = 6739301) B6739301
theorem B2103619 : Blo 1869636 2103619 := bstep (se 1 (by rfl) ⟨1577714, by rfl⟩ : syracuseStep 2103619 = 3155429) B3155429
theorem B6314381 : Blo 1869636 6314381 := bstep (se 3 (by rfl) ⟨1183946, by rfl⟩ : syracuseStep 6314381 = 2367893) B2367893
theorem B6314435 : Blo 1869636 6314435 := bstep (se 1 (by rfl) ⟨4735826, by rfl⟩ : syracuseStep 6314435 = 9471653) B9471653
theorem B10115525 : Blo 1869636 10115525 := bstep (se 4 (by rfl) ⟨948330, by rfl⟩ : syracuseStep 10115525 = 1896661) B1896661
theorem B2103763 : Blo 1869636 2103763 := bstep (se 1 (by rfl) ⟨1577822, by rfl⟩ : syracuseStep 2103763 = 3155645) B3155645
theorem B4209137 : Blo 1869636 4209137 := bstep (se 2 (by rfl) ⟨1578426, by rfl⟩ : syracuseStep 4209137 = 3156853) B3156853
theorem B3996145 : Blo 1869636 3996145 := bstep (se 2 (by rfl) ⟨1498554, by rfl⟩ : syracuseStep 3996145 = 2997109) B2997109
theorem B4209155 : Blo 1869636 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B2103907 : Blo 1869636 2103907 := bstep (se 1 (by rfl) ⟨1577930, by rfl⟩ : syracuseStep 2103907 = 3155861) B3155861
theorem B11983565 : Blo 1869636 11983565 := bstep (se 3 (by rfl) ⟨2246918, by rfl⟩ : syracuseStep 11983565 = 4493837) B4493837
theorem B6314705 : Blo 1869636 6314705 := bstep (se 2 (by rfl) ⟨2368014, by rfl⟩ : syracuseStep 6314705 = 4736029) B4736029
theorem B5995217 : Blo 1869636 5995217 := bstep (se 2 (by rfl) ⟨2248206, by rfl⟩ : syracuseStep 5995217 = 4496413) B4496413
theorem B2562787 : Blo 1869636 2562787 := bstep (se 1 (by rfl) ⟨1922090, by rfl⟩ : syracuseStep 2562787 = 3844181) B3844181
theorem B2104051 : Blo 1869636 2104051 := bstep (se 1 (by rfl) ⟨1578038, by rfl⟩ : syracuseStep 2104051 = 3156077) B3156077
theorem B4209425 : Blo 1869636 4209425 := bstep (se 2 (by rfl) ⟨1578534, by rfl⟩ : syracuseStep 4209425 = 3157069) B3157069
theorem B4209443 : Blo 1869636 4209443 := bstep (se 1 (by rfl) ⟨3157082, by rfl⟩ : syracuseStep 4209443 = 6314165) B6314165
theorem B2104195 : Blo 1869636 2104195 := bstep (se 1 (by rfl) ⟨1578146, by rfl⟩ : syracuseStep 2104195 = 3156293) B3156293
theorem B1997731 : Blo 1869636 1997731 := bstep (se 1 (by rfl) ⟨1498298, by rfl⟩ : syracuseStep 1997731 = 2996597) B2996597
theorem B4733873 : Blo 1869636 4733873 := bstep (se 2 (by rfl) ⟨1775202, by rfl⟩ : syracuseStep 4733873 = 3550405) B3550405
theorem B21314501 : Blo 1869636 21314501 := bstep (se 4 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 21314501 = 3996469) B3996469
theorem B2366435 : Blo 1869636 2366435 := bstep (se 1 (by rfl) ⟨1774826, by rfl⟩ : syracuseStep 2366435 = 3549653) B3549653
theorem B4733923 : Blo 1869636 4733923 := bstep (se 1 (by rfl) ⟨3550442, by rfl⟩ : syracuseStep 4733923 = 7100885) B7100885
theorem B2882531 : Blo 1869636 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B9468899 : Blo 1869636 9468899 := bstep (se 1 (by rfl) ⟨7101674, by rfl⟩ : syracuseStep 9468899 = 14203349) B14203349
theorem B2104339 : Blo 1869636 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B4209713 : Blo 1869636 4209713 := bstep (se 2 (by rfl) ⟨1578642, by rfl⟩ : syracuseStep 4209713 = 3157285) B3157285
theorem B4209731 : Blo 1869636 4209731 := bstep (se 1 (by rfl) ⟨3157298, by rfl⟩ : syracuseStep 4209731 = 6314597) B6314597
theorem B7101539 : Blo 1869636 7101539 := bstep (se 1 (by rfl) ⟨5326154, by rfl⟩ : syracuseStep 7101539 = 10652309) B10652309
theorem B4734065 : Blo 1869636 4734065 := bstep (se 2 (by rfl) ⟨1775274, by rfl⟩ : syracuseStep 4734065 = 3550549) B3550549
theorem B7101553 : Blo 1869636 7101553 := bstep (se 2 (by rfl) ⟨2663082, by rfl⟩ : syracuseStep 7101553 = 5326165) B5326165
theorem B3996803 : Blo 1869636 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B2104483 : Blo 1869636 2104483 := bstep (se 1 (by rfl) ⟨1578362, by rfl⟩ : syracuseStep 2104483 = 3156725) B3156725
theorem B5995729 : Blo 1869636 5995729 := bstep (se 2 (by rfl) ⟨2248398, by rfl⟩ : syracuseStep 5995729 = 4496797) B4496797
theorem B6315245 : Blo 1869636 6315245 := bstep (se 3 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 6315245 = 2368217) B2368217
theorem B10648867 : Blo 1869636 10648867 := bstep (se 1 (by rfl) ⟨7986650, by rfl⟩ : syracuseStep 10648867 = 15973301) B15973301
theorem B6315299 : Blo 1869636 6315299 := bstep (se 1 (by rfl) ⟨4736474, by rfl⟩ : syracuseStep 6315299 = 9472949) B9472949
theorem B8985905 : Blo 1869636 8985905 := bstep (se 2 (by rfl) ⟨3369714, by rfl⟩ : syracuseStep 8985905 = 6739429) B6739429
theorem B2104627 : Blo 1869636 2104627 := bstep (se 1 (by rfl) ⟨1578470, by rfl⟩ : syracuseStep 2104627 = 3156941) B3156941
theorem B4210001 : Blo 1869636 4210001 := bstep (se 2 (by rfl) ⟨1578750, by rfl⟩ : syracuseStep 4210001 = 3157501) B3157501
theorem B4210019 : Blo 1869636 4210019 := bstep (se 1 (by rfl) ⟨3157514, by rfl⟩ : syracuseStep 4210019 = 6315029) B6315029
theorem B2563489 : Blo 1869636 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B2104771 : Blo 1869636 2104771 := bstep (se 1 (by rfl) ⟨1578578, by rfl⟩ : syracuseStep 2104771 = 3157157) B3157157
theorem B26959331 : Blo 1869636 26959331 := bstep (se 1 (by rfl) ⟨20219498, by rfl⟩ : syracuseStep 26959331 = 40438997) B40438997
theorem B4865521 : Blo 1869636 4865521 := bstep (se 2 (by rfl) ⟨1824570, by rfl⟩ : syracuseStep 4865521 = 3649141) B3649141
theorem B48578069 : Blo 1869636 48578069 := bstep (se 6 (by rfl) ⟨1138548, by rfl⟩ : syracuseStep 48578069 = 2277097) B2277097
theorem B6315569 : Blo 1869636 6315569 := bstep (se 2 (by rfl) ⟨2368338, by rfl⟩ : syracuseStep 6315569 = 4736677) B4736677
theorem B2997827 : Blo 1869636 2997827 := bstep (se 1 (by rfl) ⟨2248370, by rfl⟩ : syracuseStep 2997827 = 4496741) B4496741
theorem B2104915 : Blo 1869636 2104915 := bstep (se 1 (by rfl) ⟨1578686, by rfl⟩ : syracuseStep 2104915 = 3157373) B3157373
theorem B4210289 : Blo 1869636 4210289 := bstep (se 2 (by rfl) ⟨1578858, by rfl⟩ : syracuseStep 4210289 = 3157717) B3157717
theorem B4210307 : Blo 1869636 4210307 := bstep (se 1 (by rfl) ⟨3157730, by rfl⟩ : syracuseStep 4210307 = 6315461) B6315461
theorem B2367139 : Blo 1869636 2367139 := bstep (se 1 (by rfl) ⟨1775354, by rfl⟩ : syracuseStep 2367139 = 3550709) B3550709
theorem B5398211 : Blo 1869636 5398211 := bstep (se 1 (by rfl) ⟨4048658, by rfl⟩ : syracuseStep 5398211 = 8097317) B8097317
theorem B2105059 : Blo 1869636 2105059 := bstep (se 1 (by rfl) ⟨1578794, by rfl⟩ : syracuseStep 2105059 = 3157589) B3157589
theorem B5324525 : Blo 1869636 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B2367235 : Blo 1869636 2367235 := bstep (se 1 (by rfl) ⟨1775426, by rfl⟩ : syracuseStep 2367235 = 3550853) B3550853
theorem B9469709 : Blo 1869636 9469709 := bstep (se 3 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 9469709 = 3551141) B3551141
theorem B10649393 : Blo 1869636 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B2105203 : Blo 1869636 2105203 := bstep (se 1 (by rfl) ⟨1578902, by rfl⟩ : syracuseStep 2105203 = 3157805) B3157805
theorem B4210577 : Blo 1869636 4210577 := bstep (se 2 (by rfl) ⟨1578966, by rfl⟩ : syracuseStep 4210577 = 3157933) B3157933
theorem B5324707 : Blo 1869636 5324707 := bstep (se 1 (by rfl) ⟨3993530, by rfl⟩ : syracuseStep 5324707 = 7987061) B7987061
theorem B3792803 : Blo 1869636 3792803 := bstep (se 1 (by rfl) ⟨2844602, by rfl⟩ : syracuseStep 3792803 = 5689205) B5689205
theorem B4210595 : Blo 1869636 4210595 := bstep (se 1 (by rfl) ⟨3157946, by rfl⟩ : syracuseStep 4210595 = 6315893) B6315893
theorem B8536013 : Blo 1869636 8536013 := bstep (se 3 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 8536013 = 3201005) B3201005
theorem B5324753 : Blo 1869636 5324753 := bstep (se 2 (by rfl) ⟨1996782, by rfl⟩ : syracuseStep 5324753 = 3993565) B3993565
theorem B2662411 : Blo 1869636 2662411 := bstep (se 1 (by rfl) ⟨1996808, by rfl⟩ : syracuseStep 2662411 = 3993617) B3993617
theorem B6316055 : Blo 1869636 6316055 := bstep (se 1 (by rfl) ⟨4737041, by rfl⟩ : syracuseStep 6316055 = 9474083) B9474083
theorem B4210739 : Blo 1869636 4210739 := bstep (se 1 (by rfl) ⟨3158054, by rfl⟩ : syracuseStep 4210739 = 6316109) B6316109
theorem B43196485 : Blo 1869636 43196485 := bstep (se 4 (by rfl) ⟨4049670, by rfl⟩ : syracuseStep 43196485 = 8099341) B8099341
theorem B2105419 : Blo 1869636 2105419 := bstep (se 1 (by rfl) ⟨1579064, by rfl⟩ : syracuseStep 2105419 = 3158129) B3158129
theorem B4210775 : Blo 1869636 4210775 := bstep (se 1 (by rfl) ⟨3158081, by rfl⟩ : syracuseStep 4210775 = 6316163) B6316163
theorem B2105527 : Blo 1869636 2105527 := bstep (se 1 (by rfl) ⟨1579145, by rfl⟩ : syracuseStep 2105527 = 3158291) B3158291
theorem B4735169 : Blo 1869636 4735169 := bstep (se 2 (by rfl) ⟨1775688, by rfl⟩ : syracuseStep 4735169 = 3551377) B3551377
theorem B7987403 : Blo 1869636 7987403 := bstep (se 1 (by rfl) ⟨5990552, by rfl⟩ : syracuseStep 7987403 = 11981105) B11981105
theorem B5054681 : Blo 1869636 5054681 := bstep (se 2 (by rfl) ⟨1895505, by rfl⟩ : syracuseStep 5054681 = 3791011) B3791011
theorem B4210955 : Blo 1869636 4210955 := bstep (se 1 (by rfl) ⟨3158216, by rfl⟩ : syracuseStep 4210955 = 6316433) B6316433
theorem B4211009 : Blo 1869636 4211009 := bstep (se 2 (by rfl) ⟨1579128, by rfl⟩ : syracuseStep 4211009 = 3158257) B3158257
theorem B10658141 : Blo 1869636 10658141 := bstep (se 3 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 10658141 = 3996803) B3996803
theorem B107823473 : Blo 1869636 107823473 := bstep (se 2 (by rfl) ⟨40433802, by rfl⟩ : syracuseStep 107823473 = 80867605) B80867605
theorem B2367883 : Blo 1869636 2367883 := bstep (se 1 (by rfl) ⟨1775912, by rfl⟩ : syracuseStep 2367883 = 3551825) B3551825
theorem B6488471 : Blo 1869636 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B15172019 : Blo 1869636 15172019 := bstep (se 1 (by rfl) ⟨11379014, by rfl⟩ : syracuseStep 15172019 = 22758029) B22758029
theorem B5325277 : Blo 1869636 5325277 := bstep (se 3 (by rfl) ⟨998489, by rfl⟩ : syracuseStep 5325277 = 1996979) B1996979
theorem B4268555 : Blo 1869636 4268555 := bstep (se 1 (by rfl) ⟨3201416, by rfl⟩ : syracuseStep 4268555 = 6402833) B6402833
theorem B5325335 : Blo 1869636 5325335 := bstep (se 1 (by rfl) ⟨3994001, by rfl⟩ : syracuseStep 5325335 = 7988003) B7988003
theorem B6316595 : Blo 1869636 6316595 := bstep (se 1 (by rfl) ⟨4737446, by rfl⟩ : syracuseStep 6316595 = 9474893) B9474893
theorem B8536727 : Blo 1869636 8536727 := bstep (se 1 (by rfl) ⟨6402545, by rfl⟩ : syracuseStep 8536727 = 12805091) B12805091
theorem B9470681 : Blo 1869636 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B4735705 : Blo 1869636 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B3417049 : Blo 1869636 3417049 := bstep (se 2 (by rfl) ⟨1281393, by rfl⟩ : syracuseStep 3417049 = 2562787) B2562787
theorem B2663447 : Blo 1869636 2663447 := bstep (se 1 (by rfl) ⟨1997585, by rfl⟩ : syracuseStep 2663447 = 3995171) B3995171
theorem B6743063 : Blo 1869636 6743063 := bstep (se 1 (by rfl) ⟨5057297, by rfl⟩ : syracuseStep 6743063 = 10114595) B10114595
theorem B10658891 : Blo 1869636 10658891 := bstep (se 1 (by rfl) ⟨7994168, by rfl⟩ : syracuseStep 10658891 = 15988337) B15988337
theorem B3155159 : Blo 1869636 3155159 := bstep (se 1 (by rfl) ⟨2366369, by rfl⟩ : syracuseStep 3155159 = 4732739) B4732739
theorem B2663641 : Blo 1869636 2663641 := bstep (se 2 (by rfl) ⟨998865, by rfl⟩ : syracuseStep 2663641 = 1997731) B1997731
theorem B3155287 : Blo 1869636 3155287 := bstep (se 1 (by rfl) ⟨2366465, by rfl⟩ : syracuseStep 3155287 = 4732931) B4732931
theorem B5989783 : Blo 1869636 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B2024875 : Blo 1869636 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B7988701 : Blo 1869636 7988701 := bstep (se 3 (by rfl) ⟨1497881, by rfl⟩ : syracuseStep 7988701 = 2995763) B2995763
theorem B40437265 : Blo 1869636 40437265 := bstep (se 2 (by rfl) ⟨15163974, by rfl⟩ : syracuseStep 40437265 = 30327949) B30327949
theorem B6743569 : Blo 1869636 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B6743683 : Blo 1869636 6743683 := bstep (se 1 (by rfl) ⟨5057762, by rfl⟩ : syracuseStep 6743683 = 10115525) B10115525
theorem B14198489 : Blo 1869636 14198489 := bstep (se 2 (by rfl) ⟨5324433, by rfl⟩ : syracuseStep 14198489 = 10648867) B10648867
theorem B5326553 : Blo 1869636 5326553 := bstep (se 2 (by rfl) ⟨1997457, by rfl⟩ : syracuseStep 5326553 = 3994915) B3994915
theorem B7989043 : Blo 1869636 7989043 := bstep (se 1 (by rfl) ⟨5991782, by rfl⟩ : syracuseStep 7989043 = 11983565) B11983565
theorem B4736819 : Blo 1869636 4736819 := bstep (se 1 (by rfl) ⟨3552614, by rfl⟩ : syracuseStep 4736819 = 7105229) B7105229
theorem B1869643 : Blo 1869636 1869643 := bstep (se 1 (by rfl) ⟨1402232, by rfl⟩ : syracuseStep 1869643 = 2804465) B2804465
theorem B5326667 : Blo 1869636 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B5769035 : Blo 1869636 5769035 := bstep (se 1 (by rfl) ⟨4326776, by rfl⟩ : syracuseStep 5769035 = 8653553) B8653553
theorem B1869655 : Blo 1869636 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B1869675 : Blo 1869636 1869675 := bstep (se 1 (by rfl) ⟨1402256, by rfl⟩ : syracuseStep 1869675 = 2804513) B2804513
theorem B1869687 : Blo 1869636 1869687 := bstep (se 1 (by rfl) ⟨1402265, by rfl⟩ : syracuseStep 1869687 = 2804531) B2804531
theorem B3417985 : Blo 1869636 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B1869707 : Blo 1869636 1869707 := bstep (se 1 (by rfl) ⟨1402280, by rfl⟩ : syracuseStep 1869707 = 2804561) B2804561
theorem B1869719 : Blo 1869636 1869719 := bstep (se 1 (by rfl) ⟨1402289, by rfl⟩ : syracuseStep 1869719 = 2804579) B2804579
theorem B1869739 : Blo 1869636 1869739 := bstep (se 1 (by rfl) ⟨1402304, by rfl⟩ : syracuseStep 1869739 = 2804609) B2804609
theorem B1869751 : Blo 1869636 1869751 := bstep (se 1 (by rfl) ⟨1402313, by rfl⟩ : syracuseStep 1869751 = 2804627) B2804627
theorem B1869771 : Blo 1869636 1869771 := bstep (se 1 (by rfl) ⟨1402328, by rfl⟩ : syracuseStep 1869771 = 2804657) B2804657
theorem B3155915 : Blo 1869636 3155915 := bstep (se 1 (by rfl) ⟨2366936, by rfl⟩ : syracuseStep 3155915 = 4733873) B4733873
theorem B1869783 : Blo 1869636 1869783 := bstep (se 1 (by rfl) ⟨1402337, by rfl⟩ : syracuseStep 1869783 = 2804675) B2804675
theorem B1869803 : Blo 1869636 1869803 := bstep (se 1 (by rfl) ⟨1402352, by rfl⟩ : syracuseStep 1869803 = 2804705) B2804705
theorem B1869815 : Blo 1869636 1869815 := bstep (se 1 (by rfl) ⟨1402361, by rfl⟩ : syracuseStep 1869815 = 2804723) B2804723
theorem B1869835 : Blo 1869636 1869835 := bstep (se 1 (by rfl) ⟨1402376, by rfl⟩ : syracuseStep 1869835 = 2804753) B2804753
theorem B1869847 : Blo 1869636 1869847 := bstep (se 1 (by rfl) ⟨1402385, by rfl⟩ : syracuseStep 1869847 = 2804771) B2804771
theorem B1869867 : Blo 1869636 1869867 := bstep (se 1 (by rfl) ⟨1402400, by rfl⟩ : syracuseStep 1869867 = 2804801) B2804801
theorem B1869879 : Blo 1869636 1869879 := bstep (se 1 (by rfl) ⟨1402409, by rfl⟩ : syracuseStep 1869879 = 2804819) B2804819
theorem B1869899 : Blo 1869636 1869899 := bstep (se 1 (by rfl) ⟨1402424, by rfl⟩ : syracuseStep 1869899 = 2804849) B2804849
theorem B3156043 : Blo 1869636 3156043 := bstep (se 1 (by rfl) ⟨2367032, by rfl⟩ : syracuseStep 3156043 = 4734065) B4734065
theorem B1869911 : Blo 1869636 1869911 := bstep (se 1 (by rfl) ⟨1402433, by rfl⟩ : syracuseStep 1869911 = 2804867) B2804867
theorem B4737113 : Blo 1869636 4737113 := bstep (se 2 (by rfl) ⟨1776417, by rfl⟩ : syracuseStep 4737113 = 3552835) B3552835
theorem B1869931 : Blo 1869636 1869931 := bstep (se 1 (by rfl) ⟨1402448, by rfl⟩ : syracuseStep 1869931 = 2804897) B2804897
theorem B1869943 : Blo 1869636 1869943 := bstep (se 1 (by rfl) ⟨1402457, by rfl⟩ : syracuseStep 1869943 = 2804915) B2804915
theorem B21301379 : Blo 1869636 21301379 := bstep (se 1 (by rfl) ⟨15976034, by rfl⟩ : syracuseStep 21301379 = 31952069) B31952069
theorem B1869963 : Blo 1869636 1869963 := bstep (se 1 (by rfl) ⟨1402472, by rfl⟩ : syracuseStep 1869963 = 2804945) B2804945
theorem B1869975 : Blo 1869636 1869975 := bstep (se 1 (by rfl) ⟨1402481, by rfl⟩ : syracuseStep 1869975 = 2804963) B2804963
theorem B1869995 : Blo 1869636 1869995 := bstep (se 1 (by rfl) ⟨1402496, by rfl⟩ : syracuseStep 1869995 = 2804993) B2804993
theorem B1870007 : Blo 1869636 1870007 := bstep (se 1 (by rfl) ⟨1402505, by rfl⟩ : syracuseStep 1870007 = 2805011) B2805011
theorem B5990603 : Blo 1869636 5990603 := bstep (se 1 (by rfl) ⟨4492952, by rfl⟩ : syracuseStep 5990603 = 8985905) B8985905
theorem B1870027 : Blo 1869636 1870027 := bstep (se 1 (by rfl) ⟨1402520, by rfl⟩ : syracuseStep 1870027 = 2805041) B2805041
theorem B1870039 : Blo 1869636 1870039 := bstep (se 1 (by rfl) ⟨1402529, by rfl⟩ : syracuseStep 1870039 = 2805059) B2805059
theorem B3156185 : Blo 1869636 3156185 := bstep (se 2 (by rfl) ⟨1183569, by rfl⟩ : syracuseStep 3156185 = 2367139) B2367139
theorem B1870059 : Blo 1869636 1870059 := bstep (se 1 (by rfl) ⟨1402544, by rfl⟩ : syracuseStep 1870059 = 2805089) B2805089
theorem B1870071 : Blo 1869636 1870071 := bstep (se 1 (by rfl) ⟨1402553, by rfl⟩ : syracuseStep 1870071 = 2805107) B2805107
theorem B16197893 : Blo 1869636 16197893 := bstep (se 4 (by rfl) ⟨1518552, by rfl⟩ : syracuseStep 16197893 = 3037105) B3037105
theorem B14207237 : Blo 1869636 14207237 := bstep (se 4 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 14207237 = 2663857) B2663857
theorem B1870091 : Blo 1869636 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1870103 : Blo 1869636 1870103 := bstep (se 1 (by rfl) ⟨1402577, by rfl⟩ : syracuseStep 1870103 = 2805155) B2805155
theorem B1870123 : Blo 1869636 1870123 := bstep (se 1 (by rfl) ⟨1402592, by rfl⟩ : syracuseStep 1870123 = 2805185) B2805185
theorem B9472301 : Blo 1869636 9472301 := bstep (se 3 (by rfl) ⟨1776056, by rfl⟩ : syracuseStep 9472301 = 3552113) B3552113
theorem B1870135 : Blo 1869636 1870135 := bstep (se 1 (by rfl) ⟨1402601, by rfl⟩ : syracuseStep 1870135 = 2805203) B2805203
theorem B1870155 : Blo 1869636 1870155 := bstep (se 1 (by rfl) ⟨1402616, by rfl⟩ : syracuseStep 1870155 = 2805233) B2805233
theorem B1870167 : Blo 1869636 1870167 := bstep (se 1 (by rfl) ⟨1402625, by rfl⟩ : syracuseStep 1870167 = 2805251) B2805251
theorem B3156313 : Blo 1869636 3156313 := bstep (se 2 (by rfl) ⟨1183617, by rfl⟩ : syracuseStep 3156313 = 2367235) B2367235
theorem B32385379 : Blo 1869636 32385379 := bstep (se 1 (by rfl) ⟨24289034, by rfl⟩ : syracuseStep 32385379 = 48578069) B48578069
theorem B1870187 : Blo 1869636 1870187 := bstep (se 1 (by rfl) ⟨1402640, by rfl⟩ : syracuseStep 1870187 = 2805281) B2805281
theorem B1870199 : Blo 1869636 1870199 := bstep (se 1 (by rfl) ⟨1402649, by rfl⟩ : syracuseStep 1870199 = 2805299) B2805299
theorem B1870219 : Blo 1869636 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B1870231 : Blo 1869636 1870231 := bstep (se 1 (by rfl) ⟨1402673, by rfl⟩ : syracuseStep 1870231 = 2805347) B2805347
theorem B1870251 : Blo 1869636 1870251 := bstep (se 1 (by rfl) ⟨1402688, by rfl⟩ : syracuseStep 1870251 = 2805377) B2805377
theorem B7104941 : Blo 1869636 7104941 := bstep (se 3 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 7104941 = 2664353) B2664353
theorem B1870263 : Blo 1869636 1870263 := bstep (se 1 (by rfl) ⟨1402697, by rfl⟩ : syracuseStep 1870263 = 2805395) B2805395
theorem B1870283 : Blo 1869636 1870283 := bstep (se 1 (by rfl) ⟨1402712, by rfl⟩ : syracuseStep 1870283 = 2805425) B2805425
theorem B3598807 : Blo 1869636 3598807 := bstep (se 1 (by rfl) ⟨2699105, by rfl⟩ : syracuseStep 3598807 = 5398211) B5398211
theorem B1870295 : Blo 1869636 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B1870315 : Blo 1869636 1870315 := bstep (se 1 (by rfl) ⟨1402736, by rfl⟩ : syracuseStep 1870315 = 2805473) B2805473
theorem B3549683 : Blo 1869636 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B1870327 : Blo 1869636 1870327 := bstep (se 1 (by rfl) ⟨1402745, by rfl⟩ : syracuseStep 1870327 = 2805491) B2805491
theorem B1870347 : Blo 1869636 1870347 := bstep (se 1 (by rfl) ⟨1402760, by rfl⟩ : syracuseStep 1870347 = 2805521) B2805521
theorem B35965457 : Blo 1869636 35965457 := bstep (se 2 (by rfl) ⟨13487046, by rfl⟩ : syracuseStep 35965457 = 26974093) B26974093
theorem B1870359 : Blo 1869636 1870359 := bstep (se 1 (by rfl) ⟨1402769, by rfl⟩ : syracuseStep 1870359 = 2805539) B2805539
theorem B1870379 : Blo 1869636 1870379 := bstep (se 1 (by rfl) ⟨1402784, by rfl⟩ : syracuseStep 1870379 = 2805569) B2805569
theorem B1870391 : Blo 1869636 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B1870411 : Blo 1869636 1870411 := bstep (se 1 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 1870411 = 2805617) B2805617
theorem B1870423 : Blo 1869636 1870423 := bstep (se 1 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 1870423 = 2805635) B2805635
theorem B6310493 : Blo 1869636 6310493 := bstep (se 3 (by rfl) ⟨1183217, by rfl⟩ : syracuseStep 6310493 = 2366435) B2366435
theorem B1870443 : Blo 1869636 1870443 := bstep (se 1 (by rfl) ⟨1402832, by rfl⟩ : syracuseStep 1870443 = 2805665) B2805665
theorem B1870455 : Blo 1869636 1870455 := bstep (se 1 (by rfl) ⟨1402841, by rfl⟩ : syracuseStep 1870455 = 2805683) B2805683
theorem B3549835 : Blo 1869636 3549835 := bstep (se 1 (by rfl) ⟨2662376, by rfl⟩ : syracuseStep 3549835 = 5324753) B5324753
theorem B1870475 : Blo 1869636 1870475 := bstep (se 1 (by rfl) ⟨1402856, by rfl⟩ : syracuseStep 1870475 = 2805713) B2805713
theorem B1870487 : Blo 1869636 1870487 := bstep (se 1 (by rfl) ⟨1402865, by rfl⟩ : syracuseStep 1870487 = 2805731) B2805731
theorem B1870507 : Blo 1869636 1870507 := bstep (se 1 (by rfl) ⟨1402880, by rfl⟩ : syracuseStep 1870507 = 2805761) B2805761
theorem B1870519 : Blo 1869636 1870519 := bstep (se 1 (by rfl) ⟨1402889, by rfl⟩ : syracuseStep 1870519 = 2805779) B2805779
theorem B1870539 : Blo 1869636 1870539 := bstep (se 1 (by rfl) ⟨1402904, by rfl⟩ : syracuseStep 1870539 = 2805809) B2805809
theorem B1870551 : Blo 1869636 1870551 := bstep (se 1 (by rfl) ⟨1402913, by rfl⟩ : syracuseStep 1870551 = 2805827) B2805827
theorem B1870571 : Blo 1869636 1870571 := bstep (se 1 (by rfl) ⟨1402928, by rfl⟩ : syracuseStep 1870571 = 2805857) B2805857
theorem B1870583 : Blo 1869636 1870583 := bstep (se 1 (by rfl) ⟨1402937, by rfl⟩ : syracuseStep 1870583 = 2805875) B2805875
theorem B1870603 : Blo 1869636 1870603 := bstep (se 1 (by rfl) ⟨1402952, by rfl⟩ : syracuseStep 1870603 = 2805905) B2805905
theorem B1870615 : Blo 1869636 1870615 := bstep (se 1 (by rfl) ⟨1402961, by rfl⟩ : syracuseStep 1870615 = 2805923) B2805923
theorem B1870635 : Blo 1869636 1870635 := bstep (se 1 (by rfl) ⟨1402976, by rfl⟩ : syracuseStep 1870635 = 2805953) B2805953
theorem B1870647 : Blo 1869636 1870647 := bstep (se 1 (by rfl) ⟨1402985, by rfl⟩ : syracuseStep 1870647 = 2805971) B2805971
theorem B2804555 : Blo 1869636 2804555 := bstep (se 1 (by rfl) ⟨2103416, by rfl⟩ : syracuseStep 2804555 = 4206833) B4206833
theorem B1870667 : Blo 1869636 1870667 := bstep (se 1 (by rfl) ⟨1403000, by rfl⟩ : syracuseStep 1870667 = 2806001) B2806001
theorem B2804567 : Blo 1869636 2804567 := bstep (se 1 (by rfl) ⟨2103425, by rfl⟩ : syracuseStep 2804567 = 4206851) B4206851
theorem B1870679 : Blo 1869636 1870679 := bstep (se 1 (by rfl) ⟨1403009, by rfl⟩ : syracuseStep 1870679 = 2806019) B2806019
theorem B1870699 : Blo 1869636 1870699 := bstep (se 1 (by rfl) ⟨1403024, by rfl⟩ : syracuseStep 1870699 = 2806049) B2806049
theorem B1870711 : Blo 1869636 1870711 := bstep (se 1 (by rfl) ⟨1403033, by rfl⟩ : syracuseStep 1870711 = 2806067) B2806067
theorem B1870731 : Blo 1869636 1870731 := bstep (se 1 (by rfl) ⟨1403048, by rfl⟩ : syracuseStep 1870731 = 2806097) B2806097
theorem B1870743 : Blo 1869636 1870743 := bstep (se 1 (by rfl) ⟨1403057, by rfl⟩ : syracuseStep 1870743 = 2806115) B2806115
theorem B3156887 : Blo 1869636 3156887 := bstep (se 1 (by rfl) ⟨2367665, by rfl⟩ : syracuseStep 3156887 = 4735331) B4735331
theorem B2804633 : Blo 1869636 2804633 := bstep (se 2 (by rfl) ⟨1051737, by rfl⟩ : syracuseStep 2804633 = 2103475) B2103475
theorem B1870763 : Blo 1869636 1870763 := bstep (se 1 (by rfl) ⟨1403072, by rfl⟩ : syracuseStep 1870763 = 2806145) B2806145
theorem B5991347 : Blo 1869636 5991347 := bstep (se 1 (by rfl) ⟨4493510, by rfl⟩ : syracuseStep 5991347 = 8987021) B8987021
theorem B5327795 : Blo 1869636 5327795 := bstep (se 1 (by rfl) ⟨3995846, by rfl⟩ : syracuseStep 5327795 = 7991693) B7991693
theorem B1870775 : Blo 1869636 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1870795 : Blo 1869636 1870795 := bstep (se 1 (by rfl) ⟨1403096, by rfl⟩ : syracuseStep 1870795 = 2806193) B2806193
theorem B1870807 : Blo 1869636 1870807 := bstep (se 1 (by rfl) ⟨1403105, by rfl⟩ : syracuseStep 1870807 = 2806211) B2806211
theorem B3550169 : Blo 1869636 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B2845655 : Blo 1869636 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1870827 : Blo 1869636 1870827 := bstep (se 1 (by rfl) ⟨1403120, by rfl⟩ : syracuseStep 1870827 = 2806241) B2806241
theorem B1870839 : Blo 1869636 1870839 := bstep (se 1 (by rfl) ⟨1403129, by rfl⟩ : syracuseStep 1870839 = 2806259) B2806259
theorem B2804747 : Blo 1869636 2804747 := bstep (se 1 (by rfl) ⟨2103560, by rfl⟩ : syracuseStep 2804747 = 4207121) B4207121
theorem B1870859 : Blo 1869636 1870859 := bstep (se 1 (by rfl) ⟨1403144, by rfl⟩ : syracuseStep 1870859 = 2806289) B2806289
theorem B2804759 : Blo 1869636 2804759 := bstep (se 1 (by rfl) ⟨2103569, by rfl⟩ : syracuseStep 2804759 = 4207139) B4207139
theorem B3157015 : Blo 1869636 3157015 := bstep (se 1 (by rfl) ⟨2367761, by rfl⟩ : syracuseStep 3157015 = 4735523) B4735523
theorem B1870871 : Blo 1869636 1870871 := bstep (se 1 (by rfl) ⟨1403153, by rfl⟩ : syracuseStep 1870871 = 2806307) B2806307
theorem B1870891 : Blo 1869636 1870891 := bstep (se 1 (by rfl) ⟨1403168, by rfl⟩ : syracuseStep 1870891 = 2806337) B2806337
theorem B7580723 : Blo 1869636 7580723 := bstep (se 1 (by rfl) ⟨5685542, by rfl⟩ : syracuseStep 7580723 = 11371085) B11371085
theorem B5401651 : Blo 1869636 5401651 := bstep (se 1 (by rfl) ⟨4051238, by rfl⟩ : syracuseStep 5401651 = 8102477) B8102477
theorem B1870903 : Blo 1869636 1870903 := bstep (se 1 (by rfl) ⟨1403177, by rfl⟩ : syracuseStep 1870903 = 2806355) B2806355
theorem B1870923 : Blo 1869636 1870923 := bstep (se 1 (by rfl) ⟨1403192, by rfl⟩ : syracuseStep 1870923 = 2806385) B2806385
theorem B2247755 : Blo 1869636 2247755 := bstep (se 1 (by rfl) ⟨1685816, by rfl⟩ : syracuseStep 2247755 = 3371633) B3371633
theorem B1870935 : Blo 1869636 1870935 := bstep (se 1 (by rfl) ⟨1403201, by rfl⟩ : syracuseStep 1870935 = 2806403) B2806403
theorem B2804825 : Blo 1869636 2804825 := bstep (se 2 (by rfl) ⟨1051809, by rfl⟩ : syracuseStep 2804825 = 2103619) B2103619
theorem B1870955 : Blo 1869636 1870955 := bstep (se 1 (by rfl) ⟨1403216, by rfl⟩ : syracuseStep 1870955 = 2806433) B2806433
theorem B1870967 : Blo 1869636 1870967 := bstep (se 1 (by rfl) ⟨1403225, by rfl⟩ : syracuseStep 1870967 = 2806451) B2806451
theorem B1870987 : Blo 1869636 1870987 := bstep (se 1 (by rfl) ⟨1403240, by rfl⟩ : syracuseStep 1870987 = 2806481) B2806481
theorem B1870999 : Blo 1869636 1870999 := bstep (se 1 (by rfl) ⟨1403249, by rfl⟩ : syracuseStep 1870999 = 2806499) B2806499
theorem B1871019 : Blo 1869636 1871019 := bstep (se 1 (by rfl) ⟨1403264, by rfl⟩ : syracuseStep 1871019 = 2806529) B2806529
theorem B7105715 : Blo 1869636 7105715 := bstep (se 1 (by rfl) ⟨5329286, by rfl⟩ : syracuseStep 7105715 = 10658573) B10658573
theorem B1871031 : Blo 1869636 1871031 := bstep (se 1 (by rfl) ⟨1403273, by rfl⟩ : syracuseStep 1871031 = 2806547) B2806547
theorem B2804939 : Blo 1869636 2804939 := bstep (se 1 (by rfl) ⟨2103704, by rfl⟩ : syracuseStep 2804939 = 4207409) B4207409
theorem B1871051 : Blo 1869636 1871051 := bstep (se 1 (by rfl) ⟨1403288, by rfl⟩ : syracuseStep 1871051 = 2806577) B2806577
theorem B2804951 : Blo 1869636 2804951 := bstep (se 1 (by rfl) ⟨2103713, by rfl⟩ : syracuseStep 2804951 = 4207427) B4207427
theorem B1871063 : Blo 1869636 1871063 := bstep (se 1 (by rfl) ⟨1403297, by rfl⟩ : syracuseStep 1871063 = 2806595) B2806595
theorem B1871083 : Blo 1869636 1871083 := bstep (se 1 (by rfl) ⟨1403312, by rfl⟩ : syracuseStep 1871083 = 2806625) B2806625
theorem B1871095 : Blo 1869636 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B1871115 : Blo 1869636 1871115 := bstep (se 1 (by rfl) ⟨1403336, by rfl⟩ : syracuseStep 1871115 = 2806673) B2806673
theorem B1871127 : Blo 1869636 1871127 := bstep (se 1 (by rfl) ⟨1403345, by rfl⟩ : syracuseStep 1871127 = 2806691) B2806691
theorem B2805017 : Blo 1869636 2805017 := bstep (se 2 (by rfl) ⟨1051881, by rfl⟩ : syracuseStep 2805017 = 2103763) B2103763
theorem B1871147 : Blo 1869636 1871147 := bstep (se 1 (by rfl) ⟨1403360, by rfl⟩ : syracuseStep 1871147 = 2806721) B2806721
theorem B3370291 : Blo 1869636 3370291 := bstep (se 1 (by rfl) ⟨2527718, by rfl⟩ : syracuseStep 3370291 = 5055437) B5055437
theorem B1871159 : Blo 1869636 1871159 := bstep (se 1 (by rfl) ⟨1403369, by rfl⟩ : syracuseStep 1871159 = 2806739) B2806739
theorem B5328193 : Blo 1869636 5328193 := bstep (se 2 (by rfl) ⟨1998072, by rfl⟩ : syracuseStep 5328193 = 3996145) B3996145
theorem B1871179 : Blo 1869636 1871179 := bstep (se 1 (by rfl) ⟨1403384, by rfl⟩ : syracuseStep 1871179 = 2806769) B2806769
theorem B1871191 : Blo 1869636 1871191 := bstep (se 1 (by rfl) ⟨1403393, by rfl⟩ : syracuseStep 1871191 = 2806787) B2806787
theorem B1871211 : Blo 1869636 1871211 := bstep (se 1 (by rfl) ⟨1403408, by rfl⟩ : syracuseStep 1871211 = 2806817) B2806817
theorem B1871223 : Blo 1869636 1871223 := bstep (se 1 (by rfl) ⟨1403417, by rfl⟩ : syracuseStep 1871223 = 2806835) B2806835
theorem B10653059 : Blo 1869636 10653059 := bstep (se 1 (by rfl) ⟨7989794, by rfl⟩ : syracuseStep 10653059 = 15979589) B15979589
theorem B2805131 : Blo 1869636 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B1871243 : Blo 1869636 1871243 := bstep (se 1 (by rfl) ⟨1403432, by rfl⟩ : syracuseStep 1871243 = 2806865) B2806865
theorem B2805143 : Blo 1869636 2805143 := bstep (se 1 (by rfl) ⟨2103857, by rfl⟩ : syracuseStep 2805143 = 4207715) B4207715
theorem B1871255 : Blo 1869636 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B1871275 : Blo 1869636 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B3599795 : Blo 1869636 3599795 := bstep (se 1 (by rfl) ⟨2699846, by rfl⟩ : syracuseStep 3599795 = 5399693) B5399693
theorem B1871287 : Blo 1869636 1871287 := bstep (se 1 (by rfl) ⟨1403465, by rfl⟩ : syracuseStep 1871287 = 2806931) B2806931
theorem B1871307 : Blo 1869636 1871307 := bstep (se 1 (by rfl) ⟨1403480, by rfl⟩ : syracuseStep 1871307 = 2806961) B2806961
theorem B1871319 : Blo 1869636 1871319 := bstep (se 1 (by rfl) ⟨1403489, by rfl⟩ : syracuseStep 1871319 = 2806979) B2806979
theorem B2805209 : Blo 1869636 2805209 := bstep (se 2 (by rfl) ⟨1051953, by rfl⟩ : syracuseStep 2805209 = 2103907) B2103907
theorem B1871339 : Blo 1869636 1871339 := bstep (se 1 (by rfl) ⟨1403504, by rfl⟩ : syracuseStep 1871339 = 2807009) B2807009
theorem B1871351 : Blo 1869636 1871351 := bstep (se 1 (by rfl) ⟨1403513, by rfl⟩ : syracuseStep 1871351 = 2807027) B2807027
theorem B1871371 : Blo 1869636 1871371 := bstep (se 1 (by rfl) ⟨1403528, by rfl⟩ : syracuseStep 1871371 = 2807057) B2807057
theorem B1871383 : Blo 1869636 1871383 := bstep (se 1 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 1871383 = 2807075) B2807075
theorem B3993113 : Blo 1869636 3993113 := bstep (se 2 (by rfl) ⟨1497417, by rfl⟩ : syracuseStep 3993113 = 2994835) B2994835
theorem B1871403 : Blo 1869636 1871403 := bstep (se 1 (by rfl) ⟨1403552, by rfl⟩ : syracuseStep 1871403 = 2807105) B2807105
theorem B1871415 : Blo 1869636 1871415 := bstep (se 1 (by rfl) ⟨1403561, by rfl⟩ : syracuseStep 1871415 = 2807123) B2807123
theorem B2805323 : Blo 1869636 2805323 := bstep (se 1 (by rfl) ⟨2103992, by rfl⟩ : syracuseStep 2805323 = 4207985) B4207985
theorem B1871435 : Blo 1869636 1871435 := bstep (se 1 (by rfl) ⟨1403576, by rfl⟩ : syracuseStep 1871435 = 2807153) B2807153
theorem B2805335 : Blo 1869636 2805335 := bstep (se 1 (by rfl) ⟨2104001, by rfl⟩ : syracuseStep 2805335 = 4208003) B4208003
theorem B3550807 : Blo 1869636 3550807 := bstep (se 1 (by rfl) ⟨2663105, by rfl⟩ : syracuseStep 3550807 = 5326211) B5326211
theorem B1871447 : Blo 1869636 1871447 := bstep (se 1 (by rfl) ⟨1403585, by rfl⟩ : syracuseStep 1871447 = 2807171) B2807171
theorem B1871467 : Blo 1869636 1871467 := bstep (se 1 (by rfl) ⟨1403600, by rfl⟩ : syracuseStep 1871467 = 2807201) B2807201
theorem B1871479 : Blo 1869636 1871479 := bstep (se 1 (by rfl) ⟨1403609, by rfl⟩ : syracuseStep 1871479 = 2807219) B2807219
theorem B3157643 : Blo 1869636 3157643 := bstep (se 1 (by rfl) ⟨2368232, by rfl⟩ : syracuseStep 3157643 = 4736465) B4736465
theorem B1871499 : Blo 1869636 1871499 := bstep (se 1 (by rfl) ⟨1403624, by rfl⟩ : syracuseStep 1871499 = 2807249) B2807249
theorem B1871511 : Blo 1869636 1871511 := bstep (se 1 (by rfl) ⟨1403633, by rfl⟩ : syracuseStep 1871511 = 2807267) B2807267
theorem B2805401 : Blo 1869636 2805401 := bstep (se 2 (by rfl) ⟨1052025, by rfl⟩ : syracuseStep 2805401 = 2104051) B2104051
theorem B1871531 : Blo 1869636 1871531 := bstep (se 1 (by rfl) ⟨1403648, by rfl⟩ : syracuseStep 1871531 = 2807297) B2807297
theorem B7196339 : Blo 1869636 7196339 := bstep (se 1 (by rfl) ⟨5397254, by rfl⟩ : syracuseStep 7196339 = 10794509) B10794509
theorem B1871543 : Blo 1869636 1871543 := bstep (se 1 (by rfl) ⟨1403657, by rfl⟩ : syracuseStep 1871543 = 2807315) B2807315
theorem B6311627 : Blo 1869636 6311627 := bstep (se 1 (by rfl) ⟨4733720, by rfl⟩ : syracuseStep 6311627 = 9467441) B9467441
theorem B5058251 : Blo 1869636 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B1871563 : Blo 1869636 1871563 := bstep (se 1 (by rfl) ⟨1403672, by rfl⟩ : syracuseStep 1871563 = 2807345) B2807345
theorem B1871575 : Blo 1869636 1871575 := bstep (se 1 (by rfl) ⟨1403681, by rfl⟩ : syracuseStep 1871575 = 2807363) B2807363
theorem B1871595 : Blo 1869636 1871595 := bstep (se 1 (by rfl) ⟨1403696, by rfl⟩ : syracuseStep 1871595 = 2807393) B2807393
theorem B31960817 : Blo 1869636 31960817 := bstep (se 2 (by rfl) ⟨11985306, by rfl⟩ : syracuseStep 31960817 = 23970613) B23970613
theorem B1871607 : Blo 1869636 1871607 := bstep (se 1 (by rfl) ⟨1403705, by rfl⟩ : syracuseStep 1871607 = 2807411) B2807411
theorem B2805515 : Blo 1869636 2805515 := bstep (se 1 (by rfl) ⟨2104136, by rfl⟩ : syracuseStep 2805515 = 4208273) B4208273
theorem B3157771 : Blo 1869636 3157771 := bstep (se 1 (by rfl) ⟨2368328, by rfl⟩ : syracuseStep 3157771 = 4736657) B4736657
theorem B1871627 : Blo 1869636 1871627 := bstep (se 1 (by rfl) ⟨1403720, by rfl⟩ : syracuseStep 1871627 = 2807441) B2807441
theorem B2805527 : Blo 1869636 2805527 := bstep (se 1 (by rfl) ⟨2104145, by rfl⟩ : syracuseStep 2805527 = 4208291) B4208291
theorem B10653515 : Blo 1869636 10653515 := bstep (se 1 (by rfl) ⟨7990136, by rfl⟩ : syracuseStep 10653515 = 15980273) B15980273
theorem B2805593 : Blo 1869636 2805593 := bstep (se 2 (by rfl) ⟨1052097, by rfl⟩ : syracuseStep 2805593 = 2104195) B2104195
theorem B15175525 : Blo 1869636 15175525 := bstep (se 4 (by rfl) ⟨1422705, by rfl⟩ : syracuseStep 15175525 = 2845411) B2845411
theorem B3157913 : Blo 1869636 3157913 := bstep (se 2 (by rfl) ⟨1184217, by rfl⟩ : syracuseStep 3157913 = 2368435) B2368435
theorem B2805707 : Blo 1869636 2805707 := bstep (se 1 (by rfl) ⟨2104280, by rfl⟩ : syracuseStep 2805707 = 4208561) B4208561
theorem B2805719 : Blo 1869636 2805719 := bstep (se 1 (by rfl) ⟨2104289, by rfl⟩ : syracuseStep 2805719 = 4208579) B4208579
theorem B6311897 : Blo 1869636 6311897 := bstep (se 2 (by rfl) ⟨2366961, by rfl⟩ : syracuseStep 6311897 = 4733923) B4733923
theorem B9236497 : Blo 1869636 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B2805785 : Blo 1869636 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B3158041 : Blo 1869636 3158041 := bstep (se 2 (by rfl) ⟨1184265, by rfl⟩ : syracuseStep 3158041 = 2368531) B2368531
theorem B4206707 : Blo 1869636 4206707 := bstep (se 1 (by rfl) ⟨3155030, by rfl⟩ : syracuseStep 4206707 = 6310061) B6310061
theorem B2805899 : Blo 1869636 2805899 := bstep (se 1 (by rfl) ⟨2104424, by rfl⟩ : syracuseStep 2805899 = 4208849) B4208849
theorem B4206743 : Blo 1869636 4206743 := bstep (se 1 (by rfl) ⟨3155057, by rfl⟩ : syracuseStep 4206743 = 6310115) B6310115
theorem B2805911 : Blo 1869636 2805911 := bstep (se 1 (by rfl) ⟨2104433, by rfl⟩ : syracuseStep 2805911 = 4208867) B4208867
theorem B11980979 : Blo 1869636 11980979 := bstep (se 1 (by rfl) ⟨8985734, by rfl⟩ : syracuseStep 11980979 = 17971469) B17971469
theorem B2805977 : Blo 1869636 2805977 := bstep (se 2 (by rfl) ⟨1052241, by rfl⟩ : syracuseStep 2805977 = 2104483) B2104483
theorem B4501811 : Blo 1869636 4501811 := bstep (se 1 (by rfl) ⟨3376358, by rfl⟩ : syracuseStep 4501811 = 6752717) B6752717
theorem B3993907 : Blo 1869636 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B4206923 : Blo 1869636 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B2806091 : Blo 1869636 2806091 := bstep (se 1 (by rfl) ⟨2104568, by rfl⟩ : syracuseStep 2806091 = 4209137) B4209137
theorem B2806103 : Blo 1869636 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B6402397 : Blo 1869636 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B4206977 : Blo 1869636 4206977 := bstep (se 2 (by rfl) ⟨1577616, by rfl⟩ : syracuseStep 4206977 = 3155233) B3155233
theorem B3551627 : Blo 1869636 3551627 := bstep (se 1 (by rfl) ⟨2663720, by rfl⟩ : syracuseStep 3551627 = 5327441) B5327441
theorem B2806169 : Blo 1869636 2806169 := bstep (se 2 (by rfl) ⟨1052313, by rfl⟩ : syracuseStep 2806169 = 2104627) B2104627
theorem B3551681 : Blo 1869636 3551681 := bstep (se 2 (by rfl) ⟨1331880, by rfl⟩ : syracuseStep 3551681 = 2663761) B2663761
theorem B2806283 : Blo 1869636 2806283 := bstep (se 1 (by rfl) ⟨2104712, by rfl⟩ : syracuseStep 2806283 = 4209425) B4209425
theorem B2806295 : Blo 1869636 2806295 := bstep (se 1 (by rfl) ⟨2104721, by rfl⟩ : syracuseStep 2806295 = 4209443) B4209443
theorem B3600947 : Blo 1869636 3600947 := bstep (se 1 (by rfl) ⟨2700710, by rfl⟩ : syracuseStep 3600947 = 5401421) B5401421
theorem B4207193 : Blo 1869636 4207193 := bstep (se 2 (by rfl) ⟨1577697, by rfl⟩ : syracuseStep 4207193 = 3155395) B3155395
theorem B2806361 : Blo 1869636 2806361 := bstep (se 2 (by rfl) ⟨1052385, by rfl⟩ : syracuseStep 2806361 = 2104771) B2104771
theorem B14209667 : Blo 1869636 14209667 := bstep (se 1 (by rfl) ⟨10657250, by rfl⟩ : syracuseStep 14209667 = 21314501) B21314501
theorem B1921687 : Blo 1869636 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B6312599 : Blo 1869636 6312599 := bstep (se 1 (by rfl) ⟨4734449, by rfl⟩ : syracuseStep 6312599 = 9468899) B9468899
theorem B4207283 : Blo 1869636 4207283 := bstep (se 1 (by rfl) ⟨3155462, by rfl⟩ : syracuseStep 4207283 = 6310925) B6310925
theorem B2806475 : Blo 1869636 2806475 := bstep (se 1 (by rfl) ⟨2104856, by rfl⟩ : syracuseStep 2806475 = 4209713) B4209713
theorem B4207319 : Blo 1869636 4207319 := bstep (se 1 (by rfl) ⟨3155489, by rfl⟩ : syracuseStep 4207319 = 6310979) B6310979
theorem B2806487 : Blo 1869636 2806487 := bstep (se 1 (by rfl) ⟨2104865, by rfl⟩ : syracuseStep 2806487 = 4209731) B4209731
theorem B6738653 : Blo 1869636 6738653 := bstep (se 3 (by rfl) ⟨1263497, by rfl⟩ : syracuseStep 6738653 = 2526995) B2526995
theorem B2806553 : Blo 1869636 2806553 := bstep (se 2 (by rfl) ⟨1052457, by rfl⟩ : syracuseStep 2806553 = 2104915) B2104915
theorem B9597761 : Blo 1869636 9597761 := bstep (se 2 (by rfl) ⟨3599160, by rfl⟩ : syracuseStep 9597761 = 7198321) B7198321
theorem B4494145 : Blo 1869636 4494145 := bstep (se 2 (by rfl) ⟨1685304, by rfl⟩ : syracuseStep 4494145 = 3370609) B3370609
theorem B2192215 : Blo 1869636 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B4207499 : Blo 1869636 4207499 := bstep (se 1 (by rfl) ⟨3155624, by rfl⟩ : syracuseStep 4207499 = 6311249) B6311249
theorem B2806667 : Blo 1869636 2806667 := bstep (se 1 (by rfl) ⟨2105000, by rfl⟩ : syracuseStep 2806667 = 4210001) B4210001
theorem B2806679 : Blo 1869636 2806679 := bstep (se 1 (by rfl) ⟨2105009, by rfl⟩ : syracuseStep 2806679 = 4210019) B4210019
theorem B4207553 : Blo 1869636 4207553 := bstep (se 2 (by rfl) ⟨1577832, by rfl⟩ : syracuseStep 4207553 = 3155665) B3155665
theorem B2806745 : Blo 1869636 2806745 := bstep (se 2 (by rfl) ⟨1052529, by rfl⟩ : syracuseStep 2806745 = 2105059) B2105059
theorem B14201891 : Blo 1869636 14201891 := bstep (se 1 (by rfl) ⟨10651418, by rfl⟩ : syracuseStep 14201891 = 21302837) B21302837
theorem B9466955 : Blo 1869636 9466955 := bstep (se 1 (by rfl) ⟨7100216, by rfl⟩ : syracuseStep 9466955 = 14200433) B14200433
theorem B2806859 : Blo 1869636 2806859 := bstep (se 1 (by rfl) ⟨2105144, by rfl⟩ : syracuseStep 2806859 = 4210289) B4210289
theorem B2806871 : Blo 1869636 2806871 := bstep (se 1 (by rfl) ⟨2105153, by rfl⟩ : syracuseStep 2806871 = 4210307) B4210307
theorem B10114141 : Blo 1869636 10114141 := bstep (se 3 (by rfl) ⟨1896401, by rfl⟩ : syracuseStep 10114141 = 3792803) B3792803
theorem B3994753 : Blo 1869636 3994753 := bstep (se 2 (by rfl) ⟨1498032, by rfl⟩ : syracuseStep 3994753 = 2996065) B2996065
theorem B4207769 : Blo 1869636 4207769 := bstep (se 2 (by rfl) ⟨1577913, by rfl⟩ : syracuseStep 4207769 = 3155827) B3155827
theorem B2806937 : Blo 1869636 2806937 := bstep (se 2 (by rfl) ⟨1052601, by rfl⟩ : syracuseStep 2806937 = 2105203) B2105203
theorem B6313139 : Blo 1869636 6313139 := bstep (se 1 (by rfl) ⟨4734854, by rfl⟩ : syracuseStep 6313139 = 9469709) B9469709
theorem B7099595 : Blo 1869636 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B7099609 : Blo 1869636 7099609 := bstep (se 2 (by rfl) ⟨2662353, by rfl⟩ : syracuseStep 7099609 = 5324707) B5324707
theorem B4207859 : Blo 1869636 4207859 := bstep (se 1 (by rfl) ⟨3155894, by rfl⟩ : syracuseStep 4207859 = 6311789) B6311789
theorem B2807051 : Blo 1869636 2807051 := bstep (se 1 (by rfl) ⟨2105288, by rfl⟩ : syracuseStep 2807051 = 4210577) B4210577
theorem B4207895 : Blo 1869636 4207895 := bstep (se 1 (by rfl) ⟨3155921, by rfl⟩ : syracuseStep 4207895 = 6311843) B6311843
theorem B2807063 : Blo 1869636 2807063 := bstep (se 1 (by rfl) ⟨2105297, by rfl⟩ : syracuseStep 2807063 = 4210595) B4210595
theorem B5690675 : Blo 1869636 5690675 := bstep (se 1 (by rfl) ⟨4268006, by rfl⟩ : syracuseStep 5690675 = 8536013) B8536013
theorem B3552599 : Blo 1869636 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B7992665 : Blo 1869636 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B2807129 : Blo 1869636 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B6313409 : Blo 1869636 6313409 := bstep (se 2 (by rfl) ⟨2367528, by rfl⟩ : syracuseStep 6313409 = 4735057) B4735057
theorem B4208075 : Blo 1869636 4208075 := bstep (se 1 (by rfl) ⟨3156056, by rfl⟩ : syracuseStep 4208075 = 6312113) B6312113
theorem B2807243 : Blo 1869636 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B3036631 : Blo 1869636 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B3995095 : Blo 1869636 3995095 := bstep (se 1 (by rfl) ⟨2996321, by rfl⟩ : syracuseStep 3995095 = 5992643) B5992643
theorem B2807255 : Blo 1869636 2807255 := bstep (se 1 (by rfl) ⟨2105441, by rfl⟩ : syracuseStep 2807255 = 4210883) B4210883
theorem B4208129 : Blo 1869636 4208129 := bstep (se 2 (by rfl) ⟨1578048, by rfl⟩ : syracuseStep 4208129 = 3156097) B3156097
theorem B2807321 : Blo 1869636 2807321 := bstep (se 2 (by rfl) ⟨1052745, by rfl⟩ : syracuseStep 2807321 = 2105491) B2105491
theorem B12801611 : Blo 1869636 12801611 := bstep (se 1 (by rfl) ⟨9601208, by rfl⟩ : syracuseStep 12801611 = 19202417) B19202417
theorem B7583321 : Blo 1869636 7583321 := bstep (se 2 (by rfl) ⟨2843745, by rfl⟩ : syracuseStep 7583321 = 5687491) B5687491
theorem B11982437 : Blo 1869636 11982437 := bstep (se 4 (by rfl) ⟨1123353, by rfl⟩ : syracuseStep 11982437 = 2246707) B2246707
theorem B2807435 : Blo 1869636 2807435 := bstep (se 1 (by rfl) ⟨2105576, by rfl⟩ : syracuseStep 2807435 = 4211153) B4211153
theorem B2807447 : Blo 1869636 2807447 := bstep (se 1 (by rfl) ⟨2105585, by rfl⟩ : syracuseStep 2807447 = 4211171) B4211171
theorem B4208345 : Blo 1869636 4208345 := bstep (se 2 (by rfl) ⟨1578129, by rfl⟩ : syracuseStep 4208345 = 3156259) B3156259
theorem B1996535 : Blo 1869636 1996535 := bstep (se 1 (by rfl) ⟨1497401, by rfl⟩ : syracuseStep 1996535 = 2994803) B2994803
theorem B4208435 : Blo 1869636 4208435 := bstep (se 1 (by rfl) ⟨3156326, by rfl⟩ : syracuseStep 4208435 = 6312653) B6312653
theorem B4208471 : Blo 1869636 4208471 := bstep (se 1 (by rfl) ⟨3156353, by rfl⟩ : syracuseStep 4208471 = 6312707) B6312707
theorem B3553139 : Blo 1869636 3553139 := bstep (se 1 (by rfl) ⟨2664854, by rfl⟩ : syracuseStep 3553139 = 5329709) B5329709
theorem B6313949 : Blo 1869636 6313949 := bstep (se 3 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 6313949 = 2367731) B2367731
theorem B4208651 : Blo 1869636 4208651 := bstep (se 1 (by rfl) ⟨3156488, by rfl⟩ : syracuseStep 4208651 = 6312977) B6312977
theorem B4732951 : Blo 1869636 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B10115117 : Blo 1869636 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B4208705 : Blo 1869636 4208705 := bstep (se 2 (by rfl) ⟨1578264, by rfl⟩ : syracuseStep 4208705 = 3156529) B3156529
theorem B184440907 : Blo 1869636 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B2103403 : Blo 1869636 2103403 := bstep (se 1 (by rfl) ⟨1577552, by rfl⟩ : syracuseStep 2103403 = 3155105) B3155105
theorem B7100567 : Blo 1869636 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B2103511 : Blo 1869636 2103511 := bstep (se 1 (by rfl) ⟨1577633, by rfl⟩ : syracuseStep 2103511 = 3155267) B3155267
theorem B4208921 : Blo 1869636 4208921 := bstep (se 2 (by rfl) ⟨1578345, by rfl⟩ : syracuseStep 4208921 = 3156691) B3156691
theorem B13859117 : Blo 1869636 13859117 := bstep (se 3 (by rfl) ⟨2598584, by rfl⟩ : syracuseStep 13859117 = 5197169) B5197169
theorem B4209011 : Blo 1869636 4209011 := bstep (se 1 (by rfl) ⟨3156758, by rfl⟩ : syracuseStep 4209011 = 6313517) B6313517
theorem B2103691 : Blo 1869636 2103691 := bstep (se 1 (by rfl) ⟨1577768, by rfl⟩ : syracuseStep 2103691 = 3155537) B3155537
theorem B4209047 : Blo 1869636 4209047 := bstep (se 1 (by rfl) ⟨3156785, by rfl⟩ : syracuseStep 4209047 = 6313571) B6313571
theorem B15169943 : Blo 1869636 15169943 := bstep (se 1 (by rfl) ⟨11377457, by rfl⟩ : syracuseStep 15169943 = 22754915) B22754915
theorem B1997227 : Blo 1869636 1997227 := bstep (se 1 (by rfl) ⟨1497920, by rfl⟩ : syracuseStep 1997227 = 2995841) B2995841
theorem B4733387 : Blo 1869636 4733387 := bstep (se 1 (by rfl) ⟨3550040, by rfl⟩ : syracuseStep 4733387 = 7100081) B7100081
theorem B2103799 : Blo 1869636 2103799 := bstep (se 1 (by rfl) ⟨1577849, by rfl⟩ : syracuseStep 2103799 = 3155699) B3155699
theorem B4495895 : Blo 1869636 4495895 := bstep (se 1 (by rfl) ⟨3371921, by rfl⟩ : syracuseStep 4495895 = 6743843) B6743843
theorem B4209227 : Blo 1869636 4209227 := bstep (se 1 (by rfl) ⟨3156920, by rfl⟩ : syracuseStep 4209227 = 6313841) B6313841
theorem B4209281 : Blo 1869636 4209281 := bstep (se 2 (by rfl) ⟨1578480, by rfl⟩ : syracuseStep 4209281 = 3156961) B3156961
theorem B3996299 : Blo 1869636 3996299 := bstep (se 1 (by rfl) ⟨2997224, by rfl⟩ : syracuseStep 3996299 = 5994449) B5994449
theorem B2103979 : Blo 1869636 2103979 := bstep (se 1 (by rfl) ⟨1577984, by rfl⟩ : syracuseStep 2103979 = 3155969) B3155969
theorem B2104087 : Blo 1869636 2104087 := bstep (se 1 (by rfl) ⟨1578065, by rfl⟩ : syracuseStep 2104087 = 3156131) B3156131
theorem B4266803 : Blo 1869636 4266803 := bstep (se 1 (by rfl) ⟨3200102, by rfl⟩ : syracuseStep 4266803 = 6400205) B6400205
theorem B4733761 : Blo 1869636 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B9468737 : Blo 1869636 9468737 := bstep (se 2 (by rfl) ⟨3550776, by rfl⟩ : syracuseStep 9468737 = 7101553) B7101553
theorem B4266839 : Blo 1869636 4266839 := bstep (se 1 (by rfl) ⟨3200129, by rfl⟩ : syracuseStep 4266839 = 6400259) B6400259
theorem B4209497 : Blo 1869636 4209497 := bstep (se 2 (by rfl) ⟨1578561, by rfl⟩ : syracuseStep 4209497 = 3157123) B3157123
theorem B4209587 : Blo 1869636 4209587 := bstep (se 1 (by rfl) ⟨3157190, by rfl⟩ : syracuseStep 4209587 = 6314381) B6314381
theorem B7994305 : Blo 1869636 7994305 := bstep (se 2 (by rfl) ⟨2997864, by rfl⟩ : syracuseStep 7994305 = 5995729) B5995729
theorem B2104267 : Blo 1869636 2104267 := bstep (se 1 (by rfl) ⟨1578200, by rfl⟩ : syracuseStep 2104267 = 3156401) B3156401
theorem B4209623 : Blo 1869636 4209623 := bstep (se 1 (by rfl) ⟨3157217, by rfl⟩ : syracuseStep 4209623 = 6314435) B6314435
theorem B17538053 : Blo 1869636 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B53959715 : Blo 1869636 53959715 := bstep (se 1 (by rfl) ⟨40469786, by rfl⟩ : syracuseStep 53959715 = 80939573) B80939573
theorem B2104375 : Blo 1869636 2104375 := bstep (se 1 (by rfl) ⟨1578281, by rfl⟩ : syracuseStep 2104375 = 3156563) B3156563
theorem B6315083 : Blo 1869636 6315083 := bstep (se 1 (by rfl) ⟨4736312, by rfl⟩ : syracuseStep 6315083 = 9472625) B9472625
theorem B4209803 : Blo 1869636 4209803 := bstep (se 1 (by rfl) ⟨3157352, by rfl⟩ : syracuseStep 4209803 = 6314705) B6314705
theorem B3996811 : Blo 1869636 3996811 := bstep (se 1 (by rfl) ⟨2997608, by rfl⟩ : syracuseStep 3996811 = 5995217) B5995217
theorem B3792025 : Blo 1869636 3792025 := bstep (se 2 (by rfl) ⟨1422009, by rfl⟩ : syracuseStep 3792025 = 2844019) B2844019
theorem B4209857 : Blo 1869636 4209857 := bstep (se 2 (by rfl) ⟨1578696, by rfl⟩ : syracuseStep 4209857 = 3157393) B3157393
theorem B23968973 : Blo 1869636 23968973 := bstep (se 3 (by rfl) ⟨4494182, by rfl⟩ : syracuseStep 23968973 = 8988365) B8988365
theorem B2104555 : Blo 1869636 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B3792179 : Blo 1869636 3792179 := bstep (se 1 (by rfl) ⟨2844134, by rfl⟩ : syracuseStep 3792179 = 5688269) B5688269
theorem B6487361 : Blo 1869636 6487361 := bstep (se 2 (by rfl) ⟨2432760, by rfl⟩ : syracuseStep 6487361 = 4865521) B4865521
theorem B2104663 : Blo 1869636 2104663 := bstep (se 1 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 2104663 = 3156995) B3156995
theorem B6315353 : Blo 1869636 6315353 := bstep (se 2 (by rfl) ⟨2368257, by rfl⟩ : syracuseStep 6315353 = 4736515) B4736515
theorem B7101827 : Blo 1869636 7101827 := bstep (se 1 (by rfl) ⟨5326370, by rfl⟩ : syracuseStep 7101827 = 10652741) B10652741
theorem B4734359 : Blo 1869636 4734359 := bstep (se 1 (by rfl) ⟨3550769, by rfl⟩ : syracuseStep 4734359 = 7101539) B7101539
theorem B4210073 : Blo 1869636 4210073 := bstep (se 2 (by rfl) ⟨1578777, by rfl⟩ : syracuseStep 4210073 = 3157555) B3157555
theorem B4210163 : Blo 1869636 4210163 := bstep (se 1 (by rfl) ⟨3157622, by rfl⟩ : syracuseStep 4210163 = 6315245) B6315245
theorem B2104843 : Blo 1869636 2104843 := bstep (se 1 (by rfl) ⟨1578632, by rfl⟩ : syracuseStep 2104843 = 3157265) B3157265
theorem B4210199 : Blo 1869636 4210199 := bstep (se 1 (by rfl) ⟨3157649, by rfl⟩ : syracuseStep 4210199 = 6315299) B6315299
theorem B23076427 : Blo 1869636 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B2104951 : Blo 1869636 2104951 := bstep (se 1 (by rfl) ⟨1578713, by rfl⟩ : syracuseStep 2104951 = 3157427) B3157427
theorem B17972887 : Blo 1869636 17972887 := bstep (se 1 (by rfl) ⟨13479665, by rfl⟩ : syracuseStep 17972887 = 26959331) B26959331
theorem B4210379 : Blo 1869636 4210379 := bstep (se 1 (by rfl) ⟨3157784, by rfl⟩ : syracuseStep 4210379 = 6315569) B6315569
theorem B28802765 : Blo 1869636 28802765 := bstep (se 3 (by rfl) ⟨5400518, by rfl⟩ : syracuseStep 28802765 = 10801037) B10801037
theorem B2662103 : Blo 1869636 2662103 := bstep (se 1 (by rfl) ⟨1996577, by rfl⟩ : syracuseStep 2662103 = 3993155) B3993155
theorem B1998551 : Blo 1869636 1998551 := bstep (se 1 (by rfl) ⟨1498913, by rfl⟩ : syracuseStep 1998551 = 2997827) B2997827
theorem B4210433 : Blo 1869636 4210433 := bstep (se 2 (by rfl) ⟨1578912, by rfl⟩ : syracuseStep 4210433 = 3157825) B3157825
theorem B2105131 : Blo 1869636 2105131 := bstep (se 1 (by rfl) ⟨1578848, by rfl⟩ : syracuseStep 2105131 = 3157697) B3157697
theorem B2400139 : Blo 1869636 2400139 := bstep (se 1 (by rfl) ⟨1800104, by rfl⟩ : syracuseStep 2400139 = 3600209) B3600209
theorem B2105239 : Blo 1869636 2105239 := bstep (se 1 (by rfl) ⟨1578929, by rfl⟩ : syracuseStep 2105239 = 3157859) B3157859
theorem B4210649 : Blo 1869636 4210649 := bstep (se 2 (by rfl) ⟨1578993, by rfl⟩ : syracuseStep 4210649 = 3157987) B3157987
theorem B46768141 : Blo 1869636 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B4210703 : Blo 1869636 4210703 := bstep (se 1 (by rfl) ⟨3158027, by rfl⟩ : syracuseStep 4210703 = 6316055) B6316055
theorem B4210721 : Blo 1869636 4210721 := bstep (se 2 (by rfl) ⟨1579020, by rfl⟩ : syracuseStep 4210721 = 3158041) B3158041
theorem B7102525 : Blo 1869636 7102525 := bstep (se 3 (by rfl) ⟨1331723, by rfl⟩ : syracuseStep 7102525 = 2663447) B2663447
theorem B7987319 : Blo 1869636 7987319 := bstep (se 1 (by rfl) ⟨5990489, by rfl⟩ : syracuseStep 7987319 = 11980979) B11980979
theorem B5324935 : Blo 1869636 5324935 := bstep (se 1 (by rfl) ⟨3993701, by rfl⟩ : syracuseStep 5324935 = 7987403) B7987403
theorem B4325647 : Blo 1869636 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B2367787 : Blo 1869636 2367787 := bstep (se 1 (by rfl) ⟨1775840, by rfl⟩ : syracuseStep 2367787 = 3551681) B3551681
theorem B4211063 : Blo 1869636 4211063 := bstep (se 1 (by rfl) ⟨3158297, by rfl⟩ : syracuseStep 4211063 = 6316595) B6316595
theorem B5325209 : Blo 1869636 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B8536529 : Blo 1869636 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B43180505 : Blo 1869636 43180505 := bstep (se 2 (by rfl) ⟨16192689, by rfl⟩ : syracuseStep 43180505 = 32385379) B32385379
theorem B15974941 : Blo 1869636 15974941 := bstep (se 3 (by rfl) ⟨2995301, by rfl⟩ : syracuseStep 15974941 = 5990603) B5990603
theorem B6398507 : Blo 1869636 6398507 := bstep (se 1 (by rfl) ⟨4798880, by rfl⟩ : syracuseStep 6398507 = 9597761) B9597761
theorem B2662969 : Blo 1869636 2662969 := bstep (se 2 (by rfl) ⟨998613, by rfl⟩ : syracuseStep 2662969 = 1997227) B1997227
theorem B9471005 : Blo 1869636 9471005 := bstep (se 3 (by rfl) ⟨1775813, by rfl⟩ : syracuseStep 9471005 = 3551627) B3551627
theorem B5055547 : Blo 1869636 5055547 := bstep (se 1 (by rfl) ⟨3791660, by rfl⟩ : syracuseStep 5055547 = 7583321) B7583321
theorem B40453181 : Blo 1869636 40453181 := bstep (se 3 (by rfl) ⟨7584971, by rfl⟩ : syracuseStep 40453181 = 15169943) B15169943
theorem B7988291 : Blo 1869636 7988291 := bstep (se 1 (by rfl) ⟨5991218, by rfl⟩ : syracuseStep 7988291 = 11982437) B11982437
theorem B2368759 : Blo 1869636 2368759 := bstep (se 1 (by rfl) ⟨1776569, by rfl⟩ : syracuseStep 2368759 = 3553139) B3553139
theorem B10659073 : Blo 1869636 10659073 := bstep (se 2 (by rfl) ⟨3997152, by rfl⟩ : syracuseStep 10659073 = 7994305) B7994305
theorem B6743411 : Blo 1869636 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B7202201 : Blo 1869636 7202201 := bstep (se 2 (by rfl) ⟨2700825, by rfl⟩ : syracuseStep 7202201 = 5401651) B5401651
theorem B13485521 : Blo 1869636 13485521 := bstep (se 2 (by rfl) ⟨5057070, by rfl⟩ : syracuseStep 13485521 = 10114141) B10114141
theorem B9602525 : Blo 1869636 9602525 := bstep (se 3 (by rfl) ⟨1800473, by rfl⟩ : syracuseStep 9602525 = 3600947) B3600947
theorem B5326337 : Blo 1869636 5326337 := bstep (se 2 (by rfl) ⟨1997376, by rfl⟩ : syracuseStep 5326337 = 3994753) B3994753
theorem B10798595 : Blo 1869636 10798595 := bstep (se 1 (by rfl) ⟨8098946, by rfl⟩ : syracuseStep 10798595 = 16197893) B16197893
theorem B9471491 : Blo 1869636 9471491 := bstep (se 1 (by rfl) ⟨7103618, by rfl⟩ : syracuseStep 9471491 = 14207237) B14207237
theorem B5056033 : Blo 1869636 5056033 := bstep (se 2 (by rfl) ⟨1896012, by rfl⟩ : syracuseStep 5056033 = 3792025) B3792025
theorem B17974885 : Blo 1869636 17974885 := bstep (se 4 (by rfl) ⟨1685145, by rfl⟩ : syracuseStep 17974885 = 3370291) B3370291
theorem B4736627 : Blo 1869636 4736627 := bstep (se 1 (by rfl) ⟨3552470, by rfl⟩ : syracuseStep 4736627 = 7104941) B7104941
theorem B3155591 : Blo 1869636 3155591 := bstep (se 1 (by rfl) ⟨2366693, by rfl⟩ : syracuseStep 3155591 = 4733387) B4733387
theorem B7104257 : Blo 1869636 7104257 := bstep (se 2 (by rfl) ⟨2664096, by rfl⟩ : syracuseStep 7104257 = 5328193) B5328193
theorem B2664199 : Blo 1869636 2664199 := bstep (se 1 (by rfl) ⟨1998149, by rfl⟩ : syracuseStep 2664199 = 3996299) B3996299
theorem B1869703 : Blo 1869636 1869703 := bstep (se 1 (by rfl) ⟨1402277, by rfl⟩ : syracuseStep 1869703 = 2804555) B2804555
theorem B1869711 : Blo 1869636 1869711 := bstep (se 1 (by rfl) ⟨1402283, by rfl⟩ : syracuseStep 1869711 = 2804567) B2804567
theorem B2844559 : Blo 1869636 2844559 := bstep (se 1 (by rfl) ⟨2133419, by rfl⟩ : syracuseStep 2844559 = 4266839) B4266839
theorem B1869755 : Blo 1869636 1869755 := bstep (se 1 (by rfl) ⟨1402316, by rfl⟩ : syracuseStep 1869755 = 2804633) B2804633
theorem B4048841 : Blo 1869636 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B5326793 : Blo 1869636 5326793 := bstep (se 2 (by rfl) ⟨1997547, by rfl⟩ : syracuseStep 5326793 = 3995095) B3995095
theorem B10651601 : Blo 1869636 10651601 := bstep (se 2 (by rfl) ⟨3994350, by rfl⟩ : syracuseStep 10651601 = 7988701) B7988701
theorem B1869831 : Blo 1869636 1869831 := bstep (se 1 (by rfl) ⟨1402373, by rfl⟩ : syracuseStep 1869831 = 2804747) B2804747
theorem B1869839 : Blo 1869636 1869839 := bstep (se 1 (by rfl) ⟨1402379, by rfl⟩ : syracuseStep 1869839 = 2804759) B2804759
theorem B35973143 : Blo 1869636 35973143 := bstep (se 1 (by rfl) ⟨26979857, by rfl⟩ : syracuseStep 35973143 = 53959715) B53959715
theorem B1869883 : Blo 1869636 1869883 := bstep (se 1 (by rfl) ⟨1402412, by rfl⟩ : syracuseStep 1869883 = 2804825) B2804825
theorem B4737143 : Blo 1869636 4737143 := bstep (se 1 (by rfl) ⟨3552857, by rfl⟩ : syracuseStep 4737143 = 7105715) B7105715
theorem B1869959 : Blo 1869636 1869959 := bstep (se 1 (by rfl) ⟨1402469, by rfl⟩ : syracuseStep 1869959 = 2804939) B2804939
theorem B1869967 : Blo 1869636 1869967 := bstep (se 1 (by rfl) ⟨1402475, by rfl⟩ : syracuseStep 1869967 = 2804951) B2804951
theorem B1870011 : Blo 1869636 1870011 := bstep (se 1 (by rfl) ⟨1402508, by rfl⟩ : syracuseStep 1870011 = 2805017) B2805017
theorem B23963849 : Blo 1869636 23963849 := bstep (se 2 (by rfl) ⟨8986443, by rfl⟩ : syracuseStep 23963849 = 17972887) B17972887
theorem B1870087 : Blo 1869636 1870087 := bstep (se 1 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 1870087 = 2805131) B2805131
theorem B1870095 : Blo 1869636 1870095 := bstep (se 1 (by rfl) ⟨1402571, by rfl⟩ : syracuseStep 1870095 = 2805143) B2805143
theorem B3156239 : Blo 1869636 3156239 := bstep (se 1 (by rfl) ⟨2367179, by rfl⟩ : syracuseStep 3156239 = 4734359) B4734359
theorem B1870139 : Blo 1869636 1870139 := bstep (se 1 (by rfl) ⟨1402604, by rfl⟩ : syracuseStep 1870139 = 2805209) B2805209
theorem B1870215 : Blo 1869636 1870215 := bstep (se 1 (by rfl) ⟨1402661, by rfl⟩ : syracuseStep 1870215 = 2805323) B2805323
theorem B1870223 : Blo 1869636 1870223 := bstep (se 1 (by rfl) ⟨1402667, by rfl⟩ : syracuseStep 1870223 = 2805335) B2805335
theorem B10652057 : Blo 1869636 10652057 := bstep (se 2 (by rfl) ⟨3994521, by rfl⟩ : syracuseStep 10652057 = 7989043) B7989043
theorem B1870267 : Blo 1869636 1870267 := bstep (se 1 (by rfl) ⟨1402700, by rfl⟩ : syracuseStep 1870267 = 2805401) B2805401
theorem B15976925 : Blo 1869636 15976925 := bstep (se 3 (by rfl) ⟨2995673, by rfl⟩ : syracuseStep 15976925 = 5991347) B5991347
theorem B4557313 : Blo 1869636 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B1870343 : Blo 1869636 1870343 := bstep (se 1 (by rfl) ⟨1402757, by rfl⟩ : syracuseStep 1870343 = 2805515) B2805515
theorem B1870351 : Blo 1869636 1870351 := bstep (se 1 (by rfl) ⟨1402763, by rfl⟩ : syracuseStep 1870351 = 2805527) B2805527
theorem B1870395 : Blo 1869636 1870395 := bstep (se 1 (by rfl) ⟨1402796, by rfl⟩ : syracuseStep 1870395 = 2805593) B2805593
theorem B1870471 : Blo 1869636 1870471 := bstep (se 1 (by rfl) ⟨1402853, by rfl⟩ : syracuseStep 1870471 = 2805707) B2805707
theorem B1870479 : Blo 1869636 1870479 := bstep (se 1 (by rfl) ⟨1402859, by rfl⟩ : syracuseStep 1870479 = 2805719) B2805719
theorem B3549881 : Blo 1869636 3549881 := bstep (se 2 (by rfl) ⟨1331205, by rfl⟩ : syracuseStep 3549881 = 2662411) B2662411
theorem B1870523 : Blo 1869636 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B12315329 : Blo 1869636 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B6310601 : Blo 1869636 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B2804471 : Blo 1869636 2804471 := bstep (se 1 (by rfl) ⟨2103353, by rfl⟩ : syracuseStep 2804471 = 4206707) B4206707
theorem B1870599 : Blo 1869636 1870599 := bstep (se 1 (by rfl) ⟨1402949, by rfl⟩ : syracuseStep 1870599 = 2805899) B2805899
theorem B2804495 : Blo 1869636 2804495 := bstep (se 1 (by rfl) ⟨2103371, by rfl⟩ : syracuseStep 2804495 = 4206743) B4206743
theorem B1870607 : Blo 1869636 1870607 := bstep (se 1 (by rfl) ⟨1402955, by rfl⟩ : syracuseStep 1870607 = 2805911) B2805911
theorem B3156779 : Blo 1869636 3156779 := bstep (se 1 (by rfl) ⟨2367584, by rfl⟩ : syracuseStep 3156779 = 4735169) B4735169
theorem B2804537 : Blo 1869636 2804537 := bstep (se 2 (by rfl) ⟨1051701, by rfl⟩ : syracuseStep 2804537 = 2103403) B2103403
theorem B1870651 : Blo 1869636 1870651 := bstep (se 1 (by rfl) ⟨1402988, by rfl⟩ : syracuseStep 1870651 = 2805977) B2805977
theorem B3001207 : Blo 1869636 3001207 := bstep (se 1 (by rfl) ⟨2250905, by rfl⟩ : syracuseStep 3001207 = 4501811) B4501811
theorem B2804615 : Blo 1869636 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B1870727 : Blo 1869636 1870727 := bstep (se 1 (by rfl) ⟨1403045, by rfl⟩ : syracuseStep 1870727 = 2806091) B2806091
theorem B1870735 : Blo 1869636 1870735 := bstep (se 1 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 1870735 = 2806103) B2806103
theorem B7105427 : Blo 1869636 7105427 := bstep (se 1 (by rfl) ⟨5329070, by rfl⟩ : syracuseStep 7105427 = 10658141) B10658141
theorem B2804651 : Blo 1869636 2804651 := bstep (se 1 (by rfl) ⟨2103488, by rfl⟩ : syracuseStep 2804651 = 4206977) B4206977
theorem B1870779 : Blo 1869636 1870779 := bstep (se 1 (by rfl) ⟨1403084, by rfl⟩ : syracuseStep 1870779 = 2806169) B2806169
theorem B2804681 : Blo 1869636 2804681 := bstep (se 2 (by rfl) ⟨1051755, by rfl⟩ : syracuseStep 2804681 = 2103511) B2103511
theorem B1870855 : Blo 1869636 1870855 := bstep (se 1 (by rfl) ⟨1403141, by rfl⟩ : syracuseStep 1870855 = 2806283) B2806283
theorem B2845703 : Blo 1869636 2845703 := bstep (se 1 (by rfl) ⟨2134277, by rfl⟩ : syracuseStep 2845703 = 4268555) B4268555
theorem B3550223 : Blo 1869636 3550223 := bstep (se 1 (by rfl) ⟨2662667, by rfl⟩ : syracuseStep 3550223 = 5325335) B5325335
theorem B1870863 : Blo 1869636 1870863 := bstep (se 1 (by rfl) ⟨1403147, by rfl⟩ : syracuseStep 1870863 = 2806295) B2806295
theorem B2804795 : Blo 1869636 2804795 := bstep (se 1 (by rfl) ⟨2103596, by rfl⟩ : syracuseStep 2804795 = 4207193) B4207193
theorem B1870907 : Blo 1869636 1870907 := bstep (se 1 (by rfl) ⟨1403180, by rfl⟩ : syracuseStep 1870907 = 2806361) B2806361
theorem B9473111 : Blo 1869636 9473111 := bstep (se 1 (by rfl) ⟨7104833, by rfl⟩ : syracuseStep 9473111 = 14209667) B14209667
theorem B2804855 : Blo 1869636 2804855 := bstep (se 1 (by rfl) ⟨2103641, by rfl⟩ : syracuseStep 2804855 = 4207283) B4207283
theorem B1870983 : Blo 1869636 1870983 := bstep (se 1 (by rfl) ⟨1403237, by rfl⟩ : syracuseStep 1870983 = 2806475) B2806475
theorem B2804879 : Blo 1869636 2804879 := bstep (se 1 (by rfl) ⟨2103659, by rfl⟩ : syracuseStep 2804879 = 4207319) B4207319
theorem B1870991 : Blo 1869636 1870991 := bstep (se 1 (by rfl) ⟨1403243, by rfl⟩ : syracuseStep 1870991 = 2806487) B2806487
theorem B4492435 : Blo 1869636 4492435 := bstep (se 1 (by rfl) ⟨3369326, by rfl⟩ : syracuseStep 4492435 = 6738653) B6738653
theorem B40995989 : Blo 1869636 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B2804921 : Blo 1869636 2804921 := bstep (se 2 (by rfl) ⟨1051845, by rfl⟩ : syracuseStep 2804921 = 2103691) B2103691
theorem B3157177 : Blo 1869636 3157177 := bstep (se 2 (by rfl) ⟨1183941, by rfl⟩ : syracuseStep 3157177 = 2367883) B2367883
theorem B1871035 : Blo 1869636 1871035 := bstep (se 1 (by rfl) ⟨1403276, by rfl⟩ : syracuseStep 1871035 = 2806553) B2806553
theorem B13479149 : Blo 1869636 13479149 := bstep (se 3 (by rfl) ⟨2527340, by rfl⟩ : syracuseStep 13479149 = 5054681) B5054681
theorem B2804999 : Blo 1869636 2804999 := bstep (se 1 (by rfl) ⟨2103749, by rfl⟩ : syracuseStep 2804999 = 4207499) B4207499
theorem B1871111 : Blo 1869636 1871111 := bstep (se 1 (by rfl) ⟨1403333, by rfl⟩ : syracuseStep 1871111 = 2806667) B2806667
theorem B1871119 : Blo 1869636 1871119 := bstep (se 1 (by rfl) ⟨1403339, by rfl⟩ : syracuseStep 1871119 = 2806679) B2806679
theorem B2805035 : Blo 1869636 2805035 := bstep (se 1 (by rfl) ⟨2103776, by rfl⟩ : syracuseStep 2805035 = 4207553) B4207553
theorem B1871163 : Blo 1869636 1871163 := bstep (se 1 (by rfl) ⟨1403372, by rfl⟩ : syracuseStep 1871163 = 2806745) B2806745
theorem B2805065 : Blo 1869636 2805065 := bstep (se 2 (by rfl) ⟨1051899, by rfl⟩ : syracuseStep 2805065 = 2103799) B2103799
theorem B6311303 : Blo 1869636 6311303 := bstep (se 1 (by rfl) ⟨4733477, by rfl⟩ : syracuseStep 6311303 = 9466955) B9466955
theorem B1871239 : Blo 1869636 1871239 := bstep (se 1 (by rfl) ⟨1403429, by rfl⟩ : syracuseStep 1871239 = 2806859) B2806859
theorem B7105927 : Blo 1869636 7105927 := bstep (se 1 (by rfl) ⟨5329445, by rfl⟩ : syracuseStep 7105927 = 10658891) B10658891
theorem B1871247 : Blo 1869636 1871247 := bstep (se 1 (by rfl) ⟨1403435, by rfl⟩ : syracuseStep 1871247 = 2806871) B2806871
theorem B2805179 : Blo 1869636 2805179 := bstep (se 1 (by rfl) ⟨2103884, by rfl⟩ : syracuseStep 2805179 = 4207769) B4207769
theorem B1871291 : Blo 1869636 1871291 := bstep (se 1 (by rfl) ⟨1403468, by rfl⟩ : syracuseStep 1871291 = 2806937) B2806937
theorem B15175133 : Blo 1869636 15175133 := bstep (se 3 (by rfl) ⟨2845337, by rfl⟩ : syracuseStep 15175133 = 5690675) B5690675
theorem B2805239 : Blo 1869636 2805239 := bstep (se 1 (by rfl) ⟨2103929, by rfl⟩ : syracuseStep 2805239 = 4207859) B4207859
theorem B1871367 : Blo 1869636 1871367 := bstep (se 1 (by rfl) ⟨1403525, by rfl⟩ : syracuseStep 1871367 = 2807051) B2807051
theorem B2805263 : Blo 1869636 2805263 := bstep (se 1 (by rfl) ⟨2103947, by rfl⟩ : syracuseStep 2805263 = 4207895) B4207895
theorem B1871375 : Blo 1869636 1871375 := bstep (se 1 (by rfl) ⟨1403531, by rfl⟩ : syracuseStep 1871375 = 2807063) B2807063
theorem B2805305 : Blo 1869636 2805305 := bstep (se 2 (by rfl) ⟨1051989, by rfl⟩ : syracuseStep 2805305 = 2103979) B2103979
theorem B5328443 : Blo 1869636 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B1871419 : Blo 1869636 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B9473597 : Blo 1869636 9473597 := bstep (se 3 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 9473597 = 3552599) B3552599
theorem B2805383 : Blo 1869636 2805383 := bstep (se 1 (by rfl) ⟨2104037, by rfl⟩ : syracuseStep 2805383 = 4208075) B4208075
theorem B1871495 : Blo 1869636 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B1871503 : Blo 1869636 1871503 := bstep (se 1 (by rfl) ⟨1403627, by rfl⟩ : syracuseStep 1871503 = 2807255) B2807255
theorem B2805419 : Blo 1869636 2805419 := bstep (se 1 (by rfl) ⟨2104064, by rfl⟩ : syracuseStep 2805419 = 4208129) B4208129
theorem B1871547 : Blo 1869636 1871547 := bstep (se 1 (by rfl) ⟨1403660, by rfl⟩ : syracuseStep 1871547 = 2807321) B2807321
theorem B2805449 : Blo 1869636 2805449 := bstep (se 2 (by rfl) ⟨1052043, by rfl⟩ : syracuseStep 2805449 = 2104087) B2104087
theorem B6311681 : Blo 1869636 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B5992193 : Blo 1869636 5992193 := bstep (se 2 (by rfl) ⟨2247072, by rfl⟩ : syracuseStep 5992193 = 4494145) B4494145
theorem B1871623 : Blo 1869636 1871623 := bstep (se 1 (by rfl) ⟨1403717, by rfl⟩ : syracuseStep 1871623 = 2807435) B2807435
theorem B1871631 : Blo 1869636 1871631 := bstep (se 1 (by rfl) ⟨1403723, by rfl⟩ : syracuseStep 1871631 = 2807447) B2807447
theorem B9465659 : Blo 1869636 9465659 := bstep (se 1 (by rfl) ⟨7099244, by rfl⟩ : syracuseStep 9465659 = 14198489) B14198489
theorem B2805563 : Blo 1869636 2805563 := bstep (se 1 (by rfl) ⟨2104172, by rfl⟩ : syracuseStep 2805563 = 4208345) B4208345
theorem B3551035 : Blo 1869636 3551035 := bstep (se 1 (by rfl) ⟨2663276, by rfl⟩ : syracuseStep 3551035 = 5326553) B5326553
theorem B2805623 : Blo 1869636 2805623 := bstep (se 1 (by rfl) ⟨2104217, by rfl⟩ : syracuseStep 2805623 = 4208435) B4208435
theorem B3157879 : Blo 1869636 3157879 := bstep (se 1 (by rfl) ⟨2368409, by rfl⟩ : syracuseStep 3157879 = 4736819) B4736819
theorem B3551111 : Blo 1869636 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B3846023 : Blo 1869636 3846023 := bstep (se 1 (by rfl) ⟨2884517, by rfl⟩ : syracuseStep 3846023 = 5769035) B5769035
theorem B2805647 : Blo 1869636 2805647 := bstep (se 1 (by rfl) ⟨2104235, by rfl⟩ : syracuseStep 2805647 = 4208471) B4208471
theorem B2805689 : Blo 1869636 2805689 := bstep (se 2 (by rfl) ⟨1052133, by rfl⟩ : syracuseStep 2805689 = 2104267) B2104267
theorem B9465821 : Blo 1869636 9465821 := bstep (se 3 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 9465821 = 3549683) B3549683
theorem B2805767 : Blo 1869636 2805767 := bstep (se 1 (by rfl) ⟨2104325, by rfl⟩ : syracuseStep 2805767 = 4208651) B4208651
theorem B2805803 : Blo 1869636 2805803 := bstep (se 1 (by rfl) ⟨2104352, by rfl⟩ : syracuseStep 2805803 = 4208705) B4208705
theorem B3158075 : Blo 1869636 3158075 := bstep (se 1 (by rfl) ⟨2368556, by rfl⟩ : syracuseStep 3158075 = 4737113) B4737113
theorem B2805833 : Blo 1869636 2805833 := bstep (se 2 (by rfl) ⟨1052187, by rfl⟩ : syracuseStep 2805833 = 2104375) B2104375
theorem B14200919 : Blo 1869636 14200919 := bstep (se 1 (by rfl) ⟨10650689, by rfl⟩ : syracuseStep 14200919 = 21301379) B21301379
theorem B5329081 : Blo 1869636 5329081 := bstep (se 2 (by rfl) ⟨1998405, by rfl⟩ : syracuseStep 5329081 = 3996811) B3996811
theorem B2805947 : Blo 1869636 2805947 := bstep (se 1 (by rfl) ⟨2104460, by rfl⟩ : syracuseStep 2805947 = 4208921) B4208921
theorem B2806007 : Blo 1869636 2806007 := bstep (se 1 (by rfl) ⟨2104505, by rfl⟩ : syracuseStep 2806007 = 4209011) B4209011
theorem B2806031 : Blo 1869636 2806031 := bstep (se 1 (by rfl) ⟨2104523, by rfl⟩ : syracuseStep 2806031 = 4209047) B4209047
theorem B9466145 : Blo 1869636 9466145 := bstep (se 2 (by rfl) ⟨3549804, by rfl⟩ : syracuseStep 9466145 = 7099609) B7099609
theorem B3551521 : Blo 1869636 3551521 := bstep (se 2 (by rfl) ⟨1331820, by rfl⟩ : syracuseStep 3551521 = 2663641) B2663641
theorem B2806073 : Blo 1869636 2806073 := bstep (se 2 (by rfl) ⟨1052277, by rfl⟩ : syracuseStep 2806073 = 2104555) B2104555
theorem B2806151 : Blo 1869636 2806151 := bstep (se 1 (by rfl) ⟨2104613, by rfl⟩ : syracuseStep 2806151 = 4209227) B4209227
theorem B4206995 : Blo 1869636 4206995 := bstep (se 1 (by rfl) ⟨3155246, by rfl⟩ : syracuseStep 4206995 = 6310493) B6310493
theorem B2806187 : Blo 1869636 2806187 := bstep (se 1 (by rfl) ⟨2104640, by rfl⟩ : syracuseStep 2806187 = 4209281) B4209281
theorem B4207049 : Blo 1869636 4207049 := bstep (se 2 (by rfl) ⟨1577643, by rfl⟩ : syracuseStep 4207049 = 3155287) B3155287
theorem B2806217 : Blo 1869636 2806217 := bstep (se 2 (by rfl) ⟨1052331, by rfl⟩ : syracuseStep 2806217 = 2104663) B2104663
theorem B6312491 : Blo 1869636 6312491 := bstep (se 1 (by rfl) ⟨4734368, by rfl⟩ : syracuseStep 6312491 = 9468737) B9468737
theorem B2699833 : Blo 1869636 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B2806331 : Blo 1869636 2806331 := bstep (se 1 (by rfl) ⟨2104748, by rfl⟩ : syracuseStep 2806331 = 4209497) B4209497
theorem B7098941 : Blo 1869636 7098941 := bstep (se 3 (by rfl) ⟨1331051, by rfl⟩ : syracuseStep 7098941 = 2662103) B2662103
theorem B5329469 : Blo 1869636 5329469 := bstep (se 3 (by rfl) ⟨999275, by rfl⟩ : syracuseStep 5329469 = 1998551) B1998551
theorem B2806391 : Blo 1869636 2806391 := bstep (se 1 (by rfl) ⟨2104793, by rfl⟩ : syracuseStep 2806391 = 4209587) B4209587
theorem B3551863 : Blo 1869636 3551863 := bstep (se 1 (by rfl) ⟨2663897, by rfl⟩ : syracuseStep 3551863 = 5327795) B5327795
theorem B2806415 : Blo 1869636 2806415 := bstep (se 1 (by rfl) ⟨2104811, by rfl⟩ : syracuseStep 2806415 = 4209623) B4209623
theorem B1897103 : Blo 1869636 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B2806457 : Blo 1869636 2806457 := bstep (se 2 (by rfl) ⟨1052421, by rfl⟩ : syracuseStep 2806457 = 2104843) B2104843
theorem B53916353 : Blo 1869636 53916353 := bstep (se 2 (by rfl) ⟨20218632, by rfl⟩ : syracuseStep 53916353 = 40437265) B40437265
theorem B8991425 : Blo 1869636 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B2806535 : Blo 1869636 2806535 := bstep (se 1 (by rfl) ⟨2104901, by rfl⟩ : syracuseStep 2806535 = 4209803) B4209803
theorem B2806571 : Blo 1869636 2806571 := bstep (se 1 (by rfl) ⟨2104928, by rfl⟩ : syracuseStep 2806571 = 4209857) B4209857
theorem B15979315 : Blo 1869636 15979315 := bstep (se 1 (by rfl) ⟨11984486, by rfl⟩ : syracuseStep 15979315 = 23968973) B23968973
theorem B2806601 : Blo 1869636 2806601 := bstep (se 2 (by rfl) ⟨1052475, by rfl⟩ : syracuseStep 2806601 = 2104951) B2104951
theorem B8991577 : Blo 1869636 8991577 := bstep (se 2 (by rfl) ⟨3371841, by rfl⟩ : syracuseStep 8991577 = 6743683) B6743683
theorem B2528119 : Blo 1869636 2528119 := bstep (se 1 (by rfl) ⟨1896089, by rfl⟩ : syracuseStep 2528119 = 3792179) B3792179
theorem B2806715 : Blo 1869636 2806715 := bstep (se 1 (by rfl) ⟨2105036, by rfl⟩ : syracuseStep 2806715 = 4210073) B4210073
theorem B2806775 : Blo 1869636 2806775 := bstep (se 1 (by rfl) ⟨2105081, by rfl⟩ : syracuseStep 2806775 = 4210163) B4210163
theorem B2806799 : Blo 1869636 2806799 := bstep (se 1 (by rfl) ⟨2105099, by rfl⟩ : syracuseStep 2806799 = 4210199) B4210199
theorem B2806841 : Blo 1869636 2806841 := bstep (se 2 (by rfl) ⟨1052565, by rfl⟩ : syracuseStep 2806841 = 2105131) B2105131
theorem B4797559 : Blo 1869636 4797559 := bstep (se 1 (by rfl) ⟨3598169, by rfl⟩ : syracuseStep 4797559 = 7196339) B7196339
theorem B18224261 : Blo 1869636 18224261 := bstep (se 4 (by rfl) ⟨1708524, by rfl⟩ : syracuseStep 18224261 = 3417049) B3417049
theorem B4207751 : Blo 1869636 4207751 := bstep (se 1 (by rfl) ⟨3155813, by rfl⟩ : syracuseStep 4207751 = 6311627) B6311627
theorem B2806919 : Blo 1869636 2806919 := bstep (se 1 (by rfl) ⟨2105189, by rfl⟩ : syracuseStep 2806919 = 4210379) B4210379
theorem B3372167 : Blo 1869636 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B2806955 : Blo 1869636 2806955 := bstep (se 1 (by rfl) ⟨2105216, by rfl⟩ : syracuseStep 2806955 = 4210433) B4210433
theorem B3200185 : Blo 1869636 3200185 := bstep (se 2 (by rfl) ⟨1200069, by rfl⟩ : syracuseStep 3200185 = 2400139) B2400139
theorem B2806985 : Blo 1869636 2806985 := bstep (se 2 (by rfl) ⟨1052619, by rfl⟩ : syracuseStep 2806985 = 2105239) B2105239
theorem B9467117 : Blo 1869636 9467117 := bstep (se 3 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 9467117 = 3550169) B3550169
theorem B4207931 : Blo 1869636 4207931 := bstep (se 1 (by rfl) ⟨3155948, by rfl⟩ : syracuseStep 4207931 = 6311897) B6311897
theorem B2807099 : Blo 1869636 2807099 := bstep (se 1 (by rfl) ⟨2105324, by rfl⟩ : syracuseStep 2807099 = 4210649) B4210649
theorem B2807159 : Blo 1869636 2807159 := bstep (se 1 (by rfl) ⟨2105369, by rfl⟩ : syracuseStep 2807159 = 4210739) B4210739
theorem B2807183 : Blo 1869636 2807183 := bstep (se 1 (by rfl) ⟨2105387, by rfl⟩ : syracuseStep 2807183 = 4210775) B4210775
theorem B57595313 : Blo 1869636 57595313 := bstep (se 2 (by rfl) ⟨21598242, by rfl⟩ : syracuseStep 57595313 = 43196485) B43196485
theorem B4208057 : Blo 1869636 4208057 := bstep (se 2 (by rfl) ⟨1578021, by rfl⟩ : syracuseStep 4208057 = 3156043) B3156043
theorem B2807225 : Blo 1869636 2807225 := bstep (se 2 (by rfl) ⟨1052709, by rfl⟩ : syracuseStep 2807225 = 2105419) B2105419
theorem B20215261 : Blo 1869636 20215261 := bstep (se 3 (by rfl) ⟨3790361, by rfl⟩ : syracuseStep 20215261 = 7580723) B7580723
theorem B2807303 : Blo 1869636 2807303 := bstep (se 1 (by rfl) ⟨2105477, by rfl⟩ : syracuseStep 2807303 = 4210955) B4210955
theorem B5994013 : Blo 1869636 5994013 := bstep (se 3 (by rfl) ⟨1123877, by rfl⟩ : syracuseStep 5994013 = 2247755) B2247755
theorem B2807339 : Blo 1869636 2807339 := bstep (se 1 (by rfl) ⟨2105504, by rfl⟩ : syracuseStep 2807339 = 4211009) B4211009
theorem B2807369 : Blo 1869636 2807369 := bstep (se 2 (by rfl) ⟨1052763, by rfl⟩ : syracuseStep 2807369 = 2105527) B2105527
theorem B71882315 : Blo 1869636 71882315 := bstep (se 1 (by rfl) ⟨53911736, by rfl⟩ : syracuseStep 71882315 = 107823473) B107823473
theorem B10114679 : Blo 1869636 10114679 := bstep (se 1 (by rfl) ⟨7586009, by rfl⟩ : syracuseStep 10114679 = 15172019) B15172019
theorem B983684837 : Blo 1869636 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B4208399 : Blo 1869636 4208399 := bstep (se 1 (by rfl) ⟨3156299, by rfl⟩ : syracuseStep 4208399 = 6312599) B6312599
theorem B5691151 : Blo 1869636 5691151 := bstep (se 1 (by rfl) ⟨4268363, by rfl⟩ : syracuseStep 5691151 = 8536727) B8536727
theorem B4208417 : Blo 1869636 4208417 := bstep (se 2 (by rfl) ⟨1578156, by rfl⟩ : syracuseStep 4208417 = 3156313) B3156313
theorem B6313787 : Blo 1869636 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B4798409 : Blo 1869636 4798409 := bstep (se 2 (by rfl) ⟨1799403, by rfl⟩ : syracuseStep 4798409 = 3598807) B3598807
theorem B7100369 : Blo 1869636 7100369 := bstep (se 2 (by rfl) ⟨2662638, by rfl⟩ : syracuseStep 7100369 = 5325277) B5325277
theorem B4495375 : Blo 1869636 4495375 := bstep (se 1 (by rfl) ⟨3371531, by rfl⟩ : syracuseStep 4495375 = 6743063) B6743063
theorem B9467927 : Blo 1869636 9467927 := bstep (se 1 (by rfl) ⟨7100945, by rfl⟩ : syracuseStep 9467927 = 14201891) B14201891
theorem B4208759 : Blo 1869636 4208759 := bstep (se 1 (by rfl) ⟨3156569, by rfl⟩ : syracuseStep 4208759 = 6313139) B6313139
theorem B4733063 : Blo 1869636 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B2103439 : Blo 1869636 2103439 := bstep (se 1 (by rfl) ⟨1577579, by rfl⟩ : syracuseStep 2103439 = 3155159) B3155159
theorem B4733113 : Blo 1869636 4733113 := bstep (se 2 (by rfl) ⟨1774917, by rfl⟩ : syracuseStep 4733113 = 3549835) B3549835
theorem B6314273 : Blo 1869636 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B4208939 : Blo 1869636 4208939 := bstep (se 1 (by rfl) ⟨3156704, by rfl⟩ : syracuseStep 4208939 = 6313409) B6313409
theorem B8534407 : Blo 1869636 8534407 := bstep (se 1 (by rfl) ⟨6400805, by rfl⟩ : syracuseStep 8534407 = 12801611) B12801611
theorem B2103943 : Blo 1869636 2103943 := bstep (se 1 (by rfl) ⟨1577957, by rfl⟩ : syracuseStep 2103943 = 3155915) B3155915
theorem B4209299 : Blo 1869636 4209299 := bstep (se 1 (by rfl) ⟨3156974, by rfl⟩ : syracuseStep 4209299 = 6313949) B6313949
theorem B4209353 : Blo 1869636 4209353 := bstep (se 2 (by rfl) ⟨1578507, by rfl⟩ : syracuseStep 4209353 = 3157015) B3157015
theorem B4733711 : Blo 1869636 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B2104123 : Blo 1869636 2104123 := bstep (se 1 (by rfl) ⟨1578092, by rfl⟩ : syracuseStep 2104123 = 3156185) B3156185
theorem B6314867 : Blo 1869636 6314867 := bstep (se 1 (by rfl) ⟨4736150, by rfl⟩ : syracuseStep 6314867 = 9472301) B9472301
theorem B9239411 : Blo 1869636 9239411 := bstep (se 1 (by rfl) ⟨6929558, by rfl⟩ : syracuseStep 9239411 = 13859117) B13859117
theorem B23976971 : Blo 1869636 23976971 := bstep (se 1 (by rfl) ⟨17982728, by rfl⟩ : syracuseStep 23976971 = 35965457) B35965457
theorem B2997263 : Blo 1869636 2997263 := bstep (se 1 (by rfl) ⟨2247947, by rfl⟩ : syracuseStep 2997263 = 4495895) B4495895
theorem B46767253 : Blo 1869636 46767253 := bstep (se 6 (by rfl) ⟨1096107, by rfl⟩ : syracuseStep 46767253 = 2192215) B2192215
theorem B7986377 : Blo 1869636 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B2104591 : Blo 1869636 2104591 := bstep (se 1 (by rfl) ⟨1578443, by rfl⟩ : syracuseStep 2104591 = 3156887) B3156887
theorem B5324093 : Blo 1869636 5324093 := bstep (se 3 (by rfl) ⟨998267, by rfl⟩ : syracuseStep 5324093 = 1996535) B1996535
theorem B4210055 : Blo 1869636 4210055 := bstep (se 1 (by rfl) ⟨3157541, by rfl⟩ : syracuseStep 4210055 = 6315083) B6315083
theorem B30768569 : Blo 1869636 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B4734409 : Blo 1869636 4734409 := bstep (se 2 (by rfl) ⟨1775403, by rfl⟩ : syracuseStep 4734409 = 3550807) B3550807
theorem B11378141 : Blo 1869636 11378141 := bstep (se 3 (by rfl) ⟨2133401, by rfl⟩ : syracuseStep 11378141 = 4266803) B4266803
theorem B4324907 : Blo 1869636 4324907 := bstep (se 1 (by rfl) ⟨3243680, by rfl⟩ : syracuseStep 4324907 = 6487361) B6487361
theorem B4210235 : Blo 1869636 4210235 := bstep (se 1 (by rfl) ⟨3157676, by rfl⟩ : syracuseStep 4210235 = 6315353) B6315353
theorem B4734551 : Blo 1869636 4734551 := bstep (se 1 (by rfl) ⟨3550913, by rfl⟩ : syracuseStep 4734551 = 7101827) B7101827
theorem B7102039 : Blo 1869636 7102039 := bstep (se 1 (by rfl) ⟨5326529, by rfl⟩ : syracuseStep 7102039 = 10653059) B10653059
theorem B2399863 : Blo 1869636 2399863 := bstep (se 1 (by rfl) ⟨1799897, by rfl⟩ : syracuseStep 2399863 = 3599795) B3599795
theorem B4210361 : Blo 1869636 4210361 := bstep (se 2 (by rfl) ⟨1578885, by rfl⟩ : syracuseStep 4210361 = 3157771) B3157771
theorem B2662075 : Blo 1869636 2662075 := bstep (se 1 (by rfl) ⟨1996556, by rfl⟩ : syracuseStep 2662075 = 3993113) B3993113
theorem B2105095 : Blo 1869636 2105095 := bstep (se 1 (by rfl) ⟨1578821, by rfl⟩ : syracuseStep 2105095 = 3157643) B3157643
theorem B20234033 : Blo 1869636 20234033 := bstep (se 2 (by rfl) ⟨7587762, by rfl⟩ : syracuseStep 20234033 = 15175525) B15175525
theorem B19201843 : Blo 1869636 19201843 := bstep (se 1 (by rfl) ⟨14401382, by rfl⟩ : syracuseStep 19201843 = 28802765) B28802765
theorem B21307211 : Blo 1869636 21307211 := bstep (se 1 (by rfl) ⟨15980408, by rfl⟩ : syracuseStep 21307211 = 31960817) B31960817
theorem B7102343 : Blo 1869636 7102343 := bstep (se 1 (by rfl) ⟨5326757, by rfl⟩ : syracuseStep 7102343 = 10653515) B10653515
theorem B2105275 : Blo 1869636 2105275 := bstep (se 1 (by rfl) ⟨1578956, by rfl⟩ : syracuseStep 2105275 = 3157913) B3157913
theorem B62357521 : Blo 1869636 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B2105383 : Blo 1869636 2105383 := bstep (se 1 (by rfl) ⟨1579037, by rfl⟩ : syracuseStep 2105383 = 3158075) B3158075
theorem B5324879 : Blo 1869636 5324879 := bstep (se 1 (by rfl) ⟨3993659, by rfl⟩ : syracuseStep 5324879 = 7987319) B7987319
theorem B9470033 : Blo 1869636 9470033 := bstep (se 2 (by rfl) ⟨3551262, by rfl⟩ : syracuseStep 9470033 = 7102525) B7102525
theorem B28787003 : Blo 1869636 28787003 := bstep (se 1 (by rfl) ⟨21590252, by rfl⟩ : syracuseStep 28787003 = 43180505) B43180505
theorem B5767529 : Blo 1869636 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B4735361 : Blo 1869636 4735361 := bstep (se 2 (by rfl) ⟨1775760, by rfl⟩ : syracuseStep 4735361 = 3551521) B3551521
theorem B11379209 : Blo 1869636 11379209 := bstep (se 2 (by rfl) ⟨4267203, by rfl⟩ : syracuseStep 11379209 = 8534407) B8534407
theorem B21299921 : Blo 1869636 21299921 := bstep (se 2 (by rfl) ⟨7987470, by rfl⟩ : syracuseStep 21299921 = 15974941) B15974941
theorem B26968787 : Blo 1869636 26968787 := bstep (se 1 (by rfl) ⟨20226590, by rfl⟩ : syracuseStep 26968787 = 40453181) B40453181
theorem B5325527 : Blo 1869636 5325527 := bstep (se 1 (by rfl) ⟨3994145, by rfl⟩ : syracuseStep 5325527 = 7988291) B7988291
theorem B12149507 : Blo 1869636 12149507 := bstep (se 1 (by rfl) ⟨9112130, by rfl⟩ : syracuseStep 12149507 = 18224261) B18224261
theorem B4735817 : Blo 1869636 4735817 := bstep (se 2 (by rfl) ⟨1775931, by rfl⟩ : syracuseStep 4735817 = 3551863) B3551863
theorem B38396875 : Blo 1869636 38396875 := bstep (se 1 (by rfl) ⟨28797656, by rfl⟩ : syracuseStep 38396875 = 57595313) B57595313
theorem B4736171 : Blo 1869636 4736171 := bstep (se 1 (by rfl) ⟨3552128, by rfl⟩ : syracuseStep 4736171 = 7104257) B7104257
theorem B30352805 : Blo 1869636 30352805 := bstep (se 4 (by rfl) ⟨2845575, by rfl⟩ : syracuseStep 30352805 = 5691151) B5691151
theorem B3155375 : Blo 1869636 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B15975899 : Blo 1869636 15975899 := bstep (se 1 (by rfl) ⟨11981924, by rfl⟩ : syracuseStep 15975899 = 23963849) B23963849
theorem B5989913 : Blo 1869636 5989913 := bstep (se 2 (by rfl) ⟨2246217, by rfl⟩ : syracuseStep 5989913 = 4492435) B4492435
theorem B102409829 : Blo 1869636 102409829 := bstep (se 4 (by rfl) ⟨9600921, by rfl⟩ : syracuseStep 102409829 = 19201843) B19201843
theorem B10651283 : Blo 1869636 10651283 := bstep (se 1 (by rfl) ⟨7988462, by rfl⟩ : syracuseStep 10651283 = 15976925) B15976925
theorem B8210219 : Blo 1869636 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B1869647 : Blo 1869636 1869647 := bstep (se 1 (by rfl) ⟨1402235, by rfl⟩ : syracuseStep 1869647 = 2804471) B2804471
theorem B1869663 : Blo 1869636 1869663 := bstep (se 1 (by rfl) ⟨1402247, by rfl⟩ : syracuseStep 1869663 = 2804495) B2804495
theorem B3155807 : Blo 1869636 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B1869691 : Blo 1869636 1869691 := bstep (se 1 (by rfl) ⟨1402268, by rfl⟩ : syracuseStep 1869691 = 2804537) B2804537
theorem B1869743 : Blo 1869636 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B4736951 : Blo 1869636 4736951 := bstep (se 1 (by rfl) ⟨3552713, by rfl⟩ : syracuseStep 4736951 = 7105427) B7105427
theorem B1869767 : Blo 1869636 1869767 := bstep (se 1 (by rfl) ⟨1402325, by rfl⟩ : syracuseStep 1869767 = 2804651) B2804651
theorem B26953681 : Blo 1869636 26953681 := bstep (se 2 (by rfl) ⟨10107630, by rfl⟩ : syracuseStep 26953681 = 20215261) B20215261
theorem B1869787 : Blo 1869636 1869787 := bstep (se 1 (by rfl) ⟨1402340, by rfl⟩ : syracuseStep 1869787 = 2804681) B2804681
theorem B15984647 : Blo 1869636 15984647 := bstep (se 1 (by rfl) ⟨11988485, by rfl⟩ : syracuseStep 15984647 = 23976971) B23976971
theorem B1869863 : Blo 1869636 1869863 := bstep (se 1 (by rfl) ⟨1402397, by rfl⟩ : syracuseStep 1869863 = 2804795) B2804795
theorem B1869903 : Blo 1869636 1869903 := bstep (se 1 (by rfl) ⟨1402427, by rfl⟩ : syracuseStep 1869903 = 2804855) B2804855
theorem B1869919 : Blo 1869636 1869919 := bstep (se 1 (by rfl) ⟨1402439, by rfl⟩ : syracuseStep 1869919 = 2804879) B2804879
theorem B27330659 : Blo 1869636 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B1869947 : Blo 1869636 1869947 := bstep (se 1 (by rfl) ⟨1402460, by rfl⟩ : syracuseStep 1869947 = 2804921) B2804921
theorem B1869999 : Blo 1869636 1869999 := bstep (se 1 (by rfl) ⟨1402499, by rfl⟩ : syracuseStep 1869999 = 2804999) B2804999
theorem B1870023 : Blo 1869636 1870023 := bstep (se 1 (by rfl) ⟨1402517, by rfl⟩ : syracuseStep 1870023 = 2805035) B2805035
theorem B3549395 : Blo 1869636 3549395 := bstep (se 1 (by rfl) ⟨2662046, by rfl⟩ : syracuseStep 3549395 = 5324093) B5324093
theorem B1870043 : Blo 1869636 1870043 := bstep (se 1 (by rfl) ⟨1402532, by rfl⟩ : syracuseStep 1870043 = 2805065) B2805065
theorem B3549433 : Blo 1869636 3549433 := bstep (se 2 (by rfl) ⟨1331037, by rfl⟩ : syracuseStep 3549433 = 2662075) B2662075
theorem B1870119 : Blo 1869636 1870119 := bstep (se 1 (by rfl) ⟨1402589, by rfl⟩ : syracuseStep 1870119 = 2805179) B2805179
theorem B1870159 : Blo 1869636 1870159 := bstep (se 1 (by rfl) ⟨1402619, by rfl⟩ : syracuseStep 1870159 = 2805239) B2805239
theorem B1870175 : Blo 1869636 1870175 := bstep (se 1 (by rfl) ⟨1402631, by rfl⟩ : syracuseStep 1870175 = 2805263) B2805263
theorem B1870203 : Blo 1869636 1870203 := bstep (se 1 (by rfl) ⟨1402652, by rfl⟩ : syracuseStep 1870203 = 2805305) B2805305
theorem B3156367 : Blo 1869636 3156367 := bstep (se 1 (by rfl) ⟨2367275, by rfl⟩ : syracuseStep 3156367 = 4734551) B4734551
theorem B1870255 : Blo 1869636 1870255 := bstep (se 1 (by rfl) ⟨1402691, by rfl⟩ : syracuseStep 1870255 = 2805383) B2805383
theorem B1870279 : Blo 1869636 1870279 := bstep (se 1 (by rfl) ⟨1402709, by rfl⟩ : syracuseStep 1870279 = 2805419) B2805419
theorem B1870299 : Blo 1869636 1870299 := bstep (se 1 (by rfl) ⟨1402724, by rfl⟩ : syracuseStep 1870299 = 2805449) B2805449
theorem B6310439 : Blo 1869636 6310439 := bstep (se 1 (by rfl) ⟨4732829, by rfl⟩ : syracuseStep 6310439 = 9465659) B9465659
theorem B1870375 : Blo 1869636 1870375 := bstep (se 1 (by rfl) ⟨1402781, by rfl⟩ : syracuseStep 1870375 = 2805563) B2805563
theorem B1870415 : Blo 1869636 1870415 := bstep (se 1 (by rfl) ⟨1402811, by rfl⟩ : syracuseStep 1870415 = 2805623) B2805623
theorem B1870431 : Blo 1869636 1870431 := bstep (se 1 (by rfl) ⟨1402823, by rfl⟩ : syracuseStep 1870431 = 2805647) B2805647
theorem B1870459 : Blo 1869636 1870459 := bstep (se 1 (by rfl) ⟨1402844, by rfl⟩ : syracuseStep 1870459 = 2805689) B2805689
theorem B6310547 : Blo 1869636 6310547 := bstep (se 1 (by rfl) ⟨4732910, by rfl⟩ : syracuseStep 6310547 = 9465821) B9465821
theorem B1870511 : Blo 1869636 1870511 := bstep (se 1 (by rfl) ⟨1402883, by rfl⟩ : syracuseStep 1870511 = 2805767) B2805767
theorem B7588541 : Blo 1869636 7588541 := bstep (se 3 (by rfl) ⟨1422851, by rfl⟩ : syracuseStep 7588541 = 2845703) B2845703
theorem B1870535 : Blo 1869636 1870535 := bstep (se 1 (by rfl) ⟨1402901, by rfl⟩ : syracuseStep 1870535 = 2805803) B2805803
theorem B1870555 : Blo 1869636 1870555 := bstep (se 1 (by rfl) ⟨1402916, by rfl⟩ : syracuseStep 1870555 = 2805833) B2805833
theorem B1870631 : Blo 1869636 1870631 := bstep (se 1 (by rfl) ⟨1402973, by rfl⟩ : syracuseStep 1870631 = 2805947) B2805947
theorem B1870671 : Blo 1869636 1870671 := bstep (se 1 (by rfl) ⟨1403003, by rfl⟩ : syracuseStep 1870671 = 2806007) B2806007
theorem B1870687 : Blo 1869636 1870687 := bstep (se 1 (by rfl) ⟨1403015, by rfl⟩ : syracuseStep 1870687 = 2806031) B2806031
theorem B2804585 : Blo 1869636 2804585 := bstep (se 2 (by rfl) ⟨1051719, by rfl⟩ : syracuseStep 2804585 = 2103439) B2103439
theorem B6310763 : Blo 1869636 6310763 := bstep (se 1 (by rfl) ⟨4733072, by rfl⟩ : syracuseStep 6310763 = 9466145) B9466145
theorem B1870715 : Blo 1869636 1870715 := bstep (se 1 (by rfl) ⟨1403036, by rfl⟩ : syracuseStep 1870715 = 2806073) B2806073
theorem B6310817 : Blo 1869636 6310817 := bstep (se 2 (by rfl) ⟨2366556, by rfl⟩ : syracuseStep 6310817 = 4733113) B4733113
theorem B7105441 : Blo 1869636 7105441 := bstep (se 2 (by rfl) ⟨2664540, by rfl⟩ : syracuseStep 7105441 = 5329081) B5329081
theorem B1870767 : Blo 1869636 1870767 := bstep (se 1 (by rfl) ⟨1403075, by rfl⟩ : syracuseStep 1870767 = 2806151) B2806151
theorem B2804663 : Blo 1869636 2804663 := bstep (se 1 (by rfl) ⟨2103497, by rfl⟩ : syracuseStep 2804663 = 4206995) B4206995
theorem B3550139 : Blo 1869636 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B1870791 : Blo 1869636 1870791 := bstep (se 1 (by rfl) ⟨1403093, by rfl⟩ : syracuseStep 1870791 = 2806187) B2806187
theorem B2804699 : Blo 1869636 2804699 := bstep (se 1 (by rfl) ⟨2103524, by rfl⟩ : syracuseStep 2804699 = 4207049) B4207049
theorem B1870811 : Blo 1869636 1870811 := bstep (se 1 (by rfl) ⟨1403108, by rfl⟩ : syracuseStep 1870811 = 2806217) B2806217
theorem B1870887 : Blo 1869636 1870887 := bstep (se 1 (by rfl) ⟨1403165, by rfl⟩ : syracuseStep 1870887 = 2806331) B2806331
theorem B3157049 : Blo 1869636 3157049 := bstep (se 2 (by rfl) ⟨1183893, by rfl⟩ : syracuseStep 3157049 = 2367787) B2367787
theorem B1870927 : Blo 1869636 1870927 := bstep (se 1 (by rfl) ⟨1403195, by rfl⟩ : syracuseStep 1870927 = 2806391) B2806391
theorem B1870943 : Blo 1869636 1870943 := bstep (se 1 (by rfl) ⟨1403207, by rfl⟩ : syracuseStep 1870943 = 2806415) B2806415
theorem B1870971 : Blo 1869636 1870971 := bstep (se 1 (by rfl) ⟨1403228, by rfl⟩ : syracuseStep 1870971 = 2806457) B2806457
theorem B1871023 : Blo 1869636 1871023 := bstep (se 1 (by rfl) ⟨1403267, by rfl⟩ : syracuseStep 1871023 = 2806535) B2806535
theorem B1871047 : Blo 1869636 1871047 := bstep (se 1 (by rfl) ⟨1403285, by rfl⟩ : syracuseStep 1871047 = 2806571) B2806571
theorem B1871067 : Blo 1869636 1871067 := bstep (se 1 (by rfl) ⟨1403300, by rfl⟩ : syracuseStep 1871067 = 2806601) B2806601
theorem B1871143 : Blo 1869636 1871143 := bstep (se 1 (by rfl) ⟨1403357, by rfl⟩ : syracuseStep 1871143 = 2806715) B2806715
theorem B1871183 : Blo 1869636 1871183 := bstep (se 1 (by rfl) ⟨1403387, by rfl⟩ : syracuseStep 1871183 = 2806775) B2806775
theorem B1871199 : Blo 1869636 1871199 := bstep (se 1 (by rfl) ⟨1403399, by rfl⟩ : syracuseStep 1871199 = 2806799) B2806799
theorem B1871227 : Blo 1869636 1871227 := bstep (se 1 (by rfl) ⟨1403420, by rfl⟩ : syracuseStep 1871227 = 2806841) B2806841
theorem B3550625 : Blo 1869636 3550625 := bstep (se 2 (by rfl) ⟨1331484, by rfl⟩ : syracuseStep 3550625 = 2662969) B2662969
theorem B3599777 : Blo 1869636 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B2805167 : Blo 1869636 2805167 := bstep (se 1 (by rfl) ⟨2103875, by rfl⟩ : syracuseStep 2805167 = 4207751) B4207751
theorem B1871279 : Blo 1869636 1871279 := bstep (se 1 (by rfl) ⟨1403459, by rfl⟩ : syracuseStep 1871279 = 2806919) B2806919
theorem B2248111 : Blo 1869636 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B1871303 : Blo 1869636 1871303 := bstep (se 1 (by rfl) ⟨1403477, by rfl⟩ : syracuseStep 1871303 = 2806955) B2806955
theorem B1871323 : Blo 1869636 1871323 := bstep (se 1 (by rfl) ⟨1403492, by rfl⟩ : syracuseStep 1871323 = 2806985) B2806985
theorem B6311411 : Blo 1869636 6311411 := bstep (se 1 (by rfl) ⟨4733558, by rfl⟩ : syracuseStep 6311411 = 9467117) B9467117
theorem B2805257 : Blo 1869636 2805257 := bstep (se 2 (by rfl) ⟨1051971, by rfl⟩ : syracuseStep 2805257 = 2103943) B2103943
theorem B2805287 : Blo 1869636 2805287 := bstep (se 1 (by rfl) ⟨2103965, by rfl⟩ : syracuseStep 2805287 = 4207931) B4207931
theorem B1871399 : Blo 1869636 1871399 := bstep (se 1 (by rfl) ⟨1403549, by rfl⟩ : syracuseStep 1871399 = 2807099) B2807099
theorem B1871439 : Blo 1869636 1871439 := bstep (se 1 (by rfl) ⟨1403579, by rfl⟩ : syracuseStep 1871439 = 2807159) B2807159
theorem B1871455 : Blo 1869636 1871455 := bstep (se 1 (by rfl) ⟨1403591, by rfl⟩ : syracuseStep 1871455 = 2807183) B2807183
theorem B2805371 : Blo 1869636 2805371 := bstep (se 1 (by rfl) ⟨2104028, by rfl⟩ : syracuseStep 2805371 = 4208057) B4208057
theorem B1871483 : Blo 1869636 1871483 := bstep (se 1 (by rfl) ⟨1403612, by rfl⟩ : syracuseStep 1871483 = 2807225) B2807225
theorem B8990347 : Blo 1869636 8990347 := bstep (se 1 (by rfl) ⟨6742760, by rfl⟩ : syracuseStep 8990347 = 13485521) B13485521
theorem B6401683 : Blo 1869636 6401683 := bstep (se 1 (by rfl) ⟨4801262, by rfl⟩ : syracuseStep 6401683 = 9602525) B9602525
theorem B3550891 : Blo 1869636 3550891 := bstep (se 1 (by rfl) ⟨2663168, by rfl⟩ : syracuseStep 3550891 = 5326337) B5326337
theorem B1871535 : Blo 1869636 1871535 := bstep (se 1 (by rfl) ⟨1403651, by rfl⟩ : syracuseStep 1871535 = 2807303) B2807303
theorem B1871559 : Blo 1869636 1871559 := bstep (se 1 (by rfl) ⟨1403669, by rfl⟩ : syracuseStep 1871559 = 2807339) B2807339
theorem B1871579 : Blo 1869636 1871579 := bstep (se 1 (by rfl) ⟨1403684, by rfl⟩ : syracuseStep 1871579 = 2807369) B2807369
theorem B19205869 : Blo 1869636 19205869 := bstep (se 3 (by rfl) ⟨3601100, by rfl⟩ : syracuseStep 19205869 = 7202201) B7202201
theorem B3157751 : Blo 1869636 3157751 := bstep (se 1 (by rfl) ⟨2368313, by rfl⟩ : syracuseStep 3157751 = 4736627) B4736627
theorem B2805497 : Blo 1869636 2805497 := bstep (se 2 (by rfl) ⟨1052061, by rfl⟩ : syracuseStep 2805497 = 2104123) B2104123
theorem B11988769 : Blo 1869636 11988769 := bstep (se 2 (by rfl) ⟨4495788, by rfl⟩ : syracuseStep 11988769 = 8991577) B8991577
theorem B655789891 : Blo 1869636 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B4001609 : Blo 1869636 4001609 := bstep (se 2 (by rfl) ⟨1500603, by rfl⟩ : syracuseStep 4001609 = 3001207) B3001207
theorem B3370825 : Blo 1869636 3370825 := bstep (se 2 (by rfl) ⟨1264059, by rfl⟩ : syracuseStep 3370825 = 2528119) B2528119
theorem B2805599 : Blo 1869636 2805599 := bstep (se 1 (by rfl) ⟨2104199, by rfl⟩ : syracuseStep 2805599 = 4208399) B4208399
theorem B2805611 : Blo 1869636 2805611 := bstep (se 1 (by rfl) ⟨2104208, by rfl⟩ : syracuseStep 2805611 = 4208417) B4208417
theorem B2699227 : Blo 1869636 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B3551195 : Blo 1869636 3551195 := bstep (se 1 (by rfl) ⟨2663396, by rfl⟩ : syracuseStep 3551195 = 5326793) B5326793
theorem B6311951 : Blo 1869636 6311951 := bstep (se 1 (by rfl) ⟨4733963, by rfl⟩ : syracuseStep 6311951 = 9467927) B9467927
theorem B23982095 : Blo 1869636 23982095 := bstep (se 1 (by rfl) ⟨17986571, by rfl⟩ : syracuseStep 23982095 = 35973143) B35973143
theorem B2805839 : Blo 1869636 2805839 := bstep (se 1 (by rfl) ⟨2104379, by rfl⟩ : syracuseStep 2805839 = 4208759) B4208759
theorem B3158095 : Blo 1869636 3158095 := bstep (se 1 (by rfl) ⟨2368571, by rfl⟩ : syracuseStep 3158095 = 4737143) B4737143
theorem B14209181 : Blo 1869636 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B2805959 : Blo 1869636 2805959 := bstep (se 1 (by rfl) ⟨2104469, by rfl⟩ : syracuseStep 2805959 = 4208939) B4208939
theorem B26972477 : Blo 1869636 26972477 := bstep (se 3 (by rfl) ⟨5057339, by rfl⟩ : syracuseStep 26972477 = 10114679) B10114679
theorem B3158345 : Blo 1869636 3158345 := bstep (se 2 (by rfl) ⟨1184379, by rfl⟩ : syracuseStep 3158345 = 2368759) B2368759
theorem B2806121 : Blo 1869636 2806121 := bstep (se 2 (by rfl) ⟨1052295, by rfl⟩ : syracuseStep 2806121 = 2104591) B2104591
theorem B5058941 : Blo 1869636 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B2806199 : Blo 1869636 2806199 := bstep (se 1 (by rfl) ⟨2104649, by rfl⟩ : syracuseStep 2806199 = 4209299) B4209299
theorem B4207067 : Blo 1869636 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B2806235 : Blo 1869636 2806235 := bstep (se 1 (by rfl) ⟨2104676, by rfl⟩ : syracuseStep 2806235 = 4209353) B4209353
theorem B9474569 : Blo 1869636 9474569 := bstep (se 2 (by rfl) ⟨3552963, by rfl⟩ : syracuseStep 9474569 = 7105927) B7105927
theorem B6312545 : Blo 1869636 6312545 := bstep (se 2 (by rfl) ⟨2367204, by rfl⟩ : syracuseStep 6312545 = 4734409) B4734409
theorem B7992017 : Blo 1869636 7992017 := bstep (se 2 (by rfl) ⟨2997006, by rfl⟩ : syracuseStep 7992017 = 5994013) B5994013
theorem B23966513 : Blo 1869636 23966513 := bstep (se 2 (by rfl) ⟨8987442, by rfl⟩ : syracuseStep 23966513 = 17974885) B17974885
theorem B3199817 : Blo 1869636 3199817 := bstep (se 2 (by rfl) ⟨1199931, by rfl⟩ : syracuseStep 3199817 = 2399863) B2399863
theorem B4207535 : Blo 1869636 4207535 := bstep (se 1 (by rfl) ⟨3155651, by rfl⟩ : syracuseStep 4207535 = 6311303) B6311303
theorem B2806703 : Blo 1869636 2806703 := bstep (se 1 (by rfl) ⟨2105027, by rfl⟩ : syracuseStep 2806703 = 4210055) B4210055
theorem B24638429 : Blo 1869636 24638429 := bstep (se 3 (by rfl) ⟨4619705, by rfl⟩ : syracuseStep 24638429 = 9239411) B9239411
theorem B3552265 : Blo 1869636 3552265 := bstep (se 2 (by rfl) ⟨1332099, by rfl⟩ : syracuseStep 3552265 = 2664199) B2664199
theorem B2806793 : Blo 1869636 2806793 := bstep (se 2 (by rfl) ⟨1052547, by rfl⟩ : syracuseStep 2806793 = 2105095) B2105095
theorem B2806823 : Blo 1869636 2806823 := bstep (se 1 (by rfl) ⟨2105117, by rfl⟩ : syracuseStep 2806823 = 4210235) B4210235
theorem B2806907 : Blo 1869636 2806907 := bstep (se 1 (by rfl) ⟨2105180, by rfl⟩ : syracuseStep 2806907 = 4210361) B4210361
theorem B4207787 : Blo 1869636 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B3994795 : Blo 1869636 3994795 := bstep (se 1 (by rfl) ⟨2996096, by rfl⟩ : syracuseStep 3994795 = 5992193) B5992193
theorem B13489355 : Blo 1869636 13489355 := bstep (se 1 (by rfl) ⟨10117016, by rfl⟩ : syracuseStep 13489355 = 20234033) B20234033
theorem B2807033 : Blo 1869636 2807033 := bstep (se 2 (by rfl) ⟨1052637, by rfl⟩ : syracuseStep 2807033 = 2105275) B2105275
theorem B2807135 : Blo 1869636 2807135 := bstep (se 1 (by rfl) ⟨2105351, by rfl⟩ : syracuseStep 2807135 = 4210703) B4210703
theorem B5993833 : Blo 1869636 5993833 := bstep (se 2 (by rfl) ⟨2247687, by rfl⟩ : syracuseStep 5993833 = 4495375) B4495375
theorem B2807147 : Blo 1869636 2807147 := bstep (se 1 (by rfl) ⟨2105360, by rfl⟩ : syracuseStep 2807147 = 4210721) B4210721
theorem B7992701 : Blo 1869636 7992701 := bstep (se 3 (by rfl) ⟨1498631, by rfl⟩ : syracuseStep 7992701 = 2997263) B2997263
theorem B9467279 : Blo 1869636 9467279 := bstep (se 1 (by rfl) ⟨7100459, by rfl⟩ : syracuseStep 9467279 = 14200919) B14200919
theorem B7099913 : Blo 1869636 7099913 := bstep (se 2 (by rfl) ⟨2662467, by rfl⟩ : syracuseStep 7099913 = 5324935) B5324935
theorem B2807375 : Blo 1869636 2807375 := bstep (se 1 (by rfl) ⟨2105531, by rfl⟩ : syracuseStep 2807375 = 4211063) B4211063
theorem B5691019 : Blo 1869636 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B4265671 : Blo 1869636 4265671 := bstep (se 1 (by rfl) ⟨3199253, by rfl⟩ : syracuseStep 4265671 = 6398507) B6398507
theorem B4208327 : Blo 1869636 4208327 := bstep (se 1 (by rfl) ⟨3156245, by rfl⟩ : syracuseStep 4208327 = 6312491) B6312491
theorem B4732627 : Blo 1869636 4732627 := bstep (se 1 (by rfl) ⟨3549470, by rfl⟩ : syracuseStep 4732627 = 7098941) B7098941
theorem B3552979 : Blo 1869636 3552979 := bstep (se 1 (by rfl) ⟨2664734, by rfl⟩ : syracuseStep 3552979 = 5329469) B5329469
theorem B35944235 : Blo 1869636 35944235 := bstep (se 1 (by rfl) ⟨26958176, by rfl⟩ : syracuseStep 35944235 = 53916353) B53916353
theorem B5994283 : Blo 1869636 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B21297005 : Blo 1869636 21297005 := bstep (se 3 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 21297005 = 7986377) B7986377
theorem B6076417 : Blo 1869636 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B6314003 : Blo 1869636 6314003 := bstep (se 1 (by rfl) ⟨4735502, by rfl⟩ : syracuseStep 6314003 = 9471005) B9471005
theorem B4495607 : Blo 1869636 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B7199063 : Blo 1869636 7199063 := bstep (se 1 (by rfl) ⟨5399297, by rfl⟩ : syracuseStep 7199063 = 10798595) B10798595
theorem B6314327 : Blo 1869636 6314327 := bstep (se 1 (by rfl) ⟨4735745, by rfl⟩ : syracuseStep 6314327 = 9471491) B9471491
theorem B47921543 : Blo 1869636 47921543 := bstep (se 1 (by rfl) ⟨35941157, by rfl⟩ : syracuseStep 47921543 = 71882315) B71882315
theorem B21305753 : Blo 1869636 21305753 := bstep (se 2 (by rfl) ⟨7989657, by rfl⟩ : syracuseStep 21305753 = 15979315) B15979315
theorem B2103727 : Blo 1869636 2103727 := bstep (se 1 (by rfl) ⟨1577795, by rfl⟩ : syracuseStep 2103727 = 3155591) B3155591
theorem B4209191 : Blo 1869636 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B4733579 : Blo 1869636 4733579 := bstep (se 1 (by rfl) ⟨3550184, by rfl⟩ : syracuseStep 4733579 = 7100369) B7100369
theorem B7101067 : Blo 1869636 7101067 := bstep (se 1 (by rfl) ⟨5325800, by rfl⟩ : syracuseStep 7101067 = 10651601) B10651601
theorem B6740729 : Blo 1869636 6740729 := bstep (se 2 (by rfl) ⟨2527773, by rfl⟩ : syracuseStep 6740729 = 5055547) B5055547
theorem B6396745 : Blo 1869636 6396745 := bstep (se 2 (by rfl) ⟨2398779, by rfl⟩ : syracuseStep 6396745 = 4797559) B4797559
theorem B2104159 : Blo 1869636 2104159 := bstep (se 1 (by rfl) ⟨1578119, by rfl⟩ : syracuseStep 2104159 = 3156239) B3156239
theorem B4209515 : Blo 1869636 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B62356337 : Blo 1869636 62356337 := bstep (se 2 (by rfl) ⟨23383626, by rfl⟩ : syracuseStep 62356337 = 46767253) B46767253
theorem B4266913 : Blo 1869636 4266913 := bstep (se 2 (by rfl) ⟨1600092, by rfl⟩ : syracuseStep 4266913 = 3200185) B3200185
theorem B4209569 : Blo 1869636 4209569 := bstep (se 2 (by rfl) ⟨1578588, by rfl⟩ : syracuseStep 4209569 = 3157177) B3157177
theorem B7101371 : Blo 1869636 7101371 := bstep (se 1 (by rfl) ⟨5326028, by rfl⟩ : syracuseStep 7101371 = 10652057) B10652057
theorem B14212097 : Blo 1869636 14212097 := bstep (se 2 (by rfl) ⟨5329536, by rfl⟩ : syracuseStep 14212097 = 10659073) B10659073
theorem B2366587 : Blo 1869636 2366587 := bstep (se 1 (by rfl) ⟨1774940, by rfl⟩ : syracuseStep 2366587 = 3549881) B3549881
theorem B2104519 : Blo 1869636 2104519 := bstep (se 1 (by rfl) ⟨1578389, by rfl⟩ : syracuseStep 2104519 = 3156779) B3156779
theorem B4209911 : Blo 1869636 4209911 := bstep (se 1 (by rfl) ⟨3157433, by rfl⟩ : syracuseStep 4209911 = 6314867) B6314867
theorem B2366815 : Blo 1869636 2366815 := bstep (se 1 (by rfl) ⟨1775111, by rfl⟩ : syracuseStep 2366815 = 3550223) B3550223
theorem B6741377 : Blo 1869636 6741377 := bstep (se 2 (by rfl) ⟨2528016, by rfl⟩ : syracuseStep 6741377 = 5056033) B5056033
theorem B6315407 : Blo 1869636 6315407 := bstep (se 1 (by rfl) ⟨4736555, by rfl⟩ : syracuseStep 6315407 = 9473111) B9473111
theorem B51183029 : Blo 1869636 51183029 := bstep (se 5 (by rfl) ⟨2399204, by rfl⟩ : syracuseStep 51183029 = 4798409) B4798409
theorem B9469385 : Blo 1869636 9469385 := bstep (se 2 (by rfl) ⟨3551019, by rfl⟩ : syracuseStep 9469385 = 7102039) B7102039
theorem B8986099 : Blo 1869636 8986099 := bstep (se 1 (by rfl) ⟨6739574, by rfl⟩ : syracuseStep 8986099 = 13479149) B13479149
theorem B20512379 : Blo 1869636 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B7585427 : Blo 1869636 7585427 := bstep (se 1 (by rfl) ⟨5689070, by rfl⟩ : syracuseStep 7585427 = 11378141) B11378141
theorem B10116755 : Blo 1869636 10116755 := bstep (se 1 (by rfl) ⟨7587566, by rfl⟩ : syracuseStep 10116755 = 15175133) B15175133
theorem B2883271 : Blo 1869636 2883271 := bstep (se 1 (by rfl) ⟨2162453, by rfl⟩ : syracuseStep 2883271 = 4324907) B4324907
theorem B6315731 : Blo 1869636 6315731 := bstep (se 1 (by rfl) ⟨4736798, by rfl⟩ : syracuseStep 6315731 = 9473597) B9473597
theorem B4734713 : Blo 1869636 4734713 := bstep (se 2 (by rfl) ⟨1775517, by rfl⟩ : syracuseStep 4734713 = 3551035) B3551035
theorem B4210505 : Blo 1869636 4210505 := bstep (se 2 (by rfl) ⟨1578939, by rfl⟩ : syracuseStep 4210505 = 3157879) B3157879
theorem B3792745 : Blo 1869636 3792745 := bstep (se 2 (by rfl) ⟨1422279, by rfl⟩ : syracuseStep 3792745 = 2844559) B2844559
theorem B14204807 : Blo 1869636 14204807 := bstep (se 1 (by rfl) ⟨10653605, by rfl⟩ : syracuseStep 14204807 = 21307211) B21307211
theorem B2367407 : Blo 1869636 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B4734895 : Blo 1869636 4734895 := bstep (se 1 (by rfl) ⟨3551171, by rfl⟩ : syracuseStep 4734895 = 7102343) B7102343
theorem B2564015 : Blo 1869636 2564015 := bstep (se 1 (by rfl) ⟨1923011, by rfl⟩ : syracuseStep 2564015 = 3846023) B3846023
theorem B8101889 : Blo 1869636 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B4210793 : Blo 1869636 4210793 := bstep (se 2 (by rfl) ⟨1579047, by rfl⟩ : syracuseStep 4210793 = 3158095) B3158095
theorem B17981651 : Blo 1869636 17981651 := bstep (se 1 (by rfl) ⟨13486238, by rfl⟩ : syracuseStep 17981651 = 26972477) B26972477
theorem B2105563 : Blo 1869636 2105563 := bstep (se 1 (by rfl) ⟨1579172, by rfl⟩ : syracuseStep 2105563 = 3158345) B3158345
theorem B6316379 : Blo 1869636 6316379 := bstep (se 1 (by rfl) ⟨4737284, by rfl⟩ : syracuseStep 6316379 = 9474569) B9474569
theorem B20235203 : Blo 1869636 20235203 := bstep (se 1 (by rfl) ⟨15176402, by rfl⟩ : syracuseStep 20235203 = 30352805) B30352805
theorem B10650599 : Blo 1869636 10650599 := bstep (se 1 (by rfl) ⟨7987949, by rfl⟩ : syracuseStep 10650599 = 15975899) B15975899
theorem B68273219 : Blo 1869636 68273219 := bstep (se 1 (by rfl) ⟨51204914, by rfl⟩ : syracuseStep 68273219 = 102409829) B102409829
theorem B8528993 : Blo 1869636 8528993 := bstep (se 2 (by rfl) ⟨3198372, by rfl⟩ : syracuseStep 8528993 = 6396745) B6396745
theorem B23962823 : Blo 1869636 23962823 := bstep (se 1 (by rfl) ⟨17972117, by rfl⟩ : syracuseStep 23962823 = 35944235) B35944235
theorem B14198003 : Blo 1869636 14198003 := bstep (se 1 (by rfl) ⟨10648502, by rfl⟩ : syracuseStep 14198003 = 21297005) B21297005
theorem B4736353 : Blo 1869636 4736353 := bstep (se 2 (by rfl) ⟨1776132, by rfl⟩ : syracuseStep 4736353 = 3552265) B3552265
theorem B30344557 : Blo 1869636 30344557 := bstep (se 3 (by rfl) ⟨5689604, by rfl⟩ : syracuseStep 30344557 = 11379209) B11379209
theorem B18220439 : Blo 1869636 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B3155449 : Blo 1869636 3155449 := bstep (se 2 (by rfl) ⟨1183293, by rfl⟩ : syracuseStep 3155449 = 2366587) B2366587
theorem B5326393 : Blo 1869636 5326393 := bstep (se 2 (by rfl) ⟨1997397, by rfl⟩ : syracuseStep 5326393 = 3994795) B3994795
theorem B20227805 : Blo 1869636 20227805 := bstep (se 3 (by rfl) ⟨3792713, by rfl⟩ : syracuseStep 20227805 = 7585427) B7585427
theorem B3155719 : Blo 1869636 3155719 := bstep (se 1 (by rfl) ⟨2366789, by rfl⟩ : syracuseStep 3155719 = 4733579) B4733579
theorem B3155753 : Blo 1869636 3155753 := bstep (se 2 (by rfl) ⟨1183407, by rfl⟩ : syracuseStep 3155753 = 2366815) B2366815
theorem B20227973 : Blo 1869636 20227973 := bstep (se 4 (by rfl) ⟨1896372, by rfl⟩ : syracuseStep 20227973 = 3792745) B3792745
theorem B1869723 : Blo 1869636 1869723 := bstep (se 1 (by rfl) ⟨1402292, by rfl⟩ : syracuseStep 1869723 = 2804585) B2804585
theorem B1869775 : Blo 1869636 1869775 := bstep (se 1 (by rfl) ⟨1402331, by rfl⟩ : syracuseStep 1869775 = 2804663) B2804663
theorem B1869799 : Blo 1869636 1869799 := bstep (se 1 (by rfl) ⟨1402349, by rfl⟩ : syracuseStep 1869799 = 2804699) B2804699
theorem B11987129 : Blo 1869636 11987129 := bstep (se 2 (by rfl) ⟨4495173, by rfl⟩ : syracuseStep 11987129 = 8990347) B8990347
theorem B7588025 : Blo 1869636 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B5687561 : Blo 1869636 5687561 := bstep (se 2 (by rfl) ⟨2132835, by rfl⟩ : syracuseStep 5687561 = 4265671) B4265671
theorem B3844361 : Blo 1869636 3844361 := bstep (se 2 (by rfl) ⟨1441635, by rfl⟩ : syracuseStep 3844361 = 2883271) B2883271
theorem B6310169 : Blo 1869636 6310169 := bstep (se 2 (by rfl) ⟨2366313, by rfl⟩ : syracuseStep 6310169 = 4732627) B4732627
theorem B4737305 : Blo 1869636 4737305 := bstep (se 2 (by rfl) ⟨1776489, by rfl⟩ : syracuseStep 4737305 = 3552979) B3552979
theorem B1870111 : Blo 1869636 1870111 := bstep (se 1 (by rfl) ⟨1402583, by rfl⟩ : syracuseStep 1870111 = 2805167) B2805167
theorem B34122019 : Blo 1869636 34122019 := bstep (se 1 (by rfl) ⟨25591514, by rfl⟩ : syracuseStep 34122019 = 51183029) B51183029
theorem B1870171 : Blo 1869636 1870171 := bstep (se 1 (by rfl) ⟨1402628, by rfl⟩ : syracuseStep 1870171 = 2805257) B2805257
theorem B1870191 : Blo 1869636 1870191 := bstep (se 1 (by rfl) ⟨1402643, by rfl⟩ : syracuseStep 1870191 = 2805287) B2805287
theorem B15985025 : Blo 1869636 15985025 := bstep (se 2 (by rfl) ⟨5994384, by rfl⟩ : syracuseStep 15985025 = 11988769) B11988769
theorem B1870247 : Blo 1869636 1870247 := bstep (se 1 (by rfl) ⟨1402685, by rfl⟩ : syracuseStep 1870247 = 2805371) B2805371
theorem B13674919 : Blo 1869636 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B6744503 : Blo 1869636 6744503 := bstep (se 1 (by rfl) ⟨5058377, by rfl⟩ : syracuseStep 6744503 = 10116755) B10116755
theorem B14395877 : Blo 1869636 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B1870331 : Blo 1869636 1870331 := bstep (se 1 (by rfl) ⟨1402748, by rfl⟩ : syracuseStep 1870331 = 2805497) B2805497
theorem B3156475 : Blo 1869636 3156475 := bstep (se 1 (by rfl) ⟨2367356, by rfl⟩ : syracuseStep 3156475 = 4734713) B4734713
theorem B1870399 : Blo 1869636 1870399 := bstep (se 1 (by rfl) ⟨1402799, by rfl⟩ : syracuseStep 1870399 = 2805599) B2805599
theorem B1870407 : Blo 1869636 1870407 := bstep (se 1 (by rfl) ⟨1402805, by rfl⟩ : syracuseStep 1870407 = 2805611) B2805611
theorem B65702477 : Blo 1869636 65702477 := bstep (se 3 (by rfl) ⟨12319214, by rfl⟩ : syracuseStep 65702477 = 24638429) B24638429
theorem B83143361 : Blo 1869636 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B3549919 : Blo 1869636 3549919 := bstep (se 1 (by rfl) ⟨2662439, by rfl⟩ : syracuseStep 3549919 = 5324879) B5324879
theorem B1870559 : Blo 1869636 1870559 := bstep (se 1 (by rfl) ⟨1402919, by rfl⟩ : syracuseStep 1870559 = 2805839) B2805839
theorem B9472787 : Blo 1869636 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B1870639 : Blo 1869636 1870639 := bstep (se 1 (by rfl) ⟨1402979, by rfl⟩ : syracuseStep 1870639 = 2805959) B2805959
theorem B1870747 : Blo 1869636 1870747 := bstep (se 1 (by rfl) ⟨1403060, by rfl⟩ : syracuseStep 1870747 = 2806121) B2806121
theorem B3156907 : Blo 1869636 3156907 := bstep (se 1 (by rfl) ⟨2367680, by rfl⟩ : syracuseStep 3156907 = 4735361) B4735361
theorem B1870799 : Blo 1869636 1870799 := bstep (se 1 (by rfl) ⟨1403099, by rfl⟩ : syracuseStep 1870799 = 2806199) B2806199
theorem B2804711 : Blo 1869636 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B1870823 : Blo 1869636 1870823 := bstep (se 1 (by rfl) ⟨1403117, by rfl⟩ : syracuseStep 1870823 = 2806235) B2806235
theorem B14199947 : Blo 1869636 14199947 := bstep (se 1 (by rfl) ⟨10649960, by rfl⟩ : syracuseStep 14199947 = 21299921) B21299921
theorem B5328011 : Blo 1869636 5328011 := bstep (se 1 (by rfl) ⟨3996008, by rfl⟩ : syracuseStep 5328011 = 7992017) B7992017
theorem B15977675 : Blo 1869636 15977675 := bstep (se 1 (by rfl) ⟨11983256, by rfl⟩ : syracuseStep 15977675 = 23966513) B23966513
theorem B2133211 : Blo 1869636 2133211 := bstep (se 1 (by rfl) ⟨1599908, by rfl⟩ : syracuseStep 2133211 = 3199817) B3199817
theorem B3157211 : Blo 1869636 3157211 := bstep (se 1 (by rfl) ⟨2367908, by rfl⟩ : syracuseStep 3157211 = 4735817) B4735817
theorem B2804969 : Blo 1869636 2804969 := bstep (se 2 (by rfl) ⟨1051863, by rfl⟩ : syracuseStep 2804969 = 2103727) B2103727
theorem B2805023 : Blo 1869636 2805023 := bstep (se 1 (by rfl) ⟨2103767, by rfl⟩ : syracuseStep 2805023 = 4207535) B4207535
theorem B1871135 : Blo 1869636 1871135 := bstep (se 1 (by rfl) ⟨1403351, by rfl⟩ : syracuseStep 1871135 = 2806703) B2806703
theorem B1871195 : Blo 1869636 1871195 := bstep (se 1 (by rfl) ⟨1403396, by rfl⟩ : syracuseStep 1871195 = 2806793) B2806793
theorem B1871215 : Blo 1869636 1871215 := bstep (se 1 (by rfl) ⟨1403411, by rfl⟩ : syracuseStep 1871215 = 2806823) B2806823
theorem B1871271 : Blo 1869636 1871271 := bstep (se 1 (by rfl) ⟨1403453, by rfl⟩ : syracuseStep 1871271 = 2806907) B2806907
theorem B2805191 : Blo 1869636 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B3157447 : Blo 1869636 3157447 := bstep (se 1 (by rfl) ⟨2368085, by rfl⟩ : syracuseStep 3157447 = 4736171) B4736171
theorem B1871355 : Blo 1869636 1871355 := bstep (se 1 (by rfl) ⟨1403516, by rfl⟩ : syracuseStep 1871355 = 2807033) B2807033
theorem B1871423 : Blo 1869636 1871423 := bstep (se 1 (by rfl) ⟨1403567, by rfl⟩ : syracuseStep 1871423 = 2807135) B2807135
theorem B1871431 : Blo 1869636 1871431 := bstep (se 1 (by rfl) ⟨1403573, by rfl⟩ : syracuseStep 1871431 = 2807147) B2807147
theorem B5328467 : Blo 1869636 5328467 := bstep (se 1 (by rfl) ⟨3996350, by rfl⟩ : syracuseStep 5328467 = 7992701) B7992701
theorem B6311519 : Blo 1869636 6311519 := bstep (se 1 (by rfl) ⟨4733639, by rfl⟩ : syracuseStep 6311519 = 9467279) B9467279
theorem B15380077 : Blo 1869636 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B3993275 : Blo 1869636 3993275 := bstep (se 1 (by rfl) ⟨2994956, by rfl⟩ : syracuseStep 3993275 = 5989913) B5989913
theorem B1871583 : Blo 1869636 1871583 := bstep (se 1 (by rfl) ⟨1403687, by rfl⟩ : syracuseStep 1871583 = 2807375) B2807375
theorem B2805545 : Blo 1869636 2805545 := bstep (se 2 (by rfl) ⟨1052079, by rfl⟩ : syracuseStep 2805545 = 2104159) B2104159
theorem B2805551 : Blo 1869636 2805551 := bstep (se 1 (by rfl) ⟨2104163, by rfl⟩ : syracuseStep 2805551 = 4208327) B4208327
theorem B5689217 : Blo 1869636 5689217 := bstep (se 2 (by rfl) ⟨2133456, by rfl⟩ : syracuseStep 5689217 = 4266913) B4266913
theorem B9473921 : Blo 1869636 9473921 := bstep (se 2 (by rfl) ⟨3552720, by rfl⟩ : syracuseStep 9473921 = 7105441) B7105441
theorem B51195833 : Blo 1869636 51195833 := bstep (se 2 (by rfl) ⟨19198437, by rfl⟩ : syracuseStep 51195833 = 38396875) B38396875
theorem B3157967 : Blo 1869636 3157967 := bstep (se 1 (by rfl) ⟨2368475, by rfl⟩ : syracuseStep 3157967 = 4736951) B4736951
theorem B2806025 : Blo 1869636 2806025 := bstep (se 2 (by rfl) ⟨1052259, by rfl⟩ : syracuseStep 2806025 = 2104519) B2104519
theorem B4206959 : Blo 1869636 4206959 := bstep (se 1 (by rfl) ⟨3155219, by rfl⟩ : syracuseStep 4206959 = 6310439) B6310439
theorem B2806127 : Blo 1869636 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B17977733 : Blo 1869636 17977733 := bstep (se 4 (by rfl) ⟨1685412, by rfl⟩ : syracuseStep 17977733 = 3370825) B3370825
theorem B4207031 : Blo 1869636 4207031 := bstep (se 1 (by rfl) ⟨3155273, by rfl⟩ : syracuseStep 4207031 = 6310547) B6310547
theorem B5059027 : Blo 1869636 5059027 := bstep (se 1 (by rfl) ⟨3794270, by rfl⟩ : syracuseStep 5059027 = 7588541) B7588541
theorem B7991777 : Blo 1869636 7991777 := bstep (se 2 (by rfl) ⟨2996916, by rfl⟩ : syracuseStep 7991777 = 5993833) B5993833
theorem B4493819 : Blo 1869636 4493819 := bstep (se 1 (by rfl) ⟨3370364, by rfl⟩ : syracuseStep 4493819 = 6740729) B6740729
theorem B14201405 : Blo 1869636 14201405 := bstep (se 3 (by rfl) ⟨2662763, by rfl⟩ : syracuseStep 14201405 = 5325527) B5325527
theorem B4207175 : Blo 1869636 4207175 := bstep (se 1 (by rfl) ⟨3155381, by rfl⟩ : syracuseStep 4207175 = 6310763) B6310763
theorem B2806343 : Blo 1869636 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B41570891 : Blo 1869636 41570891 := bstep (se 1 (by rfl) ⟨31178168, by rfl⟩ : syracuseStep 41570891 = 62356337) B62356337
theorem B4207211 : Blo 1869636 4207211 := bstep (se 1 (by rfl) ⟨3155408, by rfl⟩ : syracuseStep 4207211 = 6310817) B6310817
theorem B2806379 : Blo 1869636 2806379 := bstep (se 1 (by rfl) ⟨2104784, by rfl⟩ : syracuseStep 2806379 = 4209569) B4209569
theorem B11981465 : Blo 1869636 11981465 := bstep (se 2 (by rfl) ⟨4493049, by rfl⟩ : syracuseStep 11981465 = 8986099) B8986099
theorem B9474731 : Blo 1869636 9474731 := bstep (se 1 (by rfl) ⟨7106048, by rfl⟩ : syracuseStep 9474731 = 14212097) B14212097
theorem B21893917 : Blo 1869636 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B2806607 : Blo 1869636 2806607 := bstep (se 1 (by rfl) ⟨2104955, by rfl⟩ : syracuseStep 2806607 = 4209911) B4209911
theorem B4494251 : Blo 1869636 4494251 := bstep (se 1 (by rfl) ⟨3370688, by rfl⟩ : syracuseStep 4494251 = 6741377) B6741377
theorem B6312923 : Blo 1869636 6312923 := bstep (se 1 (by rfl) ⟨4734692, by rfl⟩ : syracuseStep 6312923 = 9469385) B9469385
theorem B4207607 : Blo 1869636 4207607 := bstep (se 1 (by rfl) ⟨3155705, by rfl⟩ : syracuseStep 4207607 = 6311411) B6311411
theorem B7992377 : Blo 1869636 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B874386521 : Blo 1869636 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B6313085 : Blo 1869636 6313085 := bstep (se 3 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 6313085 = 2367407) B2367407
theorem B6837373 : Blo 1869636 6837373 := bstep (se 3 (by rfl) ⟨1282007, by rfl⟩ : syracuseStep 6837373 = 2564015) B2564015
theorem B2667739 : Blo 1869636 2667739 := bstep (se 1 (by rfl) ⟨2000804, by rfl⟩ : syracuseStep 2667739 = 4001609) B4001609
theorem B2807003 : Blo 1869636 2807003 := bstep (se 1 (by rfl) ⟨2105252, by rfl⟩ : syracuseStep 2807003 = 4210505) B4210505
theorem B6313193 : Blo 1869636 6313193 := bstep (se 2 (by rfl) ⟨2367447, by rfl⟩ : syracuseStep 6313193 = 4734895) B4734895
theorem B4207967 : Blo 1869636 4207967 := bstep (se 1 (by rfl) ⟨3155975, by rfl⟩ : syracuseStep 4207967 = 6311951) B6311951
theorem B15988063 : Blo 1869636 15988063 := bstep (se 1 (by rfl) ⟨11991047, by rfl⟩ : syracuseStep 15988063 = 23982095) B23982095
theorem B2807177 : Blo 1869636 2807177 := bstep (se 2 (by rfl) ⟨1052691, by rfl⟩ : syracuseStep 2807177 = 2105383) B2105383
theorem B6313355 : Blo 1869636 6313355 := bstep (se 1 (by rfl) ⟨4735016, by rfl⟩ : syracuseStep 6313355 = 9470033) B9470033
theorem B19191335 : Blo 1869636 19191335 := bstep (se 1 (by rfl) ⟨14393501, by rfl⟩ : syracuseStep 19191335 = 28787003) B28787003
theorem B4732577 : Blo 1869636 4732577 := bstep (se 2 (by rfl) ⟨1774716, by rfl⟩ : syracuseStep 4732577 = 3549433) B3549433
theorem B4208363 : Blo 1869636 4208363 := bstep (se 1 (by rfl) ⟨3156272, by rfl⟩ : syracuseStep 4208363 = 6312545) B6312545
theorem B17979191 : Blo 1869636 17979191 := bstep (se 1 (by rfl) ⟨13484393, by rfl⟩ : syracuseStep 17979191 = 26968787) B26968787
theorem B8099671 : Blo 1869636 8099671 := bstep (se 1 (by rfl) ⟨6074753, by rfl⟩ : syracuseStep 8099671 = 12149507) B12149507
theorem B4208489 : Blo 1869636 4208489 := bstep (se 2 (by rfl) ⟨1578183, by rfl⟩ : syracuseStep 4208489 = 3156367) B3156367
theorem B8992903 : Blo 1869636 8992903 := bstep (se 1 (by rfl) ⟨6744677, by rfl⟩ : syracuseStep 8992903 = 13489355) B13489355
theorem B9468089 : Blo 1869636 9468089 := bstep (se 2 (by rfl) ⟨3550533, by rfl⟩ : syracuseStep 9468089 = 7101067) B7101067
theorem B2103583 : Blo 1869636 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B13490509 : Blo 1869636 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B4733275 : Blo 1869636 4733275 := bstep (se 1 (by rfl) ⟨3549956, by rfl⟩ : syracuseStep 4733275 = 7099913) B7099913
theorem B7100855 : Blo 1869636 7100855 := bstep (se 1 (by rfl) ⟨5325641, by rfl⟩ : syracuseStep 7100855 = 10651283) B10651283
theorem B2103871 : Blo 1869636 2103871 := bstep (se 1 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 2103871 = 3155807) B3155807
theorem B10656431 : Blo 1869636 10656431 := bstep (se 1 (by rfl) ⟨7992323, by rfl⟩ : syracuseStep 10656431 = 15984647) B15984647
theorem B4209335 : Blo 1869636 4209335 := bstep (se 1 (by rfl) ⟨3157001, by rfl⟩ : syracuseStep 4209335 = 6314003) B6314003
theorem B2366263 : Blo 1869636 2366263 := bstep (se 1 (by rfl) ⟨1774697, by rfl⟩ : syracuseStep 2366263 = 3549395) B3549395
theorem B2997071 : Blo 1869636 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B4799375 : Blo 1869636 4799375 := bstep (se 1 (by rfl) ⟨3599531, by rfl⟩ : syracuseStep 4799375 = 7199063) B7199063
theorem B4209551 : Blo 1869636 4209551 := bstep (se 1 (by rfl) ⟨3157163, by rfl⟩ : syracuseStep 4209551 = 6314327) B6314327
theorem B31947695 : Blo 1869636 31947695 := bstep (se 1 (by rfl) ⟨23960771, by rfl⟩ : syracuseStep 31947695 = 47921543) B47921543
theorem B14203835 : Blo 1869636 14203835 := bstep (se 1 (by rfl) ⟨10652876, by rfl⟩ : syracuseStep 14203835 = 21305753) B21305753
theorem B2997481 : Blo 1869636 2997481 := bstep (se 2 (by rfl) ⟨1124055, by rfl⟩ : syracuseStep 2997481 = 2248111) B2248111
theorem B2366759 : Blo 1869636 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B4734247 : Blo 1869636 4734247 := bstep (se 1 (by rfl) ⟨3550685, by rfl⟩ : syracuseStep 4734247 = 7101371) B7101371
theorem B2104699 : Blo 1869636 2104699 := bstep (se 1 (by rfl) ⟨1578524, by rfl⟩ : syracuseStep 2104699 = 3157049) B3157049
theorem B8535577 : Blo 1869636 8535577 := bstep (se 2 (by rfl) ⟨3200841, by rfl⟩ : syracuseStep 8535577 = 6401683) B6401683
theorem B4734521 : Blo 1869636 4734521 := bstep (se 2 (by rfl) ⟨1775445, by rfl⟩ : syracuseStep 4734521 = 3550891) B3550891
theorem B4210271 : Blo 1869636 4210271 := bstep (se 1 (by rfl) ⟨3157703, by rfl⟩ : syracuseStep 4210271 = 6315407) B6315407
theorem B2367083 : Blo 1869636 2367083 := bstep (se 1 (by rfl) ⟨1775312, by rfl⟩ : syracuseStep 2367083 = 3550625) B3550625
theorem B2399851 : Blo 1869636 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B25607825 : Blo 1869636 25607825 := bstep (se 2 (by rfl) ⟨9602934, by rfl⟩ : syracuseStep 25607825 = 19205869) B19205869
theorem B4210487 : Blo 1869636 4210487 := bstep (se 1 (by rfl) ⟨3157865, by rfl⟩ : syracuseStep 4210487 = 6315731) B6315731
theorem B2105167 : Blo 1869636 2105167 := bstep (se 1 (by rfl) ⟨1578875, by rfl⟩ : syracuseStep 2105167 = 3157751) B3157751
theorem B9469871 : Blo 1869636 9469871 := bstep (se 1 (by rfl) ⟨7102403, by rfl⟩ : syracuseStep 9469871 = 14204807) B14204807
theorem B35938241 : Blo 1869636 35938241 := bstep (se 2 (by rfl) ⟨13476840, by rfl⟩ : syracuseStep 35938241 = 26953681) B26953681
theorem B2367463 : Blo 1869636 2367463 := bstep (se 1 (by rfl) ⟨1775597, by rfl⟩ : syracuseStep 2367463 = 3551195) B3551195
theorem B4210919 : Blo 1869636 4210919 := bstep (se 1 (by rfl) ⟨3158189, by rfl⟩ : syracuseStep 4210919 = 6316379) B6316379
theorem B11985155 : Blo 1869636 11985155 := bstep (se 1 (by rfl) ⟨8988866, by rfl⟩ : syracuseStep 11985155 = 17977733) B17977733
theorem B27713927 : Blo 1869636 27713927 := bstep (se 1 (by rfl) ⟨20785445, by rfl⟩ : syracuseStep 27713927 = 41570891) B41570891
theorem B7987643 : Blo 1869636 7987643 := bstep (se 1 (by rfl) ⟨5990732, by rfl⟩ : syracuseStep 7987643 = 11981465) B11981465
theorem B6316487 : Blo 1869636 6316487 := bstep (se 1 (by rfl) ⟨4737365, by rfl⟩ : syracuseStep 6316487 = 9474731) B9474731
theorem B45515479 : Blo 1869636 45515479 := bstep (se 1 (by rfl) ⟨34136609, by rfl⟩ : syracuseStep 45515479 = 68273219) B68273219
theorem B5685995 : Blo 1869636 5685995 := bstep (se 1 (by rfl) ⟨4264496, by rfl⟩ : syracuseStep 5685995 = 8528993) B8528993
theorem B15975215 : Blo 1869636 15975215 := bstep (se 1 (by rfl) ⟨11981411, by rfl⟩ : syracuseStep 15975215 = 23962823) B23962823
theorem B3155017 : Blo 1869636 3155017 := bstep (se 2 (by rfl) ⟨1183131, by rfl⟩ : syracuseStep 3155017 = 2366263) B2366263
theorem B3155051 : Blo 1869636 3155051 := bstep (se 1 (by rfl) ⟨2366288, by rfl⟩ : syracuseStep 3155051 = 4732577) B4732577
theorem B13485203 : Blo 1869636 13485203 := bstep (se 1 (by rfl) ⟨10113902, by rfl⟩ : syracuseStep 13485203 = 20227805) B20227805
theorem B11986127 : Blo 1869636 11986127 := bstep (se 1 (by rfl) ⟨8989595, by rfl⟩ : syracuseStep 11986127 = 17979191) B17979191
theorem B51176893 : Blo 1869636 51176893 := bstep (se 3 (by rfl) ⟨9595667, by rfl⟩ : syracuseStep 51176893 = 19191335) B19191335
theorem B3556985 : Blo 1869636 3556985 := bstep (se 2 (by rfl) ⟨1333869, by rfl⟩ : syracuseStep 3556985 = 2667739) B2667739
theorem B2844281 : Blo 1869636 2844281 := bstep (se 2 (by rfl) ⟨1066605, by rfl⟩ : syracuseStep 2844281 = 2133211) B2133211
theorem B7104287 : Blo 1869636 7104287 := bstep (se 1 (by rfl) ⟨5328215, by rfl⟩ : syracuseStep 7104287 = 10656431) B10656431
theorem B21317417 : Blo 1869636 21317417 := bstep (se 2 (by rfl) ⟨7994031, by rfl⟩ : syracuseStep 21317417 = 15988063) B15988063
theorem B55428907 : Blo 1869636 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B1869807 : Blo 1869636 1869807 := bstep (se 1 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 1869807 = 2804711) B2804711
theorem B11380769 : Blo 1869636 11380769 := bstep (se 2 (by rfl) ⟨4267788, by rfl⟩ : syracuseStep 11380769 = 8535577) B8535577
theorem B10651783 : Blo 1869636 10651783 := bstep (se 1 (by rfl) ⟨7988837, by rfl⟩ : syracuseStep 10651783 = 15977675) B15977675
theorem B20506769 : Blo 1869636 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B1869979 : Blo 1869636 1869979 := bstep (se 1 (by rfl) ⟨1402484, by rfl⟩ : syracuseStep 1869979 = 2804969) B2804969
theorem B1870015 : Blo 1869636 1870015 := bstep (se 1 (by rfl) ⟨1402511, by rfl⟩ : syracuseStep 1870015 = 2805023) B2805023
theorem B1870127 : Blo 1869636 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B3156347 : Blo 1869636 3156347 := bstep (se 1 (by rfl) ⟨2367260, by rfl⟩ : syracuseStep 3156347 = 4734521) B4734521
theorem B10799561 : Blo 1869636 10799561 := bstep (se 2 (by rfl) ⟨4049835, by rfl⟩ : syracuseStep 10799561 = 8099671) B8099671
theorem B1870363 : Blo 1869636 1870363 := bstep (se 1 (by rfl) ⟨1402772, by rfl⟩ : syracuseStep 1870363 = 2805545) B2805545
theorem B1870367 : Blo 1869636 1870367 := bstep (se 1 (by rfl) ⟨1402775, by rfl⟩ : syracuseStep 1870367 = 2805551) B2805551
theorem B34130555 : Blo 1869636 34130555 := bstep (se 1 (by rfl) ⟨25597916, by rfl⟩ : syracuseStep 34130555 = 51195833) B51195833
theorem B3156617 : Blo 1869636 3156617 := bstep (se 2 (by rfl) ⟨1183731, by rfl⟩ : syracuseStep 3156617 = 2367463) B2367463
theorem B5401259 : Blo 1869636 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B11987767 : Blo 1869636 11987767 := bstep (se 1 (by rfl) ⟨8990825, by rfl⟩ : syracuseStep 11987767 = 17981651) B17981651
theorem B1870683 : Blo 1869636 1870683 := bstep (se 1 (by rfl) ⟨1403012, by rfl⟩ : syracuseStep 1870683 = 2806025) B2806025
theorem B2804639 : Blo 1869636 2804639 := bstep (se 1 (by rfl) ⟨2103479, by rfl⟩ : syracuseStep 2804639 = 4206959) B4206959
theorem B1870751 : Blo 1869636 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B2804687 : Blo 1869636 2804687 := bstep (se 1 (by rfl) ⟨2103515, by rfl⟩ : syracuseStep 2804687 = 4207031) B4207031
theorem B5327851 : Blo 1869636 5327851 := bstep (se 1 (by rfl) ⟨3995888, by rfl⟩ : syracuseStep 5327851 = 7991777) B7991777
theorem B2804777 : Blo 1869636 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B2804783 : Blo 1869636 2804783 := bstep (se 1 (by rfl) ⟨2103587, by rfl⟩ : syracuseStep 2804783 = 4207175) B4207175
theorem B1870895 : Blo 1869636 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B2804807 : Blo 1869636 2804807 := bstep (se 1 (by rfl) ⟨2103605, by rfl⟩ : syracuseStep 2804807 = 4207211) B4207211
theorem B1870919 : Blo 1869636 1870919 := bstep (se 1 (by rfl) ⟨1403189, by rfl⟩ : syracuseStep 1870919 = 2806379) B2806379
theorem B6311033 : Blo 1869636 6311033 := bstep (se 2 (by rfl) ⟨2366637, by rfl⟩ : syracuseStep 6311033 = 4733275) B4733275
theorem B1871071 : Blo 1869636 1871071 := bstep (se 1 (by rfl) ⟨1403303, by rfl⟩ : syracuseStep 1871071 = 2806607) B2806607
theorem B12799205 : Blo 1869636 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B6745369 : Blo 1869636 6745369 := bstep (se 2 (by rfl) ⟨2529513, by rfl⟩ : syracuseStep 6745369 = 5059027) B5059027
theorem B2805071 : Blo 1869636 2805071 := bstep (se 1 (by rfl) ⟨2103803, by rfl⟩ : syracuseStep 2805071 = 4207607) B4207607
theorem B10251629 : Blo 1869636 10251629 := bstep (se 3 (by rfl) ⟨1922180, by rfl⟩ : syracuseStep 10251629 = 3844361) B3844361
theorem B5328251 : Blo 1869636 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B2805161 : Blo 1869636 2805161 := bstep (se 2 (by rfl) ⟨1051935, by rfl⟩ : syracuseStep 2805161 = 2103871) B2103871
theorem B6311357 : Blo 1869636 6311357 := bstep (se 3 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 6311357 = 2366759) B2366759
theorem B1871335 : Blo 1869636 1871335 := bstep (se 1 (by rfl) ⟨1403501, by rfl⟩ : syracuseStep 1871335 = 2807003) B2807003
theorem B9465335 : Blo 1869636 9465335 := bstep (se 1 (by rfl) ⟨7099001, by rfl⟩ : syracuseStep 9465335 = 14198003) B14198003
theorem B2805311 : Blo 1869636 2805311 := bstep (se 1 (by rfl) ⟨2103983, by rfl⟩ : syracuseStep 2805311 = 4207967) B4207967
theorem B1871451 : Blo 1869636 1871451 := bstep (se 1 (by rfl) ⟨1403588, by rfl⟩ : syracuseStep 1871451 = 2807177) B2807177
theorem B29191889 : Blo 1869636 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B17985341 : Blo 1869636 17985341 := bstep (se 3 (by rfl) ⟨3372251, by rfl⟩ : syracuseStep 17985341 = 6744503) B6744503
theorem B2805575 : Blo 1869636 2805575 := bstep (se 1 (by rfl) ⟨2104181, by rfl⟩ : syracuseStep 2805575 = 4208363) B4208363
theorem B2805659 : Blo 1869636 2805659 := bstep (se 1 (by rfl) ⟨2104244, by rfl⟩ : syracuseStep 2805659 = 4208489) B4208489
theorem B6312059 : Blo 1869636 6312059 := bstep (se 1 (by rfl) ⟨4734044, by rfl⟩ : syracuseStep 6312059 = 9468089) B9468089
theorem B7991419 : Blo 1869636 7991419 := bstep (se 1 (by rfl) ⟨5993564, by rfl⟩ : syracuseStep 7991419 = 11987129) B11987129
theorem B5058683 : Blo 1869636 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B4206779 : Blo 1869636 4206779 := bstep (se 1 (by rfl) ⟨3155084, by rfl⟩ : syracuseStep 4206779 = 6310169) B6310169
theorem B3158203 : Blo 1869636 3158203 := bstep (se 1 (by rfl) ⟨2368652, by rfl⟩ : syracuseStep 3158203 = 4737305) B4737305
theorem B6312221 : Blo 1869636 6312221 := bstep (se 3 (by rfl) ⟨1183541, by rfl⟩ : syracuseStep 6312221 = 2367083) B2367083
theorem B9597251 : Blo 1869636 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B6312329 : Blo 1869636 6312329 := bstep (se 2 (by rfl) ⟨2367123, by rfl⟩ : syracuseStep 6312329 = 4734247) B4734247
theorem B2806223 : Blo 1869636 2806223 := bstep (se 1 (by rfl) ⟨2104667, by rfl⟩ : syracuseStep 2806223 = 4209335) B4209335
theorem B2806265 : Blo 1869636 2806265 := bstep (se 2 (by rfl) ⟨1052349, by rfl⟩ : syracuseStep 2806265 = 2104699) B2104699
theorem B3199583 : Blo 1869636 3199583 := bstep (se 1 (by rfl) ⟨2399687, by rfl⟩ : syracuseStep 3199583 = 4799375) B4799375
theorem B2806367 : Blo 1869636 2806367 := bstep (se 1 (by rfl) ⟨2104775, by rfl⟩ : syracuseStep 2806367 = 4209551) B4209551
theorem B4207265 : Blo 1869636 4207265 := bstep (se 2 (by rfl) ⟨1577724, by rfl⟩ : syracuseStep 4207265 = 3155449) B3155449
theorem B9466631 : Blo 1869636 9466631 := bstep (se 1 (by rfl) ⟨7099973, by rfl⟩ : syracuseStep 9466631 = 14199947) B14199947
theorem B3552007 : Blo 1869636 3552007 := bstep (se 1 (by rfl) ⟨2664005, by rfl⟩ : syracuseStep 3552007 = 5328011) B5328011
theorem B4207625 : Blo 1869636 4207625 := bstep (se 2 (by rfl) ⟨1577859, by rfl⟩ : syracuseStep 4207625 = 3155719) B3155719
theorem B53941261 : Blo 1869636 53941261 := bstep (se 3 (by rfl) ⟨10113986, by rfl⟩ : syracuseStep 53941261 = 20227973) B20227973
theorem B3552311 : Blo 1869636 3552311 := bstep (se 1 (by rfl) ⟨2664233, by rfl⟩ : syracuseStep 3552311 = 5328467) B5328467
theorem B4207679 : Blo 1869636 4207679 := bstep (se 1 (by rfl) ⟨3155759, by rfl⟩ : syracuseStep 4207679 = 6311519) B6311519
theorem B2806847 : Blo 1869636 2806847 := bstep (se 1 (by rfl) ⟨2105135, by rfl⟩ : syracuseStep 2806847 = 4210271) B4210271
theorem B2806889 : Blo 1869636 2806889 := bstep (se 2 (by rfl) ⟨1052583, by rfl⟩ : syracuseStep 2806889 = 2105167) B2105167
theorem B2806991 : Blo 1869636 2806991 := bstep (se 1 (by rfl) ⟨2105243, by rfl⟩ : syracuseStep 2806991 = 4210487) B4210487
theorem B6313247 : Blo 1869636 6313247 := bstep (se 1 (by rfl) ⟨4734935, by rfl⟩ : syracuseStep 6313247 = 9469871) B9469871
theorem B23958827 : Blo 1869636 23958827 := bstep (se 1 (by rfl) ⟨17969120, by rfl⟩ : syracuseStep 23958827 = 35938241) B35938241
theorem B2807195 : Blo 1869636 2807195 := bstep (se 1 (by rfl) ⟨2105396, by rfl⟩ : syracuseStep 2807195 = 4210793) B4210793
theorem B11990537 : Blo 1869636 11990537 := bstep (se 2 (by rfl) ⟨4496451, by rfl⟩ : syracuseStep 11990537 = 8992903) B8992903
theorem B2807417 : Blo 1869636 2807417 := bstep (se 2 (by rfl) ⟨1052781, by rfl⟩ : syracuseStep 2807417 = 2105563) B2105563
theorem B2995879 : Blo 1869636 2995879 := bstep (se 1 (by rfl) ⟨2246909, by rfl⟩ : syracuseStep 2995879 = 4493819) B4493819
theorem B9467603 : Blo 1869636 9467603 := bstep (se 1 (by rfl) ⟨7100702, by rfl⟩ : syracuseStep 9467603 = 14201405) B14201405
theorem B45496025 : Blo 1869636 45496025 := bstep (se 2 (by rfl) ⟨17061009, by rfl⟩ : syracuseStep 45496025 = 34122019) B34122019
theorem B17987345 : Blo 1869636 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B18233225 : Blo 1869636 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B13490135 : Blo 1869636 13490135 := bstep (se 1 (by rfl) ⟨10117601, by rfl⟩ : syracuseStep 13490135 = 20235203) B20235203
theorem B4208615 : Blo 1869636 4208615 := bstep (se 1 (by rfl) ⟨3156461, by rfl⟩ : syracuseStep 4208615 = 6312923) B6312923
theorem B7100399 : Blo 1869636 7100399 := bstep (se 1 (by rfl) ⟨5325299, by rfl⟩ : syracuseStep 7100399 = 10650599) B10650599
theorem B4208633 : Blo 1869636 4208633 := bstep (se 2 (by rfl) ⟨1578237, by rfl⟩ : syracuseStep 4208633 = 3156475) B3156475
theorem B582924347 : Blo 1869636 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B4208723 : Blo 1869636 4208723 := bstep (se 1 (by rfl) ⟨3156542, by rfl⟩ : syracuseStep 4208723 = 6313085) B6313085
theorem B4208795 : Blo 1869636 4208795 := bstep (se 1 (by rfl) ⟨3156596, by rfl⟩ : syracuseStep 4208795 = 6313193) B6313193
theorem B4208903 : Blo 1869636 4208903 := bstep (se 1 (by rfl) ⟨3156677, by rfl⟩ : syracuseStep 4208903 = 6313355) B6313355
theorem B12146959 : Blo 1869636 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B4733225 : Blo 1869636 4733225 := bstep (se 2 (by rfl) ⟨1774959, by rfl⟩ : syracuseStep 4733225 = 3549919) B3549919
theorem B2103835 : Blo 1869636 2103835 := bstep (se 1 (by rfl) ⟨1577876, by rfl⟩ : syracuseStep 2103835 = 3155753) B3155753
theorem B4209209 : Blo 1869636 4209209 := bstep (se 2 (by rfl) ⟨1578453, by rfl⟩ : syracuseStep 4209209 = 3156907) B3156907
theorem B9116497 : Blo 1869636 9116497 := bstep (se 2 (by rfl) ⟨3418686, by rfl⟩ : syracuseStep 9116497 = 6837373) B6837373
theorem B3791707 : Blo 1869636 3791707 := bstep (se 1 (by rfl) ⟨2843780, by rfl⟩ : syracuseStep 3791707 = 5687561) B5687561
theorem B10656683 : Blo 1869636 10656683 := bstep (se 1 (by rfl) ⟨7992512, by rfl⟩ : syracuseStep 10656683 = 15985025) B15985025
theorem B4733903 : Blo 1869636 4733903 := bstep (se 1 (by rfl) ⟨3550427, by rfl⟩ : syracuseStep 4733903 = 7100855) B7100855
theorem B3996641 : Blo 1869636 3996641 := bstep (se 2 (by rfl) ⟨1498740, by rfl⟩ : syracuseStep 3996641 = 2997481) B2997481
theorem B43801651 : Blo 1869636 43801651 := bstep (se 1 (by rfl) ⟨32851238, by rfl⟩ : syracuseStep 43801651 = 65702477) B65702477
theorem B6315137 : Blo 1869636 6315137 := bstep (se 2 (by rfl) ⟨2368176, by rfl⟩ : syracuseStep 6315137 = 4736353) B4736353
theorem B40459409 : Blo 1869636 40459409 := bstep (se 2 (by rfl) ⟨15172278, by rfl⟩ : syracuseStep 40459409 = 30344557) B30344557
theorem B6315191 : Blo 1869636 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B1998047 : Blo 1869636 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B4209929 : Blo 1869636 4209929 := bstep (se 2 (by rfl) ⟨1578723, by rfl⟩ : syracuseStep 4209929 = 3157447) B3157447
theorem B21298463 : Blo 1869636 21298463 := bstep (se 1 (by rfl) ⟨15973847, by rfl⟩ : syracuseStep 21298463 = 31947695) B31947695
theorem B9469223 : Blo 1869636 9469223 := bstep (se 1 (by rfl) ⟨7101917, by rfl⟩ : syracuseStep 9469223 = 14203835) B14203835
theorem B7101857 : Blo 1869636 7101857 := bstep (se 2 (by rfl) ⟨2663196, by rfl⟩ : syracuseStep 7101857 = 5326393) B5326393
theorem B2104807 : Blo 1869636 2104807 := bstep (se 1 (by rfl) ⟨1578605, by rfl⟩ : syracuseStep 2104807 = 3157211) B3157211
theorem B17071883 : Blo 1869636 17071883 := bstep (se 1 (by rfl) ⟨12803912, by rfl⟩ : syracuseStep 17071883 = 25607825) B25607825
theorem B11984669 : Blo 1869636 11984669 := bstep (se 3 (by rfl) ⟨2247125, by rfl⟩ : syracuseStep 11984669 = 4494251) B4494251
theorem B2662183 : Blo 1869636 2662183 := bstep (se 1 (by rfl) ⟨1996637, by rfl⟩ : syracuseStep 2662183 = 3993275) B3993275
theorem B3792811 : Blo 1869636 3792811 := bstep (se 1 (by rfl) ⟨2844608, by rfl⟩ : syracuseStep 3792811 = 5689217) B5689217
theorem B6315947 : Blo 1869636 6315947 := bstep (se 1 (by rfl) ⟨4736960, by rfl⟩ : syracuseStep 6315947 = 9473921) B9473921
theorem B2105311 : Blo 1869636 2105311 := bstep (se 1 (by rfl) ⟨1578983, by rfl⟩ : syracuseStep 2105311 = 3157967) B3157967
theorem B4210937 : Blo 1869636 4210937 := bstep (se 2 (by rfl) ⟨1579101, by rfl⟩ : syracuseStep 4210937 = 3158203) B3158203
theorem B5325095 : Blo 1869636 5325095 := bstep (se 1 (by rfl) ⟨3993821, by rfl⟩ : syracuseStep 5325095 = 7987643) B7987643
theorem B4210991 : Blo 1869636 4210991 := bstep (se 1 (by rfl) ⟨3158243, by rfl⟩ : syracuseStep 4210991 = 6316487) B6316487
theorem B16195945 : Blo 1869636 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B10650143 : Blo 1869636 10650143 := bstep (se 1 (by rfl) ⟨7987607, by rfl⟩ : syracuseStep 10650143 = 15975215) B15975215
theorem B2368207 : Blo 1869636 2368207 := bstep (se 1 (by rfl) ⟨1776155, by rfl⟩ : syracuseStep 2368207 = 3552311) B3552311
theorem B25592669 : Blo 1869636 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B60687305 : Blo 1869636 60687305 := bstep (se 2 (by rfl) ⟨22757739, by rfl⟩ : syracuseStep 60687305 = 45515479) B45515479
theorem B4736009 : Blo 1869636 4736009 := bstep (se 2 (by rfl) ⟨1776003, by rfl⟩ : syracuseStep 4736009 = 3552007) B3552007
theorem B15983689 : Blo 1869636 15983689 := bstep (se 2 (by rfl) ⟨5993883, by rfl⟩ : syracuseStep 15983689 = 11987767) B11987767
theorem B4736191 : Blo 1869636 4736191 := bstep (se 1 (by rfl) ⟨3552143, by rfl⟩ : syracuseStep 4736191 = 7104287) B7104287
theorem B7103801 : Blo 1869636 7103801 := bstep (se 2 (by rfl) ⟨2663925, by rfl⟩ : syracuseStep 7103801 = 5327851) B5327851
theorem B7587179 : Blo 1869636 7587179 := bstep (se 1 (by rfl) ⟨5690384, by rfl⟩ : syracuseStep 7587179 = 11380769) B11380769
theorem B58402201 : Blo 1869636 58402201 := bstep (se 2 (by rfl) ⟨21900825, by rfl⟩ : syracuseStep 58402201 = 43801651) B43801651
theorem B3155483 : Blo 1869636 3155483 := bstep (se 1 (by rfl) ⟨2366612, by rfl⟩ : syracuseStep 3155483 = 4733225) B4733225
theorem B80889749 : Blo 1869636 80889749 := bstep (se 6 (by rfl) ⟨1895853, by rfl⟩ : syracuseStep 80889749 = 3791707) B3791707
theorem B1869759 : Blo 1869636 1869759 := bstep (se 1 (by rfl) ⟨1402319, by rfl⟩ : syracuseStep 1869759 = 2804639) B2804639
theorem B7104455 : Blo 1869636 7104455 := bstep (se 1 (by rfl) ⟨5328341, by rfl⟩ : syracuseStep 7104455 = 10656683) B10656683
theorem B1869791 : Blo 1869636 1869791 := bstep (se 1 (by rfl) ⟨1402343, by rfl⟩ : syracuseStep 1869791 = 2804687) B2804687
theorem B3155935 : Blo 1869636 3155935 := bstep (se 1 (by rfl) ⟨2366951, by rfl⟩ : syracuseStep 3155935 = 4733903) B4733903
theorem B2664427 : Blo 1869636 2664427 := bstep (se 1 (by rfl) ⟨1998320, by rfl⟩ : syracuseStep 2664427 = 3996641) B3996641
theorem B1869851 : Blo 1869636 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B1869855 : Blo 1869636 1869855 := bstep (se 1 (by rfl) ⟨1402391, by rfl⟩ : syracuseStep 1869855 = 2804783) B2804783
theorem B1869871 : Blo 1869636 1869871 := bstep (se 1 (by rfl) ⟨1402403, by rfl⟩ : syracuseStep 1869871 = 2804807) B2804807
theorem B14198975 : Blo 1869636 14198975 := bstep (se 1 (by rfl) ⟨10649231, by rfl⟩ : syracuseStep 14198975 = 21298463) B21298463
theorem B1870047 : Blo 1869636 1870047 := bstep (se 1 (by rfl) ⟨1402535, by rfl⟩ : syracuseStep 1870047 = 2805071) B2805071
theorem B6834419 : Blo 1869636 6834419 := bstep (se 1 (by rfl) ⟨5125814, by rfl⟩ : syracuseStep 6834419 = 10251629) B10251629
theorem B1870107 : Blo 1869636 1870107 := bstep (se 1 (by rfl) ⟨1402580, by rfl⟩ : syracuseStep 1870107 = 2805161) B2805161
theorem B6310223 : Blo 1869636 6310223 := bstep (se 1 (by rfl) ⟨4732667, by rfl⟩ : syracuseStep 6310223 = 9465335) B9465335
theorem B1870207 : Blo 1869636 1870207 := bstep (se 1 (by rfl) ⟨1402655, by rfl⟩ : syracuseStep 1870207 = 2805311) B2805311
theorem B3549577 : Blo 1869636 3549577 := bstep (se 2 (by rfl) ⟨1331091, by rfl⟩ : syracuseStep 3549577 = 2662183) B2662183
theorem B11381255 : Blo 1869636 11381255 := bstep (se 1 (by rfl) ⟨8535941, by rfl⟩ : syracuseStep 11381255 = 17071883) B17071883
theorem B7989779 : Blo 1869636 7989779 := bstep (se 1 (by rfl) ⟨5992334, by rfl⟩ : syracuseStep 7989779 = 11984669) B11984669
theorem B1870383 : Blo 1869636 1870383 := bstep (se 1 (by rfl) ⟨1402787, by rfl⟩ : syracuseStep 1870383 = 2805575) B2805575
theorem B5057081 : Blo 1869636 5057081 := bstep (se 2 (by rfl) ⟨1896405, by rfl⟩ : syracuseStep 5057081 = 3792811) B3792811
theorem B1870439 : Blo 1869636 1870439 := bstep (se 1 (by rfl) ⟨1402829, by rfl⟩ : syracuseStep 1870439 = 2805659) B2805659
theorem B2804519 : Blo 1869636 2804519 := bstep (se 1 (by rfl) ⟨2103389, by rfl⟩ : syracuseStep 2804519 = 4206779) B4206779
theorem B7990103 : Blo 1869636 7990103 := bstep (se 1 (by rfl) ⟨5992577, by rfl⟩ : syracuseStep 7990103 = 11985155) B11985155
theorem B18475951 : Blo 1869636 18475951 := bstep (se 1 (by rfl) ⟨13856963, by rfl⟩ : syracuseStep 18475951 = 27713927) B27713927
theorem B1870815 : Blo 1869636 1870815 := bstep (se 1 (by rfl) ⟨1403111, by rfl⟩ : syracuseStep 1870815 = 2806223) B2806223
theorem B1870843 : Blo 1869636 1870843 := bstep (se 1 (by rfl) ⟨1403132, by rfl⟩ : syracuseStep 1870843 = 2806265) B2806265
theorem B2133055 : Blo 1869636 2133055 := bstep (se 1 (by rfl) ⟨1599791, by rfl⟩ : syracuseStep 2133055 = 3199583) B3199583
theorem B1870911 : Blo 1869636 1870911 := bstep (se 1 (by rfl) ⟨1403183, by rfl⟩ : syracuseStep 1870911 = 2806367) B2806367
theorem B2804843 : Blo 1869636 2804843 := bstep (se 1 (by rfl) ⟨2103632, by rfl⟩ : syracuseStep 2804843 = 4207265) B4207265
theorem B6311087 : Blo 1869636 6311087 := bstep (se 1 (by rfl) ⟨4733315, by rfl⟩ : syracuseStep 6311087 = 9466631) B9466631
theorem B5328125 : Blo 1869636 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B2805083 : Blo 1869636 2805083 := bstep (se 1 (by rfl) ⟨2103812, by rfl⟩ : syracuseStep 2805083 = 4207625) B4207625
theorem B2805113 : Blo 1869636 2805113 := bstep (se 2 (by rfl) ⟨1051917, by rfl⟩ : syracuseStep 2805113 = 2103835) B2103835
theorem B2805119 : Blo 1869636 2805119 := bstep (se 1 (by rfl) ⟨2103839, by rfl⟩ : syracuseStep 2805119 = 4207679) B4207679
theorem B1871231 : Blo 1869636 1871231 := bstep (se 1 (by rfl) ⟨1403423, by rfl⟩ : syracuseStep 1871231 = 2806847) B2806847
theorem B1871259 : Blo 1869636 1871259 := bstep (se 1 (by rfl) ⟨1403444, by rfl⟩ : syracuseStep 1871259 = 2806889) B2806889
theorem B8990135 : Blo 1869636 8990135 := bstep (se 1 (by rfl) ⟨6742601, by rfl⟩ : syracuseStep 8990135 = 13485203) B13485203
theorem B7990751 : Blo 1869636 7990751 := bstep (se 1 (by rfl) ⟨5993063, by rfl⟩ : syracuseStep 7990751 = 11986127) B11986127
theorem B1871327 : Blo 1869636 1871327 := bstep (se 1 (by rfl) ⟨1403495, by rfl⟩ : syracuseStep 1871327 = 2806991) B2806991
theorem B1871463 : Blo 1869636 1871463 := bstep (se 1 (by rfl) ⟨1403597, by rfl⟩ : syracuseStep 1871463 = 2807195) B2807195
theorem B1871611 : Blo 1869636 1871611 := bstep (se 1 (by rfl) ⟨1403708, by rfl⟩ : syracuseStep 1871611 = 2807417) B2807417
theorem B6311735 : Blo 1869636 6311735 := bstep (se 1 (by rfl) ⟨4733801, by rfl⟩ : syracuseStep 6311735 = 9467603) B9467603
theorem B30330683 : Blo 1869636 30330683 := bstep (se 1 (by rfl) ⟨22748012, by rfl⟩ : syracuseStep 30330683 = 45496025) B45496025
theorem B37941173 : Blo 1869636 37941173 := bstep (se 5 (by rfl) ⟨1778492, by rfl⟩ : syracuseStep 37941173 = 3556985) B3556985
theorem B2805743 : Blo 1869636 2805743 := bstep (se 1 (by rfl) ⟨2104307, by rfl⟩ : syracuseStep 2805743 = 4208615) B4208615
theorem B2805755 : Blo 1869636 2805755 := bstep (se 1 (by rfl) ⟨2104316, by rfl⟩ : syracuseStep 2805755 = 4208633) B4208633
theorem B71921681 : Blo 1869636 71921681 := bstep (se 2 (by rfl) ⟨26970630, by rfl⟩ : syracuseStep 71921681 = 53941261) B53941261
theorem B388616231 : Blo 1869636 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B2805815 : Blo 1869636 2805815 := bstep (se 1 (by rfl) ⟨2104361, by rfl⟩ : syracuseStep 2805815 = 4208723) B4208723
theorem B4206689 : Blo 1869636 4206689 := bstep (se 2 (by rfl) ⟨1577508, by rfl⟩ : syracuseStep 4206689 = 3155017) B3155017
theorem B2805863 : Blo 1869636 2805863 := bstep (se 1 (by rfl) ⟨2104397, by rfl⟩ : syracuseStep 2805863 = 4208795) B4208795
theorem B2805935 : Blo 1869636 2805935 := bstep (se 1 (by rfl) ⟨2104451, by rfl⟩ : syracuseStep 2805935 = 4208903) B4208903
theorem B2806139 : Blo 1869636 2806139 := bstep (se 1 (by rfl) ⟨2104604, by rfl⟩ : syracuseStep 2806139 = 4209209) B4209209
theorem B22753703 : Blo 1869636 22753703 := bstep (se 1 (by rfl) ⟨17065277, by rfl⟩ : syracuseStep 22753703 = 34130555) B34130555
theorem B3600839 : Blo 1869636 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B68235857 : Blo 1869636 68235857 := bstep (se 2 (by rfl) ⟨25588446, by rfl⟩ : syracuseStep 68235857 = 51176893) B51176893
theorem B2806409 : Blo 1869636 2806409 := bstep (se 2 (by rfl) ⟨1052403, by rfl⟩ : syracuseStep 2806409 = 2104807) B2104807
theorem B4207355 : Blo 1869636 4207355 := bstep (se 1 (by rfl) ⟨3155516, by rfl⟩ : syracuseStep 4207355 = 6311033) B6311033
theorem B26972939 : Blo 1869636 26972939 := bstep (se 1 (by rfl) ⟨20229704, by rfl⟩ : syracuseStep 26972939 = 40459409) B40459409
theorem B8532803 : Blo 1869636 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B47960909 : Blo 1869636 47960909 := bstep (se 3 (by rfl) ⟨8992670, by rfl⟩ : syracuseStep 47960909 = 17985341) B17985341
theorem B2806619 : Blo 1869636 2806619 := bstep (se 1 (by rfl) ⟨2104964, by rfl⟩ : syracuseStep 2806619 = 4209929) B4209929
theorem B6312815 : Blo 1869636 6312815 := bstep (se 1 (by rfl) ⟨4734611, by rfl⟩ : syracuseStep 6312815 = 9469223) B9469223
theorem B3994505 : Blo 1869636 3994505 := bstep (se 2 (by rfl) ⟨1497939, by rfl⟩ : syracuseStep 3994505 = 2995879) B2995879
theorem B3552167 : Blo 1869636 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B4207571 : Blo 1869636 4207571 := bstep (se 1 (by rfl) ⟨3155678, by rfl⟩ : syracuseStep 4207571 = 6311357) B6311357
theorem B73905209 : Blo 1869636 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B19461259 : Blo 1869636 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B2807081 : Blo 1869636 2807081 := bstep (se 2 (by rfl) ⟨1052655, by rfl⟩ : syracuseStep 2807081 = 2105311) B2105311
theorem B4208039 : Blo 1869636 4208039 := bstep (se 1 (by rfl) ⟨3156029, by rfl⟩ : syracuseStep 4208039 = 6312059) B6312059
theorem B3372455 : Blo 1869636 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B2807279 : Blo 1869636 2807279 := bstep (se 1 (by rfl) ⟨2105459, by rfl⟩ : syracuseStep 2807279 = 4210919) B4210919
theorem B10655225 : Blo 1869636 10655225 := bstep (se 2 (by rfl) ⟨3995709, by rfl⟩ : syracuseStep 10655225 = 7991419) B7991419
theorem B14202377 : Blo 1869636 14202377 := bstep (se 2 (by rfl) ⟨5325891, by rfl⟩ : syracuseStep 14202377 = 10651783) B10651783
theorem B4208147 : Blo 1869636 4208147 := bstep (se 1 (by rfl) ⟨3156110, by rfl⟩ : syracuseStep 4208147 = 6312221) B6312221
theorem B4208219 : Blo 1869636 4208219 := bstep (se 1 (by rfl) ⟨3156164, by rfl⟩ : syracuseStep 4208219 = 6312329) B6312329
theorem B2103367 : Blo 1869636 2103367 := bstep (se 1 (by rfl) ⟨1577525, by rfl⟩ : syracuseStep 2103367 = 3155051) B3155051
theorem B4208831 : Blo 1869636 4208831 := bstep (se 1 (by rfl) ⟨3156623, by rfl⟩ : syracuseStep 4208831 = 6313247) B6313247
theorem B15972551 : Blo 1869636 15972551 := bstep (se 1 (by rfl) ⟨11979413, by rfl⟩ : syracuseStep 15972551 = 23958827) B23958827
theorem B7993691 : Blo 1869636 7993691 := bstep (se 1 (by rfl) ⟨5995268, by rfl⟩ : syracuseStep 7993691 = 11990537) B11990537
theorem B12155329 : Blo 1869636 12155329 := bstep (se 2 (by rfl) ⟨4558248, by rfl⟩ : syracuseStep 12155329 = 9116497) B9116497
theorem B11991563 : Blo 1869636 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B14211611 : Blo 1869636 14211611 := bstep (se 1 (by rfl) ⟨10658708, by rfl⟩ : syracuseStep 14211611 = 21317417) B21317417
theorem B12155483 : Blo 1869636 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B8993423 : Blo 1869636 8993423 := bstep (se 1 (by rfl) ⟨6745067, by rfl⟩ : syracuseStep 8993423 = 13490135) B13490135
theorem B4733599 : Blo 1869636 4733599 := bstep (se 1 (by rfl) ⟨3550199, by rfl⟩ : syracuseStep 4733599 = 7100399) B7100399
theorem B13671179 : Blo 1869636 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B2104231 : Blo 1869636 2104231 := bstep (se 1 (by rfl) ⟨1578173, by rfl⟩ : syracuseStep 2104231 = 3156347) B3156347
theorem B7199707 : Blo 1869636 7199707 := bstep (se 1 (by rfl) ⟨5399780, by rfl⟩ : syracuseStep 7199707 = 10799561) B10799561
theorem B7584749 : Blo 1869636 7584749 := bstep (se 3 (by rfl) ⟨1422140, by rfl⟩ : syracuseStep 7584749 = 2844281) B2844281
theorem B8993825 : Blo 1869636 8993825 := bstep (se 2 (by rfl) ⟨3372684, by rfl⟩ : syracuseStep 8993825 = 6745369) B6745369
theorem B2104411 : Blo 1869636 2104411 := bstep (se 1 (by rfl) ⟨1578308, by rfl⟩ : syracuseStep 2104411 = 3156617) B3156617
theorem B15162653 : Blo 1869636 15162653 := bstep (se 3 (by rfl) ⟨2842997, by rfl⟩ : syracuseStep 15162653 = 5685995) B5685995
theorem B4210091 : Blo 1869636 4210091 := bstep (se 1 (by rfl) ⟨3157568, by rfl⟩ : syracuseStep 4210091 = 6315137) B6315137
theorem B4210127 : Blo 1869636 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B4734571 : Blo 1869636 4734571 := bstep (se 1 (by rfl) ⟨3550928, by rfl⟩ : syracuseStep 4734571 = 7101857) B7101857
theorem B4210631 : Blo 1869636 4210631 := bstep (se 1 (by rfl) ⟨3157973, by rfl⟩ : syracuseStep 4210631 = 6315947) B6315947
theorem B47947787 : Blo 1869636 47947787 := bstep (se 1 (by rfl) ⟨35960840, by rfl⟩ : syracuseStep 47947787 = 71921681) B71921681
theorem B2400559 : Blo 1869636 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B45490571 : Blo 1869636 45490571 := bstep (se 1 (by rfl) ⟨34117928, by rfl⟩ : syracuseStep 45490571 = 68235857) B68235857
theorem B21594593 : Blo 1869636 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B17981959 : Blo 1869636 17981959 := bstep (se 1 (by rfl) ⟨13486469, by rfl⟩ : syracuseStep 17981959 = 26972939) B26972939
theorem B31973939 : Blo 1869636 31973939 := bstep (se 1 (by rfl) ⟨23980454, by rfl⟩ : syracuseStep 31973939 = 47960909) B47960909
theorem B2663003 : Blo 1869636 2663003 := bstep (se 1 (by rfl) ⟨1997252, by rfl⟩ : syracuseStep 2663003 = 3994505) B3994505
theorem B2368111 : Blo 1869636 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B4735867 : Blo 1869636 4735867 := bstep (se 1 (by rfl) ⟨3551900, by rfl⟩ : syracuseStep 4735867 = 7103801) B7103801
theorem B7103483 : Blo 1869636 7103483 := bstep (se 1 (by rfl) ⟨5327612, by rfl⟩ : syracuseStep 7103483 = 10655225) B10655225
theorem B24634601 : Blo 1869636 24634601 := bstep (se 2 (by rfl) ⟨9237975, by rfl⟩ : syracuseStep 24634601 = 18475951) B18475951
theorem B21308669 : Blo 1869636 21308669 := bstep (se 3 (by rfl) ⟨3995375, by rfl⟩ : syracuseStep 21308669 = 7990751) B7990751
theorem B4736303 : Blo 1869636 4736303 := bstep (se 1 (by rfl) ⟨3552227, by rfl⟩ : syracuseStep 4736303 = 7104455) B7104455
theorem B2844073 : Blo 1869636 2844073 := bstep (se 2 (by rfl) ⟨1066527, by rfl⟩ : syracuseStep 2844073 = 2133055) B2133055
theorem B4556279 : Blo 1869636 4556279 := bstep (se 1 (by rfl) ⟨3417209, by rfl⟩ : syracuseStep 4556279 = 6834419) B6834419
theorem B7587503 : Blo 1869636 7587503 := bstep (se 1 (by rfl) ⟨5690627, by rfl⟩ : syracuseStep 7587503 = 11381255) B11381255
theorem B5326519 : Blo 1869636 5326519 := bstep (se 1 (by rfl) ⟨3994889, by rfl⟩ : syracuseStep 5326519 = 7989779) B7989779
theorem B8103655 : Blo 1869636 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B1869679 : Blo 1869636 1869679 := bstep (se 1 (by rfl) ⟨1402259, by rfl⟩ : syracuseStep 1869679 = 2804519) B2804519
theorem B5326735 : Blo 1869636 5326735 := bstep (se 1 (by rfl) ⟨3995051, by rfl⟩ : syracuseStep 5326735 = 7990103) B7990103
theorem B5056499 : Blo 1869636 5056499 := bstep (se 1 (by rfl) ⟨3792374, by rfl⟩ : syracuseStep 5056499 = 7584749) B7584749
theorem B1869895 : Blo 1869636 1869895 := bstep (se 1 (by rfl) ⟨1402421, by rfl⟩ : syracuseStep 1869895 = 2804843) B2804843
theorem B1870055 : Blo 1869636 1870055 := bstep (se 1 (by rfl) ⟨1402541, by rfl⟩ : syracuseStep 1870055 = 2805083) B2805083
theorem B1870075 : Blo 1869636 1870075 := bstep (se 1 (by rfl) ⟨1402556, by rfl⟩ : syracuseStep 1870075 = 2805113) B2805113
theorem B1870079 : Blo 1869636 1870079 := bstep (se 1 (by rfl) ⟨1402559, by rfl⟩ : syracuseStep 1870079 = 2805119) B2805119
theorem B20220455 : Blo 1869636 20220455 := bstep (se 1 (by rfl) ⟨15165341, by rfl⟩ : syracuseStep 20220455 = 30330683) B30330683
theorem B1870495 : Blo 1869636 1870495 := bstep (se 1 (by rfl) ⟨1402871, by rfl⟩ : syracuseStep 1870495 = 2805743) B2805743
theorem B1870503 : Blo 1869636 1870503 := bstep (se 1 (by rfl) ⟨1402877, by rfl⟩ : syracuseStep 1870503 = 2805755) B2805755
theorem B1870543 : Blo 1869636 1870543 := bstep (se 1 (by rfl) ⟨1402907, by rfl⟩ : syracuseStep 1870543 = 2805815) B2805815
theorem B2804459 : Blo 1869636 2804459 := bstep (se 1 (by rfl) ⟨2103344, by rfl⟩ : syracuseStep 2804459 = 4206689) B4206689
theorem B1870575 : Blo 1869636 1870575 := bstep (se 1 (by rfl) ⟨1402931, by rfl⟩ : syracuseStep 1870575 = 2805863) B2805863
theorem B2804489 : Blo 1869636 2804489 := bstep (se 2 (by rfl) ⟨1051683, by rfl⟩ : syracuseStep 2804489 = 2103367) B2103367
theorem B1870623 : Blo 1869636 1870623 := bstep (se 1 (by rfl) ⟨1402967, by rfl⟩ : syracuseStep 1870623 = 2805935) B2805935
theorem B3550063 : Blo 1869636 3550063 := bstep (se 1 (by rfl) ⟨2662547, by rfl⟩ : syracuseStep 3550063 = 5325095) B5325095
theorem B1870759 : Blo 1869636 1870759 := bstep (se 1 (by rfl) ⟨1403069, by rfl⟩ : syracuseStep 1870759 = 2806139) B2806139
theorem B1870939 : Blo 1869636 1870939 := bstep (se 1 (by rfl) ⟨1403204, by rfl⟩ : syracuseStep 1870939 = 2806409) B2806409
theorem B2804903 : Blo 1869636 2804903 := bstep (se 1 (by rfl) ⟨2103677, by rfl⟩ : syracuseStep 2804903 = 4207355) B4207355
theorem B1871079 : Blo 1869636 1871079 := bstep (se 1 (by rfl) ⟨1403309, by rfl⟩ : syracuseStep 1871079 = 2806619) B2806619
theorem B2805047 : Blo 1869636 2805047 := bstep (se 1 (by rfl) ⟨2103785, by rfl⟩ : syracuseStep 2805047 = 4207571) B4207571
theorem B3157339 : Blo 1869636 3157339 := bstep (se 1 (by rfl) ⟨2368004, by rfl⟩ : syracuseStep 3157339 = 4736009) B4736009
theorem B49270139 : Blo 1869636 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B1871387 : Blo 1869636 1871387 := bstep (se 1 (by rfl) ⟨1403540, by rfl⟩ : syracuseStep 1871387 = 2807081) B2807081
theorem B6311465 : Blo 1869636 6311465 := bstep (se 2 (by rfl) ⟨2366799, by rfl⟩ : syracuseStep 6311465 = 4733599) B4733599
theorem B5058119 : Blo 1869636 5058119 := bstep (se 1 (by rfl) ⟨3793589, by rfl⟩ : syracuseStep 5058119 = 7587179) B7587179
theorem B3157609 : Blo 1869636 3157609 := bstep (se 2 (by rfl) ⟨1184103, by rfl⟩ : syracuseStep 3157609 = 2368207) B2368207
theorem B2805359 : Blo 1869636 2805359 := bstep (se 1 (by rfl) ⟨2104019, by rfl⟩ : syracuseStep 2805359 = 4208039) B4208039
theorem B2248303 : Blo 1869636 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B1871519 : Blo 1869636 1871519 := bstep (se 1 (by rfl) ⟨1403639, by rfl⟩ : syracuseStep 1871519 = 2807279) B2807279
theorem B2805431 : Blo 1869636 2805431 := bstep (se 1 (by rfl) ⟨2104073, by rfl⟩ : syracuseStep 2805431 = 4208147) B4208147
theorem B2805479 : Blo 1869636 2805479 := bstep (se 1 (by rfl) ⟨2104109, by rfl⟩ : syracuseStep 2805479 = 4208219) B4208219
theorem B2805641 : Blo 1869636 2805641 := bstep (se 2 (by rfl) ⟨1052115, by rfl⟩ : syracuseStep 2805641 = 2104231) B2104231
theorem B21311585 : Blo 1869636 21311585 := bstep (se 2 (by rfl) ⟨7991844, by rfl⟩ : syracuseStep 21311585 = 15983689) B15983689
theorem B2805881 : Blo 1869636 2805881 := bstep (se 2 (by rfl) ⟨1052205, by rfl⟩ : syracuseStep 2805881 = 2104411) B2104411
theorem B9465983 : Blo 1869636 9465983 := bstep (se 1 (by rfl) ⟨7099487, by rfl⟩ : syracuseStep 9465983 = 14198975) B14198975
theorem B2805887 : Blo 1869636 2805887 := bstep (se 1 (by rfl) ⟨2104415, by rfl⟩ : syracuseStep 2805887 = 4208831) B4208831
theorem B25948345 : Blo 1869636 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B4206815 : Blo 1869636 4206815 := bstep (se 1 (by rfl) ⟨3155111, by rfl⟩ : syracuseStep 4206815 = 6310223) B6310223
theorem B5329127 : Blo 1869636 5329127 := bstep (se 1 (by rfl) ⟨3996845, by rfl⟩ : syracuseStep 5329127 = 7993691) B7993691
theorem B9474407 : Blo 1869636 9474407 := bstep (se 1 (by rfl) ⟨7105805, by rfl⟩ : syracuseStep 9474407 = 14211611) B14211611
theorem B3371387 : Blo 1869636 3371387 := bstep (se 1 (by rfl) ⟨2528540, by rfl⟩ : syracuseStep 3371387 = 5057081) B5057081
theorem B9114119 : Blo 1869636 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B77869601 : Blo 1869636 77869601 := bstep (se 2 (by rfl) ⟨29201100, by rfl⟩ : syracuseStep 77869601 = 58402201) B58402201
theorem B4207391 : Blo 1869636 4207391 := bstep (se 1 (by rfl) ⟨3155543, by rfl⟩ : syracuseStep 4207391 = 6311087) B6311087
theorem B6312761 : Blo 1869636 6312761 := bstep (se 2 (by rfl) ⟨2367285, by rfl⟩ : syracuseStep 6312761 = 4734571) B4734571
theorem B3552083 : Blo 1869636 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B22754141 : Blo 1869636 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B2806727 : Blo 1869636 2806727 := bstep (se 1 (by rfl) ⟨2105045, by rfl⟩ : syracuseStep 2806727 = 4210091) B4210091
theorem B5993423 : Blo 1869636 5993423 := bstep (se 1 (by rfl) ⟨4495067, by rfl⟩ : syracuseStep 5993423 = 8990135) B8990135
theorem B2806751 : Blo 1869636 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B64828421 : Blo 1869636 64828421 := bstep (se 4 (by rfl) ⟨6077664, by rfl⟩ : syracuseStep 64828421 = 12155329) B12155329
theorem B4207823 : Blo 1869636 4207823 := bstep (se 1 (by rfl) ⟨3155867, by rfl⟩ : syracuseStep 4207823 = 6311735) B6311735
theorem B25294115 : Blo 1869636 25294115 := bstep (se 1 (by rfl) ⟨18970586, by rfl⟩ : syracuseStep 25294115 = 37941173) B37941173
theorem B4207913 : Blo 1869636 4207913 := bstep (se 2 (by rfl) ⟨1577967, by rfl⟩ : syracuseStep 4207913 = 3155935) B3155935
theorem B2807087 : Blo 1869636 2807087 := bstep (se 1 (by rfl) ⟨2105315, by rfl⟩ : syracuseStep 2807087 = 4210631) B4210631
theorem B3552569 : Blo 1869636 3552569 := bstep (se 2 (by rfl) ⟨1332213, by rfl⟩ : syracuseStep 3552569 = 2664427) B2664427
theorem B259077487 : Blo 1869636 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B2807291 : Blo 1869636 2807291 := bstep (se 1 (by rfl) ⟨2105468, by rfl⟩ : syracuseStep 2807291 = 4210937) B4210937
theorem B2807327 : Blo 1869636 2807327 := bstep (se 1 (by rfl) ⟨2105495, by rfl⟩ : syracuseStep 2807327 = 4210991) B4210991
theorem B15169135 : Blo 1869636 15169135 := bstep (se 1 (by rfl) ⟨11376851, by rfl⟩ : syracuseStep 15169135 = 22753703) B22753703
theorem B7100095 : Blo 1869636 7100095 := bstep (se 1 (by rfl) ⟨5325071, by rfl⟩ : syracuseStep 7100095 = 10650143) B10650143
theorem B4732769 : Blo 1869636 4732769 := bstep (se 2 (by rfl) ⟨1774788, by rfl⟩ : syracuseStep 4732769 = 3549577) B3549577
theorem B17061779 : Blo 1869636 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B4208543 : Blo 1869636 4208543 := bstep (se 1 (by rfl) ⟨3156407, by rfl⟩ : syracuseStep 4208543 = 6312815) B6312815
theorem B40458203 : Blo 1869636 40458203 := bstep (se 1 (by rfl) ⟨30343652, by rfl⟩ : syracuseStep 40458203 = 60687305) B60687305
theorem B9468251 : Blo 1869636 9468251 := bstep (se 1 (by rfl) ⟨7101188, by rfl⟩ : syracuseStep 9468251 = 14202377) B14202377
theorem B2103655 : Blo 1869636 2103655 := bstep (se 1 (by rfl) ⟨1577741, by rfl⟩ : syracuseStep 2103655 = 3155483) B3155483
theorem B53926499 : Blo 1869636 53926499 := bstep (se 1 (by rfl) ⟨40444874, by rfl⟩ : syracuseStep 53926499 = 80889749) B80889749
theorem B9599609 : Blo 1869636 9599609 := bstep (se 2 (by rfl) ⟨3599853, by rfl⟩ : syracuseStep 9599609 = 7199707) B7199707
theorem B10648367 : Blo 1869636 10648367 := bstep (se 1 (by rfl) ⟨7986275, by rfl⟩ : syracuseStep 10648367 = 15972551) B15972551
theorem B6314921 : Blo 1869636 6314921 := bstep (se 2 (by rfl) ⟨2368095, by rfl⟩ : syracuseStep 6314921 = 4736191) B4736191
theorem B7994375 : Blo 1869636 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B5995615 : Blo 1869636 5995615 := bstep (se 1 (by rfl) ⟨4496711, by rfl⟩ : syracuseStep 5995615 = 8993423) B8993423
theorem B5995883 : Blo 1869636 5995883 := bstep (se 1 (by rfl) ⟨4496912, by rfl⟩ : syracuseStep 5995883 = 8993825) B8993825
theorem B10108435 : Blo 1869636 10108435 := bstep (se 1 (by rfl) ⟨7581326, by rfl⟩ : syracuseStep 10108435 = 15162653) B15162653
theorem B31965191 : Blo 1869636 31965191 := bstep (se 1 (by rfl) ⟨23973893, by rfl⟩ : syracuseStep 31965191 = 47947787) B47947787
theorem B6316271 : Blo 1869636 6316271 := bstep (se 1 (by rfl) ⟨4737203, by rfl⟩ : syracuseStep 6316271 = 9474407) B9474407
theorem B30327047 : Blo 1869636 30327047 := bstep (se 1 (by rfl) ⟨22745285, by rfl⟩ : syracuseStep 30327047 = 45490571) B45490571
theorem B51913067 : Blo 1869636 51913067 := bstep (se 1 (by rfl) ⟨38934800, by rfl⟩ : syracuseStep 51913067 = 77869601) B77869601
theorem B21315959 : Blo 1869636 21315959 := bstep (se 1 (by rfl) ⟨15986969, by rfl⟩ : syracuseStep 21315959 = 31973939) B31973939
theorem B2368055 : Blo 1869636 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B4735655 : Blo 1869636 4735655 := bstep (se 1 (by rfl) ⟨3551741, by rfl⟩ : syracuseStep 4735655 = 7103483) B7103483
theorem B14205779 : Blo 1869636 14205779 := bstep (se 1 (by rfl) ⟨10654334, by rfl⟩ : syracuseStep 14205779 = 21308669) B21308669
theorem B2368379 : Blo 1869636 2368379 := bstep (se 1 (by rfl) ⟨1776284, by rfl⟩ : syracuseStep 2368379 = 3552569) B3552569
theorem B3155179 : Blo 1869636 3155179 := bstep (se 1 (by rfl) ⟨2366384, by rfl⟩ : syracuseStep 3155179 = 4732769) B4732769
theorem B6399739 : Blo 1869636 6399739 := bstep (se 1 (by rfl) ⟨4799804, by rfl⟩ : syracuseStep 6399739 = 9599609) B9599609
theorem B1869639 : Blo 1869636 1869639 := bstep (se 1 (by rfl) ⟨1402229, by rfl⟩ : syracuseStep 1869639 = 2804459) B2804459
theorem B1869659 : Blo 1869636 1869659 := bstep (se 1 (by rfl) ⟨1402244, by rfl⟩ : syracuseStep 1869659 = 2804489) B2804489
theorem B13477913 : Blo 1869636 13477913 := bstep (se 2 (by rfl) ⟨5054217, by rfl⟩ : syracuseStep 13477913 = 10108435) B10108435
theorem B1869935 : Blo 1869636 1869935 := bstep (se 1 (by rfl) ⟨1402451, by rfl⟩ : syracuseStep 1869935 = 2804903) B2804903
theorem B1870031 : Blo 1869636 1870031 := bstep (se 1 (by rfl) ⟨1402523, by rfl⟩ : syracuseStep 1870031 = 2805047) B2805047
theorem B1870239 : Blo 1869636 1870239 := bstep (se 1 (by rfl) ⟨1402679, by rfl⟩ : syracuseStep 1870239 = 2805359) B2805359
theorem B1870287 : Blo 1869636 1870287 := bstep (se 1 (by rfl) ⟨1402715, by rfl⟩ : syracuseStep 1870287 = 2805431) B2805431
theorem B1870319 : Blo 1869636 1870319 := bstep (se 1 (by rfl) ⟨1402739, by rfl⟩ : syracuseStep 1870319 = 2805479) B2805479
theorem B1870427 : Blo 1869636 1870427 := bstep (se 1 (by rfl) ⟨1402820, by rfl⟩ : syracuseStep 1870427 = 2805641) B2805641
theorem B14207723 : Blo 1869636 14207723 := bstep (se 1 (by rfl) ⟨10655792, by rfl⟩ : syracuseStep 14207723 = 21311585) B21311585
theorem B1870587 : Blo 1869636 1870587 := bstep (se 1 (by rfl) ⟨1402940, by rfl⟩ : syracuseStep 1870587 = 2805881) B2805881
theorem B6310655 : Blo 1869636 6310655 := bstep (se 1 (by rfl) ⟨4732991, by rfl⟩ : syracuseStep 6310655 = 9465983) B9465983
theorem B1870591 : Blo 1869636 1870591 := bstep (se 1 (by rfl) ⟨1402943, by rfl⟩ : syracuseStep 1870591 = 2805887) B2805887
theorem B2804543 : Blo 1869636 2804543 := bstep (se 1 (by rfl) ⟨2103407, by rfl⟩ : syracuseStep 2804543 = 4206815) B4206815
theorem B34597793 : Blo 1869636 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B14396395 : Blo 1869636 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B2804873 : Blo 1869636 2804873 := bstep (se 2 (by rfl) ⟨1051827, by rfl⟩ : syracuseStep 2804873 = 2103655) B2103655
theorem B2804927 : Blo 1869636 2804927 := bstep (se 1 (by rfl) ⟨2103695, by rfl⟩ : syracuseStep 2804927 = 4207391) B4207391
theorem B1871151 : Blo 1869636 1871151 := bstep (se 1 (by rfl) ⟨1403363, by rfl⟩ : syracuseStep 1871151 = 2806727) B2806727
theorem B1871167 : Blo 1869636 1871167 := bstep (se 1 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 1871167 = 2806751) B2806751
theorem B2805215 : Blo 1869636 2805215 := bstep (se 1 (by rfl) ⟨2103911, by rfl⟩ : syracuseStep 2805215 = 4207823) B4207823
theorem B3157481 : Blo 1869636 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B16862743 : Blo 1869636 16862743 := bstep (se 1 (by rfl) ⟨12647057, by rfl⟩ : syracuseStep 16862743 = 25294115) B25294115
theorem B2805275 : Blo 1869636 2805275 := bstep (se 1 (by rfl) ⟨2103956, by rfl⟩ : syracuseStep 2805275 = 4207913) B4207913
theorem B3157535 : Blo 1869636 3157535 := bstep (se 1 (by rfl) ⟨2368151, by rfl⟩ : syracuseStep 3157535 = 4736303) B4736303
theorem B1871391 : Blo 1869636 1871391 := bstep (se 1 (by rfl) ⟨1403543, by rfl⟩ : syracuseStep 1871391 = 2807087) B2807087
theorem B8990365 : Blo 1869636 8990365 := bstep (se 3 (by rfl) ⟨1685693, by rfl⟩ : syracuseStep 8990365 = 3371387) B3371387
theorem B1871527 : Blo 1869636 1871527 := bstep (se 1 (by rfl) ⟨1403645, by rfl⟩ : syracuseStep 1871527 = 2807291) B2807291
theorem B1871551 : Blo 1869636 1871551 := bstep (se 1 (by rfl) ⟨1403663, by rfl⟩ : syracuseStep 1871551 = 2807327) B2807327
theorem B5058335 : Blo 1869636 5058335 := bstep (se 1 (by rfl) ⟨3793751, by rfl⟩ : syracuseStep 5058335 = 7587503) B7587503
theorem B11374519 : Blo 1869636 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B2805695 : Blo 1869636 2805695 := bstep (se 1 (by rfl) ⟨2104271, by rfl⟩ : syracuseStep 2805695 = 4208543) B4208543
theorem B26972135 : Blo 1869636 26972135 := bstep (se 1 (by rfl) ⟨20229101, by rfl⟩ : syracuseStep 26972135 = 40458203) B40458203
theorem B3370999 : Blo 1869636 3370999 := bstep (se 1 (by rfl) ⟨2528249, by rfl⟩ : syracuseStep 3370999 = 5056499) B5056499
theorem B6312167 : Blo 1869636 6312167 := bstep (se 1 (by rfl) ⟨4734125, by rfl⟩ : syracuseStep 6312167 = 9468251) B9468251
theorem B13480303 : Blo 1869636 13480303 := bstep (se 1 (by rfl) ⟨10110227, by rfl⟩ : syracuseStep 13480303 = 20220455) B20220455
theorem B35950999 : Blo 1869636 35950999 := bstep (se 1 (by rfl) ⟨26963249, by rfl⟩ : syracuseStep 35950999 = 53926499) B53926499
theorem B345436649 : Blo 1869636 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B7098911 : Blo 1869636 7098911 := bstep (se 1 (by rfl) ⟨5324183, by rfl⟩ : syracuseStep 7098911 = 10648367) B10648367
theorem B5329583 : Blo 1869636 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B32846759 : Blo 1869636 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B9466793 : Blo 1869636 9466793 := bstep (se 2 (by rfl) ⟨3550047, by rfl⟩ : syracuseStep 9466793 = 7100095) B7100095
theorem B4207643 : Blo 1869636 4207643 := bstep (se 1 (by rfl) ⟨3155732, by rfl⟩ : syracuseStep 4207643 = 6311465) B6311465
theorem B3372079 : Blo 1869636 3372079 := bstep (se 1 (by rfl) ⟨2529059, by rfl⟩ : syracuseStep 3372079 = 5058119) B5058119
theorem B3552751 : Blo 1869636 3552751 := bstep (se 1 (by rfl) ⟨2664563, by rfl⟩ : syracuseStep 3552751 = 5329127) B5329127
theorem B6076079 : Blo 1869636 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B4208507 : Blo 1869636 4208507 := bstep (se 1 (by rfl) ⟨3156380, by rfl⟩ : syracuseStep 4208507 = 6312761) B6312761
theorem B15169427 : Blo 1869636 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B3995615 : Blo 1869636 3995615 := bstep (se 1 (by rfl) ⟨2996711, by rfl⟩ : syracuseStep 3995615 = 5993423) B5993423
theorem B43218947 : Blo 1869636 43218947 := bstep (se 1 (by rfl) ⟨32414210, by rfl⟩ : syracuseStep 43218947 = 64828421) B64828421
theorem B23975945 : Blo 1869636 23975945 := bstep (se 2 (by rfl) ⟨8990979, by rfl⟩ : syracuseStep 23975945 = 17981959) B17981959
theorem B16423067 : Blo 1869636 16423067 := bstep (se 1 (by rfl) ⟨12317300, by rfl⟩ : syracuseStep 16423067 = 24634601) B24634601
theorem B15989021 : Blo 1869636 15989021 := bstep (se 3 (by rfl) ⟨2997941, by rfl⟩ : syracuseStep 15989021 = 5995883) B5995883
theorem B3037519 : Blo 1869636 3037519 := bstep (se 1 (by rfl) ⟨2278139, by rfl⟩ : syracuseStep 3037519 = 4556279) B4556279
theorem B4733417 : Blo 1869636 4733417 := bstep (se 2 (by rfl) ⟨1775031, by rfl⟩ : syracuseStep 4733417 = 3550063) B3550063
theorem B6314489 : Blo 1869636 6314489 := bstep (se 2 (by rfl) ⟨2367933, by rfl⟩ : syracuseStep 6314489 = 4735867) B4735867
theorem B7994153 : Blo 1869636 7994153 := bstep (se 2 (by rfl) ⟨2997807, by rfl⟩ : syracuseStep 7994153 = 5995615) B5995615
theorem B7101341 : Blo 1869636 7101341 := bstep (se 3 (by rfl) ⟨1331501, by rfl⟩ : syracuseStep 7101341 = 2663003) B2663003
theorem B12802981 : Blo 1869636 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B4209785 : Blo 1869636 4209785 := bstep (se 2 (by rfl) ⟨1578669, by rfl⟩ : syracuseStep 4209785 = 3157339) B3157339
theorem B3792097 : Blo 1869636 3792097 := bstep (se 2 (by rfl) ⟨1422036, by rfl⟩ : syracuseStep 3792097 = 2844073) B2844073
theorem B4209947 : Blo 1869636 4209947 := bstep (se 1 (by rfl) ⟨3157460, by rfl⟩ : syracuseStep 4209947 = 6314921) B6314921
theorem B4210145 : Blo 1869636 4210145 := bstep (se 2 (by rfl) ⟨1578804, by rfl⟩ : syracuseStep 4210145 = 3157609) B3157609
theorem B20225513 : Blo 1869636 20225513 := bstep (se 2 (by rfl) ⟨7584567, by rfl⟩ : syracuseStep 20225513 = 15169135) B15169135
theorem B2997737 : Blo 1869636 2997737 := bstep (se 2 (by rfl) ⟨1124151, by rfl⟩ : syracuseStep 2997737 = 2248303) B2248303
theorem B7102025 : Blo 1869636 7102025 := bstep (se 2 (by rfl) ⟨2663259, by rfl⟩ : syracuseStep 7102025 = 5326519) B5326519
theorem B10804873 : Blo 1869636 10804873 := bstep (se 2 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 10804873 = 8103655) B8103655
theorem B7102313 : Blo 1869636 7102313 := bstep (se 2 (by rfl) ⟨2663367, by rfl⟩ : syracuseStep 7102313 = 5326735) B5326735
theorem B4210847 : Blo 1869636 4210847 := bstep (se 1 (by rfl) ⟨3158135, by rfl⟩ : syracuseStep 4210847 = 6316271) B6316271
theorem B20218031 : Blo 1869636 20218031 := bstep (se 1 (by rfl) ⟨15163523, by rfl⟩ : syracuseStep 20218031 = 30327047) B30327047
theorem B17973737 : Blo 1869636 17973737 := bstep (se 2 (by rfl) ⟨6740151, by rfl⟩ : syracuseStep 17973737 = 13480303) B13480303
theorem B9470519 : Blo 1869636 9470519 := bstep (se 1 (by rfl) ⟨7102889, by rfl⟩ : syracuseStep 9470519 = 14205779) B14205779
theorem B21897839 : Blo 1869636 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B19195193 : Blo 1869636 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B28812631 : Blo 1869636 28812631 := bstep (se 1 (by rfl) ⟨21609473, by rfl⟩ : syracuseStep 28812631 = 43218947) B43218947
theorem B15983963 : Blo 1869636 15983963 := bstep (se 1 (by rfl) ⟨11987972, by rfl⟩ : syracuseStep 15983963 = 23975945) B23975945
theorem B10659347 : Blo 1869636 10659347 := bstep (se 1 (by rfl) ⟨7994510, by rfl⟩ : syracuseStep 10659347 = 15989021) B15989021
theorem B5056129 : Blo 1869636 5056129 := bstep (se 2 (by rfl) ⟨1896048, by rfl⟩ : syracuseStep 5056129 = 3792097) B3792097
theorem B3155611 : Blo 1869636 3155611 := bstep (se 1 (by rfl) ⟨2366708, by rfl⟩ : syracuseStep 3155611 = 4733417) B4733417
theorem B9471815 : Blo 1869636 9471815 := bstep (se 1 (by rfl) ⟨7103861, by rfl⟩ : syracuseStep 9471815 = 14207723) B14207723
theorem B1869695 : Blo 1869636 1869695 := bstep (se 1 (by rfl) ⟨1402271, by rfl⟩ : syracuseStep 1869695 = 2804543) B2804543
theorem B4737001 : Blo 1869636 4737001 := bstep (se 2 (by rfl) ⟨1776375, by rfl⟩ : syracuseStep 4737001 = 3552751) B3552751
theorem B1869915 : Blo 1869636 1869915 := bstep (se 1 (by rfl) ⟨1402436, by rfl⟩ : syracuseStep 1869915 = 2804873) B2804873
theorem B1869951 : Blo 1869636 1869951 := bstep (se 1 (by rfl) ⟨1402463, by rfl⟩ : syracuseStep 1869951 = 2804927) B2804927
theorem B11987153 : Blo 1869636 11987153 := bstep (se 2 (by rfl) ⟨4495182, by rfl⟩ : syracuseStep 11987153 = 8990365) B8990365
theorem B1870143 : Blo 1869636 1870143 := bstep (se 1 (by rfl) ⟨1402607, by rfl⟩ : syracuseStep 1870143 = 2805215) B2805215
theorem B1870183 : Blo 1869636 1870183 := bstep (se 1 (by rfl) ⟨1402637, by rfl⟩ : syracuseStep 1870183 = 2805275) B2805275
theorem B15166025 : Blo 1869636 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B1870463 : Blo 1869636 1870463 := bstep (se 1 (by rfl) ⟨1402847, by rfl⟩ : syracuseStep 1870463 = 2805695) B2805695
theorem B21310127 : Blo 1869636 21310127 := bstep (se 1 (by rfl) ⟨15982595, by rfl⟩ : syracuseStep 21310127 = 31965191) B31965191
theorem B3157103 : Blo 1869636 3157103 := bstep (se 1 (by rfl) ⟨2367827, by rfl⟩ : syracuseStep 3157103 = 4735655) B4735655
theorem B47934665 : Blo 1869636 47934665 := bstep (se 2 (by rfl) ⟨17975499, by rfl⟩ : syracuseStep 47934665 = 35950999) B35950999
theorem B6311195 : Blo 1869636 6311195 := bstep (se 1 (by rfl) ⟨4733396, by rfl⟩ : syracuseStep 6311195 = 9466793) B9466793
theorem B2805095 : Blo 1869636 2805095 := bstep (se 1 (by rfl) ⟨2103821, by rfl⟩ : syracuseStep 2805095 = 4207643) B4207643
theorem B4050719 : Blo 1869636 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B2805671 : Blo 1869636 2805671 := bstep (se 1 (by rfl) ⟨2104253, by rfl⟩ : syracuseStep 2805671 = 4208507) B4208507
theorem B10112951 : Blo 1869636 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B34131941 : Blo 1869636 34131941 := bstep (se 4 (by rfl) ⟨3199869, by rfl⟩ : syracuseStep 34131941 = 6399739) B6399739
theorem B10948711 : Blo 1869636 10948711 := bstep (se 1 (by rfl) ⟨8211533, by rfl⟩ : syracuseStep 10948711 = 16423067) B16423067
theorem B4206905 : Blo 1869636 4206905 := bstep (se 2 (by rfl) ⟨1577589, by rfl⟩ : syracuseStep 4206905 = 3155179) B3155179
theorem B16200101 : Blo 1869636 16200101 := bstep (se 4 (by rfl) ⟨1518759, by rfl⟩ : syracuseStep 16200101 = 3037519) B3037519
theorem B4207103 : Blo 1869636 4207103 := bstep (se 1 (by rfl) ⟨3155327, by rfl⟩ : syracuseStep 4207103 = 6310655) B6310655
theorem B5329435 : Blo 1869636 5329435 := bstep (se 1 (by rfl) ⟨3997076, by rfl⟩ : syracuseStep 5329435 = 7994153) B7994153
theorem B23065195 : Blo 1869636 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B22483657 : Blo 1869636 22483657 := bstep (se 2 (by rfl) ⟨8431371, by rfl⟩ : syracuseStep 22483657 = 16862743) B16862743
theorem B2806523 : Blo 1869636 2806523 := bstep (se 1 (by rfl) ⟨2104892, by rfl⟩ : syracuseStep 2806523 = 4209785) B4209785
theorem B13488893 : Blo 1869636 13488893 := bstep (se 3 (by rfl) ⟨2529167, by rfl⟩ : syracuseStep 13488893 = 5058335) B5058335
theorem B14406497 : Blo 1869636 14406497 := bstep (se 2 (by rfl) ⟨5402436, by rfl⟩ : syracuseStep 14406497 = 10804873) B10804873
theorem B2806631 : Blo 1869636 2806631 := bstep (se 1 (by rfl) ⟨2104973, by rfl⟩ : syracuseStep 2806631 = 4209947) B4209947
theorem B2806763 : Blo 1869636 2806763 := bstep (se 1 (by rfl) ⟨2105072, by rfl⟩ : syracuseStep 2806763 = 4210145) B4210145
theorem B10654973 : Blo 1869636 10654973 := bstep (se 3 (by rfl) ⟨1997807, by rfl⟩ : syracuseStep 10654973 = 3995615) B3995615
theorem B4494665 : Blo 1869636 4494665 := bstep (se 2 (by rfl) ⟨1685499, by rfl⟩ : syracuseStep 4494665 = 3370999) B3370999
theorem B4208111 : Blo 1869636 4208111 := bstep (se 1 (by rfl) ⟨3156083, by rfl⟩ : syracuseStep 4208111 = 6312167) B6312167
theorem B14210639 : Blo 1869636 14210639 := bstep (se 1 (by rfl) ⟨10657979, by rfl⟩ : syracuseStep 14210639 = 21315959) B21315959
theorem B230291099 : Blo 1869636 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B4732607 : Blo 1869636 4732607 := bstep (se 1 (by rfl) ⟨3549455, by rfl⟩ : syracuseStep 4732607 = 7098911) B7098911
theorem B3553055 : Blo 1869636 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B138434845 : Blo 1869636 138434845 := bstep (se 3 (by rfl) ⟨25956533, by rfl⟩ : syracuseStep 138434845 = 51913067) B51913067
theorem B17070641 : Blo 1869636 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B8985275 : Blo 1869636 8985275 := bstep (se 1 (by rfl) ⟨6738956, by rfl⟩ : syracuseStep 8985275 = 13477913) B13477913
theorem B4496105 : Blo 1869636 4496105 := bstep (se 2 (by rfl) ⟨1686039, by rfl⟩ : syracuseStep 4496105 = 3372079) B3372079
theorem B6314813 : Blo 1869636 6314813 := bstep (se 3 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 6314813 = 2368055) B2368055
theorem B4209659 : Blo 1869636 4209659 := bstep (se 1 (by rfl) ⟨3157244, by rfl⟩ : syracuseStep 4209659 = 6314489) B6314489
theorem B4734227 : Blo 1869636 4734227 := bstep (se 1 (by rfl) ⟨3550670, by rfl⟩ : syracuseStep 4734227 = 7101341) B7101341
theorem B13483675 : Blo 1869636 13483675 := bstep (se 1 (by rfl) ⟨10112756, by rfl⟩ : syracuseStep 13483675 = 20225513) B20225513
theorem B2104987 : Blo 1869636 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B6315677 : Blo 1869636 6315677 := bstep (se 3 (by rfl) ⟨1184189, by rfl⟩ : syracuseStep 6315677 = 2368379) B2368379
theorem B1998491 : Blo 1869636 1998491 := bstep (se 1 (by rfl) ⟨1498868, by rfl⟩ : syracuseStep 1998491 = 2997737) B2997737
theorem B2105023 : Blo 1869636 2105023 := bstep (se 1 (by rfl) ⟨1578767, by rfl⟩ : syracuseStep 2105023 = 3157535) B3157535
theorem B4734683 : Blo 1869636 4734683 := bstep (se 1 (by rfl) ⟨3551012, by rfl⟩ : syracuseStep 4734683 = 7102025) B7102025
theorem B4734875 : Blo 1869636 4734875 := bstep (se 1 (by rfl) ⟨3551156, by rfl⟩ : syracuseStep 4734875 = 7102313) B7102313
theorem B17981423 : Blo 1869636 17981423 := bstep (se 1 (by rfl) ⟨13486067, by rfl⟩ : syracuseStep 17981423 = 26972135) B26972135
theorem B14598281 : Blo 1869636 14598281 := bstep (se 2 (by rfl) ⟨5474355, by rfl⟩ : syracuseStep 14598281 = 10948711) B10948711
theorem B14598559 : Blo 1869636 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B30753593 : Blo 1869636 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B7103315 : Blo 1869636 7103315 := bstep (se 1 (by rfl) ⟨5327486, by rfl⟩ : syracuseStep 7103315 = 10654973) B10654973
theorem B12796795 : Blo 1869636 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B153527399 : Blo 1869636 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B3155071 : Blo 1869636 3155071 := bstep (se 1 (by rfl) ⟨2366303, by rfl⟩ : syracuseStep 3155071 = 4732607) B4732607
theorem B2368703 : Blo 1869636 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B11380427 : Blo 1869636 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B10110683 : Blo 1869636 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B14206751 : Blo 1869636 14206751 := bstep (se 1 (by rfl) ⟨10655063, by rfl⟩ : syracuseStep 14206751 = 21310127) B21310127
theorem B5990183 : Blo 1869636 5990183 := bstep (se 1 (by rfl) ⟨4492637, by rfl⟩ : syracuseStep 5990183 = 8985275) B8985275
theorem B3156151 : Blo 1869636 3156151 := bstep (se 1 (by rfl) ⟨2367113, by rfl⟩ : syracuseStep 3156151 = 4734227) B4734227
theorem B1870063 : Blo 1869636 1870063 := bstep (se 1 (by rfl) ⟨1402547, by rfl⟩ : syracuseStep 1870063 = 2805095) B2805095
theorem B3156455 : Blo 1869636 3156455 := bstep (se 1 (by rfl) ⟨2367341, by rfl⟩ : syracuseStep 3156455 = 4734683) B4734683
theorem B3156583 : Blo 1869636 3156583 := bstep (se 1 (by rfl) ⟨2367437, by rfl⟩ : syracuseStep 3156583 = 4734875) B4734875
theorem B1870447 : Blo 1869636 1870447 := bstep (se 1 (by rfl) ⟨1402835, by rfl⟩ : syracuseStep 1870447 = 2805671) B2805671
theorem B11987615 : Blo 1869636 11987615 := bstep (se 1 (by rfl) ⟨8990711, by rfl⟩ : syracuseStep 11987615 = 17981423) B17981423
theorem B13478687 : Blo 1869636 13478687 := bstep (se 1 (by rfl) ⟨10109015, by rfl⟩ : syracuseStep 13478687 = 20218031) B20218031
theorem B2804603 : Blo 1869636 2804603 := bstep (se 1 (by rfl) ⟨2103452, by rfl⟩ : syracuseStep 2804603 = 4206905) B4206905
theorem B10800067 : Blo 1869636 10800067 := bstep (se 1 (by rfl) ⟨8100050, by rfl⟩ : syracuseStep 10800067 = 16200101) B16200101
theorem B2804735 : Blo 1869636 2804735 := bstep (se 1 (by rfl) ⟨2103551, by rfl⟩ : syracuseStep 2804735 = 4207103) B4207103
theorem B1871015 : Blo 1869636 1871015 := bstep (se 1 (by rfl) ⟨1403261, by rfl⟩ : syracuseStep 1871015 = 2806523) B2806523
theorem B9604331 : Blo 1869636 9604331 := bstep (se 1 (by rfl) ⟨7203248, by rfl⟩ : syracuseStep 9604331 = 14406497) B14406497
theorem B1871087 : Blo 1869636 1871087 := bstep (se 1 (by rfl) ⟨1403315, by rfl⟩ : syracuseStep 1871087 = 2806631) B2806631
theorem B1871175 : Blo 1869636 1871175 := bstep (se 1 (by rfl) ⟨1403381, by rfl⟩ : syracuseStep 1871175 = 2806763) B2806763
theorem B7105913 : Blo 1869636 7105913 := bstep (se 2 (by rfl) ⟨2664717, by rfl⟩ : syracuseStep 7105913 = 5329435) B5329435
theorem B29978209 : Blo 1869636 29978209 := bstep (se 2 (by rfl) ⟨11241828, by rfl⟩ : syracuseStep 29978209 = 22483657) B22483657
theorem B2805407 : Blo 1869636 2805407 := bstep (se 1 (by rfl) ⟨2104055, by rfl⟩ : syracuseStep 2805407 = 4208111) B4208111
theorem B7106231 : Blo 1869636 7106231 := bstep (se 1 (by rfl) ⟨5329673, by rfl⟩ : syracuseStep 7106231 = 10659347) B10659347
theorem B9473759 : Blo 1869636 9473759 := bstep (se 1 (by rfl) ⟨7105319, by rfl⟩ : syracuseStep 9473759 = 14210639) B14210639
theorem B7991435 : Blo 1869636 7991435 := bstep (se 1 (by rfl) ⟨5993576, by rfl⟩ : syracuseStep 7991435 = 11987153) B11987153
theorem B5329309 : Blo 1869636 5329309 := bstep (se 3 (by rfl) ⟨999245, by rfl⟩ : syracuseStep 5329309 = 1998491) B1998491
theorem B38416841 : Blo 1869636 38416841 := bstep (se 2 (by rfl) ⟨14406315, by rfl⟩ : syracuseStep 38416841 = 28812631) B28812631
theorem B11989613 : Blo 1869636 11989613 := bstep (se 3 (by rfl) ⟨2248052, by rfl⟩ : syracuseStep 11989613 = 4496105) B4496105
theorem B2806439 : Blo 1869636 2806439 := bstep (se 1 (by rfl) ⟨2104829, by rfl⟩ : syracuseStep 2806439 = 4209659) B4209659
theorem B4207463 : Blo 1869636 4207463 := bstep (se 1 (by rfl) ⟨3155597, by rfl⟩ : syracuseStep 4207463 = 6311195) B6311195
theorem B4207481 : Blo 1869636 4207481 := bstep (se 2 (by rfl) ⟨1577805, by rfl⟩ : syracuseStep 4207481 = 3155611) B3155611
theorem B17978233 : Blo 1869636 17978233 := bstep (se 2 (by rfl) ⟨6741837, by rfl⟩ : syracuseStep 17978233 = 13483675) B13483675
theorem B2806649 : Blo 1869636 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B2806697 : Blo 1869636 2806697 := bstep (se 2 (by rfl) ⟨1052511, by rfl⟩ : syracuseStep 2806697 = 2105023) B2105023
theorem B2700479 : Blo 1869636 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B22754627 : Blo 1869636 22754627 := bstep (se 1 (by rfl) ⟨17065970, by rfl⟩ : syracuseStep 22754627 = 34131941) B34131941
theorem B2807231 : Blo 1869636 2807231 := bstep (se 1 (by rfl) ⟨2105423, by rfl⟩ : syracuseStep 2807231 = 4210847) B4210847
theorem B11982491 : Blo 1869636 11982491 := bstep (se 1 (by rfl) ⟨8986868, by rfl⟩ : syracuseStep 11982491 = 17973737) B17973737
theorem B6313679 : Blo 1869636 6313679 := bstep (se 1 (by rfl) ⟨4735259, by rfl⟩ : syracuseStep 6313679 = 9470519) B9470519
theorem B184579793 : Blo 1869636 184579793 := bstep (se 2 (by rfl) ⟨69217422, by rfl⟩ : syracuseStep 184579793 = 138434845) B138434845
theorem B8992595 : Blo 1869636 8992595 := bstep (se 1 (by rfl) ⟨6744446, by rfl⟩ : syracuseStep 8992595 = 13488893) B13488893
theorem B2996443 : Blo 1869636 2996443 := bstep (se 1 (by rfl) ⟨2247332, by rfl⟩ : syracuseStep 2996443 = 4494665) B4494665
theorem B10655975 : Blo 1869636 10655975 := bstep (se 1 (by rfl) ⟨7991981, by rfl⟩ : syracuseStep 10655975 = 15983963) B15983963
theorem B6314543 : Blo 1869636 6314543 := bstep (se 1 (by rfl) ⟨4735907, by rfl⟩ : syracuseStep 6314543 = 9471815) B9471815
theorem B4209875 : Blo 1869636 4209875 := bstep (se 1 (by rfl) ⟨3157406, by rfl⟩ : syracuseStep 4209875 = 6314813) B6314813
theorem B2104735 : Blo 1869636 2104735 := bstep (se 1 (by rfl) ⟨1578551, by rfl⟩ : syracuseStep 2104735 = 3157103) B3157103
theorem B31956443 : Blo 1869636 31956443 := bstep (se 1 (by rfl) ⟨23967332, by rfl⟩ : syracuseStep 31956443 = 47934665) B47934665
theorem B6741505 : Blo 1869636 6741505 := bstep (se 2 (by rfl) ⟨2528064, by rfl⟩ : syracuseStep 6741505 = 5056129) B5056129
theorem B4210451 : Blo 1869636 4210451 := bstep (se 1 (by rfl) ⟨3157838, by rfl⟩ : syracuseStep 4210451 = 6315677) B6315677
theorem B6741967 : Blo 1869636 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B6316001 : Blo 1869636 6316001 := bstep (se 2 (by rfl) ⟨2368500, by rfl⟩ : syracuseStep 6316001 = 4737001) B4737001
theorem B9732187 : Blo 1869636 9732187 := bstep (se 1 (by rfl) ⟨7299140, by rfl⟩ : syracuseStep 9732187 = 14598281) B14598281
theorem B7201277 : Blo 1869636 7201277 := bstep (se 3 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 7201277 = 2700479) B2700479
theorem B6316541 : Blo 1869636 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B19464745 : Blo 1869636 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B4735543 : Blo 1869636 4735543 := bstep (se 1 (by rfl) ⟨3551657, by rfl⟩ : syracuseStep 4735543 = 7103315) B7103315
theorem B102351599 : Blo 1869636 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B7988327 : Blo 1869636 7988327 := bstep (se 1 (by rfl) ⟨5991245, by rfl⟩ : syracuseStep 7988327 = 11982491) B11982491
theorem B7586951 : Blo 1869636 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B123053195 : Blo 1869636 123053195 := bstep (se 1 (by rfl) ⟨92289896, by rfl⟩ : syracuseStep 123053195 = 184579793) B184579793
theorem B23970977 : Blo 1869636 23970977 := bstep (se 2 (by rfl) ⟨8989116, by rfl⟩ : syracuseStep 23970977 = 17978233) B17978233
theorem B9471167 : Blo 1869636 9471167 := bstep (se 1 (by rfl) ⟨7103375, by rfl⟩ : syracuseStep 9471167 = 14206751) B14206751
theorem B7103983 : Blo 1869636 7103983 := bstep (se 1 (by rfl) ⟨5327987, by rfl⟩ : syracuseStep 7103983 = 10655975) B10655975
theorem B1869735 : Blo 1869636 1869735 := bstep (se 1 (by rfl) ⟨1402301, by rfl⟩ : syracuseStep 1869735 = 2804603) B2804603
theorem B68249573 : Blo 1869636 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B1869823 : Blo 1869636 1869823 := bstep (se 1 (by rfl) ⟨1402367, by rfl⟩ : syracuseStep 1869823 = 2804735) B2804735
theorem B8988673 : Blo 1869636 8988673 := bstep (se 2 (by rfl) ⟨3370752, by rfl⟩ : syracuseStep 8988673 = 6741505) B6741505
theorem B39970945 : Blo 1869636 39970945 := bstep (se 2 (by rfl) ⟨14989104, by rfl⟩ : syracuseStep 39970945 = 29978209) B29978209
theorem B4737275 : Blo 1869636 4737275 := bstep (se 1 (by rfl) ⟨3552956, by rfl⟩ : syracuseStep 4737275 = 7105913) B7105913
theorem B1870271 : Blo 1869636 1870271 := bstep (se 1 (by rfl) ⟨1402703, by rfl⟩ : syracuseStep 1870271 = 2805407) B2805407
theorem B4737487 : Blo 1869636 4737487 := bstep (se 1 (by rfl) ⟨3553115, by rfl⟩ : syracuseStep 4737487 = 7106231) B7106231
theorem B8989289 : Blo 1869636 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B5327623 : Blo 1869636 5327623 := bstep (se 1 (by rfl) ⟨3995717, by rfl⟩ : syracuseStep 5327623 = 7991435) B7991435
theorem B25611227 : Blo 1869636 25611227 := bstep (se 1 (by rfl) ⟨19208420, by rfl⟩ : syracuseStep 25611227 = 38416841) B38416841
theorem B1870959 : Blo 1869636 1870959 := bstep (se 1 (by rfl) ⟨1403219, by rfl⟩ : syracuseStep 1870959 = 2806439) B2806439
theorem B7105745 : Blo 1869636 7105745 := bstep (se 2 (by rfl) ⟨2664654, by rfl⟩ : syracuseStep 7105745 = 5329309) B5329309
theorem B2804975 : Blo 1869636 2804975 := bstep (se 1 (by rfl) ⟨2103731, by rfl⟩ : syracuseStep 2804975 = 4207463) B4207463
theorem B2804987 : Blo 1869636 2804987 := bstep (se 1 (by rfl) ⟨2103740, by rfl⟩ : syracuseStep 2804987 = 4207481) B4207481
theorem B1871099 : Blo 1869636 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B1871131 : Blo 1869636 1871131 := bstep (se 1 (by rfl) ⟨1403348, by rfl⟩ : syracuseStep 1871131 = 2806697) B2806697
theorem B1871487 : Blo 1869636 1871487 := bstep (se 1 (by rfl) ⟨1403615, by rfl⟩ : syracuseStep 1871487 = 2807231) B2807231
theorem B3993455 : Blo 1869636 3993455 := bstep (se 1 (by rfl) ⟨2995091, by rfl⟩ : syracuseStep 3993455 = 5990183) B5990183
theorem B4206761 : Blo 1869636 4206761 := bstep (se 2 (by rfl) ⟨1577535, by rfl⟩ : syracuseStep 4206761 = 3155071) B3155071
theorem B7991743 : Blo 1869636 7991743 := bstep (se 1 (by rfl) ⟨5993807, by rfl⟩ : syracuseStep 7991743 = 11987615) B11987615
theorem B2806313 : Blo 1869636 2806313 := bstep (se 2 (by rfl) ⟨1052367, by rfl⟩ : syracuseStep 2806313 = 2104735) B2104735
theorem B2806583 : Blo 1869636 2806583 := bstep (se 1 (by rfl) ⟨2104937, by rfl⟩ : syracuseStep 2806583 = 4209875) B4209875
theorem B6402887 : Blo 1869636 6402887 := bstep (se 1 (by rfl) ⟨4802165, by rfl⟩ : syracuseStep 6402887 = 9604331) B9604331
theorem B21304295 : Blo 1869636 21304295 := bstep (se 1 (by rfl) ⟨15978221, by rfl⟩ : syracuseStep 21304295 = 31956443) B31956443
theorem B2806967 : Blo 1869636 2806967 := bstep (se 1 (by rfl) ⟨2105225, by rfl⟩ : syracuseStep 2806967 = 4210451) B4210451
theorem B4208201 : Blo 1869636 4208201 := bstep (se 2 (by rfl) ⟨1578075, by rfl⟩ : syracuseStep 4208201 = 3156151) B3156151
theorem B3995257 : Blo 1869636 3995257 := bstep (se 2 (by rfl) ⟨1498221, by rfl⟩ : syracuseStep 3995257 = 2996443) B2996443
theorem B7993075 : Blo 1869636 7993075 := bstep (se 1 (by rfl) ⟨5994806, by rfl⟩ : syracuseStep 7993075 = 11989613) B11989613
theorem B20502395 : Blo 1869636 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B4208777 : Blo 1869636 4208777 := bstep (se 2 (by rfl) ⟨1578291, by rfl⟩ : syracuseStep 4208777 = 3156583) B3156583
theorem B15169751 : Blo 1869636 15169751 := bstep (se 1 (by rfl) ⟨11377313, by rfl⟩ : syracuseStep 15169751 = 22754627) B22754627
theorem B4209119 : Blo 1869636 4209119 := bstep (se 1 (by rfl) ⟨3156839, by rfl⟩ : syracuseStep 4209119 = 6313679) B6313679
theorem B6740455 : Blo 1869636 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B5995063 : Blo 1869636 5995063 := bstep (se 1 (by rfl) ⟨4496297, by rfl⟩ : syracuseStep 5995063 = 8992595) B8992595
theorem B14400089 : Blo 1869636 14400089 := bstep (se 2 (by rfl) ⟨5400033, by rfl⟩ : syracuseStep 14400089 = 10800067) B10800067
theorem B2104303 : Blo 1869636 2104303 := bstep (se 1 (by rfl) ⟨1578227, by rfl⟩ : syracuseStep 2104303 = 3156455) B3156455
theorem B4209695 : Blo 1869636 4209695 := bstep (se 1 (by rfl) ⟨3157271, by rfl⟩ : syracuseStep 4209695 = 6314543) B6314543
theorem B8985791 : Blo 1869636 8985791 := bstep (se 1 (by rfl) ⟨6739343, by rfl⟩ : syracuseStep 8985791 = 13478687) B13478687
theorem B6315839 : Blo 1869636 6315839 := bstep (se 1 (by rfl) ⟨4736879, by rfl⟩ : syracuseStep 6315839 = 9473759) B9473759
theorem B4210667 : Blo 1869636 4210667 := bstep (se 1 (by rfl) ⟨3158000, by rfl⟩ : syracuseStep 4210667 = 6316001) B6316001
theorem B11984897 : Blo 1869636 11984897 := bstep (se 2 (by rfl) ⟨4494336, by rfl⟩ : syracuseStep 11984897 = 8988673) B8988673
theorem B12976249 : Blo 1869636 12976249 := bstep (se 2 (by rfl) ⟨4866093, by rfl⟩ : syracuseStep 12976249 = 9732187) B9732187
theorem B4800851 : Blo 1869636 4800851 := bstep (se 1 (by rfl) ⟨3600638, by rfl⟩ : syracuseStep 4800851 = 7201277) B7201277
theorem B4211027 : Blo 1869636 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B4268591 : Blo 1869636 4268591 := bstep (se 1 (by rfl) ⟨3201443, by rfl⟩ : syracuseStep 4268591 = 6402887) B6402887
theorem B6316649 : Blo 1869636 6316649 := bstep (se 2 (by rfl) ⟨2368743, by rfl⟩ : syracuseStep 6316649 = 4737487) B4737487
theorem B8987273 : Blo 1869636 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B25952993 : Blo 1869636 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B5325551 : Blo 1869636 5325551 := bstep (se 1 (by rfl) ⟨3994163, by rfl⟩ : syracuseStep 5325551 = 7988327) B7988327
theorem B82035463 : Blo 1869636 82035463 := bstep (se 1 (by rfl) ⟨61526597, by rfl⟩ : syracuseStep 82035463 = 123053195) B123053195
theorem B7103497 : Blo 1869636 7103497 := bstep (se 2 (by rfl) ⟨2663811, by rfl⟩ : syracuseStep 7103497 = 5327623) B5327623
theorem B45499715 : Blo 1869636 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B17074151 : Blo 1869636 17074151 := bstep (se 1 (by rfl) ⟨12805613, by rfl⟩ : syracuseStep 17074151 = 25611227) B25611227
theorem B9471977 : Blo 1869636 9471977 := bstep (se 2 (by rfl) ⟨3551991, by rfl⟩ : syracuseStep 9471977 = 7103983) B7103983
theorem B5990527 : Blo 1869636 5990527 := bstep (se 1 (by rfl) ⟨4492895, by rfl⟩ : syracuseStep 5990527 = 8985791) B8985791
theorem B4737163 : Blo 1869636 4737163 := bstep (se 1 (by rfl) ⟨3552872, by rfl⟩ : syracuseStep 4737163 = 7105745) B7105745
theorem B1869983 : Blo 1869636 1869983 := bstep (se 1 (by rfl) ⟨1402487, by rfl⟩ : syracuseStep 1869983 = 2804975) B2804975
theorem B5327009 : Blo 1869636 5327009 := bstep (se 2 (by rfl) ⟨1997628, by rfl⟩ : syracuseStep 5327009 = 3995257) B3995257
theorem B1869991 : Blo 1869636 1869991 := bstep (se 1 (by rfl) ⟨1402493, by rfl⟩ : syracuseStep 1869991 = 2804987) B2804987
theorem B2804507 : Blo 1869636 2804507 := bstep (se 1 (by rfl) ⟨2103380, by rfl⟩ : syracuseStep 2804507 = 4206761) B4206761
theorem B1870875 : Blo 1869636 1870875 := bstep (se 1 (by rfl) ⟨1403156, by rfl⟩ : syracuseStep 1870875 = 2806313) B2806313
theorem B68234399 : Blo 1869636 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B1871055 : Blo 1869636 1871055 := bstep (se 1 (by rfl) ⟨1403291, by rfl⟩ : syracuseStep 1871055 = 2806583) B2806583
theorem B1871311 : Blo 1869636 1871311 := bstep (se 1 (by rfl) ⟨1403483, by rfl⟩ : syracuseStep 1871311 = 2806967) B2806967
theorem B2805467 : Blo 1869636 2805467 := bstep (se 1 (by rfl) ⟨2104100, by rfl⟩ : syracuseStep 2805467 = 4208201) B4208201
theorem B13668263 : Blo 1869636 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B2805737 : Blo 1869636 2805737 := bstep (se 2 (by rfl) ⟨1052151, by rfl⟩ : syracuseStep 2805737 = 2104303) B2104303
theorem B2805851 : Blo 1869636 2805851 := bstep (se 1 (by rfl) ⟨2104388, by rfl⟩ : syracuseStep 2805851 = 4208777) B4208777
theorem B10113167 : Blo 1869636 10113167 := bstep (se 1 (by rfl) ⟨7584875, by rfl⟩ : syracuseStep 10113167 = 15169751) B15169751
theorem B3158183 : Blo 1869636 3158183 := bstep (se 1 (by rfl) ⟨2368637, by rfl⟩ : syracuseStep 3158183 = 4737275) B4737275
theorem B2806079 : Blo 1869636 2806079 := bstep (se 1 (by rfl) ⟨2104559, by rfl⟩ : syracuseStep 2806079 = 4209119) B4209119
theorem B5992859 : Blo 1869636 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B2806463 : Blo 1869636 2806463 := bstep (se 1 (by rfl) ⟨2104847, by rfl⟩ : syracuseStep 2806463 = 4209695) B4209695
theorem B2807111 : Blo 1869636 2807111 := bstep (se 1 (by rfl) ⟨2105333, by rfl⟩ : syracuseStep 2807111 = 4210667) B4210667
theorem B53294593 : Blo 1869636 53294593 := bstep (se 2 (by rfl) ⟨19985472, by rfl⟩ : syracuseStep 53294593 = 39970945) B39970945
theorem B20231869 : Blo 1869636 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B10655657 : Blo 1869636 10655657 := bstep (se 2 (by rfl) ⟨3995871, by rfl⟩ : syracuseStep 10655657 = 7991743) B7991743
theorem B14202863 : Blo 1869636 14202863 := bstep (se 1 (by rfl) ⟨10652147, by rfl⟩ : syracuseStep 14202863 = 21304295) B21304295
theorem B6314057 : Blo 1869636 6314057 := bstep (se 2 (by rfl) ⟨2367771, by rfl⟩ : syracuseStep 6314057 = 4735543) B4735543
theorem B7993417 : Blo 1869636 7993417 := bstep (se 2 (by rfl) ⟨2997531, by rfl⟩ : syracuseStep 7993417 = 5995063) B5995063
theorem B15980651 : Blo 1869636 15980651 := bstep (se 1 (by rfl) ⟨11985488, by rfl⟩ : syracuseStep 15980651 = 23970977) B23970977
theorem B6314111 : Blo 1869636 6314111 := bstep (se 1 (by rfl) ⟨4735583, by rfl⟩ : syracuseStep 6314111 = 9471167) B9471167
theorem B9600059 : Blo 1869636 9600059 := bstep (se 1 (by rfl) ⟨7200044, by rfl⟩ : syracuseStep 9600059 = 14400089) B14400089
theorem B10657433 : Blo 1869636 10657433 := bstep (se 2 (by rfl) ⟨3996537, by rfl⟩ : syracuseStep 10657433 = 7993075) B7993075
theorem B4210559 : Blo 1869636 4210559 := bstep (se 1 (by rfl) ⟨3157919, by rfl⟩ : syracuseStep 4210559 = 6315839) B6315839
theorem B2662303 : Blo 1869636 2662303 := bstep (se 1 (by rfl) ⟨1996727, by rfl⟩ : syracuseStep 2662303 = 3993455) B3993455
theorem B6742111 : Blo 1869636 6742111 := bstep (se 1 (by rfl) ⟨5056583, by rfl⟩ : syracuseStep 6742111 = 10113167) B10113167
theorem B10657889 : Blo 1869636 10657889 := bstep (se 2 (by rfl) ⟨3996708, by rfl⟩ : syracuseStep 10657889 = 7993417) B7993417
theorem B2105455 : Blo 1869636 2105455 := bstep (se 1 (by rfl) ⟨1579091, by rfl⟩ : syracuseStep 2105455 = 3158183) B3158183
theorem B25600157 : Blo 1869636 25600157 := bstep (se 3 (by rfl) ⟨4800029, by rfl⟩ : syracuseStep 25600157 = 9600059) B9600059
theorem B17301665 : Blo 1869636 17301665 := bstep (se 2 (by rfl) ⟨6488124, by rfl⟩ : syracuseStep 17301665 = 12976249) B12976249
theorem B7987369 : Blo 1869636 7987369 := bstep (se 2 (by rfl) ⟨2995263, by rfl⟩ : syracuseStep 7987369 = 5990527) B5990527
theorem B6316217 : Blo 1869636 6316217 := bstep (se 2 (by rfl) ⟨2368581, by rfl⟩ : syracuseStep 6316217 = 4737163) B4737163
theorem B4211099 : Blo 1869636 4211099 := bstep (se 1 (by rfl) ⟨3158324, by rfl⟩ : syracuseStep 4211099 = 6316649) B6316649
theorem B17301995 : Blo 1869636 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B109380617 : Blo 1869636 109380617 := bstep (se 2 (by rfl) ⟨41017731, by rfl⟩ : syracuseStep 109380617 = 82035463) B82035463
theorem B7103771 : Blo 1869636 7103771 := bstep (se 1 (by rfl) ⟨5327828, by rfl⟩ : syracuseStep 7103771 = 10655657) B10655657
theorem B9471329 : Blo 1869636 9471329 := bstep (se 2 (by rfl) ⟨3551748, by rfl⟩ : syracuseStep 9471329 = 7103497) B7103497
theorem B1869671 : Blo 1869636 1869671 := bstep (se 1 (by rfl) ⟨1402253, by rfl⟩ : syracuseStep 1869671 = 2804507) B2804507
theorem B71059457 : Blo 1869636 71059457 := bstep (se 2 (by rfl) ⟨26647296, by rfl⟩ : syracuseStep 71059457 = 53294593) B53294593
theorem B7104955 : Blo 1869636 7104955 := bstep (se 1 (by rfl) ⟨5328716, by rfl⟩ : syracuseStep 7104955 = 10657433) B10657433
theorem B1870311 : Blo 1869636 1870311 := bstep (se 1 (by rfl) ⟨1402733, by rfl⟩ : syracuseStep 1870311 = 2805467) B2805467
theorem B3549737 : Blo 1869636 3549737 := bstep (se 2 (by rfl) ⟨1331151, by rfl⟩ : syracuseStep 3549737 = 2662303) B2662303
theorem B9112175 : Blo 1869636 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B1870491 : Blo 1869636 1870491 := bstep (se 1 (by rfl) ⟨1402868, by rfl⟩ : syracuseStep 1870491 = 2805737) B2805737
theorem B7989931 : Blo 1869636 7989931 := bstep (se 1 (by rfl) ⟨5992448, by rfl⟩ : syracuseStep 7989931 = 11984897) B11984897
theorem B1870567 : Blo 1869636 1870567 := bstep (se 1 (by rfl) ⟨1402925, by rfl⟩ : syracuseStep 1870567 = 2805851) B2805851
theorem B1870719 : Blo 1869636 1870719 := bstep (se 1 (by rfl) ⟨1403039, by rfl⟩ : syracuseStep 1870719 = 2806079) B2806079
theorem B2845727 : Blo 1869636 2845727 := bstep (se 1 (by rfl) ⟨2134295, by rfl⟩ : syracuseStep 2845727 = 4268591) B4268591
theorem B5991515 : Blo 1869636 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B1870975 : Blo 1869636 1870975 := bstep (se 1 (by rfl) ⟨1403231, by rfl⟩ : syracuseStep 1870975 = 2806463) B2806463
theorem B3550367 : Blo 1869636 3550367 := bstep (se 1 (by rfl) ⟨2662775, by rfl⟩ : syracuseStep 3550367 = 5325551) B5325551
theorem B1871407 : Blo 1869636 1871407 := bstep (se 1 (by rfl) ⟨1403555, by rfl⟩ : syracuseStep 1871407 = 2807111) B2807111
theorem B11382767 : Blo 1869636 11382767 := bstep (se 1 (by rfl) ⟨8537075, by rfl⟩ : syracuseStep 11382767 = 17074151) B17074151
theorem B10653767 : Blo 1869636 10653767 := bstep (se 1 (by rfl) ⟨7990325, by rfl⟩ : syracuseStep 10653767 = 15980651) B15980651
theorem B3551339 : Blo 1869636 3551339 := bstep (se 1 (by rfl) ⟨2663504, by rfl⟩ : syracuseStep 3551339 = 5327009) B5327009
theorem B2807039 : Blo 1869636 2807039 := bstep (se 1 (by rfl) ⟨2105279, by rfl⟩ : syracuseStep 2807039 = 4210559) B4210559
theorem B3200567 : Blo 1869636 3200567 := bstep (se 1 (by rfl) ⟨2400425, by rfl⟩ : syracuseStep 3200567 = 4800851) B4800851
theorem B2807351 : Blo 1869636 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B3995239 : Blo 1869636 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B30333143 : Blo 1869636 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B6314651 : Blo 1869636 6314651 := bstep (se 1 (by rfl) ⟨4735988, by rfl⟩ : syracuseStep 6314651 = 9471977) B9471977
theorem B9468575 : Blo 1869636 9468575 := bstep (se 1 (by rfl) ⟨7101431, by rfl⟩ : syracuseStep 9468575 = 14202863) B14202863
theorem B4209371 : Blo 1869636 4209371 := bstep (se 1 (by rfl) ⟨3157028, by rfl⟩ : syracuseStep 4209371 = 6314057) B6314057
theorem B4209407 : Blo 1869636 4209407 := bstep (se 1 (by rfl) ⟨3157055, by rfl⟩ : syracuseStep 4209407 = 6314111) B6314111
theorem B45489599 : Blo 1869636 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B26975825 : Blo 1869636 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B7102511 : Blo 1869636 7102511 := bstep (se 1 (by rfl) ⟨5326883, by rfl⟩ : syracuseStep 7102511 = 10653767) B10653767
theorem B2367559 : Blo 1869636 2367559 := bstep (se 1 (by rfl) ⟨1775669, by rfl⟩ : syracuseStep 2367559 = 3551339) B3551339
theorem B11534443 : Blo 1869636 11534443 := bstep (se 1 (by rfl) ⟨8650832, by rfl⟩ : syracuseStep 11534443 = 17301665) B17301665
theorem B4210811 : Blo 1869636 4210811 := bstep (se 1 (by rfl) ⟨3158108, by rfl⟩ : syracuseStep 4210811 = 6316217) B6316217
theorem B10649825 : Blo 1869636 10649825 := bstep (se 2 (by rfl) ⟨3993684, by rfl⟩ : syracuseStep 10649825 = 7987369) B7987369
theorem B11534663 : Blo 1869636 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B4735847 : Blo 1869636 4735847 := bstep (se 1 (by rfl) ⟨3551885, by rfl⟩ : syracuseStep 4735847 = 7103771) B7103771
theorem B5326985 : Blo 1869636 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B17983883 : Blo 1869636 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B7588511 : Blo 1869636 7588511 := bstep (se 1 (by rfl) ⟨5691383, by rfl⟩ : syracuseStep 7588511 = 11382767) B11382767
theorem B189491885 : Blo 1869636 189491885 := bstep (se 3 (by rfl) ⟨35529728, by rfl⟩ : syracuseStep 189491885 = 71059457) B71059457
theorem B7105259 : Blo 1869636 7105259 := bstep (se 1 (by rfl) ⟨5328944, by rfl⟩ : syracuseStep 7105259 = 10657889) B10657889
theorem B17066771 : Blo 1869636 17066771 := bstep (se 1 (by rfl) ⟨12800078, by rfl⟩ : syracuseStep 17066771 = 25600157) B25600157
theorem B8989481 : Blo 1869636 8989481 := bstep (se 2 (by rfl) ⟨3371055, by rfl⟩ : syracuseStep 8989481 = 6742111) B6742111
theorem B9473273 : Blo 1869636 9473273 := bstep (se 2 (by rfl) ⟨3552477, by rfl⟩ : syracuseStep 9473273 = 7104955) B7104955
theorem B72920411 : Blo 1869636 72920411 := bstep (se 1 (by rfl) ⟨54690308, by rfl⟩ : syracuseStep 72920411 = 109380617) B109380617
theorem B1871359 : Blo 1869636 1871359 := bstep (se 1 (by rfl) ⟨1403519, by rfl⟩ : syracuseStep 1871359 = 2807039) B2807039
theorem B10653241 : Blo 1869636 10653241 := bstep (se 2 (by rfl) ⟨3994965, by rfl⟩ : syracuseStep 10653241 = 7989931) B7989931
theorem B1871567 : Blo 1869636 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B20222095 : Blo 1869636 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B6074783 : Blo 1869636 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B6312383 : Blo 1869636 6312383 := bstep (se 1 (by rfl) ⟨4734287, by rfl⟩ : syracuseStep 6312383 = 9468575) B9468575
theorem B2806247 : Blo 1869636 2806247 := bstep (se 1 (by rfl) ⟨2104685, by rfl⟩ : syracuseStep 2806247 = 4209371) B4209371
theorem B2806271 : Blo 1869636 2806271 := bstep (se 1 (by rfl) ⟨2104703, by rfl⟩ : syracuseStep 2806271 = 4209407) B4209407
theorem B1897151 : Blo 1869636 1897151 := bstep (se 1 (by rfl) ⟨1422863, by rfl⟩ : syracuseStep 1897151 = 2845727) B2845727
theorem B3994343 : Blo 1869636 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B2807273 : Blo 1869636 2807273 := bstep (se 2 (by rfl) ⟨1052727, by rfl⟩ : syracuseStep 2807273 = 2105455) B2105455
theorem B2807399 : Blo 1869636 2807399 := bstep (se 1 (by rfl) ⟨2105549, by rfl⟩ : syracuseStep 2807399 = 4211099) B4211099
theorem B6314219 : Blo 1869636 6314219 := bstep (se 1 (by rfl) ⟨4735664, by rfl⟩ : syracuseStep 6314219 = 9471329) B9471329
theorem B8534845 : Blo 1869636 8534845 := bstep (se 3 (by rfl) ⟨1600283, by rfl⟩ : syracuseStep 8534845 = 3200567) B3200567
theorem B2366491 : Blo 1869636 2366491 := bstep (se 1 (by rfl) ⟨1774868, by rfl⟩ : syracuseStep 2366491 = 3549737) B3549737
theorem B4209767 : Blo 1869636 4209767 := bstep (se 1 (by rfl) ⟨3157325, by rfl⟩ : syracuseStep 4209767 = 6314651) B6314651
theorem B2366911 : Blo 1869636 2366911 := bstep (se 1 (by rfl) ⟨1775183, by rfl⟩ : syracuseStep 2366911 = 3550367) B3550367
theorem B30326399 : Blo 1869636 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B4735007 : Blo 1869636 4735007 := bstep (se 1 (by rfl) ⟨3551255, by rfl⟩ : syracuseStep 4735007 = 7102511) B7102511
theorem B14205293 : Blo 1869636 14205293 := bstep (se 3 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 14205293 = 5326985) B5326985
theorem B2662895 : Blo 1869636 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B11379793 : Blo 1869636 11379793 := bstep (se 2 (by rfl) ⟨4267422, by rfl⟩ : syracuseStep 11379793 = 8534845) B8534845
theorem B3155321 : Blo 1869636 3155321 := bstep (se 2 (by rfl) ⟨1183245, by rfl⟩ : syracuseStep 3155321 = 2366491) B2366491
theorem B4736839 : Blo 1869636 4736839 := bstep (se 1 (by rfl) ⟨3552629, by rfl⟩ : syracuseStep 4736839 = 7105259) B7105259
theorem B3155881 : Blo 1869636 3155881 := bstep (se 2 (by rfl) ⟨1183455, by rfl⟩ : syracuseStep 3155881 = 2366911) B2366911
theorem B20236277 : Blo 1869636 20236277 := bstep (se 5 (by rfl) ⟨948575, by rfl⟩ : syracuseStep 20236277 = 1897151) B1897151
theorem B23971949 : Blo 1869636 23971949 := bstep (se 3 (by rfl) ⟨4494740, by rfl⟩ : syracuseStep 23971949 = 8989481) B8989481
theorem B48613607 : Blo 1869636 48613607 := bstep (se 1 (by rfl) ⟨36460205, by rfl⟩ : syracuseStep 48613607 = 72920411) B72920411
theorem B3156745 : Blo 1869636 3156745 := bstep (se 2 (by rfl) ⟨1183779, by rfl⟩ : syracuseStep 3156745 = 2367559) B2367559
theorem B26962793 : Blo 1869636 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B4049855 : Blo 1869636 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B1870831 : Blo 1869636 1870831 := bstep (se 1 (by rfl) ⟨1403123, by rfl⟩ : syracuseStep 1870831 = 2806247) B2806247
theorem B1870847 : Blo 1869636 1870847 := bstep (se 1 (by rfl) ⟨1403135, by rfl⟩ : syracuseStep 1870847 = 2806271) B2806271
theorem B61517029 : Blo 1869636 61517029 := bstep (se 4 (by rfl) ⟨5767221, by rfl⟩ : syracuseStep 61517029 = 11534443) B11534443
theorem B3157231 : Blo 1869636 3157231 := bstep (se 1 (by rfl) ⟨2367923, by rfl⟩ : syracuseStep 3157231 = 4735847) B4735847
theorem B1871515 : Blo 1869636 1871515 := bstep (se 1 (by rfl) ⟨1403636, by rfl⟩ : syracuseStep 1871515 = 2807273) B2807273
theorem B1871599 : Blo 1869636 1871599 := bstep (se 1 (by rfl) ⟨1403699, by rfl⟩ : syracuseStep 1871599 = 2807399) B2807399
theorem B11989255 : Blo 1869636 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B5059007 : Blo 1869636 5059007 := bstep (se 1 (by rfl) ⟨3794255, by rfl⟩ : syracuseStep 5059007 = 7588511) B7588511
theorem B2806511 : Blo 1869636 2806511 := bstep (se 1 (by rfl) ⟨2104883, by rfl⟩ : syracuseStep 2806511 = 4209767) B4209767
theorem B2807207 : Blo 1869636 2807207 := bstep (se 1 (by rfl) ⟨2105405, by rfl⟩ : syracuseStep 2807207 = 4210811) B4210811
theorem B7099883 : Blo 1869636 7099883 := bstep (se 1 (by rfl) ⟨5324912, by rfl⟩ : syracuseStep 7099883 = 10649825) B10649825
theorem B7689775 : Blo 1869636 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B4208255 : Blo 1869636 4208255 := bstep (se 1 (by rfl) ⟨3156191, by rfl⟩ : syracuseStep 4208255 = 6312383) B6312383
theorem B4209479 : Blo 1869636 4209479 := bstep (se 1 (by rfl) ⟨3157109, by rfl⟩ : syracuseStep 4209479 = 6314219) B6314219
theorem B126327923 : Blo 1869636 126327923 := bstep (se 1 (by rfl) ⟨94745942, by rfl⟩ : syracuseStep 126327923 = 189491885) B189491885
theorem B11377847 : Blo 1869636 11377847 := bstep (se 1 (by rfl) ⟨8533385, by rfl⟩ : syracuseStep 11377847 = 17066771) B17066771
theorem B14204321 : Blo 1869636 14204321 := bstep (se 2 (by rfl) ⟨5326620, by rfl⟩ : syracuseStep 14204321 = 10653241) B10653241
theorem B6315515 : Blo 1869636 6315515 := bstep (se 1 (by rfl) ⟨4736636, by rfl⟩ : syracuseStep 6315515 = 9473273) B9473273
theorem B20217599 : Blo 1869636 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B9470195 : Blo 1869636 9470195 := bstep (se 1 (by rfl) ⟨7102646, by rfl⟩ : syracuseStep 9470195 = 14205293) B14205293
theorem B15173057 : Blo 1869636 15173057 := bstep (se 2 (by rfl) ⟨5689896, by rfl⟩ : syracuseStep 15173057 = 11379793) B11379793
theorem B32409071 : Blo 1869636 32409071 := bstep (se 1 (by rfl) ⟨24306803, by rfl⟩ : syracuseStep 32409071 = 48613607) B48613607
theorem B17975195 : Blo 1869636 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B13478399 : Blo 1869636 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B53963405 : Blo 1869636 53963405 := bstep (se 3 (by rfl) ⟨10118138, by rfl⟩ : syracuseStep 53963405 = 20236277) B20236277
theorem B3156671 : Blo 1869636 3156671 := bstep (se 1 (by rfl) ⟨2367503, by rfl⟩ : syracuseStep 3156671 = 4735007) B4735007
theorem B15985673 : Blo 1869636 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B1871007 : Blo 1869636 1871007 := bstep (se 1 (by rfl) ⟨1403255, by rfl⟩ : syracuseStep 1871007 = 2806511) B2806511
theorem B1871471 : Blo 1869636 1871471 := bstep (se 1 (by rfl) ⟨1403603, by rfl⟩ : syracuseStep 1871471 = 2807207) B2807207
theorem B2805503 : Blo 1869636 2805503 := bstep (se 1 (by rfl) ⟨2104127, by rfl⟩ : syracuseStep 2805503 = 4208255) B4208255
theorem B82022705 : Blo 1869636 82022705 := bstep (se 2 (by rfl) ⟨30758514, by rfl⟩ : syracuseStep 82022705 = 61517029) B61517029
theorem B2806319 : Blo 1869636 2806319 := bstep (se 1 (by rfl) ⟨2104739, by rfl⟩ : syracuseStep 2806319 = 4209479) B4209479
theorem B2699903 : Blo 1869636 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B10253033 : Blo 1869636 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B84218615 : Blo 1869636 84218615 := bstep (se 1 (by rfl) ⟨63163961, by rfl⟩ : syracuseStep 84218615 = 126327923) B126327923
theorem B4207841 : Blo 1869636 4207841 := bstep (se 2 (by rfl) ⟨1577940, by rfl⟩ : syracuseStep 4207841 = 3155881) B3155881
theorem B3372671 : Blo 1869636 3372671 := bstep (se 1 (by rfl) ⟨2529503, by rfl⟩ : syracuseStep 3372671 = 5059007) B5059007
theorem B30340925 : Blo 1869636 30340925 := bstep (se 3 (by rfl) ⟨5688923, by rfl⟩ : syracuseStep 30340925 = 11377847) B11377847
theorem B2103547 : Blo 1869636 2103547 := bstep (se 1 (by rfl) ⟨1577660, by rfl⟩ : syracuseStep 2103547 = 3155321) B3155321
theorem B4733255 : Blo 1869636 4733255 := bstep (se 1 (by rfl) ⟨3549941, by rfl⟩ : syracuseStep 4733255 = 7099883) B7099883
theorem B4208993 : Blo 1869636 4208993 := bstep (se 2 (by rfl) ⟨1578372, by rfl⟩ : syracuseStep 4208993 = 3156745) B3156745
theorem B7101053 : Blo 1869636 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B15981299 : Blo 1869636 15981299 := bstep (se 1 (by rfl) ⟨11985974, by rfl⟩ : syracuseStep 15981299 = 23971949) B23971949
theorem B4209641 : Blo 1869636 4209641 := bstep (se 2 (by rfl) ⟨1578615, by rfl⟩ : syracuseStep 4209641 = 3157231) B3157231
theorem B9469547 : Blo 1869636 9469547 := bstep (se 1 (by rfl) ⟨7102160, by rfl⟩ : syracuseStep 9469547 = 14204321) B14204321
theorem B4210343 : Blo 1869636 4210343 := bstep (se 1 (by rfl) ⟨3157757, by rfl⟩ : syracuseStep 4210343 = 6315515) B6315515
theorem B6315785 : Blo 1869636 6315785 := bstep (se 2 (by rfl) ⟨2368419, by rfl⟩ : syracuseStep 6315785 = 4736839) B4736839
theorem B54681803 : Blo 1869636 54681803 := bstep (se 1 (by rfl) ⟨41011352, by rfl⟩ : syracuseStep 54681803 = 82022705) B82022705
theorem B20227283 : Blo 1869636 20227283 := bstep (se 1 (by rfl) ⟨15170462, by rfl⟩ : syracuseStep 20227283 = 30340925) B30340925
theorem B3155503 : Blo 1869636 3155503 := bstep (se 1 (by rfl) ⟨2366627, by rfl⟩ : syracuseStep 3155503 = 4733255) B4733255
theorem B1870335 : Blo 1869636 1870335 := bstep (se 1 (by rfl) ⟨1402751, by rfl⟩ : syracuseStep 1870335 = 2805503) B2805503
theorem B2804729 : Blo 1869636 2804729 := bstep (se 2 (by rfl) ⟨1051773, by rfl⟩ : syracuseStep 2804729 = 2103547) B2103547
theorem B1870879 : Blo 1869636 1870879 := bstep (se 1 (by rfl) ⟨1403159, by rfl⟩ : syracuseStep 1870879 = 2806319) B2806319
theorem B6835355 : Blo 1869636 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B2805227 : Blo 1869636 2805227 := bstep (se 1 (by rfl) ⟨2103920, by rfl⟩ : syracuseStep 2805227 = 4207841) B4207841
theorem B21606047 : Blo 1869636 21606047 := bstep (se 1 (by rfl) ⟨16204535, by rfl⟩ : syracuseStep 21606047 = 32409071) B32409071
theorem B2248447 : Blo 1869636 2248447 := bstep (se 1 (by rfl) ⟨1686335, by rfl⟩ : syracuseStep 2248447 = 3372671) B3372671
theorem B2805995 : Blo 1869636 2805995 := bstep (se 1 (by rfl) ⟨2104496, by rfl⟩ : syracuseStep 2805995 = 4208993) B4208993
theorem B35975603 : Blo 1869636 35975603 := bstep (se 1 (by rfl) ⟨26981702, by rfl⟩ : syracuseStep 35975603 = 53963405) B53963405
theorem B10654199 : Blo 1869636 10654199 := bstep (se 1 (by rfl) ⟨7990649, by rfl⟩ : syracuseStep 10654199 = 15981299) B15981299
theorem B2806427 : Blo 1869636 2806427 := bstep (se 1 (by rfl) ⟨2104820, by rfl⟩ : syracuseStep 2806427 = 4209641) B4209641
theorem B6313031 : Blo 1869636 6313031 := bstep (se 1 (by rfl) ⟨4734773, by rfl⟩ : syracuseStep 6313031 = 9469547) B9469547
theorem B2806895 : Blo 1869636 2806895 := bstep (se 1 (by rfl) ⟨2105171, by rfl⟩ : syracuseStep 2806895 = 4210343) B4210343
theorem B6313463 : Blo 1869636 6313463 := bstep (se 1 (by rfl) ⟨4735097, by rfl⟩ : syracuseStep 6313463 = 9470195) B9470195
theorem B56145743 : Blo 1869636 56145743 := bstep (se 1 (by rfl) ⟨42109307, by rfl⟩ : syracuseStep 56145743 = 84218615) B84218615
theorem B10115371 : Blo 1869636 10115371 := bstep (se 1 (by rfl) ⟨7586528, by rfl⟩ : syracuseStep 10115371 = 15173057) B15173057
theorem B11983463 : Blo 1869636 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B7199741 : Blo 1869636 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B8985599 : Blo 1869636 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B4734035 : Blo 1869636 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B2104447 : Blo 1869636 2104447 := bstep (se 1 (by rfl) ⟨1578335, by rfl⟩ : syracuseStep 2104447 = 3156671) B3156671
theorem B10657115 : Blo 1869636 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B4210523 : Blo 1869636 4210523 := bstep (se 1 (by rfl) ⟨3157892, by rfl⟩ : syracuseStep 4210523 = 6315785) B6315785
theorem B36454535 : Blo 1869636 36454535 := bstep (se 1 (by rfl) ⟨27340901, by rfl⟩ : syracuseStep 36454535 = 54681803) B54681803
theorem B7102799 : Blo 1869636 7102799 := bstep (se 1 (by rfl) ⟨5327099, by rfl⟩ : syracuseStep 7102799 = 10654199) B10654199
theorem B13484855 : Blo 1869636 13484855 := bstep (se 1 (by rfl) ⟨10113641, by rfl⟩ : syracuseStep 13484855 = 20227283) B20227283
theorem B37430495 : Blo 1869636 37430495 := bstep (se 1 (by rfl) ⟨28072871, by rfl⟩ : syracuseStep 37430495 = 56145743) B56145743
theorem B7988975 : Blo 1869636 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B1869819 : Blo 1869636 1869819 := bstep (se 1 (by rfl) ⟨1402364, by rfl⟩ : syracuseStep 1869819 = 2804729) B2804729
theorem B5990399 : Blo 1869636 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B3156023 : Blo 1869636 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B4556903 : Blo 1869636 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B7104743 : Blo 1869636 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B1870151 : Blo 1869636 1870151 := bstep (se 1 (by rfl) ⟨1402613, by rfl⟩ : syracuseStep 1870151 = 2805227) B2805227
theorem B14404031 : Blo 1869636 14404031 := bstep (se 1 (by rfl) ⟨10803023, by rfl⟩ : syracuseStep 14404031 = 21606047) B21606047
theorem B1870663 : Blo 1869636 1870663 := bstep (se 1 (by rfl) ⟨1402997, by rfl⟩ : syracuseStep 1870663 = 2805995) B2805995
theorem B13487161 : Blo 1869636 13487161 := bstep (se 2 (by rfl) ⟨5057685, by rfl⟩ : syracuseStep 13487161 = 10115371) B10115371
theorem B1870951 : Blo 1869636 1870951 := bstep (se 1 (by rfl) ⟨1403213, by rfl⟩ : syracuseStep 1870951 = 2806427) B2806427
theorem B1871263 : Blo 1869636 1871263 := bstep (se 1 (by rfl) ⟨1403447, by rfl⟩ : syracuseStep 1871263 = 2806895) B2806895
theorem B2805929 : Blo 1869636 2805929 := bstep (se 2 (by rfl) ⟨1052223, by rfl⟩ : syracuseStep 2805929 = 2104447) B2104447
theorem B4207337 : Blo 1869636 4207337 := bstep (se 2 (by rfl) ⟨1577751, by rfl⟩ : syracuseStep 4207337 = 3155503) B3155503
theorem B2807015 : Blo 1869636 2807015 := bstep (se 1 (by rfl) ⟨2105261, by rfl⟩ : syracuseStep 2807015 = 4210523) B4210523
theorem B23983735 : Blo 1869636 23983735 := bstep (se 1 (by rfl) ⟨17987801, by rfl⟩ : syracuseStep 23983735 = 35975603) B35975603
theorem B4208687 : Blo 1869636 4208687 := bstep (se 1 (by rfl) ⟨3156515, by rfl⟩ : syracuseStep 4208687 = 6313031) B6313031
theorem B4208975 : Blo 1869636 4208975 := bstep (se 1 (by rfl) ⟨3156731, by rfl⟩ : syracuseStep 4208975 = 6313463) B6313463
theorem B4799827 : Blo 1869636 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B2997929 : Blo 1869636 2997929 := bstep (se 2 (by rfl) ⟨1124223, by rfl⟩ : syracuseStep 2997929 = 2248447) B2248447
theorem B4735199 : Blo 1869636 4735199 := bstep (se 1 (by rfl) ⟨3551399, by rfl⟩ : syracuseStep 4735199 = 7102799) B7102799
theorem B24953663 : Blo 1869636 24953663 := bstep (se 1 (by rfl) ⟨18715247, by rfl⟩ : syracuseStep 24953663 = 37430495) B37430495
theorem B5325983 : Blo 1869636 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B17982881 : Blo 1869636 17982881 := bstep (se 2 (by rfl) ⟨6743580, by rfl⟩ : syracuseStep 17982881 = 13487161) B13487161
theorem B4736495 : Blo 1869636 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B9602687 : Blo 1869636 9602687 := bstep (se 1 (by rfl) ⟨7202015, by rfl⟩ : syracuseStep 9602687 = 14404031) B14404031
theorem B1870619 : Blo 1869636 1870619 := bstep (se 1 (by rfl) ⟨1402964, by rfl⟩ : syracuseStep 1870619 = 2805929) B2805929
theorem B2804891 : Blo 1869636 2804891 := bstep (se 1 (by rfl) ⟨2103668, by rfl⟩ : syracuseStep 2804891 = 4207337) B4207337
theorem B8989903 : Blo 1869636 8989903 := bstep (se 1 (by rfl) ⟨6742427, by rfl⟩ : syracuseStep 8989903 = 13484855) B13484855
theorem B1871343 : Blo 1869636 1871343 := bstep (se 1 (by rfl) ⟨1403507, by rfl⟩ : syracuseStep 1871343 = 2807015) B2807015
theorem B48606965 : Blo 1869636 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B3993599 : Blo 1869636 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B2805791 : Blo 1869636 2805791 := bstep (se 1 (by rfl) ⟨2104343, by rfl⟩ : syracuseStep 2805791 = 4208687) B4208687
theorem B2805983 : Blo 1869636 2805983 := bstep (se 1 (by rfl) ⟨2104487, by rfl⟩ : syracuseStep 2805983 = 4208975) B4208975
theorem B31978313 : Blo 1869636 31978313 := bstep (se 2 (by rfl) ⟨11991867, by rfl⟩ : syracuseStep 31978313 = 23983735) B23983735
theorem B24303023 : Blo 1869636 24303023 := bstep (se 1 (by rfl) ⟨18227267, by rfl⟩ : syracuseStep 24303023 = 36454535) B36454535
theorem B2104015 : Blo 1869636 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B25599077 : Blo 1869636 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B7994477 : Blo 1869636 7994477 := bstep (se 3 (by rfl) ⟨1498964, by rfl⟩ : syracuseStep 7994477 = 2997929) B2997929
theorem B11986537 : Blo 1869636 11986537 := bstep (se 2 (by rfl) ⟨4494951, by rfl⟩ : syracuseStep 11986537 = 8989903) B8989903
theorem B17066051 : Blo 1869636 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B1869927 : Blo 1869636 1869927 := bstep (se 1 (by rfl) ⟨1402445, by rfl⟩ : syracuseStep 1869927 = 2804891) B2804891
theorem B1870527 : Blo 1869636 1870527 := bstep (se 1 (by rfl) ⟨1402895, by rfl⟩ : syracuseStep 1870527 = 2805791) B2805791
theorem B1870655 : Blo 1869636 1870655 := bstep (se 1 (by rfl) ⟨1402991, by rfl⟩ : syracuseStep 1870655 = 2805983) B2805983
theorem B3156799 : Blo 1869636 3156799 := bstep (se 1 (by rfl) ⟨2367599, by rfl⟩ : syracuseStep 3156799 = 4735199) B4735199
theorem B21318875 : Blo 1869636 21318875 := bstep (se 1 (by rfl) ⟨15989156, by rfl⟩ : syracuseStep 21318875 = 31978313) B31978313
theorem B3550655 : Blo 1869636 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B2805353 : Blo 1869636 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B11988587 : Blo 1869636 11988587 := bstep (se 1 (by rfl) ⟨8991440, by rfl⟩ : syracuseStep 11988587 = 17982881) B17982881
theorem B3157663 : Blo 1869636 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B6401791 : Blo 1869636 6401791 := bstep (se 1 (by rfl) ⟨4801343, by rfl⟩ : syracuseStep 6401791 = 9602687) B9602687
theorem B5329651 : Blo 1869636 5329651 := bstep (se 1 (by rfl) ⟨3997238, by rfl⟩ : syracuseStep 5329651 = 7994477) B7994477
theorem B32404643 : Blo 1869636 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B16635775 : Blo 1869636 16635775 := bstep (se 1 (by rfl) ⟨12476831, by rfl⟩ : syracuseStep 16635775 = 24953663) B24953663
theorem B16202015 : Blo 1869636 16202015 := bstep (se 1 (by rfl) ⟨12151511, by rfl⟩ : syracuseStep 16202015 = 24303023) B24303023
theorem B2662399 : Blo 1869636 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B21603095 : Blo 1869636 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B1870235 : Blo 1869636 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B14199461 : Blo 1869636 14199461 := bstep (se 4 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 14199461 = 2662399) B2662399
theorem B7106201 : Blo 1869636 7106201 := bstep (se 2 (by rfl) ⟨2664825, by rfl⟩ : syracuseStep 7106201 = 5329651) B5329651
theorem B10801343 : Blo 1869636 10801343 := bstep (se 1 (by rfl) ⟨8101007, by rfl⟩ : syracuseStep 10801343 = 16202015) B16202015
theorem B31969565 : Blo 1869636 31969565 := bstep (se 3 (by rfl) ⟨5994293, by rfl⟩ : syracuseStep 31969565 = 11988587) B11988587
theorem B22181033 : Blo 1869636 22181033 := bstep (se 2 (by rfl) ⟨8317887, by rfl⟩ : syracuseStep 22181033 = 16635775) B16635775
theorem B4209065 : Blo 1869636 4209065 := bstep (se 2 (by rfl) ⟨1578399, by rfl⟩ : syracuseStep 4209065 = 3156799) B3156799
theorem B9468413 : Blo 1869636 9468413 := bstep (se 3 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 9468413 = 3550655) B3550655
theorem B11377367 : Blo 1869636 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B15982049 : Blo 1869636 15982049 := bstep (se 2 (by rfl) ⟨5993268, by rfl⟩ : syracuseStep 15982049 = 11986537) B11986537
theorem B14212583 : Blo 1869636 14212583 := bstep (se 1 (by rfl) ⟨10659437, by rfl⟩ : syracuseStep 14212583 = 21318875) B21318875
theorem B4210217 : Blo 1869636 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B8535721 : Blo 1869636 8535721 := bstep (se 2 (by rfl) ⟨3200895, by rfl⟩ : syracuseStep 8535721 = 6401791) B6401791
theorem B7200895 : Blo 1869636 7200895 := bstep (se 1 (by rfl) ⟨5400671, by rfl⟩ : syracuseStep 7200895 = 10801343) B10801343
theorem B14402063 : Blo 1869636 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B14787355 : Blo 1869636 14787355 := bstep (se 1 (by rfl) ⟨11090516, by rfl⟩ : syracuseStep 14787355 = 22181033) B22181033
theorem B11380961 : Blo 1869636 11380961 := bstep (se 2 (by rfl) ⟨4267860, by rfl⟩ : syracuseStep 11380961 = 8535721) B8535721
theorem B4737467 : Blo 1869636 4737467 := bstep (se 1 (by rfl) ⟨3553100, by rfl⟩ : syracuseStep 4737467 = 7106201) B7106201
theorem B2806043 : Blo 1869636 2806043 := bstep (se 1 (by rfl) ⟨2104532, by rfl⟩ : syracuseStep 2806043 = 4209065) B4209065
theorem B6312275 : Blo 1869636 6312275 := bstep (se 1 (by rfl) ⟨4734206, by rfl⟩ : syracuseStep 6312275 = 9468413) B9468413
theorem B9466307 : Blo 1869636 9466307 := bstep (se 1 (by rfl) ⟨7099730, by rfl⟩ : syracuseStep 9466307 = 14199461) B14199461
theorem B10654699 : Blo 1869636 10654699 := bstep (se 1 (by rfl) ⟨7991024, by rfl⟩ : syracuseStep 10654699 = 15982049) B15982049
theorem B9475055 : Blo 1869636 9475055 := bstep (se 1 (by rfl) ⟨7106291, by rfl⟩ : syracuseStep 9475055 = 14212583) B14212583
theorem B2806811 : Blo 1869636 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B21313043 : Blo 1869636 21313043 := bstep (se 1 (by rfl) ⟨15984782, by rfl⟩ : syracuseStep 21313043 = 31969565) B31969565
theorem B7584911 : Blo 1869636 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B9601193 : Blo 1869636 9601193 := bstep (se 2 (by rfl) ⟨3600447, by rfl⟩ : syracuseStep 9601193 = 7200895) B7200895
theorem B9601375 : Blo 1869636 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B6316703 : Blo 1869636 6316703 := bstep (se 1 (by rfl) ⟨4737527, by rfl⟩ : syracuseStep 6316703 = 9475055) B9475055
theorem B14206265 : Blo 1869636 14206265 := bstep (se 2 (by rfl) ⟨5327349, by rfl⟩ : syracuseStep 14206265 = 10654699) B10654699
theorem B7587307 : Blo 1869636 7587307 := bstep (se 1 (by rfl) ⟨5690480, by rfl⟩ : syracuseStep 7587307 = 11380961) B11380961
theorem B5056607 : Blo 1869636 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B1870695 : Blo 1869636 1870695 := bstep (se 1 (by rfl) ⟨1403021, by rfl⟩ : syracuseStep 1870695 = 2806043) B2806043
theorem B6310871 : Blo 1869636 6310871 := bstep (se 1 (by rfl) ⟨4733153, by rfl⟩ : syracuseStep 6310871 = 9466307) B9466307
theorem B1871207 : Blo 1869636 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B14208695 : Blo 1869636 14208695 := bstep (se 1 (by rfl) ⟨10656521, by rfl⟩ : syracuseStep 14208695 = 21313043) B21313043
theorem B3158311 : Blo 1869636 3158311 := bstep (se 1 (by rfl) ⟨2368733, by rfl⟩ : syracuseStep 3158311 = 4737467) B4737467
theorem B4208183 : Blo 1869636 4208183 := bstep (se 1 (by rfl) ⟨3156137, by rfl⟩ : syracuseStep 4208183 = 6312275) B6312275
theorem B19716473 : Blo 1869636 19716473 := bstep (se 2 (by rfl) ⟨7393677, by rfl⟩ : syracuseStep 19716473 = 14787355) B14787355
theorem B4211081 : Blo 1869636 4211081 := bstep (se 2 (by rfl) ⟨1579155, by rfl⟩ : syracuseStep 4211081 = 3158311) B3158311
theorem B4211135 : Blo 1869636 4211135 := bstep (se 1 (by rfl) ⟨3158351, by rfl⟩ : syracuseStep 4211135 = 6316703) B6316703
theorem B9470843 : Blo 1869636 9470843 := bstep (se 1 (by rfl) ⟨7103132, by rfl⟩ : syracuseStep 9470843 = 14206265) B14206265
theorem B9472463 : Blo 1869636 9472463 := bstep (se 1 (by rfl) ⟨7104347, by rfl⟩ : syracuseStep 9472463 = 14208695) B14208695
theorem B6400795 : Blo 1869636 6400795 := bstep (se 1 (by rfl) ⟨4800596, by rfl⟩ : syracuseStep 6400795 = 9601193) B9601193
theorem B2805455 : Blo 1869636 2805455 := bstep (se 1 (by rfl) ⟨2104091, by rfl⟩ : syracuseStep 2805455 = 4208183) B4208183
theorem B3371071 : Blo 1869636 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B13144315 : Blo 1869636 13144315 := bstep (se 1 (by rfl) ⟨9858236, by rfl⟩ : syracuseStep 13144315 = 19716473) B19716473
theorem B4207247 : Blo 1869636 4207247 := bstep (se 1 (by rfl) ⟨3155435, by rfl⟩ : syracuseStep 4207247 = 6310871) B6310871
theorem B12801833 : Blo 1869636 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B10116409 : Blo 1869636 10116409 := bstep (se 2 (by rfl) ⟨3793653, by rfl⟩ : syracuseStep 10116409 = 7587307) B7587307
theorem B1870303 : Blo 1869636 1870303 := bstep (se 1 (by rfl) ⟨1402727, by rfl⟩ : syracuseStep 1870303 = 2805455) B2805455
theorem B17525753 : Blo 1869636 17525753 := bstep (se 2 (by rfl) ⟨6572157, by rfl⟩ : syracuseStep 17525753 = 13144315) B13144315
theorem B2804831 : Blo 1869636 2804831 := bstep (se 1 (by rfl) ⟨2103623, by rfl⟩ : syracuseStep 2804831 = 4207247) B4207247
theorem B13488545 : Blo 1869636 13488545 := bstep (se 2 (by rfl) ⟨5058204, by rfl⟩ : syracuseStep 13488545 = 10116409) B10116409
theorem B4494761 : Blo 1869636 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B2807387 : Blo 1869636 2807387 := bstep (se 1 (by rfl) ⟨2105540, by rfl⟩ : syracuseStep 2807387 = 4211081) B4211081
theorem B2807423 : Blo 1869636 2807423 := bstep (se 1 (by rfl) ⟨2105567, by rfl⟩ : syracuseStep 2807423 = 4211135) B4211135
theorem B6313895 : Blo 1869636 6313895 := bstep (se 1 (by rfl) ⟨4735421, by rfl⟩ : syracuseStep 6313895 = 9470843) B9470843
theorem B8534393 : Blo 1869636 8534393 := bstep (se 2 (by rfl) ⟨3200397, by rfl⟩ : syracuseStep 8534393 = 6400795) B6400795
theorem B8534555 : Blo 1869636 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B6314975 : Blo 1869636 6314975 := bstep (se 1 (by rfl) ⟨4736231, by rfl⟩ : syracuseStep 6314975 = 9472463) B9472463
theorem B11683835 : Blo 1869636 11683835 := bstep (se 1 (by rfl) ⟨8762876, by rfl⟩ : syracuseStep 11683835 = 17525753) B17525753
theorem B1869887 : Blo 1869636 1869887 := bstep (se 1 (by rfl) ⟨1402415, by rfl⟩ : syracuseStep 1869887 = 2804831) B2804831
theorem B1871591 : Blo 1869636 1871591 := bstep (se 1 (by rfl) ⟨1403693, by rfl⟩ : syracuseStep 1871591 = 2807387) B2807387
theorem B1871615 : Blo 1869636 1871615 := bstep (se 1 (by rfl) ⟨1403711, by rfl⟩ : syracuseStep 1871615 = 2807423) B2807423
theorem B5689595 : Blo 1869636 5689595 := bstep (se 1 (by rfl) ⟨4267196, by rfl⟩ : syracuseStep 5689595 = 8534393) B8534393
theorem B5689703 : Blo 1869636 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B2996507 : Blo 1869636 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B35969453 : Blo 1869636 35969453 := bstep (se 3 (by rfl) ⟨6744272, by rfl⟩ : syracuseStep 35969453 = 13488545) B13488545
theorem B4209263 : Blo 1869636 4209263 := bstep (se 1 (by rfl) ⟨3156947, by rfl⟩ : syracuseStep 4209263 = 6313895) B6313895
theorem B4209983 : Blo 1869636 4209983 := bstep (se 1 (by rfl) ⟨3157487, by rfl⟩ : syracuseStep 4209983 = 6314975) B6314975
theorem B3793063 : Blo 1869636 3793063 := bstep (se 1 (by rfl) ⟨2844797, by rfl⟩ : syracuseStep 3793063 = 5689595) B5689595
theorem B15172541 : Blo 1869636 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B23979635 : Blo 1869636 23979635 := bstep (se 1 (by rfl) ⟨17984726, by rfl⟩ : syracuseStep 23979635 = 35969453) B35969453
theorem B2806175 : Blo 1869636 2806175 := bstep (se 1 (by rfl) ⟨2104631, by rfl⟩ : syracuseStep 2806175 = 4209263) B4209263
theorem B2806655 : Blo 1869636 2806655 := bstep (se 1 (by rfl) ⟨2104991, by rfl⟩ : syracuseStep 2806655 = 4209983) B4209983
theorem B7789223 : Blo 1869636 7789223 := bstep (se 1 (by rfl) ⟨5841917, by rfl⟩ : syracuseStep 7789223 = 11683835) B11683835
theorem B1997671 : Blo 1869636 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B2663561 : Blo 1869636 2663561 := bstep (se 2 (by rfl) ⟨998835, by rfl⟩ : syracuseStep 2663561 = 1997671) B1997671
theorem B5057417 : Blo 1869636 5057417 := bstep (se 2 (by rfl) ⟨1896531, by rfl⟩ : syracuseStep 5057417 = 3793063) B3793063
theorem B1870783 : Blo 1869636 1870783 := bstep (se 1 (by rfl) ⟨1403087, by rfl⟩ : syracuseStep 1870783 = 2806175) B2806175
theorem B1871103 : Blo 1869636 1871103 := bstep (se 1 (by rfl) ⟨1403327, by rfl⟩ : syracuseStep 1871103 = 2806655) B2806655
theorem B15986423 : Blo 1869636 15986423 := bstep (se 1 (by rfl) ⟨11989817, by rfl⟩ : syracuseStep 15986423 = 23979635) B23979635
theorem B20771261 : Blo 1869636 20771261 := bstep (se 3 (by rfl) ⟨3894611, by rfl⟩ : syracuseStep 20771261 = 7789223) B7789223
theorem B10115027 : Blo 1869636 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B7102829 : Blo 1869636 7102829 := bstep (se 3 (by rfl) ⟨1331780, by rfl⟩ : syracuseStep 7102829 = 2663561) B2663561
theorem B6743351 : Blo 1869636 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B13486445 : Blo 1869636 13486445 := bstep (se 3 (by rfl) ⟨2528708, by rfl⟩ : syracuseStep 13486445 = 5057417) B5057417
theorem B13847507 : Blo 1869636 13847507 := bstep (se 1 (by rfl) ⟨10385630, by rfl⟩ : syracuseStep 13847507 = 20771261) B20771261
theorem B10657615 : Blo 1869636 10657615 := bstep (se 1 (by rfl) ⟨7993211, by rfl⟩ : syracuseStep 10657615 = 15986423) B15986423
theorem B4735219 : Blo 1869636 4735219 := bstep (se 1 (by rfl) ⟨3551414, by rfl⟩ : syracuseStep 4735219 = 7102829) B7102829
theorem B8990963 : Blo 1869636 8990963 := bstep (se 1 (by rfl) ⟨6743222, by rfl⟩ : syracuseStep 8990963 = 13486445) B13486445
theorem B14210153 : Blo 1869636 14210153 := bstep (se 2 (by rfl) ⟨5328807, by rfl⟩ : syracuseStep 14210153 = 10657615) B10657615
theorem B4495567 : Blo 1869636 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B9231671 : Blo 1869636 9231671 := bstep (se 1 (by rfl) ⟨6923753, by rfl⟩ : syracuseStep 9231671 = 13847507) B13847507
theorem B6154447 : Blo 1869636 6154447 := bstep (se 1 (by rfl) ⟨4615835, by rfl⟩ : syracuseStep 6154447 = 9231671) B9231671
theorem B9473435 : Blo 1869636 9473435 := bstep (se 1 (by rfl) ⟨7105076, by rfl⟩ : syracuseStep 9473435 = 14210153) B14210153
theorem B5993975 : Blo 1869636 5993975 := bstep (se 1 (by rfl) ⟨4495481, by rfl⟩ : syracuseStep 5993975 = 8990963) B8990963
theorem B5994089 : Blo 1869636 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B6313625 : Blo 1869636 6313625 := bstep (se 2 (by rfl) ⟨2367609, by rfl⟩ : syracuseStep 6313625 = 4735219) B4735219
theorem B8205929 : Blo 1869636 8205929 := bstep (se 2 (by rfl) ⟨3077223, by rfl⟩ : syracuseStep 8205929 = 6154447) B6154447
theorem B3995983 : Blo 1869636 3995983 := bstep (se 1 (by rfl) ⟨2996987, by rfl⟩ : syracuseStep 3995983 = 5993975) B5993975
theorem B3996059 : Blo 1869636 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B4209083 : Blo 1869636 4209083 := bstep (se 1 (by rfl) ⟨3156812, by rfl⟩ : syracuseStep 4209083 = 6313625) B6313625
theorem B6315623 : Blo 1869636 6315623 := bstep (se 1 (by rfl) ⟨4736717, by rfl⟩ : syracuseStep 6315623 = 9473435) B9473435
theorem B5327977 : Blo 1869636 5327977 := bstep (se 2 (by rfl) ⟨1997991, by rfl⟩ : syracuseStep 5327977 = 3995983) B3995983
theorem B2806055 : Blo 1869636 2806055 := bstep (se 1 (by rfl) ⟨2104541, by rfl⟩ : syracuseStep 2806055 = 4209083) B4209083
theorem B10656157 : Blo 1869636 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B87529909 : Blo 1869636 87529909 := bstep (se 5 (by rfl) ⟨4102964, by rfl⟩ : syracuseStep 87529909 = 8205929) B8205929
theorem B4210415 : Blo 1869636 4210415 := bstep (se 1 (by rfl) ⟨3157811, by rfl⟩ : syracuseStep 4210415 = 6315623) B6315623
theorem B7103969 : Blo 1869636 7103969 := bstep (se 2 (by rfl) ⟨2663988, by rfl⟩ : syracuseStep 7103969 = 5327977) B5327977
theorem B1870703 : Blo 1869636 1870703 := bstep (se 1 (by rfl) ⟨1403027, by rfl⟩ : syracuseStep 1870703 = 2806055) B2806055
theorem B14208209 : Blo 1869636 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B116706545 : Blo 1869636 116706545 := bstep (se 2 (by rfl) ⟨43764954, by rfl⟩ : syracuseStep 116706545 = 87529909) B87529909
theorem B2806943 : Blo 1869636 2806943 := bstep (se 1 (by rfl) ⟨2105207, by rfl⟩ : syracuseStep 2806943 = 4210415) B4210415
theorem B4735979 : Blo 1869636 4735979 := bstep (se 1 (by rfl) ⟨3551984, by rfl⟩ : syracuseStep 4735979 = 7103969) B7103969
theorem B9472139 : Blo 1869636 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B1871295 : Blo 1869636 1871295 := bstep (se 1 (by rfl) ⟨1403471, by rfl⟩ : syracuseStep 1871295 = 2806943) B2806943
theorem B77804363 : Blo 1869636 77804363 := bstep (se 1 (by rfl) ⟨58353272, by rfl⟩ : syracuseStep 77804363 = 116706545) B116706545
theorem B3157319 : Blo 1869636 3157319 := bstep (se 1 (by rfl) ⟨2367989, by rfl⟩ : syracuseStep 3157319 = 4735979) B4735979
theorem B51869575 : Blo 1869636 51869575 := bstep (se 1 (by rfl) ⟨38902181, by rfl⟩ : syracuseStep 51869575 = 77804363) B77804363
theorem B6314759 : Blo 1869636 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B69159433 : Blo 1869636 69159433 := bstep (se 2 (by rfl) ⟨25934787, by rfl⟩ : syracuseStep 69159433 = 51869575) B51869575
theorem B4209839 : Blo 1869636 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B2104879 : Blo 1869636 2104879 := bstep (se 1 (by rfl) ⟨1578659, by rfl⟩ : syracuseStep 2104879 = 3157319) B3157319
theorem B92212577 : Blo 1869636 92212577 := bstep (se 2 (by rfl) ⟨34579716, by rfl⟩ : syracuseStep 92212577 = 69159433) B69159433
theorem B2806505 : Blo 1869636 2806505 := bstep (se 2 (by rfl) ⟨1052439, by rfl⟩ : syracuseStep 2806505 = 2104879) B2104879
theorem B2806559 : Blo 1869636 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B61475051 : Blo 1869636 61475051 := bstep (se 1 (by rfl) ⟨46106288, by rfl⟩ : syracuseStep 61475051 = 92212577) B92212577
theorem B1871003 : Blo 1869636 1871003 := bstep (se 1 (by rfl) ⟨1403252, by rfl⟩ : syracuseStep 1871003 = 2806505) B2806505
theorem B1871039 : Blo 1869636 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B40983367 : Blo 1869636 40983367 := bstep (se 1 (by rfl) ⟨30737525, by rfl⟩ : syracuseStep 40983367 = 61475051) B61475051
theorem B54644489 : Blo 1869636 54644489 := bstep (se 2 (by rfl) ⟨20491683, by rfl⟩ : syracuseStep 54644489 = 40983367) B40983367
theorem B36429659 : Blo 1869636 36429659 := bstep (se 1 (by rfl) ⟨27322244, by rfl⟩ : syracuseStep 36429659 = 54644489) B54644489
theorem B24286439 : Blo 1869636 24286439 := bstep (se 1 (by rfl) ⟨18214829, by rfl⟩ : syracuseStep 24286439 = 36429659) B36429659
theorem B64763837 : Blo 1869636 64763837 := bstep (se 3 (by rfl) ⟨12143219, by rfl⟩ : syracuseStep 64763837 = 24286439) B24286439
theorem B43175891 : Blo 1869636 43175891 := bstep (se 1 (by rfl) ⟨32381918, by rfl⟩ : syracuseStep 43175891 = 64763837) B64763837
theorem B28783927 : Blo 1869636 28783927 := bstep (se 1 (by rfl) ⟨21587945, by rfl⟩ : syracuseStep 28783927 = 43175891) B43175891
theorem B38378569 : Blo 1869636 38378569 := bstep (se 2 (by rfl) ⟨14391963, by rfl⟩ : syracuseStep 38378569 = 28783927) B28783927
theorem B51171425 : Blo 1869636 51171425 := bstep (se 2 (by rfl) ⟨19189284, by rfl⟩ : syracuseStep 51171425 = 38378569) B38378569
theorem B34114283 : Blo 1869636 34114283 := bstep (se 1 (by rfl) ⟨25585712, by rfl⟩ : syracuseStep 34114283 = 51171425) B51171425
theorem B22742855 : Blo 1869636 22742855 := bstep (se 1 (by rfl) ⟨17057141, by rfl⟩ : syracuseStep 22742855 = 34114283) B34114283
theorem B15161903 : Blo 1869636 15161903 := bstep (se 1 (by rfl) ⟨11371427, by rfl⟩ : syracuseStep 15161903 = 22742855) B22742855
theorem B10107935 : Blo 1869636 10107935 := bstep (se 1 (by rfl) ⟨7580951, by rfl⟩ : syracuseStep 10107935 = 15161903) B15161903
theorem B6738623 : Blo 1869636 6738623 := bstep (se 1 (by rfl) ⟨5053967, by rfl⟩ : syracuseStep 6738623 = 10107935) B10107935
theorem B4492415 : Blo 1869636 4492415 := bstep (se 1 (by rfl) ⟨3369311, by rfl⟩ : syracuseStep 4492415 = 6738623) B6738623
theorem B2994943 : Blo 1869636 2994943 := bstep (se 1 (by rfl) ⟨2246207, by rfl⟩ : syracuseStep 2994943 = 4492415) B4492415
theorem B3993257 : Blo 1869636 3993257 := bstep (se 2 (by rfl) ⟨1497471, by rfl⟩ : syracuseStep 3993257 = 2994943) B2994943
theorem B10648685 : Blo 1869636 10648685 := bstep (se 3 (by rfl) ⟨1996628, by rfl⟩ : syracuseStep 10648685 = 3993257) B3993257
theorem B7099123 : Blo 1869636 7099123 := bstep (se 1 (by rfl) ⟨5324342, by rfl⟩ : syracuseStep 7099123 = 10648685) B10648685
theorem B9465497 : Blo 1869636 9465497 := bstep (se 2 (by rfl) ⟨3549561, by rfl⟩ : syracuseStep 9465497 = 7099123) B7099123
theorem B6310331 : Blo 1869636 6310331 := bstep (se 1 (by rfl) ⟨4732748, by rfl⟩ : syracuseStep 6310331 = 9465497) B9465497
theorem B4206887 : Blo 1869636 4206887 := bstep (se 1 (by rfl) ⟨3155165, by rfl⟩ : syracuseStep 4206887 = 6310331) B6310331
theorem B2804591 : Blo 1869636 2804591 := bstep (se 1 (by rfl) ⟨2103443, by rfl⟩ : syracuseStep 2804591 = 4206887) B4206887
theorem B1869727 : Blo 1869636 1869727 := bstep (se 1 (by rfl) ⟨1402295, by rfl⟩ : syracuseStep 1869727 = 2804591) B2804591

theorem C0 (j : ℕ) (h1 : 467409 ≤ j) (h2 : j ≤ 467908) : Blo 1869636 (4 * j + 3) := by
  interval_cases j
  · exact B1869639
  · exact B1869643
  · exact B1869647
  · exact B1869651
  · exact B1869655
  · exact B1869659
  · exact B1869663
  · exact B1869667
  · exact B1869671
  · exact B1869675
  · exact B1869679
  · exact B1869683
  · exact B1869687
  · exact B1869691
  · exact B1869695
  · exact B1869699
  · exact B1869703
  · exact B1869707
  · exact B1869711
  · exact B1869715
  · exact B1869719
  · exact B1869723
  · exact B1869727
  · exact B1869731
  · exact B1869735
  · exact B1869739
  · exact B1869743
  · exact B1869747
  · exact B1869751
  · exact B1869755
  · exact B1869759
  · exact B1869763
  · exact B1869767
  · exact B1869771
  · exact B1869775
  · exact B1869779
  · exact B1869783
  · exact B1869787
  · exact B1869791
  · exact B1869795
  · exact B1869799
  · exact B1869803
  · exact B1869807
  · exact B1869811
  · exact B1869815
  · exact B1869819
  · exact B1869823
  · exact B1869827
  · exact B1869831
  · exact B1869835
  · exact B1869839
  · exact B1869843
  · exact B1869847
  · exact B1869851
  · exact B1869855
  · exact B1869859
  · exact B1869863
  · exact B1869867
  · exact B1869871
  · exact B1869875
  · exact B1869879
  · exact B1869883
  · exact B1869887
  · exact B1869891
  · exact B1869895
  · exact B1869899
  · exact B1869903
  · exact B1869907
  · exact B1869911
  · exact B1869915
  · exact B1869919
  · exact B1869923
  · exact B1869927
  · exact B1869931
  · exact B1869935
  · exact B1869939
  · exact B1869943
  · exact B1869947
  · exact B1869951
  · exact B1869955
  · exact B1869959
  · exact B1869963
  · exact B1869967
  · exact B1869971
  · exact B1869975
  · exact B1869979
  · exact B1869983
  · exact B1869987
  · exact B1869991
  · exact B1869995
  · exact B1869999
  · exact B1870003
  · exact B1870007
  · exact B1870011
  · exact B1870015
  · exact B1870019
  · exact B1870023
  · exact B1870027
  · exact B1870031
  · exact B1870035
  · exact B1870039
  · exact B1870043
  · exact B1870047
  · exact B1870051
  · exact B1870055
  · exact B1870059
  · exact B1870063
  · exact B1870067
  · exact B1870071
  · exact B1870075
  · exact B1870079
  · exact B1870083
  · exact B1870087
  · exact B1870091
  · exact B1870095
  · exact B1870099
  · exact B1870103
  · exact B1870107
  · exact B1870111
  · exact B1870115
  · exact B1870119
  · exact B1870123
  · exact B1870127
  · exact B1870131
  · exact B1870135
  · exact B1870139
  · exact B1870143
  · exact B1870147
  · exact B1870151
  · exact B1870155
  · exact B1870159
  · exact B1870163
  · exact B1870167
  · exact B1870171
  · exact B1870175
  · exact B1870179
  · exact B1870183
  · exact B1870187
  · exact B1870191
  · exact B1870195
  · exact B1870199
  · exact B1870203
  · exact B1870207
  · exact B1870211
  · exact B1870215
  · exact B1870219
  · exact B1870223
  · exact B1870227
  · exact B1870231
  · exact B1870235
  · exact B1870239
  · exact B1870243
  · exact B1870247
  · exact B1870251
  · exact B1870255
  · exact B1870259
  · exact B1870263
  · exact B1870267
  · exact B1870271
  · exact B1870275
  · exact B1870279
  · exact B1870283
  · exact B1870287
  · exact B1870291
  · exact B1870295
  · exact B1870299
  · exact B1870303
  · exact B1870307
  · exact B1870311
  · exact B1870315
  · exact B1870319
  · exact B1870323
  · exact B1870327
  · exact B1870331
  · exact B1870335
  · exact B1870339
  · exact B1870343
  · exact B1870347
  · exact B1870351
  · exact B1870355
  · exact B1870359
  · exact B1870363
  · exact B1870367
  · exact B1870371
  · exact B1870375
  · exact B1870379
  · exact B1870383
  · exact B1870387
  · exact B1870391
  · exact B1870395
  · exact B1870399
  · exact B1870403
  · exact B1870407
  · exact B1870411
  · exact B1870415
  · exact B1870419
  · exact B1870423
  · exact B1870427
  · exact B1870431
  · exact B1870435
  · exact B1870439
  · exact B1870443
  · exact B1870447
  · exact B1870451
  · exact B1870455
  · exact B1870459
  · exact B1870463
  · exact B1870467
  · exact B1870471
  · exact B1870475
  · exact B1870479
  · exact B1870483
  · exact B1870487
  · exact B1870491
  · exact B1870495
  · exact B1870499
  · exact B1870503
  · exact B1870507
  · exact B1870511
  · exact B1870515
  · exact B1870519
  · exact B1870523
  · exact B1870527
  · exact B1870531
  · exact B1870535
  · exact B1870539
  · exact B1870543
  · exact B1870547
  · exact B1870551
  · exact B1870555
  · exact B1870559
  · exact B1870563
  · exact B1870567
  · exact B1870571
  · exact B1870575
  · exact B1870579
  · exact B1870583
  · exact B1870587
  · exact B1870591
  · exact B1870595
  · exact B1870599
  · exact B1870603
  · exact B1870607
  · exact B1870611
  · exact B1870615
  · exact B1870619
  · exact B1870623
  · exact B1870627
  · exact B1870631
  · exact B1870635
  · exact B1870639
  · exact B1870643
  · exact B1870647
  · exact B1870651
  · exact B1870655
  · exact B1870659
  · exact B1870663
  · exact B1870667
  · exact B1870671
  · exact B1870675
  · exact B1870679
  · exact B1870683
  · exact B1870687
  · exact B1870691
  · exact B1870695
  · exact B1870699
  · exact B1870703
  · exact B1870707
  · exact B1870711
  · exact B1870715
  · exact B1870719
  · exact B1870723
  · exact B1870727
  · exact B1870731
  · exact B1870735
  · exact B1870739
  · exact B1870743
  · exact B1870747
  · exact B1870751
  · exact B1870755
  · exact B1870759
  · exact B1870763
  · exact B1870767
  · exact B1870771
  · exact B1870775
  · exact B1870779
  · exact B1870783
  · exact B1870787
  · exact B1870791
  · exact B1870795
  · exact B1870799
  · exact B1870803
  · exact B1870807
  · exact B1870811
  · exact B1870815
  · exact B1870819
  · exact B1870823
  · exact B1870827
  · exact B1870831
  · exact B1870835
  · exact B1870839
  · exact B1870843
  · exact B1870847
  · exact B1870851
  · exact B1870855
  · exact B1870859
  · exact B1870863
  · exact B1870867
  · exact B1870871
  · exact B1870875
  · exact B1870879
  · exact B1870883
  · exact B1870887
  · exact B1870891
  · exact B1870895
  · exact B1870899
  · exact B1870903
  · exact B1870907
  · exact B1870911
  · exact B1870915
  · exact B1870919
  · exact B1870923
  · exact B1870927
  · exact B1870931
  · exact B1870935
  · exact B1870939
  · exact B1870943
  · exact B1870947
  · exact B1870951
  · exact B1870955
  · exact B1870959
  · exact B1870963
  · exact B1870967
  · exact B1870971
  · exact B1870975
  · exact B1870979
  · exact B1870983
  · exact B1870987
  · exact B1870991
  · exact B1870995
  · exact B1870999
  · exact B1871003
  · exact B1871007
  · exact B1871011
  · exact B1871015
  · exact B1871019
  · exact B1871023
  · exact B1871027
  · exact B1871031
  · exact B1871035
  · exact B1871039
  · exact B1871043
  · exact B1871047
  · exact B1871051
  · exact B1871055
  · exact B1871059
  · exact B1871063
  · exact B1871067
  · exact B1871071
  · exact B1871075
  · exact B1871079
  · exact B1871083
  · exact B1871087
  · exact B1871091
  · exact B1871095
  · exact B1871099
  · exact B1871103
  · exact B1871107
  · exact B1871111
  · exact B1871115
  · exact B1871119
  · exact B1871123
  · exact B1871127
  · exact B1871131
  · exact B1871135
  · exact B1871139
  · exact B1871143
  · exact B1871147
  · exact B1871151
  · exact B1871155
  · exact B1871159
  · exact B1871163
  · exact B1871167
  · exact B1871171
  · exact B1871175
  · exact B1871179
  · exact B1871183
  · exact B1871187
  · exact B1871191
  · exact B1871195
  · exact B1871199
  · exact B1871203
  · exact B1871207
  · exact B1871211
  · exact B1871215
  · exact B1871219
  · exact B1871223
  · exact B1871227
  · exact B1871231
  · exact B1871235
  · exact B1871239
  · exact B1871243
  · exact B1871247
  · exact B1871251
  · exact B1871255
  · exact B1871259
  · exact B1871263
  · exact B1871267
  · exact B1871271
  · exact B1871275
  · exact B1871279
  · exact B1871283
  · exact B1871287
  · exact B1871291
  · exact B1871295
  · exact B1871299
  · exact B1871303
  · exact B1871307
  · exact B1871311
  · exact B1871315
  · exact B1871319
  · exact B1871323
  · exact B1871327
  · exact B1871331
  · exact B1871335
  · exact B1871339
  · exact B1871343
  · exact B1871347
  · exact B1871351
  · exact B1871355
  · exact B1871359
  · exact B1871363
  · exact B1871367
  · exact B1871371
  · exact B1871375
  · exact B1871379
  · exact B1871383
  · exact B1871387
  · exact B1871391
  · exact B1871395
  · exact B1871399
  · exact B1871403
  · exact B1871407
  · exact B1871411
  · exact B1871415
  · exact B1871419
  · exact B1871423
  · exact B1871427
  · exact B1871431
  · exact B1871435
  · exact B1871439
  · exact B1871443
  · exact B1871447
  · exact B1871451
  · exact B1871455
  · exact B1871459
  · exact B1871463
  · exact B1871467
  · exact B1871471
  · exact B1871475
  · exact B1871479
  · exact B1871483
  · exact B1871487
  · exact B1871491
  · exact B1871495
  · exact B1871499
  · exact B1871503
  · exact B1871507
  · exact B1871511
  · exact B1871515
  · exact B1871519
  · exact B1871523
  · exact B1871527
  · exact B1871531
  · exact B1871535
  · exact B1871539
  · exact B1871543
  · exact B1871547
  · exact B1871551
  · exact B1871555
  · exact B1871559
  · exact B1871563
  · exact B1871567
  · exact B1871571
  · exact B1871575
  · exact B1871579
  · exact B1871583
  · exact B1871587
  · exact B1871591
  · exact B1871595
  · exact B1871599
  · exact B1871603
  · exact B1871607
  · exact B1871611
  · exact B1871615
  · exact B1871619
  · exact B1871623
  · exact B1871627
  · exact B1871631
  · exact B1871635

theorem solution (m : ℕ) (hlo : 1869636 ≤ m) (hhi : m ≤ 1871636) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 467409 ≤ j := by omega
    have hj2 : j ≤ 467908 := by omega
    have hb : Blo 1869636 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
