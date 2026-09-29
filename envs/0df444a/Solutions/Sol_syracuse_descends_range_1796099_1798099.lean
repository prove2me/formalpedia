-- Prove2me | solution 1 for syracuse_descends_range_1796099_1798099
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:49:00.146895+00:00
-- url     : https://prove2.me/submissions/40ec0f6f-dd3f-41c6-b2c0-2b569508cfe1

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


theorem B2695181 : Blo 1796099 2695181 := bbase (se 3 (by rfl) ⟨505346, by rfl⟩ : syracuseStep 2695181 = 1010693) (by norm_num)
theorem B3694621 : Blo 1796099 3694621 := bbase (se 3 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 3694621 = 1385483) (by norm_num)
theorem B2695205 : Blo 1796099 2695205 := bbase (se 4 (by rfl) ⟨252675, by rfl⟩ : syracuseStep 2695205 = 505351) (by norm_num)
theorem B4317229 : Blo 1796099 4317229 := bbase (se 3 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 4317229 = 1618961) (by norm_num)
theorem B18702389 : Blo 1796099 18702389 := bbase (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) (by norm_num)
theorem B2695229 : Blo 1796099 2695229 := bbase (se 3 (by rfl) ⟨505355, by rfl⟩ : syracuseStep 2695229 = 1010711) (by norm_num)
theorem B3457093 : Blo 1796099 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B2695253 : Blo 1796099 2695253 := bbase (se 8 (by rfl) ⟨15792, by rfl⟩ : syracuseStep 2695253 = 31585) (by norm_num)
theorem B9093221 : Blo 1796099 9093221 := bbase (se 4 (by rfl) ⟨852489, by rfl⟩ : syracuseStep 9093221 = 1704979) (by norm_num)
theorem B3031141 : Blo 1796099 3031141 := bbase (se 4 (by rfl) ⟨284169, by rfl⟩ : syracuseStep 3031141 = 568339) (by norm_num)
theorem B2695277 : Blo 1796099 2695277 := bbase (se 3 (by rfl) ⟨505364, by rfl⟩ : syracuseStep 2695277 = 1010729) (by norm_num)
theorem B2695301 : Blo 1796099 2695301 := bbase (se 4 (by rfl) ⟨252684, by rfl⟩ : syracuseStep 2695301 = 505369) (by norm_num)
theorem B2695325 : Blo 1796099 2695325 := bbase (se 3 (by rfl) ⟨505373, by rfl⟩ : syracuseStep 2695325 = 1010747) (by norm_num)
theorem B14565557 : Blo 1796099 14565557 := bbase (se 5 (by rfl) ⟨682760, by rfl⟩ : syracuseStep 14565557 = 1365521) (by norm_num)
theorem B2695349 : Blo 1796099 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B3031229 : Blo 1796099 3031229 := bbase (se 3 (by rfl) ⟨568355, by rfl⟩ : syracuseStep 3031229 = 1136711) (by norm_num)
theorem B2695373 : Blo 1796099 2695373 := bbase (se 3 (by rfl) ⟨505382, by rfl⟩ : syracuseStep 2695373 = 1010765) (by norm_num)
theorem B8536277 : Blo 1796099 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B2187481 : Blo 1796099 2187481 := bbase (se 2 (by rfl) ⟨820305, by rfl⟩ : syracuseStep 2187481 = 1640611) (by norm_num)
theorem B6062309 : Blo 1796099 6062309 := bbase (se 4 (by rfl) ⟨568341, by rfl⟩ : syracuseStep 6062309 = 1136683) (by norm_num)
theorem B2695397 : Blo 1796099 2695397 := bbase (se 4 (by rfl) ⟨252693, by rfl⟩ : syracuseStep 2695397 = 505387) (by norm_num)
theorem B4317421 : Blo 1796099 4317421 := bbase (se 3 (by rfl) ⟨809516, by rfl⟩ : syracuseStep 4317421 = 1619033) (by norm_num)
theorem B4546813 : Blo 1796099 4546813 := bbase (se 3 (by rfl) ⟨852527, by rfl⟩ : syracuseStep 4546813 = 1705055) (by norm_num)
theorem B2695421 : Blo 1796099 2695421 := bbase (se 3 (by rfl) ⟨505391, by rfl⟩ : syracuseStep 2695421 = 1010783) (by norm_num)
theorem B14565653 : Blo 1796099 14565653 := bbase (se 6 (by rfl) ⟨341382, by rfl⟩ : syracuseStep 14565653 = 682765) (by norm_num)
theorem B2695445 : Blo 1796099 2695445 := bbase (se 6 (by rfl) ⟨63174, by rfl⟩ : syracuseStep 2695445 = 126349) (by norm_num)
theorem B2695469 : Blo 1796099 2695469 := bbase (se 3 (by rfl) ⟨505400, by rfl⟩ : syracuseStep 2695469 = 1010801) (by norm_num)
theorem B3031357 : Blo 1796099 3031357 := bbase (se 3 (by rfl) ⟨568379, by rfl⟩ : syracuseStep 3031357 = 1136759) (by norm_num)
theorem B2695493 : Blo 1796099 2695493 := bbase (se 4 (by rfl) ⟨252702, by rfl⟩ : syracuseStep 2695493 = 505405) (by norm_num)
theorem B2695517 : Blo 1796099 2695517 := bbase (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) (by norm_num)
theorem B4546925 : Blo 1796099 4546925 := bbase (se 3 (by rfl) ⟨852548, by rfl⟩ : syracuseStep 4546925 = 1705097) (by norm_num)
theorem B2695541 : Blo 1796099 2695541 := bbase (se 5 (by rfl) ⟨126353, by rfl⟩ : syracuseStep 2695541 = 252707) (by norm_num)
theorem B2695565 : Blo 1796099 2695565 := bbase (se 3 (by rfl) ⟨505418, by rfl⟩ : syracuseStep 2695565 = 1010837) (by norm_num)
theorem B3031445 : Blo 1796099 3031445 := bbase (se 6 (by rfl) ⟨71049, by rfl⟩ : syracuseStep 3031445 = 142099) (by norm_num)
theorem B19423637 : Blo 1796099 19423637 := bbase (se 6 (by rfl) ⟨455241, by rfl⟩ : syracuseStep 19423637 = 910483) (by norm_num)
theorem B2695589 : Blo 1796099 2695589 := bbase (se 4 (by rfl) ⟨252711, by rfl⟩ : syracuseStep 2695589 = 505423) (by norm_num)
theorem B2695613 : Blo 1796099 2695613 := bbase (se 3 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 2695613 = 1010855) (by norm_num)
theorem B14565845 : Blo 1796099 14565845 := bbase (se 7 (by rfl) ⟨170693, by rfl⟩ : syracuseStep 14565845 = 341387) (by norm_num)
theorem B2695637 : Blo 1796099 2695637 := bbase (se 7 (by rfl) ⟨31589, by rfl⟩ : syracuseStep 2695637 = 63179) (by norm_num)
theorem B2695661 : Blo 1796099 2695661 := bbase (se 3 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 2695661 = 1010873) (by norm_num)
theorem B2695685 : Blo 1796099 2695685 := bbase (se 4 (by rfl) ⟨252720, by rfl⟩ : syracuseStep 2695685 = 505441) (by norm_num)
theorem B3031573 : Blo 1796099 3031573 := bbase (se 6 (by rfl) ⟨71052, by rfl⟩ : syracuseStep 3031573 = 142105) (by norm_num)
theorem B2695709 : Blo 1796099 2695709 := bbase (se 3 (by rfl) ⟨505445, by rfl⟩ : syracuseStep 2695709 = 1010891) (by norm_num)
theorem B4547117 : Blo 1796099 4547117 := bbase (se 3 (by rfl) ⟨852584, by rfl⟩ : syracuseStep 4547117 = 1705169) (by norm_num)
theorem B4317749 : Blo 1796099 4317749 := bbase (se 5 (by rfl) ⟨202394, by rfl⟩ : syracuseStep 4317749 = 404789) (by norm_num)
theorem B2695733 : Blo 1796099 2695733 := bbase (se 5 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 2695733 = 252725) (by norm_num)
theorem B2695757 : Blo 1796099 2695757 := bbase (se 3 (by rfl) ⟨505454, by rfl⟩ : syracuseStep 2695757 = 1010909) (by norm_num)
theorem B10232405 : Blo 1796099 10232405 := bbase (se 8 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 10232405 = 119911) (by norm_num)
theorem B6824533 : Blo 1796099 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B2695781 : Blo 1796099 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B3031661 : Blo 1796099 3031661 := bbase (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) (by norm_num)
theorem B2695805 : Blo 1796099 2695805 := bbase (se 3 (by rfl) ⟨505463, by rfl⟩ : syracuseStep 2695805 = 1010927) (by norm_num)
theorem B6062741 : Blo 1796099 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B2695829 : Blo 1796099 2695829 := bbase (se 6 (by rfl) ⟨63183, by rfl⟩ : syracuseStep 2695829 = 126367) (by norm_num)
theorem B2695853 : Blo 1796099 2695853 := bbase (se 3 (by rfl) ⟨505472, by rfl⟩ : syracuseStep 2695853 = 1010945) (by norm_num)
theorem B2695877 : Blo 1796099 2695877 := bbase (se 4 (by rfl) ⟨252738, by rfl⟩ : syracuseStep 2695877 = 505477) (by norm_num)
theorem B13837013 : Blo 1796099 13837013 := bbase (se 7 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 13837013 = 324305) (by norm_num)
theorem B2695901 : Blo 1796099 2695901 := bbase (se 3 (by rfl) ⟨505481, by rfl⟩ : syracuseStep 2695901 = 1010963) (by norm_num)
theorem B7283429 : Blo 1796099 7283429 := bbase (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) (by norm_num)
theorem B3031789 : Blo 1796099 3031789 := bbase (se 3 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 3031789 = 1136921) (by norm_num)
theorem B2695925 : Blo 1796099 2695925 := bbase (se 5 (by rfl) ⟨126371, by rfl⟩ : syracuseStep 2695925 = 252743) (by norm_num)
theorem B2695949 : Blo 1796099 2695949 := bbase (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) (by norm_num)
theorem B2695973 : Blo 1796099 2695973 := bbase (se 4 (by rfl) ⟨252747, by rfl⟩ : syracuseStep 2695973 = 505495) (by norm_num)
theorem B2695997 : Blo 1796099 2695997 := bbase (se 3 (by rfl) ⟨505499, by rfl⟩ : syracuseStep 2695997 = 1010999) (by norm_num)
theorem B3031877 : Blo 1796099 3031877 := bbase (se 4 (by rfl) ⟨284238, by rfl⟩ : syracuseStep 3031877 = 568477) (by norm_num)
theorem B2696021 : Blo 1796099 2696021 := bbase (se 9 (by rfl) ⟨7898, by rfl⟩ : syracuseStep 2696021 = 15797) (by norm_num)
theorem B2696045 : Blo 1796099 2696045 := bbase (se 3 (by rfl) ⟨505508, by rfl⟩ : syracuseStep 2696045 = 1011017) (by norm_num)
theorem B4547461 : Blo 1796099 4547461 := bbase (se 4 (by rfl) ⟨426324, by rfl⟩ : syracuseStep 4547461 = 852649) (by norm_num)
theorem B2696069 : Blo 1796099 2696069 := bbase (se 4 (by rfl) ⟨252756, by rfl⟩ : syracuseStep 2696069 = 505513) (by norm_num)
theorem B6824837 : Blo 1796099 6824837 := bbase (se 4 (by rfl) ⟨639828, by rfl⟩ : syracuseStep 6824837 = 1279657) (by norm_num)
theorem B2696093 : Blo 1796099 2696093 := bbase (se 3 (by rfl) ⟨505517, by rfl⟩ : syracuseStep 2696093 = 1011035) (by norm_num)
theorem B2696117 : Blo 1796099 2696117 := bbase (se 5 (by rfl) ⟨126380, by rfl⟩ : syracuseStep 2696117 = 252761) (by norm_num)
theorem B3032005 : Blo 1796099 3032005 := bbase (se 4 (by rfl) ⟨284250, by rfl⟩ : syracuseStep 3032005 = 568501) (by norm_num)
theorem B2696141 : Blo 1796099 2696141 := bbase (se 3 (by rfl) ⟨505526, by rfl⟩ : syracuseStep 2696141 = 1011053) (by norm_num)
theorem B9102293 : Blo 1796099 9102293 := bbase (se 7 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 9102293 = 213335) (by norm_num)
theorem B4318181 : Blo 1796099 4318181 := bbase (se 4 (by rfl) ⟨404829, by rfl⟩ : syracuseStep 4318181 = 809659) (by norm_num)
theorem B2696165 : Blo 1796099 2696165 := bbase (se 4 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 2696165 = 505531) (by norm_num)
theorem B4547573 : Blo 1796099 4547573 := bbase (se 5 (by rfl) ⟨213167, by rfl⟩ : syracuseStep 4547573 = 426335) (by norm_num)
theorem B2696189 : Blo 1796099 2696189 := bbase (se 3 (by rfl) ⟨505535, by rfl⟩ : syracuseStep 2696189 = 1011071) (by norm_num)
theorem B2049025 : Blo 1796099 2049025 := bbase (se 2 (by rfl) ⟨768384, by rfl⟩ : syracuseStep 2049025 = 1536769) (by norm_num)
theorem B2696213 : Blo 1796099 2696213 := bbase (se 6 (by rfl) ⟨63192, by rfl⟩ : syracuseStep 2696213 = 126385) (by norm_num)
theorem B3032093 : Blo 1796099 3032093 := bbase (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) (by norm_num)
theorem B2696237 : Blo 1796099 2696237 := bbase (se 3 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 2696237 = 1011089) (by norm_num)
theorem B6063173 : Blo 1796099 6063173 := bbase (se 4 (by rfl) ⟨568422, by rfl⟩ : syracuseStep 6063173 = 1136845) (by norm_num)
theorem B2696261 : Blo 1796099 2696261 := bbase (se 4 (by rfl) ⟨252774, by rfl⟩ : syracuseStep 2696261 = 505549) (by norm_num)
theorem B2696285 : Blo 1796099 2696285 := bbase (se 3 (by rfl) ⟨505553, by rfl⟩ : syracuseStep 2696285 = 1011107) (by norm_num)
theorem B2696309 : Blo 1796099 2696309 := bbase (se 5 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 2696309 = 252779) (by norm_num)
theorem B2696333 : Blo 1796099 2696333 := bbase (se 3 (by rfl) ⟨505562, by rfl⟩ : syracuseStep 2696333 = 1011125) (by norm_num)
theorem B4613261 : Blo 1796099 4613261 := bbase (se 3 (by rfl) ⟨864986, by rfl⟩ : syracuseStep 4613261 = 1729973) (by norm_num)
theorem B3032221 : Blo 1796099 3032221 := bbase (se 3 (by rfl) ⟨568541, by rfl⟩ : syracuseStep 3032221 = 1137083) (by norm_num)
theorem B2696357 : Blo 1796099 2696357 := bbase (se 4 (by rfl) ⟨252783, by rfl⟩ : syracuseStep 2696357 = 505567) (by norm_num)
theorem B4859045 : Blo 1796099 4859045 := bbase (se 4 (by rfl) ⟨455535, by rfl⟩ : syracuseStep 4859045 = 911071) (by norm_num)
theorem B4547765 : Blo 1796099 4547765 := bbase (se 5 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 4547765 = 426353) (by norm_num)
theorem B2696381 : Blo 1796099 2696381 := bbase (se 3 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 2696381 = 1011143) (by norm_num)
theorem B2696405 : Blo 1796099 2696405 := bbase (se 7 (by rfl) ⟨31598, by rfl⟩ : syracuseStep 2696405 = 63197) (by norm_num)
theorem B3237085 : Blo 1796099 3237085 := bbase (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) (by norm_num)
theorem B5833957 : Blo 1796099 5833957 := bbase (se 4 (by rfl) ⟨546933, by rfl⟩ : syracuseStep 5833957 = 1093867) (by norm_num)
theorem B2696429 : Blo 1796099 2696429 := bbase (se 3 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 2696429 = 1011161) (by norm_num)
theorem B3032309 : Blo 1796099 3032309 := bbase (se 5 (by rfl) ⟨142139, by rfl⟩ : syracuseStep 3032309 = 284279) (by norm_num)
theorem B2696453 : Blo 1796099 2696453 := bbase (se 4 (by rfl) ⟨252792, by rfl⟩ : syracuseStep 2696453 = 505585) (by norm_num)
theorem B2696477 : Blo 1796099 2696477 := bbase (se 3 (by rfl) ⟨505589, by rfl⟩ : syracuseStep 2696477 = 1011179) (by norm_num)
theorem B8308021 : Blo 1796099 8308021 := bbase (se 5 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 8308021 = 778877) (by norm_num)
theorem B4318517 : Blo 1796099 4318517 := bbase (se 5 (by rfl) ⟨202430, by rfl⟩ : syracuseStep 4318517 = 404861) (by norm_num)
theorem B2696501 : Blo 1796099 2696501 := bbase (se 5 (by rfl) ⟨126398, by rfl⟩ : syracuseStep 2696501 = 252797) (by norm_num)
theorem B2696525 : Blo 1796099 2696525 := bbase (se 3 (by rfl) ⟨505598, by rfl⟩ : syracuseStep 2696525 = 1011197) (by norm_num)
theorem B2696549 : Blo 1796099 2696549 := bbase (se 4 (by rfl) ⟨252801, by rfl⟩ : syracuseStep 2696549 = 505603) (by norm_num)
theorem B9094517 : Blo 1796099 9094517 := bbase (se 5 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 9094517 = 852611) (by norm_num)
theorem B3032437 : Blo 1796099 3032437 := bbase (se 5 (by rfl) ⟨142145, by rfl⟩ : syracuseStep 3032437 = 284291) (by norm_num)
theorem B2696573 : Blo 1796099 2696573 := bbase (se 3 (by rfl) ⟨505607, by rfl⟩ : syracuseStep 2696573 = 1011215) (by norm_num)
theorem B4097413 : Blo 1796099 4097413 := bbase (se 4 (by rfl) ⟨384132, by rfl⟩ : syracuseStep 4097413 = 768265) (by norm_num)
theorem B2696597 : Blo 1796099 2696597 := bbase (se 6 (by rfl) ⟨63201, by rfl⟩ : syracuseStep 2696597 = 126403) (by norm_num)
theorem B2696621 : Blo 1796099 2696621 := bbase (se 3 (by rfl) ⟨505616, by rfl⟩ : syracuseStep 2696621 = 1011233) (by norm_num)
theorem B2696645 : Blo 1796099 2696645 := bbase (se 4 (by rfl) ⟨252810, by rfl⟩ : syracuseStep 2696645 = 505621) (by norm_num)
theorem B1918409 : Blo 1796099 1918409 := bbase (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) (by norm_num)
theorem B3032525 : Blo 1796099 3032525 := bbase (se 3 (by rfl) ⟨568598, by rfl⟩ : syracuseStep 3032525 = 1137197) (by norm_num)
theorem B2696669 : Blo 1796099 2696669 := bbase (se 3 (by rfl) ⟨505625, by rfl⟩ : syracuseStep 2696669 = 1011251) (by norm_num)
theorem B6063605 : Blo 1796099 6063605 := bbase (se 5 (by rfl) ⟨284231, by rfl⟩ : syracuseStep 6063605 = 568463) (by norm_num)
theorem B2696693 : Blo 1796099 2696693 := bbase (se 5 (by rfl) ⟨126407, by rfl⟩ : syracuseStep 2696693 = 252815) (by norm_num)
theorem B2336261 : Blo 1796099 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B4548109 : Blo 1796099 4548109 := bbase (se 3 (by rfl) ⟨852770, by rfl⟩ : syracuseStep 4548109 = 1705541) (by norm_num)
theorem B2696717 : Blo 1796099 2696717 := bbase (se 3 (by rfl) ⟨505634, by rfl⟩ : syracuseStep 2696717 = 1011269) (by norm_num)
theorem B2696741 : Blo 1796099 2696741 := bbase (se 4 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 2696741 = 505639) (by norm_num)
theorem B2696765 : Blo 1796099 2696765 := bbase (se 3 (by rfl) ⟨505643, by rfl⟩ : syracuseStep 2696765 = 1011287) (by norm_num)
theorem B3032653 : Blo 1796099 3032653 := bbase (se 3 (by rfl) ⟨568622, by rfl⟩ : syracuseStep 3032653 = 1137245) (by norm_num)
theorem B2696789 : Blo 1796099 2696789 := bbase (se 8 (by rfl) ⟨15801, by rfl⟩ : syracuseStep 2696789 = 31603) (by norm_num)
theorem B2696813 : Blo 1796099 2696813 := bbase (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) (by norm_num)
theorem B4548221 : Blo 1796099 4548221 := bbase (se 3 (by rfl) ⟨852791, by rfl⟩ : syracuseStep 4548221 = 1705583) (by norm_num)
theorem B2696837 : Blo 1796099 2696837 := bbase (se 4 (by rfl) ⟨252828, by rfl⟩ : syracuseStep 2696837 = 505657) (by norm_num)
theorem B21849749 : Blo 1796099 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B8636053 : Blo 1796099 8636053 := bbase (se 6 (by rfl) ⟨202407, by rfl⟩ : syracuseStep 8636053 = 404815) (by norm_num)
theorem B2696861 : Blo 1796099 2696861 := bbase (se 3 (by rfl) ⟨505661, by rfl⟩ : syracuseStep 2696861 = 1011323) (by norm_num)
theorem B3032741 : Blo 1796099 3032741 := bbase (se 4 (by rfl) ⟨284319, by rfl⟩ : syracuseStep 3032741 = 568639) (by norm_num)
theorem B2049709 : Blo 1796099 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B2696885 : Blo 1796099 2696885 := bbase (se 5 (by rfl) ⟨126416, by rfl⟩ : syracuseStep 2696885 = 252833) (by norm_num)
theorem B3327677 : Blo 1796099 3327677 := bbase (se 3 (by rfl) ⟨623939, by rfl⟩ : syracuseStep 3327677 = 1247879) (by norm_num)
theorem B1918657 : Blo 1796099 1918657 := bbase (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) (by norm_num)
theorem B2696909 : Blo 1796099 2696909 := bbase (se 3 (by rfl) ⟨505670, by rfl⟩ : syracuseStep 2696909 = 1011341) (by norm_num)
theorem B2696933 : Blo 1796099 2696933 := bbase (se 4 (by rfl) ⟨252837, by rfl⟩ : syracuseStep 2696933 = 505675) (by norm_num)
theorem B2696957 : Blo 1796099 2696957 := bbase (se 3 (by rfl) ⟨505679, by rfl⟩ : syracuseStep 2696957 = 1011359) (by norm_num)
theorem B2696981 : Blo 1796099 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B3032869 : Blo 1796099 3032869 := bbase (se 4 (by rfl) ⟨284331, by rfl⟩ : syracuseStep 3032869 = 568663) (by norm_num)
theorem B2697005 : Blo 1796099 2697005 := bbase (se 3 (by rfl) ⟨505688, by rfl⟩ : syracuseStep 2697005 = 1011377) (by norm_num)
theorem B4548413 : Blo 1796099 4548413 := bbase (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) (by norm_num)
theorem B2557765 : Blo 1796099 2557765 := bbase (se 4 (by rfl) ⟨239790, by rfl⟩ : syracuseStep 2557765 = 479581) (by norm_num)
theorem B2697029 : Blo 1796099 2697029 := bbase (se 4 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 2697029 = 505693) (by norm_num)
theorem B2697053 : Blo 1796099 2697053 := bbase (se 3 (by rfl) ⟨505697, by rfl⟩ : syracuseStep 2697053 = 1011395) (by norm_num)
theorem B3237749 : Blo 1796099 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2697077 : Blo 1796099 2697077 := bbase (se 5 (by rfl) ⟨126425, by rfl⟩ : syracuseStep 2697077 = 252851) (by norm_num)
theorem B3032957 : Blo 1796099 3032957 := bbase (se 3 (by rfl) ⟨568679, by rfl⟩ : syracuseStep 3032957 = 1137359) (by norm_num)
theorem B2697101 : Blo 1796099 2697101 := bbase (se 3 (by rfl) ⟨505706, by rfl⟩ : syracuseStep 2697101 = 1011413) (by norm_num)
theorem B6064037 : Blo 1796099 6064037 := bbase (se 4 (by rfl) ⟨568503, by rfl⟩ : syracuseStep 6064037 = 1137007) (by norm_num)
theorem B2697125 : Blo 1796099 2697125 := bbase (se 4 (by rfl) ⟨252855, by rfl⟩ : syracuseStep 2697125 = 505711) (by norm_num)
theorem B2049961 : Blo 1796099 2049961 := bbase (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) (by norm_num)
theorem B2697149 : Blo 1796099 2697149 := bbase (se 3 (by rfl) ⟨505715, by rfl⟩ : syracuseStep 2697149 = 1011431) (by norm_num)
theorem B3033085 : Blo 1796099 3033085 := bbase (se 3 (by rfl) ⟨568703, by rfl⟩ : syracuseStep 3033085 = 1137407) (by norm_num)
theorem B3033173 : Blo 1796099 3033173 := bbase (se 8 (by rfl) ⟨17772, by rfl⟩ : syracuseStep 3033173 = 35545) (by norm_num)
theorem B1919089 : Blo 1796099 1919089 := bbase (se 2 (by rfl) ⟨719658, by rfl⟩ : syracuseStep 1919089 = 1439317) (by norm_num)
theorem B4548757 : Blo 1796099 4548757 := bbase (se 6 (by rfl) ⟨106611, by rfl⟩ : syracuseStep 4548757 = 213223) (by norm_num)
theorem B1820837 : Blo 1796099 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B1919161 : Blo 1796099 1919161 := bbase (se 2 (by rfl) ⟨719685, by rfl⟩ : syracuseStep 1919161 = 1439371) (by norm_num)
theorem B3836101 : Blo 1796099 3836101 := bbase (se 4 (by rfl) ⟨359634, by rfl⟩ : syracuseStep 3836101 = 719269) (by norm_num)
theorem B3033301 : Blo 1796099 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B4548869 : Blo 1796099 4548869 := bbase (se 4 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 4548869 = 852913) (by norm_num)
theorem B2304281 : Blo 1796099 2304281 := bbase (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) (by norm_num)
theorem B3033389 : Blo 1796099 3033389 := bbase (se 3 (by rfl) ⟨568760, by rfl⟩ : syracuseStep 3033389 = 1137521) (by norm_num)
theorem B2877781 : Blo 1796099 2877781 := bbase (se 10 (by rfl) ⟨4215, by rfl⟩ : syracuseStep 2877781 = 8431) (by norm_num)
theorem B6064469 : Blo 1796099 6064469 := bbase (se 10 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 6064469 = 17767) (by norm_num)
theorem B4319573 : Blo 1796099 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B1845605 : Blo 1796099 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B3033517 : Blo 1796099 3033517 := bbase (se 3 (by rfl) ⟨568784, by rfl⟩ : syracuseStep 3033517 = 1137569) (by norm_num)
theorem B4549061 : Blo 1796099 4549061 := bbase (se 4 (by rfl) ⟨426474, by rfl⟩ : syracuseStep 4549061 = 852949) (by norm_num)
theorem B11512277 : Blo 1796099 11512277 := bbase (se 7 (by rfl) ⟨134909, by rfl⟩ : syracuseStep 11512277 = 269819) (by norm_num)
theorem B7678421 : Blo 1796099 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B3410437 : Blo 1796099 3410437 := bbase (se 4 (by rfl) ⟨319728, by rfl⟩ : syracuseStep 3410437 = 639457) (by norm_num)
theorem B3033605 : Blo 1796099 3033605 := bbase (se 4 (by rfl) ⟨284400, by rfl⟩ : syracuseStep 3033605 = 568801) (by norm_num)
theorem B1919533 : Blo 1796099 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B4041269 : Blo 1796099 4041269 := bbase (se 5 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 4041269 = 378869) (by norm_num)
theorem B3836477 : Blo 1796099 3836477 := bbase (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) (by norm_num)
theorem B2558557 : Blo 1796099 2558557 := bbase (se 3 (by rfl) ⟨479729, by rfl⟩ : syracuseStep 2558557 = 959459) (by norm_num)
theorem B4098653 : Blo 1796099 4098653 := bbase (se 3 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 4098653 = 1536995) (by norm_num)
theorem B4041341 : Blo 1796099 4041341 := bbase (se 3 (by rfl) ⟨757751, by rfl⟩ : syracuseStep 4041341 = 1515503) (by norm_num)
theorem B3943037 : Blo 1796099 3943037 := bbase (se 3 (by rfl) ⟨739319, by rfl⟩ : syracuseStep 3943037 = 1478639) (by norm_num)
theorem B9095813 : Blo 1796099 9095813 := bbase (se 4 (by rfl) ⟨852732, by rfl⟩ : syracuseStep 9095813 = 1705465) (by norm_num)
theorem B3033733 : Blo 1796099 3033733 := bbase (se 4 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 3033733 = 568825) (by norm_num)
theorem B3410581 : Blo 1796099 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B4041413 : Blo 1796099 4041413 := bbase (se 4 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 4041413 = 757765) (by norm_num)
theorem B3033821 : Blo 1796099 3033821 := bbase (se 3 (by rfl) ⟨568841, by rfl⟩ : syracuseStep 3033821 = 1137683) (by norm_num)
theorem B15346421 : Blo 1796099 15346421 := bbase (se 5 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 15346421 = 1438727) (by norm_num)
theorem B10234613 : Blo 1796099 10234613 := bbase (se 5 (by rfl) ⟨479747, by rfl⟩ : syracuseStep 10234613 = 959495) (by norm_num)
theorem B6064901 : Blo 1796099 6064901 := bbase (se 4 (by rfl) ⟨568584, by rfl⟩ : syracuseStep 6064901 = 1137169) (by norm_num)
theorem B4041485 : Blo 1796099 4041485 := bbase (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) (by norm_num)
theorem B4549405 : Blo 1796099 4549405 := bbase (se 3 (by rfl) ⟨853013, by rfl⟩ : syracuseStep 4549405 = 1706027) (by norm_num)
theorem B1821485 : Blo 1796099 1821485 := bbase (se 3 (by rfl) ⟨341528, by rfl⟩ : syracuseStep 1821485 = 683057) (by norm_num)
theorem B3410741 : Blo 1796099 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B1821509 : Blo 1796099 1821509 := bbase (se 4 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 1821509 = 341533) (by norm_num)
theorem B4041557 : Blo 1796099 4041557 := bbase (se 9 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 4041557 = 23681) (by norm_num)
theorem B3033949 : Blo 1796099 3033949 := bbase (se 3 (by rfl) ⟨568865, by rfl⟩ : syracuseStep 3033949 = 1137731) (by norm_num)
theorem B4549517 : Blo 1796099 4549517 := bbase (se 3 (by rfl) ⟨853034, by rfl⟩ : syracuseStep 4549517 = 1706069) (by norm_num)
theorem B4041629 : Blo 1796099 4041629 := bbase (se 3 (by rfl) ⟨757805, by rfl⟩ : syracuseStep 4041629 = 1515611) (by norm_num)
theorem B1919909 : Blo 1796099 1919909 := bbase (se 4 (by rfl) ⟨179991, by rfl⟩ : syracuseStep 1919909 = 359983) (by norm_num)
theorem B2558893 : Blo 1796099 2558893 := bbase (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) (by norm_num)
theorem B3034037 : Blo 1796099 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B3410885 : Blo 1796099 3410885 := bbase (se 4 (by rfl) ⟨319770, by rfl⟩ : syracuseStep 3410885 = 639541) (by norm_num)
theorem B6826949 : Blo 1796099 6826949 := bbase (se 4 (by rfl) ⟨640026, by rfl⟩ : syracuseStep 6826949 = 1280053) (by norm_num)
theorem B4041701 : Blo 1796099 4041701 := bbase (se 4 (by rfl) ⟨378909, by rfl⟩ : syracuseStep 4041701 = 757819) (by norm_num)
theorem B1919981 : Blo 1796099 1919981 := bbase (se 3 (by rfl) ⟨359996, by rfl⟩ : syracuseStep 1919981 = 719993) (by norm_num)
theorem B2919421 : Blo 1796099 2919421 := bbase (se 3 (by rfl) ⟨547391, by rfl⟩ : syracuseStep 2919421 = 1094783) (by norm_num)
theorem B2731013 : Blo 1796099 2731013 := bbase (se 4 (by rfl) ⟨256032, by rfl⟩ : syracuseStep 2731013 = 512065) (by norm_num)
theorem B3460117 : Blo 1796099 3460117 := bbase (se 6 (by rfl) ⟨81096, by rfl⟩ : syracuseStep 3460117 = 162193) (by norm_num)
theorem B4041773 : Blo 1796099 4041773 := bbase (se 3 (by rfl) ⟨757832, by rfl⟩ : syracuseStep 4041773 = 1515665) (by norm_num)
theorem B3034165 : Blo 1796099 3034165 := bbase (se 5 (by rfl) ⟨142226, by rfl⟩ : syracuseStep 3034165 = 284453) (by norm_num)
theorem B4549709 : Blo 1796099 4549709 := bbase (se 3 (by rfl) ⟨853070, by rfl⟩ : syracuseStep 4549709 = 1706141) (by norm_num)
theorem B4041845 : Blo 1796099 4041845 := bbase (se 5 (by rfl) ⟨189461, by rfl⟩ : syracuseStep 4041845 = 378923) (by norm_num)
theorem B2559109 : Blo 1796099 2559109 := bbase (se 4 (by rfl) ⟨239916, by rfl⟩ : syracuseStep 2559109 = 479833) (by norm_num)
theorem B3034253 : Blo 1796099 3034253 := bbase (se 3 (by rfl) ⟨568922, by rfl⟩ : syracuseStep 3034253 = 1137845) (by norm_num)
theorem B6065333 : Blo 1796099 6065333 := bbase (se 5 (by rfl) ⟨284312, by rfl⟩ : syracuseStep 6065333 = 568625) (by norm_num)
theorem B4041917 : Blo 1796099 4041917 := bbase (se 3 (by rfl) ⟨757859, by rfl⟩ : syracuseStep 4041917 = 1515719) (by norm_num)
theorem B5115109 : Blo 1796099 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B3411173 : Blo 1796099 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B4041989 : Blo 1796099 4041989 := bbase (se 4 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 4041989 = 757873) (by norm_num)
theorem B13651253 : Blo 1796099 13651253 := bbase (se 5 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 13651253 = 1279805) (by norm_num)
theorem B4042061 : Blo 1796099 4042061 := bbase (se 3 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 4042061 = 1515773) (by norm_num)
theorem B2461037 : Blo 1796099 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B1822061 : Blo 1796099 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B3411325 : Blo 1796099 3411325 := bbase (se 3 (by rfl) ⟨639623, by rfl⟩ : syracuseStep 3411325 = 1279247) (by norm_num)
theorem B4042133 : Blo 1796099 4042133 := bbase (se 6 (by rfl) ⟨94737, by rfl⟩ : syracuseStep 4042133 = 189475) (by norm_num)
theorem B4550053 : Blo 1796099 4550053 := bbase (se 4 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 4550053 = 853135) (by norm_num)
theorem B4042205 : Blo 1796099 4042205 := bbase (se 3 (by rfl) ⟨757913, by rfl⟩ : syracuseStep 4042205 = 1515827) (by norm_num)
theorem B2878973 : Blo 1796099 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B2559485 : Blo 1796099 2559485 := bbase (se 3 (by rfl) ⟨479903, by rfl⟩ : syracuseStep 2559485 = 959807) (by norm_num)
theorem B2305553 : Blo 1796099 2305553 := bbase (se 2 (by rfl) ⟨864582, by rfl⟩ : syracuseStep 2305553 = 1729165) (by norm_num)
theorem B4550165 : Blo 1796099 4550165 := bbase (se 6 (by rfl) ⟨106644, by rfl⟩ : syracuseStep 4550165 = 213289) (by norm_num)
theorem B4042277 : Blo 1796099 4042277 := bbase (se 4 (by rfl) ⟨378963, by rfl⟩ : syracuseStep 4042277 = 757927) (by norm_num)
theorem B6065765 : Blo 1796099 6065765 := bbase (se 4 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 6065765 = 1137331) (by norm_num)
theorem B4042349 : Blo 1796099 4042349 := bbase (se 3 (by rfl) ⟨757940, by rfl⟩ : syracuseStep 4042349 = 1515881) (by norm_num)
theorem B2158249 : Blo 1796099 2158249 := bbase (se 2 (by rfl) ⟨809343, by rfl⟩ : syracuseStep 2158249 = 1618687) (by norm_num)
theorem B3411629 : Blo 1796099 3411629 := bbase (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) (by norm_num)
theorem B4042421 : Blo 1796099 4042421 := bbase (se 5 (by rfl) ⟨189488, by rfl⟩ : syracuseStep 4042421 = 378977) (by norm_num)
theorem B2879165 : Blo 1796099 2879165 := bbase (se 3 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 2879165 = 1079687) (by norm_num)
theorem B13643477 : Blo 1796099 13643477 := bbase (se 7 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 13643477 = 319769) (by norm_num)
theorem B8752853 : Blo 1796099 8752853 := bbase (se 7 (by rfl) ⟨102572, by rfl⟩ : syracuseStep 8752853 = 205145) (by norm_num)
theorem B4550357 : Blo 1796099 4550357 := bbase (se 7 (by rfl) ⟨53324, by rfl⟩ : syracuseStep 4550357 = 106649) (by norm_num)
theorem B4042493 : Blo 1796099 4042493 := bbase (se 3 (by rfl) ⟨757967, by rfl⟩ : syracuseStep 4042493 = 1515935) (by norm_num)
theorem B2158345 : Blo 1796099 2158345 := bbase (se 2 (by rfl) ⟨809379, by rfl⟩ : syracuseStep 2158345 = 1618759) (by norm_num)
theorem B2305837 : Blo 1796099 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B4042565 : Blo 1796099 4042565 := bbase (se 4 (by rfl) ⟨378990, by rfl⟩ : syracuseStep 4042565 = 757981) (by norm_num)
theorem B4042637 : Blo 1796099 4042637 := bbase (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) (by norm_num)
theorem B9097109 : Blo 1796099 9097109 := bbase (se 6 (by rfl) ⟨213213, by rfl⟩ : syracuseStep 9097109 = 426427) (by norm_num)
theorem B16396181 : Blo 1796099 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B4042709 : Blo 1796099 4042709 := bbase (se 7 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 4042709 = 94751) (by norm_num)
theorem B2273285 : Blo 1796099 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B6066197 : Blo 1796099 6066197 := bbase (se 6 (by rfl) ⟨142176, by rfl⟩ : syracuseStep 6066197 = 284353) (by norm_num)
theorem B4042781 : Blo 1796099 4042781 := bbase (se 3 (by rfl) ⟨758021, by rfl⟩ : syracuseStep 4042781 = 1516043) (by norm_num)
theorem B4550701 : Blo 1796099 4550701 := bbase (se 3 (by rfl) ⟨853256, by rfl⟩ : syracuseStep 4550701 = 1706513) (by norm_num)
theorem B2273341 : Blo 1796099 2273341 := bbase (se 3 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 2273341 = 852503) (by norm_num)
theorem B4042853 : Blo 1796099 4042853 := bbase (se 4 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 4042853 = 758035) (by norm_num)
theorem B4100213 : Blo 1796099 4100213 := bbase (se 5 (by rfl) ⟨192197, by rfl⟩ : syracuseStep 4100213 = 384395) (by norm_num)
theorem B2273437 : Blo 1796099 2273437 := bbase (se 3 (by rfl) ⟨426269, by rfl⟩ : syracuseStep 2273437 = 852539) (by norm_num)
theorem B4550813 : Blo 1796099 4550813 := bbase (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) (by norm_num)
theorem B3838117 : Blo 1796099 3838117 := bbase (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) (by norm_num)
theorem B4042925 : Blo 1796099 4042925 := bbase (se 3 (by rfl) ⟨758048, by rfl⟩ : syracuseStep 4042925 = 1516097) (by norm_num)
theorem B5836997 : Blo 1796099 5836997 := bbase (se 4 (by rfl) ⟨547218, by rfl⟩ : syracuseStep 5836997 = 1094437) (by norm_num)
theorem B7680197 : Blo 1796099 7680197 := bbase (se 4 (by rfl) ⟨720018, by rfl⟩ : syracuseStep 7680197 = 1440037) (by norm_num)
theorem B3240157 : Blo 1796099 3240157 := bbase (se 3 (by rfl) ⟨607529, by rfl⟩ : syracuseStep 3240157 = 1215059) (by norm_num)
theorem B4042997 : Blo 1796099 4042997 := bbase (se 5 (by rfl) ⟨189515, by rfl⟩ : syracuseStep 4042997 = 379031) (by norm_num)
theorem B12955925 : Blo 1796099 12955925 := bbase (se 6 (by rfl) ⟨303654, by rfl⟩ : syracuseStep 12955925 = 607309) (by norm_num)
theorem B7672117 : Blo 1796099 7672117 := bbase (se 5 (by rfl) ⟨359630, by rfl⟩ : syracuseStep 7672117 = 719261) (by norm_num)
theorem B5116213 : Blo 1796099 5116213 := bbase (se 5 (by rfl) ⟨239822, by rfl⟩ : syracuseStep 5116213 = 479645) (by norm_num)
theorem B4043069 : Blo 1796099 4043069 := bbase (se 3 (by rfl) ⟨758075, by rfl⟩ : syracuseStep 4043069 = 1516151) (by norm_num)
theorem B7672133 : Blo 1796099 7672133 := bbase (se 4 (by rfl) ⟨719262, by rfl⟩ : syracuseStep 7672133 = 1438525) (by norm_num)
theorem B2273609 : Blo 1796099 2273609 := bbase (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) (by norm_num)
theorem B6476117 : Blo 1796099 6476117 := bbase (se 10 (by rfl) ⟨9486, by rfl⟩ : syracuseStep 6476117 = 18973) (by norm_num)
theorem B4551005 : Blo 1796099 4551005 := bbase (se 3 (by rfl) ⟨853313, by rfl⟩ : syracuseStep 4551005 = 1706627) (by norm_num)
theorem B2273665 : Blo 1796099 2273665 := bbase (se 2 (by rfl) ⟨852624, by rfl⟩ : syracuseStep 2273665 = 1705249) (by norm_num)
theorem B4043141 : Blo 1796099 4043141 := bbase (se 4 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 4043141 = 758089) (by norm_num)
theorem B3412381 : Blo 1796099 3412381 := bbase (se 3 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 3412381 = 1279643) (by norm_num)
theorem B2306497 : Blo 1796099 2306497 := bbase (se 2 (by rfl) ⟨864936, by rfl⟩ : syracuseStep 2306497 = 1729873) (by norm_num)
theorem B6066629 : Blo 1796099 6066629 := bbase (se 4 (by rfl) ⟨568746, by rfl⟩ : syracuseStep 6066629 = 1137493) (by norm_num)
theorem B4043213 : Blo 1796099 4043213 := bbase (se 3 (by rfl) ⟨758102, by rfl⟩ : syracuseStep 4043213 = 1516205) (by norm_num)
theorem B2273761 : Blo 1796099 2273761 := bbase (se 2 (by rfl) ⟨852660, by rfl⟩ : syracuseStep 2273761 = 1705321) (by norm_num)
theorem B4043285 : Blo 1796099 4043285 := bbase (se 6 (by rfl) ⟨94764, by rfl⟩ : syracuseStep 4043285 = 189529) (by norm_num)
theorem B3412525 : Blo 1796099 3412525 := bbase (se 3 (by rfl) ⟨639848, by rfl⟩ : syracuseStep 3412525 = 1279697) (by norm_num)
theorem B4043357 : Blo 1796099 4043357 := bbase (se 3 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 4043357 = 1516259) (by norm_num)
theorem B2273933 : Blo 1796099 2273933 := bbase (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) (by norm_num)
theorem B4043429 : Blo 1796099 4043429 := bbase (se 4 (by rfl) ⟨379071, by rfl⟩ : syracuseStep 4043429 = 758143) (by norm_num)
theorem B4551349 : Blo 1796099 4551349 := bbase (se 5 (by rfl) ⟨213344, by rfl⟩ : syracuseStep 4551349 = 426689) (by norm_num)
theorem B2273989 : Blo 1796099 2273989 := bbase (se 4 (by rfl) ⟨213186, by rfl⟩ : syracuseStep 2273989 = 426373) (by norm_num)
theorem B3412685 : Blo 1796099 3412685 := bbase (se 3 (by rfl) ⟨639878, by rfl⟩ : syracuseStep 3412685 = 1279757) (by norm_num)
theorem B4043501 : Blo 1796099 4043501 := bbase (se 3 (by rfl) ⟨758156, by rfl⟩ : syracuseStep 4043501 = 1516313) (by norm_num)
theorem B2159345 : Blo 1796099 2159345 := bbase (se 2 (by rfl) ⟨809754, by rfl⟩ : syracuseStep 2159345 = 1619509) (by norm_num)
theorem B6820645 : Blo 1796099 6820645 := bbase (se 4 (by rfl) ⟨639435, by rfl⟩ : syracuseStep 6820645 = 1278871) (by norm_num)
theorem B2274085 : Blo 1796099 2274085 := bbase (se 4 (by rfl) ⟨213195, by rfl⟩ : syracuseStep 2274085 = 426391) (by norm_num)
theorem B2077489 : Blo 1796099 2077489 := bbase (se 2 (by rfl) ⟨779058, by rfl⟩ : syracuseStep 2077489 = 1558117) (by norm_num)
theorem B4043573 : Blo 1796099 4043573 := bbase (se 5 (by rfl) ⟨189542, by rfl⟩ : syracuseStep 4043573 = 379085) (by norm_num)
theorem B4608829 : Blo 1796099 4608829 := bbase (se 3 (by rfl) ⟨864155, by rfl⟩ : syracuseStep 4608829 = 1728311) (by norm_num)
theorem B3412829 : Blo 1796099 3412829 := bbase (se 3 (by rfl) ⟨639905, by rfl⟩ : syracuseStep 3412829 = 1279811) (by norm_num)
theorem B6067061 : Blo 1796099 6067061 := bbase (se 5 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 6067061 = 568787) (by norm_num)
theorem B4043645 : Blo 1796099 4043645 := bbase (se 3 (by rfl) ⟨758183, by rfl⟩ : syracuseStep 4043645 = 1516367) (by norm_num)
theorem B4043717 : Blo 1796099 4043717 := bbase (se 4 (by rfl) ⟨379098, by rfl⟩ : syracuseStep 4043717 = 758197) (by norm_num)
theorem B2274257 : Blo 1796099 2274257 := bbase (se 2 (by rfl) ⟨852846, by rfl⟩ : syracuseStep 2274257 = 1705693) (by norm_num)
theorem B2274313 : Blo 1796099 2274313 := bbase (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) (by norm_num)
theorem B4043789 : Blo 1796099 4043789 := bbase (se 3 (by rfl) ⟨758210, by rfl⟩ : syracuseStep 4043789 = 1516421) (by norm_num)
theorem B2159633 : Blo 1796099 2159633 := bbase (se 2 (by rfl) ⟨809862, by rfl⟩ : syracuseStep 2159633 = 1619725) (by norm_num)
theorem B3839005 : Blo 1796099 3839005 := bbase (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) (by norm_num)
theorem B6820949 : Blo 1796099 6820949 := bbase (se 8 (by rfl) ⟨39966, by rfl⟩ : syracuseStep 6820949 = 79933) (by norm_num)
theorem B4043861 : Blo 1796099 4043861 := bbase (se 8 (by rfl) ⟨23694, by rfl⟩ : syracuseStep 4043861 = 47389) (by norm_num)
theorem B2274409 : Blo 1796099 2274409 := bbase (se 2 (by rfl) ⟨852903, by rfl⟩ : syracuseStep 2274409 = 1705807) (by norm_num)
theorem B3413117 : Blo 1796099 3413117 := bbase (se 3 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 3413117 = 1279919) (by norm_num)
theorem B4043933 : Blo 1796099 4043933 := bbase (se 3 (by rfl) ⟨758237, by rfl⟩ : syracuseStep 4043933 = 1516475) (by norm_num)
theorem B9098405 : Blo 1796099 9098405 := bbase (se 4 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 9098405 = 1705951) (by norm_num)
theorem B2159797 : Blo 1796099 2159797 := bbase (se 5 (by rfl) ⟨101240, by rfl⟩ : syracuseStep 2159797 = 202481) (by norm_num)
theorem B3642565 : Blo 1796099 3642565 := bbase (se 4 (by rfl) ⟨341490, by rfl⟩ : syracuseStep 3642565 = 682981) (by norm_num)
theorem B2159825 : Blo 1796099 2159825 := bbase (se 2 (by rfl) ⟨809934, by rfl⟩ : syracuseStep 2159825 = 1619869) (by norm_num)
theorem B4044005 : Blo 1796099 4044005 := bbase (se 4 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 4044005 = 758251) (by norm_num)
theorem B3642629 : Blo 1796099 3642629 := bbase (se 4 (by rfl) ⟨341496, by rfl⟩ : syracuseStep 3642629 = 682993) (by norm_num)
theorem B2020621 : Blo 1796099 2020621 := bbase (se 3 (by rfl) ⟨378866, by rfl⟩ : syracuseStep 2020621 = 757733) (by norm_num)
theorem B2274581 : Blo 1796099 2274581 := bbase (se 6 (by rfl) ⟨53310, by rfl⟩ : syracuseStep 2274581 = 106621) (by norm_num)
theorem B3413269 : Blo 1796099 3413269 := bbase (se 6 (by rfl) ⟨79998, by rfl⟩ : syracuseStep 3413269 = 159997) (by norm_num)
theorem B6067493 : Blo 1796099 6067493 := bbase (se 4 (by rfl) ⟨568827, by rfl⟩ : syracuseStep 6067493 = 1137655) (by norm_num)
theorem B4044077 : Blo 1796099 4044077 := bbase (se 3 (by rfl) ⟨758264, by rfl⟩ : syracuseStep 4044077 = 1516529) (by norm_num)
theorem B2020657 : Blo 1796099 2020657 := bbase (se 2 (by rfl) ⟨757746, by rfl⟩ : syracuseStep 2020657 = 1515493) (by norm_num)
theorem B2159941 : Blo 1796099 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B2274637 : Blo 1796099 2274637 := bbase (se 3 (by rfl) ⟨426494, by rfl⟩ : syracuseStep 2274637 = 852989) (by norm_num)
theorem B2020693 : Blo 1796099 2020693 := bbase (se 15 (by rfl) ⟨92, by rfl⟩ : syracuseStep 2020693 = 185) (by norm_num)
theorem B4044149 : Blo 1796099 4044149 := bbase (se 5 (by rfl) ⟨189569, by rfl⟩ : syracuseStep 4044149 = 379139) (by norm_num)
theorem B2020729 : Blo 1796099 2020729 := bbase (se 2 (by rfl) ⟨757773, by rfl⟩ : syracuseStep 2020729 = 1515547) (by norm_num)
theorem B2020765 : Blo 1796099 2020765 := bbase (se 3 (by rfl) ⟨378893, by rfl⟩ : syracuseStep 2020765 = 757787) (by norm_num)
theorem B2160037 : Blo 1796099 2160037 := bbase (se 4 (by rfl) ⟨202503, by rfl⟩ : syracuseStep 2160037 = 405007) (by norm_num)
theorem B2274733 : Blo 1796099 2274733 := bbase (se 3 (by rfl) ⟨426512, by rfl⟩ : syracuseStep 2274733 = 853025) (by norm_num)
theorem B17274293 : Blo 1796099 17274293 := bbase (se 5 (by rfl) ⟨809732, by rfl⟩ : syracuseStep 17274293 = 1619465) (by norm_num)
theorem B4044221 : Blo 1796099 4044221 := bbase (se 3 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 4044221 = 1516583) (by norm_num)
theorem B2020801 : Blo 1796099 2020801 := bbase (se 2 (by rfl) ⟨757800, by rfl⟩ : syracuseStep 2020801 = 1515601) (by norm_num)
theorem B2020837 : Blo 1796099 2020837 := bbase (se 4 (by rfl) ⟨189453, by rfl⟩ : syracuseStep 2020837 = 378907) (by norm_num)
theorem B5256677 : Blo 1796099 5256677 := bbase (se 4 (by rfl) ⟨492813, by rfl⟩ : syracuseStep 5256677 = 985627) (by norm_num)
theorem B9713141 : Blo 1796099 9713141 := bbase (se 5 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 9713141 = 910607) (by norm_num)
theorem B4044293 : Blo 1796099 4044293 := bbase (se 4 (by rfl) ⟨379152, by rfl⟩ : syracuseStep 4044293 = 758305) (by norm_num)
theorem B2020873 : Blo 1796099 2020873 := bbase (se 2 (by rfl) ⟨757827, by rfl⟩ : syracuseStep 2020873 = 1515655) (by norm_num)
theorem B3839501 : Blo 1796099 3839501 := bbase (se 3 (by rfl) ⟨719906, by rfl⟩ : syracuseStep 3839501 = 1439813) (by norm_num)
theorem B2020909 : Blo 1796099 2020909 := bbase (se 3 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 2020909 = 757841) (by norm_num)
theorem B8640053 : Blo 1796099 8640053 := bbase (se 5 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 8640053 = 810005) (by norm_num)
theorem B3413573 : Blo 1796099 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B4044365 : Blo 1796099 4044365 := bbase (se 3 (by rfl) ⟨758318, by rfl⟩ : syracuseStep 4044365 = 1516637) (by norm_num)
theorem B2020945 : Blo 1796099 2020945 := bbase (se 2 (by rfl) ⟨757854, by rfl⟩ : syracuseStep 2020945 = 1515709) (by norm_num)
theorem B2274905 : Blo 1796099 2274905 := bbase (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) (by norm_num)
theorem B2020981 : Blo 1796099 2020981 := bbase (se 5 (by rfl) ⟨94733, by rfl⟩ : syracuseStep 2020981 = 189467) (by norm_num)
theorem B2274961 : Blo 1796099 2274961 := bbase (se 2 (by rfl) ⟨853110, by rfl⟩ : syracuseStep 2274961 = 1706221) (by norm_num)
theorem B4044437 : Blo 1796099 4044437 := bbase (se 6 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 4044437 = 189583) (by norm_num)
theorem B2021017 : Blo 1796099 2021017 := bbase (se 2 (by rfl) ⟨757881, by rfl⟩ : syracuseStep 2021017 = 1515763) (by norm_num)
theorem B2021053 : Blo 1796099 2021053 := bbase (se 3 (by rfl) ⟨378947, by rfl⟩ : syracuseStep 2021053 = 757895) (by norm_num)
theorem B6067925 : Blo 1796099 6067925 := bbase (se 7 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 6067925 = 142217) (by norm_num)
theorem B3282653 : Blo 1796099 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B4044509 : Blo 1796099 4044509 := bbase (se 3 (by rfl) ⟨758345, by rfl⟩ : syracuseStep 4044509 = 1516691) (by norm_num)
theorem B2021089 : Blo 1796099 2021089 := bbase (se 2 (by rfl) ⟨757908, by rfl⟩ : syracuseStep 2021089 = 1515817) (by norm_num)
theorem B2275057 : Blo 1796099 2275057 := bbase (se 2 (by rfl) ⟨853146, by rfl⟩ : syracuseStep 2275057 = 1706293) (by norm_num)
theorem B2021125 : Blo 1796099 2021125 := bbase (se 4 (by rfl) ⟨189480, by rfl⟩ : syracuseStep 2021125 = 378961) (by norm_num)
theorem B5117717 : Blo 1796099 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B4044581 : Blo 1796099 4044581 := bbase (se 4 (by rfl) ⟨379179, by rfl⟩ : syracuseStep 4044581 = 758359) (by norm_num)
theorem B2021161 : Blo 1796099 2021161 := bbase (se 2 (by rfl) ⟨757935, by rfl⟩ : syracuseStep 2021161 = 1515871) (by norm_num)
theorem B2021197 : Blo 1796099 2021197 := bbase (se 3 (by rfl) ⟨378974, by rfl⟩ : syracuseStep 2021197 = 757949) (by norm_num)
theorem B4044653 : Blo 1796099 4044653 := bbase (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) (by norm_num)
theorem B2021233 : Blo 1796099 2021233 := bbase (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) (by norm_num)
theorem B2021269 : Blo 1796099 2021269 := bbase (se 6 (by rfl) ⟨47373, by rfl⟩ : syracuseStep 2021269 = 94747) (by norm_num)
theorem B2275229 : Blo 1796099 2275229 := bbase (se 3 (by rfl) ⟨426605, by rfl⟩ : syracuseStep 2275229 = 853211) (by norm_num)
theorem B4044725 : Blo 1796099 4044725 := bbase (se 5 (by rfl) ⟨189596, by rfl⟩ : syracuseStep 4044725 = 379193) (by norm_num)
theorem B2021305 : Blo 1796099 2021305 := bbase (se 2 (by rfl) ⟨757989, by rfl⟩ : syracuseStep 2021305 = 1515979) (by norm_num)
theorem B2275285 : Blo 1796099 2275285 := bbase (se 7 (by rfl) ⟨26663, by rfl⟩ : syracuseStep 2275285 = 53327) (by norm_num)
theorem B2021341 : Blo 1796099 2021341 := bbase (se 3 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 2021341 = 758003) (by norm_num)
theorem B4044797 : Blo 1796099 4044797 := bbase (se 3 (by rfl) ⟨758399, by rfl⟩ : syracuseStep 4044797 = 1516799) (by norm_num)
theorem B2021377 : Blo 1796099 2021377 := bbase (se 2 (by rfl) ⟨758016, by rfl⟩ : syracuseStep 2021377 = 1516033) (by norm_num)
theorem B2021413 : Blo 1796099 2021413 := bbase (se 4 (by rfl) ⟨189507, by rfl⟩ : syracuseStep 2021413 = 379015) (by norm_num)
theorem B2275381 : Blo 1796099 2275381 := bbase (se 5 (by rfl) ⟨106658, by rfl⟩ : syracuseStep 2275381 = 213317) (by norm_num)
theorem B4044869 : Blo 1796099 4044869 := bbase (se 4 (by rfl) ⟨379206, by rfl⟩ : syracuseStep 4044869 = 758413) (by norm_num)
theorem B2021449 : Blo 1796099 2021449 := bbase (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) (by norm_num)
theorem B2021485 : Blo 1796099 2021485 := bbase (se 3 (by rfl) ⟨379028, by rfl⟩ : syracuseStep 2021485 = 758057) (by norm_num)
theorem B6068357 : Blo 1796099 6068357 := bbase (se 4 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 6068357 = 1137817) (by norm_num)
theorem B4044941 : Blo 1796099 4044941 := bbase (se 3 (by rfl) ⟨758426, by rfl⟩ : syracuseStep 4044941 = 1516853) (by norm_num)
theorem B2021521 : Blo 1796099 2021521 := bbase (se 2 (by rfl) ⟨758070, by rfl⟩ : syracuseStep 2021521 = 1516141) (by norm_num)
theorem B2021557 : Blo 1796099 2021557 := bbase (se 5 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 2021557 = 189521) (by norm_num)
theorem B4045013 : Blo 1796099 4045013 := bbase (se 7 (by rfl) ⟨47402, by rfl⟩ : syracuseStep 4045013 = 94805) (by norm_num)
theorem B2021593 : Blo 1796099 2021593 := bbase (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) (by norm_num)
theorem B2275553 : Blo 1796099 2275553 := bbase (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) (by norm_num)
theorem B2021629 : Blo 1796099 2021629 := bbase (se 3 (by rfl) ⟨379055, by rfl⟩ : syracuseStep 2021629 = 758111) (by norm_num)
theorem B2275609 : Blo 1796099 2275609 := bbase (se 2 (by rfl) ⟨853353, by rfl⟩ : syracuseStep 2275609 = 1706707) (by norm_num)
theorem B4045085 : Blo 1796099 4045085 := bbase (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) (by norm_num)
theorem B2021665 : Blo 1796099 2021665 := bbase (se 2 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 2021665 = 1516249) (by norm_num)
theorem B2021701 : Blo 1796099 2021701 := bbase (se 4 (by rfl) ⟨189534, by rfl⟩ : syracuseStep 2021701 = 379069) (by norm_num)
theorem B4045157 : Blo 1796099 4045157 := bbase (se 4 (by rfl) ⟨379233, by rfl⟩ : syracuseStep 4045157 = 758467) (by norm_num)
theorem B2021737 : Blo 1796099 2021737 := bbase (se 2 (by rfl) ⟨758151, by rfl⟩ : syracuseStep 2021737 = 1516303) (by norm_num)
theorem B2275705 : Blo 1796099 2275705 := bbase (se 2 (by rfl) ⟨853389, by rfl⟩ : syracuseStep 2275705 = 1706779) (by norm_num)
theorem B2021773 : Blo 1796099 2021773 := bbase (se 3 (by rfl) ⟨379082, by rfl⟩ : syracuseStep 2021773 = 758165) (by norm_num)
theorem B4045229 : Blo 1796099 4045229 := bbase (se 3 (by rfl) ⟨758480, by rfl⟩ : syracuseStep 4045229 = 1516961) (by norm_num)
theorem B2021809 : Blo 1796099 2021809 := bbase (se 2 (by rfl) ⟨758178, by rfl⟩ : syracuseStep 2021809 = 1516357) (by norm_num)
theorem B9099701 : Blo 1796099 9099701 := bbase (se 5 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 9099701 = 853097) (by norm_num)
theorem B2021845 : Blo 1796099 2021845 := bbase (se 7 (by rfl) ⟨23693, by rfl⟩ : syracuseStep 2021845 = 47387) (by norm_num)
theorem B34552277 : Blo 1796099 34552277 := bbase (se 7 (by rfl) ⟨404909, by rfl⟩ : syracuseStep 34552277 = 809819) (by norm_num)
theorem B4610533 : Blo 1796099 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B17512949 : Blo 1796099 17512949 := bbase (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) (by norm_num)
theorem B4045301 : Blo 1796099 4045301 := bbase (se 5 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 4045301 = 379247) (by norm_num)
theorem B2021881 : Blo 1796099 2021881 := bbase (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) (by norm_num)
theorem B7674389 : Blo 1796099 7674389 := bbase (se 6 (by rfl) ⟨179868, by rfl⟩ : syracuseStep 7674389 = 359737) (by norm_num)
theorem B2021917 : Blo 1796099 2021917 := bbase (se 3 (by rfl) ⟨379109, by rfl⟩ : syracuseStep 2021917 = 758219) (by norm_num)
theorem B4045373 : Blo 1796099 4045373 := bbase (se 3 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 4045373 = 1517015) (by norm_num)
theorem B2021953 : Blo 1796099 2021953 := bbase (se 2 (by rfl) ⟨758232, by rfl⟩ : syracuseStep 2021953 = 1516465) (by norm_num)
theorem B2021989 : Blo 1796099 2021989 := bbase (se 4 (by rfl) ⟨189561, by rfl⟩ : syracuseStep 2021989 = 379123) (by norm_num)
theorem B7289477 : Blo 1796099 7289477 := bbase (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) (by norm_num)
theorem B4045445 : Blo 1796099 4045445 := bbase (se 4 (by rfl) ⟨379260, by rfl⟩ : syracuseStep 4045445 = 758521) (by norm_num)
theorem B2022025 : Blo 1796099 2022025 := bbase (se 2 (by rfl) ⟨758259, by rfl⟩ : syracuseStep 2022025 = 1516519) (by norm_num)
theorem B10230421 : Blo 1796099 10230421 := bbase (se 6 (by rfl) ⟨239775, by rfl⟩ : syracuseStep 10230421 = 479551) (by norm_num)
theorem B2022061 : Blo 1796099 2022061 := bbase (se 3 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 2022061 = 758273) (by norm_num)
theorem B5757637 : Blo 1796099 5757637 := bbase (se 4 (by rfl) ⟨539778, by rfl⟩ : syracuseStep 5757637 = 1079557) (by norm_num)
theorem B4045517 : Blo 1796099 4045517 := bbase (se 3 (by rfl) ⟨758534, by rfl⟩ : syracuseStep 4045517 = 1517069) (by norm_num)
theorem B2022097 : Blo 1796099 2022097 := bbase (se 2 (by rfl) ⟨758286, by rfl⟩ : syracuseStep 2022097 = 1516573) (by norm_num)
theorem B2022133 : Blo 1796099 2022133 := bbase (se 5 (by rfl) ⟨94787, by rfl⟩ : syracuseStep 2022133 = 189575) (by norm_num)
theorem B7289605 : Blo 1796099 7289605 := bbase (se 4 (by rfl) ⟨683400, by rfl⟩ : syracuseStep 7289605 = 1366801) (by norm_num)
theorem B6478613 : Blo 1796099 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B4045589 : Blo 1796099 4045589 := bbase (se 6 (by rfl) ⟨94818, by rfl⟩ : syracuseStep 4045589 = 189637) (by norm_num)
theorem B2022169 : Blo 1796099 2022169 := bbase (se 2 (by rfl) ⟨758313, by rfl⟩ : syracuseStep 2022169 = 1516627) (by norm_num)
theorem B2022205 : Blo 1796099 2022205 := bbase (se 3 (by rfl) ⟨379163, by rfl⟩ : syracuseStep 2022205 = 758327) (by norm_num)
theorem B4045661 : Blo 1796099 4045661 := bbase (se 3 (by rfl) ⟨758561, by rfl⟩ : syracuseStep 4045661 = 1517123) (by norm_num)
theorem B2022241 : Blo 1796099 2022241 := bbase (se 2 (by rfl) ⟨758340, by rfl⟩ : syracuseStep 2022241 = 1516681) (by norm_num)
theorem B2022277 : Blo 1796099 2022277 := bbase (se 4 (by rfl) ⟨189588, by rfl⟩ : syracuseStep 2022277 = 379177) (by norm_num)
theorem B2022313 : Blo 1796099 2022313 := bbase (se 2 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 2022313 = 1516735) (by norm_num)
theorem B5757893 : Blo 1796099 5757893 := bbase (se 4 (by rfl) ⟨539802, by rfl⟩ : syracuseStep 5757893 = 1079605) (by norm_num)
theorem B2022349 : Blo 1796099 2022349 := bbase (se 3 (by rfl) ⟨379190, by rfl⟩ : syracuseStep 2022349 = 758381) (by norm_num)
theorem B2022385 : Blo 1796099 2022385 := bbase (se 2 (by rfl) ⟨758394, by rfl⟩ : syracuseStep 2022385 = 1516789) (by norm_num)
theorem B2694149 : Blo 1796099 2694149 := bbase (se 4 (by rfl) ⟨252576, by rfl⟩ : syracuseStep 2694149 = 505153) (by norm_num)
theorem B2022421 : Blo 1796099 2022421 := bbase (se 6 (by rfl) ⟨47400, by rfl⟩ : syracuseStep 2022421 = 94801) (by norm_num)
theorem B2694173 : Blo 1796099 2694173 := bbase (se 3 (by rfl) ⟨505157, by rfl⟩ : syracuseStep 2694173 = 1010315) (by norm_num)
theorem B2694197 : Blo 1796099 2694197 := bbase (se 5 (by rfl) ⟨126290, by rfl⟩ : syracuseStep 2694197 = 252581) (by norm_num)
theorem B2022457 : Blo 1796099 2022457 := bbase (se 2 (by rfl) ⟨758421, by rfl⟩ : syracuseStep 2022457 = 1516843) (by norm_num)
theorem B2694221 : Blo 1796099 2694221 := bbase (se 3 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 2694221 = 1010333) (by norm_num)
theorem B147881045 : Blo 1796099 147881045 := bbase (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) (by norm_num)
theorem B2022493 : Blo 1796099 2022493 := bbase (se 3 (by rfl) ⟨379217, by rfl⟩ : syracuseStep 2022493 = 758435) (by norm_num)
theorem B2694245 : Blo 1796099 2694245 := bbase (se 4 (by rfl) ⟨252585, by rfl⟩ : syracuseStep 2694245 = 505171) (by norm_num)
theorem B14965877 : Blo 1796099 14965877 := bbase (se 5 (by rfl) ⟨701525, by rfl⟩ : syracuseStep 14965877 = 1403051) (by norm_num)
theorem B2694269 : Blo 1796099 2694269 := bbase (se 3 (by rfl) ⟨505175, by rfl⟩ : syracuseStep 2694269 = 1010351) (by norm_num)
theorem B2022529 : Blo 1796099 2022529 := bbase (se 2 (by rfl) ⟨758448, by rfl⟩ : syracuseStep 2022529 = 1516897) (by norm_num)
theorem B2694293 : Blo 1796099 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B6823061 : Blo 1796099 6823061 := bbase (se 6 (by rfl) ⟨159915, by rfl⟩ : syracuseStep 6823061 = 319831) (by norm_num)
theorem B2022565 : Blo 1796099 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B2694317 : Blo 1796099 2694317 := bbase (se 3 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 2694317 = 1010369) (by norm_num)
theorem B2694341 : Blo 1796099 2694341 := bbase (se 4 (by rfl) ⟨252594, by rfl⟩ : syracuseStep 2694341 = 505189) (by norm_num)
theorem B2022601 : Blo 1796099 2022601 := bbase (se 2 (by rfl) ⟨758475, by rfl⟩ : syracuseStep 2022601 = 1516951) (by norm_num)
theorem B2694365 : Blo 1796099 2694365 := bbase (se 3 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 2694365 = 1010387) (by norm_num)
theorem B4611293 : Blo 1796099 4611293 := bbase (se 3 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 4611293 = 1729235) (by norm_num)
theorem B2022637 : Blo 1796099 2022637 := bbase (se 3 (by rfl) ⟨379244, by rfl⟩ : syracuseStep 2022637 = 758489) (by norm_num)
theorem B2694389 : Blo 1796099 2694389 := bbase (se 5 (by rfl) ⟨126299, by rfl⟩ : syracuseStep 2694389 = 252599) (by norm_num)
theorem B2694413 : Blo 1796099 2694413 := bbase (se 3 (by rfl) ⟨505202, by rfl⟩ : syracuseStep 2694413 = 1010405) (by norm_num)
theorem B2022673 : Blo 1796099 2022673 := bbase (se 2 (by rfl) ⟨758502, by rfl⟩ : syracuseStep 2022673 = 1517005) (by norm_num)
theorem B2694437 : Blo 1796099 2694437 := bbase (se 4 (by rfl) ⟨252603, by rfl⟩ : syracuseStep 2694437 = 505207) (by norm_num)
theorem B2022709 : Blo 1796099 2022709 := bbase (se 5 (by rfl) ⟨94814, by rfl⟩ : syracuseStep 2022709 = 189629) (by norm_num)
theorem B2694461 : Blo 1796099 2694461 := bbase (se 3 (by rfl) ⟨505211, by rfl⟩ : syracuseStep 2694461 = 1010423) (by norm_num)
theorem B5119301 : Blo 1796099 5119301 := bbase (se 4 (by rfl) ⟨479934, by rfl⟩ : syracuseStep 5119301 = 959869) (by norm_num)
theorem B2694485 : Blo 1796099 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B6479189 : Blo 1796099 6479189 := bbase (se 11 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 6479189 = 9491) (by norm_num)
theorem B2022745 : Blo 1796099 2022745 := bbase (se 2 (by rfl) ⟨758529, by rfl⟩ : syracuseStep 2022745 = 1517059) (by norm_num)
theorem B2694509 : Blo 1796099 2694509 := bbase (se 3 (by rfl) ⟨505220, by rfl⟩ : syracuseStep 2694509 = 1010441) (by norm_num)
theorem B9715061 : Blo 1796099 9715061 := bbase (se 5 (by rfl) ⟨455393, by rfl⟩ : syracuseStep 9715061 = 910787) (by norm_num)
theorem B2022781 : Blo 1796099 2022781 := bbase (se 3 (by rfl) ⟨379271, by rfl⟩ : syracuseStep 2022781 = 758543) (by norm_num)
theorem B2694533 : Blo 1796099 2694533 := bbase (se 4 (by rfl) ⟨252612, by rfl⟩ : syracuseStep 2694533 = 505225) (by norm_num)
theorem B2694557 : Blo 1796099 2694557 := bbase (se 3 (by rfl) ⟨505229, by rfl⟩ : syracuseStep 2694557 = 1010459) (by norm_num)
theorem B2022817 : Blo 1796099 2022817 := bbase (se 2 (by rfl) ⟨758556, by rfl⟩ : syracuseStep 2022817 = 1517113) (by norm_num)
theorem B2694581 : Blo 1796099 2694581 := bbase (se 5 (by rfl) ⟨126308, by rfl⟩ : syracuseStep 2694581 = 252617) (by norm_num)
theorem B6823349 : Blo 1796099 6823349 := bbase (se 5 (by rfl) ⟨319844, by rfl⟩ : syracuseStep 6823349 = 639689) (by norm_num)
theorem B2022853 : Blo 1796099 2022853 := bbase (se 4 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 2022853 = 379285) (by norm_num)
theorem B2694605 : Blo 1796099 2694605 := bbase (se 3 (by rfl) ⟨505238, by rfl⟩ : syracuseStep 2694605 = 1010477) (by norm_num)
theorem B2694629 : Blo 1796099 2694629 := bbase (se 4 (by rfl) ⟨252621, by rfl⟩ : syracuseStep 2694629 = 505243) (by norm_num)
theorem B4857317 : Blo 1796099 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B2694653 : Blo 1796099 2694653 := bbase (se 3 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 2694653 = 1010495) (by norm_num)
theorem B2694677 : Blo 1796099 2694677 := bbase (se 6 (by rfl) ⟨63156, by rfl⟩ : syracuseStep 2694677 = 126313) (by norm_num)
theorem B2694701 : Blo 1796099 2694701 := bbase (se 3 (by rfl) ⟨505256, by rfl⟩ : syracuseStep 2694701 = 1010513) (by norm_num)
theorem B2694725 : Blo 1796099 2694725 := bbase (se 4 (by rfl) ⟨252630, by rfl⟩ : syracuseStep 2694725 = 505261) (by norm_num)
theorem B2694749 : Blo 1796099 2694749 := bbase (se 3 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 2694749 = 1010531) (by norm_num)
theorem B2694773 : Blo 1796099 2694773 := bbase (se 5 (by rfl) ⟨126317, by rfl⟩ : syracuseStep 2694773 = 252635) (by norm_num)
theorem B2694797 : Blo 1796099 2694797 := bbase (se 3 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 2694797 = 1010549) (by norm_num)
theorem B2694821 : Blo 1796099 2694821 := bbase (se 4 (by rfl) ⟨252639, by rfl⟩ : syracuseStep 2694821 = 505279) (by norm_num)
theorem B2694845 : Blo 1796099 2694845 := bbase (se 3 (by rfl) ⟨505283, by rfl⟩ : syracuseStep 2694845 = 1010567) (by norm_num)
theorem B5463749 : Blo 1796099 5463749 := bbase (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) (by norm_num)
theorem B9100997 : Blo 1796099 9100997 := bbase (se 4 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 9100997 = 1706437) (by norm_num)
theorem B2694869 : Blo 1796099 2694869 := bbase (se 7 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 2694869 = 63161) (by norm_num)
theorem B3890917 : Blo 1796099 3890917 := bbase (se 4 (by rfl) ⟨364773, by rfl⟩ : syracuseStep 3890917 = 729547) (by norm_num)
theorem B2694893 : Blo 1796099 2694893 := bbase (se 3 (by rfl) ⟨505292, by rfl⟩ : syracuseStep 2694893 = 1010585) (by norm_num)
theorem B2694917 : Blo 1796099 2694917 := bbase (se 4 (by rfl) ⟨252648, by rfl⟩ : syracuseStep 2694917 = 505297) (by norm_num)
theorem B6479621 : Blo 1796099 6479621 := bbase (se 4 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 6479621 = 1214929) (by norm_num)
theorem B2694941 : Blo 1796099 2694941 := bbase (se 3 (by rfl) ⟨505301, by rfl⟩ : syracuseStep 2694941 = 1010603) (by norm_num)
theorem B6913829 : Blo 1796099 6913829 := bbase (se 4 (by rfl) ⟨648171, by rfl⟩ : syracuseStep 6913829 = 1296343) (by norm_num)
theorem B6061877 : Blo 1796099 6061877 := bbase (se 5 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 6061877 = 568301) (by norm_num)
theorem B2694965 : Blo 1796099 2694965 := bbase (se 5 (by rfl) ⟨126326, by rfl⟩ : syracuseStep 2694965 = 252653) (by norm_num)
theorem B2694989 : Blo 1796099 2694989 := bbase (se 3 (by rfl) ⟨505310, by rfl⟩ : syracuseStep 2694989 = 1010621) (by norm_num)
theorem B2695013 : Blo 1796099 2695013 := bbase (se 4 (by rfl) ⟨252657, by rfl⟩ : syracuseStep 2695013 = 505315) (by norm_num)
theorem B2695037 : Blo 1796099 2695037 := bbase (se 3 (by rfl) ⟨505319, by rfl⟩ : syracuseStep 2695037 = 1010639) (by norm_num)
theorem B3030925 : Blo 1796099 3030925 := bbase (se 3 (by rfl) ⟨568298, by rfl⟩ : syracuseStep 3030925 = 1136597) (by norm_num)
theorem B2695061 : Blo 1796099 2695061 := bbase (se 6 (by rfl) ⟨63165, by rfl⟩ : syracuseStep 2695061 = 126331) (by norm_num)
theorem B4546469 : Blo 1796099 4546469 := bbase (se 4 (by rfl) ⟨426231, by rfl⟩ : syracuseStep 4546469 = 852463) (by norm_num)
theorem B2695085 : Blo 1796099 2695085 := bbase (se 3 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 2695085 = 1010657) (by norm_num)
theorem B2695109 : Blo 1796099 2695109 := bbase (se 4 (by rfl) ⟨252666, by rfl⟩ : syracuseStep 2695109 = 505333) (by norm_num)
theorem B4317133 : Blo 1796099 4317133 := bbase (se 3 (by rfl) ⟨809462, by rfl⟩ : syracuseStep 4317133 = 1618925) (by norm_num)
theorem B2695133 : Blo 1796099 2695133 := bbase (se 3 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 2695133 = 1010675) (by norm_num)
theorem B3031013 : Blo 1796099 3031013 := bbase (se 4 (by rfl) ⟨284157, by rfl⟩ : syracuseStep 3031013 = 568315) (by norm_num)
theorem B5119973 : Blo 1796099 5119973 := bbase (se 4 (by rfl) ⟨479997, by rfl⟩ : syracuseStep 5119973 = 959995) (by norm_num)
theorem B2695157 : Blo 1796099 2695157 := bbase (se 5 (by rfl) ⟨126335, by rfl⟩ : syracuseStep 2695157 = 252671) (by norm_num)
theorem B2695169 : Blo 1796099 2695169 := bstep (se 2 (by rfl) ⟨1010688, by rfl⟩ : syracuseStep 2695169 = 2021377) B2021377
theorem B6062093 : Blo 1796099 6062093 := bstep (se 3 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 6062093 = 2273285) B2273285
theorem B2695187 : Blo 1796099 2695187 := bstep (se 1 (by rfl) ⟨2021390, by rfl⟩ : syracuseStep 2695187 = 4042781) B4042781
theorem B12468259 : Blo 1796099 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B5759021 : Blo 1796099 5759021 := bstep (se 3 (by rfl) ⟨1079816, by rfl⟩ : syracuseStep 5759021 = 2159633) B2159633
theorem B2695217 : Blo 1796099 2695217 := bstep (se 2 (by rfl) ⟨1010706, by rfl⟩ : syracuseStep 2695217 = 2021413) B2021413
theorem B6062147 : Blo 1796099 6062147 := bstep (se 1 (by rfl) ⟨4546610, by rfl⟩ : syracuseStep 6062147 = 9093221) B9093221
theorem B2695235 : Blo 1796099 2695235 := bstep (se 1 (by rfl) ⟨2021426, by rfl⟩ : syracuseStep 2695235 = 4042853) B4042853
theorem B3031121 : Blo 1796099 3031121 := bstep (se 2 (by rfl) ⟨1136670, by rfl⟩ : syracuseStep 3031121 = 2273341) B2273341
theorem B2695265 : Blo 1796099 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B2695283 : Blo 1796099 2695283 := bstep (se 1 (by rfl) ⟨2021462, by rfl⟩ : syracuseStep 2695283 = 4042925) B4042925
theorem B3891331 : Blo 1796099 3891331 := bstep (se 1 (by rfl) ⟨2918498, by rfl⟩ : syracuseStep 3891331 = 5836997) B5836997
theorem B2695313 : Blo 1796099 2695313 := bstep (se 2 (by rfl) ⟨1010742, by rfl⟩ : syracuseStep 2695313 = 2021485) B2021485
theorem B2695331 : Blo 1796099 2695331 := bstep (se 1 (by rfl) ⟨2021498, by rfl⟩ : syracuseStep 2695331 = 4042997) B4042997
theorem B24592565 : Blo 1796099 24592565 := bstep (se 5 (by rfl) ⟨1152776, by rfl⟩ : syracuseStep 24592565 = 2305553) B2305553
theorem B2695361 : Blo 1796099 2695361 := bstep (se 2 (by rfl) ⟨1010760, by rfl⟩ : syracuseStep 2695361 = 2021521) B2021521
theorem B3031249 : Blo 1796099 3031249 := bstep (se 2 (by rfl) ⟨1136718, by rfl⟩ : syracuseStep 3031249 = 2273437) B2273437
theorem B2695379 : Blo 1796099 2695379 := bstep (se 1 (by rfl) ⟨2021534, by rfl⟩ : syracuseStep 2695379 = 4043069) B4043069
theorem B2695409 : Blo 1796099 2695409 := bstep (se 2 (by rfl) ⟨1010778, by rfl⟩ : syracuseStep 2695409 = 2021557) B2021557
theorem B3031283 : Blo 1796099 3031283 := bstep (se 1 (by rfl) ⟨2273462, by rfl⟩ : syracuseStep 3031283 = 4546925) B4546925
theorem B2695427 : Blo 1796099 2695427 := bstep (se 1 (by rfl) ⟨2021570, by rfl⟩ : syracuseStep 2695427 = 4043141) B4043141
theorem B2916641 : Blo 1796099 2916641 := bstep (se 2 (by rfl) ⟨1093740, by rfl⟩ : syracuseStep 2916641 = 2187481) B2187481
theorem B2695457 : Blo 1796099 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B2695475 : Blo 1796099 2695475 := bstep (se 1 (by rfl) ⟨2021606, by rfl⟩ : syracuseStep 2695475 = 4043213) B4043213
theorem B9101645 : Blo 1796099 9101645 := bstep (se 3 (by rfl) ⟨1706558, by rfl⟩ : syracuseStep 9101645 = 3413117) B3413117
theorem B6062417 : Blo 1796099 6062417 := bstep (se 2 (by rfl) ⟨2273406, by rfl⟩ : syracuseStep 6062417 = 4546813) B4546813
theorem B2695505 : Blo 1796099 2695505 := bstep (se 2 (by rfl) ⟨1010814, by rfl⟩ : syracuseStep 2695505 = 2021629) B2021629
theorem B2695523 : Blo 1796099 2695523 := bstep (se 1 (by rfl) ⟨2021642, by rfl⟩ : syracuseStep 2695523 = 4043285) B4043285
theorem B3031411 : Blo 1796099 3031411 := bstep (se 1 (by rfl) ⟨2273558, by rfl⟩ : syracuseStep 3031411 = 4547117) B4547117
theorem B2695553 : Blo 1796099 2695553 := bstep (se 2 (by rfl) ⟨1010832, by rfl⟩ : syracuseStep 2695553 = 2021665) B2021665
theorem B2695571 : Blo 1796099 2695571 := bstep (se 1 (by rfl) ⟨2021678, by rfl⟩ : syracuseStep 2695571 = 4043357) B4043357
theorem B2695601 : Blo 1796099 2695601 := bstep (se 2 (by rfl) ⟨1010850, by rfl⟩ : syracuseStep 2695601 = 2021701) B2021701
theorem B2695619 : Blo 1796099 2695619 := bstep (se 1 (by rfl) ⟨2021714, by rfl⟩ : syracuseStep 2695619 = 4043429) B4043429
theorem B2695649 : Blo 1796099 2695649 := bstep (se 2 (by rfl) ⟨1010868, by rfl⟩ : syracuseStep 2695649 = 2021737) B2021737
theorem B9224675 : Blo 1796099 9224675 := bstep (se 1 (by rfl) ⟨6918506, by rfl⟩ : syracuseStep 9224675 = 13837013) B13837013
theorem B2695667 : Blo 1796099 2695667 := bstep (se 1 (by rfl) ⟨2021750, by rfl⟩ : syracuseStep 2695667 = 4043501) B4043501
theorem B3031553 : Blo 1796099 3031553 := bstep (se 2 (by rfl) ⟨1136832, by rfl⟩ : syracuseStep 3031553 = 2273665) B2273665
theorem B20480525 : Blo 1796099 20480525 := bstep (se 3 (by rfl) ⟨3840098, by rfl⟩ : syracuseStep 20480525 = 7680197) B7680197
theorem B2695697 : Blo 1796099 2695697 := bstep (se 2 (by rfl) ⟨1010886, by rfl⟩ : syracuseStep 2695697 = 2021773) B2021773
theorem B2695715 : Blo 1796099 2695715 := bstep (se 1 (by rfl) ⟨2021786, by rfl⟩ : syracuseStep 2695715 = 4043573) B4043573
theorem B5759533 : Blo 1796099 5759533 := bstep (se 3 (by rfl) ⟨1079912, by rfl⟩ : syracuseStep 5759533 = 2159825) B2159825
theorem B2695745 : Blo 1796099 2695745 := bstep (se 2 (by rfl) ⟨1010904, by rfl⟩ : syracuseStep 2695745 = 2021809) B2021809
theorem B2695763 : Blo 1796099 2695763 := bstep (se 1 (by rfl) ⟨2021822, by rfl⟩ : syracuseStep 2695763 = 4043645) B4043645
theorem B2695793 : Blo 1796099 2695793 := bstep (se 2 (by rfl) ⟨1010922, by rfl⟩ : syracuseStep 2695793 = 2021845) B2021845
theorem B3031681 : Blo 1796099 3031681 := bstep (se 2 (by rfl) ⟨1136880, by rfl⟩ : syracuseStep 3031681 = 2273761) B2273761
theorem B2695811 : Blo 1796099 2695811 := bstep (se 1 (by rfl) ⟨2021858, by rfl⟩ : syracuseStep 2695811 = 4043717) B4043717
theorem B2695841 : Blo 1796099 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B3031715 : Blo 1796099 3031715 := bstep (se 1 (by rfl) ⟨2273786, by rfl⟩ : syracuseStep 3031715 = 4547573) B4547573
theorem B4547249 : Blo 1796099 4547249 := bstep (se 2 (by rfl) ⟨1705218, by rfl⟩ : syracuseStep 4547249 = 3410437) B3410437
theorem B2695859 : Blo 1796099 2695859 := bstep (se 1 (by rfl) ⟨2021894, by rfl⟩ : syracuseStep 2695859 = 4043789) B4043789
theorem B2695889 : Blo 1796099 2695889 := bstep (se 2 (by rfl) ⟨1010958, by rfl⟩ : syracuseStep 2695889 = 2021917) B2021917
theorem B4547299 : Blo 1796099 4547299 := bstep (se 1 (by rfl) ⟨3410474, by rfl⟩ : syracuseStep 4547299 = 6820949) B6820949
theorem B2695907 : Blo 1796099 2695907 := bstep (se 1 (by rfl) ⟨2021930, by rfl⟩ : syracuseStep 2695907 = 4043861) B4043861
theorem B6144749 : Blo 1796099 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B2695937 : Blo 1796099 2695937 := bstep (se 2 (by rfl) ⟨1010976, by rfl⟩ : syracuseStep 2695937 = 2021953) B2021953
theorem B2695955 : Blo 1796099 2695955 := bstep (se 1 (by rfl) ⟨2021966, by rfl⟩ : syracuseStep 2695955 = 4043933) B4043933
theorem B3031843 : Blo 1796099 3031843 := bstep (se 1 (by rfl) ⟨2273882, by rfl⟩ : syracuseStep 3031843 = 4547765) B4547765
theorem B2695985 : Blo 1796099 2695985 := bstep (se 2 (by rfl) ⟨1010994, by rfl⟩ : syracuseStep 2695985 = 2021989) B2021989
theorem B2696003 : Blo 1796099 2696003 := bstep (se 1 (by rfl) ⟨2022002, by rfl⟩ : syracuseStep 2696003 = 4044005) B4044005
theorem B2696033 : Blo 1796099 2696033 := bstep (se 2 (by rfl) ⟨1011012, by rfl⟩ : syracuseStep 2696033 = 2022025) B2022025
theorem B6062957 : Blo 1796099 6062957 := bstep (se 3 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 6062957 = 2273609) B2273609
theorem B13640561 : Blo 1796099 13640561 := bstep (se 2 (by rfl) ⟨5115210, by rfl⟩ : syracuseStep 13640561 = 10230421) B10230421
theorem B4547441 : Blo 1796099 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B2696051 : Blo 1796099 2696051 := bstep (se 1 (by rfl) ⟨2022038, by rfl⟩ : syracuseStep 2696051 = 4044077) B4044077
theorem B17269645 : Blo 1796099 17269645 := bstep (se 3 (by rfl) ⟨3238058, by rfl⟩ : syracuseStep 17269645 = 6476117) B6476117
theorem B11518861 : Blo 1796099 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B2696081 : Blo 1796099 2696081 := bstep (se 2 (by rfl) ⟨1011030, by rfl⟩ : syracuseStep 2696081 = 2022061) B2022061
theorem B6063011 : Blo 1796099 6063011 := bstep (se 1 (by rfl) ⟨4547258, by rfl⟩ : syracuseStep 6063011 = 9094517) B9094517
theorem B2696099 : Blo 1796099 2696099 := bstep (se 1 (by rfl) ⟨2022074, by rfl⟩ : syracuseStep 2696099 = 4044149) B4044149
theorem B3031985 : Blo 1796099 3031985 := bstep (se 2 (by rfl) ⟨1136994, by rfl⟩ : syracuseStep 3031985 = 2273989) B2273989
theorem B7676849 : Blo 1796099 7676849 := bstep (se 2 (by rfl) ⟨2878818, by rfl⟩ : syracuseStep 7676849 = 5757637) B5757637
theorem B2696129 : Blo 1796099 2696129 := bstep (se 2 (by rfl) ⟨1011048, by rfl⟩ : syracuseStep 2696129 = 2022097) B2022097
theorem B6562765 : Blo 1796099 6562765 := bstep (se 3 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 6562765 = 2461037) B2461037
theorem B4858829 : Blo 1796099 4858829 := bstep (se 3 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 4858829 = 1822061) B1822061
theorem B2696147 : Blo 1796099 2696147 := bstep (se 1 (by rfl) ⟨2022110, by rfl⟩ : syracuseStep 2696147 = 4044221) B4044221
theorem B2696177 : Blo 1796099 2696177 := bstep (se 2 (by rfl) ⟨1011066, by rfl⟩ : syracuseStep 2696177 = 2022133) B2022133
theorem B2696195 : Blo 1796099 2696195 := bstep (se 1 (by rfl) ⟨2022146, by rfl⟩ : syracuseStep 2696195 = 4044293) B4044293
theorem B10232837 : Blo 1796099 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B2696225 : Blo 1796099 2696225 := bstep (se 2 (by rfl) ⟨1011084, by rfl⟩ : syracuseStep 2696225 = 2022169) B2022169
theorem B5760035 : Blo 1796099 5760035 := bstep (se 1 (by rfl) ⟨4320026, by rfl⟩ : syracuseStep 5760035 = 8640053) B8640053
theorem B9094193 : Blo 1796099 9094193 := bstep (se 2 (by rfl) ⟨3410322, by rfl⟩ : syracuseStep 9094193 = 6820645) B6820645
theorem B3032113 : Blo 1796099 3032113 := bstep (se 2 (by rfl) ⟨1137042, by rfl⟩ : syracuseStep 3032113 = 2274085) B2274085
theorem B2696243 : Blo 1796099 2696243 := bstep (se 1 (by rfl) ⟨2022182, by rfl⟩ : syracuseStep 2696243 = 4044365) B4044365
theorem B2769985 : Blo 1796099 2769985 := bstep (se 2 (by rfl) ⟨1038744, by rfl⟩ : syracuseStep 2769985 = 2077489) B2077489
theorem B2696273 : Blo 1796099 2696273 := bstep (se 2 (by rfl) ⟨1011102, by rfl⟩ : syracuseStep 2696273 = 2022205) B2022205
theorem B3032147 : Blo 1796099 3032147 := bstep (se 1 (by rfl) ⟨2274110, by rfl⟩ : syracuseStep 3032147 = 4548221) B4548221
theorem B14566499 : Blo 1796099 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B2696291 : Blo 1796099 2696291 := bstep (se 1 (by rfl) ⟨2022218, by rfl⟩ : syracuseStep 2696291 = 4044437) B4044437
theorem B2696321 : Blo 1796099 2696321 := bstep (se 2 (by rfl) ⟨1011120, by rfl⟩ : syracuseStep 2696321 = 2022241) B2022241
theorem B2188435 : Blo 1796099 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B2696339 : Blo 1796099 2696339 := bstep (se 1 (by rfl) ⟨2022254, by rfl⟩ : syracuseStep 2696339 = 4044509) B4044509
theorem B6063281 : Blo 1796099 6063281 := bstep (se 2 (by rfl) ⟨2273730, by rfl⟩ : syracuseStep 6063281 = 4547461) B4547461
theorem B2696369 : Blo 1796099 2696369 := bstep (se 2 (by rfl) ⟨1011138, by rfl⟩ : syracuseStep 2696369 = 2022277) B2022277
theorem B2696387 : Blo 1796099 2696387 := bstep (se 1 (by rfl) ⟨2022290, by rfl⟩ : syracuseStep 2696387 = 4044581) B4044581
theorem B3032275 : Blo 1796099 3032275 := bstep (se 1 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 3032275 = 4548413) B4548413
theorem B2696417 : Blo 1796099 2696417 := bstep (se 2 (by rfl) ⟨1011156, by rfl⟩ : syracuseStep 2696417 = 2022313) B2022313
theorem B2696435 : Blo 1796099 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B14017805 : Blo 1796099 14017805 := bstep (se 3 (by rfl) ⟨2628338, by rfl⟩ : syracuseStep 14017805 = 5256677) B5256677
theorem B2696465 : Blo 1796099 2696465 := bstep (se 2 (by rfl) ⟨1011174, by rfl⟩ : syracuseStep 2696465 = 2022349) B2022349
theorem B2696483 : Blo 1796099 2696483 := bstep (se 1 (by rfl) ⟨2022362, by rfl⟩ : syracuseStep 2696483 = 4044725) B4044725
theorem B2696513 : Blo 1796099 2696513 := bstep (se 2 (by rfl) ⟨1011192, by rfl⟩ : syracuseStep 2696513 = 2022385) B2022385
theorem B6825293 : Blo 1796099 6825293 := bstep (se 3 (by rfl) ⟨1279742, by rfl⟩ : syracuseStep 6825293 = 2559485) B2559485
theorem B2696531 : Blo 1796099 2696531 := bstep (se 1 (by rfl) ⟨2022398, by rfl⟩ : syracuseStep 2696531 = 4044797) B4044797
theorem B3032417 : Blo 1796099 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B2696561 : Blo 1796099 2696561 := bstep (se 2 (by rfl) ⟨1011210, by rfl⟩ : syracuseStep 2696561 = 2022421) B2022421
theorem B4613489 : Blo 1796099 4613489 := bstep (se 2 (by rfl) ⟨1730058, by rfl⟩ : syracuseStep 4613489 = 3460117) B3460117
theorem B2696579 : Blo 1796099 2696579 := bstep (se 1 (by rfl) ⟨2022434, by rfl⟩ : syracuseStep 2696579 = 4044869) B4044869
theorem B11511173 : Blo 1796099 11511173 := bstep (se 4 (by rfl) ⟨1079172, by rfl⟩ : syracuseStep 11511173 = 2158345) B2158345
theorem B2696609 : Blo 1796099 2696609 := bstep (se 2 (by rfl) ⟨1011228, by rfl⟩ : syracuseStep 2696609 = 2022457) B2022457
theorem B2696627 : Blo 1796099 2696627 := bstep (se 1 (by rfl) ⟨2022470, by rfl⟩ : syracuseStep 2696627 = 4044941) B4044941
theorem B2696657 : Blo 1796099 2696657 := bstep (se 2 (by rfl) ⟨1011246, by rfl⟩ : syracuseStep 2696657 = 2022493) B2022493
theorem B3032545 : Blo 1796099 3032545 := bstep (se 2 (by rfl) ⟨1137204, by rfl⟩ : syracuseStep 3032545 = 2274409) B2274409
theorem B2696675 : Blo 1796099 2696675 := bstep (se 1 (by rfl) ⟨2022506, by rfl⟩ : syracuseStep 2696675 = 4045013) B4045013
theorem B2696705 : Blo 1796099 2696705 := bstep (se 2 (by rfl) ⟨1011264, by rfl⟩ : syracuseStep 2696705 = 2022529) B2022529
theorem B3032579 : Blo 1796099 3032579 := bstep (se 1 (by rfl) ⟨2274434, by rfl⟩ : syracuseStep 3032579 = 4548869) B4548869
theorem B2696723 : Blo 1796099 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B2696753 : Blo 1796099 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B2696771 : Blo 1796099 2696771 := bstep (se 1 (by rfl) ⟨2022578, by rfl⟩ : syracuseStep 2696771 = 4045157) B4045157
theorem B2696801 : Blo 1796099 2696801 := bstep (se 2 (by rfl) ⟨1011300, by rfl⟩ : syracuseStep 2696801 = 2022601) B2022601
theorem B2696819 : Blo 1796099 2696819 := bstep (se 1 (by rfl) ⟨2022614, by rfl⟩ : syracuseStep 2696819 = 4045229) B4045229
theorem B3032707 : Blo 1796099 3032707 := bstep (se 1 (by rfl) ⟨2274530, by rfl⟩ : syracuseStep 3032707 = 4549061) B4549061
theorem B2696849 : Blo 1796099 2696849 := bstep (se 2 (by rfl) ⟨1011318, by rfl⟩ : syracuseStep 2696849 = 2022637) B2022637
theorem B2696867 : Blo 1796099 2696867 := bstep (se 1 (by rfl) ⟨2022650, by rfl⟩ : syracuseStep 2696867 = 4045301) B4045301
theorem B2696897 : Blo 1796099 2696897 := bstep (se 2 (by rfl) ⟨1011336, by rfl⟩ : syracuseStep 2696897 = 2022673) B2022673
theorem B6063821 : Blo 1796099 6063821 := bstep (se 3 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 6063821 = 2273933) B2273933
theorem B2557651 : Blo 1796099 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B2696915 : Blo 1796099 2696915 := bstep (se 1 (by rfl) ⟨2022686, by rfl⟩ : syracuseStep 2696915 = 4045373) B4045373
theorem B11077361 : Blo 1796099 11077361 := bstep (se 2 (by rfl) ⟨4154010, by rfl⟩ : syracuseStep 11077361 = 8308021) B8308021
theorem B2696945 : Blo 1796099 2696945 := bstep (se 2 (by rfl) ⟨1011354, by rfl⟩ : syracuseStep 2696945 = 2022709) B2022709
theorem B6063875 : Blo 1796099 6063875 := bstep (se 1 (by rfl) ⟨4547906, by rfl⟩ : syracuseStep 6063875 = 9095813) B9095813
theorem B4859651 : Blo 1796099 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B2696963 : Blo 1796099 2696963 := bstep (se 1 (by rfl) ⟨2022722, by rfl⟩ : syracuseStep 2696963 = 4045445) B4045445
theorem B3032849 : Blo 1796099 3032849 := bstep (se 2 (by rfl) ⟨1137318, by rfl⟩ : syracuseStep 3032849 = 2274637) B2274637
theorem B2696993 : Blo 1796099 2696993 := bstep (se 2 (by rfl) ⟨1011372, by rfl⟩ : syracuseStep 2696993 = 2022745) B2022745
theorem B2697011 : Blo 1796099 2697011 := bstep (se 1 (by rfl) ⟨2022758, by rfl⟩ : syracuseStep 2697011 = 4045517) B4045517
theorem B7677773 : Blo 1796099 7677773 := bstep (se 3 (by rfl) ⟨1439582, by rfl⟩ : syracuseStep 7677773 = 2879165) B2879165
theorem B4548433 : Blo 1796099 4548433 := bstep (se 2 (by rfl) ⟨1705662, by rfl⟩ : syracuseStep 4548433 = 3411325) B3411325
theorem B2697041 : Blo 1796099 2697041 := bstep (se 2 (by rfl) ⟨1011390, by rfl⟩ : syracuseStep 2697041 = 2022781) B2022781
theorem B4319075 : Blo 1796099 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2697059 : Blo 1796099 2697059 := bstep (se 1 (by rfl) ⟨2022794, by rfl⟩ : syracuseStep 2697059 = 4045589) B4045589
theorem B2697089 : Blo 1796099 2697089 := bstep (se 2 (by rfl) ⟨1011408, by rfl⟩ : syracuseStep 2697089 = 2022817) B2022817
theorem B3032977 : Blo 1796099 3032977 := bstep (se 2 (by rfl) ⟨1137366, by rfl⟩ : syracuseStep 3032977 = 2274733) B2274733
theorem B2697107 : Blo 1796099 2697107 := bstep (se 1 (by rfl) ⟨2022830, by rfl⟩ : syracuseStep 2697107 = 4045661) B4045661
theorem B2697137 : Blo 1796099 2697137 := bstep (se 2 (by rfl) ⟨1011426, by rfl⟩ : syracuseStep 2697137 = 2022853) B2022853
theorem B3033011 : Blo 1796099 3033011 := bstep (se 1 (by rfl) ⟨2274758, by rfl⟩ : syracuseStep 3033011 = 4549517) B4549517
theorem B1796099 : Blo 1796099 1796099 := bstep (se 1 (by rfl) ⟨1347074, by rfl⟩ : syracuseStep 1796099 = 2694149) B2694149
theorem B1820675 : Blo 1796099 1820675 := bstep (se 1 (by rfl) ⟨1365506, by rfl⟩ : syracuseStep 1820675 = 2731013) B2731013
theorem B6064145 : Blo 1796099 6064145 := bstep (se 2 (by rfl) ⟨2274054, by rfl⟩ : syracuseStep 6064145 = 4548109) B4548109
theorem B1796115 : Blo 1796099 1796115 := bstep (se 1 (by rfl) ⟨1347086, by rfl⟩ : syracuseStep 1796115 = 2694173) B2694173
theorem B1796131 : Blo 1796099 1796131 := bstep (se 1 (by rfl) ⟨1347098, by rfl⟩ : syracuseStep 1796131 = 2694197) B2694197
theorem B1796147 : Blo 1796099 1796147 := bstep (se 1 (by rfl) ⟨1347110, by rfl⟩ : syracuseStep 1796147 = 2694221) B2694221
theorem B3033139 : Blo 1796099 3033139 := bstep (se 1 (by rfl) ⟨2274854, by rfl⟩ : syracuseStep 3033139 = 4549709) B4549709
theorem B1796163 : Blo 1796099 1796163 := bstep (se 1 (by rfl) ⟨1347122, by rfl⟩ : syracuseStep 1796163 = 2694245) B2694245
theorem B1796179 : Blo 1796099 1796179 := bstep (se 1 (by rfl) ⟨1347134, by rfl⟩ : syracuseStep 1796179 = 2694269) B2694269
theorem B1796195 : Blo 1796099 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B4548707 : Blo 1796099 4548707 := bstep (se 1 (by rfl) ⟨3411530, by rfl⟩ : syracuseStep 4548707 = 6823061) B6823061
theorem B1796211 : Blo 1796099 1796211 := bstep (se 1 (by rfl) ⟨1347158, by rfl⟩ : syracuseStep 1796211 = 2694317) B2694317
theorem B1796227 : Blo 1796099 1796227 := bstep (se 1 (by rfl) ⟨1347170, by rfl⟩ : syracuseStep 1796227 = 2694341) B2694341
theorem B1796243 : Blo 1796099 1796243 := bstep (se 1 (by rfl) ⟨1347182, by rfl⟩ : syracuseStep 1796243 = 2694365) B2694365
theorem B3074195 : Blo 1796099 3074195 := bstep (se 1 (by rfl) ⟨2305646, by rfl⟩ : syracuseStep 3074195 = 4611293) B4611293
theorem B1796259 : Blo 1796099 1796259 := bstep (se 1 (by rfl) ⟨1347194, by rfl⟩ : syracuseStep 1796259 = 2694389) B2694389
theorem B1796275 : Blo 1796099 1796275 := bstep (se 1 (by rfl) ⟨1347206, by rfl⟩ : syracuseStep 1796275 = 2694413) B2694413
theorem B3033281 : Blo 1796099 3033281 := bstep (se 2 (by rfl) ⟨1137480, by rfl⟩ : syracuseStep 3033281 = 2274961) B2274961
theorem B1796291 : Blo 1796099 1796291 := bstep (se 1 (by rfl) ⟨1347218, by rfl⟩ : syracuseStep 1796291 = 2694437) B2694437
theorem B1796307 : Blo 1796099 1796307 := bstep (se 1 (by rfl) ⟨1347230, by rfl⟩ : syracuseStep 1796307 = 2694461) B2694461
theorem B2877665 : Blo 1796099 2877665 := bstep (se 2 (by rfl) ⟨1079124, by rfl⟩ : syracuseStep 2877665 = 2158249) B2158249
theorem B1796323 : Blo 1796099 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B4319459 : Blo 1796099 4319459 := bstep (se 1 (by rfl) ⟨3239594, by rfl⟩ : syracuseStep 4319459 = 6479189) B6479189
theorem B1796339 : Blo 1796099 1796339 := bstep (se 1 (by rfl) ⟨1347254, by rfl⟩ : syracuseStep 1796339 = 2694509) B2694509
theorem B1796355 : Blo 1796099 1796355 := bstep (se 1 (by rfl) ⟨1347266, by rfl⟩ : syracuseStep 1796355 = 2694533) B2694533
theorem B1796371 : Blo 1796099 1796371 := bstep (se 1 (by rfl) ⟨1347278, by rfl⟩ : syracuseStep 1796371 = 2694557) B2694557
theorem B1796387 : Blo 1796099 1796387 := bstep (se 1 (by rfl) ⟨1347290, by rfl⟩ : syracuseStep 1796387 = 2694581) B2694581
theorem B4548899 : Blo 1796099 4548899 := bstep (se 1 (by rfl) ⟨3411674, by rfl⟩ : syracuseStep 4548899 = 6823349) B6823349
theorem B5187889 : Blo 1796099 5187889 := bstep (se 2 (by rfl) ⟨1945458, by rfl⟩ : syracuseStep 5187889 = 3890917) B3890917
theorem B1796403 : Blo 1796099 1796403 := bstep (se 1 (by rfl) ⟨1347302, by rfl⟩ : syracuseStep 1796403 = 2694605) B2694605
theorem B3033409 : Blo 1796099 3033409 := bstep (se 2 (by rfl) ⟨1137528, by rfl⟩ : syracuseStep 3033409 = 2275057) B2275057
theorem B1796419 : Blo 1796099 1796419 := bstep (se 1 (by rfl) ⟨1347314, by rfl⟩ : syracuseStep 1796419 = 2694629) B2694629
theorem B3238211 : Blo 1796099 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B1796435 : Blo 1796099 1796435 := bstep (se 1 (by rfl) ⟨1347326, by rfl⟩ : syracuseStep 1796435 = 2694653) B2694653
theorem B1919315 : Blo 1796099 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B1796451 : Blo 1796099 1796451 := bstep (se 1 (by rfl) ⟨1347338, by rfl⟩ : syracuseStep 1796451 = 2694677) B2694677
theorem B3033443 : Blo 1796099 3033443 := bstep (se 1 (by rfl) ⟨2275082, by rfl⟩ : syracuseStep 3033443 = 4550165) B4550165
theorem B1796467 : Blo 1796099 1796467 := bstep (se 1 (by rfl) ⟨1347350, by rfl⟩ : syracuseStep 1796467 = 2694701) B2694701
theorem B1796483 : Blo 1796099 1796483 := bstep (se 1 (by rfl) ⟨1347362, by rfl⟩ : syracuseStep 1796483 = 2694725) B2694725
theorem B3074449 : Blo 1796099 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B1796499 : Blo 1796099 1796499 := bstep (se 1 (by rfl) ⟨1347374, by rfl⟩ : syracuseStep 1796499 = 2694749) B2694749
theorem B1796515 : Blo 1796099 1796515 := bstep (se 1 (by rfl) ⟨1347386, by rfl⟩ : syracuseStep 1796515 = 2694773) B2694773
theorem B3410353 : Blo 1796099 3410353 := bstep (se 2 (by rfl) ⟨1278882, by rfl⟩ : syracuseStep 3410353 = 2557765) B2557765
theorem B1796531 : Blo 1796099 1796531 := bstep (se 1 (by rfl) ⟨1347398, by rfl⟩ : syracuseStep 1796531 = 2694797) B2694797
theorem B1796547 : Blo 1796099 1796547 := bstep (se 1 (by rfl) ⟨1347410, by rfl⟩ : syracuseStep 1796547 = 2694821) B2694821
theorem B1796563 : Blo 1796099 1796563 := bstep (se 1 (by rfl) ⟨1347422, by rfl⟩ : syracuseStep 1796563 = 2694845) B2694845
theorem B1796579 : Blo 1796099 1796579 := bstep (se 1 (by rfl) ⟨1347434, by rfl⟩ : syracuseStep 1796579 = 2694869) B2694869
theorem B9095651 : Blo 1796099 9095651 := bstep (se 1 (by rfl) ⟨6821738, by rfl⟩ : syracuseStep 9095651 = 13643477) B13643477
theorem B5835235 : Blo 1796099 5835235 := bstep (se 1 (by rfl) ⟨4376426, by rfl⟩ : syracuseStep 5835235 = 8752853) B8752853
theorem B3033571 : Blo 1796099 3033571 := bstep (se 1 (by rfl) ⟨2275178, by rfl⟩ : syracuseStep 3033571 = 4550357) B4550357
theorem B1796595 : Blo 1796099 1796595 := bstep (se 1 (by rfl) ⟨1347446, by rfl⟩ : syracuseStep 1796595 = 2694893) B2694893
theorem B1796611 : Blo 1796099 1796611 := bstep (se 1 (by rfl) ⟨1347458, by rfl⟩ : syracuseStep 1796611 = 2694917) B2694917
theorem B4319747 : Blo 1796099 4319747 := bstep (se 1 (by rfl) ⟨3239810, by rfl⟩ : syracuseStep 4319747 = 6479621) B6479621
theorem B4041233 : Blo 1796099 4041233 := bstep (se 2 (by rfl) ⟨1515462, by rfl⟩ : syracuseStep 4041233 = 3030925) B3030925
theorem B1796627 : Blo 1796099 1796627 := bstep (se 1 (by rfl) ⟨1347470, by rfl⟩ : syracuseStep 1796627 = 2694941) B2694941
theorem B4041251 : Blo 1796099 4041251 := bstep (se 1 (by rfl) ⟨3030938, by rfl⟩ : syracuseStep 4041251 = 6061877) B6061877
theorem B1796643 : Blo 1796099 1796643 := bstep (se 1 (by rfl) ⟨1347482, by rfl⟩ : syracuseStep 1796643 = 2694965) B2694965
theorem B6064685 : Blo 1796099 6064685 := bstep (se 3 (by rfl) ⟨1137128, by rfl⟩ : syracuseStep 6064685 = 2274257) B2274257
theorem B1796659 : Blo 1796099 1796659 := bstep (se 1 (by rfl) ⟨1347494, by rfl⟩ : syracuseStep 1796659 = 2694989) B2694989
theorem B1796675 : Blo 1796099 1796675 := bstep (se 1 (by rfl) ⟨1347506, by rfl⟩ : syracuseStep 1796675 = 2695013) B2695013
theorem B1796691 : Blo 1796099 1796691 := bstep (se 1 (by rfl) ⟨1347518, by rfl⟩ : syracuseStep 1796691 = 2695037) B2695037
theorem B1796707 : Blo 1796099 1796707 := bstep (se 1 (by rfl) ⟨1347530, by rfl⟩ : syracuseStep 1796707 = 2695061) B2695061
theorem B6064739 : Blo 1796099 6064739 := bstep (se 1 (by rfl) ⟨4548554, by rfl⟩ : syracuseStep 6064739 = 9097109) B9097109
theorem B10930787 : Blo 1796099 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B3033713 : Blo 1796099 3033713 := bstep (se 2 (by rfl) ⟨1137642, by rfl⟩ : syracuseStep 3033713 = 2275285) B2275285
theorem B1796723 : Blo 1796099 1796723 := bstep (se 1 (by rfl) ⟨1347542, by rfl⟩ : syracuseStep 1796723 = 2695085) B2695085
theorem B1796739 : Blo 1796099 1796739 := bstep (se 1 (by rfl) ⟨1347554, by rfl⟩ : syracuseStep 1796739 = 2695109) B2695109
theorem B1796755 : Blo 1796099 1796755 := bstep (se 1 (by rfl) ⟨1347566, by rfl⟩ : syracuseStep 1796755 = 2695133) B2695133
theorem B1796771 : Blo 1796099 1796771 := bstep (se 1 (by rfl) ⟨1347578, by rfl⟩ : syracuseStep 1796771 = 2695157) B2695157
theorem B1796787 : Blo 1796099 1796787 := bstep (se 1 (by rfl) ⟨1347590, by rfl⟩ : syracuseStep 1796787 = 2695181) B2695181
theorem B1796803 : Blo 1796099 1796803 := bstep (se 1 (by rfl) ⟨1347602, by rfl⟩ : syracuseStep 1796803 = 2695205) B2695205
theorem B4926161 : Blo 1796099 4926161 := bstep (se 2 (by rfl) ⟨1847310, by rfl⟩ : syracuseStep 4926161 = 3694621) B3694621
theorem B1796819 : Blo 1796099 1796819 := bstep (se 1 (by rfl) ⟨1347614, by rfl⟩ : syracuseStep 1796819 = 2695229) B2695229
theorem B1796835 : Blo 1796099 1796835 := bstep (se 1 (by rfl) ⟨1347626, by rfl⟩ : syracuseStep 1796835 = 2695253) B2695253
theorem B3033841 : Blo 1796099 3033841 := bstep (se 2 (by rfl) ⟨1137690, by rfl⟩ : syracuseStep 3033841 = 2275381) B2275381
theorem B1796851 : Blo 1796099 1796851 := bstep (se 1 (by rfl) ⟨1347638, by rfl⟩ : syracuseStep 1796851 = 2695277) B2695277
theorem B1796867 : Blo 1796099 1796867 := bstep (se 1 (by rfl) ⟨1347650, by rfl⟩ : syracuseStep 1796867 = 2695301) B2695301
theorem B1796883 : Blo 1796099 1796883 := bstep (se 1 (by rfl) ⟨1347662, by rfl⟩ : syracuseStep 1796883 = 2695325) B2695325
theorem B3033875 : Blo 1796099 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B9710371 : Blo 1796099 9710371 := bstep (se 1 (by rfl) ⟨7282778, by rfl⟩ : syracuseStep 9710371 = 14565557) B14565557
theorem B1796899 : Blo 1796099 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B4041521 : Blo 1796099 4041521 := bstep (se 2 (by rfl) ⟨1515570, by rfl⟩ : syracuseStep 4041521 = 3031141) B3031141
theorem B1796915 : Blo 1796099 1796915 := bstep (se 1 (by rfl) ⟨1347686, by rfl⟩ : syracuseStep 1796915 = 2695373) B2695373
theorem B2558785 : Blo 1796099 2558785 := bstep (se 2 (by rfl) ⟨959544, by rfl⟩ : syracuseStep 2558785 = 1919089) B1919089
theorem B4041539 : Blo 1796099 4041539 := bstep (se 1 (by rfl) ⟨3031154, by rfl⟩ : syracuseStep 4041539 = 6062309) B6062309
theorem B1796931 : Blo 1796099 1796931 := bstep (se 1 (by rfl) ⟨1347698, by rfl⟩ : syracuseStep 1796931 = 2695397) B2695397
theorem B20474693 : Blo 1796099 20474693 := bstep (se 4 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 20474693 = 3839005) B3839005
theorem B1796947 : Blo 1796099 1796947 := bstep (se 1 (by rfl) ⟨1347710, by rfl⟩ : syracuseStep 1796947 = 2695421) B2695421
theorem B9710435 : Blo 1796099 9710435 := bstep (se 1 (by rfl) ⟨7282826, by rfl⟩ : syracuseStep 9710435 = 14565653) B14565653
theorem B1796963 : Blo 1796099 1796963 := bstep (se 1 (by rfl) ⟨1347722, by rfl⟩ : syracuseStep 1796963 = 2695445) B2695445
theorem B8637283 : Blo 1796099 8637283 := bstep (se 1 (by rfl) ⟨6477962, by rfl⟩ : syracuseStep 8637283 = 12955925) B12955925
theorem B6065009 : Blo 1796099 6065009 := bstep (se 2 (by rfl) ⟨2274378, by rfl⟩ : syracuseStep 6065009 = 4548757) B4548757
theorem B1796979 : Blo 1796099 1796979 := bstep (se 1 (by rfl) ⟨1347734, by rfl⟩ : syracuseStep 1796979 = 2695469) B2695469
theorem B5114755 : Blo 1796099 5114755 := bstep (se 1 (by rfl) ⟨3836066, by rfl⟩ : syracuseStep 5114755 = 7672133) B7672133
theorem B1796995 : Blo 1796099 1796995 := bstep (se 1 (by rfl) ⟨1347746, by rfl⟩ : syracuseStep 1796995 = 2695493) B2695493
theorem B1797011 : Blo 1796099 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B3034003 : Blo 1796099 3034003 := bstep (se 1 (by rfl) ⟨2275502, by rfl⟩ : syracuseStep 3034003 = 4551005) B4551005
theorem B2558881 : Blo 1796099 2558881 := bstep (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) B1919161
theorem B1797027 : Blo 1796099 1797027 := bstep (se 1 (by rfl) ⟨1347770, by rfl⟩ : syracuseStep 1797027 = 2695541) B2695541
theorem B5114801 : Blo 1796099 5114801 := bstep (se 2 (by rfl) ⟨1918050, by rfl⟩ : syracuseStep 5114801 = 3836101) B3836101
theorem B1797043 : Blo 1796099 1797043 := bstep (se 1 (by rfl) ⟨1347782, by rfl⟩ : syracuseStep 1797043 = 2695565) B2695565
theorem B1797059 : Blo 1796099 1797059 := bstep (se 1 (by rfl) ⟨1347794, by rfl⟩ : syracuseStep 1797059 = 2695589) B2695589
theorem B4320209 : Blo 1796099 4320209 := bstep (se 2 (by rfl) ⟨1620078, by rfl⟩ : syracuseStep 4320209 = 3240157) B3240157
theorem B1797075 : Blo 1796099 1797075 := bstep (se 1 (by rfl) ⟨1347806, by rfl⟩ : syracuseStep 1797075 = 2695613) B2695613
theorem B9710563 : Blo 1796099 9710563 := bstep (se 1 (by rfl) ⟨7282922, by rfl⟩ : syracuseStep 9710563 = 14565845) B14565845
theorem B1797091 : Blo 1796099 1797091 := bstep (se 1 (by rfl) ⟨1347818, by rfl⟩ : syracuseStep 1797091 = 2695637) B2695637
theorem B1797107 : Blo 1796099 1797107 := bstep (se 1 (by rfl) ⟨1347830, by rfl⟩ : syracuseStep 1797107 = 2695661) B2695661
theorem B1797123 : Blo 1796099 1797123 := bstep (se 1 (by rfl) ⟨1347842, by rfl⟩ : syracuseStep 1797123 = 2695685) B2695685
theorem B1797139 : Blo 1796099 1797139 := bstep (se 1 (by rfl) ⟨1347854, by rfl⟩ : syracuseStep 1797139 = 2695709) B2695709
theorem B3034145 : Blo 1796099 3034145 := bstep (se 2 (by rfl) ⟨1137804, by rfl⟩ : syracuseStep 3034145 = 2275609) B2275609
theorem B2878499 : Blo 1796099 2878499 := bstep (se 1 (by rfl) ⟨2158874, by rfl⟩ : syracuseStep 2878499 = 4317749) B4317749
theorem B1797155 : Blo 1796099 1797155 := bstep (se 1 (by rfl) ⟨1347866, by rfl⟩ : syracuseStep 1797155 = 2695733) B2695733
theorem B1797171 : Blo 1796099 1797171 := bstep (se 1 (by rfl) ⟨1347878, by rfl⟩ : syracuseStep 1797171 = 2695757) B2695757
theorem B1797187 : Blo 1796099 1797187 := bstep (se 1 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 1797187 = 2695781) B2695781
theorem B4041809 : Blo 1796099 4041809 := bstep (se 2 (by rfl) ⟨1515678, by rfl⟩ : syracuseStep 4041809 = 3031357) B3031357
theorem B1797203 : Blo 1796099 1797203 := bstep (se 1 (by rfl) ⟨1347902, by rfl⟩ : syracuseStep 1797203 = 2695805) B2695805
theorem B4041827 : Blo 1796099 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B1797219 : Blo 1796099 1797219 := bstep (se 1 (by rfl) ⟨1347914, by rfl⟩ : syracuseStep 1797219 = 2695829) B2695829
theorem B3837041 : Blo 1796099 3837041 := bstep (se 2 (by rfl) ⟨1438890, by rfl⟩ : syracuseStep 3837041 = 2877781) B2877781
theorem B1797235 : Blo 1796099 1797235 := bstep (se 1 (by rfl) ⟨1347926, by rfl⟩ : syracuseStep 1797235 = 2695853) B2695853
theorem B1797251 : Blo 1796099 1797251 := bstep (se 1 (by rfl) ⟨1347938, by rfl⟩ : syracuseStep 1797251 = 2695877) B2695877
theorem B1797267 : Blo 1796099 1797267 := bstep (se 1 (by rfl) ⟨1347950, by rfl⟩ : syracuseStep 1797267 = 2695901) B2695901
theorem B3034273 : Blo 1796099 3034273 := bstep (se 2 (by rfl) ⟨1137852, by rfl⟩ : syracuseStep 3034273 = 2275705) B2275705
theorem B1797283 : Blo 1796099 1797283 := bstep (se 1 (by rfl) ⟨1347962, by rfl⟩ : syracuseStep 1797283 = 2695925) B2695925
theorem B1797299 : Blo 1796099 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B1797315 : Blo 1796099 1797315 := bstep (se 1 (by rfl) ⟨1347986, by rfl⟩ : syracuseStep 1797315 = 2695973) B2695973
theorem B4549841 : Blo 1796099 4549841 := bstep (se 2 (by rfl) ⟨1706190, by rfl⟩ : syracuseStep 4549841 = 3412381) B3412381
theorem B1797331 : Blo 1796099 1797331 := bstep (se 1 (by rfl) ⟨1347998, by rfl⟩ : syracuseStep 1797331 = 2695997) B2695997
theorem B1797347 : Blo 1796099 1797347 := bstep (se 1 (by rfl) ⟨1348010, by rfl⟩ : syracuseStep 1797347 = 2696021) B2696021
theorem B1797363 : Blo 1796099 1797363 := bstep (se 1 (by rfl) ⟨1348022, by rfl⟩ : syracuseStep 1797363 = 2696045) B2696045
theorem B3075329 : Blo 1796099 3075329 := bstep (se 2 (by rfl) ⟨1153248, by rfl⟩ : syracuseStep 3075329 = 2306497) B2306497
theorem B1797379 : Blo 1796099 1797379 := bstep (se 1 (by rfl) ⟨1348034, by rfl⟩ : syracuseStep 1797379 = 2696069) B2696069
theorem B4549891 : Blo 1796099 4549891 := bstep (se 1 (by rfl) ⟨3412418, by rfl⟩ : syracuseStep 4549891 = 6824837) B6824837
theorem B9096461 : Blo 1796099 9096461 := bstep (se 3 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 9096461 = 3411173) B3411173
theorem B1797395 : Blo 1796099 1797395 := bstep (se 1 (by rfl) ⟨1348046, by rfl⟩ : syracuseStep 1797395 = 2696093) B2696093
theorem B1797411 : Blo 1796099 1797411 := bstep (se 1 (by rfl) ⟨1348058, by rfl⟩ : syracuseStep 1797411 = 2696117) B2696117
theorem B6147377 : Blo 1796099 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B1797427 : Blo 1796099 1797427 := bstep (se 1 (by rfl) ⟨1348070, by rfl⟩ : syracuseStep 1797427 = 2696141) B2696141
theorem B2878787 : Blo 1796099 2878787 := bstep (se 1 (by rfl) ⟨2159090, by rfl⟩ : syracuseStep 2878787 = 4318181) B4318181
theorem B1797443 : Blo 1796099 1797443 := bstep (se 1 (by rfl) ⟨1348082, by rfl⟩ : syracuseStep 1797443 = 2696165) B2696165
theorem B1797459 : Blo 1796099 1797459 := bstep (se 1 (by rfl) ⟨1348094, by rfl⟩ : syracuseStep 1797459 = 2696189) B2696189
theorem B1797475 : Blo 1796099 1797475 := bstep (se 1 (by rfl) ⟨1348106, by rfl⟩ : syracuseStep 1797475 = 2696213) B2696213
theorem B4042097 : Blo 1796099 4042097 := bstep (se 2 (by rfl) ⟨1515786, by rfl⟩ : syracuseStep 4042097 = 3031573) B3031573
theorem B1797491 : Blo 1796099 1797491 := bstep (se 1 (by rfl) ⟨1348118, by rfl⟩ : syracuseStep 1797491 = 2696237) B2696237
theorem B4042115 : Blo 1796099 4042115 := bstep (se 1 (by rfl) ⟨3031586, by rfl⟩ : syracuseStep 4042115 = 6063173) B6063173
theorem B1797507 : Blo 1796099 1797507 := bstep (se 1 (by rfl) ⟨1348130, by rfl⟩ : syracuseStep 1797507 = 2696261) B2696261
theorem B6065549 : Blo 1796099 6065549 := bstep (se 3 (by rfl) ⟨1137290, by rfl⟩ : syracuseStep 6065549 = 2274581) B2274581
theorem B2559377 : Blo 1796099 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B4550033 : Blo 1796099 4550033 := bstep (se 2 (by rfl) ⟨1706262, by rfl⟩ : syracuseStep 4550033 = 3412525) B3412525
theorem B1797523 : Blo 1796099 1797523 := bstep (se 1 (by rfl) ⟨1348142, by rfl⟩ : syracuseStep 1797523 = 2696285) B2696285
theorem B1797539 : Blo 1796099 1797539 := bstep (se 1 (by rfl) ⟨1348154, by rfl⟩ : syracuseStep 1797539 = 2696309) B2696309
theorem B1797555 : Blo 1796099 1797555 := bstep (se 1 (by rfl) ⟨1348166, by rfl⟩ : syracuseStep 1797555 = 2696333) B2696333
theorem B6065603 : Blo 1796099 6065603 := bstep (se 1 (by rfl) ⟨4549202, by rfl⟩ : syracuseStep 6065603 = 9098405) B9098405
theorem B1797571 : Blo 1796099 1797571 := bstep (se 1 (by rfl) ⟨1348178, by rfl⟩ : syracuseStep 1797571 = 2696357) B2696357
theorem B3239363 : Blo 1796099 3239363 := bstep (se 1 (by rfl) ⟨2429522, by rfl⟩ : syracuseStep 3239363 = 4859045) B4859045
theorem B3411409 : Blo 1796099 3411409 := bstep (se 2 (by rfl) ⟨1279278, by rfl⟩ : syracuseStep 3411409 = 2558557) B2558557
theorem B1797587 : Blo 1796099 1797587 := bstep (se 1 (by rfl) ⟨1348190, by rfl⟩ : syracuseStep 1797587 = 2696381) B2696381
theorem B1797603 : Blo 1796099 1797603 := bstep (se 1 (by rfl) ⟨1348202, by rfl⟩ : syracuseStep 1797603 = 2696405) B2696405
theorem B1797619 : Blo 1796099 1797619 := bstep (se 1 (by rfl) ⟨1348214, by rfl⟩ : syracuseStep 1797619 = 2696429) B2696429
theorem B1797635 : Blo 1796099 1797635 := bstep (se 1 (by rfl) ⟨1348226, by rfl⟩ : syracuseStep 1797635 = 2696453) B2696453
theorem B1797651 : Blo 1796099 1797651 := bstep (se 1 (by rfl) ⟨1348238, by rfl⟩ : syracuseStep 1797651 = 2696477) B2696477
theorem B2879011 : Blo 1796099 2879011 := bstep (se 1 (by rfl) ⟨2159258, by rfl⟩ : syracuseStep 2879011 = 4318517) B4318517
theorem B1797667 : Blo 1796099 1797667 := bstep (se 1 (by rfl) ⟨1348250, by rfl⟩ : syracuseStep 1797667 = 2696501) B2696501
theorem B1797683 : Blo 1796099 1797683 := bstep (se 1 (by rfl) ⟨1348262, by rfl⟩ : syracuseStep 1797683 = 2696525) B2696525
theorem B1797699 : Blo 1796099 1797699 := bstep (se 1 (by rfl) ⟨1348274, by rfl⟩ : syracuseStep 1797699 = 2696549) B2696549
theorem B1797715 : Blo 1796099 1797715 := bstep (se 1 (by rfl) ⟨1348286, by rfl⟩ : syracuseStep 1797715 = 2696573) B2696573
theorem B1797731 : Blo 1796099 1797731 := bstep (se 1 (by rfl) ⟨1348298, by rfl⟩ : syracuseStep 1797731 = 2696597) B2696597
theorem B1797747 : Blo 1796099 1797747 := bstep (se 1 (by rfl) ⟨1348310, by rfl⟩ : syracuseStep 1797747 = 2696621) B2696621
theorem B1797763 : Blo 1796099 1797763 := bstep (se 1 (by rfl) ⟨1348322, by rfl⟩ : syracuseStep 1797763 = 2696645) B2696645
theorem B4042385 : Blo 1796099 4042385 := bstep (se 2 (by rfl) ⟨1515894, by rfl⟩ : syracuseStep 4042385 = 3031789) B3031789
theorem B1797779 : Blo 1796099 1797779 := bstep (se 1 (by rfl) ⟨1348334, by rfl⟩ : syracuseStep 1797779 = 2696669) B2696669
theorem B4042403 : Blo 1796099 4042403 := bstep (se 1 (by rfl) ⟨3031802, by rfl⟩ : syracuseStep 4042403 = 6063605) B6063605
theorem B6475427 : Blo 1796099 6475427 := bstep (se 1 (by rfl) ⟨4856570, by rfl⟩ : syracuseStep 6475427 = 9713141) B9713141
theorem B1797795 : Blo 1796099 1797795 := bstep (se 1 (by rfl) ⟨1348346, by rfl⟩ : syracuseStep 1797795 = 2696693) B2696693
theorem B9719473 : Blo 1796099 9719473 := bstep (se 2 (by rfl) ⟨3644802, by rfl⟩ : syracuseStep 9719473 = 7289605) B7289605
theorem B1797811 : Blo 1796099 1797811 := bstep (se 1 (by rfl) ⟨1348358, by rfl⟩ : syracuseStep 1797811 = 2696717) B2696717
theorem B1797827 : Blo 1796099 1797827 := bstep (se 1 (by rfl) ⟨1348370, by rfl⟩ : syracuseStep 1797827 = 2696741) B2696741
theorem B6065873 : Blo 1796099 6065873 := bstep (se 2 (by rfl) ⟨2274702, by rfl⟩ : syracuseStep 6065873 = 4549405) B4549405
theorem B1797843 : Blo 1796099 1797843 := bstep (se 1 (by rfl) ⟨1348382, by rfl⟩ : syracuseStep 1797843 = 2696765) B2696765
theorem B1797859 : Blo 1796099 1797859 := bstep (se 1 (by rfl) ⟨1348394, by rfl⟩ : syracuseStep 1797859 = 2696789) B2696789
theorem B1797875 : Blo 1796099 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B1797891 : Blo 1796099 1797891 := bstep (se 1 (by rfl) ⟨1348418, by rfl⟩ : syracuseStep 1797891 = 2696837) B2696837
theorem B1797907 : Blo 1796099 1797907 := bstep (se 1 (by rfl) ⟨1348430, by rfl⟩ : syracuseStep 1797907 = 2696861) B2696861
theorem B1797923 : Blo 1796099 1797923 := bstep (se 1 (by rfl) ⟨1348442, by rfl⟩ : syracuseStep 1797923 = 2696885) B2696885
theorem B1797939 : Blo 1796099 1797939 := bstep (se 1 (by rfl) ⟨1348454, by rfl⟩ : syracuseStep 1797939 = 2696909) B2696909
theorem B1797955 : Blo 1796099 1797955 := bstep (se 1 (by rfl) ⟨1348466, by rfl⟩ : syracuseStep 1797955 = 2696933) B2696933
theorem B1797971 : Blo 1796099 1797971 := bstep (se 1 (by rfl) ⟨1348478, by rfl⟩ : syracuseStep 1797971 = 2696957) B2696957
theorem B3411811 : Blo 1796099 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B1797987 : Blo 1796099 1797987 := bstep (se 1 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 1797987 = 2696981) B2696981
theorem B1798003 : Blo 1796099 1798003 := bstep (se 1 (by rfl) ⟨1348502, by rfl⟩ : syracuseStep 1798003 = 2697005) B2697005
theorem B1798019 : Blo 1796099 1798019 := bstep (se 1 (by rfl) ⟨1348514, by rfl⟩ : syracuseStep 1798019 = 2697029) B2697029
theorem B3411857 : Blo 1796099 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B1798035 : Blo 1796099 1798035 := bstep (se 1 (by rfl) ⟨1348526, by rfl⟩ : syracuseStep 1798035 = 2697053) B2697053
theorem B2158499 : Blo 1796099 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B1798051 : Blo 1796099 1798051 := bstep (se 1 (by rfl) ⟨1348538, by rfl⟩ : syracuseStep 1798051 = 2697077) B2697077
theorem B4042673 : Blo 1796099 4042673 := bstep (se 2 (by rfl) ⟨1516002, by rfl⟩ : syracuseStep 4042673 = 3032005) B3032005
theorem B1798067 : Blo 1796099 1798067 := bstep (se 1 (by rfl) ⟨1348550, by rfl⟩ : syracuseStep 1798067 = 2697101) B2697101
theorem B4042691 : Blo 1796099 4042691 := bstep (se 1 (by rfl) ⟨3032018, by rfl⟩ : syracuseStep 4042691 = 6064037) B6064037
theorem B1798083 : Blo 1796099 1798083 := bstep (se 1 (by rfl) ⟨1348562, by rfl⟩ : syracuseStep 1798083 = 2697125) B2697125
theorem B1798099 : Blo 1796099 1798099 := bstep (se 1 (by rfl) ⟨1348574, by rfl⟩ : syracuseStep 1798099 = 2697149) B2697149
theorem B2732033 : Blo 1796099 2732033 := bstep (se 2 (by rfl) ⟨1024512, by rfl⟩ : syracuseStep 2732033 = 2049025) B2049025
theorem B6230029 : Blo 1796099 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B3412145 : Blo 1796099 3412145 := bstep (se 2 (by rfl) ⟨1279554, by rfl⟩ : syracuseStep 3412145 = 2559109) B2559109
theorem B4042961 : Blo 1796099 4042961 := bstep (se 2 (by rfl) ⟨1516110, by rfl⟩ : syracuseStep 4042961 = 3032221) B3032221
theorem B4042979 : Blo 1796099 4042979 := bstep (se 1 (by rfl) ⟨3032234, by rfl⟩ : syracuseStep 4042979 = 6064469) B6064469
theorem B6066413 : Blo 1796099 6066413 := bstep (se 3 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 6066413 = 2274905) B2274905
theorem B2879729 : Blo 1796099 2879729 := bstep (se 2 (by rfl) ⟨1079898, by rfl⟩ : syracuseStep 2879729 = 2159797) B2159797
theorem B6066467 : Blo 1796099 6066467 := bstep (se 1 (by rfl) ⟨4549850, by rfl⟩ : syracuseStep 6066467 = 9099701) B9099701
theorem B6820145 : Blo 1796099 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B7778609 : Blo 1796099 7778609 := bstep (se 2 (by rfl) ⟨2916978, by rfl⟩ : syracuseStep 7778609 = 5833957) B5833957
theorem B24580421 : Blo 1796099 24580421 := bstep (se 4 (by rfl) ⟨2304414, by rfl⟩ : syracuseStep 24580421 = 4608829) B4608829
theorem B10514765 : Blo 1796099 10514765 := bstep (se 3 (by rfl) ⟨1971518, by rfl⟩ : syracuseStep 10514765 = 3943037) B3943037
theorem B5116259 : Blo 1796099 5116259 := bstep (se 1 (by rfl) ⟨3837194, by rfl⟩ : syracuseStep 5116259 = 7674389) B7674389
theorem B4551025 : Blo 1796099 4551025 := bstep (se 2 (by rfl) ⟨1706634, by rfl⟩ : syracuseStep 4551025 = 3413269) B3413269
theorem B2732435 : Blo 1796099 2732435 := bstep (se 1 (by rfl) ⟨2049326, by rfl⟩ : syracuseStep 2732435 = 4098653) B4098653
theorem B2879921 : Blo 1796099 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B4043249 : Blo 1796099 4043249 := bstep (se 2 (by rfl) ⟨1516218, by rfl⟩ : syracuseStep 4043249 = 3032437) B3032437
theorem B4043267 : Blo 1796099 4043267 := bstep (se 1 (by rfl) ⟨3032450, by rfl⟩ : syracuseStep 4043267 = 6064901) B6064901
theorem B2273827 : Blo 1796099 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B6066737 : Blo 1796099 6066737 := bstep (se 2 (by rfl) ⟨2275026, by rfl⟩ : syracuseStep 6066737 = 4550053) B4550053
theorem B2880049 : Blo 1796099 2880049 := bstep (se 2 (by rfl) ⟨1080018, by rfl⟩ : syracuseStep 2880049 = 2160037) B2160037
theorem B2273923 : Blo 1796099 2273923 := bstep (se 1 (by rfl) ⟨1705442, by rfl⟩ : syracuseStep 2273923 = 3410885) B3410885
theorem B3838595 : Blo 1796099 3838595 := bstep (se 1 (by rfl) ⟨2878946, by rfl⟩ : syracuseStep 3838595 = 5757893) B5757893
theorem B4551299 : Blo 1796099 4551299 := bstep (se 1 (by rfl) ⟨3413474, by rfl⟩ : syracuseStep 4551299 = 6826949) B6826949
theorem B98587363 : Blo 1796099 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B4043537 : Blo 1796099 4043537 := bstep (se 2 (by rfl) ⟨1516326, by rfl⟩ : syracuseStep 4043537 = 3032653) B3032653
theorem B4043555 : Blo 1796099 4043555 := bstep (se 1 (by rfl) ⟨3032666, by rfl⟩ : syracuseStep 4043555 = 6065333) B6065333
theorem B11514737 : Blo 1796099 11514737 := bstep (se 2 (by rfl) ⟨4318026, by rfl⟩ : syracuseStep 11514737 = 8636053) B8636053
theorem B3412867 : Blo 1796099 3412867 := bstep (se 1 (by rfl) ⟨2559650, by rfl⟩ : syracuseStep 3412867 = 5119301) B5119301
theorem B2732945 : Blo 1796099 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B6476707 : Blo 1796099 6476707 := bstep (se 1 (by rfl) ⟨4857530, by rfl⟩ : syracuseStep 6476707 = 9715061) B9715061
theorem B4043825 : Blo 1796099 4043825 := bstep (se 2 (by rfl) ⟨1516434, by rfl⟩ : syracuseStep 4043825 = 3032869) B3032869
theorem B4043843 : Blo 1796099 4043843 := bstep (se 1 (by rfl) ⟨3032882, by rfl⟩ : syracuseStep 4043843 = 6065765) B6065765
theorem B6067277 : Blo 1796099 6067277 := bstep (se 3 (by rfl) ⟨1137614, by rfl⟩ : syracuseStep 6067277 = 2275229) B2275229
theorem B2274419 : Blo 1796099 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B3642499 : Blo 1796099 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B6067331 : Blo 1796099 6067331 := bstep (se 1 (by rfl) ⟨4550498, by rfl⟩ : syracuseStep 6067331 = 9100997) B9100997
theorem B4609219 : Blo 1796099 4609219 := bstep (se 1 (by rfl) ⟨3456914, by rfl⟩ : syracuseStep 4609219 = 6913829) B6913829
theorem B2733281 : Blo 1796099 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B5756177 : Blo 1796099 5756177 := bstep (se 2 (by rfl) ⟨2158566, by rfl⟩ : syracuseStep 5756177 = 4317133) B4317133
theorem B2020675 : Blo 1796099 2020675 := bstep (se 1 (by rfl) ⟨1515506, by rfl⟩ : syracuseStep 2020675 = 3031013) B3031013
theorem B3413315 : Blo 1796099 3413315 := bstep (se 1 (by rfl) ⟨2559986, by rfl⟩ : syracuseStep 3413315 = 5119973) B5119973
theorem B15570245 : Blo 1796099 15570245 := bstep (se 4 (by rfl) ⟨1459710, by rfl⟩ : syracuseStep 15570245 = 2919421) B2919421
theorem B4044113 : Blo 1796099 4044113 := bstep (se 2 (by rfl) ⟨1516542, by rfl⟩ : syracuseStep 4044113 = 3033085) B3033085
theorem B4044131 : Blo 1796099 4044131 := bstep (se 1 (by rfl) ⟨3033098, by rfl⟩ : syracuseStep 4044131 = 6066197) B6066197
theorem B5756305 : Blo 1796099 5756305 := bstep (se 2 (by rfl) ⟨2158614, by rfl⟩ : syracuseStep 5756305 = 4317229) B4317229
theorem B6067601 : Blo 1796099 6067601 := bstep (se 2 (by rfl) ⟨2275350, by rfl⟩ : syracuseStep 6067601 = 4550701) B4550701
theorem B2733475 : Blo 1796099 2733475 := bstep (se 1 (by rfl) ⟨2050106, by rfl⟩ : syracuseStep 2733475 = 4100213) B4100213
theorem B4609457 : Blo 1796099 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2020819 : Blo 1796099 2020819 := bstep (se 1 (by rfl) ⟨1515614, by rfl⟩ : syracuseStep 2020819 = 3031229) B3031229
theorem B5117489 : Blo 1796099 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B2020963 : Blo 1796099 2020963 := bstep (se 1 (by rfl) ⟨1515722, by rfl⟩ : syracuseStep 2020963 = 3031445) B3031445
theorem B12949091 : Blo 1796099 12949091 := bstep (se 1 (by rfl) ⟨9711818, by rfl⟩ : syracuseStep 12949091 = 19423637) B19423637
theorem B4044401 : Blo 1796099 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B4044419 : Blo 1796099 4044419 := bstep (se 1 (by rfl) ⟨3033314, by rfl⟩ : syracuseStep 4044419 = 6066629) B6066629
theorem B39909005 : Blo 1796099 39909005 := bstep (se 3 (by rfl) ⟨7482938, by rfl⟩ : syracuseStep 39909005 = 14965877) B14965877
theorem B5756561 : Blo 1796099 5756561 := bstep (se 2 (by rfl) ⟨2158710, by rfl⟩ : syracuseStep 5756561 = 4317421) B4317421
theorem B12302029 : Blo 1796099 12302029 := bstep (se 3 (by rfl) ⟨2306630, by rfl⟩ : syracuseStep 12302029 = 4613261) B4613261
theorem B6821603 : Blo 1796099 6821603 := bstep (se 1 (by rfl) ⟨5116202, by rfl⟩ : syracuseStep 6821603 = 10232405) B10232405
theorem B10229489 : Blo 1796099 10229489 := bstep (se 2 (by rfl) ⟨3836058, by rfl⟩ : syracuseStep 10229489 = 7672117) B7672117
theorem B6821617 : Blo 1796099 6821617 := bstep (se 2 (by rfl) ⟨2558106, by rfl⟩ : syracuseStep 6821617 = 5116213) B5116213
theorem B2021107 : Blo 1796099 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B4855565 : Blo 1796099 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B2275123 : Blo 1796099 2275123 := bstep (se 1 (by rfl) ⟨1706342, by rfl⟩ : syracuseStep 2275123 = 3412685) B3412685
theorem B4855619 : Blo 1796099 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B2021251 : Blo 1796099 2021251 := bstep (se 1 (by rfl) ⟨1515938, by rfl⟩ : syracuseStep 2021251 = 3031877) B3031877
theorem B22763405 : Blo 1796099 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B4044689 : Blo 1796099 4044689 := bstep (se 2 (by rfl) ⟨1516758, by rfl⟩ : syracuseStep 4044689 = 3033517) B3033517
theorem B2275219 : Blo 1796099 2275219 := bstep (se 1 (by rfl) ⟨1706414, by rfl⟩ : syracuseStep 2275219 = 3412829) B3412829
theorem B4044707 : Blo 1796099 4044707 := bstep (se 1 (by rfl) ⟨3033530, by rfl⟩ : syracuseStep 4044707 = 6067061) B6067061
theorem B6068141 : Blo 1796099 6068141 := bstep (se 3 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 6068141 = 2275553) B2275553
theorem B6068195 : Blo 1796099 6068195 := bstep (se 1 (by rfl) ⟨4551146, by rfl⟩ : syracuseStep 6068195 = 9102293) B9102293
theorem B9713677 : Blo 1796099 9713677 := bstep (se 3 (by rfl) ⟨1821314, by rfl⟩ : syracuseStep 9713677 = 3642629) B3642629
theorem B2021395 : Blo 1796099 2021395 := bstep (se 1 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 2021395 = 3032093) B3032093
theorem B19429429 : Blo 1796099 19429429 := bstep (se 5 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 19429429 = 1821509) B1821509
theorem B9099377 : Blo 1796099 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B2021539 : Blo 1796099 2021539 := bstep (se 1 (by rfl) ⟨1516154, by rfl⟩ : syracuseStep 2021539 = 3032309) B3032309
theorem B4044977 : Blo 1796099 4044977 := bstep (se 2 (by rfl) ⟨1516866, by rfl⟩ : syracuseStep 4044977 = 3033733) B3033733
theorem B4044995 : Blo 1796099 4044995 := bstep (se 1 (by rfl) ⟨3033746, by rfl⟩ : syracuseStep 4044995 = 6067493) B6067493
theorem B6068465 : Blo 1796099 6068465 := bstep (se 2 (by rfl) ⟨2275674, by rfl⟩ : syracuseStep 6068465 = 4551349) B4551349
theorem B4921613 : Blo 1796099 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B11516195 : Blo 1796099 11516195 := bstep (se 1 (by rfl) ⟨8637146, by rfl⟩ : syracuseStep 11516195 = 17274293) B17274293
theorem B2021683 : Blo 1796099 2021683 := bstep (se 1 (by rfl) ⟨1516262, by rfl⟩ : syracuseStep 2021683 = 3032525) B3032525
theorem B2275715 : Blo 1796099 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B2021827 : Blo 1796099 2021827 := bstep (se 1 (by rfl) ⟨1516370, by rfl⟩ : syracuseStep 2021827 = 3032741) B3032741
theorem B4045265 : Blo 1796099 4045265 := bstep (se 2 (by rfl) ⟨1516974, by rfl⟩ : syracuseStep 4045265 = 3033949) B3033949
theorem B2218451 : Blo 1796099 2218451 := bstep (se 1 (by rfl) ⟨1663838, by rfl⟩ : syracuseStep 2218451 = 3327677) B3327677
theorem B4045283 : Blo 1796099 4045283 := bstep (se 1 (by rfl) ⟨3033962, by rfl⟩ : syracuseStep 4045283 = 6067925) B6067925
theorem B2021971 : Blo 1796099 2021971 := bstep (se 1 (by rfl) ⟨1516478, by rfl⟩ : syracuseStep 2021971 = 3032957) B3032957
theorem B46701197 : Blo 1796099 46701197 := bstep (se 3 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 46701197 = 17512949) B17512949
theorem B10238669 : Blo 1796099 10238669 := bstep (se 3 (by rfl) ⟨1919750, by rfl⟩ : syracuseStep 10238669 = 3839501) B3839501
theorem B2022115 : Blo 1796099 2022115 := bstep (se 1 (by rfl) ⟨1516586, by rfl⟩ : syracuseStep 2022115 = 3033173) B3033173
theorem B4045553 : Blo 1796099 4045553 := bstep (se 2 (by rfl) ⟨1517082, by rfl⟩ : syracuseStep 4045553 = 3034165) B3034165
theorem B4045571 : Blo 1796099 4045571 := bstep (se 1 (by rfl) ⟨3034178, by rfl⟩ : syracuseStep 4045571 = 6068357) B6068357
theorem B2022259 : Blo 1796099 2022259 := bstep (se 1 (by rfl) ⟨1516694, by rfl⟩ : syracuseStep 2022259 = 3033389) B3033389
theorem B4856753 : Blo 1796099 4856753 := bstep (se 2 (by rfl) ⟨1821282, by rfl⟩ : syracuseStep 4856753 = 3642565) B3642565
theorem B4316113 : Blo 1796099 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B7674851 : Blo 1796099 7674851 := bstep (se 1 (by rfl) ⟨5756138, by rfl⟩ : syracuseStep 7674851 = 11512277) B11512277
theorem B23034851 : Blo 1796099 23034851 := bstep (se 1 (by rfl) ⟨17276138, by rfl⟩ : syracuseStep 23034851 = 34552277) B34552277
theorem B5118947 : Blo 1796099 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B2022403 : Blo 1796099 2022403 := bstep (se 1 (by rfl) ⟨1516802, by rfl⟩ : syracuseStep 2022403 = 3033605) B3033605
theorem B2694161 : Blo 1796099 2694161 := bstep (se 2 (by rfl) ⟨1010310, by rfl⟩ : syracuseStep 2694161 = 2020621) B2020621
theorem B2694179 : Blo 1796099 2694179 := bstep (se 1 (by rfl) ⟨2020634, by rfl⟩ : syracuseStep 2694179 = 4041269) B4041269
theorem B2694209 : Blo 1796099 2694209 := bstep (se 2 (by rfl) ⟨1010328, by rfl⟩ : syracuseStep 2694209 = 2020657) B2020657
theorem B2694227 : Blo 1796099 2694227 := bstep (se 1 (by rfl) ⟨2020670, by rfl⟩ : syracuseStep 2694227 = 4041341) B4041341
theorem B2694257 : Blo 1796099 2694257 := bstep (se 2 (by rfl) ⟨1010346, by rfl⟩ : syracuseStep 2694257 = 2020693) B2020693
theorem B2694275 : Blo 1796099 2694275 := bstep (se 1 (by rfl) ⟨2020706, by rfl⟩ : syracuseStep 2694275 = 4041413) B4041413
theorem B2022547 : Blo 1796099 2022547 := bstep (se 1 (by rfl) ⟨1516910, by rfl⟩ : syracuseStep 2022547 = 3033821) B3033821
theorem B2694305 : Blo 1796099 2694305 := bstep (se 2 (by rfl) ⟨1010364, by rfl⟩ : syracuseStep 2694305 = 2020729) B2020729
theorem B10230947 : Blo 1796099 10230947 := bstep (se 1 (by rfl) ⟨7673210, by rfl⟩ : syracuseStep 10230947 = 15346421) B15346421
theorem B6823075 : Blo 1796099 6823075 := bstep (se 1 (by rfl) ⟨5117306, by rfl⟩ : syracuseStep 6823075 = 10234613) B10234613
theorem B5463217 : Blo 1796099 5463217 := bstep (se 2 (by rfl) ⟨2048706, by rfl⟩ : syracuseStep 5463217 = 4097413) B4097413
theorem B2694323 : Blo 1796099 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B2694353 : Blo 1796099 2694353 := bstep (se 2 (by rfl) ⟨1010382, by rfl⟩ : syracuseStep 2694353 = 2020765) B2020765
theorem B2694371 : Blo 1796099 2694371 := bstep (se 1 (by rfl) ⟨2020778, by rfl⟩ : syracuseStep 2694371 = 4041557) B4041557
theorem B2694401 : Blo 1796099 2694401 := bstep (se 2 (by rfl) ⟨1010400, by rfl⟩ : syracuseStep 2694401 = 2020801) B2020801
theorem B2694419 : Blo 1796099 2694419 := bstep (se 1 (by rfl) ⟨2020814, by rfl⟩ : syracuseStep 2694419 = 4041629) B4041629
theorem B2022691 : Blo 1796099 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B5758253 : Blo 1796099 5758253 := bstep (se 3 (by rfl) ⟨1079672, by rfl⟩ : syracuseStep 5758253 = 2159345) B2159345
theorem B2694449 : Blo 1796099 2694449 := bstep (se 2 (by rfl) ⟨1010418, by rfl⟩ : syracuseStep 2694449 = 2020837) B2020837
theorem B2694467 : Blo 1796099 2694467 := bstep (se 1 (by rfl) ⟨2020850, by rfl⟩ : syracuseStep 2694467 = 4041701) B4041701
theorem B2694497 : Blo 1796099 2694497 := bstep (se 2 (by rfl) ⟨1010436, by rfl⟩ : syracuseStep 2694497 = 2020873) B2020873
theorem B2694515 : Blo 1796099 2694515 := bstep (se 1 (by rfl) ⟨2020886, by rfl⟩ : syracuseStep 2694515 = 4041773) B4041773
theorem B2694545 : Blo 1796099 2694545 := bstep (se 2 (by rfl) ⟨1010454, by rfl⟩ : syracuseStep 2694545 = 2020909) B2020909
theorem B2694563 : Blo 1796099 2694563 := bstep (se 1 (by rfl) ⟨2020922, by rfl⟩ : syracuseStep 2694563 = 4041845) B4041845
theorem B2022835 : Blo 1796099 2022835 := bstep (se 1 (by rfl) ⟨1517126, by rfl⟩ : syracuseStep 2022835 = 3034253) B3034253
theorem B20463029 : Blo 1796099 20463029 := bstep (se 5 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 20463029 = 1918409) B1918409
theorem B2694593 : Blo 1796099 2694593 := bstep (se 2 (by rfl) ⟨1010472, by rfl⟩ : syracuseStep 2694593 = 2020945) B2020945
theorem B4857293 : Blo 1796099 4857293 := bstep (se 3 (by rfl) ⟨910742, by rfl⟩ : syracuseStep 4857293 = 1821485) B1821485
theorem B2694611 : Blo 1796099 2694611 := bstep (se 1 (by rfl) ⟨2020958, by rfl⟩ : syracuseStep 2694611 = 4041917) B4041917
theorem B2694641 : Blo 1796099 2694641 := bstep (se 2 (by rfl) ⟨1010490, by rfl⟩ : syracuseStep 2694641 = 2020981) B2020981
theorem B2694659 : Blo 1796099 2694659 := bstep (se 1 (by rfl) ⟨2020994, by rfl⟩ : syracuseStep 2694659 = 4041989) B4041989
theorem B2694689 : Blo 1796099 2694689 := bstep (se 2 (by rfl) ⟨1010508, by rfl⟩ : syracuseStep 2694689 = 2021017) B2021017
theorem B9100835 : Blo 1796099 9100835 := bstep (se 1 (by rfl) ⟨6825626, by rfl⟩ : syracuseStep 9100835 = 13651253) B13651253
theorem B2694707 : Blo 1796099 2694707 := bstep (se 1 (by rfl) ⟨2021030, by rfl⟩ : syracuseStep 2694707 = 4042061) B4042061
theorem B2694737 : Blo 1796099 2694737 := bstep (se 2 (by rfl) ⟨1010526, by rfl⟩ : syracuseStep 2694737 = 2021053) B2021053
theorem B2694755 : Blo 1796099 2694755 := bstep (se 1 (by rfl) ⟨2021066, by rfl⟩ : syracuseStep 2694755 = 4042133) B4042133
theorem B2694785 : Blo 1796099 2694785 := bstep (se 2 (by rfl) ⟨1010544, by rfl⟩ : syracuseStep 2694785 = 2021089) B2021089
theorem B2694803 : Blo 1796099 2694803 := bstep (se 1 (by rfl) ⟨2021102, by rfl⟩ : syracuseStep 2694803 = 4042205) B4042205
theorem B2694833 : Blo 1796099 2694833 := bstep (se 2 (by rfl) ⟨1010562, by rfl⟩ : syracuseStep 2694833 = 2021125) B2021125
theorem B2694851 : Blo 1796099 2694851 := bstep (se 1 (by rfl) ⟨2021138, by rfl⟩ : syracuseStep 2694851 = 4042277) B4042277
theorem B2694881 : Blo 1796099 2694881 := bstep (se 2 (by rfl) ⟨1010580, by rfl⟩ : syracuseStep 2694881 = 2021161) B2021161
theorem B2694899 : Blo 1796099 2694899 := bstep (se 1 (by rfl) ⟨2021174, by rfl⟩ : syracuseStep 2694899 = 4042349) B4042349
theorem B5119757 : Blo 1796099 5119757 := bstep (se 3 (by rfl) ⟨959954, by rfl⟩ : syracuseStep 5119757 = 1919909) B1919909
theorem B2694929 : Blo 1796099 2694929 := bstep (se 2 (by rfl) ⟨1010598, by rfl⟩ : syracuseStep 2694929 = 2021197) B2021197
theorem B2694947 : Blo 1796099 2694947 := bstep (se 1 (by rfl) ⟨2021210, by rfl⟩ : syracuseStep 2694947 = 4042421) B4042421
theorem B2694977 : Blo 1796099 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B2694995 : Blo 1796099 2694995 := bstep (se 1 (by rfl) ⟨2021246, by rfl⟩ : syracuseStep 2694995 = 4042493) B4042493
theorem B2695025 : Blo 1796099 2695025 := bstep (se 2 (by rfl) ⟨1010634, by rfl⟩ : syracuseStep 2695025 = 2021269) B2021269
theorem B2695043 : Blo 1796099 2695043 := bstep (se 1 (by rfl) ⟨2021282, by rfl⟩ : syracuseStep 2695043 = 4042565) B4042565
theorem B2695073 : Blo 1796099 2695073 := bstep (se 2 (by rfl) ⟨1010652, by rfl⟩ : syracuseStep 2695073 = 2021305) B2021305
theorem B2695091 : Blo 1796099 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B3030979 : Blo 1796099 3030979 := bstep (se 1 (by rfl) ⟨2273234, by rfl⟩ : syracuseStep 3030979 = 4546469) B4546469
theorem B5119949 : Blo 1796099 5119949 := bstep (se 3 (by rfl) ⟨959990, by rfl⟩ : syracuseStep 5119949 = 1919981) B1919981
theorem B2695121 : Blo 1796099 2695121 := bstep (se 2 (by rfl) ⟨1010670, by rfl⟩ : syracuseStep 2695121 = 2021341) B2021341
theorem B2695139 : Blo 1796099 2695139 := bstep (se 1 (by rfl) ⟨2021354, by rfl⟩ : syracuseStep 2695139 = 4042709) B4042709
theorem B8306705 : Blo 1796099 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B12951569 : Blo 1796099 12951569 := bstep (se 2 (by rfl) ⟨4856838, by rfl⟩ : syracuseStep 12951569 = 9713677) B9713677
theorem B2695193 : Blo 1796099 2695193 := bstep (se 2 (by rfl) ⟨1010697, by rfl⟩ : syracuseStep 2695193 = 2021395) B2021395
theorem B2695307 : Blo 1796099 2695307 := bstep (se 1 (by rfl) ⟨2021480, by rfl⟩ : syracuseStep 2695307 = 4042961) B4042961
theorem B2695319 : Blo 1796099 2695319 := bstep (se 1 (by rfl) ⟨2021489, by rfl⟩ : syracuseStep 2695319 = 4042979) B4042979
theorem B4546763 : Blo 1796099 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B5185739 : Blo 1796099 5185739 := bstep (se 1 (by rfl) ⟨3889304, by rfl⟩ : syracuseStep 5185739 = 7778609) B7778609
theorem B2695385 : Blo 1796099 2695385 := bstep (se 2 (by rfl) ⟨1010769, by rfl⟩ : syracuseStep 2695385 = 2021539) B2021539
theorem B2695499 : Blo 1796099 2695499 := bstep (se 1 (by rfl) ⟨2021624, by rfl⟩ : syracuseStep 2695499 = 4043249) B4043249
theorem B2695511 : Blo 1796099 2695511 := bstep (se 1 (by rfl) ⟨2021633, by rfl⟩ : syracuseStep 2695511 = 4043267) B4043267
theorem B2695577 : Blo 1796099 2695577 := bstep (se 2 (by rfl) ⟨1010841, by rfl⟩ : syracuseStep 2695577 = 2021683) B2021683
theorem B3031499 : Blo 1796099 3031499 := bstep (se 1 (by rfl) ⟨2273624, by rfl⟩ : syracuseStep 3031499 = 4547249) B4547249
theorem B4096499 : Blo 1796099 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B2695691 : Blo 1796099 2695691 := bstep (se 1 (by rfl) ⟨2021768, by rfl⟩ : syracuseStep 2695691 = 4043537) B4043537
theorem B2695703 : Blo 1796099 2695703 := bstep (se 1 (by rfl) ⟨2021777, by rfl⟩ : syracuseStep 2695703 = 4043555) B4043555
theorem B4547137 : Blo 1796099 4547137 := bstep (se 2 (by rfl) ⟨1705176, by rfl⟩ : syracuseStep 4547137 = 3410353) B3410353
theorem B9093707 : Blo 1796099 9093707 := bstep (se 1 (by rfl) ⟨6820280, by rfl⟩ : syracuseStep 9093707 = 13640561) B13640561
theorem B3031627 : Blo 1796099 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B7676491 : Blo 1796099 7676491 := bstep (se 1 (by rfl) ⟨5757368, by rfl⟩ : syracuseStep 7676491 = 11514737) B11514737
theorem B2695769 : Blo 1796099 2695769 := bstep (se 2 (by rfl) ⟨1010913, by rfl⟩ : syracuseStep 2695769 = 2021827) B2021827
theorem B8200877 : Blo 1796099 8200877 := bstep (se 3 (by rfl) ⟨1537664, by rfl⟩ : syracuseStep 8200877 = 3075329) B3075329
theorem B6062795 : Blo 1796099 6062795 := bstep (se 1 (by rfl) ⟨4547096, by rfl⟩ : syracuseStep 6062795 = 9094193) B9094193
theorem B2695883 : Blo 1796099 2695883 := bstep (se 1 (by rfl) ⟨2021912, by rfl⟩ : syracuseStep 2695883 = 4043825) B4043825
theorem B2695895 : Blo 1796099 2695895 := bstep (se 1 (by rfl) ⟨2021921, by rfl⟩ : syracuseStep 2695895 = 4043843) B4043843
theorem B3031769 : Blo 1796099 3031769 := bstep (se 2 (by rfl) ⟨1136913, by rfl⟩ : syracuseStep 3031769 = 2273827) B2273827
theorem B2695961 : Blo 1796099 2695961 := bstep (se 2 (by rfl) ⟨1010985, by rfl⟩ : syracuseStep 2695961 = 2021971) B2021971
theorem B3031897 : Blo 1796099 3031897 := bstep (se 2 (by rfl) ⟨1136961, by rfl⟩ : syracuseStep 3031897 = 2273923) B2273923
theorem B7676765 : Blo 1796099 7676765 := bstep (se 3 (by rfl) ⟨1439393, by rfl⟩ : syracuseStep 7676765 = 2878787) B2878787
theorem B10380163 : Blo 1796099 10380163 := bstep (se 1 (by rfl) ⟨7785122, by rfl⟩ : syracuseStep 10380163 = 15570245) B15570245
theorem B2696075 : Blo 1796099 2696075 := bstep (se 1 (by rfl) ⟨2022056, by rfl⟩ : syracuseStep 2696075 = 4044113) B4044113
theorem B2696087 : Blo 1796099 2696087 := bstep (se 1 (by rfl) ⟨2022065, by rfl⟩ : syracuseStep 2696087 = 4044131) B4044131
theorem B3072971 : Blo 1796099 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B6063065 : Blo 1796099 6063065 := bstep (se 2 (by rfl) ⟨2273649, by rfl⟩ : syracuseStep 6063065 = 4547299) B4547299
theorem B131449817 : Blo 1796099 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B2696153 : Blo 1796099 2696153 := bstep (se 2 (by rfl) ⟨1011057, by rfl⟩ : syracuseStep 2696153 = 2022115) B2022115
theorem B6825005 : Blo 1796099 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B2696267 : Blo 1796099 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B2696279 : Blo 1796099 2696279 := bstep (se 1 (by rfl) ⟨2022209, by rfl⟩ : syracuseStep 2696279 = 4044419) B4044419
theorem B4547735 : Blo 1796099 4547735 := bstep (se 1 (by rfl) ⟨3410801, by rfl⟩ : syracuseStep 4547735 = 6821603) B6821603
theorem B2696345 : Blo 1796099 2696345 := bstep (se 2 (by rfl) ⟨1011129, by rfl⟩ : syracuseStep 2696345 = 2022259) B2022259
theorem B3237043 : Blo 1796099 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B12952781 : Blo 1796099 12952781 := bstep (se 3 (by rfl) ⟨2428646, by rfl⟩ : syracuseStep 12952781 = 4857293) B4857293
theorem B3237079 : Blo 1796099 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B8635609 : Blo 1796099 8635609 := bstep (se 2 (by rfl) ⟨3238353, by rfl⟩ : syracuseStep 8635609 = 6476707) B6476707
theorem B2696459 : Blo 1796099 2696459 := bstep (se 1 (by rfl) ⟨2022344, by rfl⟩ : syracuseStep 2696459 = 4044689) B4044689
theorem B8750353 : Blo 1796099 8750353 := bstep (se 2 (by rfl) ⟨3281382, by rfl⟩ : syracuseStep 8750353 = 6562765) B6562765
theorem B2696471 : Blo 1796099 2696471 := bstep (se 1 (by rfl) ⟨2022353, by rfl⟩ : syracuseStep 2696471 = 4044707) B4044707
theorem B2696537 : Blo 1796099 2696537 := bstep (se 2 (by rfl) ⟨1011201, by rfl⟩ : syracuseStep 2696537 = 2022403) B2022403
theorem B3032471 : Blo 1796099 3032471 := bstep (se 1 (by rfl) ⟨2274353, by rfl⟩ : syracuseStep 3032471 = 4548707) B4548707
theorem B2049463 : Blo 1796099 2049463 := bstep (se 1 (by rfl) ⟨1537097, by rfl⟩ : syracuseStep 2049463 = 3074195) B3074195
theorem B2696651 : Blo 1796099 2696651 := bstep (se 1 (by rfl) ⟨2022488, by rfl⟩ : syracuseStep 2696651 = 4044977) B4044977
theorem B2696663 : Blo 1796099 2696663 := bstep (se 1 (by rfl) ⟨2022497, by rfl⟩ : syracuseStep 2696663 = 4044995) B4044995
theorem B3032599 : Blo 1796099 3032599 := bstep (se 1 (by rfl) ⟨2274449, by rfl⟩ : syracuseStep 3032599 = 4548899) B4548899
theorem B2917913 : Blo 1796099 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B2696729 : Blo 1796099 2696729 := bstep (se 2 (by rfl) ⟨1011273, by rfl⟩ : syracuseStep 2696729 = 2022547) B2022547
theorem B7284289 : Blo 1796099 7284289 := bstep (se 2 (by rfl) ⟨2731608, by rfl⟩ : syracuseStep 7284289 = 5463217) B5463217
theorem B6145625 : Blo 1796099 6145625 := bstep (se 2 (by rfl) ⟨2304609, by rfl⟩ : syracuseStep 6145625 = 4609219) B4609219
theorem B2696843 : Blo 1796099 2696843 := bstep (se 1 (by rfl) ⟨2022632, by rfl⟩ : syracuseStep 2696843 = 4045265) B4045265
theorem B6063767 : Blo 1796099 6063767 := bstep (se 1 (by rfl) ⟨4547825, by rfl⟩ : syracuseStep 6063767 = 9095651) B9095651
theorem B2696855 : Blo 1796099 2696855 := bstep (se 1 (by rfl) ⟨2022641, by rfl⟩ : syracuseStep 2696855 = 4045283) B4045283
theorem B2696921 : Blo 1796099 2696921 := bstep (se 2 (by rfl) ⟨1011345, by rfl⟩ : syracuseStep 2696921 = 2022691) B2022691
theorem B6825779 : Blo 1796099 6825779 := bstep (se 1 (by rfl) ⟨5119334, by rfl⟩ : syracuseStep 6825779 = 10238669) B10238669
theorem B2697035 : Blo 1796099 2697035 := bstep (se 1 (by rfl) ⟨2022776, by rfl⟩ : syracuseStep 2697035 = 4045553) B4045553
theorem B2697047 : Blo 1796099 2697047 := bstep (se 1 (by rfl) ⟨2022785, by rfl⟩ : syracuseStep 2697047 = 4045571) B4045571
theorem B13649795 : Blo 1796099 13649795 := bstep (se 1 (by rfl) ⟨10237346, by rfl⟩ : syracuseStep 13649795 = 20474693) B20474693
theorem B6473623 : Blo 1796099 6473623 := bstep (se 1 (by rfl) ⟨4855217, by rfl⟩ : syracuseStep 6473623 = 9710435) B9710435
theorem B2697113 : Blo 1796099 2697113 := bstep (se 2 (by rfl) ⟨1011417, by rfl⟩ : syracuseStep 2697113 = 2022835) B2022835
theorem B4548545 : Blo 1796099 4548545 := bstep (se 2 (by rfl) ⟨1705704, by rfl⟩ : syracuseStep 4548545 = 3411409) B3411409
theorem B3409867 : Blo 1796099 3409867 := bstep (se 1 (by rfl) ⟨2557400, by rfl⟩ : syracuseStep 3409867 = 5114801) B5114801
theorem B3237835 : Blo 1796099 3237835 := bstep (se 1 (by rfl) ⟨2428376, by rfl⟩ : syracuseStep 3237835 = 4856753) B4856753
theorem B1796107 : Blo 1796099 1796107 := bstep (se 1 (by rfl) ⟨1347080, by rfl⟩ : syracuseStep 1796107 = 2694161) B2694161
theorem B1796119 : Blo 1796099 1796119 := bstep (se 1 (by rfl) ⟨1347089, by rfl⟩ : syracuseStep 1796119 = 2694179) B2694179
theorem B1918999 : Blo 1796099 1918999 := bstep (se 1 (by rfl) ⟨1439249, by rfl⟩ : syracuseStep 1918999 = 2878499) B2878499
theorem B1796139 : Blo 1796099 1796139 := bstep (se 1 (by rfl) ⟨1347104, by rfl⟩ : syracuseStep 1796139 = 2694209) B2694209
theorem B1796151 : Blo 1796099 1796151 := bstep (se 1 (by rfl) ⟨1347113, by rfl⟩ : syracuseStep 1796151 = 2694227) B2694227
theorem B1796171 : Blo 1796099 1796171 := bstep (se 1 (by rfl) ⟨1347128, by rfl⟩ : syracuseStep 1796171 = 2694257) B2694257
theorem B2558027 : Blo 1796099 2558027 := bstep (se 1 (by rfl) ⟨1918520, by rfl⟩ : syracuseStep 2558027 = 3837041) B3837041
theorem B1796183 : Blo 1796099 1796183 := bstep (se 1 (by rfl) ⟨1347137, by rfl⟩ : syracuseStep 1796183 = 2694275) B2694275
theorem B1796203 : Blo 1796099 1796203 := bstep (se 1 (by rfl) ⟨1347152, by rfl⟩ : syracuseStep 1796203 = 2694305) B2694305
theorem B1796215 : Blo 1796099 1796215 := bstep (se 1 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 1796215 = 2694323) B2694323
theorem B1796235 : Blo 1796099 1796235 := bstep (se 1 (by rfl) ⟨1347176, by rfl⟩ : syracuseStep 1796235 = 2694353) B2694353
theorem B3033227 : Blo 1796099 3033227 := bstep (se 1 (by rfl) ⟨2274920, by rfl⟩ : syracuseStep 3033227 = 4549841) B4549841
theorem B1796247 : Blo 1796099 1796247 := bstep (se 1 (by rfl) ⟨1347185, by rfl⟩ : syracuseStep 1796247 = 2694371) B2694371
theorem B1796267 : Blo 1796099 1796267 := bstep (se 1 (by rfl) ⟨1347200, by rfl⟩ : syracuseStep 1796267 = 2694401) B2694401
theorem B6064307 : Blo 1796099 6064307 := bstep (se 1 (by rfl) ⟨4548230, by rfl⟩ : syracuseStep 6064307 = 9096461) B9096461
theorem B1796279 : Blo 1796099 1796279 := bstep (se 1 (by rfl) ⟨1347209, by rfl⟩ : syracuseStep 1796279 = 2694419) B2694419
theorem B1796299 : Blo 1796099 1796299 := bstep (se 1 (by rfl) ⟨1347224, by rfl⟩ : syracuseStep 1796299 = 2694449) B2694449
theorem B4098251 : Blo 1796099 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B1796311 : Blo 1796099 1796311 := bstep (se 1 (by rfl) ⟨1347233, by rfl⟩ : syracuseStep 1796311 = 2694467) B2694467
theorem B1796331 : Blo 1796099 1796331 := bstep (se 1 (by rfl) ⟨1347248, by rfl⟩ : syracuseStep 1796331 = 2694497) B2694497
theorem B1796343 : Blo 1796099 1796343 := bstep (se 1 (by rfl) ⟨1347257, by rfl⟩ : syracuseStep 1796343 = 2694515) B2694515
theorem B1796363 : Blo 1796099 1796363 := bstep (se 1 (by rfl) ⟨1347272, by rfl⟩ : syracuseStep 1796363 = 2694545) B2694545
theorem B3033355 : Blo 1796099 3033355 := bstep (se 1 (by rfl) ⟨2275016, by rfl⟩ : syracuseStep 3033355 = 4550033) B4550033
theorem B16402705 : Blo 1796099 16402705 := bstep (se 2 (by rfl) ⟨6151014, by rfl⟩ : syracuseStep 16402705 = 12302029) B12302029
theorem B1796375 : Blo 1796099 1796375 := bstep (se 1 (by rfl) ⟨1347281, by rfl⟩ : syracuseStep 1796375 = 2694563) B2694563
theorem B3410201 : Blo 1796099 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B13642019 : Blo 1796099 13642019 := bstep (se 1 (by rfl) ⟨10231514, by rfl⟩ : syracuseStep 13642019 = 20463029) B20463029
theorem B1796395 : Blo 1796099 1796395 := bstep (se 1 (by rfl) ⟨1347296, by rfl⟩ : syracuseStep 1796395 = 2694593) B2694593
theorem B1796407 : Blo 1796099 1796407 := bstep (se 1 (by rfl) ⟨1347305, by rfl⟩ : syracuseStep 1796407 = 2694611) B2694611
theorem B9095489 : Blo 1796099 9095489 := bstep (se 2 (by rfl) ⟨3410808, by rfl⟩ : syracuseStep 9095489 = 6821617) B6821617
theorem B1796427 : Blo 1796099 1796427 := bstep (se 1 (by rfl) ⟨1347320, by rfl⟩ : syracuseStep 1796427 = 2694641) B2694641
theorem B1796439 : Blo 1796099 1796439 := bstep (se 1 (by rfl) ⟨1347329, by rfl⟩ : syracuseStep 1796439 = 2694659) B2694659
theorem B1796459 : Blo 1796099 1796459 := bstep (se 1 (by rfl) ⟨1347344, by rfl⟩ : syracuseStep 1796459 = 2694689) B2694689
theorem B1796471 : Blo 1796099 1796471 := bstep (se 1 (by rfl) ⟨1347353, by rfl⟩ : syracuseStep 1796471 = 2694707) B2694707
theorem B1796491 : Blo 1796099 1796491 := bstep (se 1 (by rfl) ⟨1347368, by rfl⟩ : syracuseStep 1796491 = 2694737) B2694737
theorem B1796503 : Blo 1796099 1796503 := bstep (se 1 (by rfl) ⟨1347377, by rfl⟩ : syracuseStep 1796503 = 2694755) B2694755
theorem B3033497 : Blo 1796099 3033497 := bstep (se 2 (by rfl) ⟨1137561, by rfl⟩ : syracuseStep 3033497 = 2275123) B2275123
theorem B1796523 : Blo 1796099 1796523 := bstep (se 1 (by rfl) ⟨1347392, by rfl⟩ : syracuseStep 1796523 = 2694785) B2694785
theorem B1796535 : Blo 1796099 1796535 := bstep (se 1 (by rfl) ⟨1347401, by rfl⟩ : syracuseStep 1796535 = 2694803) B2694803
theorem B6064577 : Blo 1796099 6064577 := bstep (se 2 (by rfl) ⟨2274216, by rfl⟩ : syracuseStep 6064577 = 4548433) B4548433
theorem B1796555 : Blo 1796099 1796555 := bstep (se 1 (by rfl) ⟨1347416, by rfl⟩ : syracuseStep 1796555 = 2694833) B2694833
theorem B1796567 : Blo 1796099 1796567 := bstep (se 1 (by rfl) ⟨1347425, by rfl⟩ : syracuseStep 1796567 = 2694851) B2694851
theorem B4549081 : Blo 1796099 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B1796587 : Blo 1796099 1796587 := bstep (se 1 (by rfl) ⟨1347440, by rfl⟩ : syracuseStep 1796587 = 2694881) B2694881
theorem B1796599 : Blo 1796099 1796599 := bstep (se 1 (by rfl) ⟨1347449, by rfl⟩ : syracuseStep 1796599 = 2694899) B2694899
theorem B1796619 : Blo 1796099 1796619 := bstep (se 1 (by rfl) ⟨1347464, by rfl⟩ : syracuseStep 1796619 = 2694929) B2694929
theorem B1796631 : Blo 1796099 1796631 := bstep (se 1 (by rfl) ⟨1347473, by rfl⟩ : syracuseStep 1796631 = 2694947) B2694947
theorem B3033625 : Blo 1796099 3033625 := bstep (se 2 (by rfl) ⟨1137609, by rfl⟩ : syracuseStep 3033625 = 2275219) B2275219
theorem B1796651 : Blo 1796099 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B1796663 : Blo 1796099 1796663 := bstep (se 1 (by rfl) ⟨1347497, by rfl⟩ : syracuseStep 1796663 = 2694995) B2694995
theorem B1796683 : Blo 1796099 1796683 := bstep (se 1 (by rfl) ⟨1347512, by rfl⟩ : syracuseStep 1796683 = 2695025) B2695025
theorem B1796695 : Blo 1796099 1796695 := bstep (se 1 (by rfl) ⟨1347521, by rfl⟩ : syracuseStep 1796695 = 2695043) B2695043
theorem B4041305 : Blo 1796099 4041305 := bstep (se 2 (by rfl) ⟨1515489, by rfl⟩ : syracuseStep 4041305 = 3030979) B3030979
theorem B1796715 : Blo 1796099 1796715 := bstep (se 1 (by rfl) ⟨1347536, by rfl⟩ : syracuseStep 1796715 = 2695073) B2695073
theorem B1796727 : Blo 1796099 1796727 := bstep (se 1 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 1796727 = 2695091) B2695091
theorem B1796747 : Blo 1796099 1796747 := bstep (se 1 (by rfl) ⟨1347560, by rfl⟩ : syracuseStep 1796747 = 2695121) B2695121
theorem B1796759 : Blo 1796099 1796759 := bstep (se 1 (by rfl) ⟨1347569, by rfl⟩ : syracuseStep 1796759 = 2695139) B2695139
theorem B1796779 : Blo 1796099 1796779 := bstep (se 1 (by rfl) ⟨1347584, by rfl⟩ : syracuseStep 1796779 = 2695169) B2695169
theorem B7285421 : Blo 1796099 7285421 := bstep (se 3 (by rfl) ⟨1366016, by rfl⟩ : syracuseStep 7285421 = 2732033) B2732033
theorem B4041395 : Blo 1796099 4041395 := bstep (se 1 (by rfl) ⟨3031046, by rfl⟩ : syracuseStep 4041395 = 6062093) B6062093
theorem B1796791 : Blo 1796099 1796791 := bstep (se 1 (by rfl) ⟨1347593, by rfl⟩ : syracuseStep 1796791 = 2695187) B2695187
theorem B1796811 : Blo 1796099 1796811 := bstep (se 1 (by rfl) ⟨1347608, by rfl⟩ : syracuseStep 1796811 = 2695217) B2695217
theorem B4041431 : Blo 1796099 4041431 := bstep (se 1 (by rfl) ⟨3031073, by rfl⟩ : syracuseStep 4041431 = 6062147) B6062147
theorem B1796823 : Blo 1796099 1796823 := bstep (se 1 (by rfl) ⟨1347617, by rfl⟩ : syracuseStep 1796823 = 2695235) B2695235
theorem B1796843 : Blo 1796099 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B25905905 : Blo 1796099 25905905 := bstep (se 2 (by rfl) ⟨9714714, by rfl⟩ : syracuseStep 25905905 = 19429429) B19429429
theorem B1796855 : Blo 1796099 1796855 := bstep (se 1 (by rfl) ⟨1347641, by rfl⟩ : syracuseStep 1796855 = 2695283) B2695283
theorem B1796875 : Blo 1796099 1796875 := bstep (se 1 (by rfl) ⟨1347656, by rfl⟩ : syracuseStep 1796875 = 2695313) B2695313
theorem B1796887 : Blo 1796099 1796887 := bstep (se 1 (by rfl) ⟨1347665, by rfl⟩ : syracuseStep 1796887 = 2695331) B2695331
theorem B16395043 : Blo 1796099 16395043 := bstep (se 1 (by rfl) ⟨12296282, by rfl⟩ : syracuseStep 16395043 = 24592565) B24592565
theorem B1796907 : Blo 1796099 1796907 := bstep (se 1 (by rfl) ⟨1347680, by rfl⟩ : syracuseStep 1796907 = 2695361) B2695361
theorem B1796919 : Blo 1796099 1796919 := bstep (se 1 (by rfl) ⟨1347689, by rfl⟩ : syracuseStep 1796919 = 2695379) B2695379
theorem B1796939 : Blo 1796099 1796939 := bstep (se 1 (by rfl) ⟨1347704, by rfl⟩ : syracuseStep 1796939 = 2695409) B2695409
theorem B1919819 : Blo 1796099 1919819 := bstep (se 1 (by rfl) ⟨1439864, by rfl⟩ : syracuseStep 1919819 = 2879729) B2879729
theorem B1796951 : Blo 1796099 1796951 := bstep (se 1 (by rfl) ⟨1347713, by rfl⟩ : syracuseStep 1796951 = 2695427) B2695427
theorem B5188441 : Blo 1796099 5188441 := bstep (se 2 (by rfl) ⟨1945665, by rfl⟩ : syracuseStep 5188441 = 3891331) B3891331
theorem B66497381 : Blo 1796099 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B1796971 : Blo 1796099 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B1796983 : Blo 1796099 1796983 := bstep (se 1 (by rfl) ⟨1347737, by rfl⟩ : syracuseStep 1796983 = 2695475) B2695475
theorem B16386947 : Blo 1796099 16386947 := bstep (se 1 (by rfl) ⟨12290210, by rfl⟩ : syracuseStep 16386947 = 24580421) B24580421
theorem B4041611 : Blo 1796099 4041611 := bstep (se 1 (by rfl) ⟨3031208, by rfl⟩ : syracuseStep 4041611 = 6062417) B6062417
theorem B1797003 : Blo 1796099 1797003 := bstep (se 1 (by rfl) ⟨1347752, by rfl⟩ : syracuseStep 1797003 = 2695505) B2695505
theorem B3410839 : Blo 1796099 3410839 := bstep (se 1 (by rfl) ⟨2558129, by rfl⟩ : syracuseStep 3410839 = 5116259) B5116259
theorem B1797015 : Blo 1796099 1797015 := bstep (se 1 (by rfl) ⟨1347761, by rfl⟩ : syracuseStep 1797015 = 2695523) B2695523
theorem B1797035 : Blo 1796099 1797035 := bstep (se 1 (by rfl) ⟨1347776, by rfl⟩ : syracuseStep 1797035 = 2695553) B2695553
theorem B1797047 : Blo 1796099 1797047 := bstep (se 1 (by rfl) ⟨1347785, by rfl⟩ : syracuseStep 1797047 = 2695571) B2695571
theorem B1821623 : Blo 1796099 1821623 := bstep (se 1 (by rfl) ⟨1366217, by rfl⟩ : syracuseStep 1821623 = 2732435) B2732435
theorem B4041665 : Blo 1796099 4041665 := bstep (se 2 (by rfl) ⟨1515624, by rfl⟩ : syracuseStep 4041665 = 3031249) B3031249
theorem B1797067 : Blo 1796099 1797067 := bstep (se 1 (by rfl) ⟨1347800, by rfl⟩ : syracuseStep 1797067 = 2695601) B2695601
theorem B1919947 : Blo 1796099 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B1797079 : Blo 1796099 1797079 := bstep (se 1 (by rfl) ⟨1347809, by rfl⟩ : syracuseStep 1797079 = 2695619) B2695619
theorem B6065117 : Blo 1796099 6065117 := bstep (se 3 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 6065117 = 2274419) B2274419
theorem B1797099 : Blo 1796099 1797099 := bstep (se 1 (by rfl) ⟨1347824, by rfl⟩ : syracuseStep 1797099 = 2695649) B2695649
theorem B1797111 : Blo 1796099 1797111 := bstep (se 1 (by rfl) ⟨1347833, by rfl⟩ : syracuseStep 1797111 = 2695667) B2695667
theorem B1797131 : Blo 1796099 1797131 := bstep (se 1 (by rfl) ⟨1347848, by rfl⟩ : syracuseStep 1797131 = 2695697) B2695697
theorem B1797143 : Blo 1796099 1797143 := bstep (se 1 (by rfl) ⟨1347857, by rfl⟩ : syracuseStep 1797143 = 2695715) B2695715
theorem B1797163 : Blo 1796099 1797163 := bstep (se 1 (by rfl) ⟨1347872, by rfl⟩ : syracuseStep 1797163 = 2695745) B2695745
theorem B1797175 : Blo 1796099 1797175 := bstep (se 1 (by rfl) ⟨1347881, by rfl⟩ : syracuseStep 1797175 = 2695763) B2695763
theorem B6917185 : Blo 1796099 6917185 := bstep (se 2 (by rfl) ⟨2593944, by rfl⟩ : syracuseStep 6917185 = 5187889) B5187889
theorem B1797195 : Blo 1796099 1797195 := bstep (se 1 (by rfl) ⟨1347896, by rfl⟩ : syracuseStep 1797195 = 2695793) B2695793
theorem B1797207 : Blo 1796099 1797207 := bstep (se 1 (by rfl) ⟨1347905, by rfl⟩ : syracuseStep 1797207 = 2695811) B2695811
theorem B3034199 : Blo 1796099 3034199 := bstep (se 1 (by rfl) ⟨2275649, by rfl⟩ : syracuseStep 3034199 = 4551299) B4551299
theorem B1797227 : Blo 1796099 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B1797239 : Blo 1796099 1797239 := bstep (se 1 (by rfl) ⟨1347929, by rfl⟩ : syracuseStep 1797239 = 2695859) B2695859
theorem B1797259 : Blo 1796099 1797259 := bstep (se 1 (by rfl) ⟨1347944, by rfl⟩ : syracuseStep 1797259 = 2695889) B2695889
theorem B1797271 : Blo 1796099 1797271 := bstep (se 1 (by rfl) ⟨1347953, by rfl⟩ : syracuseStep 1797271 = 2695907) B2695907
theorem B4041881 : Blo 1796099 4041881 := bstep (se 2 (by rfl) ⟨1515705, by rfl⟩ : syracuseStep 4041881 = 3031411) B3031411
theorem B1797291 : Blo 1796099 1797291 := bstep (se 1 (by rfl) ⟨1347968, by rfl⟩ : syracuseStep 1797291 = 2695937) B2695937
theorem B1797303 : Blo 1796099 1797303 := bstep (se 1 (by rfl) ⟨1347977, by rfl⟩ : syracuseStep 1797303 = 2695955) B2695955
theorem B4099265 : Blo 1796099 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B1797323 : Blo 1796099 1797323 := bstep (se 1 (by rfl) ⟨1347992, by rfl⟩ : syracuseStep 1797323 = 2695985) B2695985
theorem B1797335 : Blo 1796099 1797335 := bstep (se 1 (by rfl) ⟨1348001, by rfl⟩ : syracuseStep 1797335 = 2696003) B2696003
theorem B1797355 : Blo 1796099 1797355 := bstep (se 1 (by rfl) ⟨1348016, by rfl⟩ : syracuseStep 1797355 = 2696033) B2696033
theorem B4041971 : Blo 1796099 4041971 := bstep (se 1 (by rfl) ⟨3031478, by rfl⟩ : syracuseStep 4041971 = 6062957) B6062957
theorem B1797367 : Blo 1796099 1797367 := bstep (se 1 (by rfl) ⟨1348025, by rfl⟩ : syracuseStep 1797367 = 2696051) B2696051
theorem B1797387 : Blo 1796099 1797387 := bstep (se 1 (by rfl) ⟨1348040, by rfl⟩ : syracuseStep 1797387 = 2696081) B2696081
theorem B4042007 : Blo 1796099 4042007 := bstep (se 1 (by rfl) ⟨3031505, by rfl⟩ : syracuseStep 4042007 = 6063011) B6063011
theorem B1797399 : Blo 1796099 1797399 := bstep (se 1 (by rfl) ⟨1348049, by rfl⟩ : syracuseStep 1797399 = 2696099) B2696099
theorem B1797419 : Blo 1796099 1797419 := bstep (se 1 (by rfl) ⟨1348064, by rfl⟩ : syracuseStep 1797419 = 2696129) B2696129
theorem B3239219 : Blo 1796099 3239219 := bstep (se 1 (by rfl) ⟨2429414, by rfl⟩ : syracuseStep 3239219 = 4858829) B4858829
theorem B1797431 : Blo 1796099 1797431 := bstep (se 1 (by rfl) ⟨1348073, by rfl⟩ : syracuseStep 1797431 = 2696147) B2696147
theorem B1797451 : Blo 1796099 1797451 := bstep (se 1 (by rfl) ⟨1348088, by rfl⟩ : syracuseStep 1797451 = 2696177) B2696177
theorem B1797463 : Blo 1796099 1797463 := bstep (se 1 (by rfl) ⟨1348097, by rfl⟩ : syracuseStep 1797463 = 2696195) B2696195
theorem B19426661 : Blo 1796099 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B1797483 : Blo 1796099 1797483 := bstep (se 1 (by rfl) ⟨1348112, by rfl⟩ : syracuseStep 1797483 = 2696225) B2696225
theorem B1797495 : Blo 1796099 1797495 := bstep (se 1 (by rfl) ⟨1348121, by rfl⟩ : syracuseStep 1797495 = 2696243) B2696243
theorem B1797515 : Blo 1796099 1797515 := bstep (se 1 (by rfl) ⟨1348136, by rfl⟩ : syracuseStep 1797515 = 2696273) B2696273
theorem B7679377 : Blo 1796099 7679377 := bstep (se 2 (by rfl) ⟨2879766, by rfl⟩ : syracuseStep 7679377 = 5759533) B5759533
theorem B9710999 : Blo 1796099 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B1797527 : Blo 1796099 1797527 := bstep (se 1 (by rfl) ⟨1348145, by rfl⟩ : syracuseStep 1797527 = 2696291) B2696291
theorem B1797547 : Blo 1796099 1797547 := bstep (se 1 (by rfl) ⟨1348160, by rfl⟩ : syracuseStep 1797547 = 2696321) B2696321
theorem B7777709 : Blo 1796099 7777709 := bstep (se 3 (by rfl) ⟨1458320, by rfl⟩ : syracuseStep 7777709 = 2916641) B2916641
theorem B1797559 : Blo 1796099 1797559 := bstep (se 1 (by rfl) ⟨1348169, by rfl⟩ : syracuseStep 1797559 = 2696339) B2696339
theorem B4042187 : Blo 1796099 4042187 := bstep (se 1 (by rfl) ⟨3031640, by rfl⟩ : syracuseStep 4042187 = 6063281) B6063281
theorem B1797579 : Blo 1796099 1797579 := bstep (se 1 (by rfl) ⟨1348184, by rfl⟩ : syracuseStep 1797579 = 2696369) B2696369
theorem B1797591 : Blo 1796099 1797591 := bstep (se 1 (by rfl) ⟨1348193, by rfl⟩ : syracuseStep 1797591 = 2696387) B2696387
theorem B1797611 : Blo 1796099 1797611 := bstep (se 1 (by rfl) ⟨1348208, by rfl⟩ : syracuseStep 1797611 = 2696417) B2696417
theorem B1822187 : Blo 1796099 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B1797623 : Blo 1796099 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B4042241 : Blo 1796099 4042241 := bstep (se 2 (by rfl) ⟨1515840, by rfl⟩ : syracuseStep 4042241 = 3031681) B3031681
theorem B3837451 : Blo 1796099 3837451 := bstep (se 1 (by rfl) ⟨2878088, by rfl⟩ : syracuseStep 3837451 = 5756177) B5756177
theorem B1797643 : Blo 1796099 1797643 := bstep (se 1 (by rfl) ⟨1348232, by rfl⟩ : syracuseStep 1797643 = 2696465) B2696465
theorem B1797655 : Blo 1796099 1797655 := bstep (se 1 (by rfl) ⟨1348241, by rfl⟩ : syracuseStep 1797655 = 2696483) B2696483
theorem B1797675 : Blo 1796099 1797675 := bstep (se 1 (by rfl) ⟨1348256, by rfl⟩ : syracuseStep 1797675 = 2696513) B2696513
theorem B4550195 : Blo 1796099 4550195 := bstep (se 1 (by rfl) ⟨3412646, by rfl⟩ : syracuseStep 4550195 = 6825293) B6825293
theorem B1797687 : Blo 1796099 1797687 := bstep (se 1 (by rfl) ⟨1348265, by rfl⟩ : syracuseStep 1797687 = 2696531) B2696531
theorem B1797707 : Blo 1796099 1797707 := bstep (se 1 (by rfl) ⟨1348280, by rfl⟩ : syracuseStep 1797707 = 2696561) B2696561
theorem B3075659 : Blo 1796099 3075659 := bstep (se 1 (by rfl) ⟨2306744, by rfl⟩ : syracuseStep 3075659 = 4613489) B4613489
theorem B1797719 : Blo 1796099 1797719 := bstep (se 1 (by rfl) ⟨1348289, by rfl⟩ : syracuseStep 1797719 = 2696579) B2696579
theorem B1797739 : Blo 1796099 1797739 := bstep (se 1 (by rfl) ⟨1348304, by rfl⟩ : syracuseStep 1797739 = 2696609) B2696609
theorem B1797751 : Blo 1796099 1797751 := bstep (se 1 (by rfl) ⟨1348313, by rfl⟩ : syracuseStep 1797751 = 2696627) B2696627
theorem B1797771 : Blo 1796099 1797771 := bstep (se 1 (by rfl) ⟨1348328, by rfl⟩ : syracuseStep 1797771 = 2696657) B2696657
theorem B1797783 : Blo 1796099 1797783 := bstep (se 1 (by rfl) ⟨1348337, by rfl⟩ : syracuseStep 1797783 = 2696675) B2696675
theorem B1797803 : Blo 1796099 1797803 := bstep (se 1 (by rfl) ⟨1348352, by rfl⟩ : syracuseStep 1797803 = 2696705) B2696705
theorem B1797815 : Blo 1796099 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B3411659 : Blo 1796099 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B1797835 : Blo 1796099 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B1797847 : Blo 1796099 1797847 := bstep (se 1 (by rfl) ⟨1348385, by rfl⟩ : syracuseStep 1797847 = 2696771) B2696771
theorem B12947161 : Blo 1796099 12947161 := bstep (se 2 (by rfl) ⟨4855185, by rfl⟩ : syracuseStep 12947161 = 9710371) B9710371
theorem B4042457 : Blo 1796099 4042457 := bstep (se 2 (by rfl) ⟨1515921, by rfl⟩ : syracuseStep 4042457 = 3031843) B3031843
theorem B1797867 : Blo 1796099 1797867 := bstep (se 1 (by rfl) ⟨1348400, by rfl⟩ : syracuseStep 1797867 = 2696801) B2696801
theorem B1797879 : Blo 1796099 1797879 := bstep (se 1 (by rfl) ⟨1348409, by rfl⟩ : syracuseStep 1797879 = 2696819) B2696819
theorem B3411713 : Blo 1796099 3411713 := bstep (se 2 (by rfl) ⟨1279392, by rfl⟩ : syracuseStep 3411713 = 2558785) B2558785
theorem B3837707 : Blo 1796099 3837707 := bstep (se 1 (by rfl) ⟨2878280, by rfl⟩ : syracuseStep 3837707 = 5756561) B5756561
theorem B1797899 : Blo 1796099 1797899 := bstep (se 1 (by rfl) ⟨1348424, by rfl⟩ : syracuseStep 1797899 = 2696849) B2696849
theorem B1797911 : Blo 1796099 1797911 := bstep (se 1 (by rfl) ⟨1348433, by rfl⟩ : syracuseStep 1797911 = 2696867) B2696867
theorem B1797931 : Blo 1796099 1797931 := bstep (se 1 (by rfl) ⟨1348448, by rfl⟩ : syracuseStep 1797931 = 2696897) B2696897
theorem B4042547 : Blo 1796099 4042547 := bstep (se 1 (by rfl) ⟨3031910, by rfl⟩ : syracuseStep 4042547 = 6063821) B6063821
theorem B1797943 : Blo 1796099 1797943 := bstep (se 1 (by rfl) ⟨1348457, by rfl⟩ : syracuseStep 1797943 = 2696915) B2696915
theorem B6819659 : Blo 1796099 6819659 := bstep (se 1 (by rfl) ⟨5114744, by rfl⟩ : syracuseStep 6819659 = 10229489) B10229489
theorem B7384907 : Blo 1796099 7384907 := bstep (se 1 (by rfl) ⟨5538680, by rfl⟩ : syracuseStep 7384907 = 11077361) B11077361
theorem B1797963 : Blo 1796099 1797963 := bstep (se 1 (by rfl) ⟨1348472, by rfl⟩ : syracuseStep 1797963 = 2696945) B2696945
theorem B4042583 : Blo 1796099 4042583 := bstep (se 1 (by rfl) ⟨3031937, by rfl⟩ : syracuseStep 4042583 = 6063875) B6063875
theorem B3239767 : Blo 1796099 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B6819673 : Blo 1796099 6819673 := bstep (se 2 (by rfl) ⟨2557377, by rfl⟩ : syracuseStep 6819673 = 5114755) B5114755
theorem B4550489 : Blo 1796099 4550489 := bstep (se 2 (by rfl) ⟨1706433, by rfl⟩ : syracuseStep 4550489 = 3412867) B3412867
theorem B1797975 : Blo 1796099 1797975 := bstep (se 1 (by rfl) ⟨1348481, by rfl⟩ : syracuseStep 1797975 = 2696963) B2696963
theorem B8638301 : Blo 1796099 8638301 := bstep (se 3 (by rfl) ⟨1619681, by rfl⟩ : syracuseStep 8638301 = 3239363) B3239363
theorem B1797995 : Blo 1796099 1797995 := bstep (se 1 (by rfl) ⟨1348496, by rfl⟩ : syracuseStep 1797995 = 2696993) B2696993
theorem B1798007 : Blo 1796099 1798007 := bstep (se 1 (by rfl) ⟨1348505, by rfl⟩ : syracuseStep 1798007 = 2697011) B2697011
theorem B1798027 : Blo 1796099 1798027 := bstep (se 1 (by rfl) ⟨1348520, by rfl⟩ : syracuseStep 1798027 = 2697041) B2697041
theorem B2879383 : Blo 1796099 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B1798039 : Blo 1796099 1798039 := bstep (se 1 (by rfl) ⟨1348529, by rfl⟩ : syracuseStep 1798039 = 2697059) B2697059
theorem B1798059 : Blo 1796099 1798059 := bstep (se 1 (by rfl) ⟨1348544, by rfl⟩ : syracuseStep 1798059 = 2697089) B2697089
theorem B15175603 : Blo 1796099 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B1798071 : Blo 1796099 1798071 := bstep (se 1 (by rfl) ⟨1348553, by rfl⟩ : syracuseStep 1798071 = 2697107) B2697107
theorem B5754817 : Blo 1796099 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B1798091 : Blo 1796099 1798091 := bstep (se 1 (by rfl) ⟨1348568, by rfl⟩ : syracuseStep 1798091 = 2697137) B2697137
theorem B12947417 : Blo 1796099 12947417 := bstep (se 2 (by rfl) ⟨4855281, by rfl⟩ : syracuseStep 12947417 = 9710563) B9710563
theorem B4042763 : Blo 1796099 4042763 := bstep (se 1 (by rfl) ⟨3032072, by rfl⟩ : syracuseStep 4042763 = 6064145) B6064145
theorem B4042817 : Blo 1796099 4042817 := bstep (se 2 (by rfl) ⟨1516056, by rfl⟩ : syracuseStep 4042817 = 3032113) B3032113
theorem B6066251 : Blo 1796099 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B2879639 : Blo 1796099 2879639 := bstep (se 1 (by rfl) ⟨2159729, by rfl⟩ : syracuseStep 2879639 = 4319459) B4319459
theorem B3281075 : Blo 1796099 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B29151413 : Blo 1796099 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B2158807 : Blo 1796099 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B9097433 : Blo 1796099 9097433 := bstep (se 2 (by rfl) ⟨3411537, by rfl⟩ : syracuseStep 9097433 = 6823075) B6823075
theorem B4043033 : Blo 1796099 4043033 := bstep (se 2 (by rfl) ⟨1516137, by rfl⟩ : syracuseStep 4043033 = 3032275) B3032275
theorem B2879831 : Blo 1796099 2879831 := bstep (se 1 (by rfl) ⟨2159873, by rfl⟩ : syracuseStep 2879831 = 4319747) B4319747
theorem B6066521 : Blo 1796099 6066521 := bstep (se 2 (by rfl) ⟨2274945, by rfl⟩ : syracuseStep 6066521 = 4549891) B4549891
theorem B10236253 : Blo 1796099 10236253 := bstep (se 3 (by rfl) ⟨1919297, by rfl⟩ : syracuseStep 10236253 = 3838595) B3838595
theorem B4043123 : Blo 1796099 4043123 := bstep (se 1 (by rfl) ⟨3032342, by rfl⟩ : syracuseStep 4043123 = 6064685) B6064685
theorem B4043159 : Blo 1796099 4043159 := bstep (se 1 (by rfl) ⟨3032369, by rfl⟩ : syracuseStep 4043159 = 6064739) B6064739
theorem B7287191 : Blo 1796099 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B31134131 : Blo 1796099 31134131 := bstep (se 1 (by rfl) ⟨23350598, by rfl⟩ : syracuseStep 31134131 = 46701197) B46701197
theorem B4043339 : Blo 1796099 4043339 := bstep (se 1 (by rfl) ⟨3032504, by rfl⟩ : syracuseStep 4043339 = 6065009) B6065009
theorem B4043393 : Blo 1796099 4043393 := bstep (se 2 (by rfl) ⟨1516272, by rfl⟩ : syracuseStep 4043393 = 3032545) B3032545
theorem B2880139 : Blo 1796099 2880139 := bstep (se 1 (by rfl) ⟨2160104, by rfl⟩ : syracuseStep 2880139 = 4320209) B4320209
theorem B5116567 : Blo 1796099 5116567 := bstep (se 1 (by rfl) ⟨3837425, by rfl⟩ : syracuseStep 5116567 = 7674851) B7674851
theorem B15356567 : Blo 1796099 15356567 := bstep (se 1 (by rfl) ⟨11517425, by rfl⟩ : syracuseStep 15356567 = 23034851) B23034851
theorem B3412631 : Blo 1796099 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B3838681 : Blo 1796099 3838681 := bstep (se 2 (by rfl) ⟨1439505, by rfl⟩ : syracuseStep 3838681 = 2879011) B2879011
theorem B6820631 : Blo 1796099 6820631 := bstep (se 1 (by rfl) ⟨5115473, by rfl⟩ : syracuseStep 6820631 = 10230947) B10230947
theorem B4043609 : Blo 1796099 4043609 := bstep (se 2 (by rfl) ⟨1516353, by rfl⟩ : syracuseStep 4043609 = 3032707) B3032707
theorem B3838835 : Blo 1796099 3838835 := bstep (se 1 (by rfl) ⟨2879126, by rfl⟩ : syracuseStep 3838835 = 5758253) B5758253
theorem B23663477 : Blo 1796099 23663477 := bstep (se 5 (by rfl) ⟨1109225, by rfl⟩ : syracuseStep 23663477 = 2218451) B2218451
theorem B4043699 : Blo 1796099 4043699 := bstep (se 1 (by rfl) ⟨3032774, by rfl⟩ : syracuseStep 4043699 = 6065549) B6065549
theorem B4043735 : Blo 1796099 4043735 := bstep (se 1 (by rfl) ⟨3032801, by rfl⟩ : syracuseStep 4043735 = 6065603) B6065603
theorem B6067223 : Blo 1796099 6067223 := bstep (se 1 (by rfl) ⟨4550417, by rfl⟩ : syracuseStep 6067223 = 9100835) B9100835
theorem B5755997 : Blo 1796099 5755997 := bstep (se 3 (by rfl) ⟨1079249, by rfl⟩ : syracuseStep 5755997 = 2158499) B2158499
theorem B4043915 : Blo 1796099 4043915 := bstep (se 1 (by rfl) ⟨3032936, by rfl⟩ : syracuseStep 4043915 = 6065873) B6065873
theorem B3413171 : Blo 1796099 3413171 := bstep (se 1 (by rfl) ⟨2559878, by rfl⟩ : syracuseStep 3413171 = 5119757) B5119757
theorem B4043969 : Blo 1796099 4043969 := bstep (se 2 (by rfl) ⟨1516488, by rfl⟩ : syracuseStep 4043969 = 3032977) B3032977
theorem B13653197 : Blo 1796099 13653197 := bstep (se 3 (by rfl) ⟨2559974, by rfl⟩ : syracuseStep 13653197 = 5119949) B5119949
theorem B2274571 : Blo 1796099 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B4855133 : Blo 1796099 4855133 := bstep (se 3 (by rfl) ⟨910337, by rfl⟩ : syracuseStep 4855133 = 1820675) B1820675
theorem B3839347 : Blo 1796099 3839347 := bstep (se 1 (by rfl) ⟨2879510, by rfl⟩ : syracuseStep 3839347 = 5759021) B5759021
theorem B2020747 : Blo 1796099 2020747 := bstep (se 1 (by rfl) ⟨1515560, by rfl⟩ : syracuseStep 2020747 = 3031121) B3031121
theorem B4044185 : Blo 1796099 4044185 := bstep (se 2 (by rfl) ⟨1516569, by rfl⟩ : syracuseStep 4044185 = 3033139) B3033139
theorem B4044275 : Blo 1796099 4044275 := bstep (se 1 (by rfl) ⟨3033206, by rfl⟩ : syracuseStep 4044275 = 6066413) B6066413
theorem B2020855 : Blo 1796099 2020855 := bstep (se 1 (by rfl) ⟨1515641, by rfl⟩ : syracuseStep 2020855 = 3031283) B3031283
theorem B4044311 : Blo 1796099 4044311 := bstep (se 1 (by rfl) ⟨3033233, by rfl⟩ : syracuseStep 4044311 = 6066467) B6066467
theorem B7009843 : Blo 1796099 7009843 := bstep (se 1 (by rfl) ⟨5257382, by rfl⟩ : syracuseStep 7009843 = 10514765) B10514765
theorem B6067763 : Blo 1796099 6067763 := bstep (se 1 (by rfl) ⟨4550822, by rfl⟩ : syracuseStep 6067763 = 9101645) B9101645
theorem B6149783 : Blo 1796099 6149783 := bstep (se 1 (by rfl) ⟨4612337, by rfl⟩ : syracuseStep 6149783 = 9224675) B9224675
theorem B2021035 : Blo 1796099 2021035 := bstep (se 1 (by rfl) ⟨1515776, by rfl⟩ : syracuseStep 2021035 = 3031553) B3031553
theorem B13653683 : Blo 1796099 13653683 := bstep (se 1 (by rfl) ⟨10240262, by rfl⟩ : syracuseStep 13653683 = 20480525) B20480525
theorem B4044491 : Blo 1796099 4044491 := bstep (se 1 (by rfl) ⟨3033368, by rfl⟩ : syracuseStep 4044491 = 6066737) B6066737
theorem B4044545 : Blo 1796099 4044545 := bstep (se 2 (by rfl) ⟨1516704, by rfl⟩ : syracuseStep 4044545 = 3033409) B3033409
theorem B2021143 : Blo 1796099 2021143 := bstep (se 1 (by rfl) ⟨1515857, by rfl⟩ : syracuseStep 2021143 = 3031715) B3031715
theorem B9099053 : Blo 1796099 9099053 := bstep (se 3 (by rfl) ⟨1706072, by rfl⟩ : syracuseStep 9099053 = 3412145) B3412145
theorem B6068033 : Blo 1796099 6068033 := bstep (se 2 (by rfl) ⟨2275512, by rfl⟩ : syracuseStep 6068033 = 4551025) B4551025
theorem B7673773 : Blo 1796099 7673773 := bstep (se 3 (by rfl) ⟨1438832, by rfl⟩ : syracuseStep 7673773 = 2877665) B2877665
theorem B2021323 : Blo 1796099 2021323 := bstep (se 1 (by rfl) ⟨1515992, by rfl⟩ : syracuseStep 2021323 = 3031985) B3031985
theorem B5117899 : Blo 1796099 5117899 := bstep (se 1 (by rfl) ⟨3838424, by rfl⟩ : syracuseStep 5117899 = 7676849) B7676849
theorem B7780313 : Blo 1796099 7780313 := bstep (se 2 (by rfl) ⟨2917617, by rfl⟩ : syracuseStep 7780313 = 5835235) B5835235
theorem B4044761 : Blo 1796099 4044761 := bstep (se 2 (by rfl) ⟨1516785, by rfl⟩ : syracuseStep 4044761 = 3033571) B3033571
theorem B6821891 : Blo 1796099 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B3840023 : Blo 1796099 3840023 := bstep (se 1 (by rfl) ⟨2880017, by rfl⟩ : syracuseStep 3840023 = 5760035) B5760035
theorem B4044851 : Blo 1796099 4044851 := bstep (se 1 (by rfl) ⟨3033638, by rfl⟩ : syracuseStep 4044851 = 6067277) B6067277
theorem B2021431 : Blo 1796099 2021431 := bstep (se 1 (by rfl) ⟨1516073, by rfl⟩ : syracuseStep 2021431 = 3032147) B3032147
theorem B3840065 : Blo 1796099 3840065 := bstep (se 2 (by rfl) ⟨1440024, by rfl⟩ : syracuseStep 3840065 = 2880049) B2880049
theorem B4044887 : Blo 1796099 4044887 := bstep (se 1 (by rfl) ⟨3033665, by rfl⟩ : syracuseStep 4044887 = 6067331) B6067331
theorem B30709853 : Blo 1796099 30709853 := bstep (se 3 (by rfl) ⟨5758097, by rfl⟩ : syracuseStep 30709853 = 11516195) B11516195
theorem B9345203 : Blo 1796099 9345203 := bstep (se 1 (by rfl) ⟨7008902, by rfl⟩ : syracuseStep 9345203 = 14017805) B14017805
theorem B2275543 : Blo 1796099 2275543 := bstep (se 1 (by rfl) ⟨1706657, by rfl⟩ : syracuseStep 2275543 = 3413315) B3413315
theorem B5118173 : Blo 1796099 5118173 := bstep (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) B1919315
theorem B2021611 : Blo 1796099 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B7674115 : Blo 1796099 7674115 := bstep (se 1 (by rfl) ⟨5755586, by rfl⟩ : syracuseStep 7674115 = 11511173) B11511173
theorem B4045067 : Blo 1796099 4045067 := bstep (se 1 (by rfl) ⟨3033800, by rfl⟩ : syracuseStep 4045067 = 6067601) B6067601
theorem B4045121 : Blo 1796099 4045121 := bstep (se 2 (by rfl) ⟨1516920, by rfl⟩ : syracuseStep 4045121 = 3033841) B3033841
theorem B2021719 : Blo 1796099 2021719 := bstep (se 1 (by rfl) ⟨1516289, by rfl⟩ : syracuseStep 2021719 = 3032579) B3032579
theorem B6068573 : Blo 1796099 6068573 := bstep (se 3 (by rfl) ⟨1137857, by rfl⟩ : syracuseStep 6068573 = 2275715) B2275715
theorem B8632727 : Blo 1796099 8632727 := bstep (se 1 (by rfl) ⟨6474545, by rfl⟩ : syracuseStep 8632727 = 12949091) B12949091
theorem B26606003 : Blo 1796099 26606003 := bstep (se 1 (by rfl) ⟨19954502, by rfl⟩ : syracuseStep 26606003 = 39909005) B39909005
theorem B11516377 : Blo 1796099 11516377 := bstep (se 2 (by rfl) ⟨4318641, by rfl⟩ : syracuseStep 11516377 = 8637283) B8637283
theorem B2021899 : Blo 1796099 2021899 := bstep (se 1 (by rfl) ⟨1516424, by rfl⟩ : syracuseStep 2021899 = 3032849) B3032849
theorem B23026193 : Blo 1796099 23026193 := bstep (se 2 (by rfl) ⟨8634822, by rfl⟩ : syracuseStep 23026193 = 17269645) B17269645
theorem B15358481 : Blo 1796099 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B4045337 : Blo 1796099 4045337 := bstep (se 2 (by rfl) ⟨1517001, by rfl⟩ : syracuseStep 4045337 = 3034003) B3034003
theorem B5118515 : Blo 1796099 5118515 := bstep (se 1 (by rfl) ⟨3838886, by rfl⟩ : syracuseStep 5118515 = 7677773) B7677773
theorem B4045427 : Blo 1796099 4045427 := bstep (se 1 (by rfl) ⟨3034070, by rfl⟩ : syracuseStep 4045427 = 6068141) B6068141
theorem B2022007 : Blo 1796099 2022007 := bstep (se 1 (by rfl) ⟨1516505, by rfl⟩ : syracuseStep 2022007 = 3033011) B3033011
theorem B4045463 : Blo 1796099 4045463 := bstep (se 1 (by rfl) ⟨3034097, by rfl⟩ : syracuseStep 4045463 = 6068195) B6068195
theorem B3693313 : Blo 1796099 3693313 := bstep (se 2 (by rfl) ⟨1384992, by rfl⟩ : syracuseStep 3693313 = 2769985) B2769985
theorem B2022187 : Blo 1796099 2022187 := bstep (se 1 (by rfl) ⟨1516640, by rfl⟩ : syracuseStep 2022187 = 3033281) B3033281
theorem B4045643 : Blo 1796099 4045643 := bstep (se 1 (by rfl) ⟨3034232, by rfl⟩ : syracuseStep 4045643 = 6068465) B6068465
theorem B4045697 : Blo 1796099 4045697 := bstep (se 2 (by rfl) ⟨1517136, by rfl⟩ : syracuseStep 4045697 = 3034273) B3034273
theorem B2022295 : Blo 1796099 2022295 := bstep (se 1 (by rfl) ⟨1516721, by rfl⟩ : syracuseStep 2022295 = 3033443) B3033443
theorem B2694155 : Blo 1796099 2694155 := bstep (se 1 (by rfl) ⟨2020616, by rfl⟩ : syracuseStep 2694155 = 4041233) B4041233
theorem B2694167 : Blo 1796099 2694167 := bstep (se 1 (by rfl) ⟨2020625, by rfl⟩ : syracuseStep 2694167 = 4041251) B4041251
theorem B2022475 : Blo 1796099 2022475 := bstep (se 1 (by rfl) ⟨1516856, by rfl⟩ : syracuseStep 2022475 = 3033713) B3033713
theorem B2694233 : Blo 1796099 2694233 := bstep (se 2 (by rfl) ⟨1010337, by rfl⟩ : syracuseStep 2694233 = 2020675) B2020675
theorem B3284107 : Blo 1796099 3284107 := bstep (se 1 (by rfl) ⟨2463080, by rfl⟩ : syracuseStep 3284107 = 4926161) B4926161
theorem B2022583 : Blo 1796099 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B7675073 : Blo 1796099 7675073 := bstep (se 2 (by rfl) ⟨2878152, by rfl⟩ : syracuseStep 7675073 = 5756305) B5756305
theorem B2694347 : Blo 1796099 2694347 := bstep (se 1 (by rfl) ⟨2020760, by rfl⟩ : syracuseStep 2694347 = 4041521) B4041521
theorem B2694359 : Blo 1796099 2694359 := bstep (se 1 (by rfl) ⟨2020769, by rfl⟩ : syracuseStep 2694359 = 4041539) B4041539
theorem B3644633 : Blo 1796099 3644633 := bstep (se 2 (by rfl) ⟨1366737, by rfl⟩ : syracuseStep 3644633 = 2733475) B2733475
theorem B2694425 : Blo 1796099 2694425 := bstep (se 2 (by rfl) ⟨1010409, by rfl⟩ : syracuseStep 2694425 = 2020819) B2020819
theorem B2022763 : Blo 1796099 2022763 := bstep (se 1 (by rfl) ⟨1517072, by rfl⟩ : syracuseStep 2022763 = 3034145) B3034145
theorem B2694539 : Blo 1796099 2694539 := bstep (se 1 (by rfl) ⟨2020904, by rfl⟩ : syracuseStep 2694539 = 4041809) B4041809
theorem B2694551 : Blo 1796099 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B2694617 : Blo 1796099 2694617 := bstep (se 2 (by rfl) ⟨1010481, by rfl⟩ : syracuseStep 2694617 = 2020963) B2020963
theorem B13647365 : Blo 1796099 13647365 := bstep (se 4 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 13647365 = 2558881) B2558881
theorem B12959297 : Blo 1796099 12959297 := bstep (se 2 (by rfl) ⟨4859736, by rfl⟩ : syracuseStep 12959297 = 9719473) B9719473
theorem B2694731 : Blo 1796099 2694731 := bstep (se 1 (by rfl) ⟨2021048, by rfl⟩ : syracuseStep 2694731 = 4042097) B4042097
theorem B2694743 : Blo 1796099 2694743 := bstep (se 1 (by rfl) ⟨2021057, by rfl⟩ : syracuseStep 2694743 = 4042115) B4042115
theorem B2694809 : Blo 1796099 2694809 := bstep (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) B2021107
theorem B2694923 : Blo 1796099 2694923 := bstep (se 1 (by rfl) ⟨2021192, by rfl⟩ : syracuseStep 2694923 = 4042385) B4042385
theorem B2694935 : Blo 1796099 2694935 := bstep (se 1 (by rfl) ⟨2021201, by rfl⟩ : syracuseStep 2694935 = 4042403) B4042403
theorem B4316951 : Blo 1796099 4316951 := bstep (se 1 (by rfl) ⟨3237713, by rfl⟩ : syracuseStep 4316951 = 6475427) B6475427
theorem B2695001 : Blo 1796099 2695001 := bstep (se 2 (by rfl) ⟨1010625, by rfl⟩ : syracuseStep 2695001 = 2021251) B2021251
theorem B2695115 : Blo 1796099 2695115 := bstep (se 1 (by rfl) ⟨2021336, by rfl⟩ : syracuseStep 2695115 = 4042673) B4042673
theorem B2695127 : Blo 1796099 2695127 := bstep (se 1 (by rfl) ⟨2021345, by rfl⟩ : syracuseStep 2695127 = 4042691) B4042691
theorem B2695175 : Blo 1796099 2695175 := bstep (se 1 (by rfl) ⟨2021381, by rfl⟩ : syracuseStep 2695175 = 4042763) B4042763
theorem B5537803 : Blo 1796099 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B8634379 : Blo 1796099 8634379 := bstep (se 1 (by rfl) ⟨6475784, by rfl⟩ : syracuseStep 8634379 = 12951569) B12951569
theorem B2695211 : Blo 1796099 2695211 := bstep (se 1 (by rfl) ⟨2021408, by rfl⟩ : syracuseStep 2695211 = 4042817) B4042817
theorem B2695241 : Blo 1796099 2695241 := bstep (se 2 (by rfl) ⟨1010715, by rfl⟩ : syracuseStep 2695241 = 2021431) B2021431
theorem B2187383 : Blo 1796099 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B3031175 : Blo 1796099 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B2695355 : Blo 1796099 2695355 := bstep (se 1 (by rfl) ⟨2021516, by rfl⟩ : syracuseStep 2695355 = 4043033) B4043033
theorem B2695415 : Blo 1796099 2695415 := bstep (se 1 (by rfl) ⟨2021561, by rfl⟩ : syracuseStep 2695415 = 4043123) B4043123
theorem B2695439 : Blo 1796099 2695439 := bstep (se 1 (by rfl) ⟨2021579, by rfl⟩ : syracuseStep 2695439 = 4043159) B4043159
theorem B4858127 : Blo 1796099 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B2695481 : Blo 1796099 2695481 := bstep (se 2 (by rfl) ⟨1010805, by rfl⟩ : syracuseStep 2695481 = 2021611) B2021611
theorem B10232153 : Blo 1796099 10232153 := bstep (se 2 (by rfl) ⟨3837057, by rfl⟩ : syracuseStep 10232153 = 7674115) B7674115
theorem B6062471 : Blo 1796099 6062471 := bstep (se 1 (by rfl) ⟨4546853, by rfl⟩ : syracuseStep 6062471 = 9093707) B9093707
theorem B2695559 : Blo 1796099 2695559 := bstep (se 1 (by rfl) ⟨2021669, by rfl⟩ : syracuseStep 2695559 = 4043339) B4043339
theorem B2695595 : Blo 1796099 2695595 := bstep (se 1 (by rfl) ⟨2021696, by rfl⟩ : syracuseStep 2695595 = 4043393) B4043393
theorem B2695625 : Blo 1796099 2695625 := bstep (se 2 (by rfl) ⟨1010859, by rfl⟩ : syracuseStep 2695625 = 2021719) B2021719
theorem B13648337 : Blo 1796099 13648337 := bstep (se 2 (by rfl) ⟨5118126, by rfl⟩ : syracuseStep 13648337 = 10236253) B10236253
theorem B4547087 : Blo 1796099 4547087 := bstep (se 1 (by rfl) ⟨3410315, by rfl⟩ : syracuseStep 4547087 = 6820631) B6820631
theorem B13828637 : Blo 1796099 13828637 := bstep (se 3 (by rfl) ⟨2592869, by rfl⟩ : syracuseStep 13828637 = 5185739) B5185739
theorem B2695739 : Blo 1796099 2695739 := bstep (se 1 (by rfl) ⟨2021804, by rfl⟩ : syracuseStep 2695739 = 4043609) B4043609
theorem B2695799 : Blo 1796099 2695799 := bstep (se 1 (by rfl) ⟨2021849, by rfl⟩ : syracuseStep 2695799 = 4043699) B4043699
theorem B2048647 : Blo 1796099 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B2695823 : Blo 1796099 2695823 := bstep (se 1 (by rfl) ⟨2021867, by rfl⟩ : syracuseStep 2695823 = 4043735) B4043735
theorem B2695865 : Blo 1796099 2695865 := bstep (se 2 (by rfl) ⟨1010949, by rfl⟩ : syracuseStep 2695865 = 2021899) B2021899
theorem B9093869 : Blo 1796099 9093869 := bstep (se 3 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 9093869 = 3410201) B3410201
theorem B6062849 : Blo 1796099 6062849 := bstep (se 2 (by rfl) ⟨2273568, by rfl⟩ : syracuseStep 6062849 = 4547137) B4547137
theorem B2695943 : Blo 1796099 2695943 := bstep (se 1 (by rfl) ⟨2021957, by rfl⟩ : syracuseStep 2695943 = 4043915) B4043915
theorem B3031823 : Blo 1796099 3031823 := bstep (se 1 (by rfl) ⟨2273867, by rfl⟩ : syracuseStep 3031823 = 4547735) B4547735
theorem B2695979 : Blo 1796099 2695979 := bstep (se 1 (by rfl) ⟨2021984, by rfl⟩ : syracuseStep 2695979 = 4043969) B4043969
theorem B8635187 : Blo 1796099 8635187 := bstep (se 1 (by rfl) ⟨6476390, by rfl⟩ : syracuseStep 8635187 = 12952781) B12952781
theorem B9102131 : Blo 1796099 9102131 := bstep (se 1 (by rfl) ⟨6826598, by rfl⟩ : syracuseStep 9102131 = 13653197) B13653197
theorem B2696009 : Blo 1796099 2696009 := bstep (se 2 (by rfl) ⟨1011003, by rfl⟩ : syracuseStep 2696009 = 2022007) B2022007
theorem B3236755 : Blo 1796099 3236755 := bstep (se 1 (by rfl) ⟨2427566, by rfl⟩ : syracuseStep 3236755 = 4855133) B4855133
theorem B2696123 : Blo 1796099 2696123 := bstep (se 1 (by rfl) ⟨2022092, by rfl⟩ : syracuseStep 2696123 = 4044185) B4044185
theorem B2696183 : Blo 1796099 2696183 := bstep (se 1 (by rfl) ⟨2022137, by rfl⟩ : syracuseStep 2696183 = 4044275) B4044275
theorem B2696207 : Blo 1796099 2696207 := bstep (se 1 (by rfl) ⟨2022155, by rfl⟩ : syracuseStep 2696207 = 4044311) B4044311
theorem B2696249 : Blo 1796099 2696249 := bstep (se 2 (by rfl) ⟨1011093, by rfl⟩ : syracuseStep 2696249 = 2022187) B2022187
theorem B4097083 : Blo 1796099 4097083 := bstep (se 1 (by rfl) ⟨3072812, by rfl⟩ : syracuseStep 4097083 = 6145625) B6145625
theorem B9102455 : Blo 1796099 9102455 := bstep (se 1 (by rfl) ⟨6826841, by rfl⟩ : syracuseStep 9102455 = 13653683) B13653683
theorem B2696327 : Blo 1796099 2696327 := bstep (se 1 (by rfl) ⟨2022245, by rfl⟩ : syracuseStep 2696327 = 4044491) B4044491
theorem B2696363 : Blo 1796099 2696363 := bstep (se 1 (by rfl) ⟨2022272, by rfl⟩ : syracuseStep 2696363 = 4044545) B4044545
theorem B4547785 : Blo 1796099 4547785 := bstep (se 2 (by rfl) ⟨1705419, by rfl⟩ : syracuseStep 4547785 = 3410839) B3410839
theorem B2696393 : Blo 1796099 2696393 := bstep (se 2 (by rfl) ⟨1011147, by rfl⟩ : syracuseStep 2696393 = 2022295) B2022295
theorem B4859165 : Blo 1796099 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B3032363 : Blo 1796099 3032363 := bstep (se 1 (by rfl) ⟨2274272, by rfl⟩ : syracuseStep 3032363 = 4548545) B4548545
theorem B2696507 : Blo 1796099 2696507 := bstep (se 1 (by rfl) ⟨2022380, by rfl⟩ : syracuseStep 2696507 = 4044761) B4044761
theorem B4547927 : Blo 1796099 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B2696567 : Blo 1796099 2696567 := bstep (se 1 (by rfl) ⟨2022425, by rfl⟩ : syracuseStep 2696567 = 4044851) B4044851
theorem B2696591 : Blo 1796099 2696591 := bstep (se 1 (by rfl) ⟨2022443, by rfl⟩ : syracuseStep 2696591 = 4044887) B4044887
theorem B20473235 : Blo 1796099 20473235 := bstep (se 1 (by rfl) ⟨15354926, by rfl⟩ : syracuseStep 20473235 = 30709853) B30709853
theorem B2696633 : Blo 1796099 2696633 := bstep (se 2 (by rfl) ⟨1011237, by rfl⟩ : syracuseStep 2696633 = 2022475) B2022475
theorem B2696711 : Blo 1796099 2696711 := bstep (se 1 (by rfl) ⟨2022533, by rfl⟩ : syracuseStep 2696711 = 4045067) B4045067
theorem B9094679 : Blo 1796099 9094679 := bstep (se 1 (by rfl) ⟨6821009, by rfl⟩ : syracuseStep 9094679 = 13642019) B13642019
theorem B6063659 : Blo 1796099 6063659 := bstep (se 1 (by rfl) ⟨4547744, by rfl⟩ : syracuseStep 6063659 = 9095489) B9095489
theorem B2696747 : Blo 1796099 2696747 := bstep (se 1 (by rfl) ⟨2022560, by rfl⟩ : syracuseStep 2696747 = 4045121) B4045121
theorem B2696777 : Blo 1796099 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B3032761 : Blo 1796099 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B2696891 : Blo 1796099 2696891 := bstep (se 1 (by rfl) ⟨2022668, by rfl⟩ : syracuseStep 2696891 = 4045337) B4045337
theorem B11667137 : Blo 1796099 11667137 := bstep (se 2 (by rfl) ⟨4375176, by rfl⟩ : syracuseStep 11667137 = 8750353) B8750353
theorem B2696951 : Blo 1796099 2696951 := bstep (se 1 (by rfl) ⟨2022713, by rfl⟩ : syracuseStep 2696951 = 4045427) B4045427
theorem B2696975 : Blo 1796099 2696975 := bstep (se 1 (by rfl) ⟨2022731, by rfl⟩ : syracuseStep 2696975 = 4045463) B4045463
theorem B17278757 : Blo 1796099 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B87476021 : Blo 1796099 87476021 := bstep (se 5 (by rfl) ⟨4100438, by rfl⟩ : syracuseStep 87476021 = 8200877) B8200877
theorem B2697017 : Blo 1796099 2697017 := bstep (se 2 (by rfl) ⟨1011381, by rfl⟩ : syracuseStep 2697017 = 2022763) B2022763
theorem B17270603 : Blo 1796099 17270603 := bstep (se 1 (by rfl) ⟨12952952, by rfl⟩ : syracuseStep 17270603 = 25905905) B25905905
theorem B2697095 : Blo 1796099 2697095 := bstep (se 1 (by rfl) ⟨2022821, by rfl⟩ : syracuseStep 2697095 = 4045643) B4045643
theorem B2697131 : Blo 1796099 2697131 := bstep (se 1 (by rfl) ⟨2022848, by rfl⟩ : syracuseStep 2697131 = 4045697) B4045697
theorem B1796103 : Blo 1796099 1796103 := bstep (se 1 (by rfl) ⟨1347077, by rfl⟩ : syracuseStep 1796103 = 2694155) B2694155
theorem B1796111 : Blo 1796099 1796111 := bstep (se 1 (by rfl) ⟨1347083, by rfl⟩ : syracuseStep 1796111 = 2694167) B2694167
theorem B1796155 : Blo 1796099 1796155 := bstep (se 1 (by rfl) ⟨1347116, by rfl⟩ : syracuseStep 1796155 = 2694233) B2694233
theorem B1796231 : Blo 1796099 1796231 := bstep (se 1 (by rfl) ⟨1347173, by rfl⟩ : syracuseStep 1796231 = 2694347) B2694347
theorem B1796239 : Blo 1796099 1796239 := bstep (se 1 (by rfl) ⟨1347179, by rfl⟩ : syracuseStep 1796239 = 2694359) B2694359
theorem B1796283 : Blo 1796099 1796283 := bstep (se 1 (by rfl) ⟨1347212, by rfl⟩ : syracuseStep 1796283 = 2694425) B2694425
theorem B1796359 : Blo 1796099 1796359 := bstep (se 1 (by rfl) ⟨1347269, by rfl⟩ : syracuseStep 1796359 = 2694539) B2694539
theorem B6473999 : Blo 1796099 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B1796367 : Blo 1796099 1796367 := bstep (se 1 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 1796367 = 2694551) B2694551
theorem B17262881 : Blo 1796099 17262881 := bstep (se 2 (by rfl) ⟨6473580, by rfl⟩ : syracuseStep 17262881 = 12947161) B12947161
theorem B1796411 : Blo 1796099 1796411 := bstep (se 1 (by rfl) ⟨1347308, by rfl⟩ : syracuseStep 1796411 = 2694617) B2694617
theorem B3033463 : Blo 1796099 3033463 := bstep (se 1 (by rfl) ⟨2275097, by rfl⟩ : syracuseStep 3033463 = 4550195) B4550195
theorem B1796487 : Blo 1796099 1796487 := bstep (se 1 (by rfl) ⟨1347365, by rfl⟩ : syracuseStep 1796487 = 2694731) B2694731
theorem B2050439 : Blo 1796099 2050439 := bstep (se 1 (by rfl) ⟨1537829, by rfl⟩ : syracuseStep 2050439 = 3075659) B3075659
theorem B1796495 : Blo 1796099 1796495 := bstep (se 1 (by rfl) ⟨1347371, by rfl⟩ : syracuseStep 1796495 = 2694743) B2694743
theorem B1796539 : Blo 1796099 1796539 := bstep (se 1 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 1796539 = 2694809) B2694809
theorem B1796615 : Blo 1796099 1796615 := bstep (se 1 (by rfl) ⟨1347461, by rfl⟩ : syracuseStep 1796615 = 2694923) B2694923
theorem B2558471 : Blo 1796099 2558471 := bstep (se 1 (by rfl) ⟨1918853, by rfl⟩ : syracuseStep 2558471 = 3837707) B3837707
theorem B1796623 : Blo 1796099 1796623 := bstep (se 1 (by rfl) ⟨1347467, by rfl⟩ : syracuseStep 1796623 = 2694935) B2694935
theorem B2877967 : Blo 1796099 2877967 := bstep (se 1 (by rfl) ⟨2158475, by rfl⟩ : syracuseStep 2877967 = 4316951) B4316951
theorem B1796667 : Blo 1796099 1796667 := bstep (se 1 (by rfl) ⟨1347500, by rfl⟩ : syracuseStep 1796667 = 2695001) B2695001
theorem B3033659 : Blo 1796099 3033659 := bstep (se 1 (by rfl) ⟨2275244, by rfl⟩ : syracuseStep 3033659 = 4550489) B4550489
theorem B1796743 : Blo 1796099 1796743 := bstep (se 1 (by rfl) ⟨1347557, by rfl⟩ : syracuseStep 1796743 = 2695115) B2695115
theorem B1796751 : Blo 1796099 1796751 := bstep (se 1 (by rfl) ⟨1347563, by rfl⟩ : syracuseStep 1796751 = 2695127) B2695127
theorem B1796795 : Blo 1796099 1796795 := bstep (se 1 (by rfl) ⟨1347596, by rfl⟩ : syracuseStep 1796795 = 2695193) B2695193
theorem B2558665 : Blo 1796099 2558665 := bstep (se 2 (by rfl) ⟨959499, by rfl⟩ : syracuseStep 2558665 = 1918999) B1918999
theorem B1796871 : Blo 1796099 1796871 := bstep (se 1 (by rfl) ⟨1347653, by rfl⟩ : syracuseStep 1796871 = 2695307) B2695307
theorem B1796879 : Blo 1796099 1796879 := bstep (se 1 (by rfl) ⟨1347659, by rfl⟩ : syracuseStep 1796879 = 2695319) B2695319
theorem B1919759 : Blo 1796099 1919759 := bstep (se 1 (by rfl) ⟨1439819, by rfl⟩ : syracuseStep 1919759 = 2879639) B2879639
theorem B19434275 : Blo 1796099 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B1796923 : Blo 1796099 1796923 := bstep (se 1 (by rfl) ⟨1347692, by rfl⟩ : syracuseStep 1796923 = 2695385) B2695385
theorem B6064955 : Blo 1796099 6064955 := bstep (se 1 (by rfl) ⟨4548716, by rfl⟩ : syracuseStep 6064955 = 9097433) B9097433
theorem B1796999 : Blo 1796099 1796999 := bstep (se 1 (by rfl) ⟨1347749, by rfl⟩ : syracuseStep 1796999 = 2695499) B2695499
theorem B1797007 : Blo 1796099 1797007 := bstep (se 1 (by rfl) ⟨1347755, by rfl⟩ : syracuseStep 1797007 = 2695511) B2695511
theorem B70060949 : Blo 1796099 70060949 := bstep (se 6 (by rfl) ⟨1642053, by rfl⟩ : syracuseStep 70060949 = 3284107) B3284107
theorem B31124405 : Blo 1796099 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B1797051 : Blo 1796099 1797051 := bstep (se 1 (by rfl) ⟨1347788, by rfl⟩ : syracuseStep 1797051 = 2695577) B2695577
theorem B2878409 : Blo 1796099 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B3034057 : Blo 1796099 3034057 := bstep (se 2 (by rfl) ⟨1137771, by rfl⟩ : syracuseStep 3034057 = 2275543) B2275543
theorem B1797127 : Blo 1796099 1797127 := bstep (se 1 (by rfl) ⟨1347845, by rfl⟩ : syracuseStep 1797127 = 2695691) B2695691
theorem B1797135 : Blo 1796099 1797135 := bstep (se 1 (by rfl) ⟨1347851, by rfl⟩ : syracuseStep 1797135 = 2695703) B2695703
theorem B1797179 : Blo 1796099 1797179 := bstep (se 1 (by rfl) ⟨1347884, by rfl⟩ : syracuseStep 1797179 = 2695769) B2695769
theorem B4041863 : Blo 1796099 4041863 := bstep (se 1 (by rfl) ⟨3031397, by rfl⟩ : syracuseStep 4041863 = 6062795) B6062795
theorem B1797255 : Blo 1796099 1797255 := bstep (se 1 (by rfl) ⟨1347941, by rfl⟩ : syracuseStep 1797255 = 2695883) B2695883
theorem B1797263 : Blo 1796099 1797263 := bstep (se 1 (by rfl) ⟨1347947, by rfl⟩ : syracuseStep 1797263 = 2695895) B2695895
theorem B1797307 : Blo 1796099 1797307 := bstep (se 1 (by rfl) ⟨1347980, by rfl⟩ : syracuseStep 1797307 = 2695961) B2695961
theorem B9719021 : Blo 1796099 9719021 := bstep (se 3 (by rfl) ⟨1822316, by rfl⟩ : syracuseStep 9719021 = 3644633) B3644633
theorem B2559223 : Blo 1796099 2559223 := bstep (se 1 (by rfl) ⟨1919417, by rfl⟩ : syracuseStep 2559223 = 3838835) B3838835
theorem B1797383 : Blo 1796099 1797383 := bstep (se 1 (by rfl) ⟨1348037, by rfl⟩ : syracuseStep 1797383 = 2696075) B2696075
theorem B1797391 : Blo 1796099 1797391 := bstep (se 1 (by rfl) ⟨1348043, by rfl⟩ : syracuseStep 1797391 = 2696087) B2696087
theorem B6065441 : Blo 1796099 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B15355169 : Blo 1796099 15355169 := bstep (se 2 (by rfl) ⟨5758188, by rfl⟩ : syracuseStep 15355169 = 11516377) B11516377
theorem B4042043 : Blo 1796099 4042043 := bstep (se 1 (by rfl) ⟨3031532, by rfl⟩ : syracuseStep 4042043 = 6063065) B6063065
theorem B87633211 : Blo 1796099 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B1797435 : Blo 1796099 1797435 := bstep (se 1 (by rfl) ⟨1348076, by rfl⟩ : syracuseStep 1797435 = 2696153) B2696153
theorem B4550003 : Blo 1796099 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B1797511 : Blo 1796099 1797511 := bstep (se 1 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 1797511 = 2696267) B2696267
theorem B1797519 : Blo 1796099 1797519 := bstep (se 1 (by rfl) ⟨1348139, by rfl⟩ : syracuseStep 1797519 = 2696279) B2696279
theorem B3837331 : Blo 1796099 3837331 := bstep (se 1 (by rfl) ⟨2877998, by rfl⟩ : syracuseStep 3837331 = 5755997) B5755997
theorem B4042169 : Blo 1796099 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B10235321 : Blo 1796099 10235321 := bstep (se 2 (by rfl) ⟨3838245, by rfl⟩ : syracuseStep 10235321 = 7676491) B7676491
theorem B1797563 : Blo 1796099 1797563 := bstep (se 1 (by rfl) ⟨1348172, by rfl⟩ : syracuseStep 1797563 = 2696345) B2696345
theorem B1797639 : Blo 1796099 1797639 := bstep (se 1 (by rfl) ⟨1348229, by rfl⟩ : syracuseStep 1797639 = 2696459) B2696459
theorem B1797647 : Blo 1796099 1797647 := bstep (se 1 (by rfl) ⟨1348235, by rfl⟩ : syracuseStep 1797647 = 2696471) B2696471
theorem B1797691 : Blo 1796099 1797691 := bstep (se 1 (by rfl) ⟨1348268, by rfl⟩ : syracuseStep 1797691 = 2696537) B2696537
theorem B7679549 : Blo 1796099 7679549 := bstep (se 3 (by rfl) ⟨1439915, by rfl⟩ : syracuseStep 7679549 = 2879831) B2879831
theorem B1797767 : Blo 1796099 1797767 := bstep (se 1 (by rfl) ⟨1348325, by rfl⟩ : syracuseStep 1797767 = 2696651) B2696651
theorem B1797775 : Blo 1796099 1797775 := bstep (se 1 (by rfl) ⟨1348331, by rfl⟩ : syracuseStep 1797775 = 2696663) B2696663
theorem B1797819 : Blo 1796099 1797819 := bstep (se 1 (by rfl) ⟨1348364, by rfl⟩ : syracuseStep 1797819 = 2696729) B2696729
theorem B21860057 : Blo 1796099 21860057 := bstep (se 2 (by rfl) ⟨8197521, by rfl⟩ : syracuseStep 21860057 = 16395043) B16395043
theorem B1797895 : Blo 1796099 1797895 := bstep (se 1 (by rfl) ⟨1348421, by rfl⟩ : syracuseStep 1797895 = 2696843) B2696843
theorem B4042511 : Blo 1796099 4042511 := bstep (se 1 (by rfl) ⟨3031883, by rfl⟩ : syracuseStep 4042511 = 6063767) B6063767
theorem B1797903 : Blo 1796099 1797903 := bstep (se 1 (by rfl) ⟨1348427, by rfl⟩ : syracuseStep 1797903 = 2696855) B2696855
theorem B4042529 : Blo 1796099 4042529 := bstep (se 2 (by rfl) ⟨1515948, by rfl⟩ : syracuseStep 4042529 = 3031897) B3031897
theorem B6917921 : Blo 1796099 6917921 := bstep (se 2 (by rfl) ⟨2594220, by rfl⟩ : syracuseStep 6917921 = 5188441) B5188441
theorem B1797947 : Blo 1796099 1797947 := bstep (se 1 (by rfl) ⟨1348460, by rfl⟩ : syracuseStep 1797947 = 2696921) B2696921
theorem B13840217 : Blo 1796099 13840217 := bstep (se 2 (by rfl) ⟨5190081, by rfl⟩ : syracuseStep 13840217 = 10380163) B10380163
theorem B6066035 : Blo 1796099 6066035 := bstep (se 1 (by rfl) ⟨4549526, by rfl⟩ : syracuseStep 6066035 = 9099053) B9099053
theorem B4550519 : Blo 1796099 4550519 := bstep (se 1 (by rfl) ⟨3412889, by rfl⟩ : syracuseStep 4550519 = 6825779) B6825779
theorem B1798023 : Blo 1796099 1798023 := bstep (se 1 (by rfl) ⟨1348517, by rfl⟩ : syracuseStep 1798023 = 2697035) B2697035
theorem B1798031 : Blo 1796099 1798031 := bstep (se 1 (by rfl) ⟨1348523, by rfl⟩ : syracuseStep 1798031 = 2697047) B2697047
theorem B2559929 : Blo 1796099 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B1798075 : Blo 1796099 1798075 := bstep (se 1 (by rfl) ⟨1348556, by rfl⟩ : syracuseStep 1798075 = 2697113) B2697113
theorem B10923997 : Blo 1796099 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B19697669 : Blo 1796099 19697669 := bstep (se 4 (by rfl) ⟨1846656, by rfl⟩ : syracuseStep 19697669 = 3693313) B3693313
theorem B2560015 : Blo 1796099 2560015 := bstep (se 1 (by rfl) ⟨1920011, by rfl⟩ : syracuseStep 2560015 = 3840023) B3840023
theorem B2560043 : Blo 1796099 2560043 := bstep (se 1 (by rfl) ⟨1920032, by rfl⟩ : syracuseStep 2560043 = 3840065) B3840065
theorem B6230135 : Blo 1796099 6230135 := bstep (se 1 (by rfl) ⟨4672601, by rfl⟩ : syracuseStep 6230135 = 9345203) B9345203
theorem B4042871 : Blo 1796099 4042871 := bstep (se 1 (by rfl) ⟨3032153, by rfl⟩ : syracuseStep 4042871 = 6064307) B6064307
theorem B2732167 : Blo 1796099 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B3412115 : Blo 1796099 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B5755151 : Blo 1796099 5755151 := bstep (se 1 (by rfl) ⟨4316363, by rfl⟩ : syracuseStep 5755151 = 8632727) B8632727
theorem B11514145 : Blo 1796099 11514145 := bstep (se 2 (by rfl) ⟨4317804, by rfl⟩ : syracuseStep 11514145 = 8635609) B8635609
theorem B4043051 : Blo 1796099 4043051 := bstep (se 1 (by rfl) ⟨3032288, by rfl⟩ : syracuseStep 4043051 = 6064577) B6064577
theorem B3412343 : Blo 1796099 3412343 := bstep (se 1 (by rfl) ⟨2559257, by rfl⟩ : syracuseStep 3412343 = 5118515) B5118515
theorem B19427789 : Blo 1796099 19427789 := bstep (se 3 (by rfl) ⟨3642710, by rfl⟩ : syracuseStep 19427789 = 7285421) B7285421
theorem B9097757 : Blo 1796099 9097757 := bstep (se 3 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 9097757 = 3411659) B3411659
theorem B44331587 : Blo 1796099 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B2732617 : Blo 1796099 2732617 := bstep (se 2 (by rfl) ⟨1024731, by rfl⟩ : syracuseStep 2732617 = 2049463) B2049463
theorem B10924631 : Blo 1796099 10924631 := bstep (se 1 (by rfl) ⟨8193473, by rfl⟩ : syracuseStep 10924631 = 16386947) B16386947
theorem B4043411 : Blo 1796099 4043411 := bstep (se 1 (by rfl) ⟨3032558, by rfl⟩ : syracuseStep 4043411 = 6065117) B6065117
theorem B5116601 : Blo 1796099 5116601 := bstep (se 2 (by rfl) ⟨1918725, by rfl⟩ : syracuseStep 5116601 = 3837451) B3837451
theorem B4043465 : Blo 1796099 4043465 := bstep (se 2 (by rfl) ⟨1516299, by rfl⟩ : syracuseStep 4043465 = 3032599) B3032599
theorem B9712385 : Blo 1796099 9712385 := bstep (se 2 (by rfl) ⟨3642144, by rfl⟩ : syracuseStep 9712385 = 7284289) B7284289
theorem B5116715 : Blo 1796099 5116715 := bstep (se 1 (by rfl) ⟨3837536, by rfl⟩ : syracuseStep 5116715 = 7675073) B7675073
theorem B2732843 : Blo 1796099 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B2159479 : Blo 1796099 2159479 := bstep (se 1 (by rfl) ⟨1619609, by rfl⟩ : syracuseStep 2159479 = 3239219) B3239219
theorem B9098243 : Blo 1796099 9098243 := bstep (se 1 (by rfl) ⟨6823682, by rfl⟩ : syracuseStep 9098243 = 13647365) B13647365
theorem B30692357 : Blo 1796099 30692357 := bstep (se 4 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 30692357 = 5754817) B5754817
theorem B8639531 : Blo 1796099 8639531 := bstep (se 1 (by rfl) ⟨6479648, by rfl⟩ : syracuseStep 8639531 = 12959297) B12959297
theorem B2274475 : Blo 1796099 2274475 := bstep (se 1 (by rfl) ⟨1705856, by rfl⟩ : syracuseStep 2274475 = 3411713) B3411713
theorem B8631497 : Blo 1796099 8631497 := bstep (se 2 (by rfl) ⟨3236811, by rfl⟩ : syracuseStep 8631497 = 6473623) B6473623
theorem B3839177 : Blo 1796099 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B20747501 : Blo 1796099 20747501 := bstep (se 3 (by rfl) ⟨3890156, by rfl⟩ : syracuseStep 20747501 = 7780313) B7780313
theorem B8631611 : Blo 1796099 8631611 := bstep (se 1 (by rfl) ⟨6473708, by rfl⟩ : syracuseStep 8631611 = 12947417) B12947417
theorem B4044167 : Blo 1796099 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B6821405 : Blo 1796099 6821405 := bstep (se 3 (by rfl) ⟨1279013, by rfl⟩ : syracuseStep 6821405 = 2558027) B2558027
theorem B4044347 : Blo 1796099 4044347 := bstep (se 1 (by rfl) ⟨3033260, by rfl⟩ : syracuseStep 4044347 = 6066521) B6066521
theorem B20756087 : Blo 1796099 20756087 := bstep (se 1 (by rfl) ⟨15567065, by rfl⟩ : syracuseStep 20756087 = 31134131) B31134131
theorem B2020999 : Blo 1796099 2020999 := bstep (se 1 (by rfl) ⟨1515749, by rfl⟩ : syracuseStep 2020999 = 3031499) B3031499
theorem B4044473 : Blo 1796099 4044473 := bstep (se 2 (by rfl) ⟨1516677, by rfl⟩ : syracuseStep 4044473 = 3033355) B3033355
theorem B10237711 : Blo 1796099 10237711 := bstep (se 1 (by rfl) ⟨7678283, by rfl⟩ : syracuseStep 10237711 = 15356567) B15356567
theorem B2021179 : Blo 1796099 2021179 := bstep (se 1 (by rfl) ⟨1515884, by rfl⟩ : syracuseStep 2021179 = 3031769) B3031769
theorem B5117843 : Blo 1796099 5117843 := bstep (se 1 (by rfl) ⟨3838382, by rfl⟩ : syracuseStep 5117843 = 7676765) B7676765
theorem B15775651 : Blo 1796099 15775651 := bstep (se 1 (by rfl) ⟨11831738, by rfl⟩ : syracuseStep 15775651 = 23663477) B23663477
theorem B4044815 : Blo 1796099 4044815 := bstep (se 1 (by rfl) ⟨3033611, by rfl⟩ : syracuseStep 4044815 = 6067223) B6067223
theorem B4044833 : Blo 1796099 4044833 := bstep (se 2 (by rfl) ⟨1516812, by rfl⟩ : syracuseStep 4044833 = 3033625) B3033625
theorem B2275447 : Blo 1796099 2275447 := bstep (se 1 (by rfl) ⟨1706585, by rfl⟩ : syracuseStep 2275447 = 3413171) B3413171
theorem B3840185 : Blo 1796099 3840185 := bstep (se 2 (by rfl) ⟨1440069, by rfl⟩ : syracuseStep 3840185 = 2880139) B2880139
theorem B6822089 : Blo 1796099 6822089 := bstep (se 2 (by rfl) ⟨2558283, by rfl⟩ : syracuseStep 6822089 = 5116567) B5116567
theorem B2021647 : Blo 1796099 2021647 := bstep (se 1 (by rfl) ⟨1516235, by rfl⟩ : syracuseStep 2021647 = 3032471) B3032471
theorem B5118241 : Blo 1796099 5118241 := bstep (se 2 (by rfl) ⟨1919340, by rfl⟩ : syracuseStep 5118241 = 3838681) B3838681
theorem B4045175 : Blo 1796099 4045175 := bstep (se 1 (by rfl) ⟨3033881, by rfl⟩ : syracuseStep 4045175 = 6067763) B6067763
theorem B70949341 : Blo 1796099 70949341 := bstep (se 3 (by rfl) ⟨13303001, by rfl⟩ : syracuseStep 70949341 = 26606003) B26606003
theorem B4045355 : Blo 1796099 4045355 := bstep (se 1 (by rfl) ⟨3034016, by rfl⟩ : syracuseStep 4045355 = 6068033) B6068033
theorem B9099863 : Blo 1796099 9099863 := bstep (se 1 (by rfl) ⟨6824897, by rfl⟩ : syracuseStep 9099863 = 13649795) B13649795
theorem B9222913 : Blo 1796099 9222913 := bstep (se 2 (by rfl) ⟨3458592, by rfl⟩ : syracuseStep 9222913 = 6917185) B6917185
theorem B87481093 : Blo 1796099 87481093 := bstep (se 4 (by rfl) ⟨8201352, by rfl⟩ : syracuseStep 87481093 = 16402705) B16402705
theorem B2022151 : Blo 1796099 2022151 := bstep (se 1 (by rfl) ⟨1516613, by rfl⟩ : syracuseStep 2022151 = 3033227) B3033227
theorem B4045715 : Blo 1796099 4045715 := bstep (se 1 (by rfl) ⟨3034286, by rfl⟩ : syracuseStep 4045715 = 6068573) B6068573
theorem B4316057 : Blo 1796099 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B2022331 : Blo 1796099 2022331 := bstep (se 1 (by rfl) ⟨1516748, by rfl⟩ : syracuseStep 2022331 = 3033497) B3033497
theorem B4316105 : Blo 1796099 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B15350795 : Blo 1796099 15350795 := bstep (se 1 (by rfl) ⟨11513096, by rfl⟩ : syracuseStep 15350795 = 23026193) B23026193
theorem B10238987 : Blo 1796099 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B2694203 : Blo 1796099 2694203 := bstep (se 1 (by rfl) ⟨2020652, by rfl⟩ : syracuseStep 2694203 = 4041305) B4041305
theorem B9100349 : Blo 1796099 9100349 := bstep (se 3 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 9100349 = 3412631) B3412631
theorem B16399421 : Blo 1796099 16399421 := bstep (se 3 (by rfl) ⟨3074891, by rfl⟩ : syracuseStep 16399421 = 6149783) B6149783
theorem B2694263 : Blo 1796099 2694263 := bstep (se 1 (by rfl) ⟨2020697, by rfl⟩ : syracuseStep 2694263 = 4041395) B4041395
theorem B2694287 : Blo 1796099 2694287 := bstep (se 1 (by rfl) ⟨2020715, by rfl⟩ : syracuseStep 2694287 = 4041431) B4041431
theorem B5119129 : Blo 1796099 5119129 := bstep (se 2 (by rfl) ⟨1919673, by rfl⟩ : syracuseStep 5119129 = 3839347) B3839347
theorem B2694329 : Blo 1796099 2694329 := bstep (se 2 (by rfl) ⟨1010373, by rfl⟩ : syracuseStep 2694329 = 2020747) B2020747
theorem B10239169 : Blo 1796099 10239169 := bstep (se 2 (by rfl) ⟨3839688, by rfl⟩ : syracuseStep 10239169 = 7679377) B7679377
theorem B2694407 : Blo 1796099 2694407 := bstep (se 1 (by rfl) ⟨2020805, by rfl⟩ : syracuseStep 2694407 = 4041611) B4041611
theorem B2694443 : Blo 1796099 2694443 := bstep (se 1 (by rfl) ⟨2020832, by rfl⟩ : syracuseStep 2694443 = 4041665) B4041665
theorem B2694473 : Blo 1796099 2694473 := bstep (se 2 (by rfl) ⟨1010427, by rfl⟩ : syracuseStep 2694473 = 2020855) B2020855
theorem B2022799 : Blo 1796099 2022799 := bstep (se 1 (by rfl) ⟨1517099, by rfl⟩ : syracuseStep 2022799 = 3034199) B3034199
theorem B9346457 : Blo 1796099 9346457 := bstep (se 2 (by rfl) ⟨3504921, by rfl⟩ : syracuseStep 9346457 = 7009843) B7009843
theorem B2694587 : Blo 1796099 2694587 := bstep (se 1 (by rfl) ⟨2020940, by rfl⟩ : syracuseStep 2694587 = 4041881) B4041881
theorem B2694647 : Blo 1796099 2694647 := bstep (se 1 (by rfl) ⟨2020985, by rfl⟩ : syracuseStep 2694647 = 4041971) B4041971
theorem B2694671 : Blo 1796099 2694671 := bstep (se 1 (by rfl) ⟨2021003, by rfl⟩ : syracuseStep 2694671 = 4042007) B4042007
theorem B5119517 : Blo 1796099 5119517 := bstep (se 3 (by rfl) ⟨959909, by rfl⟩ : syracuseStep 5119517 = 1919819) B1919819
theorem B2694713 : Blo 1796099 2694713 := bstep (se 2 (by rfl) ⟨1010517, by rfl⟩ : syracuseStep 2694713 = 2021035) B2021035
theorem B12951107 : Blo 1796099 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B5185139 : Blo 1796099 5185139 := bstep (se 1 (by rfl) ⟨3888854, by rfl⟩ : syracuseStep 5185139 = 7777709) B7777709
theorem B2694791 : Blo 1796099 2694791 := bstep (se 1 (by rfl) ⟨2021093, by rfl⟩ : syracuseStep 2694791 = 4042187) B4042187
theorem B2694827 : Blo 1796099 2694827 := bstep (se 1 (by rfl) ⟨2021120, by rfl⟩ : syracuseStep 2694827 = 4042241) B4042241
theorem B2694857 : Blo 1796099 2694857 := bstep (se 2 (by rfl) ⟨1010571, by rfl⟩ : syracuseStep 2694857 = 2021143) B2021143
theorem B9092897 : Blo 1796099 9092897 := bstep (se 2 (by rfl) ⟨3409836, by rfl⟩ : syracuseStep 9092897 = 6819673) B6819673
theorem B2694971 : Blo 1796099 2694971 := bstep (se 1 (by rfl) ⟨2021228, by rfl⟩ : syracuseStep 2694971 = 4042457) B4042457
theorem B4857661 : Blo 1796099 4857661 := bstep (se 3 (by rfl) ⟨910811, by rfl⟩ : syracuseStep 4857661 = 1821623) B1821623
theorem B2695031 : Blo 1796099 2695031 := bstep (se 1 (by rfl) ⟨2021273, by rfl⟩ : syracuseStep 2695031 = 4042547) B4042547
theorem B4546439 : Blo 1796099 4546439 := bstep (se 1 (by rfl) ⟨3409829, by rfl⟩ : syracuseStep 4546439 = 6819659) B6819659
theorem B4923271 : Blo 1796099 4923271 := bstep (se 1 (by rfl) ⟨3692453, by rfl⟩ : syracuseStep 4923271 = 7384907) B7384907
theorem B2695055 : Blo 1796099 2695055 := bstep (se 1 (by rfl) ⟨2021291, by rfl⟩ : syracuseStep 2695055 = 4042583) B4042583
theorem B10231697 : Blo 1796099 10231697 := bstep (se 2 (by rfl) ⟨3836886, by rfl⟩ : syracuseStep 10231697 = 7673773) B7673773
theorem B5758867 : Blo 1796099 5758867 := bstep (se 1 (by rfl) ⟨4319150, by rfl⟩ : syracuseStep 5758867 = 8638301) B8638301
theorem B20234137 : Blo 1796099 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B4546489 : Blo 1796099 4546489 := bstep (se 2 (by rfl) ⟨1704933, by rfl⟩ : syracuseStep 4546489 = 3409867) B3409867
theorem B2695097 : Blo 1796099 2695097 := bstep (se 2 (by rfl) ⟨1010661, by rfl⟩ : syracuseStep 2695097 = 2021323) B2021323
theorem B4317113 : Blo 1796099 4317113 := bstep (se 2 (by rfl) ⟨1618917, by rfl⟩ : syracuseStep 4317113 = 3237835) B3237835
theorem B6823865 : Blo 1796099 6823865 := bstep (se 2 (by rfl) ⟨2558949, by rfl⟩ : syracuseStep 6823865 = 5117899) B5117899
theorem B13131779 : Blo 1796099 13131779 := bstep (se 1 (by rfl) ⟨9848834, by rfl⟩ : syracuseStep 13131779 = 19697669) B19697669
theorem B2695247 : Blo 1796099 2695247 := bstep (se 1 (by rfl) ⟨2021435, by rfl⟩ : syracuseStep 2695247 = 4042871) B4042871
theorem B2695367 : Blo 1796099 2695367 := bstep (se 1 (by rfl) ⟨2021525, by rfl⟩ : syracuseStep 2695367 = 4043051) B4043051
theorem B12951859 : Blo 1796099 12951859 := bstep (se 1 (by rfl) ⟨9713894, by rfl⟩ : syracuseStep 12951859 = 19427789) B19427789
theorem B5833021 : Blo 1796099 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B16613693 : Blo 1796099 16613693 := bstep (se 3 (by rfl) ⟨3115067, by rfl⟩ : syracuseStep 16613693 = 6230135) B6230135
theorem B3031391 : Blo 1796099 3031391 := bstep (se 1 (by rfl) ⟨2273543, by rfl⟩ : syracuseStep 3031391 = 4547087) B4547087
theorem B2695529 : Blo 1796099 2695529 := bstep (se 2 (by rfl) ⟨1010823, by rfl⟩ : syracuseStep 2695529 = 2021647) B2021647
theorem B15352193 : Blo 1796099 15352193 := bstep (se 2 (by rfl) ⟨5757072, by rfl⟩ : syracuseStep 15352193 = 11514145) B11514145
theorem B6824321 : Blo 1796099 6824321 := bstep (se 2 (by rfl) ⟨2559120, by rfl⟩ : syracuseStep 6824321 = 5118241) B5118241
theorem B7283087 : Blo 1796099 7283087 := bstep (se 1 (by rfl) ⟨5462315, by rfl⟩ : syracuseStep 7283087 = 10924631) B10924631
theorem B2695607 : Blo 1796099 2695607 := bstep (se 1 (by rfl) ⟨2021705, by rfl⟩ : syracuseStep 2695607 = 4043411) B4043411
theorem B2695643 : Blo 1796099 2695643 := bstep (se 1 (by rfl) ⟨2021732, by rfl⟩ : syracuseStep 2695643 = 4043465) B4043465
theorem B6062579 : Blo 1796099 6062579 := bstep (se 1 (by rfl) ⟨4546934, by rfl⟩ : syracuseStep 6062579 = 9093869) B9093869
theorem B5759687 : Blo 1796099 5759687 := bstep (se 1 (by rfl) ⟨4319765, by rfl⟩ : syracuseStep 5759687 = 8639531) B8639531
theorem B3031951 : Blo 1796099 3031951 := bstep (se 1 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 3031951 = 4547927) B4547927
theorem B2696111 : Blo 1796099 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B13648823 : Blo 1796099 13648823 := bstep (se 1 (by rfl) ⟨10236617, by rfl⟩ : syracuseStep 13648823 = 20473235) B20473235
theorem B12297217 : Blo 1796099 12297217 := bstep (se 2 (by rfl) ⟨4611456, by rfl⟩ : syracuseStep 12297217 = 9222913) B9222913
theorem B2696201 : Blo 1796099 2696201 := bstep (se 2 (by rfl) ⟨1011075, by rfl⟩ : syracuseStep 2696201 = 2022151) B2022151
theorem B6063119 : Blo 1796099 6063119 := bstep (se 1 (by rfl) ⟨4547339, by rfl⟩ : syracuseStep 6063119 = 9094679) B9094679
theorem B4547603 : Blo 1796099 4547603 := bstep (se 1 (by rfl) ⟨3410702, by rfl⟩ : syracuseStep 4547603 = 6821405) B6821405
theorem B2696231 : Blo 1796099 2696231 := bstep (se 1 (by rfl) ⟨2022173, by rfl⟩ : syracuseStep 2696231 = 4044347) B4044347
theorem B13837391 : Blo 1796099 13837391 := bstep (se 1 (by rfl) ⟨10378043, by rfl⟩ : syracuseStep 13837391 = 20756087) B20756087
theorem B2696315 : Blo 1796099 2696315 := bstep (se 1 (by rfl) ⟨2022236, by rfl⟩ : syracuseStep 2696315 = 4044473) B4044473
theorem B11519171 : Blo 1796099 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B2696441 : Blo 1796099 2696441 := bstep (se 2 (by rfl) ⟨1011165, by rfl⟩ : syracuseStep 2696441 = 2022331) B2022331
theorem B2696543 : Blo 1796099 2696543 := bstep (se 1 (by rfl) ⟨2022407, by rfl⟩ : syracuseStep 2696543 = 4044815) B4044815
theorem B2696555 : Blo 1796099 2696555 := bstep (se 1 (by rfl) ⟨2022416, by rfl⟩ : syracuseStep 2696555 = 4044833) B4044833
theorem B4548059 : Blo 1796099 4548059 := bstep (se 1 (by rfl) ⟨3411044, by rfl⟩ : syracuseStep 4548059 = 6822089) B6822089
theorem B6825505 : Blo 1796099 6825505 := bstep (se 2 (by rfl) ⟨2559564, by rfl⟩ : syracuseStep 6825505 = 5119129) B5119129
theorem B3032633 : Blo 1796099 3032633 := bstep (se 2 (by rfl) ⟨1137237, by rfl⟩ : syracuseStep 3032633 = 2274475) B2274475
theorem B2696783 : Blo 1796099 2696783 := bstep (se 1 (by rfl) ⟨2022587, by rfl⟩ : syracuseStep 2696783 = 4045175) B4045175
theorem B6063713 : Blo 1796099 6063713 := bstep (se 2 (by rfl) ⟨2273892, by rfl⟩ : syracuseStep 6063713 = 4547785) B4547785
theorem B2696903 : Blo 1796099 2696903 := bstep (se 1 (by rfl) ⟨2022677, by rfl⟩ : syracuseStep 2696903 = 4045355) B4045355
theorem B116844281 : Blo 1796099 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B2697065 : Blo 1796099 2697065 := bstep (se 2 (by rfl) ⟨1011399, by rfl⟩ : syracuseStep 2697065 = 2022799) B2022799
theorem B2697143 : Blo 1796099 2697143 := bstep (se 1 (by rfl) ⟨2022857, by rfl⟩ : syracuseStep 2697143 = 4045715) B4045715
theorem B2877371 : Blo 1796099 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B1918939 : Blo 1796099 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B10233863 : Blo 1796099 10233863 := bstep (se 1 (by rfl) ⟨7675397, by rfl⟩ : syracuseStep 10233863 = 15350795) B15350795
theorem B6825991 : Blo 1796099 6825991 := bstep (se 1 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 6825991 = 10238987) B10238987
theorem B1796135 : Blo 1796099 1796135 := bstep (se 1 (by rfl) ⟨1347101, by rfl⟩ : syracuseStep 1796135 = 2694203) B2694203
theorem B1796175 : Blo 1796099 1796175 := bstep (se 1 (by rfl) ⟨1347131, by rfl⟩ : syracuseStep 1796175 = 2694263) B2694263
theorem B1796191 : Blo 1796099 1796191 := bstep (se 1 (by rfl) ⟨1347143, by rfl⟩ : syracuseStep 1796191 = 2694287) B2694287
theorem B1796219 : Blo 1796099 1796219 := bstep (se 1 (by rfl) ⟨1347164, by rfl⟩ : syracuseStep 1796219 = 2694329) B2694329
theorem B1796271 : Blo 1796099 1796271 := bstep (se 1 (by rfl) ⟨1347203, by rfl⟩ : syracuseStep 1796271 = 2694407) B2694407
theorem B1796295 : Blo 1796099 1796295 := bstep (se 1 (by rfl) ⟨1347221, by rfl⟩ : syracuseStep 1796295 = 2694443) B2694443
theorem B1796315 : Blo 1796099 1796315 := bstep (se 1 (by rfl) ⟨1347236, by rfl⟩ : syracuseStep 1796315 = 2694473) B2694473
theorem B3033335 : Blo 1796099 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B1796391 : Blo 1796099 1796391 := bstep (se 1 (by rfl) ⟨1347293, by rfl⟩ : syracuseStep 1796391 = 2694587) B2694587
theorem B1796431 : Blo 1796099 1796431 := bstep (se 1 (by rfl) ⟨1347323, by rfl⟩ : syracuseStep 1796431 = 2694647) B2694647
theorem B1796447 : Blo 1796099 1796447 := bstep (se 1 (by rfl) ⟨1347335, by rfl⟩ : syracuseStep 1796447 = 2694671) B2694671
theorem B13650281 : Blo 1796099 13650281 := bstep (se 2 (by rfl) ⟨5118855, by rfl⟩ : syracuseStep 13650281 = 10237711) B10237711
theorem B1796475 : Blo 1796099 1796475 := bstep (se 1 (by rfl) ⟨1347356, by rfl⟩ : syracuseStep 1796475 = 2694713) B2694713
theorem B1796527 : Blo 1796099 1796527 := bstep (se 1 (by rfl) ⟨1347395, by rfl⟩ : syracuseStep 1796527 = 2694791) B2694791
theorem B1796551 : Blo 1796099 1796551 := bstep (se 1 (by rfl) ⟨1347413, by rfl⟩ : syracuseStep 1796551 = 2694827) B2694827
theorem B1796571 : Blo 1796099 1796571 := bstep (se 1 (by rfl) ⟨1347428, by rfl⟩ : syracuseStep 1796571 = 2694857) B2694857
theorem B6826477 : Blo 1796099 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B6564361 : Blo 1796099 6564361 := bstep (se 2 (by rfl) ⟨2461635, by rfl⟩ : syracuseStep 6564361 = 4923271) B4923271
theorem B7678489 : Blo 1796099 7678489 := bstep (se 2 (by rfl) ⟨2879433, by rfl⟩ : syracuseStep 7678489 = 5758867) B5758867
theorem B26978849 : Blo 1796099 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1796647 : Blo 1796099 1796647 := bstep (se 1 (by rfl) ⟨1347485, by rfl⟩ : syracuseStep 1796647 = 2694971) B2694971
theorem B9226811 : Blo 1796099 9226811 := bstep (se 1 (by rfl) ⟨6920108, by rfl⟩ : syracuseStep 9226811 = 13840217) B13840217
theorem B1796687 : Blo 1796099 1796687 := bstep (se 1 (by rfl) ⟨1347515, by rfl⟩ : syracuseStep 1796687 = 2695031) B2695031
theorem B3033679 : Blo 1796099 3033679 := bstep (se 1 (by rfl) ⟨2275259, by rfl⟩ : syracuseStep 3033679 = 4550519) B4550519
theorem B1796703 : Blo 1796099 1796703 := bstep (se 1 (by rfl) ⟨1347527, by rfl⟩ : syracuseStep 1796703 = 2695055) B2695055
theorem B1796731 : Blo 1796099 1796731 := bstep (se 1 (by rfl) ⟨1347548, by rfl⟩ : syracuseStep 1796731 = 2695097) B2695097
theorem B2878075 : Blo 1796099 2878075 := bstep (se 1 (by rfl) ⟨2158556, by rfl⟩ : syracuseStep 2878075 = 4317113) B4317113
theorem B4549243 : Blo 1796099 4549243 := bstep (se 1 (by rfl) ⟨3411932, by rfl⟩ : syracuseStep 4549243 = 6823865) B6823865
theorem B1796783 : Blo 1796099 1796783 := bstep (se 1 (by rfl) ⟨1347587, by rfl⟩ : syracuseStep 1796783 = 2695175) B2695175
theorem B7383737 : Blo 1796099 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B11512505 : Blo 1796099 11512505 := bstep (se 2 (by rfl) ⟨4317189, by rfl⟩ : syracuseStep 11512505 = 8634379) B8634379
theorem B1796807 : Blo 1796099 1796807 := bstep (se 1 (by rfl) ⟨1347605, by rfl⟩ : syracuseStep 1796807 = 2695211) B2695211
theorem B1796827 : Blo 1796099 1796827 := bstep (se 1 (by rfl) ⟨1347620, by rfl⟩ : syracuseStep 1796827 = 2695241) B2695241
theorem B6826781 : Blo 1796099 6826781 := bstep (se 3 (by rfl) ⟨1280021, by rfl⟩ : syracuseStep 6826781 = 2560043) B2560043
theorem B1796903 : Blo 1796099 1796903 := bstep (se 1 (by rfl) ⟨1347677, by rfl⟩ : syracuseStep 1796903 = 2695355) B2695355
theorem B3033929 : Blo 1796099 3033929 := bstep (se 2 (by rfl) ⟨1137723, by rfl⟩ : syracuseStep 3033929 = 2275447) B2275447
theorem B1796943 : Blo 1796099 1796943 := bstep (se 1 (by rfl) ⟨1347707, by rfl⟩ : syracuseStep 1796943 = 2695415) B2695415
theorem B1796959 : Blo 1796099 1796959 := bstep (se 1 (by rfl) ⟨1347719, by rfl⟩ : syracuseStep 1796959 = 2695439) B2695439
theorem B3238751 : Blo 1796099 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B1796987 : Blo 1796099 1796987 := bstep (se 1 (by rfl) ⟨1347740, by rfl⟩ : syracuseStep 1796987 = 2695481) B2695481
theorem B4041647 : Blo 1796099 4041647 := bstep (se 1 (by rfl) ⟨3031235, by rfl⟩ : syracuseStep 4041647 = 6062471) B6062471
theorem B1797039 : Blo 1796099 1797039 := bstep (se 1 (by rfl) ⟨1347779, by rfl⟩ : syracuseStep 1797039 = 2695559) B2695559
theorem B1797063 : Blo 1796099 1797063 := bstep (se 1 (by rfl) ⟨1347797, by rfl⟩ : syracuseStep 1797063 = 2695595) B2695595
theorem B1797083 : Blo 1796099 1797083 := bstep (se 1 (by rfl) ⟨1347812, by rfl⟩ : syracuseStep 1797083 = 2695625) B2695625
theorem B9219091 : Blo 1796099 9219091 := bstep (se 1 (by rfl) ⟨6914318, by rfl⟩ : syracuseStep 9219091 = 13828637) B13828637
theorem B6065171 : Blo 1796099 6065171 := bstep (se 1 (by rfl) ⟨4548878, by rfl⟩ : syracuseStep 6065171 = 9097757) B9097757
theorem B1797159 : Blo 1796099 1797159 := bstep (se 1 (by rfl) ⟨1347869, by rfl⟩ : syracuseStep 1797159 = 2695739) B2695739
theorem B1797199 : Blo 1796099 1797199 := bstep (se 1 (by rfl) ⟨1347899, by rfl⟩ : syracuseStep 1797199 = 2695799) B2695799
theorem B1797215 : Blo 1796099 1797215 := bstep (se 1 (by rfl) ⟨1347911, by rfl⟩ : syracuseStep 1797215 = 2695823) B2695823
theorem B3411067 : Blo 1796099 3411067 := bstep (se 1 (by rfl) ⟨2558300, by rfl⟩ : syracuseStep 3411067 = 5116601) B5116601
theorem B1797243 : Blo 1796099 1797243 := bstep (se 1 (by rfl) ⟨1347932, by rfl⟩ : syracuseStep 1797243 = 2695865) B2695865
theorem B4041899 : Blo 1796099 4041899 := bstep (se 1 (by rfl) ⟨3031424, by rfl⟩ : syracuseStep 4041899 = 6062849) B6062849
theorem B6474923 : Blo 1796099 6474923 := bstep (se 1 (by rfl) ⟨4856192, by rfl⟩ : syracuseStep 6474923 = 9712385) B9712385
theorem B1797295 : Blo 1796099 1797295 := bstep (se 1 (by rfl) ⟨1347971, by rfl⟩ : syracuseStep 1797295 = 2695943) B2695943
theorem B3411143 : Blo 1796099 3411143 := bstep (se 1 (by rfl) ⟨2558357, by rfl⟩ : syracuseStep 3411143 = 5116715) B5116715
theorem B1797319 : Blo 1796099 1797319 := bstep (se 1 (by rfl) ⟨1347989, by rfl⟩ : syracuseStep 1797319 = 2695979) B2695979
theorem B1821895 : Blo 1796099 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B1797339 : Blo 1796099 1797339 := bstep (se 1 (by rfl) ⟨1348004, by rfl⟩ : syracuseStep 1797339 = 2696009) B2696009
theorem B1797415 : Blo 1796099 1797415 := bstep (se 1 (by rfl) ⟨1348061, by rfl⟩ : syracuseStep 1797415 = 2696123) B2696123
theorem B1797455 : Blo 1796099 1797455 := bstep (se 1 (by rfl) ⟨1348091, by rfl⟩ : syracuseStep 1797455 = 2696183) B2696183
theorem B6065495 : Blo 1796099 6065495 := bstep (se 1 (by rfl) ⟨4549121, by rfl⟩ : syracuseStep 6065495 = 9098243) B9098243
theorem B1797471 : Blo 1796099 1797471 := bstep (se 1 (by rfl) ⟨1348103, by rfl⟩ : syracuseStep 1797471 = 2696207) B2696207
theorem B3837289 : Blo 1796099 3837289 := bstep (se 2 (by rfl) ⟨1438983, by rfl⟩ : syracuseStep 3837289 = 2877967) B2877967
theorem B1797499 : Blo 1796099 1797499 := bstep (se 1 (by rfl) ⟨1348124, by rfl⟩ : syracuseStep 1797499 = 2696249) B2696249
theorem B15347069 : Blo 1796099 15347069 := bstep (se 3 (by rfl) ⟨2877575, by rfl⟩ : syracuseStep 15347069 = 5755151) B5755151
theorem B1797551 : Blo 1796099 1797551 := bstep (se 1 (by rfl) ⟨1348163, by rfl⟩ : syracuseStep 1797551 = 2696327) B2696327
theorem B1797575 : Blo 1796099 1797575 := bstep (se 1 (by rfl) ⟨1348181, by rfl⟩ : syracuseStep 1797575 = 2696363) B2696363
theorem B5754331 : Blo 1796099 5754331 := bstep (se 1 (by rfl) ⟨4315748, by rfl⟩ : syracuseStep 5754331 = 8631497) B8631497
theorem B2559451 : Blo 1796099 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B1797595 : Blo 1796099 1797595 := bstep (se 1 (by rfl) ⟨1348196, by rfl⟩ : syracuseStep 1797595 = 2696393) B2696393
theorem B13831667 : Blo 1796099 13831667 := bstep (se 1 (by rfl) ⟨10373750, by rfl⟩ : syracuseStep 13831667 = 20747501) B20747501
theorem B2731529 : Blo 1796099 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B3239443 : Blo 1796099 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B5754407 : Blo 1796099 5754407 := bstep (se 1 (by rfl) ⟨4315805, by rfl⟩ : syracuseStep 5754407 = 8631611) B8631611
theorem B1797671 : Blo 1796099 1797671 := bstep (se 1 (by rfl) ⟨1348253, by rfl⟩ : syracuseStep 1797671 = 2696507) B2696507
theorem B1797711 : Blo 1796099 1797711 := bstep (se 1 (by rfl) ⟨1348283, by rfl⟩ : syracuseStep 1797711 = 2696567) B2696567
theorem B1797727 : Blo 1796099 1797727 := bstep (se 1 (by rfl) ⟨1348295, by rfl⟩ : syracuseStep 1797727 = 2696591) B2696591
theorem B3411553 : Blo 1796099 3411553 := bstep (se 2 (by rfl) ⟨1279332, by rfl⟩ : syracuseStep 3411553 = 2558665) B2558665
theorem B1797755 : Blo 1796099 1797755 := bstep (se 1 (by rfl) ⟨1348316, by rfl⟩ : syracuseStep 1797755 = 2696633) B2696633
theorem B1797807 : Blo 1796099 1797807 := bstep (se 1 (by rfl) ⟨1348355, by rfl⟩ : syracuseStep 1797807 = 2696711) B2696711
theorem B116641457 : Blo 1796099 116641457 := bstep (se 2 (by rfl) ⟨43740546, by rfl⟩ : syracuseStep 116641457 = 87481093) B87481093
theorem B5467837 : Blo 1796099 5467837 := bstep (se 3 (by rfl) ⟨1025219, by rfl⟩ : syracuseStep 5467837 = 2050439) B2050439
theorem B4042439 : Blo 1796099 4042439 := bstep (se 1 (by rfl) ⟨3031829, by rfl⟩ : syracuseStep 4042439 = 6063659) B6063659
theorem B1797831 : Blo 1796099 1797831 := bstep (se 1 (by rfl) ⟨1348373, by rfl⟩ : syracuseStep 1797831 = 2696747) B2696747
theorem B1797851 : Blo 1796099 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B1797927 : Blo 1796099 1797927 := bstep (se 1 (by rfl) ⟨1348445, by rfl⟩ : syracuseStep 1797927 = 2696891) B2696891
theorem B1797967 : Blo 1796099 1797967 := bstep (se 1 (by rfl) ⟨1348475, by rfl⟩ : syracuseStep 1797967 = 2696951) B2696951
theorem B1797983 : Blo 1796099 1797983 := bstep (se 1 (by rfl) ⟨1348487, by rfl⟩ : syracuseStep 1797983 = 2696975) B2696975
theorem B1798011 : Blo 1796099 1798011 := bstep (se 1 (by rfl) ⟨1348508, by rfl⟩ : syracuseStep 1798011 = 2697017) B2697017
theorem B11513735 : Blo 1796099 11513735 := bstep (se 1 (by rfl) ⟨8635301, by rfl⟩ : syracuseStep 11513735 = 17270603) B17270603
theorem B1798063 : Blo 1796099 1798063 := bstep (se 1 (by rfl) ⟨1348547, by rfl⟩ : syracuseStep 1798063 = 2697095) B2697095
theorem B3411895 : Blo 1796099 3411895 := bstep (se 1 (by rfl) ⟨2558921, by rfl⟩ : syracuseStep 3411895 = 5117843) B5117843
theorem B1798087 : Blo 1796099 1798087 := bstep (se 1 (by rfl) ⟨1348565, by rfl⟩ : syracuseStep 1798087 = 2697131) B2697131
theorem B2560123 : Blo 1796099 2560123 := bstep (se 1 (by rfl) ⟨1920092, by rfl⟩ : syracuseStep 2560123 = 3840185) B3840185
theorem B13652225 : Blo 1796099 13652225 := bstep (se 2 (by rfl) ⟨5119584, by rfl⟩ : syracuseStep 13652225 = 10239169) B10239169
theorem B3412297 : Blo 1796099 3412297 := bstep (se 2 (by rfl) ⟨1279611, by rfl⟩ : syracuseStep 3412297 = 2559223) B2559223
theorem B6066575 : Blo 1796099 6066575 := bstep (se 1 (by rfl) ⟨4549931, by rfl⟩ : syracuseStep 6066575 = 9099863) B9099863
theorem B12956183 : Blo 1796099 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B5116441 : Blo 1796099 5116441 := bstep (se 2 (by rfl) ⟨1918665, by rfl⟩ : syracuseStep 5116441 = 3837331) B3837331
theorem B4043303 : Blo 1796099 4043303 := bstep (se 1 (by rfl) ⟨3032477, by rfl⟩ : syracuseStep 4043303 = 6064955) B6064955
theorem B46707299 : Blo 1796099 46707299 := bstep (se 1 (by rfl) ⟨35030474, by rfl⟩ : syracuseStep 46707299 = 70060949) B70060949
theorem B6066899 : Blo 1796099 6066899 := bstep (se 1 (by rfl) ⟨4550174, by rfl⟩ : syracuseStep 6066899 = 9100349) B9100349
theorem B10932947 : Blo 1796099 10932947 := bstep (se 1 (by rfl) ⟨8199710, by rfl⟩ : syracuseStep 10932947 = 16399421) B16399421
theorem B4043627 : Blo 1796099 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B10236779 : Blo 1796099 10236779 := bstep (se 1 (by rfl) ⟨7677584, by rfl⟩ : syracuseStep 10236779 = 15355169) B15355169
theorem B4043681 : Blo 1796099 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B6230971 : Blo 1796099 6230971 := bstep (se 1 (by rfl) ⟨4673228, by rfl⟩ : syracuseStep 6230971 = 9346457) B9346457
theorem B3413011 : Blo 1796099 3413011 := bstep (se 1 (by rfl) ⟨2559758, by rfl⟩ : syracuseStep 3413011 = 5119517) B5119517
theorem B6476881 : Blo 1796099 6476881 := bstep (se 2 (by rfl) ⟨2428830, by rfl⟩ : syracuseStep 6476881 = 4857661) B4857661
theorem B21034201 : Blo 1796099 21034201 := bstep (se 2 (by rfl) ⟨7887825, by rfl⟩ : syracuseStep 21034201 = 15775651) B15775651
theorem B4044023 : Blo 1796099 4044023 := bstep (se 1 (by rfl) ⟨3033017, by rfl⟩ : syracuseStep 4044023 = 6066035) B6066035
theorem B6821131 : Blo 1796099 6821131 := bstep (se 1 (by rfl) ⟨5115848, by rfl⟩ : syracuseStep 6821131 = 10231697) B10231697
theorem B3413353 : Blo 1796099 3413353 := bstep (se 2 (by rfl) ⟨1280007, by rfl⟩ : syracuseStep 3413353 = 2560015) B2560015
theorem B2020783 : Blo 1796099 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B2274743 : Blo 1796099 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B3642889 : Blo 1796099 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B6821435 : Blo 1796099 6821435 := bstep (se 1 (by rfl) ⟨5116076, by rfl⟩ : syracuseStep 6821435 = 10232153) B10232153
theorem B2274895 : Blo 1796099 2274895 := bstep (se 1 (by rfl) ⟨1706171, by rfl⟩ : syracuseStep 2274895 = 3412343) B3412343
theorem B9098891 : Blo 1796099 9098891 := bstep (se 1 (by rfl) ⟨6824168, by rfl⟩ : syracuseStep 9098891 = 13648337) B13648337
theorem B73791157 : Blo 1796099 73791157 := bstep (se 5 (by rfl) ⟨3458960, by rfl⟩ : syracuseStep 73791157 = 6917921) B6917921
theorem B29554391 : Blo 1796099 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B4044617 : Blo 1796099 4044617 := bstep (se 2 (by rfl) ⟨1516731, by rfl⟩ : syracuseStep 4044617 = 3033463) B3033463
theorem B2021215 : Blo 1796099 2021215 := bstep (se 1 (by rfl) ⟨1515911, by rfl⟩ : syracuseStep 2021215 = 3031823) B3031823
theorem B6068087 : Blo 1796099 6068087 := bstep (se 1 (by rfl) ⟨4551065, by rfl⟩ : syracuseStep 6068087 = 9102131) B9102131
theorem B94599121 : Blo 1796099 94599121 := bstep (se 2 (by rfl) ⟨35474670, by rfl⟩ : syracuseStep 94599121 = 70949341) B70949341
theorem B20461571 : Blo 1796099 20461571 := bstep (se 1 (by rfl) ⟨15346178, by rfl⟩ : syracuseStep 20461571 = 30692357) B30692357
theorem B6068303 : Blo 1796099 6068303 := bstep (se 1 (by rfl) ⟨4551227, by rfl⟩ : syracuseStep 6068303 = 9102455) B9102455
theorem B3643489 : Blo 1796099 3643489 := bstep (se 2 (by rfl) ⟨1366308, by rfl⟩ : syracuseStep 3643489 = 2732617) B2732617
theorem B2021575 : Blo 1796099 2021575 := bstep (se 1 (by rfl) ⟨1516181, by rfl⟩ : syracuseStep 2021575 = 3032363) B3032363
theorem B4315673 : Blo 1796099 4315673 := bstep (se 2 (by rfl) ⟨1618377, by rfl⟩ : syracuseStep 4315673 = 3236755) B3236755
theorem B58317347 : Blo 1796099 58317347 := bstep (se 1 (by rfl) ⟨43738010, by rfl⟩ : syracuseStep 58317347 = 87476021) B87476021
theorem B4045409 : Blo 1796099 4045409 := bstep (se 2 (by rfl) ⟨1517028, by rfl⟩ : syracuseStep 4045409 = 3034057) B3034057
theorem B6822589 : Blo 1796099 6822589 := bstep (se 3 (by rfl) ⟨1279235, by rfl⟩ : syracuseStep 6822589 = 2558471) B2558471
theorem B5462777 : Blo 1796099 5462777 := bstep (se 2 (by rfl) ⟨2048541, by rfl⟩ : syracuseStep 5462777 = 4097083) B4097083
theorem B4315999 : Blo 1796099 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B11508587 : Blo 1796099 11508587 := bstep (se 1 (by rfl) ⟨8631440, by rfl⟩ : syracuseStep 11508587 = 17262881) B17262881
theorem B13827037 : Blo 1796099 13827037 := bstep (se 3 (by rfl) ⟨2592569, by rfl⟩ : syracuseStep 13827037 = 5185139) B5185139
theorem B2022439 : Blo 1796099 2022439 := bstep (se 1 (by rfl) ⟨1516829, by rfl⟩ : syracuseStep 2022439 = 3033659) B3033659
theorem B31112365 : Blo 1796099 31112365 := bstep (se 3 (by rfl) ⟨5833568, by rfl⟩ : syracuseStep 31112365 = 11667137) B11667137
theorem B20749603 : Blo 1796099 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B11517221 : Blo 1796099 11517221 := bstep (se 4 (by rfl) ⟨1079739, by rfl⟩ : syracuseStep 11517221 = 2159479) B2159479
theorem B5119357 : Blo 1796099 5119357 := bstep (se 3 (by rfl) ⟨959879, by rfl⟩ : syracuseStep 5119357 = 1919759) B1919759
theorem B2694575 : Blo 1796099 2694575 := bstep (se 1 (by rfl) ⟨2020931, by rfl⟩ : syracuseStep 2694575 = 4041863) B4041863
theorem B23027165 : Blo 1796099 23027165 := bstep (se 3 (by rfl) ⟨4317593, by rfl⟩ : syracuseStep 23027165 = 8635187) B8635187
theorem B6479347 : Blo 1796099 6479347 := bstep (se 1 (by rfl) ⟨4859510, by rfl⟩ : syracuseStep 6479347 = 9719021) B9719021
theorem B2694665 : Blo 1796099 2694665 := bstep (se 2 (by rfl) ⟨1010499, by rfl⟩ : syracuseStep 2694665 = 2020999) B2020999
theorem B2694695 : Blo 1796099 2694695 := bstep (se 1 (by rfl) ⟨2021021, by rfl⟩ : syracuseStep 2694695 = 4042043) B4042043
theorem B2694779 : Blo 1796099 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B6823547 : Blo 1796099 6823547 := bstep (se 1 (by rfl) ⟨5117660, by rfl⟩ : syracuseStep 6823547 = 10235321) B10235321
theorem B5119699 : Blo 1796099 5119699 := bstep (se 1 (by rfl) ⟨3839774, by rfl⟩ : syracuseStep 5119699 = 7679549) B7679549
theorem B8634071 : Blo 1796099 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B2694905 : Blo 1796099 2694905 := bstep (se 2 (by rfl) ⟨1010589, by rfl⟩ : syracuseStep 2694905 = 2021179) B2021179
theorem B14573371 : Blo 1796099 14573371 := bstep (se 1 (by rfl) ⟨10930028, by rfl⟩ : syracuseStep 14573371 = 21860057) B21860057
theorem B2695007 : Blo 1796099 2695007 := bstep (se 1 (by rfl) ⟨2021255, by rfl⟩ : syracuseStep 2695007 = 4042511) B4042511
theorem B6061931 : Blo 1796099 6061931 := bstep (se 1 (by rfl) ⟨4546448, by rfl⟩ : syracuseStep 6061931 = 9092897) B9092897
theorem B2695019 : Blo 1796099 2695019 := bstep (se 1 (by rfl) ⟨2021264, by rfl⟩ : syracuseStep 2695019 = 4042529) B4042529
theorem B11509613 : Blo 1796099 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B6061985 : Blo 1796099 6061985 := bstep (se 2 (by rfl) ⟨2273244, by rfl⟩ : syracuseStep 6061985 = 4546489) B4546489
theorem B3030959 : Blo 1796099 3030959 := bstep (se 1 (by rfl) ⟨2273219, by rfl⟩ : syracuseStep 3030959 = 4546439) B4546439
theorem B14565329 : Blo 1796099 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B9101321 : Blo 1796099 9101321 := bstep (se 2 (by rfl) ⟨3412995, by rfl⟩ : syracuseStep 9101321 = 6825991) B6825991
theorem B4857985 : Blo 1796099 4857985 := bstep (se 2 (by rfl) ⟨1821744, by rfl⟩ : syracuseStep 4857985 = 3643489) B3643489
theorem B9101483 : Blo 1796099 9101483 := bstep (se 1 (by rfl) ⟨6826112, by rfl⟩ : syracuseStep 9101483 = 13652225) B13652225
theorem B11075795 : Blo 1796099 11075795 := bstep (se 1 (by rfl) ⟨8306846, by rfl⟩ : syracuseStep 11075795 = 16613693) B16613693
theorem B2695433 : Blo 1796099 2695433 := bstep (se 2 (by rfl) ⟨1010787, by rfl⟩ : syracuseStep 2695433 = 2021575) B2021575
theorem B2695535 : Blo 1796099 2695535 := bstep (se 1 (by rfl) ⟨2021651, by rfl⟩ : syracuseStep 2695535 = 4043303) B4043303
theorem B31138199 : Blo 1796099 31138199 := bstep (se 1 (by rfl) ⟨23353649, by rfl⟩ : syracuseStep 31138199 = 46707299) B46707299
theorem B17269145 : Blo 1796099 17269145 := bstep (se 2 (by rfl) ⟨6475929, by rfl⟩ : syracuseStep 17269145 = 12951859) B12951859
theorem B2695751 : Blo 1796099 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B6824519 : Blo 1796099 6824519 := bstep (se 1 (by rfl) ⟨5118389, by rfl⟩ : syracuseStep 6824519 = 10236779) B10236779
theorem B2695787 : Blo 1796099 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B9101969 : Blo 1796099 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B3031735 : Blo 1796099 3031735 := bstep (se 1 (by rfl) ⟨2273801, by rfl⟩ : syracuseStep 3031735 = 4547603) B4547603
theorem B9224927 : Blo 1796099 9224927 := bstep (se 1 (by rfl) ⟨6918695, by rfl⟩ : syracuseStep 9224927 = 13837391) B13837391
theorem B2696015 : Blo 1796099 2696015 := bstep (se 1 (by rfl) ⟨2022011, by rfl⟩ : syracuseStep 2696015 = 4044023) B4044023
theorem B3032039 : Blo 1796099 3032039 := bstep (se 1 (by rfl) ⟨2274029, by rfl⟩ : syracuseStep 3032039 = 4548059) B4548059
theorem B9716773 : Blo 1796099 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B4547623 : Blo 1796099 4547623 := bstep (se 1 (by rfl) ⟨3410717, by rfl⟩ : syracuseStep 4547623 = 6821435) B6821435
theorem B19702927 : Blo 1796099 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B2696411 : Blo 1796099 2696411 := bstep (se 1 (by rfl) ⟨2022308, by rfl⟩ : syracuseStep 2696411 = 4044617) B4044617
theorem B1918247 : Blo 1796099 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B13641047 : Blo 1796099 13641047 := bstep (se 1 (by rfl) ⟨10230785, by rfl⟩ : syracuseStep 13641047 = 20461571) B20461571
theorem B7284077 : Blo 1796099 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B2696585 : Blo 1796099 2696585 := bstep (se 2 (by rfl) ⟨1011219, by rfl⟩ : syracuseStep 2696585 = 2022439) B2022439
theorem B15345085 : Blo 1796099 15345085 := bstep (se 3 (by rfl) ⟨2877203, by rfl⟩ : syracuseStep 15345085 = 5754407) B5754407
theorem B8635841 : Blo 1796099 8635841 := bstep (se 2 (by rfl) ⟨3238440, by rfl⟩ : syracuseStep 8635841 = 6476881) B6476881
theorem B4548089 : Blo 1796099 4548089 := bstep (se 2 (by rfl) ⟨1705533, by rfl⟩ : syracuseStep 4548089 = 3411067) B3411067
theorem B9094841 : Blo 1796099 9094841 := bstep (se 2 (by rfl) ⟨3410565, by rfl⟩ : syracuseStep 9094841 = 6821131) B6821131
theorem B2877115 : Blo 1796099 2877115 := bstep (se 1 (by rfl) ⟨2157836, by rfl⟩ : syracuseStep 2877115 = 4315673) B4315673
theorem B27666137 : Blo 1796099 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B2696939 : Blo 1796099 2696939 := bstep (se 1 (by rfl) ⟨2022704, by rfl⟩ : syracuseStep 2696939 = 4045409) B4045409
theorem B6825809 : Blo 1796099 6825809 := bstep (se 2 (by rfl) ⟨2559678, by rfl⟩ : syracuseStep 6825809 = 5119357) B5119357
theorem B4319257 : Blo 1796099 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B3033193 : Blo 1796099 3033193 := bstep (se 2 (by rfl) ⟨1137447, by rfl⟩ : syracuseStep 3033193 = 2274895) B2274895
theorem B4548737 : Blo 1796099 4548737 := bstep (se 2 (by rfl) ⟨1705776, by rfl⟩ : syracuseStep 4548737 = 3411553) B3411553
theorem B7678147 : Blo 1796099 7678147 := bstep (se 1 (by rfl) ⟨5758610, by rfl⟩ : syracuseStep 7678147 = 11517221) B11517221
theorem B98388209 : Blo 1796099 98388209 := bstep (se 2 (by rfl) ⟨36895578, by rfl⟩ : syracuseStep 98388209 = 73791157) B73791157
theorem B8636669 : Blo 1796099 8636669 := bstep (se 3 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 8636669 = 3238751) B3238751
theorem B6826265 : Blo 1796099 6826265 := bstep (se 2 (by rfl) ⟨2559849, by rfl⟩ : syracuseStep 6826265 = 5119699) B5119699
theorem B1796383 : Blo 1796099 1796383 := bstep (se 1 (by rfl) ⟨1347287, by rfl⟩ : syracuseStep 1796383 = 2694575) B2694575
theorem B1796443 : Blo 1796099 1796443 := bstep (se 1 (by rfl) ⟨1347332, by rfl⟩ : syracuseStep 1796443 = 2694665) B2694665
theorem B1796463 : Blo 1796099 1796463 := bstep (se 1 (by rfl) ⟨1347347, by rfl⟩ : syracuseStep 1796463 = 2694695) B2694695
theorem B1796519 : Blo 1796099 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B4549031 : Blo 1796099 4549031 := bstep (se 1 (by rfl) ⟨3411773, by rfl⟩ : syracuseStep 4549031 = 6823547) B6823547
theorem B77760971 : Blo 1796099 77760971 := bstep (se 1 (by rfl) ⟨58320728, by rfl⟩ : syracuseStep 77760971 = 116641457) B116641457
theorem B1796603 : Blo 1796099 1796603 := bstep (se 1 (by rfl) ⟨1347452, by rfl⟩ : syracuseStep 1796603 = 2694905) B2694905
theorem B1796671 : Blo 1796099 1796671 := bstep (se 1 (by rfl) ⟨1347503, by rfl⟩ : syracuseStep 1796671 = 2695007) B2695007
theorem B4041287 : Blo 1796099 4041287 := bstep (se 1 (by rfl) ⟨3030965, by rfl⟩ : syracuseStep 4041287 = 6061931) B6061931
theorem B1796679 : Blo 1796099 1796679 := bstep (se 1 (by rfl) ⟨1347509, by rfl⟩ : syracuseStep 1796679 = 2695019) B2695019
theorem B4549193 : Blo 1796099 4549193 := bstep (se 2 (by rfl) ⟨1705947, by rfl⟩ : syracuseStep 4549193 = 3411895) B3411895
theorem B4041323 : Blo 1796099 4041323 := bstep (se 1 (by rfl) ⟨3030992, by rfl⟩ : syracuseStep 4041323 = 6061985) B6061985
theorem B2558585 : Blo 1796099 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B9710219 : Blo 1796099 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B1796831 : Blo 1796099 1796831 := bstep (se 1 (by rfl) ⟨1347623, by rfl⟩ : syracuseStep 1796831 = 2695247) B2695247
theorem B1796911 : Blo 1796099 1796911 := bstep (se 1 (by rfl) ⟨1347683, by rfl⟩ : syracuseStep 1796911 = 2695367) B2695367
theorem B1797019 : Blo 1796099 1797019 := bstep (se 1 (by rfl) ⟨1347764, by rfl⟩ : syracuseStep 1797019 = 2695529) B2695529
theorem B10234795 : Blo 1796099 10234795 := bstep (se 1 (by rfl) ⟨7676096, by rfl⟩ : syracuseStep 10234795 = 15352193) B15352193
theorem B4549547 : Blo 1796099 4549547 := bstep (se 1 (by rfl) ⟨3412160, by rfl⟩ : syracuseStep 4549547 = 6824321) B6824321
theorem B1797071 : Blo 1796099 1797071 := bstep (se 1 (by rfl) ⟨1347803, by rfl⟩ : syracuseStep 1797071 = 2695607) B2695607
theorem B1797095 : Blo 1796099 1797095 := bstep (se 1 (by rfl) ⟨1347821, by rfl⟩ : syracuseStep 1797095 = 2695643) B2695643
theorem B4041719 : Blo 1796099 4041719 := bstep (se 1 (by rfl) ⟨3031289, by rfl⟩ : syracuseStep 4041719 = 6062579) B6062579
theorem B8637455 : Blo 1796099 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B7777361 : Blo 1796099 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B4549729 : Blo 1796099 4549729 := bstep (se 2 (by rfl) ⟨1706148, by rfl⟩ : syracuseStep 4549729 = 3412297) B3412297
theorem B1797407 : Blo 1796099 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B1797467 : Blo 1796099 1797467 := bstep (se 1 (by rfl) ⟨1348100, by rfl⟩ : syracuseStep 1797467 = 2696201) B2696201
theorem B4042079 : Blo 1796099 4042079 := bstep (se 1 (by rfl) ⟨3031559, by rfl⟩ : syracuseStep 4042079 = 6063119) B6063119
theorem B8752481 : Blo 1796099 8752481 := bstep (se 2 (by rfl) ⟨3282180, by rfl⟩ : syracuseStep 8752481 = 6564361) B6564361
theorem B1797487 : Blo 1796099 1797487 := bstep (se 1 (by rfl) ⟨1348115, by rfl⟩ : syracuseStep 1797487 = 2696231) B2696231
theorem B1797543 : Blo 1796099 1797543 := bstep (se 1 (by rfl) ⟨1348157, by rfl⟩ : syracuseStep 1797543 = 2696315) B2696315
theorem B7679447 : Blo 1796099 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B6065657 : Blo 1796099 6065657 := bstep (se 2 (by rfl) ⟨2274621, by rfl⟩ : syracuseStep 6065657 = 4549243) B4549243
theorem B1797627 : Blo 1796099 1797627 := bstep (se 1 (by rfl) ⟨1348220, by rfl⟩ : syracuseStep 1797627 = 2696441) B2696441
theorem B1797695 : Blo 1796099 1797695 := bstep (se 1 (by rfl) ⟨1348271, by rfl⟩ : syracuseStep 1797695 = 2696543) B2696543
theorem B1797703 : Blo 1796099 1797703 := bstep (se 1 (by rfl) ⟨1348277, by rfl⟩ : syracuseStep 1797703 = 2696555) B2696555
theorem B9096785 : Blo 1796099 9096785 := bstep (se 2 (by rfl) ⟨3411294, by rfl⟩ : syracuseStep 9096785 = 6822589) B6822589
theorem B1797855 : Blo 1796099 1797855 := bstep (se 1 (by rfl) ⟨1348391, by rfl⟩ : syracuseStep 1797855 = 2696783) B2696783
theorem B4042475 : Blo 1796099 4042475 := bstep (se 1 (by rfl) ⟨3031856, by rfl⟩ : syracuseStep 4042475 = 6063713) B6063713
theorem B6065927 : Blo 1796099 6065927 := bstep (se 1 (by rfl) ⟨4549445, by rfl⟩ : syracuseStep 6065927 = 9098891) B9098891
theorem B5754665 : Blo 1796099 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B1797935 : Blo 1796099 1797935 := bstep (se 1 (by rfl) ⟨1348451, by rfl⟩ : syracuseStep 1797935 = 2696903) B2696903
theorem B6065981 : Blo 1796099 6065981 := bstep (se 3 (by rfl) ⟨1137371, by rfl⟩ : syracuseStep 6065981 = 2274743) B2274743
theorem B4042601 : Blo 1796099 4042601 := bstep (se 2 (by rfl) ⟨1515975, by rfl⟩ : syracuseStep 4042601 = 3031951) B3031951
theorem B1798043 : Blo 1796099 1798043 := bstep (se 1 (by rfl) ⟨1348532, by rfl⟩ : syracuseStep 1798043 = 2697065) B2697065
theorem B1798095 : Blo 1796099 1798095 := bstep (se 1 (by rfl) ⟨1348571, by rfl⟩ : syracuseStep 1798095 = 2697143) B2697143
theorem B18436049 : Blo 1796099 18436049 := bstep (se 2 (by rfl) ⟨6913518, by rfl⟩ : syracuseStep 18436049 = 13827037) B13827037
theorem B16396289 : Blo 1796099 16396289 := bstep (se 2 (by rfl) ⟨6148608, by rfl⟩ : syracuseStep 16396289 = 12297217) B12297217
theorem B12292121 : Blo 1796099 12292121 := bstep (se 2 (by rfl) ⟨4609545, by rfl⟩ : syracuseStep 12292121 = 9219091) B9219091
theorem B4550681 : Blo 1796099 4550681 := bstep (se 2 (by rfl) ⟨1706505, by rfl⟩ : syracuseStep 4550681 = 3413011) B3413011
theorem B24604829 : Blo 1796099 24604829 := bstep (se 3 (by rfl) ⟨4613405, by rfl⟩ : syracuseStep 24604829 = 9226811) B9226811
theorem B28045601 : Blo 1796099 28045601 := bstep (se 2 (by rfl) ⟨10517100, by rfl⟩ : syracuseStep 28045601 = 21034201) B21034201
theorem B17985899 : Blo 1796099 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B5116385 : Blo 1796099 5116385 := bstep (se 2 (by rfl) ⟨1918644, by rfl⟩ : syracuseStep 5116385 = 3837289) B3837289
theorem B4551137 : Blo 1796099 4551137 := bstep (se 2 (by rfl) ⟨1706676, by rfl⟩ : syracuseStep 4551137 = 3413353) B3413353
theorem B3641851 : Blo 1796099 3641851 := bstep (se 1 (by rfl) ⟨2731388, by rfl⟩ : syracuseStep 3641851 = 5462777) B5462777
theorem B4551187 : Blo 1796099 4551187 := bstep (se 1 (by rfl) ⟨3413390, by rfl⟩ : syracuseStep 4551187 = 6826781) B6826781
theorem B23024189 : Blo 1796099 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B7672391 : Blo 1796099 7672391 := bstep (se 1 (by rfl) ⟨5754293, by rfl⟩ : syracuseStep 7672391 = 11508587) B11508587
theorem B7672441 : Blo 1796099 7672441 := bstep (se 2 (by rfl) ⟨2877165, by rfl⟩ : syracuseStep 7672441 = 5754331) B5754331
theorem B3412601 : Blo 1796099 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B8639129 : Blo 1796099 8639129 := bstep (se 2 (by rfl) ⟨3239673, by rfl⟩ : syracuseStep 8639129 = 6479347) B6479347
theorem B4043447 : Blo 1796099 4043447 := bstep (se 1 (by rfl) ⟨3032585, by rfl⟩ : syracuseStep 4043447 = 6065171) B6065171
theorem B2274095 : Blo 1796099 2274095 := bstep (se 1 (by rfl) ⟨1705571, by rfl⟩ : syracuseStep 2274095 = 3411143) B3411143
theorem B4043663 : Blo 1796099 4043663 := bstep (se 1 (by rfl) ⟨3032747, by rfl⟩ : syracuseStep 4043663 = 6065495) B6065495
theorem B33231845 : Blo 1796099 33231845 := bstep (se 4 (by rfl) ⟨3115485, by rfl⟩ : syracuseStep 33231845 = 6230971) B6230971
theorem B9221111 : Blo 1796099 9221111 := bstep (se 1 (by rfl) ⟨6915833, by rfl⟩ : syracuseStep 9221111 = 13831667) B13831667
theorem B7673075 : Blo 1796099 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B2020639 : Blo 1796099 2020639 := bstep (se 1 (by rfl) ⟨1515479, by rfl⟩ : syracuseStep 2020639 = 3030959) B3030959
theorem B35018077 : Blo 1796099 35018077 := bstep (se 3 (by rfl) ⟨6565889, by rfl⟩ : syracuseStep 35018077 = 13131779) B13131779
theorem B3413497 : Blo 1796099 3413497 := bstep (se 2 (by rfl) ⟨1280061, by rfl⟩ : syracuseStep 3413497 = 2560123) B2560123
theorem B2020927 : Blo 1796099 2020927 := bstep (se 1 (by rfl) ⟨1515695, by rfl⟩ : syracuseStep 2020927 = 3031391) B3031391
theorem B4855391 : Blo 1796099 4855391 := bstep (se 1 (by rfl) ⟨3641543, by rfl⟩ : syracuseStep 4855391 = 7283087) B7283087
theorem B4044383 : Blo 1796099 4044383 := bstep (se 1 (by rfl) ⟨3033287, by rfl⟩ : syracuseStep 4044383 = 6066575) B6066575
theorem B4044599 : Blo 1796099 4044599 := bstep (se 1 (by rfl) ⟨3033449, by rfl⟩ : syracuseStep 4044599 = 6066899) B6066899
theorem B7288631 : Blo 1796099 7288631 := bstep (se 1 (by rfl) ⟨5466473, by rfl⟩ : syracuseStep 7288631 = 10932947) B10932947
theorem B9099215 : Blo 1796099 9099215 := bstep (se 1 (by rfl) ⟨6824411, by rfl⟩ : syracuseStep 9099215 = 13648823) B13648823
theorem B15349733 : Blo 1796099 15349733 := bstep (se 4 (by rfl) ⟨1439037, by rfl⟩ : syracuseStep 15349733 = 2878075) B2878075
theorem B6821921 : Blo 1796099 6821921 := bstep (se 2 (by rfl) ⟨2558220, by rfl⟩ : syracuseStep 6821921 = 5116441) B5116441
theorem B10237985 : Blo 1796099 10237985 := bstep (se 2 (by rfl) ⟨3839244, by rfl⟩ : syracuseStep 10237985 = 7678489) B7678489
theorem B4044905 : Blo 1796099 4044905 := bstep (se 2 (by rfl) ⟨1516839, by rfl⟩ : syracuseStep 4044905 = 3033679) B3033679
theorem B2021755 : Blo 1796099 2021755 := bstep (se 1 (by rfl) ⟨1516316, by rfl⟩ : syracuseStep 2021755 = 3032633) B3032633
theorem B77896187 : Blo 1796099 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B4045391 : Blo 1796099 4045391 := bstep (se 1 (by rfl) ⟨3034043, by rfl⟩ : syracuseStep 4045391 = 6068087) B6068087
theorem B6822575 : Blo 1796099 6822575 := bstep (se 1 (by rfl) ⟨5116931, by rfl⟩ : syracuseStep 6822575 = 10233863) B10233863
theorem B4045535 : Blo 1796099 4045535 := bstep (se 1 (by rfl) ⟨3034151, by rfl⟩ : syracuseStep 4045535 = 6068303) B6068303
theorem B2022223 : Blo 1796099 2022223 := bstep (se 1 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 2022223 = 3033335) B3033335
theorem B41483153 : Blo 1796099 41483153 := bstep (se 2 (by rfl) ⟨15556182, by rfl⟩ : syracuseStep 41483153 = 31112365) B31112365
theorem B9100187 : Blo 1796099 9100187 := bstep (se 1 (by rfl) ⟨6825140, by rfl⟩ : syracuseStep 9100187 = 13650281) B13650281
theorem B38878231 : Blo 1796099 38878231 := bstep (se 1 (by rfl) ⟨29158673, by rfl⟩ : syracuseStep 38878231 = 58317347) B58317347
theorem B4922491 : Blo 1796099 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B7675003 : Blo 1796099 7675003 := bstep (se 1 (by rfl) ⟨5756252, by rfl⟩ : syracuseStep 7675003 = 11512505) B11512505
theorem B15359165 : Blo 1796099 15359165 := bstep (se 3 (by rfl) ⟨2879843, by rfl⟩ : syracuseStep 15359165 = 5759687) B5759687
theorem B2022619 : Blo 1796099 2022619 := bstep (se 1 (by rfl) ⟨1516964, by rfl⟩ : syracuseStep 2022619 = 3033929) B3033929
theorem B2694377 : Blo 1796099 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B2694431 : Blo 1796099 2694431 := bstep (se 1 (by rfl) ⟨2020823, by rfl⟩ : syracuseStep 2694431 = 4041647) B4041647
theorem B4857185 : Blo 1796099 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B9100673 : Blo 1796099 9100673 := bstep (se 2 (by rfl) ⟨3412752, by rfl⟩ : syracuseStep 9100673 = 6825505) B6825505
theorem B2694599 : Blo 1796099 2694599 := bstep (se 1 (by rfl) ⟨2020949, by rfl⟩ : syracuseStep 2694599 = 4041899) B4041899
theorem B4316615 : Blo 1796099 4316615 := bstep (se 1 (by rfl) ⟨3237461, by rfl⟩ : syracuseStep 4316615 = 6474923) B6474923
theorem B7290449 : Blo 1796099 7290449 := bstep (se 2 (by rfl) ⟨2733918, by rfl⟩ : syracuseStep 7290449 = 5467837) B5467837
theorem B10231379 : Blo 1796099 10231379 := bstep (se 1 (by rfl) ⟨7673534, by rfl⟩ : syracuseStep 10231379 = 15347069) B15347069
theorem B15351443 : Blo 1796099 15351443 := bstep (se 1 (by rfl) ⟨11513582, by rfl⟩ : syracuseStep 15351443 = 23027165) B23027165
theorem B19431161 : Blo 1796099 19431161 := bstep (se 2 (by rfl) ⟨7286685, by rfl⟩ : syracuseStep 19431161 = 14573371) B14573371
theorem B2694953 : Blo 1796099 2694953 := bstep (se 2 (by rfl) ⟨1010607, by rfl⟩ : syracuseStep 2694953 = 2021215) B2021215
theorem B2694959 : Blo 1796099 2694959 := bstep (se 1 (by rfl) ⟨2021219, by rfl⟩ : syracuseStep 2694959 = 4042439) B4042439
theorem B7675823 : Blo 1796099 7675823 := bstep (se 1 (by rfl) ⟨5756867, by rfl⟩ : syracuseStep 7675823 = 11513735) B11513735
theorem B126132161 : Blo 1796099 126132161 := bstep (se 2 (by rfl) ⟨47299560, by rfl⟩ : syracuseStep 126132161 = 94599121) B94599121
theorem B5759009 : Blo 1796099 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B20758799 : Blo 1796099 20758799 := bstep (se 1 (by rfl) ⟨15569099, by rfl⟩ : syracuseStep 20758799 = 31138199) B31138199
theorem B5759419 : Blo 1796099 5759419 := bstep (se 1 (by rfl) ⟨4319564, by rfl⟩ : syracuseStep 5759419 = 8639129) B8639129
theorem B2695631 : Blo 1796099 2695631 := bstep (se 1 (by rfl) ⟨2021723, by rfl⟩ : syracuseStep 2695631 = 4043447) B4043447
theorem B2695673 : Blo 1796099 2695673 := bstep (se 2 (by rfl) ⟨1010877, by rfl⟩ : syracuseStep 2695673 = 2021755) B2021755
theorem B2695775 : Blo 1796099 2695775 := bstep (se 1 (by rfl) ⟨2021831, by rfl⟩ : syracuseStep 2695775 = 4043663) B4043663
theorem B9094031 : Blo 1796099 9094031 := bstep (se 1 (by rfl) ⟨6820523, by rfl⟩ : syracuseStep 9094031 = 13641047) B13641047
theorem B12952493 : Blo 1796099 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B3032059 : Blo 1796099 3032059 := bstep (se 1 (by rfl) ⟨2274044, by rfl⟩ : syracuseStep 3032059 = 4548089) B4548089
theorem B3236927 : Blo 1796099 3236927 := bstep (se 1 (by rfl) ⟨2427695, by rfl⟩ : syracuseStep 3236927 = 4855391) B4855391
theorem B2696255 : Blo 1796099 2696255 := bstep (se 1 (by rfl) ⟨2022191, by rfl⟩ : syracuseStep 2696255 = 4044383) B4044383
theorem B2696297 : Blo 1796099 2696297 := bstep (se 2 (by rfl) ⟨1011111, by rfl⟩ : syracuseStep 2696297 = 2022223) B2022223
theorem B6063227 : Blo 1796099 6063227 := bstep (se 1 (by rfl) ⟨4547420, by rfl⟩ : syracuseStep 6063227 = 9094841) B9094841
theorem B2696399 : Blo 1796099 2696399 := bstep (se 1 (by rfl) ⟨2022299, by rfl⟩ : syracuseStep 2696399 = 4044599) B4044599
theorem B4859087 : Blo 1796099 4859087 := bstep (se 1 (by rfl) ⟨3644315, by rfl⟩ : syracuseStep 4859087 = 7288631) B7288631
theorem B10233155 : Blo 1796099 10233155 := bstep (se 1 (by rfl) ⟨7674866, by rfl⟩ : syracuseStep 10233155 = 15349733) B15349733
theorem B4547947 : Blo 1796099 4547947 := bstep (se 1 (by rfl) ⟨3410960, by rfl⟩ : syracuseStep 4547947 = 6821921) B6821921
theorem B6825323 : Blo 1796099 6825323 := bstep (se 1 (by rfl) ⟨5118992, by rfl⟩ : syracuseStep 6825323 = 10237985) B10237985
theorem B6063497 : Blo 1796099 6063497 := bstep (se 2 (by rfl) ⟨2273811, by rfl⟩ : syracuseStep 6063497 = 4547623) B4547623
theorem B2696603 : Blo 1796099 2696603 := bstep (se 1 (by rfl) ⟨2022452, by rfl⟩ : syracuseStep 2696603 = 4044905) B4044905
theorem B3032491 : Blo 1796099 3032491 := bstep (se 1 (by rfl) ⟨2274368, by rfl⟩ : syracuseStep 3032491 = 4548737) B4548737
theorem B6563321 : Blo 1796099 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B10233337 : Blo 1796099 10233337 := bstep (se 2 (by rfl) ⟨3837501, by rfl⟩ : syracuseStep 10233337 = 7675003) B7675003
theorem B3032687 : Blo 1796099 3032687 := bstep (se 1 (by rfl) ⟨2274515, by rfl⟩ : syracuseStep 3032687 = 4549031) B4549031
theorem B2696825 : Blo 1796099 2696825 := bstep (se 2 (by rfl) ⟨1011309, by rfl⟩ : syracuseStep 2696825 = 2022619) B2022619
theorem B51840647 : Blo 1796099 51840647 := bstep (se 1 (by rfl) ⟨38880485, by rfl⟩ : syracuseStep 51840647 = 77760971) B77760971
theorem B51930791 : Blo 1796099 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B3032795 : Blo 1796099 3032795 := bstep (se 1 (by rfl) ⟨2274596, by rfl⟩ : syracuseStep 3032795 = 4549193) B4549193
theorem B2696927 : Blo 1796099 2696927 := bstep (se 1 (by rfl) ⟨2022695, by rfl⟩ : syracuseStep 2696927 = 4045391) B4045391
theorem B6473479 : Blo 1796099 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B4548383 : Blo 1796099 4548383 := bstep (se 1 (by rfl) ⟨3411287, by rfl⟩ : syracuseStep 4548383 = 6822575) B6822575
theorem B2697023 : Blo 1796099 2697023 := bstep (se 1 (by rfl) ⟨2022767, by rfl⟩ : syracuseStep 2697023 = 4045535) B4045535
theorem B3033031 : Blo 1796099 3033031 := bstep (se 1 (by rfl) ⟨2274773, by rfl⟩ : syracuseStep 3033031 = 4549547) B4549547
theorem B6064253 : Blo 1796099 6064253 := bstep (se 3 (by rfl) ⟨1137047, by rfl⟩ : syracuseStep 6064253 = 2274095) B2274095
theorem B1796251 : Blo 1796099 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B1796287 : Blo 1796099 1796287 := bstep (se 1 (by rfl) ⟨1347215, by rfl⟩ : syracuseStep 1796287 = 2694431) B2694431
theorem B5834987 : Blo 1796099 5834987 := bstep (se 1 (by rfl) ⟨4376240, by rfl⟩ : syracuseStep 5834987 = 8752481) B8752481
theorem B3836153 : Blo 1796099 3836153 := bstep (se 2 (by rfl) ⟨1438557, by rfl⟩ : syracuseStep 3836153 = 2877115) B2877115
theorem B1796399 : Blo 1796099 1796399 := bstep (se 1 (by rfl) ⟨1347299, by rfl⟩ : syracuseStep 1796399 = 2694599) B2694599
theorem B2877743 : Blo 1796099 2877743 := bstep (se 1 (by rfl) ⟨2158307, by rfl⟩ : syracuseStep 2877743 = 4316615) B4316615
theorem B6064523 : Blo 1796099 6064523 := bstep (se 1 (by rfl) ⟨4548392, by rfl⟩ : syracuseStep 6064523 = 9096785) B9096785
theorem B4860299 : Blo 1796099 4860299 := bstep (se 1 (by rfl) ⟨3645224, by rfl⟩ : syracuseStep 4860299 = 7290449) B7290449
theorem B10234295 : Blo 1796099 10234295 := bstep (se 1 (by rfl) ⟨7675721, by rfl⟩ : syracuseStep 10234295 = 15351443) B15351443
theorem B12954107 : Blo 1796099 12954107 := bstep (se 1 (by rfl) ⟨9715580, by rfl⟩ : syracuseStep 12954107 = 19431161) B19431161
theorem B3836443 : Blo 1796099 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B1796635 : Blo 1796099 1796635 := bstep (se 1 (by rfl) ⟨1347476, by rfl⟩ : syracuseStep 1796635 = 2694953) B2694953
theorem B1796639 : Blo 1796099 1796639 := bstep (se 1 (by rfl) ⟨1347479, by rfl⟩ : syracuseStep 1796639 = 2694959) B2694959
theorem B12290699 : Blo 1796099 12290699 := bstep (se 1 (by rfl) ⟨9218024, by rfl⟩ : syracuseStep 12290699 = 18436049) B18436049
theorem B10930859 : Blo 1796099 10930859 := bstep (se 1 (by rfl) ⟨8198144, by rfl⟩ : syracuseStep 10930859 = 16396289) B16396289
theorem B3033787 : Blo 1796099 3033787 := bstep (se 1 (by rfl) ⟨2275340, by rfl⟩ : syracuseStep 3033787 = 4550681) B4550681
theorem B32778989 : Blo 1796099 32778989 := bstep (se 3 (by rfl) ⟨6146060, by rfl⟩ : syracuseStep 32778989 = 12292121) B12292121
theorem B16403219 : Blo 1796099 16403219 := bstep (se 1 (by rfl) ⟨12302414, by rfl⟩ : syracuseStep 16403219 = 24604829) B24604829
theorem B7383863 : Blo 1796099 7383863 := bstep (se 1 (by rfl) ⟨5537897, by rfl⟩ : syracuseStep 7383863 = 11075795) B11075795
theorem B1796955 : Blo 1796099 1796955 := bstep (se 1 (by rfl) ⟨1347716, by rfl⟩ : syracuseStep 1796955 = 2695433) B2695433
theorem B18697067 : Blo 1796099 18697067 := bstep (se 1 (by rfl) ⟨14022800, by rfl⟩ : syracuseStep 18697067 = 28045601) B28045601
theorem B1797023 : Blo 1796099 1797023 := bstep (se 1 (by rfl) ⟨1347767, by rfl⟩ : syracuseStep 1797023 = 2695535) B2695535
theorem B11512763 : Blo 1796099 11512763 := bstep (se 1 (by rfl) ⟨8634572, by rfl⟩ : syracuseStep 11512763 = 17269145) B17269145
theorem B3410923 : Blo 1796099 3410923 := bstep (se 1 (by rfl) ⟨2558192, by rfl⟩ : syracuseStep 3410923 = 5116385) B5116385
theorem B3034091 : Blo 1796099 3034091 := bstep (se 1 (by rfl) ⟨2275568, by rfl⟩ : syracuseStep 3034091 = 4551137) B4551137
theorem B5114927 : Blo 1796099 5114927 := bstep (se 1 (by rfl) ⟨3836195, by rfl⟩ : syracuseStep 5114927 = 7672391) B7672391
theorem B1797167 : Blo 1796099 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B4549679 : Blo 1796099 4549679 := bstep (se 1 (by rfl) ⟨3412259, by rfl⟩ : syracuseStep 4549679 = 6824519) B6824519
theorem B1797191 : Blo 1796099 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B1797343 : Blo 1796099 1797343 := bstep (se 1 (by rfl) ⟨1348007, by rfl⟩ : syracuseStep 1797343 = 2696015) B2696015
theorem B22154563 : Blo 1796099 22154563 := bstep (se 1 (by rfl) ⟨16615922, by rfl⟩ : syracuseStep 22154563 = 33231845) B33231845
theorem B6147407 : Blo 1796099 6147407 := bstep (se 1 (by rfl) ⟨4610555, by rfl⟩ : syracuseStep 6147407 = 9221111) B9221111
theorem B5115325 : Blo 1796099 5115325 := bstep (se 3 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 5115325 = 1918247) B1918247
theorem B1797607 : Blo 1796099 1797607 := bstep (se 1 (by rfl) ⟨1348205, by rfl⟩ : syracuseStep 1797607 = 2696411) B2696411
theorem B5115383 : Blo 1796099 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B4042313 : Blo 1796099 4042313 := bstep (se 2 (by rfl) ⟨1515867, by rfl⟩ : syracuseStep 4042313 = 3031735) B3031735
theorem B1797723 : Blo 1796099 1797723 := bstep (se 1 (by rfl) ⟨1348292, by rfl⟩ : syracuseStep 1797723 = 2696585) B2696585
theorem B1797959 : Blo 1796099 1797959 := bstep (se 1 (by rfl) ⟨1348469, by rfl⟩ : syracuseStep 1797959 = 2696939) B2696939
theorem B4550539 : Blo 1796099 4550539 := bstep (se 1 (by rfl) ⟨3412904, by rfl⟩ : syracuseStep 4550539 = 6825809) B6825809
theorem B6066143 : Blo 1796099 6066143 := bstep (se 1 (by rfl) ⟨4549607, by rfl⟩ : syracuseStep 6066143 = 9099215) B9099215
theorem B12955697 : Blo 1796099 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B6066305 : Blo 1796099 6066305 := bstep (se 2 (by rfl) ⟨2274864, by rfl⟩ : syracuseStep 6066305 = 4549729) B4549729
theorem B4550843 : Blo 1796099 4550843 := bstep (se 1 (by rfl) ⟨3413132, by rfl⟩ : syracuseStep 4550843 = 6826265) B6826265
theorem B46690769 : Blo 1796099 46690769 := bstep (se 2 (by rfl) ⟨17509038, by rfl⟩ : syracuseStep 46690769 = 35018077) B35018077
theorem B20460113 : Blo 1796099 20460113 := bstep (se 2 (by rfl) ⟨7672542, by rfl⟩ : syracuseStep 20460113 = 15345085) B15345085
theorem B6066791 : Blo 1796099 6066791 := bstep (se 1 (by rfl) ⟨4550093, by rfl⟩ : syracuseStep 6066791 = 9100187) B9100187
theorem B4551329 : Blo 1796099 4551329 := bstep (se 2 (by rfl) ⟨1706748, by rfl⟩ : syracuseStep 4551329 = 3413497) B3413497
theorem B6067115 : Blo 1796099 6067115 := bstep (se 1 (by rfl) ⟨4550336, by rfl⟩ : syracuseStep 6067115 = 9100673) B9100673
theorem B4043771 : Blo 1796099 4043771 := bstep (se 1 (by rfl) ⟨3032828, by rfl⟩ : syracuseStep 4043771 = 6065657) B6065657
theorem B6820919 : Blo 1796099 6820919 := bstep (se 1 (by rfl) ⟨5115689, by rfl⟩ : syracuseStep 6820919 = 10231379) B10231379
theorem B20468861 : Blo 1796099 20468861 := bstep (se 3 (by rfl) ⟨3837911, by rfl⟩ : syracuseStep 20468861 = 7675823) B7675823
theorem B336352429 : Blo 1796099 336352429 := bstep (se 3 (by rfl) ⟨63066080, by rfl⟩ : syracuseStep 336352429 = 126132161) B126132161
theorem B4043951 : Blo 1796099 4043951 := bstep (se 1 (by rfl) ⟨3032963, by rfl⟩ : syracuseStep 4043951 = 6065927) B6065927
theorem B4043987 : Blo 1796099 4043987 := bstep (se 1 (by rfl) ⟨3032990, by rfl⟩ : syracuseStep 4043987 = 6065981) B6065981
theorem B6067547 : Blo 1796099 6067547 := bstep (se 1 (by rfl) ⟨4550660, by rfl⟩ : syracuseStep 6067547 = 9101321) B9101321
theorem B6067655 : Blo 1796099 6067655 := bstep (se 1 (by rfl) ⟨4550741, by rfl⟩ : syracuseStep 6067655 = 9101483) B9101483
theorem B4044257 : Blo 1796099 4044257 := bstep (se 2 (by rfl) ⟨1516596, by rfl⟩ : syracuseStep 4044257 = 3033193) B3033193
theorem B20739629 : Blo 1796099 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B10237529 : Blo 1796099 10237529 := bstep (se 2 (by rfl) ⟨3839073, by rfl⟩ : syracuseStep 10237529 = 7678147) B7678147
theorem B15349459 : Blo 1796099 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B2275067 : Blo 1796099 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B6067979 : Blo 1796099 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B6149951 : Blo 1796099 6149951 := bstep (se 1 (by rfl) ⟨4612463, by rfl⟩ : syracuseStep 6149951 = 9224927) B9224927
theorem B2021359 : Blo 1796099 2021359 := bstep (se 1 (by rfl) ⟨1516019, by rfl⟩ : syracuseStep 2021359 = 3032039) B3032039
theorem B4855801 : Blo 1796099 4855801 := bstep (se 2 (by rfl) ⟨1820925, by rfl⟩ : syracuseStep 4855801 = 3641851) B3641851
theorem B25909253 : Blo 1796099 25909253 := bstep (se 4 (by rfl) ⟨2428992, by rfl⟩ : syracuseStep 25909253 = 4857985) B4857985
theorem B6068249 : Blo 1796099 6068249 := bstep (se 2 (by rfl) ⟨2275593, by rfl⟩ : syracuseStep 6068249 = 4551187) B4551187
theorem B10229921 : Blo 1796099 10229921 := bstep (se 2 (by rfl) ⟨3836220, by rfl⟩ : syracuseStep 10229921 = 7672441) B7672441
theorem B4856051 : Blo 1796099 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B47962397 : Blo 1796099 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B5757227 : Blo 1796099 5757227 := bstep (se 1 (by rfl) ⟨4317920, by rfl⟩ : syracuseStep 5757227 = 8635841) B8635841
theorem B13646393 : Blo 1796099 13646393 := bstep (se 2 (by rfl) ⟨5117397, by rfl⟩ : syracuseStep 13646393 = 10234795) B10234795
theorem B51837641 : Blo 1796099 51837641 := bstep (se 2 (by rfl) ⟨19439115, by rfl⟩ : syracuseStep 51837641 = 38878231) B38878231
theorem B65592139 : Blo 1796099 65592139 := bstep (se 1 (by rfl) ⟨49194104, by rfl⟩ : syracuseStep 65592139 = 98388209) B98388209
theorem B5757779 : Blo 1796099 5757779 := bstep (se 1 (by rfl) ⟨4318334, by rfl⟩ : syracuseStep 5757779 = 8636669) B8636669
theorem B26270569 : Blo 1796099 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B6822893 : Blo 1796099 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B2694185 : Blo 1796099 2694185 := bstep (se 2 (by rfl) ⟨1010319, by rfl⟩ : syracuseStep 2694185 = 2020639) B2020639
theorem B2694191 : Blo 1796099 2694191 := bstep (se 1 (by rfl) ⟨2020643, by rfl⟩ : syracuseStep 2694191 = 4041287) B4041287
theorem B2694215 : Blo 1796099 2694215 := bstep (se 1 (by rfl) ⟨2020661, by rfl⟩ : syracuseStep 2694215 = 4041323) B4041323
theorem B73776365 : Blo 1796099 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B27655435 : Blo 1796099 27655435 := bstep (se 1 (by rfl) ⟨20741576, by rfl⟩ : syracuseStep 27655435 = 41483153) B41483153
theorem B2694479 : Blo 1796099 2694479 := bstep (se 1 (by rfl) ⟨2020859, by rfl⟩ : syracuseStep 2694479 = 4041719) B4041719
theorem B5758303 : Blo 1796099 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B2694569 : Blo 1796099 2694569 := bstep (se 2 (by rfl) ⟨1010463, by rfl⟩ : syracuseStep 2694569 = 2020927) B2020927
theorem B10239443 : Blo 1796099 10239443 := bstep (se 1 (by rfl) ⟨7679582, by rfl⟩ : syracuseStep 10239443 = 15359165) B15359165
theorem B2694719 : Blo 1796099 2694719 := bstep (se 1 (by rfl) ⟨2021039, by rfl⟩ : syracuseStep 2694719 = 4042079) B4042079
theorem B5119631 : Blo 1796099 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B2694983 : Blo 1796099 2694983 := bstep (se 1 (by rfl) ⟨2021237, by rfl⟩ : syracuseStep 2694983 = 4042475) B4042475
theorem B2695067 : Blo 1796099 2695067 := bstep (se 1 (by rfl) ⟨2021300, by rfl⟩ : syracuseStep 2695067 = 4042601) B4042601
theorem B13640075 : Blo 1796099 13640075 := bstep (se 1 (by rfl) ⟨10230056, by rfl⟩ : syracuseStep 13640075 = 20460113) B20460113
theorem B6062687 : Blo 1796099 6062687 := bstep (se 1 (by rfl) ⟨4547015, by rfl⟩ : syracuseStep 6062687 = 9094031) B9094031
theorem B8634995 : Blo 1796099 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B2695847 : Blo 1796099 2695847 := bstep (se 1 (by rfl) ⟨2021885, by rfl⟩ : syracuseStep 2695847 = 4043771) B4043771
theorem B4547279 : Blo 1796099 4547279 := bstep (se 1 (by rfl) ⟨3410459, by rfl⟩ : syracuseStep 4547279 = 6820919) B6820919
theorem B2695967 : Blo 1796099 2695967 := bstep (se 1 (by rfl) ⟨2021975, by rfl⟩ : syracuseStep 2695967 = 4043951) B4043951
theorem B2695991 : Blo 1796099 2695991 := bstep (se 1 (by rfl) ⟨2021993, by rfl⟩ : syracuseStep 2695991 = 4043987) B4043987
theorem B2696171 : Blo 1796099 2696171 := bstep (se 1 (by rfl) ⟨2022128, by rfl⟩ : syracuseStep 2696171 = 4044257) B4044257
theorem B4375547 : Blo 1796099 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B6825019 : Blo 1796099 6825019 := bstep (se 1 (by rfl) ⟨5118764, by rfl⟩ : syracuseStep 6825019 = 10237529) B10237529
theorem B34620527 : Blo 1796099 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B3032255 : Blo 1796099 3032255 := bstep (se 1 (by rfl) ⟨2274191, by rfl⟩ : syracuseStep 3032255 = 4548383) B4548383
theorem B4547897 : Blo 1796099 4547897 := bstep (se 2 (by rfl) ⟨1705461, by rfl⟩ : syracuseStep 4547897 = 3410923) B3410923
theorem B2557435 : Blo 1796099 2557435 := bstep (se 1 (by rfl) ⟨1918076, by rfl⟩ : syracuseStep 2557435 = 3836153) B3836153
theorem B31974931 : Blo 1796099 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B1918495 : Blo 1796099 1918495 := bstep (se 1 (by rfl) ⟨1438871, by rfl⟩ : syracuseStep 1918495 = 2877743) B2877743
theorem B8636071 : Blo 1796099 8636071 := bstep (se 1 (by rfl) ⟨6477053, by rfl⟩ : syracuseStep 8636071 = 12954107) B12954107
theorem B36873913 : Blo 1796099 36873913 := bstep (se 2 (by rfl) ⟨13827717, by rfl⟩ : syracuseStep 36873913 = 27655435) B27655435
theorem B8193799 : Blo 1796099 8193799 := bstep (se 1 (by rfl) ⟨6145349, by rfl⟩ : syracuseStep 8193799 = 12290699) B12290699
theorem B7677737 : Blo 1796099 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B6063929 : Blo 1796099 6063929 := bstep (se 2 (by rfl) ⟨2273973, by rfl⟩ : syracuseStep 6063929 = 4547947) B4547947
theorem B4548595 : Blo 1796099 4548595 := bstep (se 1 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 4548595 = 6822893) B6822893
theorem B1796123 : Blo 1796099 1796123 := bstep (se 1 (by rfl) ⟨1347092, by rfl⟩ : syracuseStep 1796123 = 2694185) B2694185
theorem B1796127 : Blo 1796099 1796127 := bstep (se 1 (by rfl) ⟨1347095, by rfl⟩ : syracuseStep 1796127 = 2694191) B2694191
theorem B3409951 : Blo 1796099 3409951 := bstep (se 1 (by rfl) ⟨2557463, by rfl⟩ : syracuseStep 3409951 = 5114927) B5114927
theorem B3033119 : Blo 1796099 3033119 := bstep (se 1 (by rfl) ⟨2274839, by rfl⟩ : syracuseStep 3033119 = 4549679) B4549679
theorem B1796143 : Blo 1796099 1796143 := bstep (se 1 (by rfl) ⟨1347107, by rfl⟩ : syracuseStep 1796143 = 2694215) B2694215
theorem B1796319 : Blo 1796099 1796319 := bstep (se 1 (by rfl) ⟨1347239, by rfl⟩ : syracuseStep 1796319 = 2694479) B2694479
theorem B4098271 : Blo 1796099 4098271 := bstep (se 1 (by rfl) ⟨3073703, by rfl⟩ : syracuseStep 4098271 = 6147407) B6147407
theorem B1796379 : Blo 1796099 1796379 := bstep (se 1 (by rfl) ⟨1347284, by rfl⟩ : syracuseStep 1796379 = 2694569) B2694569
theorem B20465945 : Blo 1796099 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B6826295 : Blo 1796099 6826295 := bstep (se 1 (by rfl) ⟨5119721, by rfl⟩ : syracuseStep 6826295 = 10239443) B10239443
theorem B3410255 : Blo 1796099 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B1796479 : Blo 1796099 1796479 := bstep (se 1 (by rfl) ⟨1347359, by rfl⟩ : syracuseStep 1796479 = 2694719) B2694719
theorem B1796655 : Blo 1796099 1796655 := bstep (se 1 (by rfl) ⟨1347491, by rfl⟩ : syracuseStep 1796655 = 2694983) B2694983
theorem B1796711 : Blo 1796099 1796711 := bstep (se 1 (by rfl) ⟨1347533, by rfl⟩ : syracuseStep 1796711 = 2695067) B2695067
theorem B6474401 : Blo 1796099 6474401 := bstep (se 2 (by rfl) ⟨2427900, by rfl⟩ : syracuseStep 6474401 = 4855801) B4855801
theorem B8637131 : Blo 1796099 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B3033895 : Blo 1796099 3033895 := bstep (se 1 (by rfl) ⟨2275421, by rfl⟩ : syracuseStep 3033895 = 4550843) B4550843
theorem B1797087 : Blo 1796099 1797087 := bstep (se 1 (by rfl) ⟨1347815, by rfl⟩ : syracuseStep 1797087 = 2695631) B2695631
theorem B1797115 : Blo 1796099 1797115 := bstep (se 1 (by rfl) ⟨1347836, by rfl⟩ : syracuseStep 1797115 = 2695673) B2695673
theorem B1797183 : Blo 1796099 1797183 := bstep (se 1 (by rfl) ⟨1347887, by rfl⟩ : syracuseStep 1797183 = 2695775) B2695775
theorem B3034219 : Blo 1796099 3034219 := bstep (se 1 (by rfl) ⟨2275664, by rfl⟩ : syracuseStep 3034219 = 4551329) B4551329
theorem B7679225 : Blo 1796099 7679225 := bstep (se 2 (by rfl) ⟨2879709, by rfl⟩ : syracuseStep 7679225 = 5759419) B5759419
theorem B5115257 : Blo 1796099 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1797503 : Blo 1796099 1797503 := bstep (se 1 (by rfl) ⟨1348127, by rfl⟩ : syracuseStep 1797503 = 2696255) B2696255
theorem B55356797 : Blo 1796099 55356797 := bstep (se 3 (by rfl) ⟨10379399, by rfl⟩ : syracuseStep 55356797 = 20758799) B20758799
theorem B1797531 : Blo 1796099 1797531 := bstep (se 1 (by rfl) ⟨1348148, by rfl⟩ : syracuseStep 1797531 = 2696297) B2696297
theorem B4042151 : Blo 1796099 4042151 := bstep (se 1 (by rfl) ⟨3031613, by rfl⟩ : syracuseStep 4042151 = 6063227) B6063227
theorem B1797599 : Blo 1796099 1797599 := bstep (se 1 (by rfl) ⟨1348199, by rfl⟩ : syracuseStep 1797599 = 2696399) B2696399
theorem B1793879621 : Blo 1796099 1793879621 := bstep (se 4 (by rfl) ⟨168176214, by rfl⟩ : syracuseStep 1793879621 = 336352429) B336352429
theorem B4550215 : Blo 1796099 4550215 := bstep (se 1 (by rfl) ⟨3412661, by rfl⟩ : syracuseStep 4550215 = 6825323) B6825323
theorem B4042331 : Blo 1796099 4042331 := bstep (se 1 (by rfl) ⟨3031748, by rfl⟩ : syracuseStep 4042331 = 6063497) B6063497
theorem B1797735 : Blo 1796099 1797735 := bstep (se 1 (by rfl) ⟨1348301, by rfl⟩ : syracuseStep 1797735 = 2696603) B2696603
theorem B1797883 : Blo 1796099 1797883 := bstep (se 1 (by rfl) ⟨1348412, by rfl⟩ : syracuseStep 1797883 = 2696825) B2696825
theorem B1797951 : Blo 1796099 1797951 := bstep (se 1 (by rfl) ⟨1348463, by rfl⟩ : syracuseStep 1797951 = 2696927) B2696927
theorem B4099967 : Blo 1796099 4099967 := bstep (se 1 (by rfl) ⟨3074975, by rfl⟩ : syracuseStep 4099967 = 6149951) B6149951
theorem B1798015 : Blo 1796099 1798015 := bstep (se 1 (by rfl) ⟨1348511, by rfl⟩ : syracuseStep 1798015 = 2697023) B2697023
theorem B4042745 : Blo 1796099 4042745 := bstep (se 2 (by rfl) ⟨1516029, by rfl⟩ : syracuseStep 4042745 = 3032059) B3032059
theorem B17272835 : Blo 1796099 17272835 := bstep (se 1 (by rfl) ⟨12954626, by rfl⟩ : syracuseStep 17272835 = 25909253) B25909253
theorem B4042835 : Blo 1796099 4042835 := bstep (se 1 (by rfl) ⟨3032126, by rfl⟩ : syracuseStep 4042835 = 6064253) B6064253
theorem B6819947 : Blo 1796099 6819947 := bstep (se 1 (by rfl) ⟨5114960, by rfl⟩ : syracuseStep 6819947 = 10229921) B10229921
theorem B3838151 : Blo 1796099 3838151 := bstep (se 1 (by rfl) ⟨2878613, by rfl⟩ : syracuseStep 3838151 = 5757227) B5757227
theorem B4043015 : Blo 1796099 4043015 := bstep (se 1 (by rfl) ⟨3032261, by rfl⟩ : syracuseStep 4043015 = 6064523) B6064523
theorem B3240199 : Blo 1796099 3240199 := bstep (se 1 (by rfl) ⟨2430149, by rfl⟩ : syracuseStep 3240199 = 4860299) B4860299
theorem B9097595 : Blo 1796099 9097595 := bstep (se 1 (by rfl) ⟨6823196, by rfl⟩ : syracuseStep 9097595 = 13646393) B13646393
theorem B7287239 : Blo 1796099 7287239 := bstep (se 1 (by rfl) ⟨5465429, by rfl⟩ : syracuseStep 7287239 = 10930859) B10930859
theorem B34558427 : Blo 1796099 34558427 := bstep (se 1 (by rfl) ⟨25918820, by rfl⟩ : syracuseStep 34558427 = 51837641) B51837641
theorem B21852659 : Blo 1796099 21852659 := bstep (se 1 (by rfl) ⟨16389494, by rfl⟩ : syracuseStep 21852659 = 32778989) B32778989
theorem B3838519 : Blo 1796099 3838519 := bstep (se 1 (by rfl) ⟨2878889, by rfl⟩ : syracuseStep 3838519 = 5757779) B5757779
theorem B4043321 : Blo 1796099 4043321 := bstep (se 2 (by rfl) ⟨1516245, by rfl⟩ : syracuseStep 4043321 = 3032491) B3032491
theorem B12464711 : Blo 1796099 12464711 := bstep (se 1 (by rfl) ⟨9348533, by rfl⟩ : syracuseStep 12464711 = 18697067) B18697067
theorem B6820433 : Blo 1796099 6820433 := bstep (se 2 (by rfl) ⟨2557662, by rfl⟩ : syracuseStep 6820433 = 5115325) B5115325
theorem B6066845 : Blo 1796099 6066845 := bstep (se 3 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 6066845 = 2275067) B2275067
theorem B13644449 : Blo 1796099 13644449 := bstep (se 2 (by rfl) ⟨5116668, by rfl⟩ : syracuseStep 13644449 = 10233337) B10233337
theorem B19690301 : Blo 1796099 19690301 := bstep (se 3 (by rfl) ⟨3691931, by rfl⟩ : syracuseStep 19690301 = 7383863) B7383863
theorem B8631305 : Blo 1796099 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B3413087 : Blo 1796099 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B6067385 : Blo 1796099 6067385 := bstep (se 2 (by rfl) ⟨2275269, by rfl⟩ : syracuseStep 6067385 = 4550539) B4550539
theorem B4044041 : Blo 1796099 4044041 := bstep (se 2 (by rfl) ⟨1516515, by rfl⟩ : syracuseStep 4044041 = 3033031) B3033031
theorem B4044095 : Blo 1796099 4044095 := bstep (se 1 (by rfl) ⟨3033071, by rfl⟩ : syracuseStep 4044095 = 6066143) B6066143
theorem B3839339 : Blo 1796099 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B4044203 : Blo 1796099 4044203 := bstep (se 1 (by rfl) ⟨3033152, by rfl⟩ : syracuseStep 4044203 = 6066305) B6066305
theorem B8631805 : Blo 1796099 8631805 := bstep (se 3 (by rfl) ⟨1618463, by rfl⟩ : syracuseStep 8631805 = 3236927) B3236927
theorem B31127179 : Blo 1796099 31127179 := bstep (se 1 (by rfl) ⟨23345384, by rfl⟩ : syracuseStep 31127179 = 46690769) B46690769
theorem B4044527 : Blo 1796099 4044527 := bstep (se 1 (by rfl) ⟨3033395, by rfl⟩ : syracuseStep 4044527 = 6066791) B6066791
theorem B12957565 : Blo 1796099 12957565 := bstep (se 3 (by rfl) ⟨2429543, by rfl⟩ : syracuseStep 12957565 = 4859087) B4859087
theorem B4044743 : Blo 1796099 4044743 := bstep (se 1 (by rfl) ⟨3033557, by rfl⟩ : syracuseStep 4044743 = 6067115) B6067115
theorem B12949469 : Blo 1796099 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B13645907 : Blo 1796099 13645907 := bstep (se 1 (by rfl) ⟨10234430, by rfl⟩ : syracuseStep 13645907 = 20468861) B20468861
theorem B6822103 : Blo 1796099 6822103 := bstep (se 1 (by rfl) ⟨5116577, by rfl⟩ : syracuseStep 6822103 = 10233155) B10233155
theorem B4045031 : Blo 1796099 4045031 := bstep (se 1 (by rfl) ⟨3033773, by rfl⟩ : syracuseStep 4045031 = 6067547) B6067547
theorem B4045049 : Blo 1796099 4045049 := bstep (se 2 (by rfl) ⟨1516893, by rfl⟩ : syracuseStep 4045049 = 3033787) B3033787
theorem B4045103 : Blo 1796099 4045103 := bstep (se 1 (by rfl) ⟨3033827, by rfl⟩ : syracuseStep 4045103 = 6067655) B6067655
theorem B13826419 : Blo 1796099 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B2021791 : Blo 1796099 2021791 := bstep (se 1 (by rfl) ⟨1516343, by rfl⟩ : syracuseStep 2021791 = 3032687) B3032687
theorem B34560431 : Blo 1796099 34560431 := bstep (se 1 (by rfl) ⟨25920323, by rfl⟩ : syracuseStep 34560431 = 51840647) B51840647
theorem B87456185 : Blo 1796099 87456185 := bstep (se 2 (by rfl) ⟨32796069, by rfl⟩ : syracuseStep 87456185 = 65592139) B65592139
theorem B35027425 : Blo 1796099 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B2021863 : Blo 1796099 2021863 := bstep (se 1 (by rfl) ⟨1516397, by rfl⟩ : syracuseStep 2021863 = 3032795) B3032795
theorem B4045319 : Blo 1796099 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B4045499 : Blo 1796099 4045499 := bstep (se 1 (by rfl) ⟨3034124, by rfl⟩ : syracuseStep 4045499 = 6068249) B6068249
theorem B3889991 : Blo 1796099 3889991 := bstep (se 1 (by rfl) ⟨2917493, by rfl⟩ : syracuseStep 3889991 = 5834987) B5834987
theorem B6822863 : Blo 1796099 6822863 := bstep (se 1 (by rfl) ⟨5117147, by rfl⟩ : syracuseStep 6822863 = 10234295) B10234295
theorem B29539417 : Blo 1796099 29539417 := bstep (se 2 (by rfl) ⟨11077281, by rfl⟩ : syracuseStep 29539417 = 22154563) B22154563
theorem B10935479 : Blo 1796099 10935479 := bstep (se 1 (by rfl) ⟨8201609, by rfl⟩ : syracuseStep 10935479 = 16403219) B16403219
theorem B7675175 : Blo 1796099 7675175 := bstep (se 1 (by rfl) ⟨5756381, by rfl⟩ : syracuseStep 7675175 = 11512763) B11512763
theorem B2022727 : Blo 1796099 2022727 := bstep (se 1 (by rfl) ⟨1517045, by rfl⟩ : syracuseStep 2022727 = 3034091) B3034091
theorem B49184243 : Blo 1796099 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B2694875 : Blo 1796099 2694875 := bstep (se 1 (by rfl) ⟨2021156, by rfl⟩ : syracuseStep 2694875 = 4042313) B4042313
theorem B2695145 : Blo 1796099 2695145 := bstep (se 2 (by rfl) ⟨1010679, by rfl⟩ : syracuseStep 2695145 = 2021359) B2021359
theorem B4546601 : Blo 1796099 4546601 := bstep (se 2 (by rfl) ⟨1704975, by rfl⟩ : syracuseStep 4546601 = 3409951) B3409951
theorem B2695223 : Blo 1796099 2695223 := bstep (se 1 (by rfl) ⟨2021417, by rfl⟩ : syracuseStep 2695223 = 4042835) B4042835
theorem B4546631 : Blo 1796099 4546631 := bstep (se 1 (by rfl) ⟨3409973, by rfl⟩ : syracuseStep 4546631 = 6819947) B6819947
theorem B170532965 : Blo 1796099 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B2695343 : Blo 1796099 2695343 := bstep (se 1 (by rfl) ⟨2021507, by rfl⟩ : syracuseStep 2695343 = 4043015) B4043015
theorem B9093383 : Blo 1796099 9093383 := bstep (se 1 (by rfl) ⟨6820037, by rfl⟩ : syracuseStep 9093383 = 13640075) B13640075
theorem B5464361 : Blo 1796099 5464361 := bstep (se 2 (by rfl) ⟨2049135, by rfl⟩ : syracuseStep 5464361 = 4098271) B4098271
theorem B4858159 : Blo 1796099 4858159 := bstep (se 1 (by rfl) ⟨3643619, by rfl⟩ : syracuseStep 4858159 = 7287239) B7287239
theorem B2695547 : Blo 1796099 2695547 := bstep (se 1 (by rfl) ⟨2021660, by rfl⟩ : syracuseStep 2695547 = 4043321) B4043321
theorem B4546955 : Blo 1796099 4546955 := bstep (se 1 (by rfl) ⟨3410216, by rfl⟩ : syracuseStep 4546955 = 6820433) B6820433
theorem B3031519 : Blo 1796099 3031519 := bstep (se 1 (by rfl) ⟨2273639, by rfl⟩ : syracuseStep 3031519 = 4547279) B4547279
theorem B2695721 : Blo 1796099 2695721 := bstep (se 2 (by rfl) ⟨1010895, by rfl⟩ : syracuseStep 2695721 = 2021791) B2021791
theorem B46703233 : Blo 1796099 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B2695817 : Blo 1796099 2695817 := bstep (se 2 (by rfl) ⟨1010931, by rfl⟩ : syracuseStep 2695817 = 2021863) B2021863
theorem B2917031 : Blo 1796099 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B2696027 : Blo 1796099 2696027 := bstep (se 1 (by rfl) ⟨2022020, by rfl⟩ : syracuseStep 2696027 = 4044041) B4044041
theorem B3031931 : Blo 1796099 3031931 := bstep (se 1 (by rfl) ⟨2273948, by rfl⟩ : syracuseStep 3031931 = 4547897) B4547897
theorem B2696063 : Blo 1796099 2696063 := bstep (se 1 (by rfl) ⟨2022047, by rfl⟩ : syracuseStep 2696063 = 4044095) B4044095
theorem B2696135 : Blo 1796099 2696135 := bstep (se 1 (by rfl) ⟨2022101, by rfl⟩ : syracuseStep 2696135 = 4044203) B4044203
theorem B2696351 : Blo 1796099 2696351 := bstep (se 1 (by rfl) ⟨2022263, by rfl⟩ : syracuseStep 2696351 = 4044527) B4044527
theorem B2696495 : Blo 1796099 2696495 := bstep (se 1 (by rfl) ⟨2022371, by rfl⟩ : syracuseStep 2696495 = 4044743) B4044743
theorem B2696687 : Blo 1796099 2696687 := bstep (se 1 (by rfl) ⟨2022515, by rfl⟩ : syracuseStep 2696687 = 4045031) B4045031
theorem B2696699 : Blo 1796099 2696699 := bstep (se 1 (by rfl) ⟨2022524, by rfl⟩ : syracuseStep 2696699 = 4045049) B4045049
theorem B2696735 : Blo 1796099 2696735 := bstep (se 1 (by rfl) ⟨2022551, by rfl⟩ : syracuseStep 2696735 = 4045103) B4045103
theorem B58304123 : Blo 1796099 58304123 := bstep (se 1 (by rfl) ⟨43728092, by rfl⟩ : syracuseStep 58304123 = 87456185) B87456185
theorem B2696879 : Blo 1796099 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B2696969 : Blo 1796099 2696969 := bstep (se 2 (by rfl) ⟨1011363, by rfl⟩ : syracuseStep 2696969 = 2022727) B2022727
theorem B2696999 : Blo 1796099 2696999 := bstep (se 1 (by rfl) ⟨2022749, by rfl⟩ : syracuseStep 2696999 = 4045499) B4045499
theorem B4548575 : Blo 1796099 4548575 := bstep (se 1 (by rfl) ⟨3411431, by rfl⟩ : syracuseStep 4548575 = 6822863) B6822863
theorem B3409913 : Blo 1796099 3409913 := bstep (se 2 (by rfl) ⟨1278717, by rfl⟩ : syracuseStep 3409913 = 2557435) B2557435
theorem B2557993 : Blo 1796099 2557993 := bstep (se 2 (by rfl) ⟨959247, by rfl⟩ : syracuseStep 2557993 = 1918495) B1918495
theorem B41502905 : Blo 1796099 41502905 := bstep (se 2 (by rfl) ⟨15563589, by rfl⟩ : syracuseStep 41502905 = 31127179) B31127179
theorem B3410171 : Blo 1796099 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B1195919747 : Blo 1796099 1195919747 := bstep (se 1 (by rfl) ⟨896939810, by rfl⟩ : syracuseStep 1195919747 = 1793879621) B1793879621
theorem B1796583 : Blo 1796099 1796583 := bstep (se 1 (by rfl) ⟨1347437, by rfl⟩ : syracuseStep 1796583 = 2694875) B2694875
theorem B6064793 : Blo 1796099 6064793 := bstep (se 2 (by rfl) ⟨2274297, by rfl⟩ : syracuseStep 6064793 = 4548595) B4548595
theorem B1796763 : Blo 1796099 1796763 := bstep (se 1 (by rfl) ⟨1347572, by rfl⟩ : syracuseStep 1796763 = 2695145) B2695145
theorem B6065063 : Blo 1796099 6065063 := bstep (se 1 (by rfl) ⟨4548797, by rfl⟩ : syracuseStep 6065063 = 9097595) B9097595
theorem B9096137 : Blo 1796099 9096137 := bstep (se 2 (by rfl) ⟨3411051, by rfl⟩ : syracuseStep 9096137 = 6822103) B6822103
theorem B23038951 : Blo 1796099 23038951 := bstep (se 1 (by rfl) ⟨17279213, by rfl⟩ : syracuseStep 23038951 = 34558427) B34558427
theorem B14568439 : Blo 1796099 14568439 := bstep (se 1 (by rfl) ⟨10926329, by rfl⟩ : syracuseStep 14568439 = 21852659) B21852659
theorem B4320265 : Blo 1796099 4320265 := bstep (se 2 (by rfl) ⟨1620099, by rfl⟩ : syracuseStep 4320265 = 3240199) B3240199
theorem B8309807 : Blo 1796099 8309807 := bstep (se 1 (by rfl) ⟨6232355, by rfl⟩ : syracuseStep 8309807 = 12464711) B12464711
theorem B4041791 : Blo 1796099 4041791 := bstep (se 1 (by rfl) ⟨3031343, by rfl⟩ : syracuseStep 4041791 = 6062687) B6062687
theorem B9096299 : Blo 1796099 9096299 := bstep (se 1 (by rfl) ⟨6822224, by rfl⟩ : syracuseStep 9096299 = 13644449) B13644449
theorem B1797231 : Blo 1796099 1797231 := bstep (se 1 (by rfl) ⟨1347923, by rfl⟩ : syracuseStep 1797231 = 2695847) B2695847
theorem B10235069 : Blo 1796099 10235069 := bstep (se 3 (by rfl) ⟨1919075, by rfl⟩ : syracuseStep 10235069 = 3838151) B3838151
theorem B1797311 : Blo 1796099 1797311 := bstep (se 1 (by rfl) ⟨1347983, by rfl⟩ : syracuseStep 1797311 = 2695967) B2695967
theorem B1797327 : Blo 1796099 1797327 := bstep (se 1 (by rfl) ⟨1347995, by rfl⟩ : syracuseStep 1797327 = 2695991) B2695991
theorem B13126867 : Blo 1796099 13126867 := bstep (se 1 (by rfl) ⟨9845150, by rfl⟩ : syracuseStep 13126867 = 19690301) B19690301
theorem B1797447 : Blo 1796099 1797447 := bstep (se 1 (by rfl) ⟨1348085, by rfl⟩ : syracuseStep 1797447 = 2696171) B2696171
theorem B5754203 : Blo 1796099 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B23080351 : Blo 1796099 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B4042619 : Blo 1796099 4042619 := bstep (se 1 (by rfl) ⟨3031964, by rfl⟩ : syracuseStep 4042619 = 6063929) B6063929
theorem B9097271 : Blo 1796099 9097271 := bstep (se 1 (by rfl) ⟨6822953, by rfl⟩ : syracuseStep 9097271 = 13645907) B13645907
theorem B13643963 : Blo 1796099 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B4550863 : Blo 1796099 4550863 := bstep (se 1 (by rfl) ⟨3413147, by rfl⟩ : syracuseStep 4550863 = 6826295) B6826295
theorem B2273503 : Blo 1796099 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B23040287 : Blo 1796099 23040287 := bstep (se 1 (by rfl) ⟨17280215, by rfl⟩ : syracuseStep 23040287 = 34560431) B34560431
theorem B2593327 : Blo 1796099 2593327 := bstep (se 1 (by rfl) ⟨1944995, by rfl⟩ : syracuseStep 2593327 = 3889991) B3889991
theorem B73740901 : Blo 1796099 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B6066953 : Blo 1796099 6066953 := bstep (se 2 (by rfl) ⟨2275107, by rfl⟩ : syracuseStep 6066953 = 4550215) B4550215
theorem B5116783 : Blo 1796099 5116783 := bstep (se 1 (by rfl) ⟨3837587, by rfl⟩ : syracuseStep 5116783 = 7675175) B7675175
theorem B11514761 : Blo 1796099 11514761 := bstep (se 2 (by rfl) ⟨4318035, by rfl⟩ : syracuseStep 11514761 = 8636071) B8636071
theorem B49165217 : Blo 1796099 49165217 := bstep (se 2 (by rfl) ⟨18436956, by rfl⟩ : syracuseStep 49165217 = 36873913) B36873913
theorem B32789495 : Blo 1796099 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B10925065 : Blo 1796099 10925065 := bstep (se 2 (by rfl) ⟨4096899, by rfl⟩ : syracuseStep 10925065 = 8193799) B8193799
theorem B2733311 : Blo 1796099 2733311 := bstep (se 1 (by rfl) ⟨2049983, by rfl⟩ : syracuseStep 2733311 = 4099967) B4099967
theorem B11515223 : Blo 1796099 11515223 := bstep (se 1 (by rfl) ⟨8636417, by rfl⟩ : syracuseStep 11515223 = 17272835) B17272835
theorem B5756663 : Blo 1796099 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B4044563 : Blo 1796099 4044563 := bstep (se 1 (by rfl) ⟨3033422, by rfl⟩ : syracuseStep 4044563 = 6066845) B6066845
theorem B2275391 : Blo 1796099 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B5118025 : Blo 1796099 5118025 := bstep (se 2 (by rfl) ⟨1919259, by rfl⟩ : syracuseStep 5118025 = 3838519) B3838519
theorem B4044923 : Blo 1796099 4044923 := bstep (se 1 (by rfl) ⟨3033692, by rfl⟩ : syracuseStep 4044923 = 6067385) B6067385
theorem B2021503 : Blo 1796099 2021503 := bstep (se 1 (by rfl) ⟨1516127, by rfl⟩ : syracuseStep 2021503 = 3032255) B3032255
theorem B10238237 : Blo 1796099 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B147618125 : Blo 1796099 147618125 := bstep (se 3 (by rfl) ⟨27678398, by rfl⟩ : syracuseStep 147618125 = 55356797) B55356797
theorem B4045193 : Blo 1796099 4045193 := bstep (se 2 (by rfl) ⟨1516947, by rfl⟩ : syracuseStep 4045193 = 3033895) B3033895
theorem B5118491 : Blo 1796099 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B8632979 : Blo 1796099 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B2022079 : Blo 1796099 2022079 := bstep (se 1 (by rfl) ⟨1516559, by rfl⟩ : syracuseStep 2022079 = 3033119) B3033119
theorem B9100025 : Blo 1796099 9100025 := bstep (se 2 (by rfl) ⟨3412509, by rfl⟩ : syracuseStep 9100025 = 6825019) B6825019
theorem B39385889 : Blo 1796099 39385889 := bstep (se 2 (by rfl) ⟨14769708, by rfl⟩ : syracuseStep 39385889 = 29539417) B29539417
theorem B4045625 : Blo 1796099 4045625 := bstep (se 2 (by rfl) ⟨1517109, by rfl⟩ : syracuseStep 4045625 = 3034219) B3034219
theorem B4316267 : Blo 1796099 4316267 := bstep (se 1 (by rfl) ⟨3237200, by rfl⟩ : syracuseStep 4316267 = 6474401) B6474401
theorem B5758087 : Blo 1796099 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B11509073 : Blo 1796099 11509073 := bstep (se 2 (by rfl) ⟨4315902, by rfl⟩ : syracuseStep 11509073 = 8631805) B8631805
theorem B7290319 : Blo 1796099 7290319 := bstep (se 1 (by rfl) ⟨5467739, by rfl⟩ : syracuseStep 7290319 = 10935479) B10935479
theorem B5119483 : Blo 1796099 5119483 := bstep (se 1 (by rfl) ⟨3839612, by rfl⟩ : syracuseStep 5119483 = 7679225) B7679225
theorem B2694767 : Blo 1796099 2694767 := bstep (se 1 (by rfl) ⟨2021075, by rfl⟩ : syracuseStep 2694767 = 4042151) B4042151
theorem B2694887 : Blo 1796099 2694887 := bstep (se 1 (by rfl) ⟨2021165, by rfl⟩ : syracuseStep 2694887 = 4042331) B4042331
theorem B17276753 : Blo 1796099 17276753 := bstep (se 2 (by rfl) ⟨6478782, by rfl⟩ : syracuseStep 17276753 = 12957565) B12957565
theorem B2695163 : Blo 1796099 2695163 := bstep (se 1 (by rfl) ⟨2021372, by rfl⟩ : syracuseStep 2695163 = 4042745) B4042745
theorem B3031067 : Blo 1796099 3031067 := bstep (se 1 (by rfl) ⟨2273300, by rfl⟩ : syracuseStep 3031067 = 4546601) B4546601
theorem B3031087 : Blo 1796099 3031087 := bstep (se 1 (by rfl) ⟨2273315, by rfl⟩ : syracuseStep 3031087 = 4546631) B4546631
theorem B113688643 : Blo 1796099 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B6824033 : Blo 1796099 6824033 := bstep (se 2 (by rfl) ⟨2559012, by rfl⟩ : syracuseStep 6824033 = 5118025) B5118025
theorem B2695337 : Blo 1796099 2695337 := bstep (se 2 (by rfl) ⟨1010751, by rfl⟩ : syracuseStep 2695337 = 2021503) B2021503
theorem B6062255 : Blo 1796099 6062255 := bstep (se 1 (by rfl) ⟨4546691, by rfl⟩ : syracuseStep 6062255 = 9093383) B9093383
theorem B15360191 : Blo 1796099 15360191 := bstep (se 1 (by rfl) ⟨11520143, by rfl⟩ : syracuseStep 15360191 = 23040287) B23040287
theorem B3031303 : Blo 1796099 3031303 := bstep (se 1 (by rfl) ⟨2273477, by rfl⟩ : syracuseStep 3031303 = 4546955) B4546955
theorem B11510045 : Blo 1796099 11510045 := bstep (se 3 (by rfl) ⟨2158133, by rfl⟩ : syracuseStep 11510045 = 4316267) B4316267
theorem B3031337 : Blo 1796099 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B7676507 : Blo 1796099 7676507 := bstep (se 1 (by rfl) ⟨5757380, by rfl⟩ : syracuseStep 7676507 = 11514761) B11514761
theorem B32776811 : Blo 1796099 32776811 := bstep (se 1 (by rfl) ⟨24582608, by rfl⟩ : syracuseStep 32776811 = 49165217) B49165217
theorem B3457769 : Blo 1796099 3457769 := bstep (se 2 (by rfl) ⟨1296663, by rfl⟩ : syracuseStep 3457769 = 2593327) B2593327
theorem B98321201 : Blo 1796099 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B7676815 : Blo 1796099 7676815 := bstep (se 1 (by rfl) ⟨5757611, by rfl⟩ : syracuseStep 7676815 = 11515223) B11515223
theorem B2696105 : Blo 1796099 2696105 := bstep (se 2 (by rfl) ⟨1011039, by rfl⟩ : syracuseStep 2696105 = 2022079) B2022079
theorem B70009957 : Blo 1796099 70009957 := bstep (se 4 (by rfl) ⟨6563433, by rfl⟩ : syracuseStep 70009957 = 13126867) B13126867
theorem B2696375 : Blo 1796099 2696375 := bstep (se 1 (by rfl) ⟨2022281, by rfl⟩ : syracuseStep 2696375 = 4044563) B4044563
theorem B3032383 : Blo 1796099 3032383 := bstep (se 1 (by rfl) ⟨2274287, by rfl⟩ : syracuseStep 3032383 = 4548575) B4548575
theorem B19424585 : Blo 1796099 19424585 := bstep (se 2 (by rfl) ⟨7284219, by rfl⟩ : syracuseStep 19424585 = 14568439) B14568439
theorem B14566753 : Blo 1796099 14566753 := bstep (se 2 (by rfl) ⟨5462532, by rfl⟩ : syracuseStep 14566753 = 10925065) B10925065
theorem B5760353 : Blo 1796099 5760353 := bstep (se 2 (by rfl) ⟨2160132, by rfl⟩ : syracuseStep 5760353 = 4320265) B4320265
theorem B13649309 : Blo 1796099 13649309 := bstep (se 3 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 13649309 = 5118491) B5118491
theorem B2696615 : Blo 1796099 2696615 := bstep (se 1 (by rfl) ⟨2022461, by rfl⟩ : syracuseStep 2696615 = 4044923) B4044923
theorem B7677449 : Blo 1796099 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B6825491 : Blo 1796099 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B98412083 : Blo 1796099 98412083 := bstep (se 1 (by rfl) ⟨73809062, by rfl⟩ : syracuseStep 98412083 = 147618125) B147618125
theorem B797279831 : Blo 1796099 797279831 := bstep (se 1 (by rfl) ⟨597959873, by rfl⟩ : syracuseStep 797279831 = 1195919747) B1195919747
theorem B2696795 : Blo 1796099 2696795 := bstep (se 1 (by rfl) ⟨2022596, by rfl⟩ : syracuseStep 2696795 = 4045193) B4045193
theorem B26257259 : Blo 1796099 26257259 := bstep (se 1 (by rfl) ⟨19692944, by rfl⟩ : syracuseStep 26257259 = 39385889) B39385889
theorem B2697083 : Blo 1796099 2697083 := bstep (se 1 (by rfl) ⟨2022812, by rfl⟩ : syracuseStep 2697083 = 4045625) B4045625
theorem B6064091 : Blo 1796099 6064091 := bstep (se 1 (by rfl) ⟨4548068, by rfl⟩ : syracuseStep 6064091 = 9096137) B9096137
theorem B6825977 : Blo 1796099 6825977 := bstep (se 2 (by rfl) ⟨2559741, by rfl⟩ : syracuseStep 6825977 = 5119483) B5119483
theorem B5539871 : Blo 1796099 5539871 := bstep (se 1 (by rfl) ⟨4154903, by rfl⟩ : syracuseStep 5539871 = 8309807) B8309807
theorem B6064199 : Blo 1796099 6064199 := bstep (se 1 (by rfl) ⟨4548149, by rfl⟩ : syracuseStep 6064199 = 9096299) B9096299
theorem B3836135 : Blo 1796099 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B1796511 : Blo 1796099 1796511 := bstep (se 1 (by rfl) ⟨1347383, by rfl⟩ : syracuseStep 1796511 = 2694767) B2694767
theorem B1796591 : Blo 1796099 1796591 := bstep (se 1 (by rfl) ⟨1347443, by rfl⟩ : syracuseStep 1796591 = 2694887) B2694887
theorem B1796775 : Blo 1796099 1796775 := bstep (se 1 (by rfl) ⟨1347581, by rfl⟩ : syracuseStep 1796775 = 2695163) B2695163
theorem B1796815 : Blo 1796099 1796815 := bstep (se 1 (by rfl) ⟨1347611, by rfl⟩ : syracuseStep 1796815 = 2695223) B2695223
theorem B6064847 : Blo 1796099 6064847 := bstep (se 1 (by rfl) ⟨4548635, by rfl⟩ : syracuseStep 6064847 = 9097271) B9097271
theorem B3410657 : Blo 1796099 3410657 := bstep (se 2 (by rfl) ⟨1278996, by rfl⟩ : syracuseStep 3410657 = 2557993) B2557993
theorem B1796895 : Blo 1796099 1796895 := bstep (se 1 (by rfl) ⟨1347671, by rfl⟩ : syracuseStep 1796895 = 2695343) B2695343
theorem B9095975 : Blo 1796099 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B1797031 : Blo 1796099 1797031 := bstep (se 1 (by rfl) ⟨1347773, by rfl⟩ : syracuseStep 1797031 = 2695547) B2695547
theorem B1797147 : Blo 1796099 1797147 := bstep (se 1 (by rfl) ⟨1347860, by rfl⟩ : syracuseStep 1797147 = 2695721) B2695721
theorem B1797211 : Blo 1796099 1797211 := bstep (se 1 (by rfl) ⟨1347908, by rfl⟩ : syracuseStep 1797211 = 2695817) B2695817
theorem B1797351 : Blo 1796099 1797351 := bstep (se 1 (by rfl) ⟨1348013, by rfl⟩ : syracuseStep 1797351 = 2696027) B2696027
theorem B1797375 : Blo 1796099 1797375 := bstep (se 1 (by rfl) ⟨1348031, by rfl⟩ : syracuseStep 1797375 = 2696063) B2696063
theorem B4042025 : Blo 1796099 4042025 := bstep (se 2 (by rfl) ⟨1515759, by rfl⟩ : syracuseStep 4042025 = 3031519) B3031519
theorem B1797423 : Blo 1796099 1797423 := bstep (se 1 (by rfl) ⟨1348067, by rfl⟩ : syracuseStep 1797423 = 2696135) B2696135
theorem B1797567 : Blo 1796099 1797567 := bstep (se 1 (by rfl) ⟨1348175, by rfl⟩ : syracuseStep 1797567 = 2696351) B2696351
theorem B1822207 : Blo 1796099 1822207 := bstep (se 1 (by rfl) ⟨1366655, by rfl⟩ : syracuseStep 1822207 = 2733311) B2733311
theorem B1797663 : Blo 1796099 1797663 := bstep (se 1 (by rfl) ⟨1348247, by rfl⟩ : syracuseStep 1797663 = 2696495) B2696495
theorem B1797791 : Blo 1796099 1797791 := bstep (se 1 (by rfl) ⟨1348343, by rfl⟩ : syracuseStep 1797791 = 2696687) B2696687
theorem B1797799 : Blo 1796099 1797799 := bstep (se 1 (by rfl) ⟨1348349, by rfl⟩ : syracuseStep 1797799 = 2696699) B2696699
theorem B1797823 : Blo 1796099 1797823 := bstep (se 1 (by rfl) ⟨1348367, by rfl⟩ : syracuseStep 1797823 = 2696735) B2696735
theorem B1797919 : Blo 1796099 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B3837775 : Blo 1796099 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B1797979 : Blo 1796099 1797979 := bstep (se 1 (by rfl) ⟨1348484, by rfl⟩ : syracuseStep 1797979 = 2696969) B2696969
theorem B1797999 : Blo 1796099 1797999 := bstep (se 1 (by rfl) ⟨1348499, by rfl⟩ : syracuseStep 1797999 = 2696999) B2696999
theorem B2273275 : Blo 1796099 2273275 := bstep (se 1 (by rfl) ⟨1704956, by rfl⟩ : syracuseStep 2273275 = 3409913) B3409913
theorem B27668603 : Blo 1796099 27668603 := bstep (se 1 (by rfl) ⟨20751452, by rfl⟩ : syracuseStep 27668603 = 41502905) B41502905
theorem B2273447 : Blo 1796099 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B5755319 : Blo 1796099 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B4043195 : Blo 1796099 4043195 := bstep (se 1 (by rfl) ⟨3032396, by rfl⟩ : syracuseStep 4043195 = 6064793) B6064793
theorem B7778749 : Blo 1796099 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B6066683 : Blo 1796099 6066683 := bstep (se 1 (by rfl) ⟨4550012, by rfl⟩ : syracuseStep 6066683 = 9100025) B9100025
theorem B30773801 : Blo 1796099 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B9720425 : Blo 1796099 9720425 := bstep (se 2 (by rfl) ⟨3645159, by rfl⟩ : syracuseStep 9720425 = 7290319) B7290319
theorem B4043375 : Blo 1796099 4043375 := bstep (se 1 (by rfl) ⟨3032531, by rfl⟩ : syracuseStep 4043375 = 6065063) B6065063
theorem B7672715 : Blo 1796099 7672715 := bstep (se 1 (by rfl) ⟨5754536, by rfl⟩ : syracuseStep 7672715 = 11509073) B11509073
theorem B87438653 : Blo 1796099 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B6067709 : Blo 1796099 6067709 := bstep (se 3 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 6067709 = 2275391) B2275391
theorem B3642907 : Blo 1796099 3642907 := bstep (se 1 (by rfl) ⟨2732180, by rfl⟩ : syracuseStep 3642907 = 5464361) B5464361
theorem B6067817 : Blo 1796099 6067817 := bstep (se 2 (by rfl) ⟨2275431, by rfl⟩ : syracuseStep 6067817 = 4550863) B4550863
theorem B6477545 : Blo 1796099 6477545 := bstep (se 2 (by rfl) ⟨2429079, by rfl⟩ : syracuseStep 6477545 = 4858159) B4858159
theorem B4044635 : Blo 1796099 4044635 := bstep (se 1 (by rfl) ⟨3033476, by rfl⟩ : syracuseStep 4044635 = 6066953) B6066953
theorem B2021287 : Blo 1796099 2021287 := bstep (se 1 (by rfl) ⟨1515965, by rfl⟩ : syracuseStep 2021287 = 3031931) B3031931
theorem B249083909 : Blo 1796099 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B38869415 : Blo 1796099 38869415 := bstep (se 1 (by rfl) ⟨29152061, by rfl⟩ : syracuseStep 38869415 = 58304123) B58304123
theorem B6822377 : Blo 1796099 6822377 := bstep (se 2 (by rfl) ⟨2558391, by rfl⟩ : syracuseStep 6822377 = 5116783) B5116783
theorem B30718601 : Blo 1796099 30718601 := bstep (se 2 (by rfl) ⟨11519475, by rfl⟩ : syracuseStep 30718601 = 23038951) B23038951
theorem B2694527 : Blo 1796099 2694527 := bstep (se 1 (by rfl) ⟨2020895, by rfl⟩ : syracuseStep 2694527 = 4041791) B4041791
theorem B6823379 : Blo 1796099 6823379 := bstep (se 1 (by rfl) ⟨5117534, by rfl⟩ : syracuseStep 6823379 = 10235069) B10235069
theorem B46071341 : Blo 1796099 46071341 := bstep (se 3 (by rfl) ⟨8638376, by rfl⟩ : syracuseStep 46071341 = 17276753) B17276753
theorem B2695079 : Blo 1796099 2695079 := bstep (se 1 (by rfl) ⟨2021309, by rfl⟩ : syracuseStep 2695079 = 4042619) B4042619
theorem B151584857 : Blo 1796099 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B10240127 : Blo 1796099 10240127 := bstep (se 1 (by rfl) ⟨7680095, by rfl⟩ : syracuseStep 10240127 = 15360191) B15360191
theorem B2695463 : Blo 1796099 2695463 := bstep (se 1 (by rfl) ⟨2021597, by rfl⟩ : syracuseStep 2695463 = 4043195) B4043195
theorem B6480283 : Blo 1796099 6480283 := bstep (se 1 (by rfl) ⟨4860212, by rfl⟩ : syracuseStep 6480283 = 9720425) B9720425
theorem B2695583 : Blo 1796099 2695583 := bstep (se 1 (by rfl) ⟨2021687, by rfl⟩ : syracuseStep 2695583 = 4043375) B4043375
theorem B6062525 : Blo 1796099 6062525 := bstep (se 3 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 6062525 = 2273447) B2273447
theorem B10371665 : Blo 1796099 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B15360941 : Blo 1796099 15360941 := bstep (se 3 (by rfl) ⟨2880176, by rfl⟩ : syracuseStep 15360941 = 5760353) B5760353
theorem B4318363 : Blo 1796099 4318363 := bstep (se 1 (by rfl) ⟨3238772, by rfl⟩ : syracuseStep 4318363 = 6477545) B6477545
theorem B2696423 : Blo 1796099 2696423 := bstep (se 1 (by rfl) ⟨2022317, by rfl⟩ : syracuseStep 2696423 = 4044635) B4044635
theorem B2557423 : Blo 1796099 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B25912943 : Blo 1796099 25912943 := bstep (se 1 (by rfl) ⟨19434707, by rfl⟩ : syracuseStep 25912943 = 38869415) B38869415
theorem B4548251 : Blo 1796099 4548251 := bstep (se 1 (by rfl) ⟨3411188, by rfl⟩ : syracuseStep 4548251 = 6822377) B6822377
theorem B6063983 : Blo 1796099 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B1796351 : Blo 1796099 1796351 := bstep (se 1 (by rfl) ⟨1347263, by rfl⟩ : syracuseStep 1796351 = 2694527) B2694527
theorem B4548919 : Blo 1796099 4548919 := bstep (se 1 (by rfl) ⟨3411689, by rfl⟩ : syracuseStep 4548919 = 6823379) B6823379
theorem B30714227 : Blo 1796099 30714227 := bstep (se 1 (by rfl) ⟨23035670, by rfl⟩ : syracuseStep 30714227 = 46071341) B46071341
theorem B1796719 : Blo 1796099 1796719 := bstep (se 1 (by rfl) ⟨1347539, by rfl⟩ : syracuseStep 1796719 = 2695079) B2695079
theorem B4041449 : Blo 1796099 4041449 := bstep (se 2 (by rfl) ⟨1515543, by rfl⟩ : syracuseStep 4041449 = 3031087) B3031087
theorem B4549355 : Blo 1796099 4549355 := bstep (se 1 (by rfl) ⟨3412016, by rfl⟩ : syracuseStep 4549355 = 6824033) B6824033
theorem B14772989 : Blo 1796099 14772989 := bstep (se 3 (by rfl) ⟨2769935, by rfl⟩ : syracuseStep 14772989 = 5539871) B5539871
theorem B1796891 : Blo 1796099 1796891 := bstep (se 1 (by rfl) ⟨1347668, by rfl⟩ : syracuseStep 1796891 = 2695337) B2695337
theorem B4041503 : Blo 1796099 4041503 := bstep (se 1 (by rfl) ⟨3031127, by rfl⟩ : syracuseStep 4041503 = 6062255) B6062255
theorem B3836879 : Blo 1796099 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B4041737 : Blo 1796099 4041737 := bstep (se 2 (by rfl) ⟨1515651, by rfl⟩ : syracuseStep 4041737 = 3031303) B3031303
theorem B21851207 : Blo 1796099 21851207 := bstep (se 1 (by rfl) ⟨16388405, by rfl⟩ : syracuseStep 21851207 = 32776811) B32776811
theorem B65547467 : Blo 1796099 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B5115143 : Blo 1796099 5115143 := bstep (se 1 (by rfl) ⟨3836357, by rfl⟩ : syracuseStep 5115143 = 7672715) B7672715
theorem B1797403 : Blo 1796099 1797403 := bstep (se 1 (by rfl) ⟨1348052, by rfl⟩ : syracuseStep 1797403 = 2696105) B2696105
theorem B1797583 : Blo 1796099 1797583 := bstep (se 1 (by rfl) ⟨1348187, by rfl⟩ : syracuseStep 1797583 = 2696375) B2696375
theorem B1797743 : Blo 1796099 1797743 := bstep (se 1 (by rfl) ⟨1348307, by rfl⟩ : syracuseStep 1797743 = 2696615) B2696615
theorem B4550327 : Blo 1796099 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B1797863 : Blo 1796099 1797863 := bstep (se 1 (by rfl) ⟨1348397, by rfl⟩ : syracuseStep 1797863 = 2696795) B2696795
theorem B10235753 : Blo 1796099 10235753 := bstep (se 2 (by rfl) ⟨3838407, by rfl⟩ : syracuseStep 10235753 = 7676815) B7676815
theorem B1798055 : Blo 1796099 1798055 := bstep (se 1 (by rfl) ⟨1348541, by rfl⟩ : syracuseStep 1798055 = 2697083) B2697083
theorem B4042727 : Blo 1796099 4042727 := bstep (se 1 (by rfl) ⟨3032045, by rfl⟩ : syracuseStep 4042727 = 6064091) B6064091
theorem B4550651 : Blo 1796099 4550651 := bstep (se 1 (by rfl) ⟨3412988, by rfl⟩ : syracuseStep 4550651 = 6825977) B6825977
theorem B166055939 : Blo 1796099 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B4042799 : Blo 1796099 4042799 := bstep (se 1 (by rfl) ⟨3032099, by rfl⟩ : syracuseStep 4042799 = 6064199) B6064199
theorem B82063469 : Blo 1796099 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B4043177 : Blo 1796099 4043177 := bstep (se 2 (by rfl) ⟨1516191, by rfl⟩ : syracuseStep 4043177 = 3032383) B3032383
theorem B4043231 : Blo 1796099 4043231 := bstep (se 1 (by rfl) ⟨3032423, by rfl⟩ : syracuseStep 4043231 = 6064847) B6064847
theorem B2273771 : Blo 1796099 2273771 := bstep (se 1 (by rfl) ⟨1705328, by rfl⟩ : syracuseStep 2273771 = 3410657) B3410657
theorem B9220717 : Blo 1796099 9220717 := bstep (se 3 (by rfl) ⟨1728884, by rfl⟩ : syracuseStep 9220717 = 3457769) B3457769
theorem B2429609 : Blo 1796099 2429609 := bstep (se 2 (by rfl) ⟨911103, by rfl⟩ : syracuseStep 2429609 = 1822207) B1822207
theorem B5117033 : Blo 1796099 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B2020711 : Blo 1796099 2020711 := bstep (se 1 (by rfl) ⟨1515533, by rfl⟩ : syracuseStep 2020711 = 3031067) B3031067
theorem B18445735 : Blo 1796099 18445735 := bstep (se 1 (by rfl) ⟨13834301, by rfl⟩ : syracuseStep 18445735 = 27668603) B27668603
theorem B7673363 : Blo 1796099 7673363 := bstep (se 1 (by rfl) ⟨5755022, by rfl⟩ : syracuseStep 7673363 = 11510045) B11510045
theorem B2020891 : Blo 1796099 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B4044455 : Blo 1796099 4044455 := bstep (se 1 (by rfl) ⟨3033341, by rfl⟩ : syracuseStep 4044455 = 6066683) B6066683
theorem B5117671 : Blo 1796099 5117671 := bstep (se 1 (by rfl) ⟨3838253, by rfl⟩ : syracuseStep 5117671 = 7676507) B7676507
theorem B58292435 : Blo 1796099 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B12949723 : Blo 1796099 12949723 := bstep (se 1 (by rfl) ⟨9712292, by rfl⟩ : syracuseStep 12949723 = 19424585) B19424585
theorem B9099539 : Blo 1796099 9099539 := bstep (se 1 (by rfl) ⟨6824654, by rfl⟩ : syracuseStep 9099539 = 13649309) B13649309
theorem B4045139 : Blo 1796099 4045139 := bstep (se 1 (by rfl) ⟨3033854, by rfl⟩ : syracuseStep 4045139 = 6067709) B6067709
theorem B5118299 : Blo 1796099 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B65608055 : Blo 1796099 65608055 := bstep (se 1 (by rfl) ⟨49206041, by rfl⟩ : syracuseStep 65608055 = 98412083) B98412083
theorem B531519887 : Blo 1796099 531519887 := bstep (se 1 (by rfl) ⟨398639915, by rfl⟩ : syracuseStep 531519887 = 797279831) B797279831
theorem B4045211 : Blo 1796099 4045211 := bstep (se 1 (by rfl) ⟨3033908, by rfl⟩ : syracuseStep 4045211 = 6067817) B6067817
theorem B17504839 : Blo 1796099 17504839 := bstep (se 1 (by rfl) ⟨13128629, by rfl⟩ : syracuseStep 17504839 = 26257259) B26257259
theorem B93346609 : Blo 1796099 93346609 := bstep (se 2 (by rfl) ⟨35004978, by rfl⟩ : syracuseStep 93346609 = 70009957) B70009957
theorem B20479067 : Blo 1796099 20479067 := bstep (se 1 (by rfl) ⟨15359300, by rfl⟩ : syracuseStep 20479067 = 30718601) B30718601
theorem B19422337 : Blo 1796099 19422337 := bstep (se 2 (by rfl) ⟨7283376, by rfl⟩ : syracuseStep 19422337 = 14566753) B14566753
theorem B4857209 : Blo 1796099 4857209 := bstep (se 2 (by rfl) ⟨1821453, by rfl⟩ : syracuseStep 4857209 = 3642907) B3642907
theorem B2694683 : Blo 1796099 2694683 := bstep (se 1 (by rfl) ⟨2021012, by rfl⟩ : syracuseStep 2694683 = 4042025) B4042025
theorem B2695049 : Blo 1796099 2695049 := bstep (se 2 (by rfl) ⟨1010643, by rfl⟩ : syracuseStep 2695049 = 2021287) B2021287
theorem B3031033 : Blo 1796099 3031033 := bstep (se 2 (by rfl) ⟨1136637, by rfl⟩ : syracuseStep 3031033 = 2273275) B2273275
theorem B2695199 : Blo 1796099 2695199 := bstep (se 1 (by rfl) ⟨2021399, by rfl⟩ : syracuseStep 2695199 = 4042799) B4042799
theorem B101056571 : Blo 1796099 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B2695451 : Blo 1796099 2695451 := bstep (se 1 (by rfl) ⟨2021588, by rfl⟩ : syracuseStep 2695451 = 4043177) B4043177
theorem B2695487 : Blo 1796099 2695487 := bstep (se 1 (by rfl) ⟨2021615, by rfl⟩ : syracuseStep 2695487 = 4043231) B4043231
theorem B6914443 : Blo 1796099 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B10240627 : Blo 1796099 10240627 := bstep (se 1 (by rfl) ⟨7680470, by rfl⟩ : syracuseStep 10240627 = 15360941) B15360941
theorem B23339785 : Blo 1796099 23339785 := bstep (se 2 (by rfl) ⟨8752419, by rfl⟩ : syracuseStep 23339785 = 17504839) B17504839
theorem B124462145 : Blo 1796099 124462145 := bstep (se 2 (by rfl) ⟨46673304, by rfl⟩ : syracuseStep 124462145 = 93346609) B93346609
theorem B3032167 : Blo 1796099 3032167 := bstep (se 1 (by rfl) ⟨2274125, by rfl⟩ : syracuseStep 3032167 = 4548251) B4548251
theorem B2696303 : Blo 1796099 2696303 := bstep (se 1 (by rfl) ⟨2022227, by rfl⟩ : syracuseStep 2696303 = 4044455) B4044455
theorem B6063389 : Blo 1796099 6063389 := bstep (se 3 (by rfl) ⟨1136885, by rfl⟩ : syracuseStep 6063389 = 2273771) B2273771
theorem B25896449 : Blo 1796099 25896449 := bstep (se 2 (by rfl) ⟨9711168, by rfl⟩ : syracuseStep 25896449 = 19422337) B19422337
theorem B2696759 : Blo 1796099 2696759 := bstep (se 1 (by rfl) ⟨2022569, by rfl⟩ : syracuseStep 2696759 = 4045139) B4045139
theorem B43738703 : Blo 1796099 43738703 := bstep (se 1 (by rfl) ⟨32804027, by rfl⟩ : syracuseStep 43738703 = 65608055) B65608055
theorem B354346591 : Blo 1796099 354346591 := bstep (se 1 (by rfl) ⟨265759943, by rfl⟩ : syracuseStep 354346591 = 531519887) B531519887
theorem B2696807 : Blo 1796099 2696807 := bstep (se 1 (by rfl) ⟨2022605, by rfl⟩ : syracuseStep 2696807 = 4045211) B4045211
theorem B3032903 : Blo 1796099 3032903 := bstep (se 1 (by rfl) ⟨2274677, by rfl⟩ : syracuseStep 3032903 = 4549355) B4549355
theorem B2557919 : Blo 1796099 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B14567471 : Blo 1796099 14567471 := bstep (se 1 (by rfl) ⟨10925603, by rfl⟩ : syracuseStep 14567471 = 21851207) B21851207
theorem B43698311 : Blo 1796099 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B3410095 : Blo 1796099 3410095 := bstep (se 1 (by rfl) ⟨2557571, by rfl⟩ : syracuseStep 3410095 = 5115143) B5115143
theorem B3238139 : Blo 1796099 3238139 := bstep (se 1 (by rfl) ⟨2428604, by rfl⟩ : syracuseStep 3238139 = 4857209) B4857209
theorem B1796455 : Blo 1796099 1796455 := bstep (se 1 (by rfl) ⟨1347341, by rfl⟩ : syracuseStep 1796455 = 2694683) B2694683
theorem B3033551 : Blo 1796099 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B1796699 : Blo 1796099 1796699 := bstep (se 1 (by rfl) ⟨1347524, by rfl⟩ : syracuseStep 1796699 = 2695049) B2695049
theorem B4041377 : Blo 1796099 4041377 := bstep (se 2 (by rfl) ⟨1515516, by rfl⟩ : syracuseStep 4041377 = 3031033) B3031033
theorem B3033767 : Blo 1796099 3033767 := bstep (se 1 (by rfl) ⟨2275325, by rfl⟩ : syracuseStep 3033767 = 4550651) B4550651
theorem B54708979 : Blo 1796099 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B6826751 : Blo 1796099 6826751 := bstep (se 1 (by rfl) ⟨5120063, by rfl⟩ : syracuseStep 6826751 = 10240127) B10240127
theorem B1796975 : Blo 1796099 1796975 := bstep (se 1 (by rfl) ⟨1347731, by rfl⟩ : syracuseStep 1796975 = 2695463) B2695463
theorem B1797055 : Blo 1796099 1797055 := bstep (se 1 (by rfl) ⟨1347791, by rfl⟩ : syracuseStep 1797055 = 2695583) B2695583
theorem B4041683 : Blo 1796099 4041683 := bstep (se 1 (by rfl) ⟨3031262, by rfl⟩ : syracuseStep 4041683 = 6062525) B6062525
theorem B6065225 : Blo 1796099 6065225 := bstep (se 2 (by rfl) ⟨2274459, by rfl⟩ : syracuseStep 6065225 = 4548919) B4548919
theorem B1797615 : Blo 1796099 1797615 := bstep (se 1 (by rfl) ⟨1348211, by rfl⟩ : syracuseStep 1797615 = 2696423) B2696423
theorem B5115575 : Blo 1796099 5115575 := bstep (se 1 (by rfl) ⟨3836681, by rfl⟩ : syracuseStep 5115575 = 7673363) B7673363
theorem B4042655 : Blo 1796099 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B6066359 : Blo 1796099 6066359 := bstep (se 1 (by rfl) ⟨4549769, by rfl⟩ : syracuseStep 6066359 = 9099539) B9099539
theorem B3412199 : Blo 1796099 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B20476151 : Blo 1796099 20476151 := bstep (se 1 (by rfl) ⟨15357113, by rfl⟩ : syracuseStep 20476151 = 30714227) B30714227
theorem B13652711 : Blo 1796099 13652711 := bstep (se 1 (by rfl) ⟨10239533, by rfl⟩ : syracuseStep 13652711 = 20479067) B20479067
theorem B110703959 : Blo 1796099 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B13645421 : Blo 1796099 13645421 := bstep (se 3 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 13645421 = 5117033) B5117033
theorem B17266297 : Blo 1796099 17266297 := bstep (se 2 (by rfl) ⟨6474861, by rfl⟩ : syracuseStep 17266297 = 12949723) B12949723
theorem B8640377 : Blo 1796099 8640377 := bstep (se 2 (by rfl) ⟨3240141, by rfl⟩ : syracuseStep 8640377 = 6480283) B6480283
theorem B12294289 : Blo 1796099 12294289 := bstep (se 2 (by rfl) ⟨4610358, by rfl⟩ : syracuseStep 12294289 = 9220717) B9220717
theorem B17275295 : Blo 1796099 17275295 := bstep (se 1 (by rfl) ⟨12956471, by rfl⟩ : syracuseStep 17275295 = 25912943) B25912943
theorem B38861623 : Blo 1796099 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B5757817 : Blo 1796099 5757817 := bstep (se 2 (by rfl) ⟨2159181, by rfl⟩ : syracuseStep 5757817 = 4318363) B4318363
theorem B6478957 : Blo 1796099 6478957 := bstep (se 3 (by rfl) ⟨1214804, by rfl⟩ : syracuseStep 6478957 = 2429609) B2429609
theorem B2694281 : Blo 1796099 2694281 := bstep (se 2 (by rfl) ⟨1010355, by rfl⟩ : syracuseStep 2694281 = 2020711) B2020711
theorem B2694299 : Blo 1796099 2694299 := bstep (se 1 (by rfl) ⟨2020724, by rfl⟩ : syracuseStep 2694299 = 4041449) B4041449
theorem B2694335 : Blo 1796099 2694335 := bstep (se 1 (by rfl) ⟨2020751, by rfl⟩ : syracuseStep 2694335 = 4041503) B4041503
theorem B39394637 : Blo 1796099 39394637 := bstep (se 3 (by rfl) ⟨7386494, by rfl⟩ : syracuseStep 39394637 = 14772989) B14772989
theorem B2694491 : Blo 1796099 2694491 := bstep (se 1 (by rfl) ⟨2020868, by rfl⟩ : syracuseStep 2694491 = 4041737) B4041737
theorem B2694521 : Blo 1796099 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B98377253 : Blo 1796099 98377253 := bstep (se 4 (by rfl) ⟨9222867, by rfl⟩ : syracuseStep 98377253 = 18445735) B18445735
theorem B6823561 : Blo 1796099 6823561 := bstep (se 2 (by rfl) ⟨2558835, by rfl⟩ : syracuseStep 6823561 = 5117671) B5117671
theorem B6823835 : Blo 1796099 6823835 := bstep (se 1 (by rfl) ⟨5117876, by rfl⟩ : syracuseStep 6823835 = 10235753) B10235753
theorem B13639589 : Blo 1796099 13639589 := bstep (se 4 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 13639589 = 2557423) B2557423
theorem B2695151 : Blo 1796099 2695151 := bstep (se 1 (by rfl) ⟨2021363, by rfl⟩ : syracuseStep 2695151 = 4042727) B4042727
theorem B67371047 : Blo 1796099 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B16392385 : Blo 1796099 16392385 := bstep (se 2 (by rfl) ⟨6147144, by rfl⟩ : syracuseStep 16392385 = 12294289) B12294289
theorem B4546793 : Blo 1796099 4546793 := bstep (se 2 (by rfl) ⟨1705047, by rfl⟩ : syracuseStep 4546793 = 3410095) B3410095
theorem B9101807 : Blo 1796099 9101807 := bstep (se 1 (by rfl) ⟨6826355, by rfl⟩ : syracuseStep 9101807 = 13652711) B13652711
theorem B73802639 : Blo 1796099 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B51815497 : Blo 1796099 51815497 := bstep (se 2 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 51815497 = 38861623) B38861623
theorem B7677089 : Blo 1796099 7677089 := bstep (se 2 (by rfl) ⟨2878908, by rfl⟩ : syracuseStep 7677089 = 5757817) B5757817
theorem B5760251 : Blo 1796099 5760251 := bstep (se 1 (by rfl) ⟨4320188, by rfl⟩ : syracuseStep 5760251 = 8640377) B8640377
theorem B29132207 : Blo 1796099 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B13641533 : Blo 1796099 13641533 := bstep (se 3 (by rfl) ⟨2557787, by rfl⟩ : syracuseStep 13641533 = 5115575) B5115575
theorem B1796187 : Blo 1796099 1796187 := bstep (se 1 (by rfl) ⟨1347140, by rfl⟩ : syracuseStep 1796187 = 2694281) B2694281
theorem B1796199 : Blo 1796099 1796199 := bstep (se 1 (by rfl) ⟨1347149, by rfl⟩ : syracuseStep 1796199 = 2694299) B2694299
theorem B1796223 : Blo 1796099 1796223 := bstep (se 1 (by rfl) ⟨1347167, by rfl⟩ : syracuseStep 1796223 = 2694335) B2694335
theorem B23021729 : Blo 1796099 23021729 := bstep (se 2 (by rfl) ⟨8633148, by rfl⟩ : syracuseStep 23021729 = 17266297) B17266297
theorem B1796327 : Blo 1796099 1796327 := bstep (se 1 (by rfl) ⟨1347245, by rfl⟩ : syracuseStep 1796327 = 2694491) B2694491
theorem B1796347 : Blo 1796099 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B4549223 : Blo 1796099 4549223 := bstep (se 1 (by rfl) ⟨3411917, by rfl⟩ : syracuseStep 4549223 = 6823835) B6823835
theorem B1796767 : Blo 1796099 1796767 := bstep (se 1 (by rfl) ⟨1347575, by rfl⟩ : syracuseStep 1796767 = 2695151) B2695151
theorem B1796799 : Blo 1796099 1796799 := bstep (se 1 (by rfl) ⟨1347599, by rfl⟩ : syracuseStep 1796799 = 2695199) B2695199
theorem B13650767 : Blo 1796099 13650767 := bstep (se 1 (by rfl) ⟨10238075, by rfl⟩ : syracuseStep 13650767 = 20476151) B20476151
theorem B1796967 : Blo 1796099 1796967 := bstep (se 1 (by rfl) ⟨1347725, by rfl⟩ : syracuseStep 1796967 = 2695451) B2695451
theorem B1796991 : Blo 1796099 1796991 := bstep (se 1 (by rfl) ⟨1347743, by rfl⟩ : syracuseStep 1796991 = 2695487) B2695487
theorem B9219257 : Blo 1796099 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B1797535 : Blo 1796099 1797535 := bstep (se 1 (by rfl) ⟨1348151, by rfl⟩ : syracuseStep 1797535 = 2696303) B2696303
theorem B4042259 : Blo 1796099 4042259 := bstep (se 1 (by rfl) ⟨3031694, by rfl⟩ : syracuseStep 4042259 = 6063389) B6063389
theorem B72945305 : Blo 1796099 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B17264299 : Blo 1796099 17264299 := bstep (se 1 (by rfl) ⟨12948224, by rfl⟩ : syracuseStep 17264299 = 25896449) B25896449
theorem B1797839 : Blo 1796099 1797839 := bstep (se 1 (by rfl) ⟨1348379, by rfl⟩ : syracuseStep 1797839 = 2696759) B2696759
theorem B29159135 : Blo 1796099 29159135 := bstep (se 1 (by rfl) ⟨21869351, by rfl⟩ : syracuseStep 29159135 = 43738703) B43738703
theorem B1797871 : Blo 1796099 1797871 := bstep (se 1 (by rfl) ⟨1348403, by rfl⟩ : syracuseStep 1797871 = 2696807) B2696807
theorem B9096947 : Blo 1796099 9096947 := bstep (se 1 (by rfl) ⟨6822710, by rfl⟩ : syracuseStep 9096947 = 13645421) B13645421
theorem B9711647 : Blo 1796099 9711647 := bstep (se 1 (by rfl) ⟨7283735, by rfl⟩ : syracuseStep 9711647 = 14567471) B14567471
theorem B4042889 : Blo 1796099 4042889 := bstep (se 2 (by rfl) ⟨1516083, by rfl⟩ : syracuseStep 4042889 = 3032167) B3032167
theorem B8638609 : Blo 1796099 8638609 := bstep (se 2 (by rfl) ⟨3239478, by rfl⟩ : syracuseStep 8638609 = 6478957) B6478957
theorem B2158759 : Blo 1796099 2158759 := bstep (se 1 (by rfl) ⟨1619069, by rfl⟩ : syracuseStep 2158759 = 3238139) B3238139
theorem B4551167 : Blo 1796099 4551167 := bstep (se 1 (by rfl) ⟨3413375, by rfl⟩ : syracuseStep 4551167 = 6826751) B6826751
theorem B4043483 : Blo 1796099 4043483 := bstep (se 1 (by rfl) ⟨3032612, by rfl⟩ : syracuseStep 4043483 = 6065225) B6065225
theorem B472462121 : Blo 1796099 472462121 := bstep (se 2 (by rfl) ⟨177173295, by rfl⟩ : syracuseStep 472462121 = 354346591) B354346591
theorem B9098081 : Blo 1796099 9098081 := bstep (se 2 (by rfl) ⟨3411780, by rfl⟩ : syracuseStep 9098081 = 6823561) B6823561
theorem B6821117 : Blo 1796099 6821117 := bstep (se 3 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 6821117 = 2557919) B2557919
theorem B4044239 : Blo 1796099 4044239 := bstep (se 1 (by rfl) ⟨3033179, by rfl⟩ : syracuseStep 4044239 = 6066359) B6066359
theorem B2274799 : Blo 1796099 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B82974763 : Blo 1796099 82974763 := bstep (se 1 (by rfl) ⟨62231072, by rfl⟩ : syracuseStep 82974763 = 124462145) B124462145
theorem B13654169 : Blo 1796099 13654169 := bstep (se 2 (by rfl) ⟨5120313, by rfl⟩ : syracuseStep 13654169 = 10240627) B10240627
theorem B31119713 : Blo 1796099 31119713 := bstep (se 2 (by rfl) ⟨11669892, by rfl⟩ : syracuseStep 31119713 = 23339785) B23339785
theorem B2021935 : Blo 1796099 2021935 := bstep (se 1 (by rfl) ⟨1516451, by rfl⟩ : syracuseStep 2021935 = 3032903) B3032903
theorem B11516863 : Blo 1796099 11516863 := bstep (se 1 (by rfl) ⟨8637647, by rfl⟩ : syracuseStep 11516863 = 17275295) B17275295
theorem B2022367 : Blo 1796099 2022367 := bstep (se 1 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 2022367 = 3033551) B3033551
theorem B2694251 : Blo 1796099 2694251 := bstep (se 1 (by rfl) ⟨2020688, by rfl⟩ : syracuseStep 2694251 = 4041377) B4041377
theorem B2022511 : Blo 1796099 2022511 := bstep (se 1 (by rfl) ⟨1516883, by rfl⟩ : syracuseStep 2022511 = 3033767) B3033767
theorem B2694455 : Blo 1796099 2694455 := bstep (se 1 (by rfl) ⟨2020841, by rfl⟩ : syracuseStep 2694455 = 4041683) B4041683
theorem B26263091 : Blo 1796099 26263091 := bstep (se 1 (by rfl) ⟨19697318, by rfl⟩ : syracuseStep 26263091 = 39394637) B39394637
theorem B65584835 : Blo 1796099 65584835 := bstep (se 1 (by rfl) ⟨49188626, by rfl⟩ : syracuseStep 65584835 = 98377253) B98377253
theorem B2695103 : Blo 1796099 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B9093059 : Blo 1796099 9093059 := bstep (se 1 (by rfl) ⟨6819794, by rfl⟩ : syracuseStep 9093059 = 13639589) B13639589
theorem B2695259 : Blo 1796099 2695259 := bstep (se 1 (by rfl) ⟨2021444, by rfl⟩ : syracuseStep 2695259 = 4042889) B4042889
theorem B3031195 : Blo 1796099 3031195 := bstep (se 1 (by rfl) ⟨2273396, by rfl⟩ : syracuseStep 3031195 = 4546793) B4546793
theorem B11518145 : Blo 1796099 11518145 := bstep (se 2 (by rfl) ⟨4319304, by rfl⟩ : syracuseStep 11518145 = 8638609) B8638609
theorem B442532069 : Blo 1796099 442532069 := bstep (se 4 (by rfl) ⟨41487381, by rfl⟩ : syracuseStep 442532069 = 82974763) B82974763
theorem B21856513 : Blo 1796099 21856513 := bstep (se 2 (by rfl) ⟨8196192, by rfl⟩ : syracuseStep 21856513 = 16392385) B16392385
theorem B2695655 : Blo 1796099 2695655 := bstep (se 1 (by rfl) ⟨2021741, by rfl⟩ : syracuseStep 2695655 = 4043483) B4043483
theorem B314974747 : Blo 1796099 314974747 := bstep (se 1 (by rfl) ⟨236231060, by rfl⟩ : syracuseStep 314974747 = 472462121) B472462121
theorem B49201759 : Blo 1796099 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B2695913 : Blo 1796099 2695913 := bstep (se 2 (by rfl) ⟨1010967, by rfl⟩ : syracuseStep 2695913 = 2021935) B2021935
theorem B4547411 : Blo 1796099 4547411 := bstep (se 1 (by rfl) ⟨3410558, by rfl⟩ : syracuseStep 4547411 = 6821117) B6821117
theorem B2696159 : Blo 1796099 2696159 := bstep (se 1 (by rfl) ⟨2022119, by rfl⟩ : syracuseStep 2696159 = 4044239) B4044239
theorem B9094355 : Blo 1796099 9094355 := bstep (se 1 (by rfl) ⟨6820766, by rfl⟩ : syracuseStep 9094355 = 13641533) B13641533
theorem B2696489 : Blo 1796099 2696489 := bstep (se 2 (by rfl) ⟨1011183, by rfl⟩ : syracuseStep 2696489 = 2022367) B2022367
theorem B9102779 : Blo 1796099 9102779 := bstep (se 1 (by rfl) ⟨6827084, by rfl⟩ : syracuseStep 9102779 = 13654169) B13654169
theorem B2696681 : Blo 1796099 2696681 := bstep (se 2 (by rfl) ⟨1011255, by rfl⟩ : syracuseStep 2696681 = 2022511) B2022511
theorem B3032815 : Blo 1796099 3032815 := bstep (se 1 (by rfl) ⟨2274611, by rfl⟩ : syracuseStep 3032815 = 4549223) B4549223
theorem B3033065 : Blo 1796099 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B1796167 : Blo 1796099 1796167 := bstep (se 1 (by rfl) ⟨1347125, by rfl⟩ : syracuseStep 1796167 = 2694251) B2694251
theorem B6146171 : Blo 1796099 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B1796303 : Blo 1796099 1796303 := bstep (se 1 (by rfl) ⟨1347227, by rfl⟩ : syracuseStep 1796303 = 2694455) B2694455
theorem B17508727 : Blo 1796099 17508727 := bstep (se 1 (by rfl) ⟨13131545, by rfl⟩ : syracuseStep 17508727 = 26263091) B26263091
theorem B48630203 : Blo 1796099 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B43723223 : Blo 1796099 43723223 := bstep (se 1 (by rfl) ⟨32792417, by rfl⟩ : syracuseStep 43723223 = 65584835) B65584835
theorem B6064631 : Blo 1796099 6064631 := bstep (se 1 (by rfl) ⟨4548473, by rfl⟩ : syracuseStep 6064631 = 9096947) B9096947
theorem B1796735 : Blo 1796099 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B6474431 : Blo 1796099 6474431 := bstep (se 1 (by rfl) ⟨4855823, by rfl⟩ : syracuseStep 6474431 = 9711647) B9711647
theorem B2878345 : Blo 1796099 2878345 := bstep (se 2 (by rfl) ⟨1079379, by rfl⟩ : syracuseStep 2878345 = 2158759) B2158759
theorem B3034111 : Blo 1796099 3034111 := bstep (se 1 (by rfl) ⟨2275583, by rfl⟩ : syracuseStep 3034111 = 4551167) B4551167
theorem B6065387 : Blo 1796099 6065387 := bstep (se 1 (by rfl) ⟨4549040, by rfl⟩ : syracuseStep 6065387 = 9098081) B9098081
theorem B15355817 : Blo 1796099 15355817 := bstep (se 2 (by rfl) ⟨5758431, by rfl⟩ : syracuseStep 15355817 = 11516863) B11516863
theorem B69087329 : Blo 1796099 69087329 := bstep (se 2 (by rfl) ⟨25907748, by rfl⟩ : syracuseStep 69087329 = 51815497) B51815497
theorem B15347819 : Blo 1796099 15347819 := bstep (se 1 (by rfl) ⟨11510864, by rfl⟩ : syracuseStep 15347819 = 23021729) B23021729
theorem B20746475 : Blo 1796099 20746475 := bstep (se 1 (by rfl) ⟨15559856, by rfl⟩ : syracuseStep 20746475 = 31119713) B31119713
theorem B44914031 : Blo 1796099 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B6067871 : Blo 1796099 6067871 := bstep (se 1 (by rfl) ⟨4550903, by rfl⟩ : syracuseStep 6067871 = 9101807) B9101807
theorem B5118059 : Blo 1796099 5118059 := bstep (se 1 (by rfl) ⟨3838544, by rfl⟩ : syracuseStep 5118059 = 7677089) B7677089
theorem B3840167 : Blo 1796099 3840167 := bstep (se 1 (by rfl) ⟨2880125, by rfl⟩ : syracuseStep 3840167 = 5760251) B5760251
theorem B19421471 : Blo 1796099 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B9100511 : Blo 1796099 9100511 := bstep (se 1 (by rfl) ⟨6825383, by rfl⟩ : syracuseStep 9100511 = 13650767) B13650767
theorem B23019065 : Blo 1796099 23019065 := bstep (se 2 (by rfl) ⟨8632149, by rfl⟩ : syracuseStep 23019065 = 17264299) B17264299
theorem B2694839 : Blo 1796099 2694839 := bstep (se 1 (by rfl) ⟨2021129, by rfl⟩ : syracuseStep 2694839 = 4042259) B4042259
theorem B19439423 : Blo 1796099 19439423 := bstep (se 1 (by rfl) ⟨14579567, by rfl⟩ : syracuseStep 19439423 = 29159135) B29159135
theorem B6062039 : Blo 1796099 6062039 := bstep (se 1 (by rfl) ⟨4546529, by rfl⟩ : syracuseStep 6062039 = 9093059) B9093059
theorem B10231879 : Blo 1796099 10231879 := bstep (se 1 (by rfl) ⟨7673909, by rfl⟩ : syracuseStep 10231879 = 15347819) B15347819
theorem B10240445 : Blo 1796099 10240445 := bstep (se 3 (by rfl) ⟨1920083, by rfl⟩ : syracuseStep 10240445 = 3840167) B3840167
theorem B3031607 : Blo 1796099 3031607 := bstep (se 1 (by rfl) ⟨2273705, by rfl⟩ : syracuseStep 3031607 = 4547411) B4547411
theorem B51790589 : Blo 1796099 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B6062903 : Blo 1796099 6062903 := bstep (se 1 (by rfl) ⟨4547177, by rfl⟩ : syracuseStep 6062903 = 9094355) B9094355
theorem B29942687 : Blo 1796099 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B4097447 : Blo 1796099 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B29148815 : Blo 1796099 29148815 := bstep (se 1 (by rfl) ⟨21861611, by rfl⟩ : syracuseStep 29148815 = 43723223) B43723223
theorem B15346043 : Blo 1796099 15346043 := bstep (se 1 (by rfl) ⟨11509532, by rfl⟩ : syracuseStep 15346043 = 23019065) B23019065
theorem B1796559 : Blo 1796099 1796559 := bstep (se 1 (by rfl) ⟨1347419, by rfl⟩ : syracuseStep 1796559 = 2694839) B2694839
theorem B4041359 : Blo 1796099 4041359 := bstep (se 1 (by rfl) ⟨3031019, by rfl⟩ : syracuseStep 4041359 = 6062039) B6062039
theorem B1796839 : Blo 1796099 1796839 := bstep (se 1 (by rfl) ⟨1347629, by rfl⟩ : syracuseStep 1796839 = 2695259) B2695259
theorem B46058219 : Blo 1796099 46058219 := bstep (se 1 (by rfl) ⟨34543664, by rfl⟩ : syracuseStep 46058219 = 69087329) B69087329
theorem B7678763 : Blo 1796099 7678763 := bstep (se 1 (by rfl) ⟨5759072, by rfl⟩ : syracuseStep 7678763 = 11518145) B11518145
theorem B295021379 : Blo 1796099 295021379 := bstep (se 1 (by rfl) ⟨221266034, by rfl⟩ : syracuseStep 295021379 = 442532069) B442532069
theorem B13830983 : Blo 1796099 13830983 := bstep (se 1 (by rfl) ⟨10373237, by rfl⟩ : syracuseStep 13830983 = 20746475) B20746475
theorem B4041593 : Blo 1796099 4041593 := bstep (se 2 (by rfl) ⟨1515597, by rfl⟩ : syracuseStep 4041593 = 3031195) B3031195
theorem B1797103 : Blo 1796099 1797103 := bstep (se 1 (by rfl) ⟨1347827, by rfl⟩ : syracuseStep 1797103 = 2695655) B2695655
theorem B29142017 : Blo 1796099 29142017 := bstep (se 2 (by rfl) ⟨10928256, by rfl⟩ : syracuseStep 29142017 = 21856513) B21856513
theorem B1797275 : Blo 1796099 1797275 := bstep (se 1 (by rfl) ⟨1347956, by rfl⟩ : syracuseStep 1797275 = 2695913) B2695913
theorem B262409381 : Blo 1796099 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B1797439 : Blo 1796099 1797439 := bstep (se 1 (by rfl) ⟨1348079, by rfl⟩ : syracuseStep 1797439 = 2696159) B2696159
theorem B419966329 : Blo 1796099 419966329 := bstep (se 2 (by rfl) ⟨157487373, by rfl⟩ : syracuseStep 419966329 = 314974747) B314974747
theorem B1797659 : Blo 1796099 1797659 := bstep (se 1 (by rfl) ⟨1348244, by rfl⟩ : syracuseStep 1797659 = 2696489) B2696489
theorem B1797787 : Blo 1796099 1797787 := bstep (se 1 (by rfl) ⟨1348340, by rfl⟩ : syracuseStep 1797787 = 2696681) B2696681
theorem B3837793 : Blo 1796099 3837793 := bstep (se 2 (by rfl) ⟨1439172, by rfl⟩ : syracuseStep 3837793 = 2878345) B2878345
theorem B3412039 : Blo 1796099 3412039 := bstep (se 1 (by rfl) ⟨2559029, by rfl⟩ : syracuseStep 3412039 = 5118059) B5118059
theorem B32420135 : Blo 1796099 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B4043087 : Blo 1796099 4043087 := bstep (se 1 (by rfl) ⟨3032315, by rfl⟩ : syracuseStep 4043087 = 6064631) B6064631
theorem B17265149 : Blo 1796099 17265149 := bstep (se 3 (by rfl) ⟨3237215, by rfl⟩ : syracuseStep 17265149 = 6474431) B6474431
theorem B6067007 : Blo 1796099 6067007 := bstep (se 1 (by rfl) ⟨4550255, by rfl⟩ : syracuseStep 6067007 = 9100511) B9100511
theorem B4043591 : Blo 1796099 4043591 := bstep (se 1 (by rfl) ⟨3032693, by rfl⟩ : syracuseStep 4043591 = 6065387) B6065387
theorem B4043753 : Blo 1796099 4043753 := bstep (se 2 (by rfl) ⟨1516407, by rfl⟩ : syracuseStep 4043753 = 3032815) B3032815
theorem B10237211 : Blo 1796099 10237211 := bstep (se 1 (by rfl) ⟨7677908, by rfl⟩ : syracuseStep 10237211 = 15355817) B15355817
theorem B23344969 : Blo 1796099 23344969 := bstep (se 2 (by rfl) ⟨8754363, by rfl⟩ : syracuseStep 23344969 = 17508727) B17508727
theorem B6068519 : Blo 1796099 6068519 := bstep (se 1 (by rfl) ⟨4551389, by rfl⟩ : syracuseStep 6068519 = 9102779) B9102779
theorem B4045247 : Blo 1796099 4045247 := bstep (se 1 (by rfl) ⟨3033935, by rfl⟩ : syracuseStep 4045247 = 6067871) B6067871
theorem B2022043 : Blo 1796099 2022043 := bstep (se 1 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 2022043 = 3033065) B3033065
theorem B4045481 : Blo 1796099 4045481 := bstep (se 2 (by rfl) ⟨1517055, by rfl⟩ : syracuseStep 4045481 = 3034111) B3034111
theorem B12959615 : Blo 1796099 12959615 := bstep (se 1 (by rfl) ⟨9719711, by rfl⟩ : syracuseStep 12959615 = 19439423) B19439423
theorem B2695391 : Blo 1796099 2695391 := bstep (se 1 (by rfl) ⟨2021543, by rfl⟩ : syracuseStep 2695391 = 4043087) B4043087
theorem B11510099 : Blo 1796099 11510099 := bstep (se 1 (by rfl) ⟨8632574, by rfl⟩ : syracuseStep 11510099 = 17265149) B17265149
theorem B2695727 : Blo 1796099 2695727 := bstep (se 1 (by rfl) ⟨2021795, by rfl⟩ : syracuseStep 2695727 = 4043591) B4043591
theorem B2695835 : Blo 1796099 2695835 := bstep (se 1 (by rfl) ⟨2021876, by rfl⟩ : syracuseStep 2695835 = 4043753) B4043753
theorem B6824807 : Blo 1796099 6824807 := bstep (se 1 (by rfl) ⟨5118605, by rfl⟩ : syracuseStep 6824807 = 10237211) B10237211
theorem B2696057 : Blo 1796099 2696057 := bstep (se 2 (by rfl) ⟨1011021, by rfl⟩ : syracuseStep 2696057 = 2022043) B2022043
theorem B19432543 : Blo 1796099 19432543 := bstep (se 1 (by rfl) ⟨14574407, by rfl⟩ : syracuseStep 19432543 = 29148815) B29148815
theorem B2696831 : Blo 1796099 2696831 := bstep (se 1 (by rfl) ⟨2022623, by rfl⟩ : syracuseStep 2696831 = 4045247) B4045247
theorem B43706101 : Blo 1796099 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B2696987 : Blo 1796099 2696987 := bstep (se 1 (by rfl) ⟨2022740, by rfl⟩ : syracuseStep 2696987 = 4045481) B4045481
theorem B30705479 : Blo 1796099 30705479 := bstep (se 1 (by rfl) ⟨23029109, by rfl⟩ : syracuseStep 30705479 = 46058219) B46058219
theorem B13642505 : Blo 1796099 13642505 := bstep (se 2 (by rfl) ⟨5115939, by rfl⟩ : syracuseStep 13642505 = 10231879) B10231879
theorem B4549385 : Blo 1796099 4549385 := bstep (se 2 (by rfl) ⟨1706019, by rfl⟩ : syracuseStep 4549385 = 3412039) B3412039
theorem B21613423 : Blo 1796099 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B6826963 : Blo 1796099 6826963 := bstep (se 1 (by rfl) ⟨5120222, by rfl⟩ : syracuseStep 6826963 = 10240445) B10240445
theorem B4041935 : Blo 1796099 4041935 := bstep (se 1 (by rfl) ⟨3031451, by rfl⟩ : syracuseStep 4041935 = 6062903) B6062903
theorem B9220655 : Blo 1796099 9220655 := bstep (se 1 (by rfl) ⟨6915491, by rfl⟩ : syracuseStep 9220655 = 13830983) B13830983
theorem B19428011 : Blo 1796099 19428011 := bstep (se 1 (by rfl) ⟨14571008, by rfl⟩ : syracuseStep 19428011 = 29142017) B29142017
theorem B34558973 : Blo 1796099 34558973 := bstep (se 3 (by rfl) ⟨6479807, by rfl⟩ : syracuseStep 34558973 = 12959615) B12959615
theorem B31126625 : Blo 1796099 31126625 := bstep (se 2 (by rfl) ⟨11672484, by rfl⟩ : syracuseStep 31126625 = 23344969) B23344969
theorem B5117057 : Blo 1796099 5117057 := bstep (se 2 (by rfl) ⟨1918896, by rfl⟩ : syracuseStep 5117057 = 3837793) B3837793
theorem B2021071 : Blo 1796099 2021071 := bstep (se 1 (by rfl) ⟨1515803, by rfl⟩ : syracuseStep 2021071 = 3031607) B3031607
theorem B34527059 : Blo 1796099 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B4044671 : Blo 1796099 4044671 := bstep (se 1 (by rfl) ⟨3033503, by rfl⟩ : syracuseStep 4044671 = 6067007) B6067007
theorem B4045679 : Blo 1796099 4045679 := bstep (se 1 (by rfl) ⟨3034259, by rfl⟩ : syracuseStep 4045679 = 6068519) B6068519
theorem B10230695 : Blo 1796099 10230695 := bstep (se 1 (by rfl) ⟨7673021, by rfl⟩ : syracuseStep 10230695 = 15346043) B15346043
theorem B2694239 : Blo 1796099 2694239 := bstep (se 1 (by rfl) ⟨2020679, by rfl⟩ : syracuseStep 2694239 = 4041359) B4041359
theorem B559955105 : Blo 1796099 559955105 := bstep (se 2 (by rfl) ⟨209983164, by rfl⟩ : syracuseStep 559955105 = 419966329) B419966329
theorem B5119175 : Blo 1796099 5119175 := bstep (se 1 (by rfl) ⟨3839381, by rfl⟩ : syracuseStep 5119175 = 7678763) B7678763
theorem B196680919 : Blo 1796099 196680919 := bstep (se 1 (by rfl) ⟨147510689, by rfl⟩ : syracuseStep 196680919 = 295021379) B295021379
theorem B2694395 : Blo 1796099 2694395 := bstep (se 1 (by rfl) ⟨2020796, by rfl⟩ : syracuseStep 2694395 = 4041593) B4041593
theorem B174939587 : Blo 1796099 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B79847165 : Blo 1796099 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B12952007 : Blo 1796099 12952007 := bstep (se 1 (by rfl) ⟨9714005, by rfl⟩ : syracuseStep 12952007 = 19428011) B19428011
theorem B20751083 : Blo 1796099 20751083 := bstep (se 1 (by rfl) ⟨15563312, by rfl⟩ : syracuseStep 20751083 = 31126625) B31126625
theorem B2696447 : Blo 1796099 2696447 := bstep (se 1 (by rfl) ⟨2022335, by rfl⟩ : syracuseStep 2696447 = 4044671) B4044671
theorem B9102617 : Blo 1796099 9102617 := bstep (se 2 (by rfl) ⟨3413481, by rfl⟩ : syracuseStep 9102617 = 6826963) B6826963
theorem B9095003 : Blo 1796099 9095003 := bstep (se 1 (by rfl) ⟨6821252, by rfl⟩ : syracuseStep 9095003 = 13642505) B13642505
theorem B3032923 : Blo 1796099 3032923 := bstep (se 1 (by rfl) ⟨2274692, by rfl⟩ : syracuseStep 3032923 = 4549385) B4549385
theorem B2697119 : Blo 1796099 2697119 := bstep (se 1 (by rfl) ⟨2022839, by rfl⟩ : syracuseStep 2697119 = 4045679) B4045679
theorem B1796159 : Blo 1796099 1796159 := bstep (se 1 (by rfl) ⟨1347119, by rfl⟩ : syracuseStep 1796159 = 2694239) B2694239
theorem B373303403 : Blo 1796099 373303403 := bstep (se 1 (by rfl) ⟨279977552, by rfl⟩ : syracuseStep 373303403 = 559955105) B559955105
theorem B1796263 : Blo 1796099 1796263 := bstep (se 1 (by rfl) ⟨1347197, by rfl⟩ : syracuseStep 1796263 = 2694395) B2694395
theorem B1796927 : Blo 1796099 1796927 := bstep (se 1 (by rfl) ⟨1347695, by rfl⟩ : syracuseStep 1796927 = 2695391) B2695391
theorem B6147103 : Blo 1796099 6147103 := bstep (se 1 (by rfl) ⟨4610327, by rfl⟩ : syracuseStep 6147103 = 9220655) B9220655
theorem B1797151 : Blo 1796099 1797151 := bstep (se 1 (by rfl) ⟨1347863, by rfl⟩ : syracuseStep 1797151 = 2695727) B2695727
theorem B1797223 : Blo 1796099 1797223 := bstep (se 1 (by rfl) ⟨1347917, by rfl⟩ : syracuseStep 1797223 = 2695835) B2695835
theorem B4549871 : Blo 1796099 4549871 := bstep (se 1 (by rfl) ⟨3412403, by rfl⟩ : syracuseStep 4549871 = 6824807) B6824807
theorem B1797371 : Blo 1796099 1797371 := bstep (se 1 (by rfl) ⟨1348028, by rfl⟩ : syracuseStep 1797371 = 2696057) B2696057
theorem B23039315 : Blo 1796099 23039315 := bstep (se 1 (by rfl) ⟨17279486, by rfl⟩ : syracuseStep 23039315 = 34558973) B34558973
theorem B3411371 : Blo 1796099 3411371 := bstep (se 1 (by rfl) ⟨2558528, by rfl⟩ : syracuseStep 3411371 = 5117057) B5117057
theorem B1797887 : Blo 1796099 1797887 := bstep (se 1 (by rfl) ⟨1348415, by rfl⟩ : syracuseStep 1797887 = 2696831) B2696831
theorem B1797991 : Blo 1796099 1797991 := bstep (se 1 (by rfl) ⟨1348493, by rfl⟩ : syracuseStep 1797991 = 2696987) B2696987
theorem B6820463 : Blo 1796099 6820463 := bstep (se 1 (by rfl) ⟨5115347, by rfl⟩ : syracuseStep 6820463 = 10230695) B10230695
theorem B3412783 : Blo 1796099 3412783 := bstep (se 1 (by rfl) ⟨2559587, by rfl⟩ : syracuseStep 3412783 = 5119175) B5119175
theorem B116626391 : Blo 1796099 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B58274801 : Blo 1796099 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B7673399 : Blo 1796099 7673399 := bstep (se 1 (by rfl) ⟨5755049, by rfl⟩ : syracuseStep 7673399 = 11510099) B11510099
theorem B28817897 : Blo 1796099 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B20470319 : Blo 1796099 20470319 := bstep (se 1 (by rfl) ⟨15352739, by rfl⟩ : syracuseStep 20470319 = 30705479) B30705479
theorem B23018039 : Blo 1796099 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B25910057 : Blo 1796099 25910057 := bstep (se 2 (by rfl) ⟨9716271, by rfl⟩ : syracuseStep 25910057 = 19432543) B19432543
theorem B262241225 : Blo 1796099 262241225 := bstep (se 2 (by rfl) ⟨98340459, by rfl⟩ : syracuseStep 262241225 = 196680919) B196680919
theorem B212925773 : Blo 1796099 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B2694623 : Blo 1796099 2694623 := bstep (se 1 (by rfl) ⟨2020967, by rfl⟩ : syracuseStep 2694623 = 4041935) B4041935
theorem B2694761 : Blo 1796099 2694761 := bstep (se 2 (by rfl) ⟨1010535, by rfl⟩ : syracuseStep 2694761 = 2021071) B2021071
theorem B8634671 : Blo 1796099 8634671 := bstep (se 1 (by rfl) ⟨6476003, by rfl⟩ : syracuseStep 8634671 = 12952007) B12952007
theorem B4546975 : Blo 1796099 4546975 := bstep (se 1 (by rfl) ⟨3410231, by rfl⟩ : syracuseStep 4546975 = 6820463) B6820463
theorem B77750927 : Blo 1796099 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B6063335 : Blo 1796099 6063335 := bstep (se 1 (by rfl) ⟨4547501, by rfl⟩ : syracuseStep 6063335 = 9095003) B9095003
theorem B15345359 : Blo 1796099 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B174827483 : Blo 1796099 174827483 := bstep (se 1 (by rfl) ⟨131120612, by rfl⟩ : syracuseStep 174827483 = 262241225) B262241225
theorem B3033247 : Blo 1796099 3033247 := bstep (se 1 (by rfl) ⟨2274935, by rfl⟩ : syracuseStep 3033247 = 4549871) B4549871
theorem B1796415 : Blo 1796099 1796415 := bstep (se 1 (by rfl) ⟨1347311, by rfl⟩ : syracuseStep 1796415 = 2694623) B2694623
theorem B1796507 : Blo 1796099 1796507 := bstep (se 1 (by rfl) ⟨1347380, by rfl⟩ : syracuseStep 1796507 = 2694761) B2694761
theorem B38849867 : Blo 1796099 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B1797631 : Blo 1796099 1797631 := bstep (se 1 (by rfl) ⟨1348223, by rfl⟩ : syracuseStep 1797631 = 2696447) B2696447
theorem B5115599 : Blo 1796099 5115599 := bstep (se 1 (by rfl) ⟨3836699, by rfl⟩ : syracuseStep 5115599 = 7673399) B7673399
theorem B4550377 : Blo 1796099 4550377 := bstep (se 2 (by rfl) ⟨1706391, by rfl⟩ : syracuseStep 4550377 = 3412783) B3412783
theorem B1798079 : Blo 1796099 1798079 := bstep (se 1 (by rfl) ⟨1348559, by rfl⟩ : syracuseStep 1798079 = 2697119) B2697119
theorem B8196137 : Blo 1796099 8196137 := bstep (se 2 (by rfl) ⟨3073551, by rfl⟩ : syracuseStep 8196137 = 6147103) B6147103
theorem B248868935 : Blo 1796099 248868935 := bstep (se 1 (by rfl) ⟨186651701, by rfl⟩ : syracuseStep 248868935 = 373303403) B373303403
theorem B17273371 : Blo 1796099 17273371 := bstep (se 1 (by rfl) ⟨12955028, by rfl⟩ : syracuseStep 17273371 = 25910057) B25910057
theorem B2274247 : Blo 1796099 2274247 := bstep (se 1 (by rfl) ⟨1705685, by rfl⟩ : syracuseStep 2274247 = 3411371) B3411371
theorem B4043897 : Blo 1796099 4043897 := bstep (se 2 (by rfl) ⟨1516461, by rfl⟩ : syracuseStep 4043897 = 3032923) B3032923
theorem B13834055 : Blo 1796099 13834055 := bstep (se 1 (by rfl) ⟨10375541, by rfl⟩ : syracuseStep 13834055 = 20751083) B20751083
theorem B6068411 : Blo 1796099 6068411 := bstep (se 1 (by rfl) ⟨4551308, by rfl⟩ : syracuseStep 6068411 = 9102617) B9102617
theorem B76847725 : Blo 1796099 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B13646879 : Blo 1796099 13646879 := bstep (se 1 (by rfl) ⟨10235159, by rfl⟩ : syracuseStep 13646879 = 20470319) B20470319
theorem B141950515 : Blo 1796099 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B15359543 : Blo 1796099 15359543 := bstep (se 1 (by rfl) ⟨11519657, by rfl⟩ : syracuseStep 15359543 = 23039315) B23039315
theorem B5464091 : Blo 1796099 5464091 := bstep (se 1 (by rfl) ⟨4098068, by rfl⟩ : syracuseStep 5464091 = 8196137) B8196137
theorem B165912623 : Blo 1796099 165912623 := bstep (se 1 (by rfl) ⟨124434467, by rfl⟩ : syracuseStep 165912623 = 248868935) B248868935
theorem B6062633 : Blo 1796099 6062633 := bstep (se 2 (by rfl) ⟨2273487, by rfl⟩ : syracuseStep 6062633 = 4546975) B4546975
theorem B2695931 : Blo 1796099 2695931 := bstep (se 1 (by rfl) ⟨2021948, by rfl⟩ : syracuseStep 2695931 = 4043897) B4043897
theorem B3032329 : Blo 1796099 3032329 := bstep (se 2 (by rfl) ⟨1137123, by rfl⟩ : syracuseStep 3032329 = 2274247) B2274247
theorem B3410399 : Blo 1796099 3410399 := bstep (se 1 (by rfl) ⟨2557799, by rfl⟩ : syracuseStep 3410399 = 5115599) B5115599
theorem B51833951 : Blo 1796099 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B23031161 : Blo 1796099 23031161 := bstep (se 2 (by rfl) ⟨8636685, by rfl⟩ : syracuseStep 23031161 = 17273371) B17273371
theorem B4042223 : Blo 1796099 4042223 := bstep (se 1 (by rfl) ⟨3031667, by rfl⟩ : syracuseStep 4042223 = 6063335) B6063335
theorem B116551655 : Blo 1796099 116551655 := bstep (se 1 (by rfl) ⟨87413741, by rfl⟩ : syracuseStep 116551655 = 174827483) B174827483
theorem B9097919 : Blo 1796099 9097919 := bstep (se 1 (by rfl) ⟨6823439, by rfl⟩ : syracuseStep 9097919 = 13646879) B13646879
theorem B25899911 : Blo 1796099 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B6067169 : Blo 1796099 6067169 := bstep (se 2 (by rfl) ⟨2275188, by rfl⟩ : syracuseStep 6067169 = 4550377) B4550377
theorem B5756447 : Blo 1796099 5756447 := bstep (se 1 (by rfl) ⟨4317335, by rfl⟩ : syracuseStep 5756447 = 8634671) B8634671
theorem B4044329 : Blo 1796099 4044329 := bstep (se 2 (by rfl) ⟨1516623, by rfl⟩ : syracuseStep 4044329 = 3033247) B3033247
theorem B102463633 : Blo 1796099 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B10230239 : Blo 1796099 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B9222703 : Blo 1796099 9222703 := bstep (se 1 (by rfl) ⟨6917027, by rfl⟩ : syracuseStep 9222703 = 13834055) B13834055
theorem B4045607 : Blo 1796099 4045607 := bstep (se 1 (by rfl) ⟨3034205, by rfl⟩ : syracuseStep 4045607 = 6068411) B6068411
theorem B189267353 : Blo 1796099 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B10239695 : Blo 1796099 10239695 := bstep (se 1 (by rfl) ⟨7679771, by rfl⟩ : syracuseStep 10239695 = 15359543) B15359543
theorem B110608415 : Blo 1796099 110608415 := bstep (se 1 (by rfl) ⟨82956311, by rfl⟩ : syracuseStep 110608415 = 165912623) B165912623
theorem B136618177 : Blo 1796099 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B2696219 : Blo 1796099 2696219 := bstep (se 1 (by rfl) ⟨2022164, by rfl⟩ : syracuseStep 2696219 = 4044329) B4044329
theorem B2697071 : Blo 1796099 2697071 := bstep (se 1 (by rfl) ⟨2022803, by rfl⟩ : syracuseStep 2697071 = 4045607) B4045607
theorem B34555967 : Blo 1796099 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B15354107 : Blo 1796099 15354107 := bstep (se 1 (by rfl) ⟨11515580, by rfl⟩ : syracuseStep 15354107 = 23031161) B23031161
theorem B6826463 : Blo 1796099 6826463 := bstep (se 1 (by rfl) ⟨5119847, by rfl⟩ : syracuseStep 6826463 = 10239695) B10239695
theorem B49187749 : Blo 1796099 49187749 := bstep (se 4 (by rfl) ⟨4611351, by rfl⟩ : syracuseStep 49187749 = 9222703) B9222703
theorem B4041755 : Blo 1796099 4041755 := bstep (se 1 (by rfl) ⟨3031316, by rfl⟩ : syracuseStep 4041755 = 6062633) B6062633
theorem B6065279 : Blo 1796099 6065279 := bstep (se 1 (by rfl) ⟨4548959, by rfl⟩ : syracuseStep 6065279 = 9097919) B9097919
theorem B1797287 : Blo 1796099 1797287 := bstep (se 1 (by rfl) ⟨1347965, by rfl⟩ : syracuseStep 1797287 = 2695931) B2695931
theorem B3837631 : Blo 1796099 3837631 := bstep (se 1 (by rfl) ⟨2878223, by rfl⟩ : syracuseStep 3837631 = 5756447) B5756447
theorem B6820159 : Blo 1796099 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B2273599 : Blo 1796099 2273599 := bstep (se 1 (by rfl) ⟨1705199, by rfl⟩ : syracuseStep 2273599 = 3410399) B3410399
theorem B4043105 : Blo 1796099 4043105 := bstep (se 2 (by rfl) ⟨1516164, by rfl⟩ : syracuseStep 4043105 = 3032329) B3032329
theorem B126178235 : Blo 1796099 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B3642727 : Blo 1796099 3642727 := bstep (se 1 (by rfl) ⟨2732045, by rfl⟩ : syracuseStep 3642727 = 5464091) B5464091
theorem B17266607 : Blo 1796099 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B4044779 : Blo 1796099 4044779 := bstep (se 1 (by rfl) ⟨3033584, by rfl⟩ : syracuseStep 4044779 = 6067169) B6067169
theorem B2694815 : Blo 1796099 2694815 := bstep (se 1 (by rfl) ⟨2021111, by rfl⟩ : syracuseStep 2694815 = 4042223) B4042223
theorem B77701103 : Blo 1796099 77701103 := bstep (se 1 (by rfl) ⟨58275827, by rfl⟩ : syracuseStep 77701103 = 116551655) B116551655
theorem B2695403 : Blo 1796099 2695403 := bstep (se 1 (by rfl) ⟨2021552, by rfl⟩ : syracuseStep 2695403 = 4043105) B4043105
theorem B182157569 : Blo 1796099 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B9093545 : Blo 1796099 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B3031465 : Blo 1796099 3031465 := bstep (se 2 (by rfl) ⟨1136799, by rfl⟩ : syracuseStep 3031465 = 2273599) B2273599
theorem B11511071 : Blo 1796099 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B2696519 : Blo 1796099 2696519 := bstep (se 1 (by rfl) ⟨2022389, by rfl⟩ : syracuseStep 2696519 = 4044779) B4044779
theorem B23037311 : Blo 1796099 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B1796543 : Blo 1796099 1796543 := bstep (se 1 (by rfl) ⟨1347407, by rfl⟩ : syracuseStep 1796543 = 2694815) B2694815
theorem B51800735 : Blo 1796099 51800735 := bstep (se 1 (by rfl) ⟨38850551, by rfl⟩ : syracuseStep 51800735 = 77701103) B77701103
theorem B73738943 : Blo 1796099 73738943 := bstep (se 1 (by rfl) ⟨55304207, by rfl⟩ : syracuseStep 73738943 = 110608415) B110608415
theorem B84118823 : Blo 1796099 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B1797479 : Blo 1796099 1797479 := bstep (se 1 (by rfl) ⟨1348109, by rfl⟩ : syracuseStep 1797479 = 2696219) B2696219
theorem B1798047 : Blo 1796099 1798047 := bstep (se 1 (by rfl) ⟨1348535, by rfl⟩ : syracuseStep 1798047 = 2697071) B2697071
theorem B10236071 : Blo 1796099 10236071 := bstep (se 1 (by rfl) ⟨7677053, by rfl⟩ : syracuseStep 10236071 = 15354107) B15354107
theorem B4550975 : Blo 1796099 4550975 := bstep (se 1 (by rfl) ⟨3413231, by rfl⟩ : syracuseStep 4550975 = 6826463) B6826463
theorem B4043519 : Blo 1796099 4043519 := bstep (se 1 (by rfl) ⟨3032639, by rfl⟩ : syracuseStep 4043519 = 6065279) B6065279
theorem B5116841 : Blo 1796099 5116841 := bstep (se 2 (by rfl) ⟨1918815, by rfl⟩ : syracuseStep 5116841 = 3837631) B3837631
theorem B65583665 : Blo 1796099 65583665 := bstep (se 2 (by rfl) ⟨24593874, by rfl⟩ : syracuseStep 65583665 = 49187749) B49187749
theorem B4856969 : Blo 1796099 4856969 := bstep (se 2 (by rfl) ⟨1821363, by rfl⟩ : syracuseStep 4856969 = 3642727) B3642727
theorem B2694503 : Blo 1796099 2694503 := bstep (se 1 (by rfl) ⟨2020877, by rfl⟩ : syracuseStep 2694503 = 4041755) B4041755
theorem B6824047 : Blo 1796099 6824047 := bstep (se 1 (by rfl) ⟨5118035, by rfl⟩ : syracuseStep 6824047 = 10236071) B10236071
theorem B121438379 : Blo 1796099 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B6062363 : Blo 1796099 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B2695679 : Blo 1796099 2695679 := bstep (se 1 (by rfl) ⟨2021759, by rfl⟩ : syracuseStep 2695679 = 4043519) B4043519
theorem B43722443 : Blo 1796099 43722443 := bstep (se 1 (by rfl) ⟨32791832, by rfl⟩ : syracuseStep 43722443 = 65583665) B65583665
theorem B3237979 : Blo 1796099 3237979 := bstep (se 1 (by rfl) ⟨2428484, by rfl⟩ : syracuseStep 3237979 = 4856969) B4856969
theorem B1796335 : Blo 1796099 1796335 := bstep (se 1 (by rfl) ⟨1347251, by rfl⟩ : syracuseStep 1796335 = 2694503) B2694503
theorem B1796935 : Blo 1796099 1796935 := bstep (se 1 (by rfl) ⟨1347701, by rfl⟩ : syracuseStep 1796935 = 2695403) B2695403
theorem B3033983 : Blo 1796099 3033983 := bstep (se 1 (by rfl) ⟨2275487, by rfl⟩ : syracuseStep 3033983 = 4550975) B4550975
theorem B4041953 : Blo 1796099 4041953 := bstep (se 2 (by rfl) ⟨1515732, by rfl⟩ : syracuseStep 4041953 = 3031465) B3031465
theorem B3411227 : Blo 1796099 3411227 := bstep (se 1 (by rfl) ⟨2558420, by rfl⟩ : syracuseStep 3411227 = 5116841) B5116841
theorem B1797679 : Blo 1796099 1797679 := bstep (se 1 (by rfl) ⟨1348259, by rfl⟩ : syracuseStep 1797679 = 2696519) B2696519
theorem B34533823 : Blo 1796099 34533823 := bstep (se 1 (by rfl) ⟨25900367, by rfl⟩ : syracuseStep 34533823 = 51800735) B51800735
theorem B56079215 : Blo 1796099 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B7674047 : Blo 1796099 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B15358207 : Blo 1796099 15358207 := bstep (se 1 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 15358207 = 23037311) B23037311
theorem B49159295 : Blo 1796099 49159295 := bstep (se 1 (by rfl) ⟨36869471, by rfl⟩ : syracuseStep 49159295 = 73738943) B73738943
theorem B4317305 : Blo 1796099 4317305 := bstep (se 2 (by rfl) ⟨1618989, by rfl⟩ : syracuseStep 4317305 = 3237979) B3237979
theorem B29148295 : Blo 1796099 29148295 := bstep (se 1 (by rfl) ⟨21861221, by rfl⟩ : syracuseStep 29148295 = 43722443) B43722443
theorem B4041575 : Blo 1796099 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B1797119 : Blo 1796099 1797119 := bstep (se 1 (by rfl) ⟨1347839, by rfl⟩ : syracuseStep 1797119 = 2695679) B2695679
theorem B5116031 : Blo 1796099 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B32772863 : Blo 1796099 32772863 := bstep (se 1 (by rfl) ⟨24579647, by rfl⟩ : syracuseStep 32772863 = 49159295) B49159295
theorem B2274151 : Blo 1796099 2274151 := bstep (se 1 (by rfl) ⟨1705613, by rfl⟩ : syracuseStep 2274151 = 3411227) B3411227
theorem B80958919 : Blo 1796099 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B9098729 : Blo 1796099 9098729 := bstep (se 2 (by rfl) ⟨3412023, by rfl⟩ : syracuseStep 9098729 = 6824047) B6824047
theorem B20477609 : Blo 1796099 20477609 := bstep (se 2 (by rfl) ⟨7679103, by rfl⟩ : syracuseStep 20477609 = 15358207) B15358207
theorem B37386143 : Blo 1796099 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B46045097 : Blo 1796099 46045097 := bstep (se 2 (by rfl) ⟨17266911, by rfl⟩ : syracuseStep 46045097 = 34533823) B34533823
theorem B2022655 : Blo 1796099 2022655 := bstep (se 1 (by rfl) ⟨1516991, by rfl⟩ : syracuseStep 2022655 = 3033983) B3033983
theorem B2694635 : Blo 1796099 2694635 := bstep (se 1 (by rfl) ⟨2020976, by rfl⟩ : syracuseStep 2694635 = 4041953) B4041953
theorem B21848575 : Blo 1796099 21848575 := bstep (se 1 (by rfl) ⟨16386431, by rfl⟩ : syracuseStep 21848575 = 32772863) B32772863
theorem B3032201 : Blo 1796099 3032201 := bstep (se 2 (by rfl) ⟨1137075, by rfl⟩ : syracuseStep 3032201 = 2274151) B2274151
theorem B30696731 : Blo 1796099 30696731 := bstep (se 1 (by rfl) ⟨23022548, by rfl⟩ : syracuseStep 30696731 = 46045097) B46045097
theorem B38864393 : Blo 1796099 38864393 := bstep (se 2 (by rfl) ⟨14574147, by rfl⟩ : syracuseStep 38864393 = 29148295) B29148295
theorem B2696873 : Blo 1796099 2696873 := bstep (se 2 (by rfl) ⟨1011327, by rfl⟩ : syracuseStep 2696873 = 2022655) B2022655
theorem B1796423 : Blo 1796099 1796423 := bstep (se 1 (by rfl) ⟨1347317, by rfl⟩ : syracuseStep 1796423 = 2694635) B2694635
theorem B3410687 : Blo 1796099 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B11512813 : Blo 1796099 11512813 := bstep (se 3 (by rfl) ⟨2158652, by rfl⟩ : syracuseStep 11512813 = 4317305) B4317305
theorem B6065819 : Blo 1796099 6065819 := bstep (se 1 (by rfl) ⟨4549364, by rfl⟩ : syracuseStep 6065819 = 9098729) B9098729
theorem B13651739 : Blo 1796099 13651739 := bstep (se 1 (by rfl) ⟨10238804, by rfl⟩ : syracuseStep 13651739 = 20477609) B20477609
theorem B24924095 : Blo 1796099 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B2694383 : Blo 1796099 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B107945225 : Blo 1796099 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B29131433 : Blo 1796099 29131433 := bstep (se 2 (by rfl) ⟨10924287, by rfl⟩ : syracuseStep 29131433 = 21848575) B21848575
theorem B20464487 : Blo 1796099 20464487 := bstep (se 1 (by rfl) ⟨15348365, by rfl⟩ : syracuseStep 20464487 = 30696731) B30696731
theorem B9095165 : Blo 1796099 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B1796255 : Blo 1796099 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B16616063 : Blo 1796099 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B1797915 : Blo 1796099 1797915 := bstep (se 1 (by rfl) ⟨1348436, by rfl⟩ : syracuseStep 1797915 = 2696873) B2696873
theorem B71963483 : Blo 1796099 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B4043879 : Blo 1796099 4043879 := bstep (se 1 (by rfl) ⟨3032909, by rfl⟩ : syracuseStep 4043879 = 6065819) B6065819
theorem B2021467 : Blo 1796099 2021467 := bstep (se 1 (by rfl) ⟨1516100, by rfl⟩ : syracuseStep 2021467 = 3032201) B3032201
theorem B25909595 : Blo 1796099 25909595 := bstep (se 1 (by rfl) ⟨19432196, by rfl⟩ : syracuseStep 25909595 = 38864393) B38864393
theorem B15350417 : Blo 1796099 15350417 := bstep (se 2 (by rfl) ⟨5756406, by rfl⟩ : syracuseStep 15350417 = 11512813) B11512813
theorem B9101159 : Blo 1796099 9101159 := bstep (se 1 (by rfl) ⟨6825869, by rfl⟩ : syracuseStep 9101159 = 13651739) B13651739
theorem B2695289 : Blo 1796099 2695289 := bstep (se 2 (by rfl) ⟨1010733, by rfl⟩ : syracuseStep 2695289 = 2021467) B2021467
theorem B2695919 : Blo 1796099 2695919 := bstep (se 1 (by rfl) ⟨2021939, by rfl⟩ : syracuseStep 2695919 = 4043879) B4043879
theorem B6063443 : Blo 1796099 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B10233611 : Blo 1796099 10233611 := bstep (se 1 (by rfl) ⟨7675208, by rfl⟩ : syracuseStep 10233611 = 15350417) B15350417
theorem B13642991 : Blo 1796099 13642991 := bstep (se 1 (by rfl) ⟨10232243, by rfl⟩ : syracuseStep 13642991 = 20464487) B20464487
theorem B17273063 : Blo 1796099 17273063 := bstep (se 1 (by rfl) ⟨12954797, by rfl⟩ : syracuseStep 17273063 = 25909595) B25909595
theorem B191902621 : Blo 1796099 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B6067439 : Blo 1796099 6067439 := bstep (se 1 (by rfl) ⟨4550579, by rfl⟩ : syracuseStep 6067439 = 9101159) B9101159
theorem B19420955 : Blo 1796099 19420955 := bstep (se 1 (by rfl) ⟨14565716, by rfl⟩ : syracuseStep 19420955 = 29131433) B29131433
theorem B44309501 : Blo 1796099 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B255870161 : Blo 1796099 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B9095327 : Blo 1796099 9095327 := bstep (se 1 (by rfl) ⟨6821495, by rfl⟩ : syracuseStep 9095327 = 13642991) B13642991
theorem B1796859 : Blo 1796099 1796859 := bstep (se 1 (by rfl) ⟨1347644, by rfl⟩ : syracuseStep 1796859 = 2695289) B2695289
theorem B1797279 : Blo 1796099 1797279 := bstep (se 1 (by rfl) ⟨1347959, by rfl⟩ : syracuseStep 1797279 = 2695919) B2695919
theorem B4042295 : Blo 1796099 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B12947303 : Blo 1796099 12947303 := bstep (se 1 (by rfl) ⟨9710477, by rfl⟩ : syracuseStep 12947303 = 19420955) B19420955
theorem B11515375 : Blo 1796099 11515375 := bstep (se 1 (by rfl) ⟨8636531, by rfl⟩ : syracuseStep 11515375 = 17273063) B17273063
theorem B4044959 : Blo 1796099 4044959 := bstep (se 1 (by rfl) ⟨3033719, by rfl⟩ : syracuseStep 4044959 = 6067439) B6067439
theorem B6822407 : Blo 1796099 6822407 := bstep (se 1 (by rfl) ⟨5116805, by rfl⟩ : syracuseStep 6822407 = 10233611) B10233611
theorem B29539667 : Blo 1796099 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B6063551 : Blo 1796099 6063551 := bstep (se 1 (by rfl) ⟨4547663, by rfl⟩ : syracuseStep 6063551 = 9095327) B9095327
theorem B2696639 : Blo 1796099 2696639 := bstep (se 1 (by rfl) ⟨2022479, by rfl⟩ : syracuseStep 2696639 = 4044959) B4044959
theorem B4548271 : Blo 1796099 4548271 := bstep (se 1 (by rfl) ⟨3411203, by rfl⟩ : syracuseStep 4548271 = 6822407) B6822407
theorem B15353833 : Blo 1796099 15353833 := bstep (se 2 (by rfl) ⟨5757687, by rfl⟩ : syracuseStep 15353833 = 11515375) B11515375
theorem B8631535 : Blo 1796099 8631535 := bstep (se 1 (by rfl) ⟨6473651, by rfl⟩ : syracuseStep 8631535 = 12947303) B12947303
theorem B170580107 : Blo 1796099 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B78772445 : Blo 1796099 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B2694863 : Blo 1796099 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B6064361 : Blo 1796099 6064361 := bstep (se 2 (by rfl) ⟨2274135, by rfl⟩ : syracuseStep 6064361 = 4548271) B4548271
theorem B1796575 : Blo 1796099 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B4042367 : Blo 1796099 4042367 := bstep (se 1 (by rfl) ⟨3031775, by rfl⟩ : syracuseStep 4042367 = 6063551) B6063551
theorem B1797759 : Blo 1796099 1797759 := bstep (se 1 (by rfl) ⟨1348319, by rfl⟩ : syracuseStep 1797759 = 2696639) B2696639
theorem B52514963 : Blo 1796099 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B113720071 : Blo 1796099 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B11508713 : Blo 1796099 11508713 := bstep (se 2 (by rfl) ⟨4315767, by rfl⟩ : syracuseStep 11508713 = 8631535) B8631535
theorem B20471777 : Blo 1796099 20471777 := bstep (se 2 (by rfl) ⟨7676916, by rfl⟩ : syracuseStep 20471777 = 15353833) B15353833
theorem B151626761 : Blo 1796099 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B4042907 : Blo 1796099 4042907 := bstep (se 1 (by rfl) ⟨3032180, by rfl⟩ : syracuseStep 4042907 = 6064361) B6064361
theorem B7672475 : Blo 1796099 7672475 := bstep (se 1 (by rfl) ⟨5754356, by rfl⟩ : syracuseStep 7672475 = 11508713) B11508713
theorem B35009975 : Blo 1796099 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B2694911 : Blo 1796099 2694911 := bstep (se 1 (by rfl) ⟨2021183, by rfl⟩ : syracuseStep 2694911 = 4042367) B4042367
theorem B13647851 : Blo 1796099 13647851 := bstep (se 1 (by rfl) ⟨10235888, by rfl⟩ : syracuseStep 13647851 = 20471777) B20471777
theorem B2695271 : Blo 1796099 2695271 := bstep (se 1 (by rfl) ⟨2021453, by rfl⟩ : syracuseStep 2695271 = 4042907) B4042907
theorem B23339983 : Blo 1796099 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B1796607 : Blo 1796099 1796607 := bstep (se 1 (by rfl) ⟨1347455, by rfl⟩ : syracuseStep 1796607 = 2694911) B2694911
theorem B5114983 : Blo 1796099 5114983 := bstep (se 1 (by rfl) ⟨3836237, by rfl⟩ : syracuseStep 5114983 = 7672475) B7672475
theorem B101084507 : Blo 1796099 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B9098567 : Blo 1796099 9098567 := bstep (se 1 (by rfl) ⟨6823925, by rfl⟩ : syracuseStep 9098567 = 13647851) B13647851
theorem B67389671 : Blo 1796099 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B1796847 : Blo 1796099 1796847 := bstep (se 1 (by rfl) ⟨1347635, by rfl⟩ : syracuseStep 1796847 = 2695271) B2695271
theorem B6065711 : Blo 1796099 6065711 := bstep (se 1 (by rfl) ⟨4549283, by rfl⟩ : syracuseStep 6065711 = 9098567) B9098567
theorem B6819977 : Blo 1796099 6819977 := bstep (se 2 (by rfl) ⟨2557491, by rfl⟩ : syracuseStep 6819977 = 5114983) B5114983
theorem B31119977 : Blo 1796099 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B4546651 : Blo 1796099 4546651 := bstep (se 1 (by rfl) ⟨3409988, by rfl⟩ : syracuseStep 4546651 = 6819977) B6819977
theorem B82986605 : Blo 1796099 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B4043807 : Blo 1796099 4043807 := bstep (se 1 (by rfl) ⟨3032855, by rfl⟩ : syracuseStep 4043807 = 6065711) B6065711
theorem B179705789 : Blo 1796099 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B6062201 : Blo 1796099 6062201 := bstep (se 2 (by rfl) ⟨2273325, by rfl⟩ : syracuseStep 6062201 = 4546651) B4546651
theorem B2695871 : Blo 1796099 2695871 := bstep (se 1 (by rfl) ⟨2021903, by rfl⟩ : syracuseStep 2695871 = 4043807) B4043807
theorem B55324403 : Blo 1796099 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B119803859 : Blo 1796099 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B36882935 : Blo 1796099 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B4041467 : Blo 1796099 4041467 := bstep (se 1 (by rfl) ⟨3031100, by rfl⟩ : syracuseStep 4041467 = 6062201) B6062201
theorem B1797247 : Blo 1796099 1797247 := bstep (se 1 (by rfl) ⟨1347935, by rfl⟩ : syracuseStep 1797247 = 2695871) B2695871
theorem B79869239 : Blo 1796099 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B24588623 : Blo 1796099 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B53246159 : Blo 1796099 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B2694311 : Blo 1796099 2694311 := bstep (se 1 (by rfl) ⟨2020733, by rfl⟩ : syracuseStep 2694311 = 4041467) B4041467
theorem B16392415 : Blo 1796099 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B35497439 : Blo 1796099 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B1796207 : Blo 1796099 1796207 := bstep (se 1 (by rfl) ⟨1347155, by rfl⟩ : syracuseStep 1796207 = 2694311) B2694311
theorem B21856553 : Blo 1796099 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B23664959 : Blo 1796099 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B14571035 : Blo 1796099 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B15776639 : Blo 1796099 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B9714023 : Blo 1796099 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B10517759 : Blo 1796099 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B6476015 : Blo 1796099 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B7011839 : Blo 1796099 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B4317343 : Blo 1796099 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B4674559 : Blo 1796099 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B23025829 : Blo 1796099 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B6232745 : Blo 1796099 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B30701105 : Blo 1796099 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B16620653 : Blo 1796099 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B44321741 : Blo 1796099 44321741 := bstep (se 3 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 44321741 = 16620653) B16620653
theorem B20467403 : Blo 1796099 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B13644935 : Blo 1796099 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B29547827 : Blo 1796099 29547827 := bstep (se 1 (by rfl) ⟨22160870, by rfl⟩ : syracuseStep 29547827 = 44321741) B44321741
theorem B9096623 : Blo 1796099 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B19698551 : Blo 1796099 19698551 := bstep (se 1 (by rfl) ⟨14773913, by rfl⟩ : syracuseStep 19698551 = 29547827) B29547827
theorem B13132367 : Blo 1796099 13132367 := bstep (se 1 (by rfl) ⟨9849275, by rfl⟩ : syracuseStep 13132367 = 19698551) B19698551
theorem B6064415 : Blo 1796099 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B4042943 : Blo 1796099 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B8754911 : Blo 1796099 8754911 := bstep (se 1 (by rfl) ⟨6566183, by rfl⟩ : syracuseStep 8754911 = 13132367) B13132367
theorem B2695295 : Blo 1796099 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B5836607 : Blo 1796099 5836607 := bstep (se 1 (by rfl) ⟨4377455, by rfl⟩ : syracuseStep 5836607 = 8754911) B8754911
theorem B1796863 : Blo 1796099 1796863 := bstep (se 1 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 1796863 = 2695295) B2695295
theorem B3891071 : Blo 1796099 3891071 := bstep (se 1 (by rfl) ⟨2918303, by rfl⟩ : syracuseStep 3891071 = 5836607) B5836607
theorem B10376189 : Blo 1796099 10376189 := bstep (se 3 (by rfl) ⟨1945535, by rfl⟩ : syracuseStep 10376189 = 3891071) B3891071
theorem B6917459 : Blo 1796099 6917459 := bstep (se 1 (by rfl) ⟨5188094, by rfl⟩ : syracuseStep 6917459 = 10376189) B10376189
theorem B18446557 : Blo 1796099 18446557 := bstep (se 3 (by rfl) ⟨3458729, by rfl⟩ : syracuseStep 18446557 = 6917459) B6917459
theorem B24595409 : Blo 1796099 24595409 := bstep (se 2 (by rfl) ⟨9223278, by rfl⟩ : syracuseStep 24595409 = 18446557) B18446557
theorem B16396939 : Blo 1796099 16396939 := bstep (se 1 (by rfl) ⟨12297704, by rfl⟩ : syracuseStep 16396939 = 24595409) B24595409
theorem B21862585 : Blo 1796099 21862585 := bstep (se 2 (by rfl) ⟨8198469, by rfl⟩ : syracuseStep 21862585 = 16396939) B16396939
theorem B29150113 : Blo 1796099 29150113 := bstep (se 2 (by rfl) ⟨10931292, by rfl⟩ : syracuseStep 29150113 = 21862585) B21862585
theorem B38866817 : Blo 1796099 38866817 := bstep (se 2 (by rfl) ⟨14575056, by rfl⟩ : syracuseStep 38866817 = 29150113) B29150113
theorem B25911211 : Blo 1796099 25911211 := bstep (se 1 (by rfl) ⟨19433408, by rfl⟩ : syracuseStep 25911211 = 38866817) B38866817
theorem B34548281 : Blo 1796099 34548281 := bstep (se 2 (by rfl) ⟨12955605, by rfl⟩ : syracuseStep 34548281 = 25911211) B25911211
theorem B23032187 : Blo 1796099 23032187 := bstep (se 1 (by rfl) ⟨17274140, by rfl⟩ : syracuseStep 23032187 = 34548281) B34548281
theorem B15354791 : Blo 1796099 15354791 := bstep (se 1 (by rfl) ⟨11516093, by rfl⟩ : syracuseStep 15354791 = 23032187) B23032187
theorem B10236527 : Blo 1796099 10236527 := bstep (se 1 (by rfl) ⟨7677395, by rfl⟩ : syracuseStep 10236527 = 15354791) B15354791
theorem B6824351 : Blo 1796099 6824351 := bstep (se 1 (by rfl) ⟨5118263, by rfl⟩ : syracuseStep 6824351 = 10236527) B10236527
theorem B4549567 : Blo 1796099 4549567 := bstep (se 1 (by rfl) ⟨3412175, by rfl⟩ : syracuseStep 4549567 = 6824351) B6824351
theorem B6066089 : Blo 1796099 6066089 := bstep (se 2 (by rfl) ⟨2274783, by rfl⟩ : syracuseStep 6066089 = 4549567) B4549567
theorem B4044059 : Blo 1796099 4044059 := bstep (se 1 (by rfl) ⟨3033044, by rfl⟩ : syracuseStep 4044059 = 6066089) B6066089
theorem B2696039 : Blo 1796099 2696039 := bstep (se 1 (by rfl) ⟨2022029, by rfl⟩ : syracuseStep 2696039 = 4044059) B4044059
theorem B1797359 : Blo 1796099 1797359 := bstep (se 1 (by rfl) ⟨1348019, by rfl⟩ : syracuseStep 1797359 = 2696039) B2696039

theorem C0 (j : ℕ) (h1 : 449024 ≤ j) (h2 : j ≤ 449524) : Blo 1796099 (4 * j + 3) := by
  interval_cases j
  · exact B1796099
  · exact B1796103
  · exact B1796107
  · exact B1796111
  · exact B1796115
  · exact B1796119
  · exact B1796123
  · exact B1796127
  · exact B1796131
  · exact B1796135
  · exact B1796139
  · exact B1796143
  · exact B1796147
  · exact B1796151
  · exact B1796155
  · exact B1796159
  · exact B1796163
  · exact B1796167
  · exact B1796171
  · exact B1796175
  · exact B1796179
  · exact B1796183
  · exact B1796187
  · exact B1796191
  · exact B1796195
  · exact B1796199
  · exact B1796203
  · exact B1796207
  · exact B1796211
  · exact B1796215
  · exact B1796219
  · exact B1796223
  · exact B1796227
  · exact B1796231
  · exact B1796235
  · exact B1796239
  · exact B1796243
  · exact B1796247
  · exact B1796251
  · exact B1796255
  · exact B1796259
  · exact B1796263
  · exact B1796267
  · exact B1796271
  · exact B1796275
  · exact B1796279
  · exact B1796283
  · exact B1796287
  · exact B1796291
  · exact B1796295
  · exact B1796299
  · exact B1796303
  · exact B1796307
  · exact B1796311
  · exact B1796315
  · exact B1796319
  · exact B1796323
  · exact B1796327
  · exact B1796331
  · exact B1796335
  · exact B1796339
  · exact B1796343
  · exact B1796347
  · exact B1796351
  · exact B1796355
  · exact B1796359
  · exact B1796363
  · exact B1796367
  · exact B1796371
  · exact B1796375
  · exact B1796379
  · exact B1796383
  · exact B1796387
  · exact B1796391
  · exact B1796395
  · exact B1796399
  · exact B1796403
  · exact B1796407
  · exact B1796411
  · exact B1796415
  · exact B1796419
  · exact B1796423
  · exact B1796427
  · exact B1796431
  · exact B1796435
  · exact B1796439
  · exact B1796443
  · exact B1796447
  · exact B1796451
  · exact B1796455
  · exact B1796459
  · exact B1796463
  · exact B1796467
  · exact B1796471
  · exact B1796475
  · exact B1796479
  · exact B1796483
  · exact B1796487
  · exact B1796491
  · exact B1796495
  · exact B1796499
  · exact B1796503
  · exact B1796507
  · exact B1796511
  · exact B1796515
  · exact B1796519
  · exact B1796523
  · exact B1796527
  · exact B1796531
  · exact B1796535
  · exact B1796539
  · exact B1796543
  · exact B1796547
  · exact B1796551
  · exact B1796555
  · exact B1796559
  · exact B1796563
  · exact B1796567
  · exact B1796571
  · exact B1796575
  · exact B1796579
  · exact B1796583
  · exact B1796587
  · exact B1796591
  · exact B1796595
  · exact B1796599
  · exact B1796603
  · exact B1796607
  · exact B1796611
  · exact B1796615
  · exact B1796619
  · exact B1796623
  · exact B1796627
  · exact B1796631
  · exact B1796635
  · exact B1796639
  · exact B1796643
  · exact B1796647
  · exact B1796651
  · exact B1796655
  · exact B1796659
  · exact B1796663
  · exact B1796667
  · exact B1796671
  · exact B1796675
  · exact B1796679
  · exact B1796683
  · exact B1796687
  · exact B1796691
  · exact B1796695
  · exact B1796699
  · exact B1796703
  · exact B1796707
  · exact B1796711
  · exact B1796715
  · exact B1796719
  · exact B1796723
  · exact B1796727
  · exact B1796731
  · exact B1796735
  · exact B1796739
  · exact B1796743
  · exact B1796747
  · exact B1796751
  · exact B1796755
  · exact B1796759
  · exact B1796763
  · exact B1796767
  · exact B1796771
  · exact B1796775
  · exact B1796779
  · exact B1796783
  · exact B1796787
  · exact B1796791
  · exact B1796795
  · exact B1796799
  · exact B1796803
  · exact B1796807
  · exact B1796811
  · exact B1796815
  · exact B1796819
  · exact B1796823
  · exact B1796827
  · exact B1796831
  · exact B1796835
  · exact B1796839
  · exact B1796843
  · exact B1796847
  · exact B1796851
  · exact B1796855
  · exact B1796859
  · exact B1796863
  · exact B1796867
  · exact B1796871
  · exact B1796875
  · exact B1796879
  · exact B1796883
  · exact B1796887
  · exact B1796891
  · exact B1796895
  · exact B1796899
  · exact B1796903
  · exact B1796907
  · exact B1796911
  · exact B1796915
  · exact B1796919
  · exact B1796923
  · exact B1796927
  · exact B1796931
  · exact B1796935
  · exact B1796939
  · exact B1796943
  · exact B1796947
  · exact B1796951
  · exact B1796955
  · exact B1796959
  · exact B1796963
  · exact B1796967
  · exact B1796971
  · exact B1796975
  · exact B1796979
  · exact B1796983
  · exact B1796987
  · exact B1796991
  · exact B1796995
  · exact B1796999
  · exact B1797003
  · exact B1797007
  · exact B1797011
  · exact B1797015
  · exact B1797019
  · exact B1797023
  · exact B1797027
  · exact B1797031
  · exact B1797035
  · exact B1797039
  · exact B1797043
  · exact B1797047
  · exact B1797051
  · exact B1797055
  · exact B1797059
  · exact B1797063
  · exact B1797067
  · exact B1797071
  · exact B1797075
  · exact B1797079
  · exact B1797083
  · exact B1797087
  · exact B1797091
  · exact B1797095
  · exact B1797099
  · exact B1797103
  · exact B1797107
  · exact B1797111
  · exact B1797115
  · exact B1797119
  · exact B1797123
  · exact B1797127
  · exact B1797131
  · exact B1797135
  · exact B1797139
  · exact B1797143
  · exact B1797147
  · exact B1797151
  · exact B1797155
  · exact B1797159
  · exact B1797163
  · exact B1797167
  · exact B1797171
  · exact B1797175
  · exact B1797179
  · exact B1797183
  · exact B1797187
  · exact B1797191
  · exact B1797195
  · exact B1797199
  · exact B1797203
  · exact B1797207
  · exact B1797211
  · exact B1797215
  · exact B1797219
  · exact B1797223
  · exact B1797227
  · exact B1797231
  · exact B1797235
  · exact B1797239
  · exact B1797243
  · exact B1797247
  · exact B1797251
  · exact B1797255
  · exact B1797259
  · exact B1797263
  · exact B1797267
  · exact B1797271
  · exact B1797275
  · exact B1797279
  · exact B1797283
  · exact B1797287
  · exact B1797291
  · exact B1797295
  · exact B1797299
  · exact B1797303
  · exact B1797307
  · exact B1797311
  · exact B1797315
  · exact B1797319
  · exact B1797323
  · exact B1797327
  · exact B1797331
  · exact B1797335
  · exact B1797339
  · exact B1797343
  · exact B1797347
  · exact B1797351
  · exact B1797355
  · exact B1797359
  · exact B1797363
  · exact B1797367
  · exact B1797371
  · exact B1797375
  · exact B1797379
  · exact B1797383
  · exact B1797387
  · exact B1797391
  · exact B1797395
  · exact B1797399
  · exact B1797403
  · exact B1797407
  · exact B1797411
  · exact B1797415
  · exact B1797419
  · exact B1797423
  · exact B1797427
  · exact B1797431
  · exact B1797435
  · exact B1797439
  · exact B1797443
  · exact B1797447
  · exact B1797451
  · exact B1797455
  · exact B1797459
  · exact B1797463
  · exact B1797467
  · exact B1797471
  · exact B1797475
  · exact B1797479
  · exact B1797483
  · exact B1797487
  · exact B1797491
  · exact B1797495
  · exact B1797499
  · exact B1797503
  · exact B1797507
  · exact B1797511
  · exact B1797515
  · exact B1797519
  · exact B1797523
  · exact B1797527
  · exact B1797531
  · exact B1797535
  · exact B1797539
  · exact B1797543
  · exact B1797547
  · exact B1797551
  · exact B1797555
  · exact B1797559
  · exact B1797563
  · exact B1797567
  · exact B1797571
  · exact B1797575
  · exact B1797579
  · exact B1797583
  · exact B1797587
  · exact B1797591
  · exact B1797595
  · exact B1797599
  · exact B1797603
  · exact B1797607
  · exact B1797611
  · exact B1797615
  · exact B1797619
  · exact B1797623
  · exact B1797627
  · exact B1797631
  · exact B1797635
  · exact B1797639
  · exact B1797643
  · exact B1797647
  · exact B1797651
  · exact B1797655
  · exact B1797659
  · exact B1797663
  · exact B1797667
  · exact B1797671
  · exact B1797675
  · exact B1797679
  · exact B1797683
  · exact B1797687
  · exact B1797691
  · exact B1797695
  · exact B1797699
  · exact B1797703
  · exact B1797707
  · exact B1797711
  · exact B1797715
  · exact B1797719
  · exact B1797723
  · exact B1797727
  · exact B1797731
  · exact B1797735
  · exact B1797739
  · exact B1797743
  · exact B1797747
  · exact B1797751
  · exact B1797755
  · exact B1797759
  · exact B1797763
  · exact B1797767
  · exact B1797771
  · exact B1797775
  · exact B1797779
  · exact B1797783
  · exact B1797787
  · exact B1797791
  · exact B1797795
  · exact B1797799
  · exact B1797803
  · exact B1797807
  · exact B1797811
  · exact B1797815
  · exact B1797819
  · exact B1797823
  · exact B1797827
  · exact B1797831
  · exact B1797835
  · exact B1797839
  · exact B1797843
  · exact B1797847
  · exact B1797851
  · exact B1797855
  · exact B1797859
  · exact B1797863
  · exact B1797867
  · exact B1797871
  · exact B1797875
  · exact B1797879
  · exact B1797883
  · exact B1797887
  · exact B1797891
  · exact B1797895
  · exact B1797899
  · exact B1797903
  · exact B1797907
  · exact B1797911
  · exact B1797915
  · exact B1797919
  · exact B1797923
  · exact B1797927
  · exact B1797931
  · exact B1797935
  · exact B1797939
  · exact B1797943
  · exact B1797947
  · exact B1797951
  · exact B1797955
  · exact B1797959
  · exact B1797963
  · exact B1797967
  · exact B1797971
  · exact B1797975
  · exact B1797979
  · exact B1797983
  · exact B1797987
  · exact B1797991
  · exact B1797995
  · exact B1797999
  · exact B1798003
  · exact B1798007
  · exact B1798011
  · exact B1798015
  · exact B1798019
  · exact B1798023
  · exact B1798027
  · exact B1798031
  · exact B1798035
  · exact B1798039
  · exact B1798043
  · exact B1798047
  · exact B1798051
  · exact B1798055
  · exact B1798059
  · exact B1798063
  · exact B1798067
  · exact B1798071
  · exact B1798075
  · exact B1798079
  · exact B1798083
  · exact B1798087
  · exact B1798091
  · exact B1798095
  · exact B1798099

theorem solution (m : ℕ) (hlo : 1796099 ≤ m) (hhi : m ≤ 1798099) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 449024 ≤ j := by omega
    have hj2 : j ≤ 449524 := by omega
    have hb : Blo 1796099 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
