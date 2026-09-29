-- Prove2me | solution 1 for syracuse_descends_range_1222929_1224429
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:59.075615+00:00
-- url     : https://prove2.me/submissions/de3184c5-fd1e-4520-8ddc-760e16bd07c3

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


theorem B1376257 : Blo 1222929 1376257 := bbase (se 2 (by rfl) ⟨516096, by rfl⟩ : syracuseStep 1376257 = 1032193) (by norm_num)
theorem B3096589 : Blo 1222929 3096589 := bbase (se 3 (by rfl) ⟨580610, by rfl⟩ : syracuseStep 3096589 = 1161221) (by norm_num)
theorem B1835021 : Blo 1222929 1835021 := bbase (se 3 (by rfl) ⟨344066, by rfl⟩ : syracuseStep 1835021 = 688133) (by norm_num)
theorem B2752541 : Blo 1222929 2752541 := bbase (se 3 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 2752541 = 1032203) (by norm_num)
theorem B2064413 : Blo 1222929 2064413 := bbase (se 3 (by rfl) ⟨387077, by rfl⟩ : syracuseStep 2064413 = 774155) (by norm_num)
theorem B1835045 : Blo 1222929 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B1548325 : Blo 1222929 1548325 := bbase (se 4 (by rfl) ⟨145155, by rfl⟩ : syracuseStep 1548325 = 290311) (by norm_num)
theorem B1376293 : Blo 1222929 1376293 := bbase (se 4 (by rfl) ⟨129027, by rfl⟩ : syracuseStep 1376293 = 258055) (by norm_num)
theorem B1835069 : Blo 1222929 1835069 := bbase (se 3 (by rfl) ⟨344075, by rfl⟩ : syracuseStep 1835069 = 688151) (by norm_num)
theorem B1376329 : Blo 1222929 1376329 := bbase (se 2 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 1376329 = 1032247) (by norm_num)
theorem B1835093 : Blo 1222929 1835093 := bbase (se 8 (by rfl) ⟨10752, by rfl⟩ : syracuseStep 1835093 = 21505) (by norm_num)
theorem B2752613 : Blo 1222929 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B1835117 : Blo 1222929 1835117 := bbase (se 3 (by rfl) ⟨344084, by rfl⟩ : syracuseStep 1835117 = 688169) (by norm_num)
theorem B1376365 : Blo 1222929 1376365 := bbase (se 3 (by rfl) ⟨258068, by rfl⟩ : syracuseStep 1376365 = 516137) (by norm_num)
theorem B3096701 : Blo 1222929 3096701 := bbase (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) (by norm_num)
theorem B1835141 : Blo 1222929 1835141 := bbase (se 4 (by rfl) ⟨172044, by rfl⟩ : syracuseStep 1835141 = 344089) (by norm_num)
theorem B1376401 : Blo 1222929 1376401 := bbase (se 2 (by rfl) ⟨516150, by rfl⟩ : syracuseStep 1376401 = 1032301) (by norm_num)
theorem B2613397 : Blo 1222929 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B2064541 : Blo 1222929 2064541 := bbase (se 3 (by rfl) ⟨387101, by rfl⟩ : syracuseStep 2064541 = 774203) (by norm_num)
theorem B1835165 : Blo 1222929 1835165 := bbase (se 3 (by rfl) ⟨344093, by rfl⟩ : syracuseStep 1835165 = 688187) (by norm_num)
theorem B2752685 : Blo 1222929 2752685 := bbase (se 3 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 2752685 = 1032257) (by norm_num)
theorem B2515117 : Blo 1222929 2515117 := bbase (se 3 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 2515117 = 943169) (by norm_num)
theorem B1835189 : Blo 1222929 1835189 := bbase (se 5 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 1835189 = 172049) (by norm_num)
theorem B1376437 : Blo 1222929 1376437 := bbase (se 5 (by rfl) ⟨64520, by rfl⟩ : syracuseStep 1376437 = 129041) (by norm_num)
theorem B1835213 : Blo 1222929 1835213 := bbase (se 3 (by rfl) ⟨344102, by rfl⟩ : syracuseStep 1835213 = 688205) (by norm_num)
theorem B1548497 : Blo 1222929 1548497 := bbase (se 2 (by rfl) ⟨580686, by rfl⟩ : syracuseStep 1548497 = 1161373) (by norm_num)
theorem B1376473 : Blo 1222929 1376473 := bbase (se 2 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 1376473 = 1032355) (by norm_num)
theorem B1835237 : Blo 1222929 1835237 := bbase (se 4 (by rfl) ⟨172053, by rfl⟩ : syracuseStep 1835237 = 344107) (by norm_num)
theorem B2515181 : Blo 1222929 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B2752757 : Blo 1222929 2752757 := bbase (se 5 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 2752757 = 258071) (by norm_num)
theorem B2064629 : Blo 1222929 2064629 := bbase (se 5 (by rfl) ⟨96779, by rfl⟩ : syracuseStep 2064629 = 193559) (by norm_num)
theorem B1835261 : Blo 1222929 1835261 := bbase (se 3 (by rfl) ⟨344111, by rfl⟩ : syracuseStep 1835261 = 688223) (by norm_num)
theorem B1376509 : Blo 1222929 1376509 := bbase (se 3 (by rfl) ⟨258095, by rfl⟩ : syracuseStep 1376509 = 516191) (by norm_num)
theorem B1548553 : Blo 1222929 1548553 := bbase (se 2 (by rfl) ⟨580707, by rfl⟩ : syracuseStep 1548553 = 1161415) (by norm_num)
theorem B1835285 : Blo 1222929 1835285 := bbase (se 6 (by rfl) ⟨43014, by rfl⟩ : syracuseStep 1835285 = 86029) (by norm_num)
theorem B1376545 : Blo 1222929 1376545 := bbase (se 2 (by rfl) ⟨516204, by rfl⟩ : syracuseStep 1376545 = 1032409) (by norm_num)
theorem B1835309 : Blo 1222929 1835309 := bbase (se 3 (by rfl) ⟨344120, by rfl⟩ : syracuseStep 1835309 = 688241) (by norm_num)
theorem B3096893 : Blo 1222929 3096893 := bbase (se 3 (by rfl) ⟨580667, by rfl⟩ : syracuseStep 3096893 = 1161335) (by norm_num)
theorem B2752829 : Blo 1222929 2752829 := bbase (se 3 (by rfl) ⟨516155, by rfl⟩ : syracuseStep 2752829 = 1032311) (by norm_num)
theorem B1835333 : Blo 1222929 1835333 := bbase (se 4 (by rfl) ⟨172062, by rfl⟩ : syracuseStep 1835333 = 344125) (by norm_num)
theorem B1376581 : Blo 1222929 1376581 := bbase (se 4 (by rfl) ⟨129054, by rfl⟩ : syracuseStep 1376581 = 258109) (by norm_num)
theorem B4129109 : Blo 1222929 4129109 := bbase (se 10 (by rfl) ⟨6048, by rfl⟩ : syracuseStep 4129109 = 12097) (by norm_num)
theorem B1835357 : Blo 1222929 1835357 := bbase (se 3 (by rfl) ⟨344129, by rfl⟩ : syracuseStep 1835357 = 688259) (by norm_num)
theorem B1548649 : Blo 1222929 1548649 := bbase (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) (by norm_num)
theorem B1376617 : Blo 1222929 1376617 := bbase (se 2 (by rfl) ⟨516231, by rfl⟩ : syracuseStep 1376617 = 1032463) (by norm_num)
theorem B2064757 : Blo 1222929 2064757 := bbase (se 5 (by rfl) ⟨96785, by rfl⟩ : syracuseStep 2064757 = 193571) (by norm_num)
theorem B1835381 : Blo 1222929 1835381 := bbase (se 5 (by rfl) ⟨86033, by rfl⟩ : syracuseStep 1835381 = 172067) (by norm_num)
theorem B2752901 : Blo 1222929 2752901 := bbase (se 4 (by rfl) ⟨258084, by rfl⟩ : syracuseStep 2752901 = 516169) (by norm_num)
theorem B1835405 : Blo 1222929 1835405 := bbase (se 3 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 1835405 = 688277) (by norm_num)
theorem B1376653 : Blo 1222929 1376653 := bbase (se 3 (by rfl) ⟨258122, by rfl⟩ : syracuseStep 1376653 = 516245) (by norm_num)
theorem B1835429 : Blo 1222929 1835429 := bbase (se 4 (by rfl) ⟨172071, by rfl⟩ : syracuseStep 1835429 = 344143) (by norm_num)
theorem B1376689 : Blo 1222929 1376689 := bbase (se 2 (by rfl) ⟨516258, by rfl⟩ : syracuseStep 1376689 = 1032517) (by norm_num)
theorem B1835453 : Blo 1222929 1835453 := bbase (se 3 (by rfl) ⟨344147, by rfl⟩ : syracuseStep 1835453 = 688295) (by norm_num)
theorem B2752973 : Blo 1222929 2752973 := bbase (se 3 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 2752973 = 1032365) (by norm_num)
theorem B2064845 : Blo 1222929 2064845 := bbase (se 3 (by rfl) ⟨387158, by rfl⟩ : syracuseStep 2064845 = 774317) (by norm_num)
theorem B1835477 : Blo 1222929 1835477 := bbase (se 7 (by rfl) ⟨21509, by rfl⟩ : syracuseStep 1835477 = 43019) (by norm_num)
theorem B1376725 : Blo 1222929 1376725 := bbase (se 7 (by rfl) ⟨16133, by rfl⟩ : syracuseStep 1376725 = 32267) (by norm_num)
theorem B1835501 : Blo 1222929 1835501 := bbase (se 3 (by rfl) ⟨344156, by rfl⟩ : syracuseStep 1835501 = 688313) (by norm_num)
theorem B1376761 : Blo 1222929 1376761 := bbase (se 2 (by rfl) ⟨516285, by rfl⟩ : syracuseStep 1376761 = 1032571) (by norm_num)
theorem B1835525 : Blo 1222929 1835525 := bbase (se 4 (by rfl) ⟨172080, by rfl⟩ : syracuseStep 1835525 = 344161) (by norm_num)
theorem B2753045 : Blo 1222929 2753045 := bbase (se 6 (by rfl) ⟨64524, by rfl⟩ : syracuseStep 2753045 = 129049) (by norm_num)
theorem B1548821 : Blo 1222929 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B1835549 : Blo 1222929 1835549 := bbase (se 3 (by rfl) ⟨344165, by rfl⟩ : syracuseStep 1835549 = 688331) (by norm_num)
theorem B1376797 : Blo 1222929 1376797 := bbase (se 3 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 1376797 = 516299) (by norm_num)
theorem B1835573 : Blo 1222929 1835573 := bbase (se 5 (by rfl) ⟨86042, by rfl⟩ : syracuseStep 1835573 = 172085) (by norm_num)
theorem B1376833 : Blo 1222929 1376833 := bbase (se 2 (by rfl) ⟨516312, by rfl⟩ : syracuseStep 1376833 = 1032625) (by norm_num)
theorem B2064973 : Blo 1222929 2064973 := bbase (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) (by norm_num)
theorem B1835597 : Blo 1222929 1835597 := bbase (se 3 (by rfl) ⟨344174, by rfl⟩ : syracuseStep 1835597 = 688349) (by norm_num)
theorem B1548877 : Blo 1222929 1548877 := bbase (se 3 (by rfl) ⟨290414, by rfl⟩ : syracuseStep 1548877 = 580829) (by norm_num)
theorem B2753117 : Blo 1222929 2753117 := bbase (se 3 (by rfl) ⟨516209, by rfl⟩ : syracuseStep 2753117 = 1032419) (by norm_num)
theorem B1835621 : Blo 1222929 1835621 := bbase (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) (by norm_num)
theorem B1376869 : Blo 1222929 1376869 := bbase (se 4 (by rfl) ⟨129081, by rfl⟩ : syracuseStep 1376869 = 258163) (by norm_num)
theorem B1835645 : Blo 1222929 1835645 := bbase (se 3 (by rfl) ⟨344183, by rfl⟩ : syracuseStep 1835645 = 688367) (by norm_num)
theorem B1376905 : Blo 1222929 1376905 := bbase (se 2 (by rfl) ⟨516339, by rfl⟩ : syracuseStep 1376905 = 1032679) (by norm_num)
theorem B3097237 : Blo 1222929 3097237 := bbase (se 6 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 3097237 = 145183) (by norm_num)
theorem B1835669 : Blo 1222929 1835669 := bbase (se 6 (by rfl) ⟨43023, by rfl⟩ : syracuseStep 1835669 = 86047) (by norm_num)
theorem B2753189 : Blo 1222929 2753189 := bbase (se 4 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 2753189 = 516223) (by norm_num)
theorem B2065061 : Blo 1222929 2065061 := bbase (se 4 (by rfl) ⟨193599, by rfl⟩ : syracuseStep 2065061 = 387199) (by norm_num)
theorem B1835693 : Blo 1222929 1835693 := bbase (se 3 (by rfl) ⟨344192, by rfl⟩ : syracuseStep 1835693 = 688385) (by norm_num)
theorem B1548973 : Blo 1222929 1548973 := bbase (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) (by norm_num)
theorem B1376941 : Blo 1222929 1376941 := bbase (se 3 (by rfl) ⟨258176, by rfl⟩ : syracuseStep 1376941 = 516353) (by norm_num)
theorem B1835717 : Blo 1222929 1835717 := bbase (se 4 (by rfl) ⟨172098, by rfl⟩ : syracuseStep 1835717 = 344197) (by norm_num)
theorem B1376977 : Blo 1222929 1376977 := bbase (se 2 (by rfl) ⟨516366, by rfl⟩ : syracuseStep 1376977 = 1032733) (by norm_num)
theorem B1835741 : Blo 1222929 1835741 := bbase (se 3 (by rfl) ⟨344201, by rfl⟩ : syracuseStep 1835741 = 688403) (by norm_num)
theorem B2753261 : Blo 1222929 2753261 := bbase (se 3 (by rfl) ⟨516236, by rfl⟩ : syracuseStep 2753261 = 1032473) (by norm_num)
theorem B1835765 : Blo 1222929 1835765 := bbase (se 5 (by rfl) ⟨86051, by rfl⟩ : syracuseStep 1835765 = 172103) (by norm_num)
theorem B1377013 : Blo 1222929 1377013 := bbase (se 5 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 1377013 = 129095) (by norm_num)
theorem B4129541 : Blo 1222929 4129541 := bbase (se 4 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 4129541 = 774289) (by norm_num)
theorem B3097349 : Blo 1222929 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B1835789 : Blo 1222929 1835789 := bbase (se 3 (by rfl) ⟨344210, by rfl⟩ : syracuseStep 1835789 = 688421) (by norm_num)
theorem B1377049 : Blo 1222929 1377049 := bbase (se 2 (by rfl) ⟨516393, by rfl⟩ : syracuseStep 1377049 = 1032787) (by norm_num)
theorem B2065189 : Blo 1222929 2065189 := bbase (se 4 (by rfl) ⟨193611, by rfl⟩ : syracuseStep 2065189 = 387223) (by norm_num)
theorem B1835813 : Blo 1222929 1835813 := bbase (se 4 (by rfl) ⟨172107, by rfl⟩ : syracuseStep 1835813 = 344215) (by norm_num)
theorem B2753333 : Blo 1222929 2753333 := bbase (se 5 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 2753333 = 258125) (by norm_num)
theorem B1835837 : Blo 1222929 1835837 := bbase (se 3 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 1835837 = 688439) (by norm_num)
theorem B1377085 : Blo 1222929 1377085 := bbase (se 3 (by rfl) ⟨258203, by rfl⟩ : syracuseStep 1377085 = 516407) (by norm_num)
theorem B1835861 : Blo 1222929 1835861 := bbase (se 9 (by rfl) ⟨5378, by rfl⟩ : syracuseStep 1835861 = 10757) (by norm_num)
theorem B1549145 : Blo 1222929 1549145 := bbase (se 2 (by rfl) ⟨580929, by rfl⟩ : syracuseStep 1549145 = 1161859) (by norm_num)
theorem B1377121 : Blo 1222929 1377121 := bbase (se 2 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 1377121 = 1032841) (by norm_num)
theorem B1835885 : Blo 1222929 1835885 := bbase (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) (by norm_num)
theorem B2753405 : Blo 1222929 2753405 := bbase (se 3 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 2753405 = 1032527) (by norm_num)
theorem B2065277 : Blo 1222929 2065277 := bbase (se 3 (by rfl) ⟨387239, by rfl⟩ : syracuseStep 2065277 = 774479) (by norm_num)
theorem B1835909 : Blo 1222929 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B1377157 : Blo 1222929 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1549201 : Blo 1222929 1549201 := bbase (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) (by norm_num)
theorem B6194069 : Blo 1222929 6194069 := bbase (se 6 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 6194069 = 290347) (by norm_num)
theorem B4645781 : Blo 1222929 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B1835933 : Blo 1222929 1835933 := bbase (se 3 (by rfl) ⟨344237, by rfl⟩ : syracuseStep 1835933 = 688475) (by norm_num)
theorem B1377193 : Blo 1222929 1377193 := bbase (se 2 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 1377193 = 1032895) (by norm_num)
theorem B1835957 : Blo 1222929 1835957 := bbase (se 5 (by rfl) ⟨86060, by rfl⟩ : syracuseStep 1835957 = 172121) (by norm_num)
theorem B3097541 : Blo 1222929 3097541 := bbase (se 4 (by rfl) ⟨290394, by rfl⟩ : syracuseStep 3097541 = 580789) (by norm_num)
theorem B2753477 : Blo 1222929 2753477 := bbase (se 4 (by rfl) ⟨258138, by rfl⟩ : syracuseStep 2753477 = 516277) (by norm_num)
theorem B1835981 : Blo 1222929 1835981 := bbase (se 3 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 1835981 = 688493) (by norm_num)
theorem B1377229 : Blo 1222929 1377229 := bbase (se 3 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 1377229 = 516461) (by norm_num)
theorem B1836005 : Blo 1222929 1836005 := bbase (se 4 (by rfl) ⟨172125, by rfl⟩ : syracuseStep 1836005 = 344251) (by norm_num)
theorem B1549297 : Blo 1222929 1549297 := bbase (se 2 (by rfl) ⟨580986, by rfl⟩ : syracuseStep 1549297 = 1161973) (by norm_num)
theorem B1377265 : Blo 1222929 1377265 := bbase (se 2 (by rfl) ⟨516474, by rfl⟩ : syracuseStep 1377265 = 1032949) (by norm_num)
theorem B2065405 : Blo 1222929 2065405 := bbase (se 3 (by rfl) ⟨387263, by rfl⟩ : syracuseStep 2065405 = 774527) (by norm_num)
theorem B1836029 : Blo 1222929 1836029 := bbase (se 3 (by rfl) ⟨344255, by rfl⟩ : syracuseStep 1836029 = 688511) (by norm_num)
theorem B2753549 : Blo 1222929 2753549 := bbase (se 3 (by rfl) ⟨516290, by rfl⟩ : syracuseStep 2753549 = 1032581) (by norm_num)
theorem B2614285 : Blo 1222929 2614285 := bbase (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) (by norm_num)
theorem B1836053 : Blo 1222929 1836053 := bbase (se 6 (by rfl) ⟨43032, by rfl⟩ : syracuseStep 1836053 = 86065) (by norm_num)
theorem B1377301 : Blo 1222929 1377301 := bbase (se 6 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 1377301 = 64561) (by norm_num)
theorem B2204701 : Blo 1222929 2204701 := bbase (se 3 (by rfl) ⟨413381, by rfl⟩ : syracuseStep 2204701 = 826763) (by norm_num)
theorem B1836077 : Blo 1222929 1836077 := bbase (se 3 (by rfl) ⟨344264, by rfl⟩ : syracuseStep 1836077 = 688529) (by norm_num)
theorem B1377337 : Blo 1222929 1377337 := bbase (se 2 (by rfl) ⟨516501, by rfl⟩ : syracuseStep 1377337 = 1033003) (by norm_num)
theorem B1836101 : Blo 1222929 1836101 := bbase (se 4 (by rfl) ⟨172134, by rfl⟩ : syracuseStep 1836101 = 344269) (by norm_num)
theorem B2753621 : Blo 1222929 2753621 := bbase (se 8 (by rfl) ⟨16134, by rfl⟩ : syracuseStep 2753621 = 32269) (by norm_num)
theorem B2065493 : Blo 1222929 2065493 := bbase (se 8 (by rfl) ⟨12102, by rfl⟩ : syracuseStep 2065493 = 24205) (by norm_num)
theorem B1836125 : Blo 1222929 1836125 := bbase (se 3 (by rfl) ⟨344273, by rfl⟩ : syracuseStep 1836125 = 688547) (by norm_num)
theorem B1377373 : Blo 1222929 1377373 := bbase (se 3 (by rfl) ⟨258257, by rfl⟩ : syracuseStep 1377373 = 516515) (by norm_num)
theorem B1836149 : Blo 1222929 1836149 := bbase (se 5 (by rfl) ⟨86069, by rfl⟩ : syracuseStep 1836149 = 172139) (by norm_num)
theorem B1377409 : Blo 1222929 1377409 := bbase (se 2 (by rfl) ⟨516528, by rfl⟩ : syracuseStep 1377409 = 1033057) (by norm_num)
theorem B1836173 : Blo 1222929 1836173 := bbase (se 3 (by rfl) ⟨344282, by rfl⟩ : syracuseStep 1836173 = 688565) (by norm_num)
theorem B2753693 : Blo 1222929 2753693 := bbase (se 3 (by rfl) ⟨516317, by rfl⟩ : syracuseStep 2753693 = 1032635) (by norm_num)
theorem B1549469 : Blo 1222929 1549469 := bbase (se 3 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 1549469 = 581051) (by norm_num)
theorem B1836197 : Blo 1222929 1836197 := bbase (se 4 (by rfl) ⟨172143, by rfl⟩ : syracuseStep 1836197 = 344287) (by norm_num)
theorem B1377445 : Blo 1222929 1377445 := bbase (se 4 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 1377445 = 258271) (by norm_num)
theorem B4646069 : Blo 1222929 4646069 := bbase (se 5 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 4646069 = 435569) (by norm_num)
theorem B4129973 : Blo 1222929 4129973 := bbase (se 5 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 4129973 = 387185) (by norm_num)
theorem B1836221 : Blo 1222929 1836221 := bbase (se 3 (by rfl) ⟨344291, by rfl⟩ : syracuseStep 1836221 = 688583) (by norm_num)
theorem B1377481 : Blo 1222929 1377481 := bbase (se 2 (by rfl) ⟨516555, by rfl⟩ : syracuseStep 1377481 = 1033111) (by norm_num)
theorem B1959125 : Blo 1222929 1959125 := bbase (se 7 (by rfl) ⟨22958, by rfl⟩ : syracuseStep 1959125 = 45917) (by norm_num)
theorem B3679445 : Blo 1222929 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2065621 : Blo 1222929 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B1836245 : Blo 1222929 1836245 := bbase (se 7 (by rfl) ⟨21518, by rfl⟩ : syracuseStep 1836245 = 43037) (by norm_num)
theorem B1549525 : Blo 1222929 1549525 := bbase (se 7 (by rfl) ⟨18158, by rfl⟩ : syracuseStep 1549525 = 36317) (by norm_num)
theorem B2753765 : Blo 1222929 2753765 := bbase (se 4 (by rfl) ⟨258165, by rfl⟩ : syracuseStep 2753765 = 516331) (by norm_num)
theorem B1836269 : Blo 1222929 1836269 := bbase (se 3 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 1836269 = 688601) (by norm_num)
theorem B3138821 : Blo 1222929 3138821 := bbase (se 4 (by rfl) ⟨294264, by rfl⟩ : syracuseStep 3138821 = 588529) (by norm_num)
theorem B1836293 : Blo 1222929 1836293 := bbase (se 4 (by rfl) ⟨172152, by rfl⟩ : syracuseStep 1836293 = 344305) (by norm_num)
theorem B3097885 : Blo 1222929 3097885 := bbase (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) (by norm_num)
theorem B1836317 : Blo 1222929 1836317 := bbase (se 3 (by rfl) ⟨344309, by rfl⟩ : syracuseStep 1836317 = 688619) (by norm_num)
theorem B2753837 : Blo 1222929 2753837 := bbase (se 3 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 2753837 = 1032689) (by norm_num)
theorem B2065709 : Blo 1222929 2065709 := bbase (se 3 (by rfl) ⟨387320, by rfl⟩ : syracuseStep 2065709 = 774641) (by norm_num)
theorem B5580085 : Blo 1222929 5580085 := bbase (se 5 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 5580085 = 523133) (by norm_num)
theorem B1836341 : Blo 1222929 1836341 := bbase (se 5 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 1836341 = 172157) (by norm_num)
theorem B1549621 : Blo 1222929 1549621 := bbase (se 5 (by rfl) ⟨72638, by rfl⟩ : syracuseStep 1549621 = 145277) (by norm_num)
theorem B1885517 : Blo 1222929 1885517 := bbase (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) (by norm_num)
theorem B1836365 : Blo 1222929 1836365 := bbase (se 3 (by rfl) ⟨344318, by rfl⟩ : syracuseStep 1836365 = 688637) (by norm_num)
theorem B1836389 : Blo 1222929 1836389 := bbase (se 4 (by rfl) ⟨172161, by rfl⟩ : syracuseStep 1836389 = 344323) (by norm_num)
theorem B2753909 : Blo 1222929 2753909 := bbase (se 5 (by rfl) ⟨129089, by rfl⟩ : syracuseStep 2753909 = 258179) (by norm_num)
theorem B1836413 : Blo 1222929 1836413 := bbase (se 3 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 1836413 = 688655) (by norm_num)
theorem B3097997 : Blo 1222929 3097997 := bbase (se 3 (by rfl) ⟨580874, by rfl⟩ : syracuseStep 3097997 = 1161749) (by norm_num)
theorem B1836437 : Blo 1222929 1836437 := bbase (se 6 (by rfl) ⟨43041, by rfl⟩ : syracuseStep 1836437 = 86083) (by norm_num)
theorem B2065837 : Blo 1222929 2065837 := bbase (se 3 (by rfl) ⟨387344, by rfl⟩ : syracuseStep 2065837 = 774689) (by norm_num)
theorem B1836461 : Blo 1222929 1836461 := bbase (se 3 (by rfl) ⟨344336, by rfl⟩ : syracuseStep 1836461 = 688673) (by norm_num)
theorem B2753981 : Blo 1222929 2753981 := bbase (se 3 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 2753981 = 1032743) (by norm_num)
theorem B1836485 : Blo 1222929 1836485 := bbase (se 4 (by rfl) ⟨172170, by rfl⟩ : syracuseStep 1836485 = 344341) (by norm_num)
theorem B3139037 : Blo 1222929 3139037 := bbase (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) (by norm_num)
theorem B1836509 : Blo 1222929 1836509 := bbase (se 3 (by rfl) ⟨344345, by rfl⟩ : syracuseStep 1836509 = 688691) (by norm_num)
theorem B1836533 : Blo 1222929 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B2614781 : Blo 1222929 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B2754053 : Blo 1222929 2754053 := bbase (se 4 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 2754053 = 516385) (by norm_num)
theorem B2065925 : Blo 1222929 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B1836557 : Blo 1222929 1836557 := bbase (se 3 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 1836557 = 688709) (by norm_num)
theorem B1836581 : Blo 1222929 1836581 := bbase (se 4 (by rfl) ⟨172179, by rfl⟩ : syracuseStep 1836581 = 344359) (by norm_num)
theorem B1836605 : Blo 1222929 1836605 := bbase (se 3 (by rfl) ⟨344363, by rfl⟩ : syracuseStep 1836605 = 688727) (by norm_num)
theorem B3098189 : Blo 1222929 3098189 := bbase (se 3 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 3098189 = 1161821) (by norm_num)
theorem B2754125 : Blo 1222929 2754125 := bbase (se 3 (by rfl) ⟨516398, by rfl⟩ : syracuseStep 2754125 = 1032797) (by norm_num)
theorem B1836629 : Blo 1222929 1836629 := bbase (se 8 (by rfl) ⟨10761, by rfl⟩ : syracuseStep 1836629 = 21523) (by norm_num)
theorem B4130405 : Blo 1222929 4130405 := bbase (se 4 (by rfl) ⟨387225, by rfl⟩ : syracuseStep 4130405 = 774451) (by norm_num)
theorem B3483253 : Blo 1222929 3483253 := bbase (se 5 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 3483253 = 326555) (by norm_num)
theorem B5883509 : Blo 1222929 5883509 := bbase (se 5 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 5883509 = 551579) (by norm_num)
theorem B2066053 : Blo 1222929 2066053 := bbase (se 4 (by rfl) ⟨193692, by rfl⟩ : syracuseStep 2066053 = 387385) (by norm_num)
theorem B2754197 : Blo 1222929 2754197 := bbase (se 6 (by rfl) ⟨64551, by rfl⟩ : syracuseStep 2754197 = 129103) (by norm_num)
theorem B2754269 : Blo 1222929 2754269 := bbase (se 3 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 2754269 = 1032851) (by norm_num)
theorem B2066141 : Blo 1222929 2066141 := bbase (se 3 (by rfl) ⟨387401, by rfl⟩ : syracuseStep 2066141 = 774803) (by norm_num)
theorem B2754341 : Blo 1222929 2754341 := bbase (se 4 (by rfl) ⟨258219, by rfl⟩ : syracuseStep 2754341 = 516439) (by norm_num)
theorem B3139373 : Blo 1222929 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B2754413 : Blo 1222929 2754413 := bbase (se 3 (by rfl) ⟨516452, by rfl⟩ : syracuseStep 2754413 = 1032905) (by norm_num)
theorem B1959805 : Blo 1222929 1959805 := bbase (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) (by norm_num)
theorem B3098533 : Blo 1222929 3098533 := bbase (se 4 (by rfl) ⟨290487, by rfl⟩ : syracuseStep 3098533 = 580975) (by norm_num)
theorem B2754485 : Blo 1222929 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B1959869 : Blo 1222929 1959869 := bbase (se 3 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 1959869 = 734951) (by norm_num)
theorem B2754557 : Blo 1222929 2754557 := bbase (se 3 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 2754557 = 1032959) (by norm_num)
theorem B4130837 : Blo 1222929 4130837 := bbase (se 6 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 4130837 = 193633) (by norm_num)
theorem B3098645 : Blo 1222929 3098645 := bbase (se 6 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 3098645 = 145249) (by norm_num)
theorem B2754629 : Blo 1222929 2754629 := bbase (se 4 (by rfl) ⟨258246, by rfl⟩ : syracuseStep 2754629 = 516493) (by norm_num)
theorem B3139661 : Blo 1222929 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B2754701 : Blo 1222929 2754701 := bbase (se 3 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 2754701 = 1033013) (by norm_num)
theorem B20400277 : Blo 1222929 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B6195365 : Blo 1222929 6195365 := bbase (se 4 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 6195365 = 1161631) (by norm_num)
theorem B3098837 : Blo 1222929 3098837 := bbase (se 7 (by rfl) ⟨36314, by rfl⟩ : syracuseStep 3098837 = 72629) (by norm_num)
theorem B2754773 : Blo 1222929 2754773 := bbase (se 7 (by rfl) ⟨32282, by rfl⟩ : syracuseStep 2754773 = 64565) (by norm_num)
theorem B2205949 : Blo 1222929 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B2754845 : Blo 1222929 2754845 := bbase (se 3 (by rfl) ⟨516533, by rfl⟩ : syracuseStep 2754845 = 1033067) (by norm_num)
theorem B4647253 : Blo 1222929 4647253 := bbase (se 10 (by rfl) ⟨6807, by rfl⟩ : syracuseStep 4647253 = 13615) (by norm_num)
theorem B2754917 : Blo 1222929 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B5228981 : Blo 1222929 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B4131269 : Blo 1222929 4131269 := bbase (se 4 (by rfl) ⟨387306, by rfl⟩ : syracuseStep 4131269 = 774613) (by norm_num)
theorem B19843541 : Blo 1222929 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B9415157 : Blo 1222929 9415157 := bbase (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) (by norm_num)
theorem B2206237 : Blo 1222929 2206237 := bbase (se 3 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 2206237 = 827339) (by norm_num)
theorem B3099181 : Blo 1222929 3099181 := bbase (se 3 (by rfl) ⟨581096, by rfl⟩ : syracuseStep 3099181 = 1162193) (by norm_num)
theorem B4409909 : Blo 1222929 4409909 := bbase (se 5 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 4409909 = 413429) (by norm_num)
theorem B4647557 : Blo 1222929 4647557 := bbase (se 4 (by rfl) ⟨435708, by rfl⟩ : syracuseStep 4647557 = 871417) (by norm_num)
theorem B3099293 : Blo 1222929 3099293 := bbase (se 3 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 3099293 = 1162235) (by norm_num)
theorem B10447541 : Blo 1222929 10447541 := bbase (se 5 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 10447541 = 979457) (by norm_num)
theorem B2206453 : Blo 1222929 2206453 := bbase (se 5 (by rfl) ⟨103427, by rfl⟩ : syracuseStep 2206453 = 206855) (by norm_num)
theorem B1239833 : Blo 1222929 1239833 := bbase (se 2 (by rfl) ⟨464937, by rfl⟩ : syracuseStep 1239833 = 929875) (by norm_num)
theorem B1395541 : Blo 1222929 1395541 := bbase (se 9 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 1395541 = 8177) (by norm_num)
theorem B4131701 : Blo 1222929 4131701 := bbase (se 5 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 4131701 = 387347) (by norm_num)
theorem B2354093 : Blo 1222929 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B4410325 : Blo 1222929 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B3918917 : Blo 1222929 3918917 := bbase (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) (by norm_num)
theorem B3484757 : Blo 1222929 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B1395833 : Blo 1222929 1395833 := bbase (se 2 (by rfl) ⟨523437, by rfl⟩ : syracuseStep 1395833 = 1046875) (by norm_num)
theorem B6966485 : Blo 1222929 6966485 := bbase (se 7 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 6966485 = 163277) (by norm_num)
theorem B1961189 : Blo 1222929 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B7843061 : Blo 1222929 7843061 := bbase (se 5 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 7843061 = 735287) (by norm_num)
theorem B4132133 : Blo 1222929 4132133 := bbase (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) (by norm_num)
theorem B2321797 : Blo 1222929 2321797 := bbase (se 4 (by rfl) ⟨217668, by rfl⟩ : syracuseStep 2321797 = 435337) (by norm_num)
theorem B6196661 : Blo 1222929 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B1306049 : Blo 1222929 1306049 := bbase (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) (by norm_num)
theorem B2321941 : Blo 1222929 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B2649677 : Blo 1222929 2649677 := bbase (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) (by norm_num)
theorem B2322101 : Blo 1222929 2322101 := bbase (se 5 (by rfl) ⟨108848, by rfl⟩ : syracuseStep 2322101 = 217697) (by norm_num)
theorem B4411061 : Blo 1222929 4411061 := bbase (se 5 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 4411061 = 413537) (by norm_num)
theorem B1306297 : Blo 1222929 1306297 := bbase (se 2 (by rfl) ⟨489861, by rfl⟩ : syracuseStep 1306297 = 979723) (by norm_num)
theorem B7065301 : Blo 1222929 7065301 := bbase (se 7 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 7065301 = 165593) (by norm_num)
theorem B1470209 : Blo 1222929 1470209 := bbase (se 2 (by rfl) ⟨551328, by rfl⟩ : syracuseStep 1470209 = 1102657) (by norm_num)
theorem B2322245 : Blo 1222929 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B1470305 : Blo 1222929 1470305 := bbase (se 2 (by rfl) ⟨551364, by rfl⟩ : syracuseStep 1470305 = 1102729) (by norm_num)
theorem B4771685 : Blo 1222929 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B1470325 : Blo 1222929 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1470469 : Blo 1222929 1470469 := bbase (se 4 (by rfl) ⟨137856, by rfl⟩ : syracuseStep 1470469 = 275713) (by norm_num)
theorem B3723317 : Blo 1222929 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B2322533 : Blo 1222929 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B1306729 : Blo 1222929 1306729 := bbase (se 2 (by rfl) ⟨490023, by rfl⟩ : syracuseStep 1306729 = 980047) (by norm_num)
theorem B1306801 : Blo 1222929 1306801 := bbase (se 2 (by rfl) ⟨490050, by rfl⟩ : syracuseStep 1306801 = 980101) (by norm_num)
theorem B2093293 : Blo 1222929 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B2322685 : Blo 1222929 2322685 := bbase (se 3 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 2322685 = 871007) (by norm_num)
theorem B3305765 : Blo 1222929 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B1765805 : Blo 1222929 1765805 := bbase (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) (by norm_num)
theorem B1741285 : Blo 1222929 1741285 := bbase (se 4 (by rfl) ⟨163245, by rfl⟩ : syracuseStep 1741285 = 326491) (by norm_num)
theorem B1307173 : Blo 1222929 1307173 := bbase (se 4 (by rfl) ⟨122547, by rfl⟩ : syracuseStep 1307173 = 245095) (by norm_num)
theorem B2322989 : Blo 1222929 2322989 := bbase (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) (by norm_num)
theorem B3486341 : Blo 1222929 3486341 := bbase (se 4 (by rfl) ⟨326844, by rfl⟩ : syracuseStep 3486341 = 653689) (by norm_num)
theorem B1569461 : Blo 1222929 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B6197957 : Blo 1222929 6197957 := bbase (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) (by norm_num)
theorem B1274585 : Blo 1222929 1274585 := bbase (se 2 (by rfl) ⟨477969, by rfl⟩ : syracuseStep 1274585 = 955939) (by norm_num)
theorem B2978861 : Blo 1222929 2978861 := bbase (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) (by norm_num)
theorem B3822661 : Blo 1222929 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B6616181 : Blo 1222929 6616181 := bbase (se 5 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 6616181 = 620267) (by norm_num)
theorem B3306629 : Blo 1222929 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B4412645 : Blo 1222929 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B1742077 : Blo 1222929 1742077 := bbase (se 3 (by rfl) ⟨326639, by rfl⟩ : syracuseStep 1742077 = 653279) (by norm_num)
theorem B3921173 : Blo 1222929 3921173 := bbase (se 6 (by rfl) ⟨91902, by rfl⟩ : syracuseStep 3921173 = 183805) (by norm_num)
theorem B2323741 : Blo 1222929 2323741 := bbase (se 3 (by rfl) ⟨435701, by rfl⟩ : syracuseStep 2323741 = 871403) (by norm_num)
theorem B2479405 : Blo 1222929 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B7837013 : Blo 1222929 7837013 := bbase (se 14 (by rfl) ⟨717, by rfl⟩ : syracuseStep 7837013 = 1435) (by norm_num)
theorem B6968693 : Blo 1222929 6968693 := bbase (se 5 (by rfl) ⟨326657, by rfl⟩ : syracuseStep 6968693 = 653315) (by norm_num)
theorem B2323885 : Blo 1222929 2323885 := bbase (se 3 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 2323885 = 871457) (by norm_num)
theorem B2790845 : Blo 1222929 2790845 := bbase (se 3 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 2790845 = 1046567) (by norm_num)
theorem B10597877 : Blo 1222929 10597877 := bbase (se 5 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 10597877 = 993551) (by norm_num)
theorem B1742413 : Blo 1222929 1742413 := bbase (se 3 (by rfl) ⟨326702, by rfl⟩ : syracuseStep 1742413 = 653405) (by norm_num)
theorem B2324045 : Blo 1222929 2324045 := bbase (se 3 (by rfl) ⟨435758, by rfl⟩ : syracuseStep 2324045 = 871517) (by norm_num)
theorem B2324189 : Blo 1222929 2324189 := bbase (se 3 (by rfl) ⟨435785, by rfl⟩ : syracuseStep 2324189 = 871571) (by norm_num)
theorem B22320917 : Blo 1222929 22320917 := bbase (se 6 (by rfl) ⟨523146, by rfl⟩ : syracuseStep 22320917 = 1046293) (by norm_num)
theorem B1742629 : Blo 1222929 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B2938805 : Blo 1222929 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B2324477 : Blo 1222929 2324477 := bbase (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) (by norm_num)
theorem B3921941 : Blo 1222929 3921941 := bbase (se 6 (by rfl) ⟨91920, by rfl⟩ : syracuseStep 3921941 = 183841) (by norm_num)
theorem B1743005 : Blo 1222929 1743005 := bbase (se 3 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 1743005 = 653627) (by norm_num)
theorem B5879989 : Blo 1222929 5879989 := bbase (se 5 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 5879989 = 551249) (by norm_num)
theorem B2939141 : Blo 1222929 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B6191477 : Blo 1222929 6191477 := bbase (se 5 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 6191477 = 580451) (by norm_num)
theorem B11753909 : Blo 1222929 11753909 := bbase (se 5 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 11753909 = 1101929) (by norm_num)
theorem B5224949 : Blo 1222929 5224949 := bbase (se 5 (by rfl) ⟨244919, by rfl⟩ : syracuseStep 5224949 = 489839) (by norm_num)
theorem B3922453 : Blo 1222929 3922453 := bbase (se 6 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 3922453 = 183865) (by norm_num)
theorem B4643365 : Blo 1222929 4643365 := bbase (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) (by norm_num)
theorem B2939533 : Blo 1222929 2939533 := bbase (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) (by norm_num)
theorem B9296693 : Blo 1222929 9296693 := bbase (se 5 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 9296693 = 871565) (by norm_num)
theorem B4643669 : Blo 1222929 4643669 := bbase (se 9 (by rfl) ⟨13604, by rfl⟩ : syracuseStep 4643669 = 27209) (by norm_num)
theorem B1489801 : Blo 1222929 1489801 := bbase (se 2 (by rfl) ⟨558675, by rfl⟩ : syracuseStep 1489801 = 1117351) (by norm_num)
theorem B7650229 : Blo 1222929 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B3095597 : Blo 1222929 3095597 := bbase (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) (by norm_num)
theorem B4127813 : Blo 1222929 4127813 := bbase (se 4 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 4127813 = 773965) (by norm_num)
theorem B2751605 : Blo 1222929 2751605 := bbase (se 5 (by rfl) ⟨128981, by rfl⟩ : syracuseStep 2751605 = 257963) (by norm_num)
theorem B1653877 : Blo 1222929 1653877 := bbase (se 5 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 1653877 = 155051) (by norm_num)
theorem B2751677 : Blo 1222929 2751677 := bbase (se 3 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 2751677 = 1031879) (by norm_num)
theorem B9288917 : Blo 1222929 9288917 := bbase (se 7 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 9288917 = 217709) (by norm_num)
theorem B2751749 : Blo 1222929 2751749 := bbase (se 4 (by rfl) ⟨257976, by rfl⟩ : syracuseStep 2751749 = 515953) (by norm_num)
theorem B2751821 : Blo 1222929 2751821 := bbase (se 3 (by rfl) ⟨515966, by rfl⟩ : syracuseStep 2751821 = 1031933) (by norm_num)
theorem B3095941 : Blo 1222929 3095941 := bbase (se 4 (by rfl) ⟨290244, by rfl⟩ : syracuseStep 3095941 = 580489) (by norm_num)
theorem B2063765 : Blo 1222929 2063765 := bbase (se 6 (by rfl) ⟨48369, by rfl⟩ : syracuseStep 2063765 = 96739) (by norm_num)
theorem B2751893 : Blo 1222929 2751893 := bbase (se 6 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 2751893 = 128995) (by norm_num)
theorem B1834397 : Blo 1222929 1834397 := bbase (se 3 (by rfl) ⟨343949, by rfl⟩ : syracuseStep 1834397 = 687899) (by norm_num)
theorem B1834421 : Blo 1222929 1834421 := bbase (se 5 (by rfl) ⟨85988, by rfl⟩ : syracuseStep 1834421 = 171977) (by norm_num)
theorem B1834445 : Blo 1222929 1834445 := bbase (se 3 (by rfl) ⟨343958, by rfl⟩ : syracuseStep 1834445 = 687917) (by norm_num)
theorem B2751965 : Blo 1222929 2751965 := bbase (se 3 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 2751965 = 1031987) (by norm_num)
theorem B1834469 : Blo 1222929 1834469 := bbase (se 4 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 1834469 = 343963) (by norm_num)
theorem B2981357 : Blo 1222929 2981357 := bbase (se 3 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 2981357 = 1118009) (by norm_num)
theorem B3096053 : Blo 1222929 3096053 := bbase (se 5 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 3096053 = 290255) (by norm_num)
theorem B4128245 : Blo 1222929 4128245 := bbase (se 5 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 4128245 = 387023) (by norm_num)
theorem B1834493 : Blo 1222929 1834493 := bbase (se 3 (by rfl) ⟨343967, by rfl⟩ : syracuseStep 1834493 = 687935) (by norm_num)
theorem B1342985 : Blo 1222929 1342985 := bbase (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) (by norm_num)
theorem B1834517 : Blo 1222929 1834517 := bbase (se 6 (by rfl) ⟨42996, by rfl⟩ : syracuseStep 1834517 = 85993) (by norm_num)
theorem B2063893 : Blo 1222929 2063893 := bbase (se 6 (by rfl) ⟨48372, by rfl⟩ : syracuseStep 2063893 = 96745) (by norm_num)
theorem B2752037 : Blo 1222929 2752037 := bbase (se 4 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 2752037 = 516007) (by norm_num)
theorem B1834541 : Blo 1222929 1834541 := bbase (se 3 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 1834541 = 687953) (by norm_num)
theorem B1834565 : Blo 1222929 1834565 := bbase (se 4 (by rfl) ⟨171990, by rfl⟩ : syracuseStep 1834565 = 343981) (by norm_num)
theorem B1547849 : Blo 1222929 1547849 := bbase (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) (by norm_num)
theorem B1375825 : Blo 1222929 1375825 := bbase (se 2 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 1375825 = 1031869) (by norm_num)
theorem B1834589 : Blo 1222929 1834589 := bbase (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) (by norm_num)
theorem B2063981 : Blo 1222929 2063981 := bbase (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) (by norm_num)
theorem B2752109 : Blo 1222929 2752109 := bbase (se 3 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 2752109 = 1032041) (by norm_num)
theorem B1375861 : Blo 1222929 1375861 := bbase (se 5 (by rfl) ⟨64493, by rfl⟩ : syracuseStep 1375861 = 128987) (by norm_num)
theorem B1834613 : Blo 1222929 1834613 := bbase (se 5 (by rfl) ⟨85997, by rfl⟩ : syracuseStep 1834613 = 171995) (by norm_num)
theorem B1547905 : Blo 1222929 1547905 := bbase (se 2 (by rfl) ⟨580464, by rfl⟩ : syracuseStep 1547905 = 1160929) (by norm_num)
theorem B6192773 : Blo 1222929 6192773 := bbase (se 4 (by rfl) ⟨580572, by rfl⟩ : syracuseStep 6192773 = 1161145) (by norm_num)
theorem B2981509 : Blo 1222929 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B1834637 : Blo 1222929 1834637 := bbase (se 3 (by rfl) ⟨343994, by rfl⟩ : syracuseStep 1834637 = 687989) (by norm_num)
theorem B1375897 : Blo 1222929 1375897 := bbase (se 2 (by rfl) ⟨515961, by rfl⟩ : syracuseStep 1375897 = 1031923) (by norm_num)
theorem B1834661 : Blo 1222929 1834661 := bbase (se 4 (by rfl) ⟨171999, by rfl⟩ : syracuseStep 1834661 = 343999) (by norm_num)
theorem B2752181 : Blo 1222929 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B3096245 : Blo 1222929 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B1375933 : Blo 1222929 1375933 := bbase (se 3 (by rfl) ⟨257987, by rfl⟩ : syracuseStep 1375933 = 515975) (by norm_num)
theorem B1834685 : Blo 1222929 1834685 := bbase (se 3 (by rfl) ⟨344003, by rfl⟩ : syracuseStep 1834685 = 688007) (by norm_num)
theorem B1834709 : Blo 1222929 1834709 := bbase (se 7 (by rfl) ⟨21500, by rfl⟩ : syracuseStep 1834709 = 43001) (by norm_num)
theorem B1375969 : Blo 1222929 1375969 := bbase (se 2 (by rfl) ⟨515988, by rfl⟩ : syracuseStep 1375969 = 1031977) (by norm_num)
theorem B1548001 : Blo 1222929 1548001 := bbase (se 2 (by rfl) ⟨580500, by rfl⟩ : syracuseStep 1548001 = 1161001) (by norm_num)
theorem B1834733 : Blo 1222929 1834733 := bbase (se 3 (by rfl) ⟨344012, by rfl⟩ : syracuseStep 1834733 = 688025) (by norm_num)
theorem B2064109 : Blo 1222929 2064109 := bbase (se 3 (by rfl) ⟨387020, by rfl⟩ : syracuseStep 2064109 = 774041) (by norm_num)
theorem B2752253 : Blo 1222929 2752253 := bbase (se 3 (by rfl) ⟨516047, by rfl⟩ : syracuseStep 2752253 = 1032095) (by norm_num)
theorem B1376005 : Blo 1222929 1376005 := bbase (se 4 (by rfl) ⟨129000, by rfl⟩ : syracuseStep 1376005 = 258001) (by norm_num)
theorem B1834757 : Blo 1222929 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B1834781 : Blo 1222929 1834781 := bbase (se 3 (by rfl) ⟨344021, by rfl⟩ : syracuseStep 1834781 = 688043) (by norm_num)
theorem B1376041 : Blo 1222929 1376041 := bbase (se 2 (by rfl) ⟨516015, by rfl⟩ : syracuseStep 1376041 = 1032031) (by norm_num)
theorem B1490737 : Blo 1222929 1490737 := bbase (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) (by norm_num)
theorem B1834805 : Blo 1222929 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B2064197 : Blo 1222929 2064197 := bbase (se 4 (by rfl) ⟨193518, by rfl⟩ : syracuseStep 2064197 = 387037) (by norm_num)
theorem B2752325 : Blo 1222929 2752325 := bbase (se 4 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 2752325 = 516061) (by norm_num)
theorem B2178893 : Blo 1222929 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B1376077 : Blo 1222929 1376077 := bbase (se 3 (by rfl) ⟨258014, by rfl⟩ : syracuseStep 1376077 = 516029) (by norm_num)
theorem B1834829 : Blo 1222929 1834829 := bbase (se 3 (by rfl) ⟨344030, by rfl⟩ : syracuseStep 1834829 = 688061) (by norm_num)
theorem B1834853 : Blo 1222929 1834853 := bbase (se 4 (by rfl) ⟨172017, by rfl⟩ : syracuseStep 1834853 = 344035) (by norm_num)
theorem B1376113 : Blo 1222929 1376113 := bbase (se 2 (by rfl) ⟨516042, by rfl⟩ : syracuseStep 1376113 = 1032085) (by norm_num)
theorem B1834877 : Blo 1222929 1834877 := bbase (se 3 (by rfl) ⟨344039, by rfl⟩ : syracuseStep 1834877 = 688079) (by norm_num)
theorem B1548173 : Blo 1222929 1548173 := bbase (se 3 (by rfl) ⟨290282, by rfl⟩ : syracuseStep 1548173 = 580565) (by norm_num)
theorem B2752397 : Blo 1222929 2752397 := bbase (se 3 (by rfl) ⟨516074, by rfl⟩ : syracuseStep 2752397 = 1032149) (by norm_num)
theorem B1376149 : Blo 1222929 1376149 := bbase (se 6 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 1376149 = 64507) (by norm_num)
theorem B1834901 : Blo 1222929 1834901 := bbase (se 6 (by rfl) ⟨43005, by rfl⟩ : syracuseStep 1834901 = 86011) (by norm_num)
theorem B4128677 : Blo 1222929 4128677 := bbase (se 4 (by rfl) ⟨387063, by rfl⟩ : syracuseStep 4128677 = 774127) (by norm_num)
theorem B1834925 : Blo 1222929 1834925 := bbase (se 3 (by rfl) ⟨344048, by rfl⟩ : syracuseStep 1834925 = 688097) (by norm_num)
theorem B1376185 : Blo 1222929 1376185 := bbase (se 2 (by rfl) ⟨516069, by rfl⟩ : syracuseStep 1376185 = 1032139) (by norm_num)
theorem B2981821 : Blo 1222929 2981821 := bbase (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) (by norm_num)
theorem B1548229 : Blo 1222929 1548229 := bbase (se 4 (by rfl) ⟨145146, by rfl⟩ : syracuseStep 1548229 = 290293) (by norm_num)
theorem B1834949 : Blo 1222929 1834949 := bbase (se 4 (by rfl) ⟨172026, by rfl⟩ : syracuseStep 1834949 = 344053) (by norm_num)
theorem B2064325 : Blo 1222929 2064325 := bbase (se 4 (by rfl) ⟨193530, by rfl⟩ : syracuseStep 2064325 = 387061) (by norm_num)
theorem B2752469 : Blo 1222929 2752469 := bbase (se 7 (by rfl) ⟨32255, by rfl⟩ : syracuseStep 2752469 = 64511) (by norm_num)
theorem B1376221 : Blo 1222929 1376221 := bbase (se 3 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 1376221 = 516083) (by norm_num)
theorem B1834973 : Blo 1222929 1834973 := bbase (se 3 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 1834973 = 688115) (by norm_num)
theorem B1834997 : Blo 1222929 1834997 := bbase (se 5 (by rfl) ⟨86015, by rfl⟩ : syracuseStep 1834997 = 172031) (by norm_num)
theorem B1835009 : Blo 1222929 1835009 := bstep (se 2 (by rfl) ⟨688128, by rfl⟩ : syracuseStep 1835009 = 1376257) B1376257
theorem B4128785 : Blo 1222929 4128785 := bstep (se 2 (by rfl) ⟨1548294, by rfl⟩ : syracuseStep 4128785 = 3096589) B3096589
theorem B1835027 : Blo 1222929 1835027 := bstep (se 1 (by rfl) ⟨1376270, by rfl⟩ : syracuseStep 1835027 = 2752541) B2752541
theorem B1376275 : Blo 1222929 1376275 := bstep (se 1 (by rfl) ⟨1032206, by rfl⟩ : syracuseStep 1376275 = 2064413) B2064413
theorem B2482211 : Blo 1222929 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B2064433 : Blo 1222929 2064433 := bstep (se 2 (by rfl) ⟨774162, by rfl⟩ : syracuseStep 2064433 = 1548325) B1548325
theorem B1835057 : Blo 1222929 1835057 := bstep (se 2 (by rfl) ⟨688146, by rfl⟩ : syracuseStep 1835057 = 1376293) B1376293
theorem B1835075 : Blo 1222929 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B13942853 : Blo 1222929 13942853 := bstep (se 4 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 13942853 = 2614285) B2614285
theorem B2064467 : Blo 1222929 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B1835105 : Blo 1222929 1835105 := bstep (se 2 (by rfl) ⟨688164, by rfl⟩ : syracuseStep 1835105 = 1376329) B1376329
theorem B1835123 : Blo 1222929 1835123 := bstep (se 1 (by rfl) ⟨1376342, by rfl⟩ : syracuseStep 1835123 = 2752685) B2752685
theorem B1835153 : Blo 1222929 1835153 := bstep (se 2 (by rfl) ⟨688182, by rfl⟩ : syracuseStep 1835153 = 1376365) B1376365
theorem B1835171 : Blo 1222929 1835171 := bstep (se 1 (by rfl) ⟨1376378, by rfl⟩ : syracuseStep 1835171 = 2752757) B2752757
theorem B1376419 : Blo 1222929 1376419 := bstep (se 1 (by rfl) ⟨1032314, by rfl⟩ : syracuseStep 1376419 = 2064629) B2064629
theorem B1835201 : Blo 1222929 1835201 := bstep (se 2 (by rfl) ⟨688200, by rfl⟩ : syracuseStep 1835201 = 1376401) B1376401
theorem B2203843 : Blo 1222929 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B8372429 : Blo 1222929 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B2752721 : Blo 1222929 2752721 := bstep (se 2 (by rfl) ⟨1032270, by rfl⟩ : syracuseStep 2752721 = 2064541) B2064541
theorem B2064595 : Blo 1222929 2064595 := bstep (se 1 (by rfl) ⟨1548446, by rfl⟩ : syracuseStep 2064595 = 3096893) B3096893
theorem B1835219 : Blo 1222929 1835219 := bstep (se 1 (by rfl) ⟨1376414, by rfl⟩ : syracuseStep 1835219 = 2752829) B2752829
theorem B2752739 : Blo 1222929 2752739 := bstep (se 1 (by rfl) ⟨2064554, by rfl⟩ : syracuseStep 2752739 = 4129109) B4129109
theorem B1835249 : Blo 1222929 1835249 := bstep (se 2 (by rfl) ⟨688218, by rfl⟩ : syracuseStep 1835249 = 1376437) B1376437
theorem B7839985 : Blo 1222929 7839985 := bstep (se 2 (by rfl) ⟨2939994, by rfl⟩ : syracuseStep 7839985 = 5879989) B5879989
theorem B1835267 : Blo 1222929 1835267 := bstep (se 1 (by rfl) ⟨1376450, by rfl⟩ : syracuseStep 1835267 = 2752901) B2752901
theorem B6193421 : Blo 1222929 6193421 := bstep (se 3 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 6193421 = 2322533) B2322533
theorem B1835297 : Blo 1222929 1835297 := bstep (se 2 (by rfl) ⟨688236, by rfl⟩ : syracuseStep 1835297 = 1376473) B1376473
theorem B1835315 : Blo 1222929 1835315 := bstep (se 1 (by rfl) ⟨1376486, by rfl⟩ : syracuseStep 1835315 = 2752973) B2752973
theorem B1376563 : Blo 1222929 1376563 := bstep (se 1 (by rfl) ⟨1032422, by rfl⟩ : syracuseStep 1376563 = 2064845) B2064845
theorem B3096913 : Blo 1222929 3096913 := bstep (se 2 (by rfl) ⟨1161342, by rfl⟩ : syracuseStep 3096913 = 2322685) B2322685
theorem B1835345 : Blo 1222929 1835345 := bstep (se 2 (by rfl) ⟨688254, by rfl⟩ : syracuseStep 1835345 = 1376509) B1376509
theorem B2941265 : Blo 1222929 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B2064737 : Blo 1222929 2064737 := bstep (se 2 (by rfl) ⟨774276, by rfl⟩ : syracuseStep 2064737 = 1548553) B1548553
theorem B1835363 : Blo 1222929 1835363 := bstep (se 1 (by rfl) ⟨1376522, by rfl⟩ : syracuseStep 1835363 = 2753045) B2753045
theorem B1548659 : Blo 1222929 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B1835393 : Blo 1222929 1835393 := bstep (se 2 (by rfl) ⟨688272, by rfl⟩ : syracuseStep 1835393 = 1376545) B1376545
theorem B1835411 : Blo 1222929 1835411 := bstep (se 1 (by rfl) ⟨1376558, by rfl⟩ : syracuseStep 1835411 = 2753117) B2753117
theorem B1835441 : Blo 1222929 1835441 := bstep (se 2 (by rfl) ⟨688290, by rfl⟩ : syracuseStep 1835441 = 1376581) B1376581
theorem B1376707 : Blo 1222929 1376707 := bstep (se 1 (by rfl) ⟨1032530, by rfl⟩ : syracuseStep 1376707 = 2065061) B2065061
theorem B1835459 : Blo 1222929 1835459 := bstep (se 1 (by rfl) ⟨1376594, by rfl⟩ : syracuseStep 1835459 = 2753189) B2753189
theorem B2064865 : Blo 1222929 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B1835489 : Blo 1222929 1835489 := bstep (se 2 (by rfl) ⟨688308, by rfl⟩ : syracuseStep 1835489 = 1376617) B1376617
theorem B2753009 : Blo 1222929 2753009 := bstep (se 2 (by rfl) ⟨1032378, by rfl⟩ : syracuseStep 2753009 = 2064757) B2064757
theorem B1835507 : Blo 1222929 1835507 := bstep (se 1 (by rfl) ⟨1376630, by rfl⟩ : syracuseStep 1835507 = 2753261) B2753261
theorem B2753027 : Blo 1222929 2753027 := bstep (se 1 (by rfl) ⟨2064770, by rfl⟩ : syracuseStep 2753027 = 4129541) B4129541
theorem B2064899 : Blo 1222929 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B1835537 : Blo 1222929 1835537 := bstep (se 2 (by rfl) ⟨688326, by rfl⟩ : syracuseStep 1835537 = 1376653) B1376653
theorem B1835555 : Blo 1222929 1835555 := bstep (se 1 (by rfl) ⟨1376666, by rfl⟩ : syracuseStep 1835555 = 2753333) B2753333
theorem B4129325 : Blo 1222929 4129325 := bstep (se 3 (by rfl) ⟨774248, by rfl⟩ : syracuseStep 4129325 = 1548497) B1548497
theorem B1835585 : Blo 1222929 1835585 := bstep (se 2 (by rfl) ⟨688344, by rfl⟩ : syracuseStep 1835585 = 1376689) B1376689
theorem B1835603 : Blo 1222929 1835603 := bstep (se 1 (by rfl) ⟨1376702, by rfl⟩ : syracuseStep 1835603 = 2753405) B2753405
theorem B1376851 : Blo 1222929 1376851 := bstep (se 1 (by rfl) ⟨1032638, by rfl⟩ : syracuseStep 1376851 = 2065277) B2065277
theorem B4129379 : Blo 1222929 4129379 := bstep (se 1 (by rfl) ⟨3097034, by rfl⟩ : syracuseStep 4129379 = 6194069) B6194069
theorem B3097187 : Blo 1222929 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B1835633 : Blo 1222929 1835633 := bstep (se 2 (by rfl) ⟨688362, by rfl⟩ : syracuseStep 1835633 = 1376725) B1376725
theorem B2065027 : Blo 1222929 2065027 := bstep (se 1 (by rfl) ⟨1548770, by rfl⟩ : syracuseStep 2065027 = 3097541) B3097541
theorem B1835651 : Blo 1222929 1835651 := bstep (se 1 (by rfl) ⟨1376738, by rfl⟩ : syracuseStep 1835651 = 2753477) B2753477
theorem B1835681 : Blo 1222929 1835681 := bstep (se 2 (by rfl) ⟨688380, by rfl⟩ : syracuseStep 1835681 = 1376761) B1376761
theorem B1835699 : Blo 1222929 1835699 := bstep (se 1 (by rfl) ⟨1376774, by rfl⟩ : syracuseStep 1835699 = 2753549) B2753549
theorem B15901381 : Blo 1222929 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B1835729 : Blo 1222929 1835729 := bstep (se 2 (by rfl) ⟨688398, by rfl⟩ : syracuseStep 1835729 = 1376797) B1376797
theorem B2941649 : Blo 1222929 2941649 := bstep (se 2 (by rfl) ⟨1103118, by rfl⟩ : syracuseStep 2941649 = 2206237) B2206237
theorem B1835747 : Blo 1222929 1835747 := bstep (se 1 (by rfl) ⟨1376810, by rfl⟩ : syracuseStep 1835747 = 2753621) B2753621
theorem B1376995 : Blo 1222929 1376995 := bstep (se 1 (by rfl) ⟨1032746, by rfl⟩ : syracuseStep 1376995 = 2065493) B2065493
theorem B1835777 : Blo 1222929 1835777 := bstep (se 2 (by rfl) ⟨688416, by rfl⟩ : syracuseStep 1835777 = 1376833) B1376833
theorem B2753297 : Blo 1222929 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B2065169 : Blo 1222929 2065169 := bstep (se 2 (by rfl) ⟨774438, by rfl⟩ : syracuseStep 2065169 = 1548877) B1548877
theorem B1835795 : Blo 1222929 1835795 := bstep (se 1 (by rfl) ⟨1376846, by rfl⟩ : syracuseStep 1835795 = 2753693) B2753693
theorem B3097379 : Blo 1222929 3097379 := bstep (se 1 (by rfl) ⟨2323034, by rfl⟩ : syracuseStep 3097379 = 4646069) B4646069
theorem B2753315 : Blo 1222929 2753315 := bstep (se 1 (by rfl) ⟨2064986, by rfl⟩ : syracuseStep 2753315 = 4129973) B4129973
theorem B1835825 : Blo 1222929 1835825 := bstep (se 2 (by rfl) ⟨688434, by rfl⟩ : syracuseStep 1835825 = 1376869) B1376869
theorem B1835843 : Blo 1222929 1835843 := bstep (se 1 (by rfl) ⟨1376882, by rfl⟩ : syracuseStep 1835843 = 2753765) B2753765
theorem B2941763 : Blo 1222929 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1835873 : Blo 1222929 1835873 := bstep (se 2 (by rfl) ⟨688452, by rfl⟩ : syracuseStep 1835873 = 1376905) B1376905
theorem B2614115 : Blo 1222929 2614115 := bstep (se 1 (by rfl) ⟨1960586, by rfl⟩ : syracuseStep 2614115 = 3921173) B3921173
theorem B4129649 : Blo 1222929 4129649 := bstep (se 2 (by rfl) ⟨1548618, by rfl⟩ : syracuseStep 4129649 = 3097237) B3097237
theorem B1835891 : Blo 1222929 1835891 := bstep (se 1 (by rfl) ⟨1376918, by rfl⟩ : syracuseStep 1835891 = 2753837) B2753837
theorem B1377139 : Blo 1222929 1377139 := bstep (se 1 (by rfl) ⟨1032854, by rfl⟩ : syracuseStep 1377139 = 2065709) B2065709
theorem B2065297 : Blo 1222929 2065297 := bstep (se 2 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 2065297 = 1548973) B1548973
theorem B1835921 : Blo 1222929 1835921 := bstep (se 2 (by rfl) ⟨688470, by rfl⟩ : syracuseStep 1835921 = 1376941) B1376941
theorem B4645795 : Blo 1222929 4645795 := bstep (se 1 (by rfl) ⟨3484346, by rfl⟩ : syracuseStep 4645795 = 6968693) B6968693
theorem B1835939 : Blo 1222929 1835939 := bstep (se 1 (by rfl) ⟨1376954, by rfl⟩ : syracuseStep 1835939 = 2753909) B2753909
theorem B2065331 : Blo 1222929 2065331 := bstep (se 1 (by rfl) ⟨1548998, by rfl⟩ : syracuseStep 2065331 = 3097997) B3097997
theorem B1835969 : Blo 1222929 1835969 := bstep (se 2 (by rfl) ⟨688488, by rfl⟩ : syracuseStep 1835969 = 1376977) B1376977
theorem B1860563 : Blo 1222929 1860563 := bstep (se 1 (by rfl) ⟨1395422, by rfl⟩ : syracuseStep 1860563 = 2790845) B2790845
theorem B1835987 : Blo 1222929 1835987 := bstep (se 1 (by rfl) ⟨1376990, by rfl⟩ : syracuseStep 1835987 = 2753981) B2753981
theorem B1836017 : Blo 1222929 1836017 := bstep (se 2 (by rfl) ⟨688506, by rfl⟩ : syracuseStep 1836017 = 1377013) B1377013
theorem B2941937 : Blo 1222929 2941937 := bstep (se 2 (by rfl) ⟨1103226, by rfl⟩ : syracuseStep 2941937 = 2206453) B2206453
theorem B1836035 : Blo 1222929 1836035 := bstep (se 1 (by rfl) ⟨1377026, by rfl⟩ : syracuseStep 1836035 = 2754053) B2754053
theorem B1377283 : Blo 1222929 1377283 := bstep (se 1 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 1377283 = 2065925) B2065925
theorem B1836065 : Blo 1222929 1836065 := bstep (se 2 (by rfl) ⟨688524, by rfl⟩ : syracuseStep 1836065 = 1377049) B1377049
theorem B2753585 : Blo 1222929 2753585 := bstep (se 2 (by rfl) ⟨1032594, by rfl⟩ : syracuseStep 2753585 = 2065189) B2065189
theorem B2065459 : Blo 1222929 2065459 := bstep (se 1 (by rfl) ⟨1549094, by rfl⟩ : syracuseStep 2065459 = 3098189) B3098189
theorem B1836083 : Blo 1222929 1836083 := bstep (se 1 (by rfl) ⟨1377062, by rfl⟩ : syracuseStep 1836083 = 2754125) B2754125
theorem B1549363 : Blo 1222929 1549363 := bstep (se 1 (by rfl) ⟨1162022, by rfl⟩ : syracuseStep 1549363 = 2324045) B2324045
theorem B2753603 : Blo 1222929 2753603 := bstep (se 1 (by rfl) ⟨2065202, by rfl⟩ : syracuseStep 2753603 = 4130405) B4130405
theorem B1836113 : Blo 1222929 1836113 := bstep (se 2 (by rfl) ⟨688542, by rfl⟩ : syracuseStep 1836113 = 1377085) B1377085
theorem B1836131 : Blo 1222929 1836131 := bstep (se 1 (by rfl) ⟨1377098, by rfl⟩ : syracuseStep 1836131 = 2754197) B2754197
theorem B1836161 : Blo 1222929 1836161 := bstep (se 2 (by rfl) ⟨688560, by rfl⟩ : syracuseStep 1836161 = 1377121) B1377121
theorem B1836179 : Blo 1222929 1836179 := bstep (se 1 (by rfl) ⟨1377134, by rfl⟩ : syracuseStep 1836179 = 2754269) B2754269
theorem B1549459 : Blo 1222929 1549459 := bstep (se 1 (by rfl) ⟨1162094, by rfl⟩ : syracuseStep 1549459 = 2324189) B2324189
theorem B1377427 : Blo 1222929 1377427 := bstep (se 1 (by rfl) ⟨1033070, by rfl⟩ : syracuseStep 1377427 = 2066141) B2066141
theorem B1836209 : Blo 1222929 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B2065601 : Blo 1222929 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B1836227 : Blo 1222929 1836227 := bstep (se 1 (by rfl) ⟨1377170, by rfl⟩ : syracuseStep 1836227 = 2754341) B2754341
theorem B1836257 : Blo 1222929 1836257 := bstep (se 2 (by rfl) ⟨688596, by rfl⟩ : syracuseStep 1836257 = 1377193) B1377193
theorem B10200305 : Blo 1222929 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1836275 : Blo 1222929 1836275 := bstep (se 1 (by rfl) ⟨1377206, by rfl⟩ : syracuseStep 1836275 = 2754413) B2754413
theorem B1836305 : Blo 1222929 1836305 := bstep (se 2 (by rfl) ⟨688614, by rfl⟩ : syracuseStep 1836305 = 1377229) B1377229
theorem B1959203 : Blo 1222929 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B1836323 : Blo 1222929 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B2065729 : Blo 1222929 2065729 := bstep (se 2 (by rfl) ⟨774648, by rfl⟩ : syracuseStep 2065729 = 1549297) B1549297
theorem B1836353 : Blo 1222929 1836353 := bstep (se 2 (by rfl) ⟨688632, by rfl⟩ : syracuseStep 1836353 = 1377265) B1377265
theorem B6972749 : Blo 1222929 6972749 := bstep (se 3 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 6972749 = 2614781) B2614781
theorem B2753873 : Blo 1222929 2753873 := bstep (se 2 (by rfl) ⟨1032702, by rfl⟩ : syracuseStep 2753873 = 2065405) B2065405
theorem B1836371 : Blo 1222929 1836371 := bstep (se 1 (by rfl) ⟨1377278, by rfl⟩ : syracuseStep 1836371 = 2754557) B2754557
theorem B2753891 : Blo 1222929 2753891 := bstep (se 1 (by rfl) ⟨2065418, by rfl⟩ : syracuseStep 2753891 = 4130837) B4130837
theorem B2065763 : Blo 1222929 2065763 := bstep (se 1 (by rfl) ⟨1549322, by rfl⟩ : syracuseStep 2065763 = 3098645) B3098645
theorem B2614627 : Blo 1222929 2614627 := bstep (se 1 (by rfl) ⟨1960970, by rfl⟩ : syracuseStep 2614627 = 3921941) B3921941
theorem B3581293 : Blo 1222929 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1836401 : Blo 1222929 1836401 := bstep (se 2 (by rfl) ⟨688650, by rfl⟩ : syracuseStep 1836401 = 1377301) B1377301
theorem B1836419 : Blo 1222929 1836419 := bstep (se 1 (by rfl) ⟨1377314, by rfl⟩ : syracuseStep 1836419 = 2754629) B2754629
theorem B4130189 : Blo 1222929 4130189 := bstep (se 3 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 4130189 = 1548821) B1548821
theorem B1836449 : Blo 1222929 1836449 := bstep (se 2 (by rfl) ⟨688668, by rfl⟩ : syracuseStep 1836449 = 1377337) B1377337
theorem B5096881 : Blo 1222929 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B1836467 : Blo 1222929 1836467 := bstep (se 1 (by rfl) ⟨1377350, by rfl⟩ : syracuseStep 1836467 = 2754701) B2754701
theorem B4130243 : Blo 1222929 4130243 := bstep (se 1 (by rfl) ⟨3097682, by rfl⟩ : syracuseStep 4130243 = 6195365) B6195365
theorem B1836497 : Blo 1222929 1836497 := bstep (se 2 (by rfl) ⟨688686, by rfl⟩ : syracuseStep 1836497 = 1377373) B1377373
theorem B2065891 : Blo 1222929 2065891 := bstep (se 1 (by rfl) ⟨1549418, by rfl⟩ : syracuseStep 2065891 = 3098837) B3098837
theorem B1836515 : Blo 1222929 1836515 := bstep (se 1 (by rfl) ⟨1377386, by rfl⟩ : syracuseStep 1836515 = 2754773) B2754773
theorem B1836545 : Blo 1222929 1836545 := bstep (se 2 (by rfl) ⟨688704, by rfl⟩ : syracuseStep 1836545 = 1377409) B1377409
theorem B1959427 : Blo 1222929 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B1836563 : Blo 1222929 1836563 := bstep (se 1 (by rfl) ⟨1377422, by rfl⟩ : syracuseStep 1836563 = 2754845) B2754845
theorem B1836593 : Blo 1222929 1836593 := bstep (se 2 (by rfl) ⟨688722, by rfl⟩ : syracuseStep 1836593 = 1377445) B1377445
theorem B1836611 : Blo 1222929 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B1836641 : Blo 1222929 1836641 := bstep (se 2 (by rfl) ⟨688740, by rfl⟩ : syracuseStep 1836641 = 1377481) B1377481
theorem B2754161 : Blo 1222929 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B2066033 : Blo 1222929 2066033 := bstep (se 2 (by rfl) ⟨774762, by rfl⟩ : syracuseStep 2066033 = 1549525) B1549525
theorem B2754179 : Blo 1222929 2754179 := bstep (se 1 (by rfl) ⟨2065634, by rfl⟩ : syracuseStep 2754179 = 4131269) B4131269
theorem B3483299 : Blo 1222929 3483299 := bstep (se 1 (by rfl) ⟨2612474, by rfl⟩ : syracuseStep 3483299 = 5224949) B5224949
theorem B4130513 : Blo 1222929 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B3098321 : Blo 1222929 3098321 := bstep (se 2 (by rfl) ⟨1161870, by rfl⟩ : syracuseStep 3098321 = 2323741) B2323741
theorem B7440113 : Blo 1222929 7440113 := bstep (se 2 (by rfl) ⟨2790042, by rfl⟩ : syracuseStep 7440113 = 5580085) B5580085
theorem B2066161 : Blo 1222929 2066161 := bstep (se 2 (by rfl) ⟨774810, by rfl⟩ : syracuseStep 2066161 = 1549621) B1549621
theorem B3098371 : Blo 1222929 3098371 := bstep (se 1 (by rfl) ⟨2323778, by rfl⟩ : syracuseStep 3098371 = 4647557) B4647557
theorem B2066195 : Blo 1222929 2066195 := bstep (se 1 (by rfl) ⟨1549646, by rfl⟩ : syracuseStep 2066195 = 3099293) B3099293
theorem B6965027 : Blo 1222929 6965027 := bstep (se 1 (by rfl) ⟨5223770, by rfl⟩ : syracuseStep 6965027 = 10447541) B10447541
theorem B3098513 : Blo 1222929 3098513 := bstep (se 2 (by rfl) ⟨1161942, by rfl⟩ : syracuseStep 3098513 = 2323885) B2323885
theorem B2754449 : Blo 1222929 2754449 := bstep (se 2 (by rfl) ⟨1032918, by rfl⟩ : syracuseStep 2754449 = 2065837) B2065837
theorem B2754467 : Blo 1222929 2754467 := bstep (se 1 (by rfl) ⟨2065850, by rfl⟩ : syracuseStep 2754467 = 4131701) B4131701
theorem B5228707 : Blo 1222929 5228707 := bstep (se 1 (by rfl) ⟨3921530, by rfl⟩ : syracuseStep 5228707 = 7843061) B7843061
theorem B2754737 : Blo 1222929 2754737 := bstep (se 2 (by rfl) ⟨1033026, by rfl⟩ : syracuseStep 2754737 = 2066053) B2066053
theorem B2754755 : Blo 1222929 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B5810381 : Blo 1222929 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B4131053 : Blo 1222929 4131053 := bstep (se 3 (by rfl) ⟨774572, by rfl⟩ : syracuseStep 4131053 = 1549145) B1549145
theorem B1222931 : Blo 1222929 1222931 := bstep (se 1 (by rfl) ⟨917198, by rfl⟩ : syracuseStep 1222931 = 1834397) B1834397
theorem B1222947 : Blo 1222929 1222947 := bstep (se 1 (by rfl) ⟨917210, by rfl⟩ : syracuseStep 1222947 = 1834421) B1834421
theorem B4131107 : Blo 1222929 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B1222963 : Blo 1222929 1222963 := bstep (se 1 (by rfl) ⟨917222, by rfl⟩ : syracuseStep 1222963 = 1834445) B1834445
theorem B1222979 : Blo 1222929 1222979 := bstep (se 1 (by rfl) ⟨917234, by rfl⟩ : syracuseStep 1222979 = 1834469) B1834469
theorem B1222995 : Blo 1222929 1222995 := bstep (se 1 (by rfl) ⟨917246, by rfl⟩ : syracuseStep 1222995 = 1834493) B1834493
theorem B1223011 : Blo 1222929 1223011 := bstep (se 1 (by rfl) ⟨917258, by rfl⟩ : syracuseStep 1223011 = 1834517) B1834517
theorem B1223027 : Blo 1222929 1223027 := bstep (se 1 (by rfl) ⟨917270, by rfl⟩ : syracuseStep 1223027 = 1834541) B1834541
theorem B1223043 : Blo 1222929 1223043 := bstep (se 1 (by rfl) ⟨917282, by rfl⟩ : syracuseStep 1223043 = 1834565) B1834565
theorem B1223059 : Blo 1222929 1223059 := bstep (se 1 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 1223059 = 1834589) B1834589
theorem B1223075 : Blo 1222929 1223075 := bstep (se 1 (by rfl) ⟨917306, by rfl⟩ : syracuseStep 1223075 = 1834613) B1834613
theorem B1223091 : Blo 1222929 1223091 := bstep (se 1 (by rfl) ⟨917318, by rfl⟩ : syracuseStep 1223091 = 1834637) B1834637
theorem B1223107 : Blo 1222929 1223107 := bstep (se 1 (by rfl) ⟨917330, by rfl⟩ : syracuseStep 1223107 = 1834661) B1834661
theorem B1223123 : Blo 1222929 1223123 := bstep (se 1 (by rfl) ⟨917342, by rfl⟩ : syracuseStep 1223123 = 1834685) B1834685
theorem B1223139 : Blo 1222929 1223139 := bstep (se 1 (by rfl) ⟨917354, by rfl⟩ : syracuseStep 1223139 = 1834709) B1834709
theorem B1960433 : Blo 1222929 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B1223155 : Blo 1222929 1223155 := bstep (se 1 (by rfl) ⟨917366, by rfl⟩ : syracuseStep 1223155 = 1834733) B1834733
theorem B1223171 : Blo 1222929 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B1223187 : Blo 1222929 1223187 := bstep (se 1 (by rfl) ⟨917390, by rfl⟩ : syracuseStep 1223187 = 1834781) B1834781
theorem B1223203 : Blo 1222929 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B4131377 : Blo 1222929 4131377 := bstep (se 2 (by rfl) ⟨1549266, by rfl⟩ : syracuseStep 4131377 = 3098533) B3098533
theorem B1223219 : Blo 1222929 1223219 := bstep (se 1 (by rfl) ⟨917414, by rfl⟩ : syracuseStep 1223219 = 1834829) B1834829
theorem B3181123 : Blo 1222929 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B1223235 : Blo 1222929 1223235 := bstep (se 1 (by rfl) ⟨917426, by rfl⟩ : syracuseStep 1223235 = 1834853) B1834853
theorem B3975761 : Blo 1222929 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B1223251 : Blo 1222929 1223251 := bstep (se 1 (by rfl) ⟨917438, by rfl⟩ : syracuseStep 1223251 = 1834877) B1834877
theorem B1223267 : Blo 1222929 1223267 := bstep (se 1 (by rfl) ⟨917450, by rfl⟩ : syracuseStep 1223267 = 1834901) B1834901
theorem B1223283 : Blo 1222929 1223283 := bstep (se 1 (by rfl) ⟨917462, by rfl⟩ : syracuseStep 1223283 = 1834925) B1834925
theorem B1223299 : Blo 1222929 1223299 := bstep (se 1 (by rfl) ⟨917474, by rfl⟩ : syracuseStep 1223299 = 1834949) B1834949
theorem B1223315 : Blo 1222929 1223315 := bstep (se 1 (by rfl) ⟨917486, by rfl⟩ : syracuseStep 1223315 = 1834973) B1834973
theorem B1223331 : Blo 1222929 1223331 := bstep (se 1 (by rfl) ⟨917498, by rfl⟩ : syracuseStep 1223331 = 1834997) B1834997
theorem B1960625 : Blo 1222929 1960625 := bstep (se 2 (by rfl) ⟨735234, by rfl⟩ : syracuseStep 1960625 = 1470469) B1470469
theorem B1223347 : Blo 1222929 1223347 := bstep (se 1 (by rfl) ⟨917510, by rfl⟩ : syracuseStep 1223347 = 1835021) B1835021
theorem B1223363 : Blo 1222929 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B1223379 : Blo 1222929 1223379 := bstep (se 1 (by rfl) ⟨917534, by rfl⟩ : syracuseStep 1223379 = 1835069) B1835069
theorem B1223395 : Blo 1222929 1223395 := bstep (se 1 (by rfl) ⟨917546, by rfl⟩ : syracuseStep 1223395 = 1835093) B1835093
theorem B1223411 : Blo 1222929 1223411 := bstep (se 1 (by rfl) ⟨917558, by rfl⟩ : syracuseStep 1223411 = 1835117) B1835117
theorem B1223427 : Blo 1222929 1223427 := bstep (se 1 (by rfl) ⟨917570, by rfl⟩ : syracuseStep 1223427 = 1835141) B1835141
theorem B1223443 : Blo 1222929 1223443 := bstep (se 1 (by rfl) ⟨917582, by rfl⟩ : syracuseStep 1223443 = 1835165) B1835165
theorem B1223459 : Blo 1222929 1223459 := bstep (se 1 (by rfl) ⟨917594, by rfl⟩ : syracuseStep 1223459 = 1835189) B1835189
theorem B1223475 : Blo 1222929 1223475 := bstep (se 1 (by rfl) ⟨917606, by rfl⟩ : syracuseStep 1223475 = 1835213) B1835213
theorem B1223491 : Blo 1222929 1223491 := bstep (se 1 (by rfl) ⟨917618, by rfl⟩ : syracuseStep 1223491 = 1835237) B1835237
theorem B11758405 : Blo 1222929 11758405 := bstep (se 4 (by rfl) ⟨1102350, by rfl⟩ : syracuseStep 11758405 = 2204701) B2204701
theorem B1223507 : Blo 1222929 1223507 := bstep (se 1 (by rfl) ⟨917630, by rfl⟩ : syracuseStep 1223507 = 1835261) B1835261
theorem B1223523 : Blo 1222929 1223523 := bstep (se 1 (by rfl) ⟨917642, by rfl⟩ : syracuseStep 1223523 = 1835285) B1835285
theorem B3484529 : Blo 1222929 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B27200369 : Blo 1222929 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1223539 : Blo 1222929 1223539 := bstep (se 1 (by rfl) ⟨917654, by rfl⟩ : syracuseStep 1223539 = 1835309) B1835309
theorem B1223555 : Blo 1222929 1223555 := bstep (se 1 (by rfl) ⟨917666, by rfl⟩ : syracuseStep 1223555 = 1835333) B1835333
theorem B3353489 : Blo 1222929 3353489 := bstep (se 2 (by rfl) ⟨1257558, by rfl⟩ : syracuseStep 3353489 = 2515117) B2515117
theorem B1223571 : Blo 1222929 1223571 := bstep (se 1 (by rfl) ⟨917678, by rfl⟩ : syracuseStep 1223571 = 1835357) B1835357
theorem B1223587 : Blo 1222929 1223587 := bstep (se 1 (by rfl) ⟨917690, by rfl⟩ : syracuseStep 1223587 = 1835381) B1835381
theorem B1223603 : Blo 1222929 1223603 := bstep (se 1 (by rfl) ⟨917702, by rfl⟩ : syracuseStep 1223603 = 1835405) B1835405
theorem B1223619 : Blo 1222929 1223619 := bstep (se 1 (by rfl) ⟨917714, by rfl⟩ : syracuseStep 1223619 = 1835429) B1835429
theorem B1223635 : Blo 1222929 1223635 := bstep (se 1 (by rfl) ⟨917726, by rfl⟩ : syracuseStep 1223635 = 1835453) B1835453
theorem B1223651 : Blo 1222929 1223651 := bstep (se 1 (by rfl) ⟨917738, by rfl⟩ : syracuseStep 1223651 = 1835477) B1835477
theorem B3722221 : Blo 1222929 3722221 := bstep (se 3 (by rfl) ⟨697916, by rfl⟩ : syracuseStep 3722221 = 1395833) B1395833
theorem B1223667 : Blo 1222929 1223667 := bstep (se 1 (by rfl) ⟨917750, by rfl⟩ : syracuseStep 1223667 = 1835501) B1835501
theorem B1223683 : Blo 1222929 1223683 := bstep (se 1 (by rfl) ⟨917762, by rfl⟩ : syracuseStep 1223683 = 1835525) B1835525
theorem B8817677 : Blo 1222929 8817677 := bstep (se 3 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 8817677 = 3306629) B3306629
theorem B1223699 : Blo 1222929 1223699 := bstep (se 1 (by rfl) ⟨917774, by rfl⟩ : syracuseStep 1223699 = 1835549) B1835549
theorem B1223715 : Blo 1222929 1223715 := bstep (se 1 (by rfl) ⟨917786, by rfl⟩ : syracuseStep 1223715 = 1835573) B1835573
theorem B1223731 : Blo 1222929 1223731 := bstep (se 1 (by rfl) ⟨917798, by rfl⟩ : syracuseStep 1223731 = 1835597) B1835597
theorem B1223747 : Blo 1222929 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B4648013 : Blo 1222929 4648013 := bstep (se 3 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 4648013 = 1743005) B1743005
theorem B4131917 : Blo 1222929 4131917 := bstep (se 3 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 4131917 = 1549469) B1549469
theorem B1223763 : Blo 1222929 1223763 := bstep (se 1 (by rfl) ⟨917822, by rfl⟩ : syracuseStep 1223763 = 1835645) B1835645
theorem B1223779 : Blo 1222929 1223779 := bstep (se 1 (by rfl) ⟨917834, by rfl⟩ : syracuseStep 1223779 = 1835669) B1835669
theorem B6196337 : Blo 1222929 6196337 := bstep (se 2 (by rfl) ⟨2323626, by rfl⟩ : syracuseStep 6196337 = 4647253) B4647253
theorem B1223795 : Blo 1222929 1223795 := bstep (se 1 (by rfl) ⟨917846, by rfl⟩ : syracuseStep 1223795 = 1835693) B1835693
theorem B1223811 : Blo 1222929 1223811 := bstep (se 1 (by rfl) ⟨917858, by rfl⟩ : syracuseStep 1223811 = 1835717) B1835717
theorem B4131971 : Blo 1222929 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B1223827 : Blo 1222929 1223827 := bstep (se 1 (by rfl) ⟨917870, by rfl⟩ : syracuseStep 1223827 = 1835741) B1835741
theorem B1223843 : Blo 1222929 1223843 := bstep (se 1 (by rfl) ⟨917882, by rfl⟩ : syracuseStep 1223843 = 1835765) B1835765
theorem B1223859 : Blo 1222929 1223859 := bstep (se 1 (by rfl) ⟨917894, by rfl⟩ : syracuseStep 1223859 = 1835789) B1835789
theorem B1223875 : Blo 1222929 1223875 := bstep (se 1 (by rfl) ⟨917906, by rfl⟩ : syracuseStep 1223875 = 1835813) B1835813
theorem B1223891 : Blo 1222929 1223891 := bstep (se 1 (by rfl) ⟨917918, by rfl⟩ : syracuseStep 1223891 = 1835837) B1835837
theorem B1223907 : Blo 1222929 1223907 := bstep (se 1 (by rfl) ⟨917930, by rfl⟩ : syracuseStep 1223907 = 1835861) B1835861
theorem B1223923 : Blo 1222929 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1223939 : Blo 1222929 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B1223955 : Blo 1222929 1223955 := bstep (se 1 (by rfl) ⟨917966, by rfl⟩ : syracuseStep 1223955 = 1835933) B1835933
theorem B1223971 : Blo 1222929 1223971 := bstep (se 1 (by rfl) ⟨917978, by rfl⟩ : syracuseStep 1223971 = 1835957) B1835957
theorem B2321713 : Blo 1222929 2321713 := bstep (se 2 (by rfl) ⟨870642, by rfl⟩ : syracuseStep 2321713 = 1741285) B1741285
theorem B1223987 : Blo 1222929 1223987 := bstep (se 1 (by rfl) ⟨917990, by rfl⟩ : syracuseStep 1223987 = 1835981) B1835981
theorem B1224003 : Blo 1222929 1224003 := bstep (se 1 (by rfl) ⟨918002, by rfl⟩ : syracuseStep 1224003 = 1836005) B1836005
theorem B1224019 : Blo 1222929 1224019 := bstep (se 1 (by rfl) ⟨918014, by rfl⟩ : syracuseStep 1224019 = 1836029) B1836029
theorem B1224035 : Blo 1222929 1224035 := bstep (se 1 (by rfl) ⟨918026, by rfl⟩ : syracuseStep 1224035 = 1836053) B1836053
theorem B5229937 : Blo 1222929 5229937 := bstep (se 2 (by rfl) ⟨1961226, by rfl⟩ : syracuseStep 5229937 = 3922453) B3922453
theorem B1224051 : Blo 1222929 1224051 := bstep (se 1 (by rfl) ⟨918038, by rfl⟩ : syracuseStep 1224051 = 1836077) B1836077
theorem B1224067 : Blo 1222929 1224067 := bstep (se 1 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 1224067 = 1836101) B1836101
theorem B4132241 : Blo 1222929 4132241 := bstep (se 2 (by rfl) ⟨1549590, by rfl⟩ : syracuseStep 4132241 = 3099181) B3099181
theorem B1224083 : Blo 1222929 1224083 := bstep (se 1 (by rfl) ⟨918062, by rfl⟩ : syracuseStep 1224083 = 1836125) B1836125
theorem B4410787 : Blo 1222929 4410787 := bstep (se 1 (by rfl) ⟨3308090, by rfl⟩ : syracuseStep 4410787 = 6616181) B6616181
theorem B1224099 : Blo 1222929 1224099 := bstep (se 1 (by rfl) ⟨918074, by rfl⟩ : syracuseStep 1224099 = 1836149) B1836149
theorem B1224115 : Blo 1222929 1224115 := bstep (se 1 (by rfl) ⟨918086, by rfl⟩ : syracuseStep 1224115 = 1836173) B1836173
theorem B1224131 : Blo 1222929 1224131 := bstep (se 1 (by rfl) ⟨918098, by rfl⟩ : syracuseStep 1224131 = 1836197) B1836197
theorem B1224147 : Blo 1222929 1224147 := bstep (se 1 (by rfl) ⟨918110, by rfl⟩ : syracuseStep 1224147 = 1836221) B1836221
theorem B1224163 : Blo 1222929 1224163 := bstep (se 1 (by rfl) ⟨918122, by rfl⟩ : syracuseStep 1224163 = 1836245) B1836245
theorem B1224179 : Blo 1222929 1224179 := bstep (se 1 (by rfl) ⟨918134, by rfl⟩ : syracuseStep 1224179 = 1836269) B1836269
theorem B2092547 : Blo 1222929 2092547 := bstep (se 1 (by rfl) ⟨1569410, by rfl⟩ : syracuseStep 2092547 = 3138821) B3138821
theorem B1224195 : Blo 1222929 1224195 := bstep (se 1 (by rfl) ⟨918146, by rfl⟩ : syracuseStep 1224195 = 1836293) B1836293
theorem B1224211 : Blo 1222929 1224211 := bstep (se 1 (by rfl) ⟨918158, by rfl⟩ : syracuseStep 1224211 = 1836317) B1836317
theorem B1224227 : Blo 1222929 1224227 := bstep (se 1 (by rfl) ⟨918170, by rfl⟩ : syracuseStep 1224227 = 1836341) B1836341
theorem B1257011 : Blo 1222929 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B1224243 : Blo 1222929 1224243 := bstep (se 1 (by rfl) ⟨918182, by rfl⟩ : syracuseStep 1224243 = 1836365) B1836365
theorem B1224259 : Blo 1222929 1224259 := bstep (se 1 (by rfl) ⟨918194, by rfl⟩ : syracuseStep 1224259 = 1836389) B1836389
theorem B1224275 : Blo 1222929 1224275 := bstep (se 1 (by rfl) ⟨918206, by rfl⟩ : syracuseStep 1224275 = 1836413) B1836413
theorem B1224291 : Blo 1222929 1224291 := bstep (se 1 (by rfl) ⟨918218, by rfl⟩ : syracuseStep 1224291 = 1836437) B1836437
theorem B1224307 : Blo 1222929 1224307 := bstep (se 1 (by rfl) ⟨918230, by rfl⟩ : syracuseStep 1224307 = 1836461) B1836461
theorem B1224323 : Blo 1222929 1224323 := bstep (se 1 (by rfl) ⟨918242, by rfl⟩ : syracuseStep 1224323 = 1836485) B1836485
theorem B6966917 : Blo 1222929 6966917 := bstep (se 4 (by rfl) ⟨653148, by rfl⟩ : syracuseStep 6966917 = 1306297) B1306297
theorem B2092691 : Blo 1222929 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B1224339 : Blo 1222929 1224339 := bstep (se 1 (by rfl) ⟨918254, by rfl⟩ : syracuseStep 1224339 = 1836509) B1836509
theorem B7065251 : Blo 1222929 7065251 := bstep (se 1 (by rfl) ⟨5298938, by rfl⟩ : syracuseStep 7065251 = 10597877) B10597877
theorem B1224355 : Blo 1222929 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B1224371 : Blo 1222929 1224371 := bstep (se 1 (by rfl) ⟨918278, by rfl⟩ : syracuseStep 1224371 = 1836557) B1836557
theorem B1224387 : Blo 1222929 1224387 := bstep (se 1 (by rfl) ⟨918290, by rfl⟩ : syracuseStep 1224387 = 1836581) B1836581
theorem B1224403 : Blo 1222929 1224403 := bstep (se 1 (by rfl) ⟨918302, by rfl⟩ : syracuseStep 1224403 = 1836605) B1836605
theorem B1224419 : Blo 1222929 1224419 := bstep (se 1 (by rfl) ⟨918314, by rfl⟩ : syracuseStep 1224419 = 1836629) B1836629
theorem B1986401 : Blo 1222929 1986401 := bstep (se 2 (by rfl) ⟨744900, by rfl⟩ : syracuseStep 1986401 = 1489801) B1489801
theorem B14880611 : Blo 1222929 14880611 := bstep (se 1 (by rfl) ⟨11160458, by rfl⟩ : syracuseStep 14880611 = 22320917) B22320917
theorem B2092915 : Blo 1222929 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B1306579 : Blo 1222929 1306579 := bstep (se 1 (by rfl) ⟨979934, by rfl⟩ : syracuseStep 1306579 = 1959869) B1959869
theorem B7065805 : Blo 1222929 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B7835939 : Blo 1222929 7835939 := bstep (se 1 (by rfl) ⟨5876954, by rfl⟩ : syracuseStep 7835939 = 11753909) B11753909
theorem B3485987 : Blo 1222929 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B2322769 : Blo 1222929 2322769 := bstep (se 2 (by rfl) ⟨871038, by rfl⟩ : syracuseStep 2322769 = 1742077) B1742077
theorem B3305873 : Blo 1222929 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B7442885 : Blo 1222929 7442885 := bstep (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) B1395541
theorem B6197795 : Blo 1222929 6197795 := bstep (se 1 (by rfl) ⟨4648346, by rfl⟩ : syracuseStep 6197795 = 9296693) B9296693
theorem B16740917 : Blo 1222929 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B1569395 : Blo 1222929 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B3920557 : Blo 1222929 3920557 := bstep (se 3 (by rfl) ⟨735104, by rfl⟩ : syracuseStep 3920557 = 1470209) B1470209
theorem B13931189 : Blo 1222929 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B2323171 : Blo 1222929 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B3306221 : Blo 1222929 3306221 := bstep (se 3 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 3306221 = 1239833) B1239833
theorem B2323217 : Blo 1222929 2323217 := bstep (se 2 (by rfl) ⟨871206, by rfl⟩ : syracuseStep 2323217 = 1742413) B1742413
theorem B1307459 : Blo 1222929 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B3920813 : Blo 1222929 3920813 := bstep (se 3 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 3920813 = 1470305) B1470305
theorem B13595573 : Blo 1222929 13595573 := bstep (se 5 (by rfl) ⟨637292, by rfl⟩ : syracuseStep 13595573 = 1274585) B1274585
theorem B1987571 : Blo 1222929 1987571 := bstep (se 1 (by rfl) ⟨1490678, by rfl⟩ : syracuseStep 1987571 = 2981357) B2981357
theorem B2323505 : Blo 1222929 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1987649 : Blo 1222929 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B6198605 : Blo 1222929 6198605 := bstep (se 3 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 6198605 = 2324477) B2324477
theorem B7943629 : Blo 1222929 7943629 := bstep (se 3 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 7943629 = 2978861) B2978861
theorem B1742305 : Blo 1222929 1742305 := bstep (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) B1306729
theorem B1742401 : Blo 1222929 1742401 := bstep (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) B1306801
theorem B2791057 : Blo 1222929 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2324227 : Blo 1222929 2324227 := bstep (se 1 (by rfl) ⟨1743170, by rfl⟩ : syracuseStep 2324227 = 3486341) B3486341
theorem B5224333 : Blo 1222929 5224333 := bstep (se 3 (by rfl) ⟨979562, by rfl⟩ : syracuseStep 5224333 = 1959125) B1959125
theorem B9811853 : Blo 1222929 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B8820677 : Blo 1222929 8820677 := bstep (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) B1653877
theorem B6191153 : Blo 1222929 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B1742897 : Blo 1222929 1742897 := bstep (se 2 (by rfl) ⟨653586, by rfl⟩ : syracuseStep 1742897 = 1307173) B1307173
theorem B15677509 : Blo 1222929 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B5224675 : Blo 1222929 5224675 := bstep (se 1 (by rfl) ⟨3918506, by rfl⟩ : syracuseStep 5224675 = 7837013) B7837013
theorem B3922339 : Blo 1222929 3922339 := bstep (se 1 (by rfl) ⟨2941754, by rfl⟩ : syracuseStep 3922339 = 5883509) B5883509
theorem B4708813 : Blo 1222929 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B5880433 : Blo 1222929 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B25107085 : Blo 1222929 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B4127597 : Blo 1222929 4127597 := bstep (se 3 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 4127597 = 1547849) B1547849
theorem B4127651 : Blo 1222929 4127651 := bstep (se 1 (by rfl) ⟨3095738, by rfl⟩ : syracuseStep 4127651 = 6191477) B6191477
theorem B13229027 : Blo 1222929 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B2939939 : Blo 1222929 2939939 := bstep (se 1 (by rfl) ⟨2204954, by rfl⟩ : syracuseStep 2939939 = 4409909) B4409909
theorem B3095729 : Blo 1222929 3095729 := bstep (se 2 (by rfl) ⟨1160898, by rfl⟩ : syracuseStep 3095729 = 2321797) B2321797
theorem B4127921 : Blo 1222929 4127921 := bstep (se 2 (by rfl) ⟨1547970, by rfl⟩ : syracuseStep 4127921 = 3095941) B3095941
theorem B3095779 : Blo 1222929 3095779 := bstep (se 1 (by rfl) ⟨2321834, by rfl⟩ : syracuseStep 3095779 = 4643669) B4643669
theorem B2751857 : Blo 1222929 2751857 := bstep (se 2 (by rfl) ⟨1031946, by rfl⟩ : syracuseStep 2751857 = 2063893) B2063893
theorem B3095921 : Blo 1222929 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2063731 : Blo 1222929 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B2751875 : Blo 1222929 2751875 := bstep (se 1 (by rfl) ⟨2063906, by rfl⟩ : syracuseStep 2751875 = 4127813) B4127813
theorem B2612611 : Blo 1222929 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B1834403 : Blo 1222929 1834403 := bstep (se 1 (by rfl) ⟨1375802, by rfl⟩ : syracuseStep 1834403 = 2751605) B2751605
theorem B1834433 : Blo 1222929 1834433 := bstep (se 2 (by rfl) ⟨687912, by rfl⟩ : syracuseStep 1834433 = 1375825) B1375825
theorem B1834451 : Blo 1222929 1834451 := bstep (se 1 (by rfl) ⟨1375838, by rfl⟩ : syracuseStep 1834451 = 2751677) B2751677
theorem B4644323 : Blo 1222929 4644323 := bstep (se 1 (by rfl) ⟨3483242, by rfl⟩ : syracuseStep 4644323 = 6966485) B6966485
theorem B6192611 : Blo 1222929 6192611 := bstep (se 1 (by rfl) ⟨4644458, by rfl⟩ : syracuseStep 6192611 = 9288917) B9288917
theorem B1834481 : Blo 1222929 1834481 := bstep (se 2 (by rfl) ⟨687930, by rfl⟩ : syracuseStep 1834481 = 1375861) B1375861
theorem B4644337 : Blo 1222929 4644337 := bstep (se 2 (by rfl) ⟨1741626, by rfl⟩ : syracuseStep 4644337 = 3483253) B3483253
theorem B2063873 : Blo 1222929 2063873 := bstep (se 2 (by rfl) ⟨773952, by rfl⟩ : syracuseStep 2063873 = 1547905) B1547905
theorem B1834499 : Blo 1222929 1834499 := bstep (se 1 (by rfl) ⟨1375874, by rfl⟩ : syracuseStep 1834499 = 2751749) B2751749
theorem B1834529 : Blo 1222929 1834529 := bstep (se 2 (by rfl) ⟨687948, by rfl⟩ : syracuseStep 1834529 = 1375897) B1375897
theorem B1834547 : Blo 1222929 1834547 := bstep (se 1 (by rfl) ⟨1375910, by rfl⟩ : syracuseStep 1834547 = 2751821) B2751821
theorem B1834577 : Blo 1222929 1834577 := bstep (se 2 (by rfl) ⟨687966, by rfl⟩ : syracuseStep 1834577 = 1375933) B1375933
theorem B1375843 : Blo 1222929 1375843 := bstep (se 1 (by rfl) ⟨1031882, by rfl⟩ : syracuseStep 1375843 = 2063765) B2063765
theorem B1834595 : Blo 1222929 1834595 := bstep (se 1 (by rfl) ⟨1375946, by rfl⟩ : syracuseStep 1834595 = 2751893) B2751893
theorem B9420401 : Blo 1222929 9420401 := bstep (se 2 (by rfl) ⟨3532650, by rfl⟩ : syracuseStep 9420401 = 7065301) B7065301
theorem B1834625 : Blo 1222929 1834625 := bstep (se 2 (by rfl) ⟨687984, by rfl⟩ : syracuseStep 1834625 = 1375969) B1375969
theorem B2064001 : Blo 1222929 2064001 := bstep (se 2 (by rfl) ⟨774000, by rfl⟩ : syracuseStep 2064001 = 1548001) B1548001
theorem B2752145 : Blo 1222929 2752145 := bstep (se 2 (by rfl) ⟨1032054, by rfl⟩ : syracuseStep 2752145 = 2064109) B2064109
theorem B1834643 : Blo 1222929 1834643 := bstep (se 1 (by rfl) ⟨1375982, by rfl⟩ : syracuseStep 1834643 = 2751965) B2751965
theorem B2064035 : Blo 1222929 2064035 := bstep (se 1 (by rfl) ⟨1548026, by rfl⟩ : syracuseStep 2064035 = 3096053) B3096053
theorem B2752163 : Blo 1222929 2752163 := bstep (se 1 (by rfl) ⟨2064122, by rfl⟩ : syracuseStep 2752163 = 4128245) B4128245
theorem B1834673 : Blo 1222929 1834673 := bstep (se 2 (by rfl) ⟨688002, by rfl⟩ : syracuseStep 1834673 = 1376005) B1376005
theorem B1834691 : Blo 1222929 1834691 := bstep (se 1 (by rfl) ⟨1376018, by rfl⟩ : syracuseStep 1834691 = 2752037) B2752037
theorem B4128461 : Blo 1222929 4128461 := bstep (se 3 (by rfl) ⟨774086, by rfl⟩ : syracuseStep 4128461 = 1548173) B1548173
theorem B1834721 : Blo 1222929 1834721 := bstep (se 2 (by rfl) ⟨688020, by rfl⟩ : syracuseStep 1834721 = 1376041) B1376041
theorem B1375987 : Blo 1222929 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B1834739 : Blo 1222929 1834739 := bstep (se 1 (by rfl) ⟨1376054, by rfl⟩ : syracuseStep 1834739 = 2752109) B2752109
theorem B4128515 : Blo 1222929 4128515 := bstep (se 1 (by rfl) ⟨3096386, by rfl⟩ : syracuseStep 4128515 = 6192773) B6192773
theorem B1834769 : Blo 1222929 1834769 := bstep (se 2 (by rfl) ⟨688038, by rfl⟩ : syracuseStep 1834769 = 1376077) B1376077
theorem B1548067 : Blo 1222929 1548067 := bstep (se 1 (by rfl) ⟨1161050, by rfl⟩ : syracuseStep 1548067 = 2322101) B2322101
theorem B1834787 : Blo 1222929 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B2064163 : Blo 1222929 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B2940707 : Blo 1222929 2940707 := bstep (se 1 (by rfl) ⟨2205530, by rfl⟩ : syracuseStep 2940707 = 4411061) B4411061
theorem B26828597 : Blo 1222929 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B1834817 : Blo 1222929 1834817 := bstep (se 2 (by rfl) ⟨688056, by rfl⟩ : syracuseStep 1834817 = 1376113) B1376113
theorem B2613073 : Blo 1222929 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B1834835 : Blo 1222929 1834835 := bstep (se 1 (by rfl) ⟨1376126, by rfl⟩ : syracuseStep 1834835 = 2752253) B2752253
theorem B1834865 : Blo 1222929 1834865 := bstep (se 2 (by rfl) ⟨688074, by rfl⟩ : syracuseStep 1834865 = 1376149) B1376149
theorem B1376131 : Blo 1222929 1376131 := bstep (se 1 (by rfl) ⟨1032098, by rfl⟩ : syracuseStep 1376131 = 2064197) B2064197
theorem B1548163 : Blo 1222929 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1834883 : Blo 1222929 1834883 := bstep (se 1 (by rfl) ⟨1376162, by rfl⟩ : syracuseStep 1834883 = 2752325) B2752325
theorem B1834913 : Blo 1222929 1834913 := bstep (se 2 (by rfl) ⟨688092, by rfl⟩ : syracuseStep 1834913 = 1376185) B1376185
theorem B2064305 : Blo 1222929 2064305 := bstep (se 2 (by rfl) ⟨774114, by rfl⟩ : syracuseStep 2064305 = 1548229) B1548229
theorem B2752433 : Blo 1222929 2752433 := bstep (se 2 (by rfl) ⟨1032162, by rfl⟩ : syracuseStep 2752433 = 2064325) B2064325
theorem B1834931 : Blo 1222929 1834931 := bstep (se 1 (by rfl) ⟨1376198, by rfl⟩ : syracuseStep 1834931 = 2752397) B2752397
theorem B2752451 : Blo 1222929 2752451 := bstep (se 1 (by rfl) ⟨2064338, by rfl⟩ : syracuseStep 2752451 = 4128677) B4128677
theorem B1834961 : Blo 1222929 1834961 := bstep (se 2 (by rfl) ⟨688110, by rfl⟩ : syracuseStep 1834961 = 1376221) B1376221
theorem B1834979 : Blo 1222929 1834979 := bstep (se 1 (by rfl) ⟨1376234, by rfl⟩ : syracuseStep 1834979 = 2752469) B2752469
theorem B2752523 : Blo 1222929 2752523 := bstep (se 1 (by rfl) ⟨2064392, by rfl⟩ : syracuseStep 2752523 = 4128785) B4128785
theorem B1835033 : Blo 1222929 1835033 := bstep (se 2 (by rfl) ⟨688137, by rfl⟩ : syracuseStep 1835033 = 1376275) B1376275
theorem B1376311 : Blo 1222929 1376311 := bstep (se 1 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 1376311 = 2064467) B2064467
theorem B2752577 : Blo 1222929 2752577 := bstep (se 2 (by rfl) ⟨1032216, by rfl⟩ : syracuseStep 2752577 = 2064433) B2064433
theorem B6619229 : Blo 1222929 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B1835147 : Blo 1222929 1835147 := bstep (se 1 (by rfl) ⟨1376360, by rfl⟩ : syracuseStep 1835147 = 2752721) B2752721
theorem B1835159 : Blo 1222929 1835159 := bstep (se 1 (by rfl) ⟨1376369, by rfl⟩ : syracuseStep 1835159 = 2752739) B2752739
theorem B4128947 : Blo 1222929 4128947 := bstep (se 1 (by rfl) ⟨3096710, by rfl⟩ : syracuseStep 4128947 = 6193421) B6193421
theorem B1835225 : Blo 1222929 1835225 := bstep (se 2 (by rfl) ⟨688209, by rfl⟩ : syracuseStep 1835225 = 1376419) B1376419
theorem B6971609 : Blo 1222929 6971609 := bstep (se 2 (by rfl) ⟨2614353, by rfl⟩ : syracuseStep 6971609 = 5228707) B5228707
theorem B1376491 : Blo 1222929 1376491 := bstep (se 1 (by rfl) ⟨1032368, by rfl⟩ : syracuseStep 1376491 = 2064737) B2064737
theorem B9421073 : Blo 1222929 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B2752793 : Blo 1222929 2752793 := bstep (se 2 (by rfl) ⟨1032297, by rfl⟩ : syracuseStep 2752793 = 2064595) B2064595
theorem B10453313 : Blo 1222929 10453313 := bstep (se 2 (by rfl) ⟨3919992, by rfl⟩ : syracuseStep 10453313 = 7839985) B7839985
theorem B1835339 : Blo 1222929 1835339 := bstep (se 1 (by rfl) ⟨1376504, by rfl⟩ : syracuseStep 1835339 = 2753009) B2753009
theorem B1835351 : Blo 1222929 1835351 := bstep (se 1 (by rfl) ⟨1376513, by rfl⟩ : syracuseStep 1835351 = 2753027) B2753027
theorem B1376599 : Blo 1222929 1376599 := bstep (se 1 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 1376599 = 2064899) B2064899
theorem B2752883 : Blo 1222929 2752883 := bstep (se 1 (by rfl) ⟨2064662, by rfl⟩ : syracuseStep 2752883 = 4129325) B4129325
theorem B2752919 : Blo 1222929 2752919 := bstep (se 1 (by rfl) ⟨2064689, by rfl⟩ : syracuseStep 2752919 = 4129379) B4129379
theorem B2064791 : Blo 1222929 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B1835417 : Blo 1222929 1835417 := bstep (se 2 (by rfl) ⟨688281, by rfl⟩ : syracuseStep 1835417 = 1376563) B1376563
theorem B4129217 : Blo 1222929 4129217 := bstep (se 2 (by rfl) ⟨1548456, by rfl⟩ : syracuseStep 4129217 = 3096913) B3096913
theorem B3097025 : Blo 1222929 3097025 := bstep (se 2 (by rfl) ⟨1161384, by rfl⟩ : syracuseStep 3097025 = 2322769) B2322769
theorem B2204147 : Blo 1222929 2204147 := bstep (se 1 (by rfl) ⟨1653110, by rfl⟩ : syracuseStep 2204147 = 3306221) B3306221
theorem B1835531 : Blo 1222929 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B1548811 : Blo 1222929 1548811 := bstep (se 1 (by rfl) ⟨1161608, by rfl⟩ : syracuseStep 1548811 = 2323217) B2323217
theorem B1376779 : Blo 1222929 1376779 := bstep (se 1 (by rfl) ⟨1032584, by rfl⟩ : syracuseStep 1376779 = 2065169) B2065169
theorem B2064919 : Blo 1222929 2064919 := bstep (se 1 (by rfl) ⟨1548689, by rfl⟩ : syracuseStep 2064919 = 3097379) B3097379
theorem B1835543 : Blo 1222929 1835543 := bstep (se 1 (by rfl) ⟨1376657, by rfl⟩ : syracuseStep 1835543 = 2753315) B2753315
theorem B2753099 : Blo 1222929 2753099 := bstep (se 1 (by rfl) ⟨2064824, by rfl⟩ : syracuseStep 2753099 = 4129649) B4129649
theorem B1835609 : Blo 1222929 1835609 := bstep (se 2 (by rfl) ⟨688353, by rfl⟩ : syracuseStep 1835609 = 1376707) B1376707
theorem B2613875 : Blo 1222929 2613875 := bstep (se 1 (by rfl) ⟨1960406, by rfl⟩ : syracuseStep 2613875 = 3920813) B3920813
theorem B1376887 : Blo 1222929 1376887 := bstep (se 1 (by rfl) ⟨1032665, by rfl⟩ : syracuseStep 1376887 = 2065331) B2065331
theorem B2753153 : Blo 1222929 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B1835723 : Blo 1222929 1835723 := bstep (se 1 (by rfl) ⟨1376792, by rfl⟩ : syracuseStep 1835723 = 2753585) B2753585
theorem B1835735 : Blo 1222929 1835735 := bstep (se 1 (by rfl) ⟨1376801, by rfl⟩ : syracuseStep 1835735 = 2753603) B2753603
theorem B1835801 : Blo 1222929 1835801 := bstep (se 2 (by rfl) ⟨688425, by rfl⟩ : syracuseStep 1835801 = 1376851) B1376851
theorem B1377067 : Blo 1222929 1377067 := bstep (se 1 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 1377067 = 2065601) B2065601
theorem B7840577 : Blo 1222929 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B6800203 : Blo 1222929 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B2753369 : Blo 1222929 2753369 := bstep (se 2 (by rfl) ⟨1032513, by rfl⟩ : syracuseStep 2753369 = 2065027) B2065027
theorem B1835915 : Blo 1222929 1835915 := bstep (se 1 (by rfl) ⟨1376936, by rfl⟩ : syracuseStep 1835915 = 2753873) B2753873
theorem B5227409 : Blo 1222929 5227409 := bstep (se 2 (by rfl) ⟨1960278, by rfl⟩ : syracuseStep 5227409 = 3920557) B3920557
theorem B1835927 : Blo 1222929 1835927 := bstep (se 1 (by rfl) ⟨1376945, by rfl⟩ : syracuseStep 1835927 = 2753891) B2753891
theorem B1377175 : Blo 1222929 1377175 := bstep (se 1 (by rfl) ⟨1032881, by rfl⟩ : syracuseStep 1377175 = 2065763) B2065763
theorem B21201841 : Blo 1222929 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B2753459 : Blo 1222929 2753459 := bstep (se 1 (by rfl) ⟨2065094, by rfl⟩ : syracuseStep 2753459 = 4130189) B4130189
theorem B2753495 : Blo 1222929 2753495 := bstep (se 1 (by rfl) ⟨2065121, by rfl⟩ : syracuseStep 2753495 = 4130243) B4130243
theorem B3097561 : Blo 1222929 3097561 := bstep (se 2 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 3097561 = 2323171) B2323171
theorem B1835993 : Blo 1222929 1835993 := bstep (se 2 (by rfl) ⟨688497, by rfl⟩ : syracuseStep 1835993 = 1376995) B1376995
theorem B4129757 : Blo 1222929 4129757 := bstep (se 3 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 4129757 = 1548659) B1548659
theorem B8815661 : Blo 1222929 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B1836107 : Blo 1222929 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B1377355 : Blo 1222929 1377355 := bstep (se 1 (by rfl) ⟨1033016, by rfl⟩ : syracuseStep 1377355 = 2066033) B2066033
theorem B1836119 : Blo 1222929 1836119 := bstep (se 1 (by rfl) ⟨1377089, by rfl⟩ : syracuseStep 1836119 = 2754179) B2754179
theorem B2753675 : Blo 1222929 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B2065547 : Blo 1222929 2065547 := bstep (se 1 (by rfl) ⟨1549160, by rfl⟩ : syracuseStep 2065547 = 3098321) B3098321
theorem B1836185 : Blo 1222929 1836185 := bstep (se 2 (by rfl) ⟨688569, by rfl⟩ : syracuseStep 1836185 = 1377139) B1377139
theorem B1377463 : Blo 1222929 1377463 := bstep (se 1 (by rfl) ⟨1033097, by rfl⟩ : syracuseStep 1377463 = 2066195) B2066195
theorem B2753729 : Blo 1222929 2753729 := bstep (se 2 (by rfl) ⟨1032648, by rfl⟩ : syracuseStep 2753729 = 2065297) B2065297
theorem B6194393 : Blo 1222929 6194393 := bstep (se 2 (by rfl) ⟨2322897, by rfl⟩ : syracuseStep 6194393 = 4645795) B4645795
theorem B2065675 : Blo 1222929 2065675 := bstep (se 1 (by rfl) ⟨1549256, by rfl⟩ : syracuseStep 2065675 = 3098513) B3098513
theorem B1836299 : Blo 1222929 1836299 := bstep (se 1 (by rfl) ⟨1377224, by rfl⟩ : syracuseStep 1836299 = 2754449) B2754449
theorem B1836311 : Blo 1222929 1836311 := bstep (se 1 (by rfl) ⟨1377233, by rfl⟩ : syracuseStep 1836311 = 2754467) B2754467
theorem B1836377 : Blo 1222929 1836377 := bstep (se 2 (by rfl) ⟨688641, by rfl⟩ : syracuseStep 1836377 = 1377283) B1377283
theorem B2753945 : Blo 1222929 2753945 := bstep (se 2 (by rfl) ⟨1032729, by rfl⟩ : syracuseStep 2753945 = 2065459) B2065459
theorem B2065817 : Blo 1222929 2065817 := bstep (se 2 (by rfl) ⟨774681, by rfl⟩ : syracuseStep 2065817 = 1549363) B1549363
theorem B1836491 : Blo 1222929 1836491 := bstep (se 1 (by rfl) ⟨1377368, by rfl⟩ : syracuseStep 1836491 = 2754737) B2754737
theorem B1836503 : Blo 1222929 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B2754035 : Blo 1222929 2754035 := bstep (se 1 (by rfl) ⟨2065526, by rfl⟩ : syracuseStep 2754035 = 4131053) B4131053
theorem B2754071 : Blo 1222929 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B2065945 : Blo 1222929 2065945 := bstep (se 2 (by rfl) ⟨774729, by rfl⟩ : syracuseStep 2065945 = 1549459) B1549459
theorem B1836569 : Blo 1222929 1836569 := bstep (se 2 (by rfl) ⟨688713, by rfl⟩ : syracuseStep 1836569 = 1377427) B1377427
theorem B10602029 : Blo 1222929 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B2754251 : Blo 1222929 2754251 := bstep (se 1 (by rfl) ⟨2065688, by rfl⟩ : syracuseStep 2754251 = 4131377) B4131377
theorem B2754305 : Blo 1222929 2754305 := bstep (se 2 (by rfl) ⟨1032864, by rfl⟩ : syracuseStep 2754305 = 2065729) B2065729
theorem B5228333 : Blo 1222929 5228333 := bstep (se 3 (by rfl) ⟨980312, by rfl⟩ : syracuseStep 5228333 = 1960625) B1960625
theorem B6973249 : Blo 1222929 6973249 := bstep (se 2 (by rfl) ⟨2614968, by rfl⟩ : syracuseStep 6973249 = 5229937) B5229937
theorem B3483481 : Blo 1222929 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B2754521 : Blo 1222929 2754521 := bstep (se 2 (by rfl) ⟨1032945, by rfl⟩ : syracuseStep 2754521 = 2065891) B2065891
theorem B1959959 : Blo 1222929 1959959 := bstep (se 1 (by rfl) ⟨1469969, by rfl⟩ : syracuseStep 1959959 = 2939939) B2939939
theorem B3098675 : Blo 1222929 3098675 := bstep (se 1 (by rfl) ⟨2324006, by rfl⟩ : syracuseStep 3098675 = 4648013) B4648013
theorem B2754611 : Blo 1222929 2754611 := bstep (se 1 (by rfl) ⟨2065958, by rfl⟩ : syracuseStep 2754611 = 4131917) B4131917
theorem B4130891 : Blo 1222929 4130891 := bstep (se 1 (by rfl) ⟨3098168, by rfl⟩ : syracuseStep 4130891 = 6196337) B6196337
theorem B2754647 : Blo 1222929 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B3721409 : Blo 1222929 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B2754827 : Blo 1222929 2754827 := bstep (se 1 (by rfl) ⟨2066120, by rfl⟩ : syracuseStep 2754827 = 4132241) B4132241
theorem B1222935 : Blo 1222929 1222935 := bstep (se 1 (by rfl) ⟨917201, by rfl⟩ : syracuseStep 1222935 = 1834403) B1834403
theorem B1222955 : Blo 1222929 1222955 := bstep (se 1 (by rfl) ⟨917216, by rfl⟩ : syracuseStep 1222955 = 1834433) B1834433
theorem B1222967 : Blo 1222929 1222967 := bstep (se 1 (by rfl) ⟨917225, by rfl⟩ : syracuseStep 1222967 = 1834451) B1834451
theorem B2754881 : Blo 1222929 2754881 := bstep (se 2 (by rfl) ⟨1033080, by rfl⟩ : syracuseStep 2754881 = 2066161) B2066161
theorem B1222987 : Blo 1222929 1222987 := bstep (se 1 (by rfl) ⟨917240, by rfl⟩ : syracuseStep 1222987 = 1834481) B1834481
theorem B1222999 : Blo 1222929 1222999 := bstep (se 1 (by rfl) ⟨917249, by rfl⟩ : syracuseStep 1222999 = 1834499) B1834499
theorem B1395031 : Blo 1222929 1395031 := bstep (se 1 (by rfl) ⟨1046273, by rfl⟩ : syracuseStep 1395031 = 2092547) B2092547
theorem B4131161 : Blo 1222929 4131161 := bstep (se 2 (by rfl) ⟨1549185, by rfl⟩ : syracuseStep 4131161 = 3098371) B3098371
theorem B3098969 : Blo 1222929 3098969 := bstep (se 2 (by rfl) ⟨1162113, by rfl⟩ : syracuseStep 3098969 = 2324227) B2324227
theorem B1223019 : Blo 1222929 1223019 := bstep (se 1 (by rfl) ⟨917264, by rfl⟩ : syracuseStep 1223019 = 1834529) B1834529
theorem B1223031 : Blo 1222929 1223031 := bstep (se 1 (by rfl) ⟨917273, by rfl⟩ : syracuseStep 1223031 = 1834547) B1834547
theorem B1223051 : Blo 1222929 1223051 := bstep (se 1 (by rfl) ⟨917288, by rfl⟩ : syracuseStep 1223051 = 1834577) B1834577
theorem B1223063 : Blo 1222929 1223063 := bstep (se 1 (by rfl) ⟨917297, by rfl⟩ : syracuseStep 1223063 = 1834595) B1834595
theorem B1223083 : Blo 1222929 1223083 := bstep (se 1 (by rfl) ⟨917312, by rfl⟩ : syracuseStep 1223083 = 1834625) B1834625
theorem B1223095 : Blo 1222929 1223095 := bstep (se 1 (by rfl) ⟨917321, by rfl⟩ : syracuseStep 1223095 = 1834643) B1834643
theorem B1395127 : Blo 1222929 1395127 := bstep (se 1 (by rfl) ⟨1046345, by rfl⟩ : syracuseStep 1395127 = 2092691) B2092691
theorem B3484097 : Blo 1222929 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B1223115 : Blo 1222929 1223115 := bstep (se 1 (by rfl) ⟨917336, by rfl⟩ : syracuseStep 1223115 = 1834673) B1834673
theorem B1223127 : Blo 1222929 1223127 := bstep (se 1 (by rfl) ⟨917345, by rfl⟩ : syracuseStep 1223127 = 1834691) B1834691
theorem B1223147 : Blo 1222929 1223147 := bstep (se 1 (by rfl) ⟨917360, by rfl⟩ : syracuseStep 1223147 = 1834721) B1834721
theorem B1223159 : Blo 1222929 1223159 := bstep (se 1 (by rfl) ⟨917369, by rfl⟩ : syracuseStep 1223159 = 1834739) B1834739
theorem B1223179 : Blo 1222929 1223179 := bstep (se 1 (by rfl) ⟨917384, by rfl⟩ : syracuseStep 1223179 = 1834769) B1834769
theorem B6965777 : Blo 1222929 6965777 := bstep (se 2 (by rfl) ⟨2612166, by rfl⟩ : syracuseStep 6965777 = 5224333) B5224333
theorem B1223191 : Blo 1222929 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B1960471 : Blo 1222929 1960471 := bstep (se 1 (by rfl) ⟨1470353, by rfl⟩ : syracuseStep 1960471 = 2940707) B2940707
theorem B17885731 : Blo 1222929 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B1223211 : Blo 1222929 1223211 := bstep (se 1 (by rfl) ⟨917408, by rfl⟩ : syracuseStep 1223211 = 1834817) B1834817
theorem B1223223 : Blo 1222929 1223223 := bstep (se 1 (by rfl) ⟨917417, by rfl⟩ : syracuseStep 1223223 = 1834835) B1834835
theorem B1223243 : Blo 1222929 1223243 := bstep (se 1 (by rfl) ⟨917432, by rfl⟩ : syracuseStep 1223243 = 1834865) B1834865
theorem B1223255 : Blo 1222929 1223255 := bstep (se 1 (by rfl) ⟨917441, by rfl⟩ : syracuseStep 1223255 = 1834883) B1834883
theorem B1223275 : Blo 1222929 1223275 := bstep (se 1 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 1223275 = 1834913) B1834913
theorem B1223287 : Blo 1222929 1223287 := bstep (se 1 (by rfl) ⟨917465, by rfl⟩ : syracuseStep 1223287 = 1834931) B1834931
theorem B1223307 : Blo 1222929 1223307 := bstep (se 1 (by rfl) ⟨917480, by rfl⟩ : syracuseStep 1223307 = 1834961) B1834961
theorem B1223319 : Blo 1222929 1223319 := bstep (se 1 (by rfl) ⟨917489, by rfl⟩ : syracuseStep 1223319 = 1834979) B1834979
theorem B1223339 : Blo 1222929 1223339 := bstep (se 1 (by rfl) ⟨917504, by rfl⟩ : syracuseStep 1223339 = 1835009) B1835009
theorem B1223351 : Blo 1222929 1223351 := bstep (se 1 (by rfl) ⟨917513, by rfl⟩ : syracuseStep 1223351 = 1835027) B1835027
theorem B1223371 : Blo 1222929 1223371 := bstep (se 1 (by rfl) ⟨917528, by rfl⟩ : syracuseStep 1223371 = 1835057) B1835057
theorem B1223383 : Blo 1222929 1223383 := bstep (se 1 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 1223383 = 1835075) B1835075
theorem B1223403 : Blo 1222929 1223403 := bstep (se 1 (by rfl) ⟨917552, by rfl⟩ : syracuseStep 1223403 = 1835105) B1835105
theorem B1223415 : Blo 1222929 1223415 := bstep (se 1 (by rfl) ⟨917561, by rfl⟩ : syracuseStep 1223415 = 1835123) B1835123
theorem B1223435 : Blo 1222929 1223435 := bstep (se 1 (by rfl) ⟨917576, by rfl⟩ : syracuseStep 1223435 = 1835153) B1835153
theorem B1223447 : Blo 1222929 1223447 := bstep (se 1 (by rfl) ⟨917585, by rfl⟩ : syracuseStep 1223447 = 1835171) B1835171
theorem B1223467 : Blo 1222929 1223467 := bstep (se 1 (by rfl) ⟨917600, by rfl⟩ : syracuseStep 1223467 = 1835201) B1835201
theorem B6196013 : Blo 1222929 6196013 := bstep (se 3 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 6196013 = 2323505) B2323505
theorem B4647725 : Blo 1222929 4647725 := bstep (se 3 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 4647725 = 1742897) B1742897
theorem B5581619 : Blo 1222929 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B1223479 : Blo 1222929 1223479 := bstep (se 1 (by rfl) ⟨917609, by rfl⟩ : syracuseStep 1223479 = 1835219) B1835219
theorem B1223499 : Blo 1222929 1223499 := bstep (se 1 (by rfl) ⟨917624, by rfl⟩ : syracuseStep 1223499 = 1835249) B1835249
theorem B1223511 : Blo 1222929 1223511 := bstep (se 1 (by rfl) ⟨917633, by rfl⟩ : syracuseStep 1223511 = 1835267) B1835267
theorem B1223531 : Blo 1222929 1223531 := bstep (se 1 (by rfl) ⟨917648, by rfl⟩ : syracuseStep 1223531 = 1835297) B1835297
theorem B1223543 : Blo 1222929 1223543 := bstep (se 1 (by rfl) ⟨917657, by rfl⟩ : syracuseStep 1223543 = 1835315) B1835315
theorem B1223563 : Blo 1222929 1223563 := bstep (se 1 (by rfl) ⟨917672, by rfl⟩ : syracuseStep 1223563 = 1835345) B1835345
theorem B1960843 : Blo 1222929 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B1223575 : Blo 1222929 1223575 := bstep (se 1 (by rfl) ⟨917681, by rfl⟩ : syracuseStep 1223575 = 1835363) B1835363
theorem B1223595 : Blo 1222929 1223595 := bstep (se 1 (by rfl) ⟨917696, by rfl⟩ : syracuseStep 1223595 = 1835393) B1835393
theorem B1223607 : Blo 1222929 1223607 := bstep (se 1 (by rfl) ⟨917705, by rfl⟩ : syracuseStep 1223607 = 1835411) B1835411
theorem B1223627 : Blo 1222929 1223627 := bstep (se 1 (by rfl) ⟨917720, by rfl⟩ : syracuseStep 1223627 = 1835441) B1835441
theorem B1223639 : Blo 1222929 1223639 := bstep (se 1 (by rfl) ⟨917729, by rfl⟩ : syracuseStep 1223639 = 1835459) B1835459
theorem B6966233 : Blo 1222929 6966233 := bstep (se 2 (by rfl) ⟨2612337, by rfl⟩ : syracuseStep 6966233 = 5224675) B5224675
theorem B1223659 : Blo 1222929 1223659 := bstep (se 1 (by rfl) ⟨917744, by rfl⟩ : syracuseStep 1223659 = 1835489) B1835489
theorem B1223671 : Blo 1222929 1223671 := bstep (se 1 (by rfl) ⟨917753, by rfl⟩ : syracuseStep 1223671 = 1835507) B1835507
theorem B9292805 : Blo 1222929 9292805 := bstep (se 4 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 9292805 = 1742401) B1742401
theorem B1223691 : Blo 1222929 1223691 := bstep (se 1 (by rfl) ⟨917768, by rfl⟩ : syracuseStep 1223691 = 1835537) B1835537
theorem B1223703 : Blo 1222929 1223703 := bstep (se 1 (by rfl) ⟨917777, by rfl⟩ : syracuseStep 1223703 = 1835555) B1835555
theorem B4131863 : Blo 1222929 4131863 := bstep (se 1 (by rfl) ⟨3098897, by rfl⟩ : syracuseStep 4131863 = 6197795) B6197795
theorem B11160611 : Blo 1222929 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B1223723 : Blo 1222929 1223723 := bstep (se 1 (by rfl) ⟨917792, by rfl⟩ : syracuseStep 1223723 = 1835585) B1835585
theorem B1223735 : Blo 1222929 1223735 := bstep (se 1 (by rfl) ⟨917801, by rfl⟩ : syracuseStep 1223735 = 1835603) B1835603
theorem B1223755 : Blo 1222929 1223755 := bstep (se 1 (by rfl) ⟨917816, by rfl⟩ : syracuseStep 1223755 = 1835633) B1835633
theorem B1223767 : Blo 1222929 1223767 := bstep (se 1 (by rfl) ⟨917825, by rfl⟩ : syracuseStep 1223767 = 1835651) B1835651
theorem B1223787 : Blo 1222929 1223787 := bstep (se 1 (by rfl) ⟨917840, by rfl⟩ : syracuseStep 1223787 = 1835681) B1835681
theorem B1223799 : Blo 1222929 1223799 := bstep (se 1 (by rfl) ⟨917849, by rfl⟩ : syracuseStep 1223799 = 1835699) B1835699
theorem B1223819 : Blo 1222929 1223819 := bstep (se 1 (by rfl) ⟨917864, by rfl⟩ : syracuseStep 1223819 = 1835729) B1835729
theorem B1961099 : Blo 1222929 1961099 := bstep (se 1 (by rfl) ⟨1470824, by rfl⟩ : syracuseStep 1961099 = 2941649) B2941649
theorem B1223831 : Blo 1222929 1223831 := bstep (se 1 (by rfl) ⟨917873, by rfl⟩ : syracuseStep 1223831 = 1835747) B1835747
theorem B1223851 : Blo 1222929 1223851 := bstep (se 1 (by rfl) ⟨917888, by rfl⟩ : syracuseStep 1223851 = 1835777) B1835777
theorem B1223863 : Blo 1222929 1223863 := bstep (se 1 (by rfl) ⟨917897, by rfl⟩ : syracuseStep 1223863 = 1835795) B1835795
theorem B1223883 : Blo 1222929 1223883 := bstep (se 1 (by rfl) ⟨917912, by rfl⟩ : syracuseStep 1223883 = 1835825) B1835825
theorem B1223895 : Blo 1222929 1223895 := bstep (se 1 (by rfl) ⟨917921, by rfl⟩ : syracuseStep 1223895 = 1835843) B1835843
theorem B5229785 : Blo 1222929 5229785 := bstep (se 2 (by rfl) ⟨1961169, by rfl⟩ : syracuseStep 5229785 = 3922339) B3922339
theorem B1223915 : Blo 1222929 1223915 := bstep (se 1 (by rfl) ⟨917936, by rfl⟩ : syracuseStep 1223915 = 1835873) B1835873
theorem B1223927 : Blo 1222929 1223927 := bstep (se 1 (by rfl) ⟨917945, by rfl⟩ : syracuseStep 1223927 = 1835891) B1835891
theorem B1223947 : Blo 1222929 1223947 := bstep (se 1 (by rfl) ⟨917960, by rfl⟩ : syracuseStep 1223947 = 1835921) B1835921
theorem B6278417 : Blo 1222929 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B1223959 : Blo 1222929 1223959 := bstep (se 1 (by rfl) ⟨917969, by rfl⟩ : syracuseStep 1223959 = 1835939) B1835939
theorem B1223979 : Blo 1222929 1223979 := bstep (se 1 (by rfl) ⟨917984, by rfl⟩ : syracuseStep 1223979 = 1835969) B1835969
theorem B1240375 : Blo 1222929 1240375 := bstep (se 1 (by rfl) ⟨930281, by rfl⟩ : syracuseStep 1240375 = 1860563) B1860563
theorem B1223991 : Blo 1222929 1223991 := bstep (se 1 (by rfl) ⟨917993, by rfl⟩ : syracuseStep 1223991 = 1835987) B1835987
theorem B1224011 : Blo 1222929 1224011 := bstep (se 1 (by rfl) ⟨918008, by rfl⟩ : syracuseStep 1224011 = 1836017) B1836017
theorem B1961291 : Blo 1222929 1961291 := bstep (se 1 (by rfl) ⟨1470968, by rfl⟩ : syracuseStep 1961291 = 2941937) B2941937
theorem B1224023 : Blo 1222929 1224023 := bstep (se 1 (by rfl) ⟨918017, by rfl⟩ : syracuseStep 1224023 = 1836035) B1836035
theorem B1224043 : Blo 1222929 1224043 := bstep (se 1 (by rfl) ⟨918032, by rfl⟩ : syracuseStep 1224043 = 1836065) B1836065
theorem B1224055 : Blo 1222929 1224055 := bstep (se 1 (by rfl) ⟨918041, by rfl⟩ : syracuseStep 1224055 = 1836083) B1836083
theorem B1224075 : Blo 1222929 1224075 := bstep (se 1 (by rfl) ⟨918056, by rfl⟩ : syracuseStep 1224075 = 1836113) B1836113
theorem B1224087 : Blo 1222929 1224087 := bstep (se 1 (by rfl) ⟨918065, by rfl⟩ : syracuseStep 1224087 = 1836131) B1836131
theorem B1224107 : Blo 1222929 1224107 := bstep (se 1 (by rfl) ⟨918080, by rfl⟩ : syracuseStep 1224107 = 1836161) B1836161
theorem B1224119 : Blo 1222929 1224119 := bstep (se 1 (by rfl) ⟨918089, by rfl⟩ : syracuseStep 1224119 = 1836179) B1836179
theorem B1224139 : Blo 1222929 1224139 := bstep (se 1 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 1224139 = 1836209) B1836209
theorem B1224151 : Blo 1222929 1224151 := bstep (se 1 (by rfl) ⟨918113, by rfl⟩ : syracuseStep 1224151 = 1836227) B1836227
theorem B1224171 : Blo 1222929 1224171 := bstep (se 1 (by rfl) ⟨918128, by rfl⟩ : syracuseStep 1224171 = 1836257) B1836257
theorem B1224183 : Blo 1222929 1224183 := bstep (se 1 (by rfl) ⟨918137, by rfl⟩ : syracuseStep 1224183 = 1836275) B1836275
theorem B1224203 : Blo 1222929 1224203 := bstep (se 1 (by rfl) ⟨918152, by rfl⟩ : syracuseStep 1224203 = 1836305) B1836305
theorem B33476113 : Blo 1222929 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B1306135 : Blo 1222929 1306135 := bstep (se 1 (by rfl) ⟨979601, by rfl⟩ : syracuseStep 1306135 = 1959203) B1959203
theorem B1224215 : Blo 1222929 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B1224235 : Blo 1222929 1224235 := bstep (se 1 (by rfl) ⟨918176, by rfl⟩ : syracuseStep 1224235 = 1836353) B1836353
theorem B4648499 : Blo 1222929 4648499 := bstep (se 1 (by rfl) ⟨3486374, by rfl⟩ : syracuseStep 4648499 = 6972749) B6972749
theorem B4132403 : Blo 1222929 4132403 := bstep (se 1 (by rfl) ⟨3099302, by rfl⟩ : syracuseStep 4132403 = 6198605) B6198605
theorem B1224247 : Blo 1222929 1224247 := bstep (se 1 (by rfl) ⟨918185, by rfl⟩ : syracuseStep 1224247 = 1836371) B1836371
theorem B1224267 : Blo 1222929 1224267 := bstep (se 1 (by rfl) ⟨918200, by rfl⟩ : syracuseStep 1224267 = 1836401) B1836401
theorem B1224279 : Blo 1222929 1224279 := bstep (se 1 (by rfl) ⟨918209, by rfl⟩ : syracuseStep 1224279 = 1836419) B1836419
theorem B1224299 : Blo 1222929 1224299 := bstep (se 1 (by rfl) ⟨918224, by rfl⟩ : syracuseStep 1224299 = 1836449) B1836449
theorem B1224311 : Blo 1222929 1224311 := bstep (se 1 (by rfl) ⟨918233, by rfl⟩ : syracuseStep 1224311 = 1836467) B1836467
theorem B1224331 : Blo 1222929 1224331 := bstep (se 1 (by rfl) ⟨918248, by rfl⟩ : syracuseStep 1224331 = 1836497) B1836497
theorem B1224343 : Blo 1222929 1224343 := bstep (se 1 (by rfl) ⟨918257, by rfl⟩ : syracuseStep 1224343 = 1836515) B1836515
theorem B1224363 : Blo 1222929 1224363 := bstep (se 1 (by rfl) ⟨918272, by rfl⟩ : syracuseStep 1224363 = 1836545) B1836545
theorem B1224375 : Blo 1222929 1224375 := bstep (se 1 (by rfl) ⟨918281, by rfl⟩ : syracuseStep 1224375 = 1836563) B1836563
theorem B1224395 : Blo 1222929 1224395 := bstep (se 1 (by rfl) ⟨918296, by rfl⟩ : syracuseStep 1224395 = 1836593) B1836593
theorem B1224407 : Blo 1222929 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B1224427 : Blo 1222929 1224427 := bstep (se 1 (by rfl) ⟨918320, by rfl⟩ : syracuseStep 1224427 = 1836641) B1836641
theorem B2322199 : Blo 1222929 2322199 := bstep (se 1 (by rfl) ⟨1741649, by rfl⟩ : syracuseStep 2322199 = 3483299) B3483299
theorem B4960075 : Blo 1222929 4960075 := bstep (se 1 (by rfl) ⟨3720056, by rfl⟩ : syracuseStep 4960075 = 7440113) B7440113
theorem B6541235 : Blo 1222929 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B1306955 : Blo 1222929 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B3486169 : Blo 1222929 3486169 := bstep (se 2 (by rfl) ⟨1307313, by rfl⟩ : syracuseStep 3486169 = 2614627) B2614627
theorem B6795841 : Blo 1222929 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B2323019 : Blo 1222929 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B18133579 : Blo 1222929 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B2323073 : Blo 1222929 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B8819351 : Blo 1222929 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B5878451 : Blo 1222929 5878451 := bstep (se 1 (by rfl) ⟨4408838, by rfl⟩ : syracuseStep 5878451 = 8817677) B8817677
theorem B7844701 : Blo 1222929 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B3486557 : Blo 1222929 3486557 := bstep (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) B1307459
theorem B5297069 : Blo 1222929 5297069 := bstep (se 3 (by rfl) ⟨993200, by rfl⟩ : syracuseStep 5297069 = 1986401) B1986401
theorem B6280267 : Blo 1222929 6280267 := bstep (se 1 (by rfl) ⟨4710200, by rfl⟩ : syracuseStep 6280267 = 9420401) B9420401
theorem B36254861 : Blo 1222929 36254861 := bstep (se 3 (by rfl) ⟨6797786, by rfl⟩ : syracuseStep 36254861 = 13595573) B13595573
theorem B2790553 : Blo 1222929 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B1742105 : Blo 1222929 1742105 := bstep (se 2 (by rfl) ⟨653289, by rfl⟩ : syracuseStep 1742105 = 1306579) B1306579
theorem B9295235 : Blo 1222929 9295235 := bstep (se 1 (by rfl) ⟨6971426, by rfl⟩ : syracuseStep 9295235 = 13942853) B13942853
theorem B20903345 : Blo 1222929 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B5223959 : Blo 1222929 5223959 := bstep (se 1 (by rfl) ⟨3917969, by rfl⟩ : syracuseStep 5223959 = 7835939) B7835939
theorem B2323991 : Blo 1222929 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B2938457 : Blo 1222929 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B9287459 : Blo 1222929 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B1742743 : Blo 1222929 1742743 := bstep (se 1 (by rfl) ⟨1307057, by rfl⟩ : syracuseStep 1742743 = 2614115) B2614115
theorem B1325047 : Blo 1222929 1325047 := bstep (se 1 (by rfl) ⟨993785, by rfl⟩ : syracuseStep 1325047 = 1987571) B1987571
theorem B1325099 : Blo 1222929 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B4241497 : Blo 1222929 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B15677873 : Blo 1222929 15677873 := bstep (se 2 (by rfl) ⟨5879202, by rfl⟩ : syracuseStep 15677873 = 11758405) B11758405
theorem B19847693 : Blo 1222929 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B4643351 : Blo 1222929 4643351 := bstep (se 1 (by rfl) ⟨3482513, by rfl⟩ : syracuseStep 4643351 = 6965027) B6965027
theorem B5880451 : Blo 1222929 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B4962961 : Blo 1222929 4962961 := bstep (se 2 (by rfl) ⟨1861110, by rfl⟩ : syracuseStep 4962961 = 3722221) B3722221
theorem B4127435 : Blo 1222929 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B3873587 : Blo 1222929 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B4127705 : Blo 1222929 4127705 := bstep (se 2 (by rfl) ⟨1547889, by rfl⟩ : syracuseStep 4127705 = 3095779) B3095779
theorem B4185053 : Blo 1222929 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B3095617 : Blo 1222929 3095617 := bstep (se 2 (by rfl) ⟨1160856, by rfl⟩ : syracuseStep 3095617 = 2321713) B2321713
theorem B4775057 : Blo 1222929 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B2751641 : Blo 1222929 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B5881049 : Blo 1222929 5881049 := bstep (se 2 (by rfl) ⟨2205393, by rfl⟩ : syracuseStep 5881049 = 4410787) B4410787
theorem B2751731 : Blo 1222929 2751731 := bstep (se 1 (by rfl) ⟨2063798, by rfl⟩ : syracuseStep 2751731 = 4127597) B4127597
theorem B2235659 : Blo 1222929 2235659 := bstep (se 1 (by rfl) ⟨1676744, by rfl⟩ : syracuseStep 2235659 = 3353489) B3353489
theorem B10591505 : Blo 1222929 10591505 := bstep (se 2 (by rfl) ⟨3971814, by rfl⟩ : syracuseStep 10591505 = 7943629) B7943629
theorem B2751767 : Blo 1222929 2751767 := bstep (se 1 (by rfl) ⟨2063825, by rfl⟩ : syracuseStep 2751767 = 4127651) B4127651
theorem B6192449 : Blo 1222929 6192449 := bstep (se 2 (by rfl) ⟨2322168, by rfl⟩ : syracuseStep 6192449 = 4644337) B4644337
theorem B2612569 : Blo 1222929 2612569 := bstep (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) B1959427
theorem B2063819 : Blo 1222929 2063819 := bstep (se 1 (by rfl) ⟨1547864, by rfl⟩ : syracuseStep 2063819 = 3095729) B3095729
theorem B2751947 : Blo 1222929 2751947 := bstep (se 1 (by rfl) ⟨2063960, by rfl⟩ : syracuseStep 2751947 = 4127921) B4127921
theorem B53632469 : Blo 1222929 53632469 := bstep (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) B1257011
theorem B1834457 : Blo 1222929 1834457 := bstep (se 2 (by rfl) ⟨687921, by rfl⟩ : syracuseStep 1834457 = 1375843) B1375843
theorem B2752001 : Blo 1222929 2752001 := bstep (se 2 (by rfl) ⟨1032000, by rfl⟩ : syracuseStep 2752001 = 2064001) B2064001
theorem B1834571 : Blo 1222929 1834571 := bstep (se 1 (by rfl) ⟨1375928, by rfl⟩ : syracuseStep 1834571 = 2751857) B2751857
theorem B2063947 : Blo 1222929 2063947 := bstep (se 1 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 2063947 = 3095921) B3095921
theorem B1834583 : Blo 1222929 1834583 := bstep (se 1 (by rfl) ⟨1375937, by rfl⟩ : syracuseStep 1834583 = 2751875) B2751875
theorem B3096215 : Blo 1222929 3096215 := bstep (se 1 (by rfl) ⟨2322161, by rfl⟩ : syracuseStep 3096215 = 4644323) B4644323
theorem B4128407 : Blo 1222929 4128407 := bstep (se 1 (by rfl) ⟨3096305, by rfl⟩ : syracuseStep 4128407 = 6192611) B6192611
theorem B1834649 : Blo 1222929 1834649 := bstep (se 2 (by rfl) ⟨687993, by rfl⟩ : syracuseStep 1834649 = 1375987) B1375987
theorem B1375915 : Blo 1222929 1375915 := bstep (se 1 (by rfl) ⟨1031936, by rfl⟩ : syracuseStep 1375915 = 2063873) B2063873
theorem B2064089 : Blo 1222929 2064089 := bstep (se 2 (by rfl) ⟨774033, by rfl⟩ : syracuseStep 2064089 = 1548067) B1548067
theorem B2752217 : Blo 1222929 2752217 := bstep (se 2 (by rfl) ⟨1032081, by rfl⟩ : syracuseStep 2752217 = 2064163) B2064163
theorem B4644611 : Blo 1222929 4644611 := bstep (se 1 (by rfl) ⟨3483458, by rfl⟩ : syracuseStep 4644611 = 6966917) B6966917
theorem B1834763 : Blo 1222929 1834763 := bstep (se 1 (by rfl) ⟨1376072, by rfl⟩ : syracuseStep 1834763 = 2752145) B2752145
theorem B1376023 : Blo 1222929 1376023 := bstep (se 1 (by rfl) ⟨1032017, by rfl⟩ : syracuseStep 1376023 = 2064035) B2064035
theorem B1834775 : Blo 1222929 1834775 := bstep (se 1 (by rfl) ⟨1376081, by rfl⟩ : syracuseStep 1834775 = 2752163) B2752163
theorem B4710167 : Blo 1222929 4710167 := bstep (se 1 (by rfl) ⟨3532625, by rfl⟩ : syracuseStep 4710167 = 7065251) B7065251
theorem B2752307 : Blo 1222929 2752307 := bstep (se 1 (by rfl) ⟨2064230, by rfl⟩ : syracuseStep 2752307 = 4128461) B4128461
theorem B2752343 : Blo 1222929 2752343 := bstep (se 1 (by rfl) ⟨2064257, by rfl⟩ : syracuseStep 2752343 = 4128515) B4128515
theorem B1834841 : Blo 1222929 1834841 := bstep (se 2 (by rfl) ⟨688065, by rfl⟩ : syracuseStep 1834841 = 1376131) B1376131
theorem B2064217 : Blo 1222929 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B9920407 : Blo 1222929 9920407 := bstep (se 1 (by rfl) ⟨7440305, by rfl⟩ : syracuseStep 9920407 = 14880611) B14880611
theorem B1376203 : Blo 1222929 1376203 := bstep (se 1 (by rfl) ⟨1032152, by rfl⟩ : syracuseStep 1376203 = 2064305) B2064305
theorem B1834955 : Blo 1222929 1834955 := bstep (se 1 (by rfl) ⟨1376216, by rfl⟩ : syracuseStep 1834955 = 2752433) B2752433
theorem B1834967 : Blo 1222929 1834967 := bstep (se 1 (by rfl) ⟨1376225, by rfl⟩ : syracuseStep 1834967 = 2752451) B2752451
theorem B1835015 : Blo 1222929 1835015 := bstep (se 1 (by rfl) ⟨1376261, by rfl⟩ : syracuseStep 1835015 = 2752523) B2752523
theorem B1835051 : Blo 1222929 1835051 := bstep (se 1 (by rfl) ⟨1376288, by rfl⟩ : syracuseStep 1835051 = 2752577) B2752577
theorem B1835081 : Blo 1222929 1835081 := bstep (se 2 (by rfl) ⟨688155, by rfl⟩ : syracuseStep 1835081 = 1376311) B1376311
theorem B2752631 : Blo 1222929 2752631 := bstep (se 1 (by rfl) ⟨2064473, by rfl⟩ : syracuseStep 2752631 = 4128947) B4128947
theorem B1835195 : Blo 1222929 1835195 := bstep (se 1 (by rfl) ⟨1376396, by rfl⟩ : syracuseStep 1835195 = 2752793) B2752793
theorem B1835255 : Blo 1222929 1835255 := bstep (se 1 (by rfl) ⟨1376441, by rfl⟩ : syracuseStep 1835255 = 2752883) B2752883
theorem B1835279 : Blo 1222929 1835279 := bstep (se 1 (by rfl) ⟨1376459, by rfl⟩ : syracuseStep 1835279 = 2752919) B2752919
theorem B1376527 : Blo 1222929 1376527 := bstep (se 1 (by rfl) ⟨1032395, by rfl⟩ : syracuseStep 1376527 = 2064791) B2064791
theorem B2752811 : Blo 1222929 2752811 := bstep (se 1 (by rfl) ⟨2064608, by rfl⟩ : syracuseStep 2752811 = 4129217) B4129217
theorem B2064683 : Blo 1222929 2064683 := bstep (se 1 (by rfl) ⟨1548512, by rfl⟩ : syracuseStep 2064683 = 3097025) B3097025
theorem B1835321 : Blo 1222929 1835321 := bstep (se 2 (by rfl) ⟨688245, by rfl⟩ : syracuseStep 1835321 = 1376491) B1376491
theorem B1835399 : Blo 1222929 1835399 := bstep (se 1 (by rfl) ⟨1376549, by rfl⟩ : syracuseStep 1835399 = 2753099) B2753099
theorem B1835435 : Blo 1222929 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B1548715 : Blo 1222929 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B1860041 : Blo 1222929 1860041 := bstep (se 2 (by rfl) ⟨697515, by rfl⟩ : syracuseStep 1860041 = 1395031) B1395031
theorem B1835465 : Blo 1222929 1835465 := bstep (se 2 (by rfl) ⟨688299, by rfl⟩ : syracuseStep 1835465 = 1376599) B1376599
theorem B5227051 : Blo 1222929 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B1835579 : Blo 1222929 1835579 := bstep (se 1 (by rfl) ⟨1376684, by rfl⟩ : syracuseStep 1835579 = 2753369) B2753369
theorem B1860169 : Blo 1222929 1860169 := bstep (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) B1395127
theorem B3531379 : Blo 1222929 3531379 := bstep (se 1 (by rfl) ⟨2648534, by rfl⟩ : syracuseStep 3531379 = 5297069) B5297069
theorem B1835639 : Blo 1222929 1835639 := bstep (se 1 (by rfl) ⟨1376729, by rfl⟩ : syracuseStep 1835639 = 2753459) B2753459
theorem B1835663 : Blo 1222929 1835663 := bstep (se 1 (by rfl) ⟨1376747, by rfl⟩ : syracuseStep 1835663 = 2753495) B2753495
theorem B2753171 : Blo 1222929 2753171 := bstep (se 1 (by rfl) ⟨2064878, by rfl⟩ : syracuseStep 2753171 = 4129757) B4129757
theorem B2065081 : Blo 1222929 2065081 := bstep (se 2 (by rfl) ⟨774405, by rfl⟩ : syracuseStep 2065081 = 1548811) B1548811
theorem B1835705 : Blo 1222929 1835705 := bstep (se 2 (by rfl) ⟨688389, by rfl⟩ : syracuseStep 1835705 = 1376779) B1376779
theorem B2753225 : Blo 1222929 2753225 := bstep (se 2 (by rfl) ⟨1032459, by rfl⟩ : syracuseStep 2753225 = 2064919) B2064919
theorem B2613961 : Blo 1222929 2613961 := bstep (se 2 (by rfl) ⟨980235, by rfl⟩ : syracuseStep 2613961 = 1960471) B1960471
theorem B23847641 : Blo 1222929 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B4645613 : Blo 1222929 4645613 := bstep (se 3 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 4645613 = 1742105) B1742105
theorem B9061121 : Blo 1222929 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B1835783 : Blo 1222929 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B1377031 : Blo 1222929 1377031 := bstep (se 1 (by rfl) ⟨1032773, by rfl⟩ : syracuseStep 1377031 = 2065547) B2065547
theorem B26469125 : Blo 1222929 26469125 := bstep (se 4 (by rfl) ⟨2481480, by rfl⟩ : syracuseStep 26469125 = 4962961) B4962961
theorem B1835819 : Blo 1222929 1835819 := bstep (se 1 (by rfl) ⟨1376864, by rfl⟩ : syracuseStep 1835819 = 2753729) B2753729
theorem B4129595 : Blo 1222929 4129595 := bstep (se 1 (by rfl) ⟨3097196, by rfl⟩ : syracuseStep 4129595 = 6194393) B6194393
theorem B1835849 : Blo 1222929 1835849 := bstep (se 2 (by rfl) ⟨688443, by rfl⟩ : syracuseStep 1835849 = 1376887) B1376887
theorem B7840601 : Blo 1222929 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B1835963 : Blo 1222929 1835963 := bstep (se 1 (by rfl) ⟨1376972, by rfl⟩ : syracuseStep 1835963 = 2753945) B2753945
theorem B1377211 : Blo 1222929 1377211 := bstep (se 1 (by rfl) ⟨1032908, by rfl⟩ : syracuseStep 1377211 = 2065817) B2065817
theorem B13935563 : Blo 1222929 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B1836023 : Blo 1222929 1836023 := bstep (se 1 (by rfl) ⟨1377017, by rfl⟩ : syracuseStep 1836023 = 2754035) B2754035
theorem B3482639 : Blo 1222929 3482639 := bstep (se 1 (by rfl) ⟨2611979, by rfl⟩ : syracuseStep 3482639 = 5223959) B5223959
theorem B1836047 : Blo 1222929 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B1836089 : Blo 1222929 1836089 := bstep (se 2 (by rfl) ⟨688533, by rfl⟩ : syracuseStep 1836089 = 1377067) B1377067
theorem B1836167 : Blo 1222929 1836167 := bstep (se 1 (by rfl) ⟨1377125, by rfl⟩ : syracuseStep 1836167 = 2754251) B2754251
theorem B26461333 : Blo 1222929 26461333 := bstep (se 6 (by rfl) ⟨620187, by rfl⟩ : syracuseStep 26461333 = 1240375) B1240375
theorem B1836203 : Blo 1222929 1836203 := bstep (se 1 (by rfl) ⟨1377152, by rfl⟩ : syracuseStep 1836203 = 2754305) B2754305
theorem B2614457 : Blo 1222929 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B1836233 : Blo 1222929 1836233 := bstep (se 2 (by rfl) ⟨688587, by rfl⟩ : syracuseStep 1836233 = 1377175) B1377175
theorem B4130081 : Blo 1222929 4130081 := bstep (se 2 (by rfl) ⟨1548780, by rfl⟩ : syracuseStep 4130081 = 3097561) B3097561
theorem B1836347 : Blo 1222929 1836347 := bstep (se 1 (by rfl) ⟨1377260, by rfl⟩ : syracuseStep 1836347 = 2754521) B2754521
theorem B2065783 : Blo 1222929 2065783 := bstep (se 1 (by rfl) ⟨1549337, by rfl⟩ : syracuseStep 2065783 = 3098675) B3098675
theorem B1836407 : Blo 1222929 1836407 := bstep (se 1 (by rfl) ⟨1377305, by rfl⟩ : syracuseStep 1836407 = 2754611) B2754611
theorem B2753927 : Blo 1222929 2753927 := bstep (se 1 (by rfl) ⟨2065445, by rfl⟩ : syracuseStep 2753927 = 4130891) B4130891
theorem B1836431 : Blo 1222929 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B8373689 : Blo 1222929 8373689 := bstep (se 2 (by rfl) ⟨3140133, by rfl⟩ : syracuseStep 8373689 = 6280267) B6280267
theorem B1836473 : Blo 1222929 1836473 := bstep (se 2 (by rfl) ⟨688677, by rfl⟩ : syracuseStep 1836473 = 1377355) B1377355
theorem B28272077 : Blo 1222929 28272077 := bstep (se 3 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 28272077 = 10602029) B10602029
theorem B1836551 : Blo 1222929 1836551 := bstep (se 1 (by rfl) ⟨1377413, by rfl⟩ : syracuseStep 1836551 = 2754827) B2754827
theorem B6194717 : Blo 1222929 6194717 := bstep (se 3 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 6194717 = 2323019) B2323019
theorem B3720737 : Blo 1222929 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B1836587 : Blo 1222929 1836587 := bstep (se 1 (by rfl) ⟨1377440, by rfl⟩ : syracuseStep 1836587 = 2754881) B2754881
theorem B2754107 : Blo 1222929 2754107 := bstep (se 1 (by rfl) ⟨2065580, by rfl⟩ : syracuseStep 2754107 = 4131161) B4131161
theorem B2065979 : Blo 1222929 2065979 := bstep (se 1 (by rfl) ⟨1549484, by rfl⟩ : syracuseStep 2065979 = 3098969) B3098969
theorem B1836617 : Blo 1222929 1836617 := bstep (se 2 (by rfl) ⟨688731, by rfl⟩ : syracuseStep 1836617 = 1377463) B1377463
theorem B13231795 : Blo 1222929 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B2754233 : Blo 1222929 2754233 := bstep (se 2 (by rfl) ⟨1032837, by rfl⟩ : syracuseStep 2754233 = 2065675) B2065675
theorem B3483425 : Blo 1222929 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B4130675 : Blo 1222929 4130675 := bstep (se 1 (by rfl) ⟨3098006, by rfl⟩ : syracuseStep 4130675 = 6196013) B6196013
theorem B3098483 : Blo 1222929 3098483 := bstep (se 1 (by rfl) ⟨2323862, by rfl⟩ : syracuseStep 3098483 = 4647725) B4647725
theorem B3721079 : Blo 1222929 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B6195203 : Blo 1222929 6195203 := bstep (se 1 (by rfl) ⟨4646402, by rfl⟩ : syracuseStep 6195203 = 9292805) B9292805
theorem B2754575 : Blo 1222929 2754575 := bstep (se 1 (by rfl) ⟨2065931, by rfl⟩ : syracuseStep 2754575 = 4131863) B4131863
theorem B7440407 : Blo 1222929 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B2754593 : Blo 1222929 2754593 := bstep (se 2 (by rfl) ⟨1032972, by rfl⟩ : syracuseStep 2754593 = 2065945) B2065945
theorem B1222971 : Blo 1222929 1222971 := bstep (se 1 (by rfl) ⟨917228, by rfl⟩ : syracuseStep 1222971 = 1834457) B1834457
theorem B3098999 : Blo 1222929 3098999 := bstep (se 1 (by rfl) ⟨2324249, by rfl⟩ : syracuseStep 3098999 = 4648499) B4648499
theorem B2754935 : Blo 1222929 2754935 := bstep (se 1 (by rfl) ⟨2066201, by rfl⟩ : syracuseStep 2754935 = 4132403) B4132403
theorem B1223047 : Blo 1222929 1223047 := bstep (se 1 (by rfl) ⟨917285, by rfl⟩ : syracuseStep 1223047 = 1834571) B1834571
theorem B1223055 : Blo 1222929 1223055 := bstep (se 1 (by rfl) ⟨917291, by rfl⟩ : syracuseStep 1223055 = 1834583) B1834583
theorem B6613433 : Blo 1222929 6613433 := bstep (se 2 (by rfl) ⟨2480037, by rfl⟩ : syracuseStep 6613433 = 4960075) B4960075
theorem B1223099 : Blo 1222929 1223099 := bstep (se 1 (by rfl) ⟨917324, by rfl⟩ : syracuseStep 1223099 = 1834649) B1834649
theorem B1223175 : Blo 1222929 1223175 := bstep (se 1 (by rfl) ⟨917381, by rfl⟩ : syracuseStep 1223175 = 1834763) B1834763
theorem B1223183 : Blo 1222929 1223183 := bstep (se 1 (by rfl) ⟨917387, by rfl⟩ : syracuseStep 1223183 = 1834775) B1834775
theorem B3140111 : Blo 1222929 3140111 := bstep (se 1 (by rfl) ⟨2355083, by rfl⟩ : syracuseStep 3140111 = 4710167) B4710167
theorem B1223227 : Blo 1222929 1223227 := bstep (se 1 (by rfl) ⟨917420, by rfl⟩ : syracuseStep 1223227 = 1834841) B1834841
theorem B4360823 : Blo 1222929 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B1223303 : Blo 1222929 1223303 := bstep (se 1 (by rfl) ⟨917477, by rfl⟩ : syracuseStep 1223303 = 1834955) B1834955
theorem B1223311 : Blo 1222929 1223311 := bstep (se 1 (by rfl) ⟨917483, by rfl⟩ : syracuseStep 1223311 = 1834967) B1834967
theorem B1223355 : Blo 1222929 1223355 := bstep (se 1 (by rfl) ⟨917516, by rfl⟩ : syracuseStep 1223355 = 1835033) B1835033
theorem B1223431 : Blo 1222929 1223431 := bstep (se 1 (by rfl) ⟨917573, by rfl⟩ : syracuseStep 1223431 = 1835147) B1835147
theorem B1223439 : Blo 1222929 1223439 := bstep (se 1 (by rfl) ⟨917579, by rfl⟩ : syracuseStep 1223439 = 1835159) B1835159
theorem B3533597 : Blo 1222929 3533597 := bstep (se 3 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 3533597 = 1325099) B1325099
theorem B5655329 : Blo 1222929 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B1223483 : Blo 1222929 1223483 := bstep (se 1 (by rfl) ⟨917612, by rfl⟩ : syracuseStep 1223483 = 1835225) B1835225
theorem B4647739 : Blo 1222929 4647739 := bstep (se 1 (by rfl) ⟨3485804, by rfl⟩ : syracuseStep 4647739 = 6971609) B6971609
theorem B1223559 : Blo 1222929 1223559 := bstep (se 1 (by rfl) ⟨917669, by rfl⟩ : syracuseStep 1223559 = 1835339) B1835339
theorem B1223567 : Blo 1222929 1223567 := bstep (se 1 (by rfl) ⟨917675, by rfl⟩ : syracuseStep 1223567 = 1835351) B1835351
theorem B1223611 : Blo 1222929 1223611 := bstep (se 1 (by rfl) ⟨917708, by rfl⟩ : syracuseStep 1223611 = 1835417) B1835417
theorem B1469431 : Blo 1222929 1469431 := bstep (se 1 (by rfl) ⟨1102073, by rfl⟩ : syracuseStep 1469431 = 2204147) B2204147
theorem B1223687 : Blo 1222929 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B1223695 : Blo 1222929 1223695 := bstep (se 1 (by rfl) ⟨917771, by rfl⟩ : syracuseStep 1223695 = 1835543) B1835543
theorem B1223739 : Blo 1222929 1223739 := bstep (se 1 (by rfl) ⟨917804, by rfl⟩ : syracuseStep 1223739 = 1835609) B1835609
theorem B1223815 : Blo 1222929 1223815 := bstep (se 1 (by rfl) ⟨917861, by rfl⟩ : syracuseStep 1223815 = 1835723) B1835723
theorem B1223823 : Blo 1222929 1223823 := bstep (se 1 (by rfl) ⟨917867, by rfl⟩ : syracuseStep 1223823 = 1835735) B1835735
theorem B1223867 : Blo 1222929 1223867 := bstep (se 1 (by rfl) ⟨917900, by rfl⟩ : syracuseStep 1223867 = 1835801) B1835801
theorem B1223943 : Blo 1222929 1223943 := bstep (se 1 (by rfl) ⟨917957, by rfl⟩ : syracuseStep 1223943 = 1835915) B1835915
theorem B3484939 : Blo 1222929 3484939 := bstep (se 1 (by rfl) ⟨2613704, by rfl⟩ : syracuseStep 3484939 = 5227409) B5227409
theorem B1223951 : Blo 1222929 1223951 := bstep (se 1 (by rfl) ⟨917963, by rfl⟩ : syracuseStep 1223951 = 1835927) B1835927
theorem B4648225 : Blo 1222929 4648225 := bstep (se 2 (by rfl) ⟨1743084, by rfl⟩ : syracuseStep 4648225 = 3486169) B3486169
theorem B1223995 : Blo 1222929 1223995 := bstep (se 1 (by rfl) ⟨917996, by rfl⟩ : syracuseStep 1223995 = 1835993) B1835993
theorem B5877107 : Blo 1222929 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B1224071 : Blo 1222929 1224071 := bstep (se 1 (by rfl) ⟨918053, by rfl⟩ : syracuseStep 1224071 = 1836107) B1836107
theorem B1224079 : Blo 1222929 1224079 := bstep (se 1 (by rfl) ⟨918059, by rfl⟩ : syracuseStep 1224079 = 1836119) B1836119
theorem B24169907 : Blo 1222929 24169907 := bstep (se 1 (by rfl) ⟨18127430, by rfl⟩ : syracuseStep 24169907 = 36254861) B36254861
theorem B24178105 : Blo 1222929 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B1224123 : Blo 1222929 1224123 := bstep (se 1 (by rfl) ⟨918092, by rfl⟩ : syracuseStep 1224123 = 1836185) B1836185
theorem B1224199 : Blo 1222929 1224199 := bstep (se 1 (by rfl) ⟨918149, by rfl⟩ : syracuseStep 1224199 = 1836299) B1836299
theorem B1224207 : Blo 1222929 1224207 := bstep (se 1 (by rfl) ⟨918155, by rfl⟩ : syracuseStep 1224207 = 1836311) B1836311
theorem B3485213 : Blo 1222929 3485213 := bstep (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) B1306955
theorem B5230109 : Blo 1222929 5230109 := bstep (se 3 (by rfl) ⟨980645, by rfl⟩ : syracuseStep 5230109 = 1961291) B1961291
theorem B1224251 : Blo 1222929 1224251 := bstep (se 1 (by rfl) ⟨918188, by rfl⟩ : syracuseStep 1224251 = 1836377) B1836377
theorem B6196823 : Blo 1222929 6196823 := bstep (se 1 (by rfl) ⟨4647617, by rfl⟩ : syracuseStep 6196823 = 9295235) B9295235
theorem B1224327 : Blo 1222929 1224327 := bstep (se 1 (by rfl) ⟨918245, by rfl⟩ : syracuseStep 1224327 = 1836491) B1836491
theorem B1224335 : Blo 1222929 1224335 := bstep (se 1 (by rfl) ⟨918251, by rfl⟩ : syracuseStep 1224335 = 1836503) B1836503
theorem B1224379 : Blo 1222929 1224379 := bstep (se 1 (by rfl) ⟨918284, by rfl⟩ : syracuseStep 1224379 = 1836569) B1836569
theorem B3485555 : Blo 1222929 3485555 := bstep (se 1 (by rfl) ⟨2614166, by rfl⟩ : syracuseStep 3485555 = 5228333) B5228333
theorem B1306639 : Blo 1222929 1306639 := bstep (se 1 (by rfl) ⟨979979, by rfl⟩ : syracuseStep 1306639 = 1959959) B1959959
theorem B6197309 : Blo 1222929 6197309 := bstep (se 3 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 6197309 = 2323991) B2323991
theorem B7835885 : Blo 1222929 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B2322731 : Blo 1222929 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B15675869 : Blo 1222929 15675869 := bstep (se 3 (by rfl) ⟨2939225, by rfl⟩ : syracuseStep 15675869 = 5878451) B5878451
theorem B2790035 : Blo 1222929 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B44634817 : Blo 1222929 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B1741513 : Blo 1222929 1741513 := bstep (se 2 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 1741513 = 1306135) B1306135
theorem B1307399 : Blo 1222929 1307399 := bstep (se 1 (by rfl) ⟨980549, by rfl⟩ : syracuseStep 1307399 = 1961099) B1961099
theorem B3183371 : Blo 1222929 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B3920699 : Blo 1222929 3920699 := bstep (se 1 (by rfl) ⟨2940524, by rfl⟩ : syracuseStep 3920699 = 5881049) B5881049
theorem B3486523 : Blo 1222929 3486523 := bstep (se 1 (by rfl) ⟨2614892, by rfl⟩ : syracuseStep 3486523 = 5229785) B5229785
theorem B35754979 : Blo 1222929 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B13227209 : Blo 1222929 13227209 := bstep (se 2 (by rfl) ⟨4960203, by rfl⟩ : syracuseStep 13227209 = 9920407) B9920407
theorem B2323657 : Blo 1222929 2323657 := bstep (se 2 (by rfl) ⟨871371, by rfl⟩ : syracuseStep 2323657 = 1742743) B1742743
theorem B1766729 : Blo 1222929 1766729 := bstep (se 2 (by rfl) ⟨662523, by rfl⟩ : syracuseStep 1766729 = 1325047) B1325047
theorem B4412819 : Blo 1222929 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B6280715 : Blo 1222929 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B6968875 : Blo 1222929 6968875 := bstep (se 1 (by rfl) ⟨5226656, by rfl⟩ : syracuseStep 6968875 = 10453313) B10453313
theorem B5879567 : Blo 1222929 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B41318261 : Blo 1222929 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B2324371 : Blo 1222929 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B5961757 : Blo 1222929 5961757 := bstep (se 3 (by rfl) ⟨1117829, by rfl⟩ : syracuseStep 5961757 = 2235659) B2235659
theorem B9066937 : Blo 1222929 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B10459601 : Blo 1222929 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B6191639 : Blo 1222929 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B28269121 : Blo 1222929 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B4127489 : Blo 1222929 4127489 := bstep (se 2 (by rfl) ⟨1547808, by rfl⟩ : syracuseStep 4127489 = 3095617) B3095617
theorem B2480939 : Blo 1222929 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B10451915 : Blo 1222929 10451915 := bstep (se 1 (by rfl) ⟨7838936, by rfl⟩ : syracuseStep 10451915 = 15677873) B15677873
theorem B6970333 : Blo 1222929 6970333 := bstep (se 3 (by rfl) ⟨1306937, by rfl⟩ : syracuseStep 6970333 = 2613875) B2613875
theorem B4643851 : Blo 1222929 4643851 := bstep (se 1 (by rfl) ⟨3482888, by rfl⟩ : syracuseStep 4643851 = 6965777) B6965777
theorem B3095567 : Blo 1222929 3095567 := bstep (se 1 (by rfl) ⟨2321675, by rfl⟩ : syracuseStep 3095567 = 4643351) B4643351
theorem B2751623 : Blo 1222929 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B2751803 : Blo 1222929 2751803 := bstep (se 1 (by rfl) ⟨2063852, by rfl⟩ : syracuseStep 2751803 = 4127705) B4127705
theorem B4644155 : Blo 1222929 4644155 := bstep (se 1 (by rfl) ⟨3483116, by rfl⟩ : syracuseStep 4644155 = 6966233) B6966233
theorem B2751929 : Blo 1222929 2751929 := bstep (se 2 (by rfl) ⟨1031973, by rfl⟩ : syracuseStep 2751929 = 2063947) B2063947
theorem B1834427 : Blo 1222929 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B1834487 : Blo 1222929 1834487 := bstep (se 1 (by rfl) ⟨1375865, by rfl⟩ : syracuseStep 1834487 = 2751731) B2751731
theorem B7061003 : Blo 1222929 7061003 := bstep (se 1 (by rfl) ⟨5295752, by rfl⟩ : syracuseStep 7061003 = 10591505) B10591505
theorem B4185611 : Blo 1222929 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B1834511 : Blo 1222929 1834511 := bstep (se 1 (by rfl) ⟨1375883, by rfl⟩ : syracuseStep 1834511 = 2751767) B2751767
theorem B4128299 : Blo 1222929 4128299 := bstep (se 1 (by rfl) ⟨3096224, by rfl⟩ : syracuseStep 4128299 = 6192449) B6192449
theorem B1834553 : Blo 1222929 1834553 := bstep (se 2 (by rfl) ⟨687957, by rfl⟩ : syracuseStep 1834553 = 1375915) B1375915
theorem B1375879 : Blo 1222929 1375879 := bstep (se 1 (by rfl) ⟨1031909, by rfl⟩ : syracuseStep 1375879 = 2063819) B2063819
theorem B1834631 : Blo 1222929 1834631 := bstep (se 1 (by rfl) ⟨1375973, by rfl⟩ : syracuseStep 1834631 = 2751947) B2751947
theorem B1834667 : Blo 1222929 1834667 := bstep (se 1 (by rfl) ⟨1376000, by rfl⟩ : syracuseStep 1834667 = 2752001) B2752001
theorem B1834697 : Blo 1222929 1834697 := bstep (se 2 (by rfl) ⟨688011, by rfl⟩ : syracuseStep 1834697 = 1376023) B1376023
theorem B3096265 : Blo 1222929 3096265 := bstep (se 2 (by rfl) ⟨1161099, by rfl⟩ : syracuseStep 3096265 = 2322199) B2322199
theorem B9297665 : Blo 1222929 9297665 := bstep (se 2 (by rfl) ⟨3486624, by rfl⟩ : syracuseStep 9297665 = 6973249) B6973249
theorem B2064143 : Blo 1222929 2064143 := bstep (se 1 (by rfl) ⟨1548107, by rfl⟩ : syracuseStep 2064143 = 3096215) B3096215
theorem B2752271 : Blo 1222929 2752271 := bstep (se 1 (by rfl) ⟨2064203, by rfl⟩ : syracuseStep 2752271 = 4128407) B4128407
theorem B2752289 : Blo 1222929 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B4644641 : Blo 1222929 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B1376059 : Blo 1222929 1376059 := bstep (se 1 (by rfl) ⟨1032044, by rfl⟩ : syracuseStep 1376059 = 2064089) B2064089
theorem B1834811 : Blo 1222929 1834811 := bstep (se 1 (by rfl) ⟨1376108, by rfl⟩ : syracuseStep 1834811 = 2752217) B2752217
theorem B3096407 : Blo 1222929 3096407 := bstep (se 1 (by rfl) ⟨2322305, by rfl⟩ : syracuseStep 3096407 = 4644611) B4644611
theorem B1834871 : Blo 1222929 1834871 := bstep (se 1 (by rfl) ⟨1376153, by rfl⟩ : syracuseStep 1834871 = 2752307) B2752307
theorem B1834895 : Blo 1222929 1834895 := bstep (se 1 (by rfl) ⟨1376171, by rfl⟩ : syracuseStep 1834895 = 2752343) B2752343
theorem B1834937 : Blo 1222929 1834937 := bstep (se 2 (by rfl) ⟨688101, by rfl⟩ : syracuseStep 1834937 = 1376203) B1376203
theorem B1835087 : Blo 1222929 1835087 := bstep (se 1 (by rfl) ⟨1376315, by rfl⟩ : syracuseStep 1835087 = 2752631) B2752631
theorem B1835207 : Blo 1222929 1835207 := bstep (se 1 (by rfl) ⟨1376405, by rfl⟩ : syracuseStep 1835207 = 2752811) B2752811
theorem B1548487 : Blo 1222929 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B1376455 : Blo 1222929 1376455 := bstep (se 1 (by rfl) ⟨1032341, by rfl⟩ : syracuseStep 1376455 = 2064683) B2064683
theorem B1835369 : Blo 1222929 1835369 := bstep (se 2 (by rfl) ⟨688263, by rfl⟩ : syracuseStep 1835369 = 1376527) B1376527
theorem B1835447 : Blo 1222929 1835447 := bstep (se 1 (by rfl) ⟨1376585, by rfl⟩ : syracuseStep 1835447 = 2753171) B2753171
theorem B1860023 : Blo 1222929 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B1835483 : Blo 1222929 1835483 := bstep (se 1 (by rfl) ⟨1376612, by rfl⟩ : syracuseStep 1835483 = 2753225) B2753225
theorem B3097075 : Blo 1222929 3097075 := bstep (se 1 (by rfl) ⟨2322806, by rfl⟩ : syracuseStep 3097075 = 4645613) B4645613
theorem B17646083 : Blo 1222929 17646083 := bstep (se 1 (by rfl) ⟨13234562, by rfl⟩ : syracuseStep 17646083 = 26469125) B26469125
theorem B2122247 : Blo 1222929 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2753063 : Blo 1222929 2753063 := bstep (se 1 (by rfl) ⟨2064797, by rfl⟩ : syracuseStep 2753063 = 4129595) B4129595
theorem B2613799 : Blo 1222929 2613799 := bstep (se 1 (by rfl) ⟨1960349, by rfl⟩ : syracuseStep 2613799 = 3920699) B3920699
theorem B2064953 : Blo 1222929 2064953 := bstep (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) B1548715
theorem B5227067 : Blo 1222929 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B9290375 : Blo 1222929 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B37692161 : Blo 1222929 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B2753387 : Blo 1222929 2753387 := bstep (se 1 (by rfl) ⟨2065040, by rfl⟩ : syracuseStep 2753387 = 4130081) B4130081
theorem B4711277 : Blo 1222929 4711277 := bstep (se 3 (by rfl) ⟨883364, by rfl⟩ : syracuseStep 4711277 = 1766729) B1766729
theorem B2753441 : Blo 1222929 2753441 := bstep (se 2 (by rfl) ⟨1032540, by rfl⟩ : syracuseStep 2753441 = 2065081) B2065081
theorem B1835951 : Blo 1222929 1835951 := bstep (se 1 (by rfl) ⟨1376963, by rfl⟩ : syracuseStep 1835951 = 2753927) B2753927
theorem B4187143 : Blo 1222929 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B1836041 : Blo 1222929 1836041 := bstep (se 2 (by rfl) ⟨688515, by rfl⟩ : syracuseStep 1836041 = 1377031) B1377031
theorem B4129811 : Blo 1222929 4129811 := bstep (se 1 (by rfl) ⟨3097358, by rfl⟩ : syracuseStep 4129811 = 6194717) B6194717
theorem B1836071 : Blo 1222929 1836071 := bstep (se 1 (by rfl) ⟨1377053, by rfl⟩ : syracuseStep 1836071 = 2754107) B2754107
theorem B1377319 : Blo 1222929 1377319 := bstep (se 1 (by rfl) ⟨1032989, by rfl⟩ : syracuseStep 1377319 = 2065979) B2065979
theorem B1836155 : Blo 1222929 1836155 := bstep (se 1 (by rfl) ⟨1377116, by rfl⟩ : syracuseStep 1836155 = 2754233) B2754233
theorem B2753783 : Blo 1222929 2753783 := bstep (se 1 (by rfl) ⟨2065337, by rfl⟩ : syracuseStep 2753783 = 4130675) B4130675
theorem B2065655 : Blo 1222929 2065655 := bstep (se 1 (by rfl) ⟨1549241, by rfl⟩ : syracuseStep 2065655 = 3098483) B3098483
theorem B1836281 : Blo 1222929 1836281 := bstep (se 2 (by rfl) ⟨688605, by rfl⟩ : syracuseStep 1836281 = 1377211) B1377211
theorem B1959241 : Blo 1222929 1959241 := bstep (se 2 (by rfl) ⟨734715, by rfl⟩ : syracuseStep 1959241 = 1469431) B1469431
theorem B4130135 : Blo 1222929 4130135 := bstep (se 1 (by rfl) ⟨3097601, by rfl⟩ : syracuseStep 4130135 = 6195203) B6195203
theorem B1836383 : Blo 1222929 1836383 := bstep (se 1 (by rfl) ⟨1377287, by rfl⟩ : syracuseStep 1836383 = 2754575) B2754575
theorem B1836395 : Blo 1222929 1836395 := bstep (se 1 (by rfl) ⟨1377296, by rfl⟩ : syracuseStep 1836395 = 2754593) B2754593
theorem B2065999 : Blo 1222929 2065999 := bstep (se 1 (by rfl) ⟨1549499, by rfl⟩ : syracuseStep 2065999 = 3098999) B3098999
theorem B1836623 : Blo 1222929 1836623 := bstep (se 1 (by rfl) ⟨1377467, by rfl⟩ : syracuseStep 1836623 = 2754935) B2754935
theorem B3098209 : Blo 1222929 3098209 := bstep (se 2 (by rfl) ⟨1161828, by rfl⟩ : syracuseStep 3098209 = 2323657) B2323657
theorem B4408955 : Blo 1222929 4408955 := bstep (se 1 (by rfl) ⟨3306716, by rfl⟩ : syracuseStep 4408955 = 6613433) B6613433
theorem B6973067 : Blo 1222929 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B4646585 : Blo 1222929 4646585 := bstep (se 2 (by rfl) ⟨1742469, by rfl⟩ : syracuseStep 4646585 = 3484939) B3484939
theorem B2754377 : Blo 1222929 2754377 := bstep (se 2 (by rfl) ⟨1032891, by rfl⟩ : syracuseStep 2754377 = 2065783) B2065783
theorem B3770219 : Blo 1222929 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B32237473 : Blo 1222929 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B9291833 : Blo 1222929 9291833 := bstep (se 2 (by rfl) ⟨3484437, by rfl⟩ : syracuseStep 9291833 = 6968875) B6968875
theorem B3918071 : Blo 1222929 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B1222951 : Blo 1222929 1222951 := bstep (se 1 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 1222951 = 1834427) B1834427
theorem B1222991 : Blo 1222929 1222991 := bstep (se 1 (by rfl) ⟨917243, by rfl⟩ : syracuseStep 1222991 = 1834487) B1834487
theorem B1223007 : Blo 1222929 1223007 := bstep (se 1 (by rfl) ⟨917255, by rfl⟩ : syracuseStep 1223007 = 1834511) B1834511
theorem B1223035 : Blo 1222929 1223035 := bstep (se 1 (by rfl) ⟨917276, by rfl⟩ : syracuseStep 1223035 = 1834553) B1834553
theorem B4131215 : Blo 1222929 4131215 := bstep (se 1 (by rfl) ⟨3098411, by rfl⟩ : syracuseStep 4131215 = 6196823) B6196823
theorem B1223087 : Blo 1222929 1223087 := bstep (se 1 (by rfl) ⟨917315, by rfl⟩ : syracuseStep 1223087 = 1834631) B1834631
theorem B1223111 : Blo 1222929 1223111 := bstep (se 1 (by rfl) ⟨917333, by rfl⟩ : syracuseStep 1223111 = 1834667) B1834667
theorem B1223131 : Blo 1222929 1223131 := bstep (se 1 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 1223131 = 1834697) B1834697
theorem B3099161 : Blo 1222929 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B1223207 : Blo 1222929 1223207 := bstep (se 1 (by rfl) ⟨917405, by rfl⟩ : syracuseStep 1223207 = 1834811) B1834811
theorem B1223247 : Blo 1222929 1223247 := bstep (se 1 (by rfl) ⟨917435, by rfl⟩ : syracuseStep 1223247 = 1834871) B1834871
theorem B1223263 : Blo 1222929 1223263 := bstep (se 1 (by rfl) ⟨917447, by rfl⟩ : syracuseStep 1223263 = 1834895) B1834895
theorem B1223291 : Blo 1222929 1223291 := bstep (se 1 (by rfl) ⟨917468, by rfl⟩ : syracuseStep 1223291 = 1834937) B1834937
theorem B1223343 : Blo 1222929 1223343 := bstep (se 1 (by rfl) ⟨917507, by rfl⟩ : syracuseStep 1223343 = 1835015) B1835015
theorem B1223367 : Blo 1222929 1223367 := bstep (se 1 (by rfl) ⟨917525, by rfl⟩ : syracuseStep 1223367 = 1835051) B1835051
theorem B7949009 : Blo 1222929 7949009 := bstep (se 2 (by rfl) ⟨2980878, by rfl⟩ : syracuseStep 7949009 = 5961757) B5961757
theorem B4131539 : Blo 1222929 4131539 := bstep (se 1 (by rfl) ⟨3098654, by rfl⟩ : syracuseStep 4131539 = 6197309) B6197309
theorem B1223387 : Blo 1222929 1223387 := bstep (se 1 (by rfl) ⟨917540, by rfl⟩ : syracuseStep 1223387 = 1835081) B1835081
theorem B1223463 : Blo 1222929 1223463 := bstep (se 1 (by rfl) ⟨917597, by rfl⟩ : syracuseStep 1223463 = 1835195) B1835195
theorem B1223503 : Blo 1222929 1223503 := bstep (se 1 (by rfl) ⟨917627, by rfl⟩ : syracuseStep 1223503 = 1835255) B1835255
theorem B1223519 : Blo 1222929 1223519 := bstep (se 1 (by rfl) ⟨917639, by rfl⟩ : syracuseStep 1223519 = 1835279) B1835279
theorem B1223547 : Blo 1222929 1223547 := bstep (se 1 (by rfl) ⟨917660, by rfl⟩ : syracuseStep 1223547 = 1835321) B1835321
theorem B1223599 : Blo 1222929 1223599 := bstep (se 1 (by rfl) ⟨917699, by rfl⟩ : syracuseStep 1223599 = 1835399) B1835399
theorem B1223623 : Blo 1222929 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B1223643 : Blo 1222929 1223643 := bstep (se 1 (by rfl) ⟨917732, by rfl⟩ : syracuseStep 1223643 = 1835465) B1835465
theorem B1223719 : Blo 1222929 1223719 := bstep (se 1 (by rfl) ⟨917789, by rfl⟩ : syracuseStep 1223719 = 1835579) B1835579
theorem B1223759 : Blo 1222929 1223759 := bstep (se 1 (by rfl) ⟨917819, by rfl⟩ : syracuseStep 1223759 = 1835639) B1835639
theorem B1223775 : Blo 1222929 1223775 := bstep (se 1 (by rfl) ⟨917831, by rfl⟩ : syracuseStep 1223775 = 1835663) B1835663
theorem B1223803 : Blo 1222929 1223803 := bstep (se 1 (by rfl) ⟨917852, by rfl⟩ : syracuseStep 1223803 = 1835705) B1835705
theorem B6040747 : Blo 1222929 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B1223855 : Blo 1222929 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B1223879 : Blo 1222929 1223879 := bstep (se 1 (by rfl) ⟨917909, by rfl⟩ : syracuseStep 1223879 = 1835819) B1835819
theorem B1223899 : Blo 1222929 1223899 := bstep (se 1 (by rfl) ⟨917924, by rfl⟩ : syracuseStep 1223899 = 1835849) B1835849
theorem B1223975 : Blo 1222929 1223975 := bstep (se 1 (by rfl) ⟨917981, by rfl⟩ : syracuseStep 1223975 = 1835963) B1835963
theorem B1224015 : Blo 1222929 1224015 := bstep (se 1 (by rfl) ⟨918011, by rfl⟩ : syracuseStep 1224015 = 1836023) B1836023
theorem B2321759 : Blo 1222929 2321759 := bstep (se 1 (by rfl) ⟨1741319, by rfl⟩ : syracuseStep 2321759 = 3482639) B3482639
theorem B1224031 : Blo 1222929 1224031 := bstep (se 1 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 1224031 = 1836047) B1836047
theorem B1224059 : Blo 1222929 1224059 := bstep (se 1 (by rfl) ⟨918044, by rfl⟩ : syracuseStep 1224059 = 1836089) B1836089
theorem B1224111 : Blo 1222929 1224111 := bstep (se 1 (by rfl) ⟨918083, by rfl⟩ : syracuseStep 1224111 = 1836167) B1836167
theorem B1224135 : Blo 1222929 1224135 := bstep (se 1 (by rfl) ⟨918101, by rfl⟩ : syracuseStep 1224135 = 1836203) B1836203
theorem B8818139 : Blo 1222929 8818139 := bstep (se 1 (by rfl) ⟨6613604, by rfl⟩ : syracuseStep 8818139 = 13227209) B13227209
theorem B1224155 : Blo 1222929 1224155 := bstep (se 1 (by rfl) ⟨918116, by rfl⟩ : syracuseStep 1224155 = 1836233) B1836233
theorem B1224231 : Blo 1222929 1224231 := bstep (se 1 (by rfl) ⟨918173, by rfl⟩ : syracuseStep 1224231 = 1836347) B1836347
theorem B1224271 : Blo 1222929 1224271 := bstep (se 1 (by rfl) ⟨918203, by rfl⟩ : syracuseStep 1224271 = 1836407) B1836407
theorem B1224287 : Blo 1222929 1224287 := bstep (se 1 (by rfl) ⟨918215, by rfl⟩ : syracuseStep 1224287 = 1836431) B1836431
theorem B2322017 : Blo 1222929 2322017 := bstep (se 2 (by rfl) ⟨870756, by rfl⟩ : syracuseStep 2322017 = 1741513) B1741513
theorem B3485281 : Blo 1222929 3485281 := bstep (se 2 (by rfl) ⟨1306980, by rfl⟩ : syracuseStep 3485281 = 2613961) B2613961
theorem B5582459 : Blo 1222929 5582459 := bstep (se 1 (by rfl) ⟨4186844, by rfl⟩ : syracuseStep 5582459 = 8373689) B8373689
theorem B1224315 : Blo 1222929 1224315 := bstep (se 1 (by rfl) ⟨918236, by rfl⟩ : syracuseStep 1224315 = 1836473) B1836473
theorem B1224367 : Blo 1222929 1224367 := bstep (se 1 (by rfl) ⟨918275, by rfl⟩ : syracuseStep 1224367 = 1836551) B1836551
theorem B1224391 : Blo 1222929 1224391 := bstep (se 1 (by rfl) ⟨918293, by rfl⟩ : syracuseStep 1224391 = 1836587) B1836587
theorem B1224411 : Blo 1222929 1224411 := bstep (se 1 (by rfl) ⟨918308, by rfl⟩ : syracuseStep 1224411 = 1836617) B1836617
theorem B11767517 : Blo 1222929 11767517 := bstep (se 3 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 11767517 = 4412819) B4412819
theorem B6196985 : Blo 1222929 6196985 := bstep (se 2 (by rfl) ⟨2323869, by rfl⟩ : syracuseStep 6196985 = 4647739) B4647739
theorem B4648697 : Blo 1222929 4648697 := bstep (se 2 (by rfl) ⟨1743261, by rfl⟩ : syracuseStep 4648697 = 3486523) B3486523
theorem B2322283 : Blo 1222929 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B4960109 : Blo 1222929 4960109 := bstep (se 3 (by rfl) ⟨930020, by rfl⟩ : syracuseStep 4960109 = 1860041) B1860041
theorem B27545507 : Blo 1222929 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B9293777 : Blo 1222929 9293777 := bstep (se 2 (by rfl) ⟨3485166, by rfl⟩ : syracuseStep 9293777 = 6970333) B6970333
theorem B47673305 : Blo 1222929 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B4960271 : Blo 1222929 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B2093407 : Blo 1222929 2093407 := bstep (se 1 (by rfl) ⟨1570055, by rfl⟩ : syracuseStep 2093407 = 3140111) B3140111
theorem B6197633 : Blo 1222929 6197633 := bstep (se 2 (by rfl) ⟨2324112, by rfl⟩ : syracuseStep 6197633 = 4648225) B4648225
theorem B2355731 : Blo 1222929 2355731 := bstep (se 1 (by rfl) ⟨1766798, by rfl⟩ : syracuseStep 2355731 = 3533597) B3533597
theorem B6967943 : Blo 1222929 6967943 := bstep (se 1 (by rfl) ⟨5225957, by rfl⟩ : syracuseStep 6967943 = 10451915) B10451915
theorem B3486397 : Blo 1222929 3486397 := bstep (se 3 (by rfl) ⟨653699, by rfl⟩ : syracuseStep 3486397 = 1307399) B1307399
theorem B17642393 : Blo 1222929 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B4707335 : Blo 1222929 4707335 := bstep (se 1 (by rfl) ⟨3530501, by rfl⟩ : syracuseStep 4707335 = 7061003) B7061003
theorem B2790407 : Blo 1222929 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B2323475 : Blo 1222929 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B3486739 : Blo 1222929 3486739 := bstep (se 1 (by rfl) ⟨2615054, by rfl⟩ : syracuseStep 3486739 = 5230109) B5230109
theorem B6198443 : Blo 1222929 6198443 := bstep (se 1 (by rfl) ⟨4648832, by rfl⟩ : syracuseStep 6198443 = 9297665) B9297665
theorem B2323703 : Blo 1222929 2323703 := bstep (se 1 (by rfl) ⟨1742777, by rfl⟩ : syracuseStep 2323703 = 3485555) B3485555
theorem B1742185 : Blo 1222929 1742185 := bstep (se 2 (by rfl) ⟨653319, by rfl⟩ : syracuseStep 1742185 = 1306639) B1306639
theorem B5223923 : Blo 1222929 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B10450579 : Blo 1222929 10450579 := bstep (se 1 (by rfl) ⟨7837934, by rfl⟩ : syracuseStep 10450579 = 15675869) B15675869
theorem B15898427 : Blo 1222929 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B12089249 : Blo 1222929 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B6969401 : Blo 1222929 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B2480225 : Blo 1222929 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B1742971 : Blo 1222929 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B4708505 : Blo 1222929 4708505 := bstep (se 2 (by rfl) ⟨1765689, by rfl⟩ : syracuseStep 4708505 = 3531379) B3531379
theorem B59513089 : Blo 1222929 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B18848051 : Blo 1222929 18848051 := bstep (se 1 (by rfl) ⟨14136038, by rfl⟩ : syracuseStep 18848051 = 28272077) B28272077
theorem B2480491 : Blo 1222929 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B2480719 : Blo 1222929 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B6191801 : Blo 1222929 6191801 := bstep (se 2 (by rfl) ⟨2321925, by rfl⟩ : syracuseStep 6191801 = 4643851) B4643851
theorem B35281777 : Blo 1222929 35281777 := bstep (se 2 (by rfl) ⟨13230666, by rfl⟩ : syracuseStep 35281777 = 26461333) B26461333
theorem B4127759 : Blo 1222929 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B2907215 : Blo 1222929 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B2751659 : Blo 1222929 2751659 := bstep (se 1 (by rfl) ⟨2063744, by rfl⟩ : syracuseStep 2751659 = 4127489) B4127489
theorem B1653959 : Blo 1222929 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B2063711 : Blo 1222929 2063711 := bstep (se 1 (by rfl) ⟨1547783, by rfl⟩ : syracuseStep 2063711 = 3095567) B3095567
theorem B15678845 : Blo 1222929 15678845 := bstep (se 3 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 15678845 = 5879567) B5879567
theorem B1834415 : Blo 1222929 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B1834505 : Blo 1222929 1834505 := bstep (se 2 (by rfl) ⟨687939, by rfl⟩ : syracuseStep 1834505 = 1375879) B1375879
theorem B1834535 : Blo 1222929 1834535 := bstep (se 1 (by rfl) ⟨1375901, by rfl⟩ : syracuseStep 1834535 = 2751803) B2751803
theorem B3096103 : Blo 1222929 3096103 := bstep (se 1 (by rfl) ⟨2322077, by rfl⟩ : syracuseStep 3096103 = 4644155) B4644155
theorem B4128353 : Blo 1222929 4128353 := bstep (se 2 (by rfl) ⟨1548132, by rfl⟩ : syracuseStep 4128353 = 3096265) B3096265
theorem B16113271 : Blo 1222929 16113271 := bstep (se 1 (by rfl) ⟨12084953, by rfl⟩ : syracuseStep 16113271 = 24169907) B24169907
theorem B1834619 : Blo 1222929 1834619 := bstep (se 1 (by rfl) ⟨1375964, by rfl⟩ : syracuseStep 1834619 = 2751929) B2751929
theorem B2752199 : Blo 1222929 2752199 := bstep (se 1 (by rfl) ⟨2064149, by rfl⟩ : syracuseStep 2752199 = 4128299) B4128299
theorem B1834745 : Blo 1222929 1834745 := bstep (se 2 (by rfl) ⟨688029, by rfl⟩ : syracuseStep 1834745 = 1376059) B1376059
theorem B1376095 : Blo 1222929 1376095 := bstep (se 1 (by rfl) ⟨1032071, by rfl⟩ : syracuseStep 1376095 = 2064143) B2064143
theorem B1834847 : Blo 1222929 1834847 := bstep (se 1 (by rfl) ⟨1376135, by rfl⟩ : syracuseStep 1834847 = 2752271) B2752271
theorem B1834859 : Blo 1222929 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B3096427 : Blo 1222929 3096427 := bstep (se 1 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 3096427 = 4644641) B4644641
theorem B2064271 : Blo 1222929 2064271 := bstep (se 1 (by rfl) ⟨1548203, by rfl⟩ : syracuseStep 2064271 = 3096407) B3096407
theorem B2064649 : Blo 1222929 2064649 := bstep (se 2 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 2064649 = 1548487) B1548487
theorem B1835273 : Blo 1222929 1835273 := bstep (se 2 (by rfl) ⟨688227, by rfl⟩ : syracuseStep 1835273 = 1376455) B1376455
theorem B11764055 : Blo 1222929 11764055 := bstep (se 1 (by rfl) ⟨8823041, by rfl⟩ : syracuseStep 11764055 = 17646083) B17646083
theorem B1835375 : Blo 1222929 1835375 := bstep (se 1 (by rfl) ⟨1376531, by rfl⟩ : syracuseStep 1835375 = 2753063) B2753063
theorem B1376635 : Blo 1222929 1376635 := bstep (se 1 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 1376635 = 2064953) B2064953
theorem B6193583 : Blo 1222929 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B4645295 : Blo 1222929 4645295 := bstep (se 1 (by rfl) ⟨3483971, by rfl⟩ : syracuseStep 4645295 = 6967943) B6967943
theorem B1835591 : Blo 1222929 1835591 := bstep (se 1 (by rfl) ⟨1376693, by rfl⟩ : syracuseStep 1835591 = 2753387) B2753387
theorem B1835627 : Blo 1222929 1835627 := bstep (se 1 (by rfl) ⟨1376720, by rfl⟩ : syracuseStep 1835627 = 2753441) B2753441
theorem B4129433 : Blo 1222929 4129433 := bstep (se 2 (by rfl) ⟨1548537, by rfl⟩ : syracuseStep 4129433 = 3097075) B3097075
theorem B2753207 : Blo 1222929 2753207 := bstep (se 1 (by rfl) ⟨2064905, by rfl⟩ : syracuseStep 2753207 = 4129811) B4129811
theorem B1548983 : Blo 1222929 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B1835855 : Blo 1222929 1835855 := bstep (se 1 (by rfl) ⟨1376891, by rfl⟩ : syracuseStep 1835855 = 2753783) B2753783
theorem B1549135 : Blo 1222929 1549135 := bstep (se 1 (by rfl) ⟨1161851, by rfl⟩ : syracuseStep 1549135 = 2323703) B2323703
theorem B1377103 : Blo 1222929 1377103 := bstep (se 1 (by rfl) ⟨1032827, by rfl⟩ : syracuseStep 1377103 = 2065655) B2065655
theorem B2753423 : Blo 1222929 2753423 := bstep (se 1 (by rfl) ⟨2065067, by rfl⟩ : syracuseStep 2753423 = 4130135) B4130135
theorem B3482615 : Blo 1222929 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B3097723 : Blo 1222929 3097723 := bstep (se 1 (by rfl) ⟨2323292, by rfl⟩ : syracuseStep 3097723 = 4646585) B4646585
theorem B1836251 : Blo 1222929 1836251 := bstep (se 1 (by rfl) ⟨1377188, by rfl⟩ : syracuseStep 1836251 = 2754377) B2754377
theorem B6194555 : Blo 1222929 6194555 := bstep (se 1 (by rfl) ⟨4645916, by rfl⟩ : syracuseStep 6194555 = 9291833) B9291833
theorem B4646267 : Blo 1222929 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B1836425 : Blo 1222929 1836425 := bstep (se 2 (by rfl) ⟨688659, by rfl⟩ : syracuseStep 1836425 = 1377319) B1377319
theorem B3139003 : Blo 1222929 3139003 := bstep (se 1 (by rfl) ⟨2354252, by rfl⟩ : syracuseStep 3139003 = 4708505) B4708505
theorem B8054329 : Blo 1222929 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B2754143 : Blo 1222929 2754143 := bstep (se 1 (by rfl) ⟨2065607, by rfl⟩ : syracuseStep 2754143 = 4131215) B4131215
theorem B2066107 : Blo 1222929 2066107 := bstep (se 1 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 2066107 = 3099161) B3099161
theorem B2754359 : Blo 1222929 2754359 := bstep (se 1 (by rfl) ⟨2065769, by rfl⟩ : syracuseStep 2754359 = 4131539) B4131539
theorem B2754665 : Blo 1222929 2754665 := bstep (se 2 (by rfl) ⟨1032999, by rfl⟩ : syracuseStep 2754665 = 2065999) B2065999
theorem B4647041 : Blo 1222929 4647041 := bstep (se 2 (by rfl) ⟨1742640, by rfl⟩ : syracuseStep 4647041 = 3485281) B3485281
theorem B4130945 : Blo 1222929 4130945 := bstep (se 2 (by rfl) ⟨1549104, by rfl⟩ : syracuseStep 4130945 = 3098209) B3098209
theorem B1222943 : Blo 1222929 1222943 := bstep (se 1 (by rfl) ⟨917207, by rfl⟩ : syracuseStep 1222943 = 1834415) B1834415
theorem B1223003 : Blo 1222929 1223003 := bstep (se 1 (by rfl) ⟨917252, by rfl⟩ : syracuseStep 1223003 = 1834505) B1834505
theorem B1223023 : Blo 1222929 1223023 := bstep (se 1 (by rfl) ⟨917267, by rfl⟩ : syracuseStep 1223023 = 1834535) B1834535
theorem B1223079 : Blo 1222929 1223079 := bstep (se 1 (by rfl) ⟨917309, by rfl⟩ : syracuseStep 1223079 = 1834619) B1834619
theorem B3721639 : Blo 1222929 3721639 := bstep (se 1 (by rfl) ⟨2791229, by rfl⟩ : syracuseStep 3721639 = 5582459) B5582459
theorem B1223163 : Blo 1222929 1223163 := bstep (se 1 (by rfl) ⟨917372, by rfl⟩ : syracuseStep 1223163 = 1834745) B1834745
theorem B4131323 : Blo 1222929 4131323 := bstep (se 1 (by rfl) ⟨3098492, by rfl⟩ : syracuseStep 4131323 = 6196985) B6196985
theorem B3099131 : Blo 1222929 3099131 := bstep (se 1 (by rfl) ⟨2324348, by rfl⟩ : syracuseStep 3099131 = 4648697) B4648697
theorem B1223231 : Blo 1222929 1223231 := bstep (se 1 (by rfl) ⟨917423, by rfl⟩ : syracuseStep 1223231 = 1834847) B1834847
theorem B1223239 : Blo 1222929 1223239 := bstep (se 1 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 1223239 = 1834859) B1834859
theorem B6195851 : Blo 1222929 6195851 := bstep (se 1 (by rfl) ⟨4646888, by rfl⟩ : syracuseStep 6195851 = 9293777) B9293777
theorem B12552893 : Blo 1222929 12552893 := bstep (se 3 (by rfl) ⟨2353667, by rfl⟩ : syracuseStep 12552893 = 4707335) B4707335
theorem B7441085 : Blo 1222929 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B1223391 : Blo 1222929 1223391 := bstep (se 1 (by rfl) ⟨917543, by rfl⟩ : syracuseStep 1223391 = 1835087) B1835087
theorem B1223471 : Blo 1222929 1223471 := bstep (se 1 (by rfl) ⟨917603, by rfl⟩ : syracuseStep 1223471 = 1835207) B1835207
theorem B1223579 : Blo 1222929 1223579 := bstep (se 1 (by rfl) ⟨917684, by rfl⟩ : syracuseStep 1223579 = 1835369) B1835369
theorem B4131755 : Blo 1222929 4131755 := bstep (se 1 (by rfl) ⟨3098816, by rfl⟩ : syracuseStep 4131755 = 6197633) B6197633
theorem B6613933 : Blo 1222929 6613933 := bstep (se 3 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 6613933 = 2480225) B2480225
theorem B1223631 : Blo 1222929 1223631 := bstep (se 1 (by rfl) ⟨917723, by rfl⟩ : syracuseStep 1223631 = 1835447) B1835447
theorem B1223655 : Blo 1222929 1223655 := bstep (se 1 (by rfl) ⟨917741, by rfl⟩ : syracuseStep 1223655 = 1835483) B1835483
theorem B79350785 : Blo 1222929 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B3484711 : Blo 1222929 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B25128107 : Blo 1222929 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B4410557 : Blo 1222929 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B3140851 : Blo 1222929 3140851 := bstep (se 1 (by rfl) ⟨2355638, by rfl⟩ : syracuseStep 3140851 = 4711277) B4711277
theorem B1223967 : Blo 1222929 1223967 := bstep (se 1 (by rfl) ⟨917975, by rfl⟩ : syracuseStep 1223967 = 1835951) B1835951
theorem B10448189 : Blo 1222929 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B1224027 : Blo 1222929 1224027 := bstep (se 1 (by rfl) ⟨918020, by rfl⟩ : syracuseStep 1224027 = 1836041) B1836041
theorem B1224047 : Blo 1222929 1224047 := bstep (se 1 (by rfl) ⟨918035, by rfl⟩ : syracuseStep 1224047 = 1836071) B1836071
theorem B3485065 : Blo 1222929 3485065 := bstep (se 2 (by rfl) ⟨1306899, by rfl⟩ : syracuseStep 3485065 = 2613799) B2613799
theorem B1224103 : Blo 1222929 1224103 := bstep (se 1 (by rfl) ⟨918077, by rfl⟩ : syracuseStep 1224103 = 1836155) B1836155
theorem B4132295 : Blo 1222929 4132295 := bstep (se 1 (by rfl) ⟨3099221, by rfl⟩ : syracuseStep 4132295 = 6198443) B6198443
theorem B1224187 : Blo 1222929 1224187 := bstep (se 1 (by rfl) ⟨918140, by rfl⟩ : syracuseStep 1224187 = 1836281) B1836281
theorem B1224255 : Blo 1222929 1224255 := bstep (se 1 (by rfl) ⟨918191, by rfl⟩ : syracuseStep 1224255 = 1836383) B1836383
theorem B1224263 : Blo 1222929 1224263 := bstep (se 1 (by rfl) ⟨918197, by rfl⟩ : syracuseStep 1224263 = 1836395) B1836395
theorem B4648529 : Blo 1222929 4648529 := bstep (se 2 (by rfl) ⟨1743198, by rfl⟩ : syracuseStep 4648529 = 3486397) B3486397
theorem B1224415 : Blo 1222929 1224415 := bstep (se 1 (by rfl) ⟨918311, by rfl⟩ : syracuseStep 1224415 = 1836623) B1836623
theorem B4648711 : Blo 1222929 4648711 := bstep (se 1 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 4648711 = 6973067) B6973067
theorem B4960061 : Blo 1222929 4960061 := bstep (se 3 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 4960061 = 1860023) B1860023
theorem B47042369 : Blo 1222929 47042369 := bstep (se 2 (by rfl) ⟨17640888, by rfl⟩ : syracuseStep 47042369 = 35281777) B35281777
theorem B5582857 : Blo 1222929 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B4648985 : Blo 1222929 4648985 := bstep (se 2 (by rfl) ⟨1743369, by rfl⟩ : syracuseStep 4648985 = 3486739) B3486739
theorem B2322913 : Blo 1222929 2322913 := bstep (se 2 (by rfl) ⟨871092, by rfl⟩ : syracuseStep 2322913 = 1742185) B1742185
theorem B1938143 : Blo 1222929 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B21484361 : Blo 1222929 21484361 := bstep (se 2 (by rfl) ⟨8056635, by rfl⟩ : syracuseStep 21484361 = 16113271) B16113271
theorem B5878759 : Blo 1222929 5878759 := bstep (se 1 (by rfl) ⟨4409069, by rfl⟩ : syracuseStep 5878759 = 8818139) B8818139
theorem B7845011 : Blo 1222929 7845011 := bstep (se 1 (by rfl) ⟨5883758, by rfl⟩ : syracuseStep 7845011 = 11767517) B11767517
theorem B3306739 : Blo 1222929 3306739 := bstep (se 1 (by rfl) ⟨2480054, by rfl⟩ : syracuseStep 3306739 = 4960109) B4960109
theorem B18363671 : Blo 1222929 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B31782203 : Blo 1222929 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B3306847 : Blo 1222929 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B2323961 : Blo 1222929 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B1414831 : Blo 1222929 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1570487 : Blo 1222929 1570487 := bstep (se 1 (by rfl) ⟨1177865, by rfl⟩ : syracuseStep 1570487 = 2355731) B2355731
theorem B3307321 : Blo 1222929 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B11761595 : Blo 1222929 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B3307625 : Blo 1222929 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B2939303 : Blo 1222929 2939303 := bstep (se 1 (by rfl) ⟨2204477, by rfl⟩ : syracuseStep 2939303 = 4408955) B4408955
theorem B10598951 : Blo 1222929 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B2513479 : Blo 1222929 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B8059499 : Blo 1222929 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B12565367 : Blo 1222929 12565367 := bstep (se 1 (by rfl) ⟨9424025, by rfl⟩ : syracuseStep 12565367 = 18848051) B18848051
theorem B2612321 : Blo 1222929 2612321 := bstep (se 2 (by rfl) ⟨979620, by rfl⟩ : syracuseStep 2612321 = 1959241) B1959241
theorem B4127867 : Blo 1222929 4127867 := bstep (se 1 (by rfl) ⟨3095900, by rfl⟩ : syracuseStep 4127867 = 6191801) B6191801
theorem B5299339 : Blo 1222929 5299339 := bstep (se 1 (by rfl) ⟨3974504, by rfl⟩ : syracuseStep 5299339 = 7949009) B7949009
theorem B11164837 : Blo 1222929 11164837 := bstep (se 4 (by rfl) ⟨1046703, by rfl⟩ : syracuseStep 11164837 = 2093407) B2093407
theorem B2751839 : Blo 1222929 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B4128137 : Blo 1222929 4128137 := bstep (se 2 (by rfl) ⟨1548051, by rfl⟩ : syracuseStep 4128137 = 3096103) B3096103
theorem B1834439 : Blo 1222929 1834439 := bstep (se 1 (by rfl) ⟨1375829, by rfl⟩ : syracuseStep 1834439 = 2751659) B2751659
theorem B13934105 : Blo 1222929 13934105 := bstep (se 2 (by rfl) ⟨5225289, by rfl⟩ : syracuseStep 13934105 = 10450579) B10450579
theorem B1375807 : Blo 1222929 1375807 := bstep (se 1 (by rfl) ⟨1031855, by rfl⟩ : syracuseStep 1375807 = 2063711) B2063711
theorem B1547839 : Blo 1222929 1547839 := bstep (se 1 (by rfl) ⟨1160879, by rfl⟩ : syracuseStep 1547839 = 2321759) B2321759
theorem B10452563 : Blo 1222929 10452563 := bstep (se 1 (by rfl) ⟨7839422, by rfl⟩ : syracuseStep 10452563 = 15678845) B15678845
theorem B1548011 : Blo 1222929 1548011 := bstep (se 1 (by rfl) ⟨1161008, by rfl⟩ : syracuseStep 1548011 = 2322017) B2322017
theorem B2752235 : Blo 1222929 2752235 := bstep (se 1 (by rfl) ⟨2064176, by rfl⟩ : syracuseStep 2752235 = 4128353) B4128353
theorem B1834793 : Blo 1222929 1834793 := bstep (se 2 (by rfl) ⟨688047, by rfl⟩ : syracuseStep 1834793 = 1376095) B1376095
theorem B1834799 : Blo 1222929 1834799 := bstep (se 1 (by rfl) ⟨1376099, by rfl⟩ : syracuseStep 1834799 = 2752199) B2752199
theorem B3096377 : Blo 1222929 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B4128569 : Blo 1222929 4128569 := bstep (se 2 (by rfl) ⟨1548213, by rfl⟩ : syracuseStep 4128569 = 3096427) B3096427
theorem B2752361 : Blo 1222929 2752361 := bstep (se 2 (by rfl) ⟨1032135, by rfl⟩ : syracuseStep 2752361 = 2064271) B2064271
theorem B42983297 : Blo 1222929 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B4129055 : Blo 1222929 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B3096863 : Blo 1222929 3096863 := bstep (se 1 (by rfl) ⟨2322647, by rfl⟩ : syracuseStep 3096863 = 4645295) B4645295
theorem B2752865 : Blo 1222929 2752865 := bstep (se 2 (by rfl) ⟨1032324, by rfl⟩ : syracuseStep 2752865 = 2064649) B2064649
theorem B2752955 : Blo 1222929 2752955 := bstep (se 1 (by rfl) ⟨2064716, by rfl⟩ : syracuseStep 2752955 = 4129433) B4129433
theorem B1835471 : Blo 1222929 1835471 := bstep (se 1 (by rfl) ⟨1376603, by rfl⟩ : syracuseStep 1835471 = 2753207) B2753207
theorem B1835513 : Blo 1222929 1835513 := bstep (se 2 (by rfl) ⟨688317, by rfl⟩ : syracuseStep 1835513 = 1376635) B1376635
theorem B1835615 : Blo 1222929 1835615 := bstep (se 1 (by rfl) ⟨1376711, by rfl⟩ : syracuseStep 1835615 = 2753423) B2753423
theorem B3097217 : Blo 1222929 3097217 := bstep (se 2 (by rfl) ⟨1161456, by rfl⟩ : syracuseStep 3097217 = 2322913) B2322913
theorem B3351305 : Blo 1222929 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B4129703 : Blo 1222929 4129703 := bstep (se 1 (by rfl) ⟨3097277, by rfl⟩ : syracuseStep 4129703 = 6194555) B6194555
theorem B3097511 : Blo 1222929 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B1549307 : Blo 1222929 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B1836095 : Blo 1222929 1836095 := bstep (se 1 (by rfl) ⟨1377071, by rfl⟩ : syracuseStep 1836095 = 2754143) B2754143
theorem B2065513 : Blo 1222929 2065513 := bstep (se 2 (by rfl) ⟨774567, by rfl⟩ : syracuseStep 2065513 = 1549135) B1549135
theorem B1836137 : Blo 1222929 1836137 := bstep (se 2 (by rfl) ⟨688551, by rfl⟩ : syracuseStep 1836137 = 1377103) B1377103
theorem B1836239 : Blo 1222929 1836239 := bstep (se 1 (by rfl) ⟨1377179, by rfl⟩ : syracuseStep 1836239 = 2754359) B2754359
theorem B7841063 : Blo 1222929 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B4646281 : Blo 1222929 4646281 := bstep (se 2 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 4646281 = 3484711) B3484711
theorem B2205083 : Blo 1222929 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B1836443 : Blo 1222929 1836443 := bstep (se 1 (by rfl) ⟨1377332, by rfl⟩ : syracuseStep 1836443 = 2754665) B2754665
theorem B3098027 : Blo 1222929 3098027 := bstep (se 1 (by rfl) ⟨2323520, by rfl⟩ : syracuseStep 3098027 = 4647041) B4647041
theorem B2753963 : Blo 1222929 2753963 := bstep (se 1 (by rfl) ⟨2065472, by rfl⟩ : syracuseStep 2753963 = 4130945) B4130945
theorem B4130297 : Blo 1222929 4130297 := bstep (se 2 (by rfl) ⟨1548861, by rfl⟩ : syracuseStep 4130297 = 3097723) B3097723
theorem B14886449 : Blo 1222929 14886449 := bstep (se 2 (by rfl) ⟨5582418, by rfl⟩ : syracuseStep 14886449 = 11164837) B11164837
theorem B1959535 : Blo 1222929 1959535 := bstep (se 1 (by rfl) ⟨1469651, by rfl⟩ : syracuseStep 1959535 = 2939303) B2939303
theorem B17639045 : Blo 1222929 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B4408985 : Blo 1222929 4408985 := bstep (se 2 (by rfl) ⟨1653369, by rfl⟩ : syracuseStep 4408985 = 3306739) B3306739
theorem B4187801 : Blo 1222929 4187801 := bstep (se 2 (by rfl) ⟨1570425, by rfl⟩ : syracuseStep 4187801 = 3140851) B3140851
theorem B2754215 : Blo 1222929 2754215 := bstep (se 1 (by rfl) ⟨2065661, by rfl⟩ : syracuseStep 2754215 = 4131323) B4131323
theorem B2066087 : Blo 1222929 2066087 := bstep (se 1 (by rfl) ⟨1549565, by rfl⟩ : syracuseStep 2066087 = 3099131) B3099131
theorem B4130567 : Blo 1222929 4130567 := bstep (se 1 (by rfl) ⟨3097925, by rfl⟩ : syracuseStep 4130567 = 6195851) B6195851
theorem B4409129 : Blo 1222929 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B4130621 : Blo 1222929 4130621 := bstep (se 3 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 4130621 = 1548983) B1548983
theorem B4187965 : Blo 1222929 4187965 := bstep (se 3 (by rfl) ⟨785243, by rfl⟩ : syracuseStep 4187965 = 1570487) B1570487
theorem B19842893 : Blo 1222929 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B4646753 : Blo 1222929 4646753 := bstep (se 2 (by rfl) ⟨1742532, by rfl⟩ : syracuseStep 4646753 = 3485065) B3485065
theorem B2754503 : Blo 1222929 2754503 := bstep (se 1 (by rfl) ⟨2065877, by rfl⟩ : syracuseStep 2754503 = 4131755) B4131755
theorem B6965459 : Blo 1222929 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B1886441 : Blo 1222929 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B2754809 : Blo 1222929 2754809 := bstep (se 2 (by rfl) ⟨1033053, by rfl⟩ : syracuseStep 2754809 = 2066107) B2066107
theorem B1222959 : Blo 1222929 1222959 := bstep (se 1 (by rfl) ⟨917219, by rfl⟩ : syracuseStep 1222959 = 1834439) B1834439
theorem B2754863 : Blo 1222929 2754863 := bstep (se 1 (by rfl) ⟨2066147, by rfl⟩ : syracuseStep 2754863 = 4132295) B4132295
theorem B3099019 : Blo 1222929 3099019 := bstep (se 1 (by rfl) ⟨2324264, by rfl⟩ : syracuseStep 3099019 = 4648529) B4648529
theorem B1223195 : Blo 1222929 1223195 := bstep (se 1 (by rfl) ⟨917396, by rfl⟩ : syracuseStep 1223195 = 1834793) B1834793
theorem B1223199 : Blo 1222929 1223199 := bstep (se 1 (by rfl) ⟨917399, by rfl⟩ : syracuseStep 1223199 = 1834799) B1834799
theorem B31361579 : Blo 1222929 31361579 := bstep (se 1 (by rfl) ⟨23521184, by rfl⟩ : syracuseStep 31361579 = 47042369) B47042369
theorem B3099323 : Blo 1222929 3099323 := bstep (se 1 (by rfl) ⟨2324492, by rfl⟩ : syracuseStep 3099323 = 4648985) B4648985
theorem B1223515 : Blo 1222929 1223515 := bstep (se 1 (by rfl) ⟨917636, by rfl⟩ : syracuseStep 1223515 = 1835273) B1835273
theorem B7842703 : Blo 1222929 7842703 := bstep (se 1 (by rfl) ⟨5882027, by rfl⟩ : syracuseStep 7842703 = 11764055) B11764055
theorem B1223583 : Blo 1222929 1223583 := bstep (se 1 (by rfl) ⟨917687, by rfl⟩ : syracuseStep 1223583 = 1835375) B1835375
theorem B1223727 : Blo 1222929 1223727 := bstep (se 1 (by rfl) ⟨917795, by rfl⟩ : syracuseStep 1223727 = 1835591) B1835591
theorem B1223751 : Blo 1222929 1223751 := bstep (se 1 (by rfl) ⟨917813, by rfl⟩ : syracuseStep 1223751 = 1835627) B1835627
theorem B1223903 : Blo 1222929 1223903 := bstep (se 1 (by rfl) ⟨917927, by rfl⟩ : syracuseStep 1223903 = 1835855) B1835855
theorem B5230007 : Blo 1222929 5230007 := bstep (se 1 (by rfl) ⟨3922505, by rfl⟩ : syracuseStep 5230007 = 7845011) B7845011
theorem B1224167 : Blo 1222929 1224167 := bstep (se 1 (by rfl) ⟨918125, by rfl⟩ : syracuseStep 1224167 = 1836251) B1836251
theorem B12242447 : Blo 1222929 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B21188135 : Blo 1222929 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B1224283 : Blo 1222929 1224283 := bstep (se 1 (by rfl) ⟨918212, by rfl⟩ : syracuseStep 1224283 = 1836425) B1836425
theorem B8818577 : Blo 1222929 8818577 := bstep (se 2 (by rfl) ⟨3306966, by rfl⟩ : syracuseStep 8818577 = 6613933) B6613933
theorem B7065785 : Blo 1222929 7065785 := bstep (se 2 (by rfl) ⟨2649669, by rfl⟩ : syracuseStep 7065785 = 5299339) B5299339
theorem B7065967 : Blo 1222929 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B8368595 : Blo 1222929 8368595 := bstep (se 1 (by rfl) ⟨6276446, by rfl⟩ : syracuseStep 8368595 = 12552893) B12552893
theorem B8376911 : Blo 1222929 8376911 := bstep (se 1 (by rfl) ⟨6282683, by rfl⟩ : syracuseStep 8376911 = 12565367) B12565367
theorem B52900523 : Blo 1222929 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B1741547 : Blo 1222929 1741547 := bstep (se 1 (by rfl) ⟨1306160, by rfl⟩ : syracuseStep 1741547 = 2612321) B2612321
theorem B57291629 : Blo 1222929 57291629 := bstep (se 3 (by rfl) ⟨10742180, by rfl⟩ : syracuseStep 57291629 = 21484361) B21484361
theorem B16741349 : Blo 1222929 16741349 := bstep (se 4 (by rfl) ⟨1569501, by rfl⟩ : syracuseStep 16741349 = 3139003) B3139003
theorem B6198281 : Blo 1222929 6198281 := bstep (se 2 (by rfl) ⟨2324355, by rfl⟩ : syracuseStep 6198281 = 4648711) B4648711
theorem B6968375 : Blo 1222929 6968375 := bstep (se 1 (by rfl) ⟨5226281, by rfl⟩ : syracuseStep 6968375 = 10452563) B10452563
theorem B3306707 : Blo 1222929 3306707 := bstep (se 1 (by rfl) ⟨2480030, by rfl⟩ : syracuseStep 3306707 = 4960061) B4960061
theorem B9286973 : Blo 1222929 9286973 := bstep (se 3 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 9286973 = 3482615) B3482615
theorem B7443809 : Blo 1222929 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B4962185 : Blo 1222929 4962185 := bstep (se 2 (by rfl) ⟨1860819, by rfl⟩ : syracuseStep 4962185 = 3721639) B3721639
theorem B7838345 : Blo 1222929 7838345 := bstep (se 2 (by rfl) ⟨2939379, by rfl⟩ : syracuseStep 7838345 = 5878759) B5878759
theorem B5372999 : Blo 1222929 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B5168381 : Blo 1222929 5168381 := bstep (se 3 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 5168381 = 1938143) B1938143
theorem B4128029 : Blo 1222929 4128029 := bstep (se 3 (by rfl) ⟨774005, by rfl⟩ : syracuseStep 4128029 = 1548011) B1548011
theorem B10739105 : Blo 1222929 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B2751911 : Blo 1222929 2751911 := bstep (se 1 (by rfl) ⟨2063933, by rfl⟩ : syracuseStep 2751911 = 4127867) B4127867
theorem B1834409 : Blo 1222929 1834409 := bstep (se 2 (by rfl) ⟨687903, by rfl⟩ : syracuseStep 1834409 = 1375807) B1375807
theorem B2063785 : Blo 1222929 2063785 := bstep (se 2 (by rfl) ⟨773919, by rfl⟩ : syracuseStep 2063785 = 1547839) B1547839
theorem B16752071 : Blo 1222929 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B2940371 : Blo 1222929 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B1834559 : Blo 1222929 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B2752091 : Blo 1222929 2752091 := bstep (se 1 (by rfl) ⟨2064068, by rfl⟩ : syracuseStep 2752091 = 4128137) B4128137
theorem B9289403 : Blo 1222929 9289403 := bstep (se 1 (by rfl) ⟨6967052, by rfl⟩ : syracuseStep 9289403 = 13934105) B13934105
theorem B1834823 : Blo 1222929 1834823 := bstep (se 1 (by rfl) ⟨1376117, by rfl⟩ : syracuseStep 1834823 = 2752235) B2752235
theorem B2064251 : Blo 1222929 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B2752379 : Blo 1222929 2752379 := bstep (se 1 (by rfl) ⟨2064284, by rfl⟩ : syracuseStep 2752379 = 4128569) B4128569
theorem B1834907 : Blo 1222929 1834907 := bstep (se 1 (by rfl) ⟨1376180, by rfl⟩ : syracuseStep 1834907 = 2752361) B2752361
theorem B28655531 : Blo 1222929 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B4710523 : Blo 1222929 4710523 := bstep (se 1 (by rfl) ⟨3532892, by rfl⟩ : syracuseStep 4710523 = 7065785) B7065785
theorem B2752703 : Blo 1222929 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B2064575 : Blo 1222929 2064575 := bstep (se 1 (by rfl) ⟨1548431, by rfl⟩ : syracuseStep 2064575 = 3096863) B3096863
theorem B1835243 : Blo 1222929 1835243 := bstep (se 1 (by rfl) ⟨1376432, by rfl⟩ : syracuseStep 1835243 = 2752865) B2752865
theorem B1835303 : Blo 1222929 1835303 := bstep (se 1 (by rfl) ⟨1376477, by rfl⟩ : syracuseStep 1835303 = 2752955) B2752955
theorem B5579063 : Blo 1222929 5579063 := bstep (se 1 (by rfl) ⟨4184297, by rfl⟩ : syracuseStep 5579063 = 8368595) B8368595
theorem B2064811 : Blo 1222929 2064811 := bstep (se 1 (by rfl) ⟨1548608, by rfl⟩ : syracuseStep 2064811 = 3097217) B3097217
theorem B35267015 : Blo 1222929 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B9421289 : Blo 1222929 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B2753135 : Blo 1222929 2753135 := bstep (se 1 (by rfl) ⟨2064851, by rfl⟩ : syracuseStep 2753135 = 4129703) B4129703
theorem B2065007 : Blo 1222929 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B4645583 : Blo 1222929 4645583 := bstep (se 1 (by rfl) ⟨3484187, by rfl⟩ : syracuseStep 4645583 = 6968375) B6968375
theorem B2204471 : Blo 1222929 2204471 := bstep (se 1 (by rfl) ⟨1653353, by rfl⟩ : syracuseStep 2204471 = 3306707) B3306707
theorem B5227375 : Blo 1222929 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B2065351 : Blo 1222929 2065351 := bstep (se 1 (by rfl) ⟨1549013, by rfl⟩ : syracuseStep 2065351 = 3098027) B3098027
theorem B1835975 : Blo 1222929 1835975 := bstep (se 1 (by rfl) ⟨1376981, by rfl⟩ : syracuseStep 1835975 = 2753963) B2753963
theorem B2753531 : Blo 1222929 2753531 := bstep (se 1 (by rfl) ⟨2065148, by rfl⟩ : syracuseStep 2753531 = 4130297) B4130297
theorem B1836143 : Blo 1222929 1836143 := bstep (se 1 (by rfl) ⟨1377107, by rfl⟩ : syracuseStep 1836143 = 2754215) B2754215
theorem B1377391 : Blo 1222929 1377391 := bstep (se 1 (by rfl) ⟨1033043, by rfl⟩ : syracuseStep 1377391 = 2066087) B2066087
theorem B2753711 : Blo 1222929 2753711 := bstep (se 1 (by rfl) ⟨2065283, by rfl⟩ : syracuseStep 2753711 = 4130567) B4130567
theorem B2753747 : Blo 1222929 2753747 := bstep (se 1 (by rfl) ⟨2065310, by rfl⟩ : syracuseStep 2753747 = 4130621) B4130621
theorem B3097835 : Blo 1222929 3097835 := bstep (se 1 (by rfl) ⟨2323376, by rfl⟩ : syracuseStep 3097835 = 4646753) B4646753
theorem B1836335 : Blo 1222929 1836335 := bstep (se 1 (by rfl) ⟨1377251, by rfl⟩ : syracuseStep 1836335 = 2754503) B2754503
theorem B2754017 : Blo 1222929 2754017 := bstep (se 2 (by rfl) ⟨1032756, by rfl⟩ : syracuseStep 2754017 = 2065513) B2065513
theorem B1836539 : Blo 1222929 1836539 := bstep (se 1 (by rfl) ⟨1377404, by rfl⟩ : syracuseStep 1836539 = 2754809) B2754809
theorem B1836575 : Blo 1222929 1836575 := bstep (se 1 (by rfl) ⟨1377431, by rfl⟩ : syracuseStep 1836575 = 2754863) B2754863
theorem B20907719 : Blo 1222929 20907719 := bstep (se 1 (by rfl) ⟨15680789, by rfl⟩ : syracuseStep 20907719 = 31361579) B31361579
theorem B2066215 : Blo 1222929 2066215 := bstep (se 1 (by rfl) ⟨1549661, by rfl⟩ : syracuseStep 2066215 = 3099323) B3099323
theorem B6195041 : Blo 1222929 6195041 := bstep (se 2 (by rfl) ⟨2323140, by rfl⟩ : syracuseStep 6195041 = 4646281) B4646281
theorem B3581999 : Blo 1222929 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B1222939 : Blo 1222929 1222939 := bstep (se 1 (by rfl) ⟨917204, by rfl⟩ : syracuseStep 1222939 = 1834409) B1834409
theorem B11168047 : Blo 1222929 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B1960247 : Blo 1222929 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B8161631 : Blo 1222929 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B14125423 : Blo 1222929 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B1223039 : Blo 1222929 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B20122037 : Blo 1222929 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B1223215 : Blo 1222929 1223215 := bstep (se 1 (by rfl) ⟨917411, by rfl⟩ : syracuseStep 1223215 = 1834823) B1834823
theorem B1223271 : Blo 1222929 1223271 := bstep (se 1 (by rfl) ⟨917453, by rfl⟩ : syracuseStep 1223271 = 1834907) B1834907
theorem B4131485 : Blo 1222929 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B1223647 : Blo 1222929 1223647 := bstep (se 1 (by rfl) ⟨917735, by rfl⟩ : syracuseStep 1223647 = 1835471) B1835471
theorem B1223675 : Blo 1222929 1223675 := bstep (se 1 (by rfl) ⟨917756, by rfl⟩ : syracuseStep 1223675 = 1835513) B1835513
theorem B1223743 : Blo 1222929 1223743 := bstep (se 1 (by rfl) ⟨917807, by rfl⟩ : syracuseStep 1223743 = 1835615) B1835615
theorem B4132025 : Blo 1222929 4132025 := bstep (se 2 (by rfl) ⟨1549509, by rfl⟩ : syracuseStep 4132025 = 3099019) B3099019
theorem B11160899 : Blo 1222929 11160899 := bstep (se 1 (by rfl) ⟨8370674, by rfl⟩ : syracuseStep 11160899 = 16741349) B16741349
theorem B13782349 : Blo 1222929 13782349 := bstep (se 3 (by rfl) ⟨2584190, by rfl⟩ : syracuseStep 13782349 = 5168381) B5168381
theorem B4132187 : Blo 1222929 4132187 := bstep (se 1 (by rfl) ⟨3099140, by rfl⟩ : syracuseStep 4132187 = 6198281) B6198281
theorem B1224063 : Blo 1222929 1224063 := bstep (se 1 (by rfl) ⟨918047, by rfl⟩ : syracuseStep 1224063 = 1836095) B1836095
theorem B1224091 : Blo 1222929 1224091 := bstep (se 1 (by rfl) ⟨918068, by rfl⟩ : syracuseStep 1224091 = 1836137) B1836137
theorem B1224159 : Blo 1222929 1224159 := bstep (se 1 (by rfl) ⟨918119, by rfl⟩ : syracuseStep 1224159 = 1836239) B1836239
theorem B1224295 : Blo 1222929 1224295 := bstep (se 1 (by rfl) ⟨918221, by rfl⟩ : syracuseStep 1224295 = 1836443) B1836443
theorem B9924299 : Blo 1222929 9924299 := bstep (se 1 (by rfl) ⟨7443224, by rfl⟩ : syracuseStep 9924299 = 14886449) B14886449
theorem B11759363 : Blo 1222929 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B10456937 : Blo 1222929 10456937 := bstep (se 2 (by rfl) ⟨3921351, by rfl⟩ : syracuseStep 10456937 = 7842703) B7842703
theorem B152777677 : Blo 1222929 152777677 := bstep (se 3 (by rfl) ⟨28645814, by rfl⟩ : syracuseStep 152777677 = 57291629) B57291629
theorem B3486671 : Blo 1222929 3486671 := bstep (se 1 (by rfl) ⟨2615003, by rfl⟩ : syracuseStep 3486671 = 5230007) B5230007
theorem B5583953 : Blo 1222929 5583953 := bstep (se 2 (by rfl) ⟨2093982, by rfl⟩ : syracuseStep 5583953 = 4187965) B4187965
theorem B5879051 : Blo 1222929 5879051 := bstep (se 1 (by rfl) ⟨4409288, by rfl⟩ : syracuseStep 5879051 = 8818577) B8818577
theorem B5584607 : Blo 1222929 5584607 := bstep (se 1 (by rfl) ⟨4188455, by rfl⟩ : syracuseStep 5584607 = 8376911) B8376911
theorem B10450853 : Blo 1222929 10450853 := bstep (se 4 (by rfl) ⟨979767, by rfl⟩ : syracuseStep 10450853 = 1959535) B1959535
theorem B6191315 : Blo 1222929 6191315 := bstep (se 1 (by rfl) ⟨4643486, by rfl⟩ : syracuseStep 6191315 = 9286973) B9286973
theorem B4962539 : Blo 1222929 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B5880221 : Blo 1222929 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B2939323 : Blo 1222929 2939323 := bstep (se 1 (by rfl) ⟨2204492, by rfl⟩ : syracuseStep 2939323 = 4408985) B4408985
theorem B2791867 : Blo 1222929 2791867 := bstep (se 1 (by rfl) ⟨2093900, by rfl⟩ : syracuseStep 2791867 = 4187801) B4187801
theorem B2939419 : Blo 1222929 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B13228595 : Blo 1222929 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B3308123 : Blo 1222929 3308123 := bstep (se 1 (by rfl) ⟨2481092, by rfl⟩ : syracuseStep 3308123 = 4962185) B4962185
theorem B4643639 : Blo 1222929 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B5225563 : Blo 1222929 5225563 := bstep (se 1 (by rfl) ⟨3919172, by rfl⟩ : syracuseStep 5225563 = 7838345) B7838345
theorem B2751713 : Blo 1222929 2751713 := bstep (se 2 (by rfl) ⟨1031892, by rfl⟩ : syracuseStep 2751713 = 2063785) B2063785
theorem B4644125 : Blo 1222929 4644125 := bstep (se 3 (by rfl) ⟨870773, by rfl⟩ : syracuseStep 4644125 = 1741547) B1741547
theorem B8936813 : Blo 1222929 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B2752019 : Blo 1222929 2752019 := bstep (se 1 (by rfl) ⟨2064014, by rfl⟩ : syracuseStep 2752019 = 4128029) B4128029
theorem B7159403 : Blo 1222929 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B1834607 : Blo 1222929 1834607 := bstep (se 1 (by rfl) ⟨1375955, by rfl⟩ : syracuseStep 1834607 = 2751911) B2751911
theorem B1834727 : Blo 1222929 1834727 := bstep (se 1 (by rfl) ⟨1376045, by rfl⟩ : syracuseStep 1834727 = 2752091) B2752091
theorem B6192935 : Blo 1222929 6192935 := bstep (se 1 (by rfl) ⟨4644701, by rfl⟩ : syracuseStep 6192935 = 9289403) B9289403
theorem B1376167 : Blo 1222929 1376167 := bstep (se 1 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 1376167 = 2064251) B2064251
theorem B1834919 : Blo 1222929 1834919 := bstep (se 1 (by rfl) ⟨1376189, by rfl⟩ : syracuseStep 1834919 = 2752379) B2752379
theorem B19103687 : Blo 1222929 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B1835135 : Blo 1222929 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B1376383 : Blo 1222929 1376383 := bstep (se 1 (by rfl) ⟨1032287, by rfl⟩ : syracuseStep 1376383 = 2064575) B2064575
theorem B3719375 : Blo 1222929 3719375 := bstep (se 1 (by rfl) ⟨2789531, by rfl⟩ : syracuseStep 3719375 = 5579063) B5579063
theorem B23511343 : Blo 1222929 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B1835423 : Blo 1222929 1835423 := bstep (se 1 (by rfl) ⟨1376567, by rfl⟩ : syracuseStep 1835423 = 2753135) B2753135
theorem B1376671 : Blo 1222929 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B3097055 : Blo 1222929 3097055 := bstep (se 1 (by rfl) ⟨2322791, by rfl⟩ : syracuseStep 3097055 = 4645583) B4645583
theorem B18833897 : Blo 1222929 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B2753081 : Blo 1222929 2753081 := bstep (se 2 (by rfl) ⟨1032405, by rfl⟩ : syracuseStep 2753081 = 2064811) B2064811
theorem B1835687 : Blo 1222929 1835687 := bstep (se 1 (by rfl) ⟨1376765, by rfl⟩ : syracuseStep 1835687 = 2753531) B2753531
theorem B1835807 : Blo 1222929 1835807 := bstep (se 1 (by rfl) ⟨1376855, by rfl⟩ : syracuseStep 1835807 = 2753711) B2753711
theorem B1835831 : Blo 1222929 1835831 := bstep (se 1 (by rfl) ⟨1376873, by rfl⟩ : syracuseStep 1835831 = 2753747) B2753747
theorem B5227325 : Blo 1222929 5227325 := bstep (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) B1960247
theorem B2065223 : Blo 1222929 2065223 := bstep (se 1 (by rfl) ⟨1548917, by rfl⟩ : syracuseStep 2065223 = 3097835) B3097835
theorem B1836011 : Blo 1222929 1836011 := bstep (se 1 (by rfl) ⟨1377008, by rfl⟩ : syracuseStep 1836011 = 2754017) B2754017
theorem B4130027 : Blo 1222929 4130027 := bstep (se 1 (by rfl) ⟨3097520, by rfl⟩ : syracuseStep 4130027 = 6195041) B6195041
theorem B2753801 : Blo 1222929 2753801 := bstep (se 2 (by rfl) ⟨1032675, by rfl⟩ : syracuseStep 2753801 = 2065351) B2065351
theorem B203703569 : Blo 1222929 203703569 := bstep (se 2 (by rfl) ⟨76388838, by rfl⟩ : syracuseStep 203703569 = 152777677) B152777677
theorem B1836521 : Blo 1222929 1836521 := bstep (se 2 (by rfl) ⟨688695, by rfl⟩ : syracuseStep 1836521 = 1377391) B1377391
theorem B5441087 : Blo 1222929 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B2205415 : Blo 1222929 2205415 := bstep (se 1 (by rfl) ⟨1654061, by rfl⟩ : syracuseStep 2205415 = 3308123) B3308123
theorem B18376465 : Blo 1222929 18376465 := bstep (se 2 (by rfl) ⟨6891174, by rfl⟩ : syracuseStep 18376465 = 13782349) B13782349
theorem B2754323 : Blo 1222929 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B2754683 : Blo 1222929 2754683 := bstep (se 1 (by rfl) ⟨2066012, by rfl⟩ : syracuseStep 2754683 = 4132025) B4132025
theorem B7440599 : Blo 1222929 7440599 := bstep (se 1 (by rfl) ⟨5580449, by rfl⟩ : syracuseStep 7440599 = 11160899) B11160899
theorem B2754791 : Blo 1222929 2754791 := bstep (se 1 (by rfl) ⟨2066093, by rfl⟩ : syracuseStep 2754791 = 4132187) B4132187
theorem B5957875 : Blo 1222929 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B2754953 : Blo 1222929 2754953 := bstep (se 2 (by rfl) ⟨1033107, by rfl⟩ : syracuseStep 2754953 = 2066215) B2066215
theorem B1223071 : Blo 1222929 1223071 := bstep (se 1 (by rfl) ⟨917303, by rfl⟩ : syracuseStep 1223071 = 1834607) B1834607
theorem B1223151 : Blo 1222929 1223151 := bstep (se 1 (by rfl) ⟨917363, by rfl⟩ : syracuseStep 1223151 = 1834727) B1834727
theorem B1223279 : Blo 1222929 1223279 := bstep (se 1 (by rfl) ⟨917459, by rfl⟩ : syracuseStep 1223279 = 1834919) B1834919
theorem B1223495 : Blo 1222929 1223495 := bstep (se 1 (by rfl) ⟨917621, by rfl⟩ : syracuseStep 1223495 = 1835243) B1835243
theorem B1223535 : Blo 1222929 1223535 := bstep (se 1 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 1223535 = 1835303) B1835303
theorem B1469647 : Blo 1222929 1469647 := bstep (se 1 (by rfl) ⟨1102235, by rfl⟩ : syracuseStep 1469647 = 2204471) B2204471
theorem B3919097 : Blo 1222929 3919097 := bstep (se 2 (by rfl) ⟨1469661, by rfl⟩ : syracuseStep 3919097 = 2939323) B2939323
theorem B3722489 : Blo 1222929 3722489 := bstep (se 2 (by rfl) ⟨1395933, by rfl⟩ : syracuseStep 3722489 = 2791867) B2791867
theorem B1223983 : Blo 1222929 1223983 := bstep (se 1 (by rfl) ⟨917987, by rfl⟩ : syracuseStep 1223983 = 1835975) B1835975
theorem B3919225 : Blo 1222929 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B3722635 : Blo 1222929 3722635 := bstep (se 1 (by rfl) ⟨2791976, by rfl⟩ : syracuseStep 3722635 = 5583953) B5583953
theorem B1224095 : Blo 1222929 1224095 := bstep (se 1 (by rfl) ⟨918071, by rfl⟩ : syracuseStep 1224095 = 1836143) B1836143
theorem B3919367 : Blo 1222929 3919367 := bstep (se 1 (by rfl) ⟨2939525, by rfl⟩ : syracuseStep 3919367 = 5879051) B5879051
theorem B1224223 : Blo 1222929 1224223 := bstep (se 1 (by rfl) ⟨918167, by rfl⟩ : syracuseStep 1224223 = 1836335) B1836335
theorem B1224359 : Blo 1222929 1224359 := bstep (se 1 (by rfl) ⟨918269, by rfl⟩ : syracuseStep 1224359 = 1836539) B1836539
theorem B1224383 : Blo 1222929 1224383 := bstep (se 1 (by rfl) ⟨918287, by rfl⟩ : syracuseStep 1224383 = 1836575) B1836575
theorem B13938479 : Blo 1222929 13938479 := bstep (se 1 (by rfl) ⟨10453859, by rfl⟩ : syracuseStep 13938479 = 20907719) B20907719
theorem B6967235 : Blo 1222929 6967235 := bstep (se 1 (by rfl) ⟨5225426, by rfl⟩ : syracuseStep 6967235 = 10450853) B10450853
theorem B2387999 : Blo 1222929 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B6967417 : Blo 1222929 6967417 := bstep (se 2 (by rfl) ⟨2612781, by rfl⟩ : syracuseStep 6967417 = 5225563) B5225563
theorem B3920147 : Blo 1222929 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B13414691 : Blo 1222929 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B8819063 : Blo 1222929 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B59569141 : Blo 1222929 59569141 := bstep (se 5 (by rfl) ⟨2792303, by rfl⟩ : syracuseStep 59569141 = 5584607) B5584607
theorem B4772935 : Blo 1222929 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B6616199 : Blo 1222929 6616199 := bstep (se 1 (by rfl) ⟨4962149, by rfl⟩ : syracuseStep 6616199 = 9924299) B9924299
theorem B12735791 : Blo 1222929 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B6280697 : Blo 1222929 6280697 := bstep (se 2 (by rfl) ⟨2355261, by rfl⟩ : syracuseStep 6280697 = 4710523) B4710523
theorem B6280859 : Blo 1222929 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B14890729 : Blo 1222929 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B2324447 : Blo 1222929 2324447 := bstep (se 1 (by rfl) ⟨1743335, by rfl⟩ : syracuseStep 2324447 = 3486671) B3486671
theorem B6969833 : Blo 1222929 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B4127543 : Blo 1222929 4127543 := bstep (se 1 (by rfl) ⟨3095657, by rfl⟩ : syracuseStep 4127543 = 6191315) B6191315
theorem B3308359 : Blo 1222929 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B3095759 : Blo 1222929 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B1834475 : Blo 1222929 1834475 := bstep (se 1 (by rfl) ⟨1375856, by rfl⟩ : syracuseStep 1834475 = 2751713) B2751713
theorem B3096083 : Blo 1222929 3096083 := bstep (se 1 (by rfl) ⟨2322062, by rfl⟩ : syracuseStep 3096083 = 4644125) B4644125
theorem B1834679 : Blo 1222929 1834679 := bstep (se 1 (by rfl) ⟨1376009, by rfl⟩ : syracuseStep 1834679 = 2752019) B2752019
theorem B7839575 : Blo 1222929 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B4128623 : Blo 1222929 4128623 := bstep (se 1 (by rfl) ⟨3096467, by rfl⟩ : syracuseStep 4128623 = 6192935) B6192935
theorem B1834889 : Blo 1222929 1834889 := bstep (se 2 (by rfl) ⟨688083, by rfl⟩ : syracuseStep 1834889 = 1376167) B1376167
theorem B6971291 : Blo 1222929 6971291 := bstep (se 1 (by rfl) ⟨5228468, by rfl⟩ : syracuseStep 6971291 = 10456937) B10456937
theorem B9289889 : Blo 1222929 9289889 := bstep (se 2 (by rfl) ⟨3483708, by rfl⟩ : syracuseStep 9289889 = 6967417) B6967417
theorem B1835177 : Blo 1222929 1835177 := bstep (se 2 (by rfl) ⟨688191, by rfl⟩ : syracuseStep 1835177 = 1376383) B1376383
theorem B2613431 : Blo 1222929 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B2064703 : Blo 1222929 2064703 := bstep (se 1 (by rfl) ⟨1548527, by rfl⟩ : syracuseStep 2064703 = 3097055) B3097055
theorem B1835387 : Blo 1222929 1835387 := bstep (se 1 (by rfl) ⟨1376540, by rfl⟩ : syracuseStep 1835387 = 2753081) B2753081
theorem B1835561 : Blo 1222929 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B1376815 : Blo 1222929 1376815 := bstep (se 1 (by rfl) ⟨1032611, by rfl⟩ : syracuseStep 1376815 = 2065223) B2065223
theorem B2753351 : Blo 1222929 2753351 := bstep (se 1 (by rfl) ⟨2065013, by rfl⟩ : syracuseStep 2753351 = 4130027) B4130027
theorem B1835867 : Blo 1222929 1835867 := bstep (se 1 (by rfl) ⟨1376900, by rfl⟩ : syracuseStep 1835867 = 2753801) B2753801
theorem B1836215 : Blo 1222929 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B1549631 : Blo 1222929 1549631 := bstep (se 1 (by rfl) ⟨1162223, by rfl⟩ : syracuseStep 1549631 = 2324447) B2324447
theorem B1836455 : Blo 1222929 1836455 := bstep (se 1 (by rfl) ⟨1377341, by rfl⟩ : syracuseStep 1836455 = 2754683) B2754683
theorem B1836527 : Blo 1222929 1836527 := bstep (se 1 (by rfl) ⟨1377395, by rfl⟩ : syracuseStep 1836527 = 2754791) B2754791
theorem B1836635 : Blo 1222929 1836635 := bstep (se 1 (by rfl) ⟨1377476, by rfl⟩ : syracuseStep 1836635 = 2754953) B2754953
theorem B4646555 : Blo 1222929 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B1222983 : Blo 1222929 1222983 := bstep (se 1 (by rfl) ⟨917237, by rfl⟩ : syracuseStep 1222983 = 1834475) B1834475
theorem B1223119 : Blo 1222929 1223119 := bstep (se 1 (by rfl) ⟨917339, by rfl⟩ : syracuseStep 1223119 = 1834679) B1834679
theorem B9292319 : Blo 1222929 9292319 := bstep (se 1 (by rfl) ⟨6969239, by rfl⟩ : syracuseStep 9292319 = 13938479) B13938479
theorem B1223259 : Blo 1222929 1223259 := bstep (se 1 (by rfl) ⟨917444, by rfl⟩ : syracuseStep 1223259 = 1834889) B1834889
theorem B4647527 : Blo 1222929 4647527 := bstep (se 1 (by rfl) ⟨3485645, by rfl⟩ : syracuseStep 4647527 = 6971291) B6971291
theorem B6367997 : Blo 1222929 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1223423 : Blo 1222929 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B1223615 : Blo 1222929 1223615 := bstep (se 1 (by rfl) ⟨917711, by rfl⟩ : syracuseStep 1223615 = 1835423) B1835423
theorem B1223791 : Blo 1222929 1223791 := bstep (se 1 (by rfl) ⟨917843, by rfl⟩ : syracuseStep 1223791 = 1835687) B1835687
theorem B1223871 : Blo 1222929 1223871 := bstep (se 1 (by rfl) ⟨917903, by rfl⟩ : syracuseStep 1223871 = 1835807) B1835807
theorem B1223887 : Blo 1222929 1223887 := bstep (se 1 (by rfl) ⟨917915, by rfl⟩ : syracuseStep 1223887 = 1835831) B1835831
theorem B3484883 : Blo 1222929 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B1224007 : Blo 1222929 1224007 := bstep (se 1 (by rfl) ⟨918005, by rfl⟩ : syracuseStep 1224007 = 1836011) B1836011
theorem B135802379 : Blo 1222929 135802379 := bstep (se 1 (by rfl) ⟨101851784, by rfl⟩ : syracuseStep 135802379 = 203703569) B203703569
theorem B8490527 : Blo 1222929 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B1224347 : Blo 1222929 1224347 := bstep (se 1 (by rfl) ⟨918260, by rfl⟩ : syracuseStep 1224347 = 1836521) B1836521
theorem B4411145 : Blo 1222929 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B16748525 : Blo 1222929 16748525 := bstep (se 3 (by rfl) ⟨3140348, by rfl⟩ : syracuseStep 16748525 = 6280697) B6280697
theorem B79425521 : Blo 1222929 79425521 := bstep (se 2 (by rfl) ⟨29784570, by rfl⟩ : syracuseStep 79425521 = 59569141) B59569141
theorem B4960399 : Blo 1222929 4960399 := bstep (se 1 (by rfl) ⟨3720299, by rfl⟩ : syracuseStep 4960399 = 7440599) B7440599
theorem B16748957 : Blo 1222929 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B19854305 : Blo 1222929 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B2479583 : Blo 1222929 2479583 := bstep (se 1 (by rfl) ⟨1859687, by rfl⟩ : syracuseStep 2479583 = 3719375) B3719375
theorem B5879375 : Blo 1222929 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B12555931 : Blo 1222929 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B17643197 : Blo 1222929 17643197 := bstep (se 3 (by rfl) ⟨3308099, by rfl⟩ : syracuseStep 17643197 = 6616199) B6616199
theorem B31348457 : Blo 1222929 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B35772509 : Blo 1222929 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B3627391 : Blo 1222929 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B7838117 : Blo 1222929 7838117 := bstep (se 4 (by rfl) ⟨734823, by rfl⟩ : syracuseStep 7838117 = 1469647) B1469647
theorem B31775333 : Blo 1222929 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B6363913 : Blo 1222929 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B5225633 : Blo 1222929 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B4963513 : Blo 1222929 4963513 := bstep (se 2 (by rfl) ⟨1861317, by rfl⟩ : syracuseStep 4963513 = 3722635) B3722635
theorem B2751695 : Blo 1222929 2751695 := bstep (se 1 (by rfl) ⟨2063771, by rfl⟩ : syracuseStep 2751695 = 4127543) B4127543
theorem B2063839 : Blo 1222929 2063839 := bstep (se 1 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 2063839 = 3095759) B3095759
theorem B2612731 : Blo 1222929 2612731 := bstep (se 1 (by rfl) ⟨1959548, by rfl⟩ : syracuseStep 2612731 = 3919097) B3919097
theorem B2481659 : Blo 1222929 2481659 := bstep (se 1 (by rfl) ⟨1861244, by rfl⟩ : syracuseStep 2481659 = 3722489) B3722489
theorem B2940553 : Blo 1222929 2940553 := bstep (se 2 (by rfl) ⟨1102707, by rfl⟩ : syracuseStep 2940553 = 2205415) B2205415
theorem B2612911 : Blo 1222929 2612911 := bstep (se 1 (by rfl) ⟨1959683, by rfl⟩ : syracuseStep 2612911 = 3919367) B3919367
theorem B2064055 : Blo 1222929 2064055 := bstep (se 1 (by rfl) ⟨1548041, by rfl⟩ : syracuseStep 2064055 = 3096083) B3096083
theorem B24501953 : Blo 1222929 24501953 := bstep (se 2 (by rfl) ⟨9188232, by rfl⟩ : syracuseStep 24501953 = 18376465) B18376465
theorem B5226383 : Blo 1222929 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B2752415 : Blo 1222929 2752415 := bstep (se 1 (by rfl) ⟨2064311, by rfl⟩ : syracuseStep 2752415 = 4128623) B4128623
theorem B4644823 : Blo 1222929 4644823 := bstep (se 1 (by rfl) ⟨3483617, by rfl⟩ : syracuseStep 4644823 = 6967235) B6967235
theorem B6193259 : Blo 1222929 6193259 := bstep (se 1 (by rfl) ⟨4644944, by rfl⟩ : syracuseStep 6193259 = 9289889) B9289889
theorem B2752937 : Blo 1222929 2752937 := bstep (se 2 (by rfl) ⟨1032351, by rfl⟩ : syracuseStep 2752937 = 2064703) B2064703
theorem B1835567 : Blo 1222929 1835567 := bstep (se 1 (by rfl) ⟨1376675, by rfl⟩ : syracuseStep 1835567 = 2753351) B2753351
theorem B1835753 : Blo 1222929 1835753 := bstep (se 2 (by rfl) ⟨688407, by rfl⟩ : syracuseStep 1835753 = 1376815) B1376815
theorem B338936885 : Blo 1222929 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B44663885 : Blo 1222929 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B3097703 : Blo 1222929 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B20898971 : Blo 1222929 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B23848339 : Blo 1222929 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B6194879 : Blo 1222929 6194879 := bstep (se 1 (by rfl) ⟨4646159, by rfl⟩ : syracuseStep 6194879 = 9292319) B9292319
theorem B3098351 : Blo 1222929 3098351 := bstep (se 1 (by rfl) ⟨2323763, by rfl⟩ : syracuseStep 3098351 = 4647527) B4647527
theorem B3483641 : Blo 1222929 3483641 := bstep (se 2 (by rfl) ⟨1306365, by rfl⟩ : syracuseStep 3483641 = 2612731) B2612731
theorem B3483755 : Blo 1222929 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B3483881 : Blo 1222929 3483881 := bstep (se 2 (by rfl) ⟨1306455, by rfl⟩ : syracuseStep 3483881 = 2612911) B2612911
theorem B13937021 : Blo 1222929 13937021 := bstep (se 3 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 13937021 = 5226383) B5226383
theorem B1223451 : Blo 1222929 1223451 := bstep (se 1 (by rfl) ⟨917588, by rfl⟩ : syracuseStep 1223451 = 1835177) B1835177
theorem B6613865 : Blo 1222929 6613865 := bstep (se 2 (by rfl) ⟨2480199, by rfl⟩ : syracuseStep 6613865 = 4960399) B4960399
theorem B1223591 : Blo 1222929 1223591 := bstep (se 1 (by rfl) ⟨917693, by rfl⟩ : syracuseStep 1223591 = 1835387) B1835387
theorem B1223707 : Blo 1222929 1223707 := bstep (se 1 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 1223707 = 1835561) B1835561
theorem B4836521 : Blo 1222929 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B1223911 : Blo 1222929 1223911 := bstep (se 1 (by rfl) ⟨917933, by rfl⟩ : syracuseStep 1223911 = 1835867) B1835867
theorem B1224143 : Blo 1222929 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B4132349 : Blo 1222929 4132349 := bstep (se 3 (by rfl) ⟨774815, by rfl⟩ : syracuseStep 4132349 = 1549631) B1549631
theorem B1224303 : Blo 1222929 1224303 := bstep (se 1 (by rfl) ⟨918227, by rfl⟩ : syracuseStep 1224303 = 1836455) B1836455
theorem B1224351 : Blo 1222929 1224351 := bstep (se 1 (by rfl) ⟨918263, by rfl⟩ : syracuseStep 1224351 = 1836527) B1836527
theorem B3919583 : Blo 1222929 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B1224423 : Blo 1222929 1224423 := bstep (se 1 (by rfl) ⟨918317, by rfl⟩ : syracuseStep 1224423 = 1836635) B1836635
theorem B2323255 : Blo 1222929 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B3920737 : Blo 1222929 3920737 := bstep (se 2 (by rfl) ⟨1470276, by rfl⟩ : syracuseStep 3920737 = 2940553) B2940553
theorem B16741241 : Blo 1222929 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B90534919 : Blo 1222929 90534919 := bstep (se 1 (by rfl) ⟨67901189, by rfl⟩ : syracuseStep 90534919 = 135802379) B135802379
theorem B52950347 : Blo 1222929 52950347 := bstep (se 1 (by rfl) ⟨39712760, by rfl⟩ : syracuseStep 52950347 = 79425521) B79425521
theorem B6969149 : Blo 1222929 6969149 := bstep (se 3 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 6969149 = 2613431) B2613431
theorem B13236203 : Blo 1222929 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B1653055 : Blo 1222929 1653055 := bstep (se 1 (by rfl) ⟨1239791, by rfl⟩ : syracuseStep 1653055 = 2479583) B2479583
theorem B8485217 : Blo 1222929 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B11762131 : Blo 1222929 11762131 := bstep (se 1 (by rfl) ⟨8821598, by rfl⟩ : syracuseStep 11762131 = 17643197) B17643197
theorem B6618017 : Blo 1222929 6618017 := bstep (se 2 (by rfl) ⟨2481756, by rfl⟩ : syracuseStep 6618017 = 4963513) B4963513
theorem B5225411 : Blo 1222929 5225411 := bstep (se 1 (by rfl) ⟨3919058, by rfl⟩ : syracuseStep 5225411 = 7838117) B7838117
theorem B2751785 : Blo 1222929 2751785 := bstep (se 2 (by rfl) ⟨1031919, by rfl⟩ : syracuseStep 2751785 = 2063839) B2063839
theorem B16981325 : Blo 1222929 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B11763053 : Blo 1222929 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B1834463 : Blo 1222929 1834463 := bstep (se 1 (by rfl) ⟨1375847, by rfl⟩ : syracuseStep 1834463 = 2751695) B2751695
theorem B2752073 : Blo 1222929 2752073 := bstep (se 2 (by rfl) ⟨1032027, by rfl⟩ : syracuseStep 2752073 = 2064055) B2064055
theorem B1654439 : Blo 1222929 1654439 := bstep (se 1 (by rfl) ⟨1240829, by rfl⟩ : syracuseStep 1654439 = 2481659) B2481659
theorem B5660351 : Blo 1222929 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B16334635 : Blo 1222929 16334635 := bstep (se 1 (by rfl) ⟨12250976, by rfl⟩ : syracuseStep 16334635 = 24501953) B24501953
theorem B1834943 : Blo 1222929 1834943 := bstep (se 1 (by rfl) ⟨1376207, by rfl⟩ : syracuseStep 1834943 = 2752415) B2752415
theorem B6193097 : Blo 1222929 6193097 := bstep (se 2 (by rfl) ⟨2322411, by rfl⟩ : syracuseStep 6193097 = 4644823) B4644823
theorem B11165683 : Blo 1222929 11165683 := bstep (se 1 (by rfl) ⟨8374262, by rfl⟩ : syracuseStep 11165683 = 16748525) B16748525
theorem B4128839 : Blo 1222929 4128839 := bstep (se 1 (by rfl) ⟨3096629, by rfl⟩ : syracuseStep 4128839 = 6193259) B6193259
theorem B1835291 : Blo 1222929 1835291 := bstep (se 1 (by rfl) ⟨1376468, by rfl⟩ : syracuseStep 1835291 = 2752937) B2752937
theorem B2065135 : Blo 1222929 2065135 := bstep (se 1 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 2065135 = 3097703) B3097703
theorem B35300231 : Blo 1222929 35300231 := bstep (se 1 (by rfl) ⟨26475173, by rfl⟩ : syracuseStep 35300231 = 52950347) B52950347
theorem B3097673 : Blo 1222929 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B4129919 : Blo 1222929 4129919 := bstep (se 1 (by rfl) ⟨3097439, by rfl⟩ : syracuseStep 4129919 = 6194879) B6194879
theorem B5227649 : Blo 1222929 5227649 := bstep (se 2 (by rfl) ⟨1960368, by rfl⟩ : syracuseStep 5227649 = 3920737) B3920737
theorem B2065567 : Blo 1222929 2065567 := bstep (se 1 (by rfl) ⟨1549175, by rfl⟩ : syracuseStep 2065567 = 3098351) B3098351
theorem B4646099 : Blo 1222929 4646099 := bstep (se 1 (by rfl) ⟨3484574, by rfl⟩ : syracuseStep 4646099 = 6969149) B6969149
theorem B8824135 : Blo 1222929 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B9291347 : Blo 1222929 9291347 := bstep (se 1 (by rfl) ⟨6968510, by rfl⟩ : syracuseStep 9291347 = 13937021) B13937021
theorem B8816293 : Blo 1222929 8816293 := bstep (se 4 (by rfl) ⟨826527, by rfl⟩ : syracuseStep 8816293 = 1653055) B1653055
theorem B4409243 : Blo 1222929 4409243 := bstep (se 1 (by rfl) ⟨3306932, by rfl⟩ : syracuseStep 4409243 = 6613865) B6613865
theorem B3483607 : Blo 1222929 3483607 := bstep (se 1 (by rfl) ⟨2612705, by rfl⟩ : syracuseStep 3483607 = 5225411) B5225411
theorem B7842035 : Blo 1222929 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B1222975 : Blo 1222929 1222975 := bstep (se 1 (by rfl) ⟨917231, by rfl⟩ : syracuseStep 1222975 = 1834463) B1834463
theorem B2754899 : Blo 1222929 2754899 := bstep (se 1 (by rfl) ⟨2066174, by rfl⟩ : syracuseStep 2754899 = 4132349) B4132349
theorem B1223295 : Blo 1222929 1223295 := bstep (se 1 (by rfl) ⟨917471, by rfl⟩ : syracuseStep 1223295 = 1834943) B1834943
theorem B14887577 : Blo 1222929 14887577 := bstep (se 2 (by rfl) ⟨5582841, by rfl⟩ : syracuseStep 14887577 = 11165683) B11165683
theorem B1223711 : Blo 1222929 1223711 := bstep (se 1 (by rfl) ⟨917783, by rfl⟩ : syracuseStep 1223711 = 1835567) B1835567
theorem B12897389 : Blo 1222929 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B1223835 : Blo 1222929 1223835 := bstep (se 1 (by rfl) ⟨917876, by rfl⟩ : syracuseStep 1223835 = 1835753) B1835753
theorem B11160827 : Blo 1222929 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B15682841 : Blo 1222929 15682841 := bstep (se 2 (by rfl) ⟨5881065, by rfl⟩ : syracuseStep 15682841 = 11762131) B11762131
theorem B2322427 : Blo 1222929 2322427 := bstep (se 1 (by rfl) ⟨1741820, by rfl⟩ : syracuseStep 2322427 = 3483641) B3483641
theorem B120713225 : Blo 1222929 120713225 := bstep (se 2 (by rfl) ⟨45267459, by rfl⟩ : syracuseStep 120713225 = 90534919) B90534919
theorem B2322503 : Blo 1222929 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B2322587 : Blo 1222929 2322587 := bstep (se 1 (by rfl) ⟨1741940, by rfl⟩ : syracuseStep 2322587 = 3483881) B3483881
theorem B5656811 : Blo 1222929 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B4411837 : Blo 1222929 4411837 := bstep (se 3 (by rfl) ⟨827219, by rfl⟩ : syracuseStep 4411837 = 1654439) B1654439
theorem B31797785 : Blo 1222929 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B4412011 : Blo 1222929 4412011 := bstep (se 1 (by rfl) ⟨3309008, by rfl⟩ : syracuseStep 4412011 = 6618017) B6618017
theorem B21779513 : Blo 1222929 21779513 := bstep (se 2 (by rfl) ⟨8167317, by rfl⟩ : syracuseStep 21779513 = 16334635) B16334635
theorem B3773567 : Blo 1222929 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B225957923 : Blo 1222929 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B29775923 : Blo 1222929 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B13932647 : Blo 1222929 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B1834523 : Blo 1222929 1834523 := bstep (se 1 (by rfl) ⟨1375892, by rfl⟩ : syracuseStep 1834523 = 2751785) B2751785
theorem B11320883 : Blo 1222929 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B1834715 : Blo 1222929 1834715 := bstep (se 1 (by rfl) ⟨1376036, by rfl⟩ : syracuseStep 1834715 = 2752073) B2752073
theorem B2613055 : Blo 1222929 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B4128731 : Blo 1222929 4128731 := bstep (se 1 (by rfl) ⟨3096548, by rfl⟩ : syracuseStep 4128731 = 6193097) B6193097
theorem B2752559 : Blo 1222929 2752559 := bstep (se 1 (by rfl) ⟨2064419, by rfl⟩ : syracuseStep 2752559 = 4128839) B4128839
theorem B1548335 : Blo 1222929 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B1548391 : Blo 1222929 1548391 := bstep (se 1 (by rfl) ⟨1161293, by rfl⟩ : syracuseStep 1548391 = 2322587) B2322587
theorem B2065115 : Blo 1222929 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B2753279 : Blo 1222929 2753279 := bstep (se 1 (by rfl) ⟨2064959, by rfl⟩ : syracuseStep 2753279 = 4129919) B4129919
theorem B2515711 : Blo 1222929 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B3097399 : Blo 1222929 3097399 := bstep (se 1 (by rfl) ⟨2323049, by rfl⟩ : syracuseStep 3097399 = 4646099) B4646099
theorem B5882681 : Blo 1222929 5882681 := bstep (se 2 (by rfl) ⟨2206005, by rfl⟩ : syracuseStep 5882681 = 4412011) B4412011
theorem B2753513 : Blo 1222929 2753513 := bstep (se 2 (by rfl) ⟨1032567, by rfl⟩ : syracuseStep 2753513 = 2065135) B2065135
theorem B6194231 : Blo 1222929 6194231 := bstep (se 1 (by rfl) ⟨4645673, by rfl⟩ : syracuseStep 6194231 = 9291347) B9291347
theorem B19850615 : Blo 1222929 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B2754089 : Blo 1222929 2754089 := bstep (se 2 (by rfl) ⟨1032783, by rfl⟩ : syracuseStep 2754089 = 2065567) B2065567
theorem B1836599 : Blo 1222929 1836599 := bstep (se 1 (by rfl) ⟨1377449, by rfl⟩ : syracuseStep 1836599 = 2754899) B2754899
theorem B11765513 : Blo 1222929 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B7440551 : Blo 1222929 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B10455227 : Blo 1222929 10455227 := bstep (se 1 (by rfl) ⟨7841420, by rfl⟩ : syracuseStep 10455227 = 15682841) B15682841
theorem B23529797 : Blo 1222929 23529797 := bstep (se 4 (by rfl) ⟨2205918, by rfl⟩ : syracuseStep 23529797 = 4411837) B4411837
theorem B1223015 : Blo 1222929 1223015 := bstep (se 1 (by rfl) ⟨917261, by rfl⟩ : syracuseStep 1223015 = 1834523) B1834523
theorem B7547255 : Blo 1222929 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B3484073 : Blo 1222929 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B1223143 : Blo 1222929 1223143 := bstep (se 1 (by rfl) ⟨917357, by rfl⟩ : syracuseStep 1223143 = 1834715) B1834715
theorem B1223527 : Blo 1222929 1223527 := bstep (se 1 (by rfl) ⟨917645, by rfl⟩ : syracuseStep 1223527 = 1835291) B1835291
theorem B15084829 : Blo 1222929 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B14519675 : Blo 1222929 14519675 := bstep (se 1 (by rfl) ⟨10889756, by rfl⟩ : syracuseStep 14519675 = 21779513) B21779513
theorem B3485099 : Blo 1222929 3485099 := bstep (se 1 (by rfl) ⟨2613824, by rfl⟩ : syracuseStep 3485099 = 5227649) B5227649
theorem B150638615 : Blo 1222929 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B9925051 : Blo 1222929 9925051 := bstep (se 1 (by rfl) ⟨7443788, by rfl⟩ : syracuseStep 9925051 = 14887577) B14887577
theorem B8598259 : Blo 1222929 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B321901933 : Blo 1222929 321901933 := bstep (se 3 (by rfl) ⟨60356612, by rfl⟩ : syracuseStep 321901933 = 120713225) B120713225
theorem B21198523 : Blo 1222929 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B23533487 : Blo 1222929 23533487 := bstep (se 1 (by rfl) ⟨17650115, by rfl⟩ : syracuseStep 23533487 = 35300231) B35300231
theorem B20912093 : Blo 1222929 20912093 := bstep (se 3 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 20912093 = 7842035) B7842035
theorem B2939495 : Blo 1222929 2939495 := bstep (se 1 (by rfl) ⟨2204621, by rfl⟩ : syracuseStep 2939495 = 4409243) B4409243
theorem B9288431 : Blo 1222929 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B11755057 : Blo 1222929 11755057 := bstep (se 2 (by rfl) ⟨4408146, by rfl⟩ : syracuseStep 11755057 = 8816293) B8816293
theorem B4644809 : Blo 1222929 4644809 := bstep (se 2 (by rfl) ⟨1741803, by rfl⟩ : syracuseStep 4644809 = 3483607) B3483607
theorem B2752487 : Blo 1222929 2752487 := bstep (se 1 (by rfl) ⟨2064365, by rfl⟩ : syracuseStep 2752487 = 4128731) B4128731
theorem B3096569 : Blo 1222929 3096569 := bstep (se 2 (by rfl) ⟨1161213, by rfl⟩ : syracuseStep 3096569 = 2322427) B2322427
theorem B100425743 : Blo 1222929 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B1835039 : Blo 1222929 1835039 := bstep (se 1 (by rfl) ⟨1376279, by rfl⟩ : syracuseStep 1835039 = 2752559) B2752559
theorem B4128893 : Blo 1222929 4128893 := bstep (se 3 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 4128893 = 1548335) B1548335
theorem B2064521 : Blo 1222929 2064521 := bstep (se 2 (by rfl) ⟨774195, by rfl⟩ : syracuseStep 2064521 = 1548391) B1548391
theorem B1376743 : Blo 1222929 1376743 := bstep (se 1 (by rfl) ⟨1032557, by rfl⟩ : syracuseStep 1376743 = 2065115) B2065115
theorem B1835519 : Blo 1222929 1835519 := bstep (se 1 (by rfl) ⟨1376639, by rfl⟩ : syracuseStep 1835519 = 2753279) B2753279
theorem B1835675 : Blo 1222929 1835675 := bstep (se 1 (by rfl) ⟨1376756, by rfl⟩ : syracuseStep 1835675 = 2753513) B2753513
theorem B4129487 : Blo 1222929 4129487 := bstep (se 1 (by rfl) ⟨3097115, by rfl⟩ : syracuseStep 4129487 = 6194231) B6194231
theorem B1836059 : Blo 1222929 1836059 := bstep (se 1 (by rfl) ⟨1377044, by rfl⟩ : syracuseStep 1836059 = 2754089) B2754089
theorem B4129865 : Blo 1222929 4129865 := bstep (se 2 (by rfl) ⟨1548699, by rfl⟩ : syracuseStep 4129865 = 3097399) B3097399
theorem B9290861 : Blo 1222929 9290861 := bstep (se 3 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 9290861 = 3484073) B3484073
theorem B15688991 : Blo 1222929 15688991 := bstep (se 1 (by rfl) ⟨11766743, by rfl⟩ : syracuseStep 15688991 = 23533487) B23533487
theorem B5031503 : Blo 1222929 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B20113105 : Blo 1222929 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B15673409 : Blo 1222929 15673409 := bstep (se 2 (by rfl) ⟨5877528, by rfl⟩ : syracuseStep 15673409 = 11755057) B11755057
theorem B28264697 : Blo 1222929 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B13233401 : Blo 1222929 13233401 := bstep (se 2 (by rfl) ⟨4962525, by rfl⟩ : syracuseStep 13233401 = 9925051) B9925051
theorem B13233743 : Blo 1222929 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B11464345 : Blo 1222929 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B3354281 : Blo 1222929 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B1224399 : Blo 1222929 1224399 := bstep (se 1 (by rfl) ⟨918299, by rfl⟩ : syracuseStep 1224399 = 1836599) B1836599
theorem B4960367 : Blo 1222929 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B9679783 : Blo 1222929 9679783 := bstep (se 1 (by rfl) ⟨7259837, by rfl⟩ : syracuseStep 9679783 = 14519675) B14519675
theorem B2323399 : Blo 1222929 2323399 := bstep (se 1 (by rfl) ⟨1742549, by rfl⟩ : syracuseStep 2323399 = 3485099) B3485099
theorem B3921787 : Blo 1222929 3921787 := bstep (se 1 (by rfl) ⟨2941340, by rfl⟩ : syracuseStep 3921787 = 5882681) B5882681
theorem B13941395 : Blo 1222929 13941395 := bstep (se 1 (by rfl) ⟨10456046, by rfl⟩ : syracuseStep 13941395 = 20912093) B20912093
theorem B6970151 : Blo 1222929 6970151 := bstep (se 1 (by rfl) ⟨5227613, by rfl⟩ : syracuseStep 6970151 = 10455227) B10455227
theorem B15686531 : Blo 1222929 15686531 := bstep (se 1 (by rfl) ⟨11764898, by rfl⟩ : syracuseStep 15686531 = 23529797) B23529797
theorem B7838653 : Blo 1222929 7838653 := bstep (se 3 (by rfl) ⟨1469747, by rfl⟩ : syracuseStep 7838653 = 2939495) B2939495
theorem B429202577 : Blo 1222929 429202577 := bstep (se 2 (by rfl) ⟨160950966, by rfl⟩ : syracuseStep 429202577 = 321901933) B321901933
theorem B6192287 : Blo 1222929 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B31374701 : Blo 1222929 31374701 := bstep (se 3 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 31374701 = 11765513) B11765513
theorem B3096539 : Blo 1222929 3096539 := bstep (se 1 (by rfl) ⟨2322404, by rfl⟩ : syracuseStep 3096539 = 4644809) B4644809
theorem B1834991 : Blo 1222929 1834991 := bstep (se 1 (by rfl) ⟨1376243, by rfl⟩ : syracuseStep 1834991 = 2752487) B2752487
theorem B2064379 : Blo 1222929 2064379 := bstep (se 1 (by rfl) ⟨1548284, by rfl⟩ : syracuseStep 2064379 = 3096569) B3096569
theorem B2752595 : Blo 1222929 2752595 := bstep (se 1 (by rfl) ⟨2064446, by rfl⟩ : syracuseStep 2752595 = 4128893) B4128893
theorem B1376347 : Blo 1222929 1376347 := bstep (se 1 (by rfl) ⟨1032260, by rfl⟩ : syracuseStep 1376347 = 2064521) B2064521
theorem B2752991 : Blo 1222929 2752991 := bstep (se 1 (by rfl) ⟨2064743, by rfl⟩ : syracuseStep 2752991 = 4129487) B4129487
theorem B1835657 : Blo 1222929 1835657 := bstep (se 2 (by rfl) ⟨688371, by rfl⟩ : syracuseStep 1835657 = 1376743) B1376743
theorem B2753243 : Blo 1222929 2753243 := bstep (se 1 (by rfl) ⟨2064932, by rfl⟩ : syracuseStep 2753243 = 4129865) B4129865
theorem B6193907 : Blo 1222929 6193907 := bstep (se 1 (by rfl) ⟨4645430, by rfl⟩ : syracuseStep 6193907 = 9290861) B9290861
theorem B3097865 : Blo 1222929 3097865 := bstep (se 2 (by rfl) ⟨1161699, by rfl⟩ : syracuseStep 3097865 = 2323399) B2323399
theorem B18843131 : Blo 1222929 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B4646767 : Blo 1222929 4646767 := bstep (se 1 (by rfl) ⟨3485075, by rfl⟩ : syracuseStep 4646767 = 6970151) B6970151
theorem B20916467 : Blo 1222929 20916467 := bstep (se 1 (by rfl) ⟨15687350, by rfl⟩ : syracuseStep 20916467 = 31374701) B31374701
theorem B5229049 : Blo 1222929 5229049 := bstep (se 2 (by rfl) ⟨1960893, by rfl⟩ : syracuseStep 5229049 = 3921787) B3921787
theorem B1223327 : Blo 1222929 1223327 := bstep (se 1 (by rfl) ⟨917495, by rfl⟩ : syracuseStep 1223327 = 1834991) B1834991
theorem B1223359 : Blo 1222929 1223359 := bstep (se 1 (by rfl) ⟨917519, by rfl⟩ : syracuseStep 1223359 = 1835039) B1835039
theorem B1223679 : Blo 1222929 1223679 := bstep (se 1 (by rfl) ⟨917759, by rfl⟩ : syracuseStep 1223679 = 1835519) B1835519
theorem B1144540205 : Blo 1222929 1144540205 := bstep (se 3 (by rfl) ⟨214601288, by rfl⟩ : syracuseStep 1144540205 = 429202577) B429202577
theorem B1223783 : Blo 1222929 1223783 := bstep (se 1 (by rfl) ⟨917837, by rfl⟩ : syracuseStep 1223783 = 1835675) B1835675
theorem B1224039 : Blo 1222929 1224039 := bstep (se 1 (by rfl) ⟨918029, by rfl⟩ : syracuseStep 1224039 = 1836059) B1836059
theorem B3354335 : Blo 1222929 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B12906377 : Blo 1222929 12906377 := bstep (se 2 (by rfl) ⟨4839891, by rfl⟩ : syracuseStep 12906377 = 9679783) B9679783
theorem B2752505 : Blo 1222929 2752505 := bstep (se 2 (by rfl) ⟨1032189, by rfl⟩ : syracuseStep 2752505 = 2064379) B2064379
theorem B10448939 : Blo 1222929 10448939 := bstep (se 1 (by rfl) ⟨7836704, by rfl⟩ : syracuseStep 10448939 = 15673409) B15673409
theorem B9294263 : Blo 1222929 9294263 := bstep (se 1 (by rfl) ⟨6970697, by rfl⟩ : syracuseStep 9294263 = 13941395) B13941395
theorem B10457687 : Blo 1222929 10457687 := bstep (se 1 (by rfl) ⟨7843265, by rfl⟩ : syracuseStep 10457687 = 15686531) B15686531
theorem B26817473 : Blo 1222929 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B66950495 : Blo 1222929 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B3306911 : Blo 1222929 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B10459327 : Blo 1222929 10459327 := bstep (se 1 (by rfl) ⟨7844495, by rfl⟩ : syracuseStep 10459327 = 15688991) B15688991
theorem B10451537 : Blo 1222929 10451537 := bstep (se 2 (by rfl) ⟨3919326, by rfl⟩ : syracuseStep 10451537 = 7838653) B7838653
theorem B4128191 : Blo 1222929 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B8822267 : Blo 1222929 8822267 := bstep (se 1 (by rfl) ⟨6616700, by rfl⟩ : syracuseStep 8822267 = 13233401) B13233401
theorem B15285793 : Blo 1222929 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B8822495 : Blo 1222929 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B2236187 : Blo 1222929 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B2064359 : Blo 1222929 2064359 := bstep (se 1 (by rfl) ⟨1548269, by rfl⟩ : syracuseStep 2064359 = 3096539) B3096539
theorem B1835063 : Blo 1222929 1835063 := bstep (se 1 (by rfl) ⟨1376297, by rfl⟩ : syracuseStep 1835063 = 2752595) B2752595
theorem B1835129 : Blo 1222929 1835129 := bstep (se 2 (by rfl) ⟨688173, by rfl⟩ : syracuseStep 1835129 = 1376347) B1376347
theorem B1835327 : Blo 1222929 1835327 := bstep (se 1 (by rfl) ⟨1376495, by rfl⟩ : syracuseStep 1835327 = 2752991) B2752991
theorem B6971791 : Blo 1222929 6971791 := bstep (se 1 (by rfl) ⟨5228843, by rfl⟩ : syracuseStep 6971791 = 10457687) B10457687
theorem B1835495 : Blo 1222929 1835495 := bstep (se 1 (by rfl) ⟨1376621, by rfl⟩ : syracuseStep 1835495 = 2753243) B2753243
theorem B4129271 : Blo 1222929 4129271 := bstep (se 1 (by rfl) ⟨3096953, by rfl⟩ : syracuseStep 4129271 = 6193907) B6193907
theorem B6972065 : Blo 1222929 6972065 := bstep (se 2 (by rfl) ⟨2614524, by rfl⟩ : syracuseStep 6972065 = 5229049) B5229049
theorem B2065243 : Blo 1222929 2065243 := bstep (se 1 (by rfl) ⟨1548932, by rfl⟩ : syracuseStep 2065243 = 3097865) B3097865
theorem B13944311 : Blo 1222929 13944311 := bstep (se 1 (by rfl) ⟨10458233, by rfl⟩ : syracuseStep 13944311 = 20916467) B20916467
theorem B6195689 : Blo 1222929 6195689 := bstep (se 2 (by rfl) ⟨2323383, by rfl⟩ : syracuseStep 6195689 = 4646767) B4646767
theorem B8604251 : Blo 1222929 8604251 := bstep (se 1 (by rfl) ⟨6453188, by rfl⟩ : syracuseStep 8604251 = 12906377) B12906377
theorem B6965959 : Blo 1222929 6965959 := bstep (se 1 (by rfl) ⟨5224469, by rfl⟩ : syracuseStep 6965959 = 10448939) B10448939
theorem B13945769 : Blo 1222929 13945769 := bstep (se 2 (by rfl) ⟨5229663, by rfl⟩ : syracuseStep 13945769 = 10459327) B10459327
theorem B6196175 : Blo 1222929 6196175 := bstep (se 1 (by rfl) ⟨4647131, by rfl⟩ : syracuseStep 6196175 = 9294263) B9294263
theorem B1223771 : Blo 1222929 1223771 := bstep (se 1 (by rfl) ⟨917828, by rfl⟩ : syracuseStep 1223771 = 1835657) B1835657
theorem B17878315 : Blo 1222929 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B44633663 : Blo 1222929 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B12562087 : Blo 1222929 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B8818429 : Blo 1222929 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B6967691 : Blo 1222929 6967691 := bstep (se 1 (by rfl) ⟨5225768, by rfl⟩ : syracuseStep 6967691 = 10451537) B10451537
theorem B763026803 : Blo 1222929 763026803 := bstep (se 1 (by rfl) ⟨572270102, by rfl⟩ : syracuseStep 763026803 = 1144540205) B1144540205
theorem B20381057 : Blo 1222929 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B5963165 : Blo 1222929 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B2752127 : Blo 1222929 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B5881511 : Blo 1222929 5881511 := bstep (se 1 (by rfl) ⟨4411133, by rfl⟩ : syracuseStep 5881511 = 8822267) B8822267
theorem B5881663 : Blo 1222929 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B2236223 : Blo 1222929 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B1835003 : Blo 1222929 1835003 := bstep (se 1 (by rfl) ⟨1376252, by rfl⟩ : syracuseStep 1835003 = 2752505) B2752505
theorem B1376239 : Blo 1222929 1376239 := bstep (se 1 (by rfl) ⟨1032179, by rfl⟩ : syracuseStep 1376239 = 2064359) B2064359
theorem B4645127 : Blo 1222929 4645127 := bstep (se 1 (by rfl) ⟨3483845, by rfl⟩ : syracuseStep 4645127 = 6967691) B6967691
theorem B2752847 : Blo 1222929 2752847 := bstep (se 1 (by rfl) ⟨2064635, by rfl⟩ : syracuseStep 2752847 = 4129271) B4129271
theorem B2753657 : Blo 1222929 2753657 := bstep (se 2 (by rfl) ⟨1032621, by rfl⟩ : syracuseStep 2753657 = 2065243) B2065243
theorem B4130459 : Blo 1222929 4130459 := bstep (se 1 (by rfl) ⟨3097844, by rfl⟩ : syracuseStep 4130459 = 6195689) B6195689
theorem B5736167 : Blo 1222929 5736167 := bstep (se 1 (by rfl) ⟨4302125, by rfl⟩ : syracuseStep 5736167 = 8604251) B8604251
theorem B4130783 : Blo 1222929 4130783 := bstep (se 1 (by rfl) ⟨3098087, by rfl⟩ : syracuseStep 4130783 = 6196175) B6196175
theorem B508684535 : Blo 1222929 508684535 := bstep (se 1 (by rfl) ⟨381513401, by rfl⟩ : syracuseStep 508684535 = 763026803) B763026803
theorem B3975443 : Blo 1222929 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B11757905 : Blo 1222929 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B29755775 : Blo 1222929 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B7842217 : Blo 1222929 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1223335 : Blo 1222929 1223335 := bstep (se 1 (by rfl) ⟨917501, by rfl⟩ : syracuseStep 1223335 = 1835003) B1835003
theorem B1223375 : Blo 1222929 1223375 := bstep (se 1 (by rfl) ⟨917531, by rfl⟩ : syracuseStep 1223375 = 1835063) B1835063
theorem B1223419 : Blo 1222929 1223419 := bstep (se 1 (by rfl) ⟨917564, by rfl⟩ : syracuseStep 1223419 = 1835129) B1835129
theorem B1223551 : Blo 1222929 1223551 := bstep (se 1 (by rfl) ⟨917663, by rfl⟩ : syracuseStep 1223551 = 1835327) B1835327
theorem B1223663 : Blo 1222929 1223663 := bstep (se 1 (by rfl) ⟨917747, by rfl⟩ : syracuseStep 1223663 = 1835495) B1835495
theorem B4648043 : Blo 1222929 4648043 := bstep (se 1 (by rfl) ⟨3486032, by rfl⟩ : syracuseStep 4648043 = 6972065) B6972065
theorem B16749449 : Blo 1222929 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B13587371 : Blo 1222929 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B3921007 : Blo 1222929 3921007 := bstep (se 1 (by rfl) ⟨2940755, by rfl⟩ : syracuseStep 3921007 = 5881511) B5881511
theorem B9295721 : Blo 1222929 9295721 := bstep (se 2 (by rfl) ⟨3485895, by rfl⟩ : syracuseStep 9295721 = 6971791) B6971791
theorem B9287945 : Blo 1222929 9287945 := bstep (se 2 (by rfl) ⟨3482979, by rfl⟩ : syracuseStep 9287945 = 6965959) B6965959
theorem B9296207 : Blo 1222929 9296207 := bstep (se 1 (by rfl) ⟨6972155, by rfl⟩ : syracuseStep 9296207 = 13944311) B13944311
theorem B23837753 : Blo 1222929 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B9297179 : Blo 1222929 9297179 := bstep (se 1 (by rfl) ⟨6972884, by rfl⟩ : syracuseStep 9297179 = 13945769) B13945769
theorem B1834751 : Blo 1222929 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B1490815 : Blo 1222929 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B1834985 : Blo 1222929 1834985 := bstep (se 2 (by rfl) ⟨688119, by rfl⟩ : syracuseStep 1834985 = 1376239) B1376239
theorem B3096751 : Blo 1222929 3096751 := bstep (se 1 (by rfl) ⟨2322563, by rfl⟩ : syracuseStep 3096751 = 4645127) B4645127
theorem B1835231 : Blo 1222929 1835231 := bstep (se 1 (by rfl) ⟨1376423, by rfl⟩ : syracuseStep 1835231 = 2752847) B2752847
theorem B11166299 : Blo 1222929 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B1835771 : Blo 1222929 1835771 := bstep (se 1 (by rfl) ⟨1376828, by rfl⟩ : syracuseStep 1835771 = 2753657) B2753657
theorem B2753639 : Blo 1222929 2753639 := bstep (se 1 (by rfl) ⟨2065229, by rfl⟩ : syracuseStep 2753639 = 4130459) B4130459
theorem B2753855 : Blo 1222929 2753855 := bstep (se 1 (by rfl) ⟨2065391, by rfl⟩ : syracuseStep 2753855 = 4130783) B4130783
theorem B5228009 : Blo 1222929 5228009 := bstep (se 2 (by rfl) ⟨1960503, by rfl⟩ : syracuseStep 5228009 = 3921007) B3921007
theorem B3098695 : Blo 1222929 3098695 := bstep (se 1 (by rfl) ⟨2324021, by rfl⟩ : syracuseStep 3098695 = 4648043) B4648043
theorem B1223167 : Blo 1222929 1223167 := bstep (se 1 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 1223167 = 1834751) B1834751
theorem B1223323 : Blo 1222929 1223323 := bstep (se 1 (by rfl) ⟨917492, by rfl⟩ : syracuseStep 1223323 = 1834985) B1834985
theorem B10456289 : Blo 1222929 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B6197147 : Blo 1222929 6197147 := bstep (se 1 (by rfl) ⟨4647860, by rfl⟩ : syracuseStep 6197147 = 9295721) B9295721
theorem B2650295 : Blo 1222929 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B6197471 : Blo 1222929 6197471 := bstep (se 1 (by rfl) ⟨4648103, by rfl⟩ : syracuseStep 6197471 = 9296207) B9296207
theorem B19837183 : Blo 1222929 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B6198119 : Blo 1222929 6198119 := bstep (se 1 (by rfl) ⟨4648589, by rfl⟩ : syracuseStep 6198119 = 9297179) B9297179
theorem B1987753 : Blo 1222929 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B9058247 : Blo 1222929 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B3824111 : Blo 1222929 3824111 := bstep (se 1 (by rfl) ⟨2868083, by rfl⟩ : syracuseStep 3824111 = 5736167) B5736167
theorem B339123023 : Blo 1222929 339123023 := bstep (se 1 (by rfl) ⟨254342267, by rfl⟩ : syracuseStep 339123023 = 508684535) B508684535
theorem B6191963 : Blo 1222929 6191963 := bstep (se 1 (by rfl) ⟨4643972, by rfl⟩ : syracuseStep 6191963 = 9287945) B9287945
theorem B7838603 : Blo 1222929 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B15891835 : Blo 1222929 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B4129001 : Blo 1222929 4129001 := bstep (se 2 (by rfl) ⟨1548375, by rfl⟩ : syracuseStep 4129001 = 3096751) B3096751
theorem B1835759 : Blo 1222929 1835759 := bstep (se 1 (by rfl) ⟨1376819, by rfl⟩ : syracuseStep 1835759 = 2753639) B2753639
theorem B1835903 : Blo 1222929 1835903 := bstep (se 1 (by rfl) ⟨1376927, by rfl⟩ : syracuseStep 1835903 = 2753855) B2753855
theorem B6038831 : Blo 1222929 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B2549407 : Blo 1222929 2549407 := bstep (se 1 (by rfl) ⟨1912055, by rfl⟩ : syracuseStep 2549407 = 3824111) B3824111
theorem B4131431 : Blo 1222929 4131431 := bstep (se 1 (by rfl) ⟨3098573, by rfl⟩ : syracuseStep 4131431 = 6197147) B6197147
theorem B4131593 : Blo 1222929 4131593 := bstep (se 2 (by rfl) ⟨1549347, by rfl⟩ : syracuseStep 4131593 = 3098695) B3098695
theorem B1223487 : Blo 1222929 1223487 := bstep (se 1 (by rfl) ⟨917615, by rfl⟩ : syracuseStep 1223487 = 1835231) B1835231
theorem B4131647 : Blo 1222929 4131647 := bstep (se 1 (by rfl) ⟨3098735, by rfl⟩ : syracuseStep 4131647 = 6197471) B6197471
theorem B1223847 : Blo 1222929 1223847 := bstep (se 1 (by rfl) ⟨917885, by rfl⟩ : syracuseStep 1223847 = 1835771) B1835771
theorem B4132079 : Blo 1222929 4132079 := bstep (se 1 (by rfl) ⟨3099059, by rfl⟩ : syracuseStep 4132079 = 6198119) B6198119
theorem B3485339 : Blo 1222929 3485339 := bstep (se 1 (by rfl) ⟨2614004, by rfl⟩ : syracuseStep 3485339 = 5228009) B5228009
theorem B2650337 : Blo 1222929 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B21189113 : Blo 1222929 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B1766863 : Blo 1222929 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B26449577 : Blo 1222929 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B7444199 : Blo 1222929 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B226082015 : Blo 1222929 226082015 := bstep (se 1 (by rfl) ⟨169561511, by rfl⟩ : syracuseStep 226082015 = 339123023) B339123023
theorem B4127975 : Blo 1222929 4127975 := bstep (se 1 (by rfl) ⟨3095981, by rfl⟩ : syracuseStep 4127975 = 6191963) B6191963
theorem B5225735 : Blo 1222929 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B6970859 : Blo 1222929 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B2752667 : Blo 1222929 2752667 := bstep (se 1 (by rfl) ⟨2064500, by rfl⟩ : syracuseStep 2752667 = 4129001) B4129001
theorem B2754287 : Blo 1222929 2754287 := bstep (se 1 (by rfl) ⟨2065715, by rfl⟩ : syracuseStep 2754287 = 4131431) B4131431
theorem B2754395 : Blo 1222929 2754395 := bstep (se 1 (by rfl) ⟨2065796, by rfl⟩ : syracuseStep 2754395 = 4131593) B4131593
theorem B2754431 : Blo 1222929 2754431 := bstep (se 1 (by rfl) ⟨2065823, by rfl⟩ : syracuseStep 2754431 = 4131647) B4131647
theorem B2754719 : Blo 1222929 2754719 := bstep (se 1 (by rfl) ⟨2066039, by rfl⟩ : syracuseStep 2754719 = 4132079) B4132079
theorem B3483823 : Blo 1222929 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B4647239 : Blo 1222929 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B14126075 : Blo 1222929 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B1223839 : Blo 1222929 1223839 := bstep (se 1 (by rfl) ⟨917879, by rfl⟩ : syracuseStep 1223839 = 1835759) B1835759
theorem B1223935 : Blo 1222929 1223935 := bstep (se 1 (by rfl) ⟨917951, by rfl⟩ : syracuseStep 1223935 = 1835903) B1835903
theorem B17633051 : Blo 1222929 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B2355817 : Blo 1222929 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B150721343 : Blo 1222929 150721343 := bstep (se 1 (by rfl) ⟨113041007, by rfl⟩ : syracuseStep 150721343 = 226082015) B226082015
theorem B2323559 : Blo 1222929 2323559 := bstep (se 1 (by rfl) ⟨1742669, by rfl⟩ : syracuseStep 2323559 = 3485339) B3485339
theorem B1766891 : Blo 1222929 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B16103549 : Blo 1222929 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B4962799 : Blo 1222929 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B2751983 : Blo 1222929 2751983 := bstep (se 1 (by rfl) ⟨2063987, by rfl⟩ : syracuseStep 2751983 = 4127975) B4127975
theorem B3399209 : Blo 1222929 3399209 := bstep (se 2 (by rfl) ⟨1274703, by rfl⟩ : syracuseStep 3399209 = 2549407) B2549407
theorem B1835111 : Blo 1222929 1835111 := bstep (se 1 (by rfl) ⟨1376333, by rfl⟩ : syracuseStep 1835111 = 2752667) B2752667
theorem B4645097 : Blo 1222929 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B1549039 : Blo 1222929 1549039 := bstep (se 1 (by rfl) ⟨1161779, by rfl⟩ : syracuseStep 1549039 = 2323559) B2323559
theorem B1836191 : Blo 1222929 1836191 := bstep (se 1 (by rfl) ⟨1377143, by rfl⟩ : syracuseStep 1836191 = 2754287) B2754287
theorem B1836263 : Blo 1222929 1836263 := bstep (se 1 (by rfl) ⟨1377197, by rfl⟩ : syracuseStep 1836263 = 2754395) B2754395
theorem B1836287 : Blo 1222929 1836287 := bstep (se 1 (by rfl) ⟨1377215, by rfl⟩ : syracuseStep 1836287 = 2754431) B2754431
theorem B4711709 : Blo 1222929 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B1836479 : Blo 1222929 1836479 := bstep (se 1 (by rfl) ⟨1377359, by rfl⟩ : syracuseStep 1836479 = 2754719) B2754719
theorem B3098159 : Blo 1222929 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B3141089 : Blo 1222929 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B10735699 : Blo 1222929 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B9417383 : Blo 1222929 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B2266139 : Blo 1222929 2266139 := bstep (se 1 (by rfl) ⟨1699604, by rfl⟩ : syracuseStep 2266139 = 3399209) B3399209
theorem B100480895 : Blo 1222929 100480895 := bstep (se 1 (by rfl) ⟨75360671, by rfl⟩ : syracuseStep 100480895 = 150721343) B150721343
theorem B6617065 : Blo 1222929 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B1834655 : Blo 1222929 1834655 := bstep (se 1 (by rfl) ⟨1375991, by rfl⟩ : syracuseStep 1834655 = 2751983) B2751983
theorem B11755367 : Blo 1222929 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B3096731 : Blo 1222929 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B2065385 : Blo 1222929 2065385 := bstep (se 2 (by rfl) ⟨774519, by rfl⟩ : syracuseStep 2065385 = 1549039) B1549039
theorem B2065439 : Blo 1222929 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B66987263 : Blo 1222929 66987263 := bstep (se 1 (by rfl) ⟨50240447, by rfl⟩ : syracuseStep 66987263 = 100480895) B100480895
theorem B1223103 : Blo 1222929 1223103 := bstep (se 1 (by rfl) ⟨917327, by rfl⟩ : syracuseStep 1223103 = 1834655) B1834655
theorem B1223407 : Blo 1222929 1223407 := bstep (se 1 (by rfl) ⟨917555, by rfl⟩ : syracuseStep 1223407 = 1835111) B1835111
theorem B14314265 : Blo 1222929 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B6278255 : Blo 1222929 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B1510759 : Blo 1222929 1510759 := bstep (se 1 (by rfl) ⟨1133069, by rfl⟩ : syracuseStep 1510759 = 2266139) B2266139
theorem B1224127 : Blo 1222929 1224127 := bstep (se 1 (by rfl) ⟨918095, by rfl⟩ : syracuseStep 1224127 = 1836191) B1836191
theorem B1224175 : Blo 1222929 1224175 := bstep (se 1 (by rfl) ⟨918131, by rfl⟩ : syracuseStep 1224175 = 1836263) B1836263
theorem B1224191 : Blo 1222929 1224191 := bstep (se 1 (by rfl) ⟨918143, by rfl⟩ : syracuseStep 1224191 = 1836287) B1836287
theorem B1224319 : Blo 1222929 1224319 := bstep (se 1 (by rfl) ⟨918239, by rfl⟩ : syracuseStep 1224319 = 1836479) B1836479
theorem B2094059 : Blo 1222929 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B7836911 : Blo 1222929 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B12564557 : Blo 1222929 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B8822753 : Blo 1222929 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B2064487 : Blo 1222929 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B1376923 : Blo 1222929 1376923 := bstep (se 1 (by rfl) ⟨1032692, by rfl⟩ : syracuseStep 1376923 = 2065385) B2065385
theorem B1376959 : Blo 1222929 1376959 := bstep (se 1 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 1376959 = 2065439) B2065439
theorem B1396039 : Blo 1222929 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B44658175 : Blo 1222929 44658175 := bstep (se 1 (by rfl) ⟨33493631, by rfl⟩ : syracuseStep 44658175 = 66987263) B66987263
theorem B8376371 : Blo 1222929 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B5224607 : Blo 1222929 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B2014345 : Blo 1222929 2014345 := bstep (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) B1510759
theorem B9542843 : Blo 1222929 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B4185503 : Blo 1222929 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B5881835 : Blo 1222929 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B2752649 : Blo 1222929 2752649 := bstep (se 2 (by rfl) ⟨1032243, by rfl⟩ : syracuseStep 2752649 = 2064487) B2064487
theorem B1835897 : Blo 1222929 1835897 := bstep (se 2 (by rfl) ⟨688461, by rfl⟩ : syracuseStep 1835897 = 1376923) B1376923
theorem B1835945 : Blo 1222929 1835945 := bstep (se 2 (by rfl) ⟨688479, by rfl⟩ : syracuseStep 1835945 = 1376959) B1376959
theorem B3483071 : Blo 1222929 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B1861385 : Blo 1222929 1861385 := bstep (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) B1396039
theorem B59544233 : Blo 1222929 59544233 := bstep (se 2 (by rfl) ⟨22329087, by rfl⟩ : syracuseStep 59544233 = 44658175) B44658175
theorem B6361895 : Blo 1222929 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B2790335 : Blo 1222929 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B3921223 : Blo 1222929 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B5584247 : Blo 1222929 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B2685793 : Blo 1222929 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B1835099 : Blo 1222929 1835099 := bstep (se 1 (by rfl) ⟨1376324, by rfl⟩ : syracuseStep 1835099 = 2752649) B2752649
theorem B3581057 : Blo 1222929 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B5228297 : Blo 1222929 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B7440893 : Blo 1222929 7440893 := bstep (se 3 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 7440893 = 2790335) B2790335
theorem B1223931 : Blo 1222929 1223931 := bstep (se 1 (by rfl) ⟨917948, by rfl⟩ : syracuseStep 1223931 = 1835897) B1835897
theorem B1223963 : Blo 1222929 1223963 := bstep (se 1 (by rfl) ⟨917972, by rfl⟩ : syracuseStep 1223963 = 1835945) B1835945
theorem B3722831 : Blo 1222929 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B2322047 : Blo 1222929 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B39696155 : Blo 1222929 39696155 := bstep (se 1 (by rfl) ⟨29772116, by rfl⟩ : syracuseStep 39696155 = 59544233) B59544233
theorem B4241263 : Blo 1222929 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B4963693 : Blo 1222929 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B5655017 : Blo 1222929 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B1223399 : Blo 1222929 1223399 := bstep (se 1 (by rfl) ⟨917549, by rfl⟩ : syracuseStep 1223399 = 1835099) B1835099
theorem B3485531 : Blo 1222929 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B26464103 : Blo 1222929 26464103 := bstep (se 1 (by rfl) ⟨19848077, by rfl⟩ : syracuseStep 26464103 = 39696155) B39696155
theorem B4960595 : Blo 1222929 4960595 := bstep (se 1 (by rfl) ⟨3720446, by rfl⟩ : syracuseStep 4960595 = 7440893) B7440893
theorem B9549485 : Blo 1222929 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B6192125 : Blo 1222929 6192125 := bstep (se 3 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 6192125 = 2322047) B2322047
theorem B6618257 : Blo 1222929 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B2481887 : Blo 1222929 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B6366323 : Blo 1222929 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B3770011 : Blo 1222929 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B4412171 : Blo 1222929 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B9294749 : Blo 1222929 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B17642735 : Blo 1222929 17642735 := bstep (se 1 (by rfl) ⟨13232051, by rfl⟩ : syracuseStep 17642735 = 26464103) B26464103
theorem B3307063 : Blo 1222929 3307063 := bstep (se 1 (by rfl) ⟨2480297, by rfl⟩ : syracuseStep 3307063 = 4960595) B4960595
theorem B4128083 : Blo 1222929 4128083 := bstep (se 1 (by rfl) ⟨3096062, by rfl⟩ : syracuseStep 4128083 = 6192125) B6192125
theorem B1654591 : Blo 1222929 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B2941447 : Blo 1222929 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B4409417 : Blo 1222929 4409417 := bstep (se 2 (by rfl) ⟨1653531, by rfl⟩ : syracuseStep 4409417 = 3307063) B3307063
theorem B2206121 : Blo 1222929 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B16976861 : Blo 1222929 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B6196499 : Blo 1222929 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B5026681 : Blo 1222929 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B11761823 : Blo 1222929 11761823 := bstep (se 1 (by rfl) ⟨8821367, by rfl⟩ : syracuseStep 11761823 = 17642735) B17642735
theorem B2752055 : Blo 1222929 2752055 := bstep (se 1 (by rfl) ⟨2064041, by rfl⟩ : syracuseStep 2752055 = 4128083) B4128083
theorem B5882989 : Blo 1222929 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B7841215 : Blo 1222929 7841215 := bstep (se 1 (by rfl) ⟨5880911, by rfl⟩ : syracuseStep 7841215 = 11761823) B11761823
theorem B4130999 : Blo 1222929 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B26808965 : Blo 1222929 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B11317907 : Blo 1222929 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B3921929 : Blo 1222929 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B2939611 : Blo 1222929 2939611 := bstep (se 1 (by rfl) ⟨2204708, by rfl⟩ : syracuseStep 2939611 = 4409417) B4409417
theorem B1834703 : Blo 1222929 1834703 := bstep (se 1 (by rfl) ⟨1376027, by rfl⟩ : syracuseStep 1834703 = 2752055) B2752055
theorem B7545271 : Blo 1222929 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B2614619 : Blo 1222929 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B2753999 : Blo 1222929 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B10454953 : Blo 1222929 10454953 := bstep (se 2 (by rfl) ⟨3920607, by rfl⟩ : syracuseStep 10454953 = 7841215) B7841215
theorem B1223135 : Blo 1222929 1223135 := bstep (se 1 (by rfl) ⟨917351, by rfl⟩ : syracuseStep 1223135 = 1834703) B1834703
theorem B3919481 : Blo 1222929 3919481 := bstep (se 2 (by rfl) ⟨1469805, by rfl⟩ : syracuseStep 3919481 = 2939611) B2939611
theorem B7843985 : Blo 1222929 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B17872643 : Blo 1222929 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B10060361 : Blo 1222929 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B6972317 : Blo 1222929 6972317 := bstep (se 3 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 6972317 = 2614619) B2614619
theorem B1835999 : Blo 1222929 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B5229323 : Blo 1222929 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B11915095 : Blo 1222929 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B13939937 : Blo 1222929 13939937 := bstep (se 2 (by rfl) ⟨5227476, by rfl⟩ : syracuseStep 13939937 = 10454953) B10454953
theorem B2612987 : Blo 1222929 2612987 := bstep (se 1 (by rfl) ⟨1959740, by rfl⟩ : syracuseStep 2612987 = 3919481) B3919481
theorem B15886793 : Blo 1222929 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B4648211 : Blo 1222929 4648211 := bstep (se 1 (by rfl) ⟨3486158, by rfl⟩ : syracuseStep 4648211 = 6972317) B6972317
theorem B1223999 : Blo 1222929 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B9293291 : Blo 1222929 9293291 := bstep (se 1 (by rfl) ⟨6969968, by rfl⟩ : syracuseStep 9293291 = 13939937) B13939937
theorem B3486215 : Blo 1222929 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B1741991 : Blo 1222929 1741991 := bstep (se 1 (by rfl) ⟨1306493, by rfl⟩ : syracuseStep 1741991 = 2612987) B2612987
theorem B6706907 : Blo 1222929 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B4645309 : Blo 1222929 4645309 := bstep (se 3 (by rfl) ⟨870995, by rfl⟩ : syracuseStep 4645309 = 1741991) B1741991
theorem B3098807 : Blo 1222929 3098807 := bstep (se 1 (by rfl) ⟨2324105, by rfl⟩ : syracuseStep 3098807 = 4648211) B4648211
theorem B6195527 : Blo 1222929 6195527 := bstep (se 1 (by rfl) ⟨4646645, by rfl⟩ : syracuseStep 6195527 = 9293291) B9293291
theorem B2324143 : Blo 1222929 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B4471271 : Blo 1222929 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B10591195 : Blo 1222929 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B6193745 : Blo 1222929 6193745 := bstep (se 2 (by rfl) ⟨2322654, by rfl⟩ : syracuseStep 6193745 = 4645309) B4645309
theorem B2065871 : Blo 1222929 2065871 := bstep (se 1 (by rfl) ⟨1549403, by rfl⟩ : syracuseStep 2065871 = 3098807) B3098807
theorem B4130351 : Blo 1222929 4130351 := bstep (se 1 (by rfl) ⟨3097763, by rfl⟩ : syracuseStep 4130351 = 6195527) B6195527
theorem B3098857 : Blo 1222929 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B14121593 : Blo 1222929 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B2980847 : Blo 1222929 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B4129163 : Blo 1222929 4129163 := bstep (se 1 (by rfl) ⟨3096872, by rfl⟩ : syracuseStep 4129163 = 6193745) B6193745
theorem B1377247 : Blo 1222929 1377247 := bstep (se 1 (by rfl) ⟨1032935, by rfl⟩ : syracuseStep 1377247 = 2065871) B2065871
theorem B2753567 : Blo 1222929 2753567 := bstep (se 1 (by rfl) ⟨2065175, by rfl⟩ : syracuseStep 2753567 = 4130351) B4130351
theorem B9414395 : Blo 1222929 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B4131809 : Blo 1222929 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B1987231 : Blo 1222929 1987231 := bstep (se 1 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 1987231 = 2980847) B2980847
theorem B2752775 : Blo 1222929 2752775 := bstep (se 1 (by rfl) ⟨2064581, by rfl⟩ : syracuseStep 2752775 = 4129163) B4129163
theorem B42394261 : Blo 1222929 42394261 := bstep (se 6 (by rfl) ⟨993615, by rfl⟩ : syracuseStep 42394261 = 1987231) B1987231
theorem B1835711 : Blo 1222929 1835711 := bstep (se 1 (by rfl) ⟨1376783, by rfl⟩ : syracuseStep 1835711 = 2753567) B2753567
theorem B6276263 : Blo 1222929 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B1836329 : Blo 1222929 1836329 := bstep (se 2 (by rfl) ⟨688623, by rfl⟩ : syracuseStep 1836329 = 1377247) B1377247
theorem B2754539 : Blo 1222929 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B1835183 : Blo 1222929 1835183 := bstep (se 1 (by rfl) ⟨1376387, by rfl⟩ : syracuseStep 1835183 = 2752775) B2752775
theorem B16736701 : Blo 1222929 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B56525681 : Blo 1222929 56525681 := bstep (se 2 (by rfl) ⟨21197130, by rfl⟩ : syracuseStep 56525681 = 42394261) B42394261
theorem B1836359 : Blo 1222929 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B1223807 : Blo 1222929 1223807 := bstep (se 1 (by rfl) ⟨917855, by rfl⟩ : syracuseStep 1223807 = 1835711) B1835711
theorem B1224219 : Blo 1222929 1224219 := bstep (se 1 (by rfl) ⟨918164, by rfl⟩ : syracuseStep 1224219 = 1836329) B1836329
theorem B37683787 : Blo 1222929 37683787 := bstep (se 1 (by rfl) ⟨28262840, by rfl⟩ : syracuseStep 37683787 = 56525681) B56525681
theorem B22315601 : Blo 1222929 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B1223455 : Blo 1222929 1223455 := bstep (se 1 (by rfl) ⟨917591, by rfl⟩ : syracuseStep 1223455 = 1835183) B1835183
theorem B1224239 : Blo 1222929 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B14877067 : Blo 1222929 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B50245049 : Blo 1222929 50245049 := bstep (se 2 (by rfl) ⟨18841893, by rfl⟩ : syracuseStep 50245049 = 37683787) B37683787
theorem B19836089 : Blo 1222929 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B133986797 : Blo 1222929 133986797 := bstep (se 3 (by rfl) ⟨25122524, by rfl⟩ : syracuseStep 133986797 = 50245049) B50245049
theorem B13224059 : Blo 1222929 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B89324531 : Blo 1222929 89324531 := bstep (se 1 (by rfl) ⟨66993398, by rfl⟩ : syracuseStep 89324531 = 133986797) B133986797
theorem B8816039 : Blo 1222929 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B59549687 : Blo 1222929 59549687 := bstep (se 1 (by rfl) ⟨44662265, by rfl⟩ : syracuseStep 59549687 = 89324531) B89324531
theorem B39699791 : Blo 1222929 39699791 := bstep (se 1 (by rfl) ⟨29774843, by rfl⟩ : syracuseStep 39699791 = 59549687) B59549687
theorem B5877359 : Blo 1222929 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B3918239 : Blo 1222929 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B26466527 : Blo 1222929 26466527 := bstep (se 1 (by rfl) ⟨19849895, by rfl⟩ : syracuseStep 26466527 = 39699791) B39699791
theorem B17644351 : Blo 1222929 17644351 := bstep (se 1 (by rfl) ⟨13233263, by rfl⟩ : syracuseStep 17644351 = 26466527) B26466527
theorem B2612159 : Blo 1222929 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B1741439 : Blo 1222929 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B23525801 : Blo 1222929 23525801 := bstep (se 2 (by rfl) ⟨8822175, by rfl⟩ : syracuseStep 23525801 = 17644351) B17644351
theorem B15683867 : Blo 1222929 15683867 := bstep (se 1 (by rfl) ⟨11762900, by rfl⟩ : syracuseStep 15683867 = 23525801) B23525801
theorem B4643837 : Blo 1222929 4643837 := bstep (se 3 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 4643837 = 1741439) B1741439
theorem B10455911 : Blo 1222929 10455911 := bstep (se 1 (by rfl) ⟨7841933, by rfl⟩ : syracuseStep 10455911 = 15683867) B15683867
theorem B3095891 : Blo 1222929 3095891 := bstep (se 1 (by rfl) ⟨2321918, by rfl⟩ : syracuseStep 3095891 = 4643837) B4643837
theorem B6970607 : Blo 1222929 6970607 := bstep (se 1 (by rfl) ⟨5227955, by rfl⟩ : syracuseStep 6970607 = 10455911) B10455911
theorem B2063927 : Blo 1222929 2063927 := bstep (se 1 (by rfl) ⟨1547945, by rfl⟩ : syracuseStep 2063927 = 3095891) B3095891
theorem B4647071 : Blo 1222929 4647071 := bstep (se 1 (by rfl) ⟨3485303, by rfl⟩ : syracuseStep 4647071 = 6970607) B6970607
theorem B1375951 : Blo 1222929 1375951 := bstep (se 1 (by rfl) ⟨1031963, by rfl⟩ : syracuseStep 1375951 = 2063927) B2063927
theorem B3098047 : Blo 1222929 3098047 := bstep (se 1 (by rfl) ⟨2323535, by rfl⟩ : syracuseStep 3098047 = 4647071) B4647071
theorem B1834601 : Blo 1222929 1834601 := bstep (se 2 (by rfl) ⟨687975, by rfl⟩ : syracuseStep 1834601 = 1375951) B1375951
theorem B4130729 : Blo 1222929 4130729 := bstep (se 2 (by rfl) ⟨1549023, by rfl⟩ : syracuseStep 4130729 = 3098047) B3098047
theorem B1223067 : Blo 1222929 1223067 := bstep (se 1 (by rfl) ⟨917300, by rfl⟩ : syracuseStep 1223067 = 1834601) B1834601
theorem B2753819 : Blo 1222929 2753819 := bstep (se 1 (by rfl) ⟨2065364, by rfl⟩ : syracuseStep 2753819 = 4130729) B4130729
theorem B1835879 : Blo 1222929 1835879 := bstep (se 1 (by rfl) ⟨1376909, by rfl⟩ : syracuseStep 1835879 = 2753819) B2753819
theorem B1223919 : Blo 1222929 1223919 := bstep (se 1 (by rfl) ⟨917939, by rfl⟩ : syracuseStep 1223919 = 1835879) B1835879

theorem C0 (j : ℕ) (h1 : 305732 ≤ j) (h2 : j ≤ 306106) : Blo 1222929 (4 * j + 3) := by
  interval_cases j
  · exact B1222931
  · exact B1222935
  · exact B1222939
  · exact B1222943
  · exact B1222947
  · exact B1222951
  · exact B1222955
  · exact B1222959
  · exact B1222963
  · exact B1222967
  · exact B1222971
  · exact B1222975
  · exact B1222979
  · exact B1222983
  · exact B1222987
  · exact B1222991
  · exact B1222995
  · exact B1222999
  · exact B1223003
  · exact B1223007
  · exact B1223011
  · exact B1223015
  · exact B1223019
  · exact B1223023
  · exact B1223027
  · exact B1223031
  · exact B1223035
  · exact B1223039
  · exact B1223043
  · exact B1223047
  · exact B1223051
  · exact B1223055
  · exact B1223059
  · exact B1223063
  · exact B1223067
  · exact B1223071
  · exact B1223075
  · exact B1223079
  · exact B1223083
  · exact B1223087
  · exact B1223091
  · exact B1223095
  · exact B1223099
  · exact B1223103
  · exact B1223107
  · exact B1223111
  · exact B1223115
  · exact B1223119
  · exact B1223123
  · exact B1223127
  · exact B1223131
  · exact B1223135
  · exact B1223139
  · exact B1223143
  · exact B1223147
  · exact B1223151
  · exact B1223155
  · exact B1223159
  · exact B1223163
  · exact B1223167
  · exact B1223171
  · exact B1223175
  · exact B1223179
  · exact B1223183
  · exact B1223187
  · exact B1223191
  · exact B1223195
  · exact B1223199
  · exact B1223203
  · exact B1223207
  · exact B1223211
  · exact B1223215
  · exact B1223219
  · exact B1223223
  · exact B1223227
  · exact B1223231
  · exact B1223235
  · exact B1223239
  · exact B1223243
  · exact B1223247
  · exact B1223251
  · exact B1223255
  · exact B1223259
  · exact B1223263
  · exact B1223267
  · exact B1223271
  · exact B1223275
  · exact B1223279
  · exact B1223283
  · exact B1223287
  · exact B1223291
  · exact B1223295
  · exact B1223299
  · exact B1223303
  · exact B1223307
  · exact B1223311
  · exact B1223315
  · exact B1223319
  · exact B1223323
  · exact B1223327
  · exact B1223331
  · exact B1223335
  · exact B1223339
  · exact B1223343
  · exact B1223347
  · exact B1223351
  · exact B1223355
  · exact B1223359
  · exact B1223363
  · exact B1223367
  · exact B1223371
  · exact B1223375
  · exact B1223379
  · exact B1223383
  · exact B1223387
  · exact B1223391
  · exact B1223395
  · exact B1223399
  · exact B1223403
  · exact B1223407
  · exact B1223411
  · exact B1223415
  · exact B1223419
  · exact B1223423
  · exact B1223427
  · exact B1223431
  · exact B1223435
  · exact B1223439
  · exact B1223443
  · exact B1223447
  · exact B1223451
  · exact B1223455
  · exact B1223459
  · exact B1223463
  · exact B1223467
  · exact B1223471
  · exact B1223475
  · exact B1223479
  · exact B1223483
  · exact B1223487
  · exact B1223491
  · exact B1223495
  · exact B1223499
  · exact B1223503
  · exact B1223507
  · exact B1223511
  · exact B1223515
  · exact B1223519
  · exact B1223523
  · exact B1223527
  · exact B1223531
  · exact B1223535
  · exact B1223539
  · exact B1223543
  · exact B1223547
  · exact B1223551
  · exact B1223555
  · exact B1223559
  · exact B1223563
  · exact B1223567
  · exact B1223571
  · exact B1223575
  · exact B1223579
  · exact B1223583
  · exact B1223587
  · exact B1223591
  · exact B1223595
  · exact B1223599
  · exact B1223603
  · exact B1223607
  · exact B1223611
  · exact B1223615
  · exact B1223619
  · exact B1223623
  · exact B1223627
  · exact B1223631
  · exact B1223635
  · exact B1223639
  · exact B1223643
  · exact B1223647
  · exact B1223651
  · exact B1223655
  · exact B1223659
  · exact B1223663
  · exact B1223667
  · exact B1223671
  · exact B1223675
  · exact B1223679
  · exact B1223683
  · exact B1223687
  · exact B1223691
  · exact B1223695
  · exact B1223699
  · exact B1223703
  · exact B1223707
  · exact B1223711
  · exact B1223715
  · exact B1223719
  · exact B1223723
  · exact B1223727
  · exact B1223731
  · exact B1223735
  · exact B1223739
  · exact B1223743
  · exact B1223747
  · exact B1223751
  · exact B1223755
  · exact B1223759
  · exact B1223763
  · exact B1223767
  · exact B1223771
  · exact B1223775
  · exact B1223779
  · exact B1223783
  · exact B1223787
  · exact B1223791
  · exact B1223795
  · exact B1223799
  · exact B1223803
  · exact B1223807
  · exact B1223811
  · exact B1223815
  · exact B1223819
  · exact B1223823
  · exact B1223827
  · exact B1223831
  · exact B1223835
  · exact B1223839
  · exact B1223843
  · exact B1223847
  · exact B1223851
  · exact B1223855
  · exact B1223859
  · exact B1223863
  · exact B1223867
  · exact B1223871
  · exact B1223875
  · exact B1223879
  · exact B1223883
  · exact B1223887
  · exact B1223891
  · exact B1223895
  · exact B1223899
  · exact B1223903
  · exact B1223907
  · exact B1223911
  · exact B1223915
  · exact B1223919
  · exact B1223923
  · exact B1223927
  · exact B1223931
  · exact B1223935
  · exact B1223939
  · exact B1223943
  · exact B1223947
  · exact B1223951
  · exact B1223955
  · exact B1223959
  · exact B1223963
  · exact B1223967
  · exact B1223971
  · exact B1223975
  · exact B1223979
  · exact B1223983
  · exact B1223987
  · exact B1223991
  · exact B1223995
  · exact B1223999
  · exact B1224003
  · exact B1224007
  · exact B1224011
  · exact B1224015
  · exact B1224019
  · exact B1224023
  · exact B1224027
  · exact B1224031
  · exact B1224035
  · exact B1224039
  · exact B1224043
  · exact B1224047
  · exact B1224051
  · exact B1224055
  · exact B1224059
  · exact B1224063
  · exact B1224067
  · exact B1224071
  · exact B1224075
  · exact B1224079
  · exact B1224083
  · exact B1224087
  · exact B1224091
  · exact B1224095
  · exact B1224099
  · exact B1224103
  · exact B1224107
  · exact B1224111
  · exact B1224115
  · exact B1224119
  · exact B1224123
  · exact B1224127
  · exact B1224131
  · exact B1224135
  · exact B1224139
  · exact B1224143
  · exact B1224147
  · exact B1224151
  · exact B1224155
  · exact B1224159
  · exact B1224163
  · exact B1224167
  · exact B1224171
  · exact B1224175
  · exact B1224179
  · exact B1224183
  · exact B1224187
  · exact B1224191
  · exact B1224195
  · exact B1224199
  · exact B1224203
  · exact B1224207
  · exact B1224211
  · exact B1224215
  · exact B1224219
  · exact B1224223
  · exact B1224227
  · exact B1224231
  · exact B1224235
  · exact B1224239
  · exact B1224243
  · exact B1224247
  · exact B1224251
  · exact B1224255
  · exact B1224259
  · exact B1224263
  · exact B1224267
  · exact B1224271
  · exact B1224275
  · exact B1224279
  · exact B1224283
  · exact B1224287
  · exact B1224291
  · exact B1224295
  · exact B1224299
  · exact B1224303
  · exact B1224307
  · exact B1224311
  · exact B1224315
  · exact B1224319
  · exact B1224323
  · exact B1224327
  · exact B1224331
  · exact B1224335
  · exact B1224339
  · exact B1224343
  · exact B1224347
  · exact B1224351
  · exact B1224355
  · exact B1224359
  · exact B1224363
  · exact B1224367
  · exact B1224371
  · exact B1224375
  · exact B1224379
  · exact B1224383
  · exact B1224387
  · exact B1224391
  · exact B1224395
  · exact B1224399
  · exact B1224403
  · exact B1224407
  · exact B1224411
  · exact B1224415
  · exact B1224419
  · exact B1224423
  · exact B1224427

theorem solution (m : ℕ) (hlo : 1222929 ≤ m) (hhi : m ≤ 1224429) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 305732 ≤ j := by omega
    have hj2 : j ≤ 306106 := by omega
    have hb : Blo 1222929 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
