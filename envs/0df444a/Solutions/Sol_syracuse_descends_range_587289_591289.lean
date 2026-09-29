-- Prove2me | solution 1 for syracuse_descends_range_587289_591289
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:25.640701+00:00
-- url     : https://prove2.me/submissions/831e3f98-ad8c-431a-a48d-d2f60357112e

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


theorem B884741 : Blo 587289 884741 := bbase (se 4 (by rfl) ⟨82944, by rfl⟩ : syracuseStep 884741 = 165889) (by norm_num)
theorem B884765 : Blo 587289 884765 := bbase (se 3 (by rfl) ⟨165893, by rfl⟩ : syracuseStep 884765 = 331787) (by norm_num)
theorem B884789 : Blo 587289 884789 := bbase (se 5 (by rfl) ⟨41474, by rfl⟩ : syracuseStep 884789 = 82949) (by norm_num)
theorem B884813 : Blo 587289 884813 := bbase (se 3 (by rfl) ⟨165902, by rfl⟩ : syracuseStep 884813 = 331805) (by norm_num)
theorem B884837 : Blo 587289 884837 := bbase (se 4 (by rfl) ⟨82953, by rfl⟩ : syracuseStep 884837 = 165907) (by norm_num)
theorem B884861 : Blo 587289 884861 := bbase (se 3 (by rfl) ⟨165911, by rfl⟩ : syracuseStep 884861 = 331823) (by norm_num)
theorem B884885 : Blo 587289 884885 := bbase (se 6 (by rfl) ⟨20739, by rfl⟩ : syracuseStep 884885 = 41479) (by norm_num)
theorem B884909 : Blo 587289 884909 := bbase (se 3 (by rfl) ⟨165920, by rfl⟩ : syracuseStep 884909 = 331841) (by norm_num)
theorem B884933 : Blo 587289 884933 := bbase (se 4 (by rfl) ⟨82962, by rfl⟩ : syracuseStep 884933 = 165925) (by norm_num)
theorem B884957 : Blo 587289 884957 := bbase (se 3 (by rfl) ⟨165929, by rfl⟩ : syracuseStep 884957 = 331859) (by norm_num)
theorem B884981 : Blo 587289 884981 := bbase (se 5 (by rfl) ⟨41483, by rfl⟩ : syracuseStep 884981 = 82967) (by norm_num)
theorem B885005 : Blo 587289 885005 := bbase (se 3 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 885005 = 331877) (by norm_num)
theorem B885029 : Blo 587289 885029 := bbase (se 4 (by rfl) ⟨82971, by rfl⟩ : syracuseStep 885029 = 165943) (by norm_num)
theorem B885053 : Blo 587289 885053 := bbase (se 3 (by rfl) ⟨165947, by rfl⟩ : syracuseStep 885053 = 331895) (by norm_num)
theorem B885077 : Blo 587289 885077 := bbase (se 10 (by rfl) ⟨1296, by rfl⟩ : syracuseStep 885077 = 2593) (by norm_num)
theorem B885101 : Blo 587289 885101 := bbase (se 3 (by rfl) ⟨165956, by rfl⟩ : syracuseStep 885101 = 331913) (by norm_num)
theorem B2130293 : Blo 587289 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B885125 : Blo 587289 885125 := bbase (se 4 (by rfl) ⟨82980, by rfl⟩ : syracuseStep 885125 = 165961) (by norm_num)
theorem B885149 : Blo 587289 885149 := bbase (se 3 (by rfl) ⟨165965, by rfl⟩ : syracuseStep 885149 = 331931) (by norm_num)
theorem B885173 : Blo 587289 885173 := bbase (se 5 (by rfl) ⟨41492, by rfl⟩ : syracuseStep 885173 = 82985) (by norm_num)
theorem B885197 : Blo 587289 885197 := bbase (se 3 (by rfl) ⟨165974, by rfl⟩ : syracuseStep 885197 = 331949) (by norm_num)
theorem B885221 : Blo 587289 885221 := bbase (se 4 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 885221 = 165979) (by norm_num)
theorem B885245 : Blo 587289 885245 := bbase (se 3 (by rfl) ⟨165983, by rfl⟩ : syracuseStep 885245 = 331967) (by norm_num)
theorem B885269 : Blo 587289 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B885293 : Blo 587289 885293 := bbase (se 3 (by rfl) ⟨165992, by rfl⟩ : syracuseStep 885293 = 331985) (by norm_num)
theorem B885317 : Blo 587289 885317 := bbase (se 4 (by rfl) ⟨82998, by rfl⟩ : syracuseStep 885317 = 165997) (by norm_num)
theorem B885341 : Blo 587289 885341 := bbase (se 3 (by rfl) ⟨166001, by rfl⟩ : syracuseStep 885341 = 332003) (by norm_num)
theorem B1344109 : Blo 587289 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B885365 : Blo 587289 885365 := bbase (se 5 (by rfl) ⟨41501, by rfl⟩ : syracuseStep 885365 = 83003) (by norm_num)
theorem B885389 : Blo 587289 885389 := bbase (se 3 (by rfl) ⟨166010, by rfl⟩ : syracuseStep 885389 = 332021) (by norm_num)
theorem B885413 : Blo 587289 885413 := bbase (se 4 (by rfl) ⟨83007, by rfl⟩ : syracuseStep 885413 = 166015) (by norm_num)
theorem B2982581 : Blo 587289 2982581 := bbase (se 5 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 2982581 = 279617) (by norm_num)
theorem B885437 : Blo 587289 885437 := bbase (se 3 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 885437 = 332039) (by norm_num)
theorem B3572437 : Blo 587289 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B885461 : Blo 587289 885461 := bbase (se 7 (by rfl) ⟨10376, by rfl⟩ : syracuseStep 885461 = 20753) (by norm_num)
theorem B885485 : Blo 587289 885485 := bbase (se 3 (by rfl) ⟨166028, by rfl⟩ : syracuseStep 885485 = 332057) (by norm_num)
theorem B885509 : Blo 587289 885509 := bbase (se 4 (by rfl) ⟨83016, by rfl⟩ : syracuseStep 885509 = 166033) (by norm_num)
theorem B885533 : Blo 587289 885533 := bbase (se 3 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 885533 = 332075) (by norm_num)
theorem B885557 : Blo 587289 885557 := bbase (se 5 (by rfl) ⟨41510, by rfl⟩ : syracuseStep 885557 = 83021) (by norm_num)
theorem B885581 : Blo 587289 885581 := bbase (se 3 (by rfl) ⟨166046, by rfl⟩ : syracuseStep 885581 = 332093) (by norm_num)
theorem B885605 : Blo 587289 885605 := bbase (se 4 (by rfl) ⟨83025, by rfl⟩ : syracuseStep 885605 = 166051) (by norm_num)
theorem B885629 : Blo 587289 885629 := bbase (se 3 (by rfl) ⟨166055, by rfl⟩ : syracuseStep 885629 = 332111) (by norm_num)
theorem B1115021 : Blo 587289 1115021 := bbase (se 3 (by rfl) ⟨209066, by rfl⟩ : syracuseStep 1115021 = 418133) (by norm_num)
theorem B885653 : Blo 587289 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B885677 : Blo 587289 885677 := bbase (se 3 (by rfl) ⟨166064, by rfl⟩ : syracuseStep 885677 = 332129) (by norm_num)
theorem B1213373 : Blo 587289 1213373 := bbase (se 3 (by rfl) ⟨227507, by rfl⟩ : syracuseStep 1213373 = 455015) (by norm_num)
theorem B885701 : Blo 587289 885701 := bbase (se 4 (by rfl) ⟨83034, by rfl⟩ : syracuseStep 885701 = 166069) (by norm_num)
theorem B885725 : Blo 587289 885725 := bbase (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) (by norm_num)
theorem B885749 : Blo 587289 885749 := bbase (se 5 (by rfl) ⟨41519, by rfl⟩ : syracuseStep 885749 = 83039) (by norm_num)
theorem B885773 : Blo 587289 885773 := bbase (se 3 (by rfl) ⟨166082, by rfl⟩ : syracuseStep 885773 = 332165) (by norm_num)
theorem B885797 : Blo 587289 885797 := bbase (se 4 (by rfl) ⟨83043, by rfl⟩ : syracuseStep 885797 = 166087) (by norm_num)
theorem B885821 : Blo 587289 885821 := bbase (se 3 (by rfl) ⟨166091, by rfl⟩ : syracuseStep 885821 = 332183) (by norm_num)
theorem B2688085 : Blo 587289 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B885845 : Blo 587289 885845 := bbase (se 8 (by rfl) ⟨5190, by rfl⟩ : syracuseStep 885845 = 10381) (by norm_num)
theorem B885869 : Blo 587289 885869 := bbase (se 3 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 885869 = 332201) (by norm_num)
theorem B2524277 : Blo 587289 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B885893 : Blo 587289 885893 := bbase (se 4 (by rfl) ⟨83052, by rfl⟩ : syracuseStep 885893 = 166105) (by norm_num)
theorem B885917 : Blo 587289 885917 := bbase (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) (by norm_num)
theorem B1115309 : Blo 587289 1115309 := bbase (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) (by norm_num)
theorem B885941 : Blo 587289 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B885965 : Blo 587289 885965 := bbase (se 3 (by rfl) ⟨166118, by rfl⟩ : syracuseStep 885965 = 332237) (by norm_num)
theorem B885989 : Blo 587289 885989 := bbase (se 4 (by rfl) ⟨83061, by rfl⟩ : syracuseStep 885989 = 166123) (by norm_num)
theorem B886013 : Blo 587289 886013 := bbase (se 3 (by rfl) ⟨166127, by rfl⟩ : syracuseStep 886013 = 332255) (by norm_num)
theorem B886037 : Blo 587289 886037 := bbase (se 6 (by rfl) ⟨20766, by rfl⟩ : syracuseStep 886037 = 41533) (by norm_num)
theorem B886061 : Blo 587289 886061 := bbase (se 3 (by rfl) ⟨166136, by rfl⟩ : syracuseStep 886061 = 332273) (by norm_num)
theorem B1115461 : Blo 587289 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B886085 : Blo 587289 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B886109 : Blo 587289 886109 := bbase (se 3 (by rfl) ⟨166145, by rfl⟩ : syracuseStep 886109 = 332291) (by norm_num)
theorem B2524517 : Blo 587289 2524517 := bbase (se 4 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 2524517 = 473347) (by norm_num)
theorem B886133 : Blo 587289 886133 := bbase (se 5 (by rfl) ⟨41537, by rfl⟩ : syracuseStep 886133 = 83075) (by norm_num)
theorem B886157 : Blo 587289 886157 := bbase (se 3 (by rfl) ⟨166154, by rfl⟩ : syracuseStep 886157 = 332309) (by norm_num)
theorem B886181 : Blo 587289 886181 := bbase (se 4 (by rfl) ⟨83079, by rfl⟩ : syracuseStep 886181 = 166159) (by norm_num)
theorem B886205 : Blo 587289 886205 := bbase (se 3 (by rfl) ⟨166163, by rfl⟩ : syracuseStep 886205 = 332327) (by norm_num)
theorem B1672645 : Blo 587289 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B886229 : Blo 587289 886229 := bbase (se 7 (by rfl) ⟨10385, by rfl⟩ : syracuseStep 886229 = 20771) (by norm_num)
theorem B755173 : Blo 587289 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1050085 : Blo 587289 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B1705445 : Blo 587289 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B886253 : Blo 587289 886253 := bbase (se 3 (by rfl) ⟨166172, by rfl⟩ : syracuseStep 886253 = 332345) (by norm_num)
theorem B886277 : Blo 587289 886277 := bbase (se 4 (by rfl) ⟨83088, by rfl⟩ : syracuseStep 886277 = 166177) (by norm_num)
theorem B886301 : Blo 587289 886301 := bbase (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) (by norm_num)
theorem B886325 : Blo 587289 886325 := bbase (se 5 (by rfl) ⟨41546, by rfl⟩ : syracuseStep 886325 = 83093) (by norm_num)
theorem B886349 : Blo 587289 886349 := bbase (se 3 (by rfl) ⟨166190, by rfl⟩ : syracuseStep 886349 = 332381) (by norm_num)
theorem B1672805 : Blo 587289 1672805 := bbase (se 4 (by rfl) ⟨156825, by rfl⟩ : syracuseStep 1672805 = 313651) (by norm_num)
theorem B886373 : Blo 587289 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B788077 : Blo 587289 788077 := bbase (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) (by norm_num)
theorem B1115765 : Blo 587289 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B886397 : Blo 587289 886397 := bbase (se 3 (by rfl) ⟨166199, by rfl⟩ : syracuseStep 886397 = 332399) (by norm_num)
theorem B886421 : Blo 587289 886421 := bbase (se 6 (by rfl) ⟨20775, by rfl⟩ : syracuseStep 886421 = 41551) (by norm_num)
theorem B886445 : Blo 587289 886445 := bbase (se 3 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 886445 = 332417) (by norm_num)
theorem B886469 : Blo 587289 886469 := bbase (se 4 (by rfl) ⟨83106, by rfl⟩ : syracuseStep 886469 = 166213) (by norm_num)
theorem B886493 : Blo 587289 886493 := bbase (se 3 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 886493 = 332435) (by norm_num)
theorem B886517 : Blo 587289 886517 := bbase (se 5 (by rfl) ⟨41555, by rfl⟩ : syracuseStep 886517 = 83111) (by norm_num)
theorem B886541 : Blo 587289 886541 := bbase (se 3 (by rfl) ⟨166226, by rfl⟩ : syracuseStep 886541 = 332453) (by norm_num)
theorem B886565 : Blo 587289 886565 := bbase (se 4 (by rfl) ⟨83115, by rfl⟩ : syracuseStep 886565 = 166231) (by norm_num)
theorem B886589 : Blo 587289 886589 := bbase (se 3 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 886589 = 332471) (by norm_num)
theorem B1673045 : Blo 587289 1673045 := bbase (se 9 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 1673045 = 9803) (by norm_num)
theorem B886613 : Blo 587289 886613 := bbase (se 9 (by rfl) ⟨2597, by rfl⟩ : syracuseStep 886613 = 5195) (by norm_num)
theorem B886637 : Blo 587289 886637 := bbase (se 3 (by rfl) ⟨166244, by rfl⟩ : syracuseStep 886637 = 332489) (by norm_num)
theorem B886661 : Blo 587289 886661 := bbase (se 4 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 886661 = 166249) (by norm_num)
theorem B886685 : Blo 587289 886685 := bbase (se 3 (by rfl) ⟨166253, by rfl⟩ : syracuseStep 886685 = 332507) (by norm_num)
theorem B886709 : Blo 587289 886709 := bbase (se 5 (by rfl) ⟨41564, by rfl⟩ : syracuseStep 886709 = 83129) (by norm_num)
theorem B2983877 : Blo 587289 2983877 := bbase (se 4 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 2983877 = 559477) (by norm_num)
theorem B886733 : Blo 587289 886733 := bbase (se 3 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 886733 = 332525) (by norm_num)
theorem B886757 : Blo 587289 886757 := bbase (se 4 (by rfl) ⟨83133, by rfl⟩ : syracuseStep 886757 = 166267) (by norm_num)
theorem B886781 : Blo 587289 886781 := bbase (se 3 (by rfl) ⟨166271, by rfl⟩ : syracuseStep 886781 = 332543) (by norm_num)
theorem B1673237 : Blo 587289 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B886805 : Blo 587289 886805 := bbase (se 6 (by rfl) ⟨20784, by rfl⟩ : syracuseStep 886805 = 41569) (by norm_num)
theorem B4261909 : Blo 587289 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B1509421 : Blo 587289 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B886829 : Blo 587289 886829 := bbase (se 3 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 886829 = 332561) (by norm_num)
theorem B886853 : Blo 587289 886853 := bbase (se 4 (by rfl) ⟨83142, by rfl⟩ : syracuseStep 886853 = 166285) (by norm_num)
theorem B886877 : Blo 587289 886877 := bbase (se 3 (by rfl) ⟨166289, by rfl⟩ : syracuseStep 886877 = 332579) (by norm_num)
theorem B886901 : Blo 587289 886901 := bbase (se 5 (by rfl) ⟨41573, by rfl⟩ : syracuseStep 886901 = 83147) (by norm_num)
theorem B886925 : Blo 587289 886925 := bbase (se 3 (by rfl) ⟨166298, by rfl⟩ : syracuseStep 886925 = 332597) (by norm_num)
theorem B7178453 : Blo 587289 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B2689253 : Blo 587289 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B1706309 : Blo 587289 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B1116517 : Blo 587289 1116517 := bbase (se 4 (by rfl) ⟨104673, by rfl⟩ : syracuseStep 1116517 = 209347) (by norm_num)
theorem B8063381 : Blo 587289 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B1116661 : Blo 587289 1116661 := bbase (se 5 (by rfl) ⟨52343, by rfl⟩ : syracuseStep 1116661 = 104687) (by norm_num)
theorem B1116821 : Blo 587289 1116821 := bbase (se 6 (by rfl) ⟨26175, by rfl⟩ : syracuseStep 1116821 = 52351) (by norm_num)
theorem B3148469 : Blo 587289 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B1116965 : Blo 587289 1116965 := bbase (se 4 (by rfl) ⟨104715, by rfl⟩ : syracuseStep 1116965 = 209431) (by norm_num)
theorem B1674229 : Blo 587289 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B2231333 : Blo 587289 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B1117253 : Blo 587289 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B2985173 : Blo 587289 2985173 := bbase (se 7 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 2985173 = 69965) (by norm_num)
theorem B1117405 : Blo 587289 1117405 := bbase (se 3 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 1117405 = 419027) (by norm_num)
theorem B1412333 : Blo 587289 1412333 := bbase (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) (by norm_num)
theorem B2231621 : Blo 587289 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B1412525 : Blo 587289 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B4460021 : Blo 587289 4460021 := bbase (se 5 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 4460021 = 418127) (by norm_num)
theorem B2395637 : Blo 587289 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1117709 : Blo 587289 1117709 := bbase (se 3 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 1117709 = 419141) (by norm_num)
theorem B1675333 : Blo 587289 1675333 := bbase (se 4 (by rfl) ⟨157062, by rfl⟩ : syracuseStep 1675333 = 314125) (by norm_num)
theorem B757873 : Blo 587289 757873 := bbase (se 2 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 757873 = 568405) (by norm_num)
theorem B1118461 : Blo 587289 1118461 := bbase (se 3 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 1118461 = 419423) (by norm_num)
theorem B2265365 : Blo 587289 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B2298133 : Blo 587289 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B3772757 : Blo 587289 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B1118605 : Blo 587289 1118605 := bbase (se 3 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 1118605 = 419477) (by norm_num)
theorem B2232805 : Blo 587289 2232805 := bbase (se 4 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 2232805 = 418651) (by norm_num)
theorem B2986469 : Blo 587289 2986469 := bbase (se 4 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 2986469 = 559963) (by norm_num)
theorem B627221 : Blo 587289 627221 := bbase (se 6 (by rfl) ⟨14700, by rfl⟩ : syracuseStep 627221 = 29401) (by norm_num)
theorem B1118765 : Blo 587289 1118765 := bbase (se 3 (by rfl) ⟨209768, by rfl⟩ : syracuseStep 1118765 = 419537) (by norm_num)
theorem B1118909 : Blo 587289 1118909 := bbase (se 3 (by rfl) ⟨209795, by rfl⟩ : syracuseStep 1118909 = 419591) (by norm_num)
theorem B627473 : Blo 587289 627473 := bbase (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) (by norm_num)
theorem B2233109 : Blo 587289 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1414093 : Blo 587289 1414093 := bbase (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) (by norm_num)
theorem B1119197 : Blo 587289 1119197 := bbase (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) (by norm_num)
theorem B3347477 : Blo 587289 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B1119349 : Blo 587289 1119349 := bbase (se 5 (by rfl) ⟨52469, by rfl⟩ : syracuseStep 1119349 = 104939) (by norm_num)
theorem B627917 : Blo 587289 627917 := bbase (se 3 (by rfl) ⟨117734, by rfl⟩ : syracuseStep 627917 = 235469) (by norm_num)
theorem B660721 : Blo 587289 660721 := bbase (se 2 (by rfl) ⟨247770, by rfl⟩ : syracuseStep 660721 = 495541) (by norm_num)
theorem B660757 : Blo 587289 660757 := bbase (se 6 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 660757 = 30973) (by norm_num)
theorem B6722837 : Blo 587289 6722837 := bbase (se 6 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 6722837 = 315133) (by norm_num)
theorem B660793 : Blo 587289 660793 := bbase (se 2 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 660793 = 495595) (by norm_num)
theorem B660829 : Blo 587289 660829 := bbase (se 3 (by rfl) ⟨123905, by rfl⟩ : syracuseStep 660829 = 247811) (by norm_num)
theorem B660865 : Blo 587289 660865 := bbase (se 2 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 660865 = 495649) (by norm_num)
theorem B5019029 : Blo 587289 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B660901 : Blo 587289 660901 := bbase (se 4 (by rfl) ⟨61959, by rfl⟩ : syracuseStep 660901 = 123919) (by norm_num)
theorem B1119653 : Blo 587289 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B628165 : Blo 587289 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B660937 : Blo 587289 660937 := bbase (se 2 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 660937 = 495703) (by norm_num)
theorem B660973 : Blo 587289 660973 := bbase (se 3 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 660973 = 247865) (by norm_num)
theorem B661009 : Blo 587289 661009 := bbase (se 2 (by rfl) ⟨247878, by rfl⟩ : syracuseStep 661009 = 495757) (by norm_num)
theorem B1676837 : Blo 587289 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B661045 : Blo 587289 661045 := bbase (se 5 (by rfl) ⟨30986, by rfl⟩ : syracuseStep 661045 = 61973) (by norm_num)
theorem B1414709 : Blo 587289 1414709 := bbase (se 5 (by rfl) ⟨66314, by rfl⟩ : syracuseStep 1414709 = 132629) (by norm_num)
theorem B661081 : Blo 587289 661081 := bbase (se 2 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 661081 = 495811) (by norm_num)
theorem B661117 : Blo 587289 661117 := bbase (se 3 (by rfl) ⟨123959, by rfl⟩ : syracuseStep 661117 = 247919) (by norm_num)
theorem B2692757 : Blo 587289 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B661153 : Blo 587289 661153 := bbase (se 2 (by rfl) ⟨247932, by rfl⟩ : syracuseStep 661153 = 495865) (by norm_num)
theorem B661189 : Blo 587289 661189 := bbase (se 4 (by rfl) ⟨61986, by rfl⟩ : syracuseStep 661189 = 123973) (by norm_num)
theorem B661225 : Blo 587289 661225 := bbase (se 2 (by rfl) ⟨247959, by rfl⟩ : syracuseStep 661225 = 495919) (by norm_num)
theorem B2987765 : Blo 587289 2987765 := bbase (se 5 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 2987765 = 280103) (by norm_num)
theorem B661261 : Blo 587289 661261 := bbase (se 3 (by rfl) ⟨123986, by rfl⟩ : syracuseStep 661261 = 247973) (by norm_num)
theorem B661297 : Blo 587289 661297 := bbase (se 2 (by rfl) ⟨247986, by rfl⟩ : syracuseStep 661297 = 495973) (by norm_num)
theorem B661333 : Blo 587289 661333 := bbase (se 9 (by rfl) ⟨1937, by rfl⟩ : syracuseStep 661333 = 3875) (by norm_num)
theorem B661369 : Blo 587289 661369 := bbase (se 2 (by rfl) ⟨248013, by rfl⟩ : syracuseStep 661369 = 496027) (by norm_num)
theorem B628609 : Blo 587289 628609 := bbase (se 2 (by rfl) ⟨235728, by rfl⟩ : syracuseStep 628609 = 471457) (by norm_num)
theorem B661405 : Blo 587289 661405 := bbase (se 3 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 661405 = 248027) (by norm_num)
theorem B628669 : Blo 587289 628669 := bbase (se 3 (by rfl) ⟨117875, by rfl⟩ : syracuseStep 628669 = 235751) (by norm_num)
theorem B661441 : Blo 587289 661441 := bbase (se 2 (by rfl) ⟨248040, by rfl⟩ : syracuseStep 661441 = 496081) (by norm_num)
theorem B9050069 : Blo 587289 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B661477 : Blo 587289 661477 := bbase (se 4 (by rfl) ⟨62013, by rfl⟩ : syracuseStep 661477 = 124027) (by norm_num)
theorem B661513 : Blo 587289 661513 := bbase (se 2 (by rfl) ⟨248067, by rfl⟩ : syracuseStep 661513 = 496135) (by norm_num)
theorem B661549 : Blo 587289 661549 := bbase (se 3 (by rfl) ⟨124040, by rfl⟩ : syracuseStep 661549 = 248081) (by norm_num)
theorem B661585 : Blo 587289 661585 := bbase (se 2 (by rfl) ⟨248094, by rfl⟩ : syracuseStep 661585 = 496189) (by norm_num)
theorem B661621 : Blo 587289 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B1120405 : Blo 587289 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B661657 : Blo 587289 661657 := bbase (se 2 (by rfl) ⟨248121, by rfl⟩ : syracuseStep 661657 = 496243) (by norm_num)
theorem B3348661 : Blo 587289 3348661 := bbase (se 5 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 3348661 = 313937) (by norm_num)
theorem B661693 : Blo 587289 661693 := bbase (se 3 (by rfl) ⟨124067, by rfl⟩ : syracuseStep 661693 = 248135) (by norm_num)
theorem B596161 : Blo 587289 596161 := bbase (se 2 (by rfl) ⟨223560, by rfl⟩ : syracuseStep 596161 = 447121) (by norm_num)
theorem B661729 : Blo 587289 661729 := bbase (se 2 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 661729 = 496297) (by norm_num)
theorem B628985 : Blo 587289 628985 := bbase (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) (by norm_num)
theorem B661765 : Blo 587289 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B1120549 : Blo 587289 1120549 := bbase (se 4 (by rfl) ⟨105051, by rfl⟩ : syracuseStep 1120549 = 210103) (by norm_num)
theorem B661801 : Blo 587289 661801 := bbase (se 2 (by rfl) ⟨248175, by rfl⟩ : syracuseStep 661801 = 496351) (by norm_num)
theorem B1415485 : Blo 587289 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B661837 : Blo 587289 661837 := bbase (se 3 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 661837 = 248189) (by norm_num)
theorem B661873 : Blo 587289 661873 := bbase (se 2 (by rfl) ⟨248202, by rfl⟩ : syracuseStep 661873 = 496405) (by norm_num)
theorem B661909 : Blo 587289 661909 := bbase (se 6 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 661909 = 31027) (by norm_num)
theorem B661945 : Blo 587289 661945 := bbase (se 2 (by rfl) ⟨248229, by rfl⟩ : syracuseStep 661945 = 496459) (by norm_num)
theorem B1120709 : Blo 587289 1120709 := bbase (se 4 (by rfl) ⟨105066, by rfl⟩ : syracuseStep 1120709 = 210133) (by norm_num)
theorem B661981 : Blo 587289 661981 := bbase (se 3 (by rfl) ⟨124121, by rfl⟩ : syracuseStep 661981 = 248243) (by norm_num)
theorem B596473 : Blo 587289 596473 := bbase (se 2 (by rfl) ⟨223677, by rfl⟩ : syracuseStep 596473 = 447355) (by norm_num)
theorem B662017 : Blo 587289 662017 := bbase (se 2 (by rfl) ⟨248256, by rfl⟩ : syracuseStep 662017 = 496513) (by norm_num)
theorem B662053 : Blo 587289 662053 := bbase (se 4 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 662053 = 124135) (by norm_num)
theorem B662089 : Blo 587289 662089 := bbase (se 2 (by rfl) ⟨248283, by rfl⟩ : syracuseStep 662089 = 496567) (by norm_num)
theorem B1120853 : Blo 587289 1120853 := bbase (se 8 (by rfl) ⟨6567, by rfl⟩ : syracuseStep 1120853 = 13135) (by norm_num)
theorem B662125 : Blo 587289 662125 := bbase (se 3 (by rfl) ⟨124148, by rfl⟩ : syracuseStep 662125 = 248297) (by norm_num)
theorem B662161 : Blo 587289 662161 := bbase (se 2 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 662161 = 496621) (by norm_num)
theorem B662197 : Blo 587289 662197 := bbase (se 5 (by rfl) ⟨31040, by rfl⟩ : syracuseStep 662197 = 62081) (by norm_num)
theorem B629429 : Blo 587289 629429 := bbase (se 5 (by rfl) ⟨29504, by rfl⟩ : syracuseStep 629429 = 59009) (by norm_num)
theorem B662233 : Blo 587289 662233 := bbase (se 2 (by rfl) ⟨248337, by rfl⟩ : syracuseStep 662233 = 496675) (by norm_num)
theorem B629489 : Blo 587289 629489 := bbase (se 2 (by rfl) ⟨236058, by rfl⟩ : syracuseStep 629489 = 472117) (by norm_num)
theorem B662269 : Blo 587289 662269 := bbase (se 3 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 662269 = 248351) (by norm_num)
theorem B662305 : Blo 587289 662305 := bbase (se 2 (by rfl) ⟨248364, by rfl⟩ : syracuseStep 662305 = 496729) (by norm_num)
theorem B662341 : Blo 587289 662341 := bbase (se 4 (by rfl) ⟨62094, by rfl⟩ : syracuseStep 662341 = 124189) (by norm_num)
theorem B3021637 : Blo 587289 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B2235221 : Blo 587289 2235221 := bbase (se 9 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 2235221 = 13097) (by norm_num)
theorem B662377 : Blo 587289 662377 := bbase (se 2 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 662377 = 496783) (by norm_num)
theorem B629617 : Blo 587289 629617 := bbase (se 2 (by rfl) ⟨236106, by rfl⟩ : syracuseStep 629617 = 472213) (by norm_num)
theorem B1121141 : Blo 587289 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B662413 : Blo 587289 662413 := bbase (se 3 (by rfl) ⟨124202, by rfl⟩ : syracuseStep 662413 = 248405) (by norm_num)
theorem B662449 : Blo 587289 662449 := bbase (se 2 (by rfl) ⟨248418, by rfl⟩ : syracuseStep 662449 = 496837) (by norm_num)
theorem B2726837 : Blo 587289 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B662485 : Blo 587289 662485 := bbase (se 7 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 662485 = 15527) (by norm_num)
theorem B662521 : Blo 587289 662521 := bbase (se 2 (by rfl) ⟨248445, by rfl⟩ : syracuseStep 662521 = 496891) (by norm_num)
theorem B1416197 : Blo 587289 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B2989061 : Blo 587289 2989061 := bbase (se 4 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 2989061 = 560449) (by norm_num)
theorem B1121293 : Blo 587289 1121293 := bbase (se 3 (by rfl) ⟨210242, by rfl⟩ : syracuseStep 1121293 = 420485) (by norm_num)
theorem B662557 : Blo 587289 662557 := bbase (se 3 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 662557 = 248459) (by norm_num)
theorem B5676085 : Blo 587289 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B662593 : Blo 587289 662593 := bbase (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) (by norm_num)
theorem B1678421 : Blo 587289 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B662629 : Blo 587289 662629 := bbase (se 4 (by rfl) ⟨62121, by rfl⟩ : syracuseStep 662629 = 124243) (by norm_num)
theorem B2235509 : Blo 587289 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B662665 : Blo 587289 662665 := bbase (se 2 (by rfl) ⟨248499, by rfl⟩ : syracuseStep 662665 = 496999) (by norm_num)
theorem B793741 : Blo 587289 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B662701 : Blo 587289 662701 := bbase (se 3 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 662701 = 248513) (by norm_num)
theorem B662737 : Blo 587289 662737 := bbase (se 2 (by rfl) ⟨248526, by rfl⟩ : syracuseStep 662737 = 497053) (by norm_num)
theorem B662773 : Blo 587289 662773 := bbase (se 5 (by rfl) ⟨31067, by rfl⟩ : syracuseStep 662773 = 62135) (by norm_num)
theorem B662809 : Blo 587289 662809 := bbase (se 2 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 662809 = 497107) (by norm_num)
theorem B630061 : Blo 587289 630061 := bbase (se 3 (by rfl) ⟨118136, by rfl⟩ : syracuseStep 630061 = 236273) (by norm_num)
theorem B662845 : Blo 587289 662845 := bbase (se 3 (by rfl) ⟨124283, by rfl⟩ : syracuseStep 662845 = 248567) (by norm_num)
theorem B1121597 : Blo 587289 1121597 := bbase (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) (by norm_num)
theorem B662881 : Blo 587289 662881 := bbase (se 2 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 662881 = 497161) (by norm_num)
theorem B662917 : Blo 587289 662917 := bbase (se 4 (by rfl) ⟨62148, by rfl⟩ : syracuseStep 662917 = 124297) (by norm_num)
theorem B630181 : Blo 587289 630181 := bbase (se 4 (by rfl) ⟨59079, by rfl⟩ : syracuseStep 630181 = 118159) (by norm_num)
theorem B662953 : Blo 587289 662953 := bbase (se 2 (by rfl) ⟨248607, by rfl⟩ : syracuseStep 662953 = 497215) (by norm_num)
theorem B662989 : Blo 587289 662989 := bbase (se 3 (by rfl) ⟨124310, by rfl⟩ : syracuseStep 662989 = 248621) (by norm_num)
theorem B663025 : Blo 587289 663025 := bbase (se 2 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 663025 = 497269) (by norm_num)
theorem B663061 : Blo 587289 663061 := bbase (se 6 (by rfl) ⟨15540, by rfl⟩ : syracuseStep 663061 = 31081) (by norm_num)
theorem B663097 : Blo 587289 663097 := bbase (se 2 (by rfl) ⟨248661, by rfl⟩ : syracuseStep 663097 = 497323) (by norm_num)
theorem B663133 : Blo 587289 663133 := bbase (se 3 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 663133 = 248675) (by norm_num)
theorem B663169 : Blo 587289 663169 := bbase (se 2 (by rfl) ⟨248688, by rfl⟩ : syracuseStep 663169 = 497377) (by norm_num)
theorem B630433 : Blo 587289 630433 := bbase (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) (by norm_num)
theorem B1416869 : Blo 587289 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B630437 : Blo 587289 630437 := bbase (se 4 (by rfl) ⟨59103, by rfl⟩ : syracuseStep 630437 = 118207) (by norm_num)
theorem B663205 : Blo 587289 663205 := bbase (se 4 (by rfl) ⟨62175, by rfl⟩ : syracuseStep 663205 = 124351) (by norm_num)
theorem B663241 : Blo 587289 663241 := bbase (se 2 (by rfl) ⟨248715, by rfl⟩ : syracuseStep 663241 = 497431) (by norm_num)
theorem B663277 : Blo 587289 663277 := bbase (se 3 (by rfl) ⟨124364, by rfl⟩ : syracuseStep 663277 = 248729) (by norm_num)
theorem B1679093 : Blo 587289 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B663313 : Blo 587289 663313 := bbase (se 2 (by rfl) ⟨248742, by rfl⟩ : syracuseStep 663313 = 497485) (by norm_num)
theorem B663349 : Blo 587289 663349 := bbase (se 5 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 663349 = 62189) (by norm_num)
theorem B663385 : Blo 587289 663385 := bbase (se 2 (by rfl) ⟨248769, by rfl⟩ : syracuseStep 663385 = 497539) (by norm_num)
theorem B663421 : Blo 587289 663421 := bbase (se 3 (by rfl) ⟨124391, by rfl⟩ : syracuseStep 663421 = 248783) (by norm_num)
theorem B991109 : Blo 587289 991109 := bbase (se 4 (by rfl) ⟨92916, by rfl⟩ : syracuseStep 991109 = 185833) (by norm_num)
theorem B663457 : Blo 587289 663457 := bbase (se 2 (by rfl) ⟨248796, by rfl⟩ : syracuseStep 663457 = 497593) (by norm_num)
theorem B597937 : Blo 587289 597937 := bbase (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) (by norm_num)
theorem B663493 : Blo 587289 663493 := bbase (se 4 (by rfl) ⟨62202, by rfl⟩ : syracuseStep 663493 = 124405) (by norm_num)
theorem B597985 : Blo 587289 597985 := bbase (se 2 (by rfl) ⟨224244, by rfl⟩ : syracuseStep 597985 = 448489) (by norm_num)
theorem B663529 : Blo 587289 663529 := bbase (se 2 (by rfl) ⟨248823, by rfl⟩ : syracuseStep 663529 = 497647) (by norm_num)
theorem B991237 : Blo 587289 991237 := bbase (se 4 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 991237 = 185857) (by norm_num)
theorem B663565 : Blo 587289 663565 := bbase (se 3 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 663565 = 248837) (by norm_num)
theorem B1122349 : Blo 587289 1122349 := bbase (se 3 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 1122349 = 420881) (by norm_num)
theorem B663601 : Blo 587289 663601 := bbase (se 2 (by rfl) ⟨248850, by rfl⟩ : syracuseStep 663601 = 497701) (by norm_num)
theorem B663637 : Blo 587289 663637 := bbase (se 8 (by rfl) ⟨3888, by rfl⟩ : syracuseStep 663637 = 7777) (by norm_num)
theorem B16162901 : Blo 587289 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B991325 : Blo 587289 991325 := bbase (se 3 (by rfl) ⟨185873, by rfl⟩ : syracuseStep 991325 = 371747) (by norm_num)
theorem B3350645 : Blo 587289 3350645 := bbase (se 5 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 3350645 = 314123) (by norm_num)
theorem B663673 : Blo 587289 663673 := bbase (se 2 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 663673 = 497755) (by norm_num)
theorem B663709 : Blo 587289 663709 := bbase (se 3 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 663709 = 248891) (by norm_num)
theorem B1679525 : Blo 587289 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B1122493 : Blo 587289 1122493 := bbase (se 3 (by rfl) ⟨210467, by rfl⟩ : syracuseStep 1122493 = 420935) (by norm_num)
theorem B663745 : Blo 587289 663745 := bbase (se 2 (by rfl) ⟨248904, by rfl⟩ : syracuseStep 663745 = 497809) (by norm_num)
theorem B631001 : Blo 587289 631001 := bbase (se 2 (by rfl) ⟨236625, by rfl⟩ : syracuseStep 631001 = 473251) (by norm_num)
theorem B991453 : Blo 587289 991453 := bbase (se 3 (by rfl) ⟨185897, by rfl⟩ : syracuseStep 991453 = 371795) (by norm_num)
theorem B663781 : Blo 587289 663781 := bbase (se 4 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 663781 = 124459) (by norm_num)
theorem B663817 : Blo 587289 663817 := bbase (se 2 (by rfl) ⟨248931, by rfl⟩ : syracuseStep 663817 = 497863) (by norm_num)
theorem B5644565 : Blo 587289 5644565 := bbase (se 6 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 5644565 = 264589) (by norm_num)
theorem B2236693 : Blo 587289 2236693 := bbase (se 6 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 2236693 = 104845) (by norm_num)
theorem B2990357 : Blo 587289 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B663853 : Blo 587289 663853 := bbase (se 3 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 663853 = 248945) (by norm_num)
theorem B991541 : Blo 587289 991541 := bbase (se 5 (by rfl) ⟨46478, by rfl⟩ : syracuseStep 991541 = 92957) (by norm_num)
theorem B663889 : Blo 587289 663889 := bbase (se 2 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 663889 = 497917) (by norm_num)
theorem B663925 : Blo 587289 663925 := bbase (se 5 (by rfl) ⟨31121, by rfl⟩ : syracuseStep 663925 = 62243) (by norm_num)
theorem B631189 : Blo 587289 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B663961 : Blo 587289 663961 := bbase (se 2 (by rfl) ⟨248985, by rfl⟩ : syracuseStep 663961 = 497971) (by norm_num)
theorem B991669 : Blo 587289 991669 := bbase (se 5 (by rfl) ⟨46484, by rfl⟩ : syracuseStep 991669 = 92969) (by norm_num)
theorem B663997 : Blo 587289 663997 := bbase (se 3 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 663997 = 248999) (by norm_num)
theorem B664033 : Blo 587289 664033 := bbase (se 2 (by rfl) ⟨249012, by rfl⟩ : syracuseStep 664033 = 498025) (by norm_num)
theorem B664069 : Blo 587289 664069 := bbase (se 4 (by rfl) ⟨62256, by rfl⟩ : syracuseStep 664069 = 124513) (by norm_num)
theorem B991757 : Blo 587289 991757 := bbase (se 3 (by rfl) ⟨185954, by rfl⟩ : syracuseStep 991757 = 371909) (by norm_num)
theorem B664105 : Blo 587289 664105 := bbase (se 2 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 664105 = 498079) (by norm_num)
theorem B3875381 : Blo 587289 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B2236997 : Blo 587289 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B664141 : Blo 587289 664141 := bbase (se 3 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 664141 = 249053) (by norm_num)
theorem B664177 : Blo 587289 664177 := bbase (se 2 (by rfl) ⟨249066, by rfl⟩ : syracuseStep 664177 = 498133) (by norm_num)
theorem B991885 : Blo 587289 991885 := bbase (se 3 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 991885 = 371957) (by norm_num)
theorem B664213 : Blo 587289 664213 := bbase (se 6 (by rfl) ⟨15567, by rfl⟩ : syracuseStep 664213 = 31135) (by norm_num)
theorem B664249 : Blo 587289 664249 := bbase (se 2 (by rfl) ⟨249093, by rfl⟩ : syracuseStep 664249 = 498187) (by norm_num)
theorem B1516229 : Blo 587289 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B664285 : Blo 587289 664285 := bbase (se 3 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 664285 = 249107) (by norm_num)
theorem B991973 : Blo 587289 991973 := bbase (se 4 (by rfl) ⟨92997, by rfl⟩ : syracuseStep 991973 = 185995) (by norm_num)
theorem B3023605 : Blo 587289 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B664321 : Blo 587289 664321 := bbase (se 2 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 664321 = 498241) (by norm_num)
theorem B664357 : Blo 587289 664357 := bbase (se 4 (by rfl) ⟨62283, by rfl⟩ : syracuseStep 664357 = 124567) (by norm_num)
theorem B664393 : Blo 587289 664393 := bbase (se 2 (by rfl) ⟨249147, by rfl⟩ : syracuseStep 664393 = 498295) (by norm_num)
theorem B992101 : Blo 587289 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B664429 : Blo 587289 664429 := bbase (se 3 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 664429 = 249161) (by norm_num)
theorem B664465 : Blo 587289 664465 := bbase (se 2 (by rfl) ⟨249174, by rfl⟩ : syracuseStep 664465 = 498349) (by norm_num)
theorem B1680277 : Blo 587289 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B664501 : Blo 587289 664501 := bbase (se 5 (by rfl) ⟨31148, by rfl⟩ : syracuseStep 664501 = 62297) (by norm_num)
theorem B992189 : Blo 587289 992189 := bbase (se 3 (by rfl) ⟨186035, by rfl⟩ : syracuseStep 992189 = 372071) (by norm_num)
theorem B664537 : Blo 587289 664537 := bbase (se 2 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 664537 = 498403) (by norm_num)
theorem B664573 : Blo 587289 664573 := bbase (se 3 (by rfl) ⟨124607, by rfl⟩ : syracuseStep 664573 = 249215) (by norm_num)
theorem B664609 : Blo 587289 664609 := bbase (se 2 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 664609 = 498457) (by norm_num)
theorem B992317 : Blo 587289 992317 := bbase (se 3 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 992317 = 372119) (by norm_num)
theorem B664645 : Blo 587289 664645 := bbase (se 4 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 664645 = 124621) (by norm_num)
theorem B664681 : Blo 587289 664681 := bbase (se 2 (by rfl) ⟨249255, by rfl⟩ : syracuseStep 664681 = 498511) (by norm_num)
theorem B795757 : Blo 587289 795757 := bbase (se 3 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 795757 = 298409) (by norm_num)
theorem B664717 : Blo 587289 664717 := bbase (se 3 (by rfl) ⟨124634, by rfl⟩ : syracuseStep 664717 = 249269) (by norm_num)
theorem B992405 : Blo 587289 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B664753 : Blo 587289 664753 := bbase (se 2 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 664753 = 498565) (by norm_num)
theorem B664789 : Blo 587289 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B664825 : Blo 587289 664825 := bbase (se 2 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 664825 = 498619) (by norm_num)
theorem B992533 : Blo 587289 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B664861 : Blo 587289 664861 := bbase (se 3 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 664861 = 249323) (by norm_num)
theorem B664897 : Blo 587289 664897 := bbase (se 2 (by rfl) ⟨249336, by rfl⟩ : syracuseStep 664897 = 498673) (by norm_num)
theorem B664933 : Blo 587289 664933 := bbase (se 4 (by rfl) ⟨62337, by rfl⟩ : syracuseStep 664933 = 124675) (by norm_num)
theorem B992621 : Blo 587289 992621 := bbase (se 3 (by rfl) ⟨186116, by rfl⟩ : syracuseStep 992621 = 372233) (by norm_num)
theorem B1418629 : Blo 587289 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B664969 : Blo 587289 664969 := bbase (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) (by norm_num)
theorem B665005 : Blo 587289 665005 := bbase (se 3 (by rfl) ⟨124688, by rfl⟩ : syracuseStep 665005 = 249377) (by norm_num)
theorem B665041 : Blo 587289 665041 := bbase (se 2 (by rfl) ⟨249390, by rfl⟩ : syracuseStep 665041 = 498781) (by norm_num)
theorem B992749 : Blo 587289 992749 := bbase (se 3 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 992749 = 372281) (by norm_num)
theorem B665077 : Blo 587289 665077 := bbase (se 5 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 665077 = 62351) (by norm_num)
theorem B2827781 : Blo 587289 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B665113 : Blo 587289 665113 := bbase (se 2 (by rfl) ⟨249417, by rfl⟩ : syracuseStep 665113 = 498835) (by norm_num)
theorem B2991653 : Blo 587289 2991653 := bbase (se 4 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 2991653 = 560935) (by norm_num)
theorem B665149 : Blo 587289 665149 := bbase (se 3 (by rfl) ⟨124715, by rfl⟩ : syracuseStep 665149 = 249431) (by norm_num)
theorem B992837 : Blo 587289 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B1254989 : Blo 587289 1254989 := bbase (se 3 (by rfl) ⟨235310, by rfl⟩ : syracuseStep 1254989 = 470621) (by norm_num)
theorem B665185 : Blo 587289 665185 := bbase (se 2 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 665185 = 498889) (by norm_num)
theorem B992965 : Blo 587289 992965 := bbase (se 4 (by rfl) ⟨93090, by rfl⟩ : syracuseStep 992965 = 186181) (by norm_num)
theorem B2827973 : Blo 587289 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B7186133 : Blo 587289 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1255133 : Blo 587289 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B993053 : Blo 587289 993053 := bbase (se 3 (by rfl) ⟨186197, by rfl⟩ : syracuseStep 993053 = 372395) (by norm_num)
theorem B1058645 : Blo 587289 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B993181 : Blo 587289 993181 := bbase (se 3 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 993181 = 372443) (by norm_num)
theorem B1419245 : Blo 587289 1419245 := bbase (se 3 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 1419245 = 532217) (by norm_num)
theorem B993269 : Blo 587289 993269 := bbase (se 5 (by rfl) ⟨46559, by rfl⟩ : syracuseStep 993269 = 93119) (by norm_num)
theorem B1255493 : Blo 587289 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B2828357 : Blo 587289 2828357 := bbase (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) (by norm_num)
theorem B3188821 : Blo 587289 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B1058933 : Blo 587289 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B993397 : Blo 587289 993397 := bbase (se 5 (by rfl) ⟨46565, by rfl⟩ : syracuseStep 993397 = 93131) (by norm_num)
theorem B993485 : Blo 587289 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B1059077 : Blo 587289 1059077 := bbase (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) (by norm_num)
theorem B3352853 : Blo 587289 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B993613 : Blo 587289 993613 := bbase (se 3 (by rfl) ⟨186302, by rfl⟩ : syracuseStep 993613 = 372605) (by norm_num)
theorem B895349 : Blo 587289 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B993701 : Blo 587289 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B895421 : Blo 587289 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B11446741 : Blo 587289 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B797141 : Blo 587289 797141 := bbase (se 7 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 797141 = 18683) (by norm_num)
theorem B1321469 : Blo 587289 1321469 := bbase (se 3 (by rfl) ⟨247775, by rfl⟩ : syracuseStep 1321469 = 495551) (by norm_num)
theorem B993829 : Blo 587289 993829 := bbase (se 4 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 993829 = 186343) (by norm_num)
theorem B1321541 : Blo 587289 1321541 := bbase (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) (by norm_num)
theorem B993917 : Blo 587289 993917 := bbase (se 3 (by rfl) ⟨186359, by rfl⟩ : syracuseStep 993917 = 372719) (by norm_num)
theorem B2239109 : Blo 587289 2239109 := bbase (se 4 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 2239109 = 419833) (by norm_num)
theorem B1321613 : Blo 587289 1321613 := bbase (se 3 (by rfl) ⟨247802, by rfl⟩ : syracuseStep 1321613 = 495605) (by norm_num)
theorem B1813157 : Blo 587289 1813157 := bbase (se 4 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 1813157 = 339967) (by norm_num)
theorem B1321685 : Blo 587289 1321685 := bbase (se 7 (by rfl) ⟨15488, by rfl⟩ : syracuseStep 1321685 = 30977) (by norm_num)
theorem B1420013 : Blo 587289 1420013 := bbase (se 3 (by rfl) ⟨266252, by rfl⟩ : syracuseStep 1420013 = 532505) (by norm_num)
theorem B1420021 : Blo 587289 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B994045 : Blo 587289 994045 := bbase (se 3 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 994045 = 372767) (by norm_num)
theorem B1321757 : Blo 587289 1321757 := bbase (se 3 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 1321757 = 495659) (by norm_num)
theorem B3189557 : Blo 587289 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2992949 : Blo 587289 2992949 := bbase (se 5 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 2992949 = 280589) (by norm_num)
theorem B1059653 : Blo 587289 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B994133 : Blo 587289 994133 := bbase (se 9 (by rfl) ⟨2912, by rfl⟩ : syracuseStep 994133 = 5825) (by norm_num)
theorem B1321829 : Blo 587289 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B2239397 : Blo 587289 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B1321901 : Blo 587289 1321901 := bbase (se 3 (by rfl) ⟨247856, by rfl⟩ : syracuseStep 1321901 = 495713) (by norm_num)
theorem B1256381 : Blo 587289 1256381 := bbase (se 3 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 1256381 = 471143) (by norm_num)
theorem B994261 : Blo 587289 994261 := bbase (se 7 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 994261 = 23303) (by norm_num)
theorem B1321973 : Blo 587289 1321973 := bbase (se 5 (by rfl) ⟨61967, by rfl⟩ : syracuseStep 1321973 = 123935) (by norm_num)
theorem B994349 : Blo 587289 994349 := bbase (se 3 (by rfl) ⟨186440, by rfl⟩ : syracuseStep 994349 = 372881) (by norm_num)
theorem B1322045 : Blo 587289 1322045 := bbase (se 3 (by rfl) ⟨247883, by rfl⟩ : syracuseStep 1322045 = 495767) (by norm_num)
theorem B4467797 : Blo 587289 4467797 := bbase (se 8 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 4467797 = 52357) (by norm_num)
theorem B1322117 : Blo 587289 1322117 := bbase (se 4 (by rfl) ⟨123948, by rfl⟩ : syracuseStep 1322117 = 247897) (by norm_num)
theorem B994477 : Blo 587289 994477 := bbase (se 3 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 994477 = 372929) (by norm_num)
theorem B1256629 : Blo 587289 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B1322189 : Blo 587289 1322189 := bbase (se 3 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 1322189 = 495821) (by norm_num)
theorem B994565 : Blo 587289 994565 := bbase (se 4 (by rfl) ⟨93240, by rfl⟩ : syracuseStep 994565 = 186481) (by norm_num)
theorem B1322261 : Blo 587289 1322261 := bbase (se 6 (by rfl) ⟨30990, by rfl⟩ : syracuseStep 1322261 = 61981) (by norm_num)
theorem B4828501 : Blo 587289 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B1322333 : Blo 587289 1322333 := bbase (se 3 (by rfl) ⟨247937, by rfl⟩ : syracuseStep 1322333 = 495875) (by norm_num)
theorem B994693 : Blo 587289 994693 := bbase (se 4 (by rfl) ⟨93252, by rfl⟩ : syracuseStep 994693 = 186505) (by norm_num)
theorem B1322405 : Blo 587289 1322405 := bbase (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) (by norm_num)
theorem B994781 : Blo 587289 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B1322477 : Blo 587289 1322477 := bbase (se 3 (by rfl) ⟨247964, by rfl⟩ : syracuseStep 1322477 = 495929) (by norm_num)
theorem B1322549 : Blo 587289 1322549 := bbase (se 5 (by rfl) ⟨61994, by rfl⟩ : syracuseStep 1322549 = 123989) (by norm_num)
theorem B994909 : Blo 587289 994909 := bbase (se 3 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 994909 = 373091) (by norm_num)
theorem B1322621 : Blo 587289 1322621 := bbase (se 3 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 1322621 = 495983) (by norm_num)
theorem B798373 : Blo 587289 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B1257133 : Blo 587289 1257133 := bbase (se 3 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 1257133 = 471425) (by norm_num)
theorem B994997 : Blo 587289 994997 := bbase (se 5 (by rfl) ⟨46640, by rfl⟩ : syracuseStep 994997 = 93281) (by norm_num)
theorem B1683125 : Blo 587289 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B1322693 : Blo 587289 1322693 := bbase (se 4 (by rfl) ⟨124002, by rfl⟩ : syracuseStep 1322693 = 248005) (by norm_num)
theorem B1322765 : Blo 587289 1322765 := bbase (se 3 (by rfl) ⟨248018, by rfl⟩ : syracuseStep 1322765 = 496037) (by norm_num)
theorem B1486613 : Blo 587289 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B995125 : Blo 587289 995125 := bbase (se 5 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 995125 = 93293) (by norm_num)
theorem B1322837 : Blo 587289 1322837 := bbase (se 9 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 1322837 = 7751) (by norm_num)
theorem B995213 : Blo 587289 995213 := bbase (se 3 (by rfl) ⟨186602, by rfl⟩ : syracuseStep 995213 = 373205) (by norm_num)
theorem B1322909 : Blo 587289 1322909 := bbase (se 3 (by rfl) ⟨248045, by rfl⟩ : syracuseStep 1322909 = 496091) (by norm_num)
theorem B3583925 : Blo 587289 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B1322981 : Blo 587289 1322981 := bbase (se 4 (by rfl) ⟨124029, by rfl⟩ : syracuseStep 1322981 = 248059) (by norm_num)
theorem B995341 : Blo 587289 995341 := bbase (se 3 (by rfl) ⟨186626, by rfl⟩ : syracuseStep 995341 = 373253) (by norm_num)
theorem B1323053 : Blo 587289 1323053 := bbase (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) (by norm_num)
theorem B2240581 : Blo 587289 2240581 := bbase (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) (by norm_num)
theorem B995429 : Blo 587289 995429 := bbase (se 4 (by rfl) ⟨93321, by rfl⟩ : syracuseStep 995429 = 186643) (by norm_num)
theorem B1486957 : Blo 587289 1486957 := bbase (se 3 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 1486957 = 557609) (by norm_num)
theorem B1323125 : Blo 587289 1323125 := bbase (se 5 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 1323125 = 124043) (by norm_num)
theorem B897173 : Blo 587289 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B1323197 : Blo 587289 1323197 := bbase (se 3 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 1323197 = 496199) (by norm_num)
theorem B1487069 : Blo 587289 1487069 := bbase (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) (by norm_num)
theorem B995557 : Blo 587289 995557 := bbase (se 4 (by rfl) ⟨93333, by rfl⟩ : syracuseStep 995557 = 186667) (by norm_num)
theorem B1323269 : Blo 587289 1323269 := bbase (se 4 (by rfl) ⟨124056, by rfl⟩ : syracuseStep 1323269 = 248113) (by norm_num)
theorem B995645 : Blo 587289 995645 := bbase (se 3 (by rfl) ⟨186683, by rfl⟩ : syracuseStep 995645 = 373367) (by norm_num)
theorem B1323341 : Blo 587289 1323341 := bbase (se 3 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 1323341 = 496253) (by norm_num)
theorem B2240885 : Blo 587289 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B1323413 : Blo 587289 1323413 := bbase (se 6 (by rfl) ⟨31017, by rfl⟩ : syracuseStep 1323413 = 62035) (by norm_num)
theorem B1487261 : Blo 587289 1487261 := bbase (se 3 (by rfl) ⟨278861, by rfl⟩ : syracuseStep 1487261 = 557723) (by norm_num)
theorem B995773 : Blo 587289 995773 := bbase (se 3 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 995773 = 373415) (by norm_num)
theorem B1323485 : Blo 587289 1323485 := bbase (se 3 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 1323485 = 496307) (by norm_num)
theorem B995861 : Blo 587289 995861 := bbase (se 6 (by rfl) ⟨23340, by rfl⟩ : syracuseStep 995861 = 46681) (by norm_num)
theorem B1323557 : Blo 587289 1323557 := bbase (se 4 (by rfl) ⟨124083, by rfl⟩ : syracuseStep 1323557 = 248167) (by norm_num)
theorem B1258021 : Blo 587289 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B1323629 : Blo 587289 1323629 := bbase (se 3 (by rfl) ⟨248180, by rfl⟩ : syracuseStep 1323629 = 496361) (by norm_num)
theorem B1192565 : Blo 587289 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B995989 : Blo 587289 995989 := bbase (se 6 (by rfl) ⟨23343, by rfl⟩ : syracuseStep 995989 = 46687) (by norm_num)
theorem B1323701 : Blo 587289 1323701 := bbase (se 5 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 1323701 = 124097) (by norm_num)
theorem B996077 : Blo 587289 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B1487605 : Blo 587289 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B1323773 : Blo 587289 1323773 := bbase (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) (by norm_num)
theorem B1323845 : Blo 587289 1323845 := bbase (se 4 (by rfl) ⟨124110, by rfl⟩ : syracuseStep 1323845 = 248221) (by norm_num)
theorem B1487717 : Blo 587289 1487717 := bbase (se 4 (by rfl) ⟨139473, by rfl⟩ : syracuseStep 1487717 = 278947) (by norm_num)
theorem B996205 : Blo 587289 996205 := bbase (se 3 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 996205 = 373577) (by norm_num)
theorem B1323917 : Blo 587289 1323917 := bbase (se 3 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 1323917 = 496469) (by norm_num)
theorem B996293 : Blo 587289 996293 := bbase (se 4 (by rfl) ⟨93402, by rfl⟩ : syracuseStep 996293 = 186805) (by norm_num)
theorem B1323989 : Blo 587289 1323989 := bbase (se 7 (by rfl) ⟨15515, by rfl⟩ : syracuseStep 1323989 = 31031) (by norm_num)
theorem B1258517 : Blo 587289 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B1324061 : Blo 587289 1324061 := bbase (se 3 (by rfl) ⟨248261, by rfl⟩ : syracuseStep 1324061 = 496523) (by norm_num)
theorem B1487909 : Blo 587289 1487909 := bbase (se 4 (by rfl) ⟨139491, by rfl⟩ : syracuseStep 1487909 = 278983) (by norm_num)
theorem B996421 : Blo 587289 996421 := bbase (se 4 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 996421 = 186829) (by norm_num)
theorem B1324133 : Blo 587289 1324133 := bbase (se 4 (by rfl) ⟨124137, by rfl⟩ : syracuseStep 1324133 = 248275) (by norm_num)
theorem B996509 : Blo 587289 996509 := bbase (se 3 (by rfl) ⟨186845, by rfl⟩ : syracuseStep 996509 = 373691) (by norm_num)
theorem B1324205 : Blo 587289 1324205 := bbase (se 3 (by rfl) ⟨248288, by rfl⟩ : syracuseStep 1324205 = 496577) (by norm_num)
theorem B1324277 : Blo 587289 1324277 := bbase (se 5 (by rfl) ⟨62075, by rfl⟩ : syracuseStep 1324277 = 124151) (by norm_num)
theorem B5027093 : Blo 587289 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B996637 : Blo 587289 996637 := bbase (se 3 (by rfl) ⟨186869, by rfl⟩ : syracuseStep 996637 = 373739) (by norm_num)
theorem B1324349 : Blo 587289 1324349 := bbase (se 3 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 1324349 = 496631) (by norm_num)
theorem B636233 : Blo 587289 636233 := bbase (se 2 (by rfl) ⟨238587, by rfl⟩ : syracuseStep 636233 = 477175) (by norm_num)
theorem B996725 : Blo 587289 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B1488253 : Blo 587289 1488253 := bbase (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) (by norm_num)
theorem B1324421 : Blo 587289 1324421 := bbase (se 4 (by rfl) ⟨124164, by rfl⟩ : syracuseStep 1324421 = 248329) (by norm_num)
theorem B1324493 : Blo 587289 1324493 := bbase (se 3 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 1324493 = 496685) (by norm_num)
theorem B636373 : Blo 587289 636373 := bbase (se 7 (by rfl) ⟨7457, by rfl⟩ : syracuseStep 636373 = 14915) (by norm_num)
theorem B1488365 : Blo 587289 1488365 := bbase (se 3 (by rfl) ⟨279068, by rfl⟩ : syracuseStep 1488365 = 558137) (by norm_num)
theorem B996853 : Blo 587289 996853 := bbase (se 5 (by rfl) ⟨46727, by rfl⟩ : syracuseStep 996853 = 93455) (by norm_num)
theorem B1324565 : Blo 587289 1324565 := bbase (se 6 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 1324565 = 62089) (by norm_num)
theorem B996941 : Blo 587289 996941 := bbase (se 3 (by rfl) ⟨186926, by rfl⟩ : syracuseStep 996941 = 373853) (by norm_num)
theorem B1324637 : Blo 587289 1324637 := bbase (se 3 (by rfl) ⟨248369, by rfl⟩ : syracuseStep 1324637 = 496739) (by norm_num)
theorem B1881701 : Blo 587289 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B1324709 : Blo 587289 1324709 := bbase (se 4 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 1324709 = 248383) (by norm_num)
theorem B1488557 : Blo 587289 1488557 := bbase (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) (by norm_num)
theorem B636589 : Blo 587289 636589 := bbase (se 3 (by rfl) ⟨119360, by rfl⟩ : syracuseStep 636589 = 238721) (by norm_num)
theorem B997069 : Blo 587289 997069 := bbase (se 3 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 997069 = 373901) (by norm_num)
theorem B1324781 : Blo 587289 1324781 := bbase (se 3 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 1324781 = 496793) (by norm_num)
theorem B997157 : Blo 587289 997157 := bbase (se 4 (by rfl) ⟨93483, by rfl⟩ : syracuseStep 997157 = 186967) (by norm_num)
theorem B1324853 : Blo 587289 1324853 := bbase (se 5 (by rfl) ⟨62102, by rfl⟩ : syracuseStep 1324853 = 124205) (by norm_num)
theorem B1324925 : Blo 587289 1324925 := bbase (se 3 (by rfl) ⟨248423, by rfl⟩ : syracuseStep 1324925 = 496847) (by norm_num)
theorem B1259405 : Blo 587289 1259405 := bbase (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) (by norm_num)
theorem B997285 : Blo 587289 997285 := bbase (se 4 (by rfl) ⟨93495, by rfl⟩ : syracuseStep 997285 = 186991) (by norm_num)
theorem B1324997 : Blo 587289 1324997 := bbase (se 4 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 1324997 = 248437) (by norm_num)
theorem B1062877 : Blo 587289 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B997373 : Blo 587289 997373 := bbase (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) (by norm_num)
theorem B1488901 : Blo 587289 1488901 := bbase (se 4 (by rfl) ⟨139584, by rfl⟩ : syracuseStep 1488901 = 279169) (by norm_num)
theorem B1259525 : Blo 587289 1259525 := bbase (se 4 (by rfl) ⟨118080, by rfl⟩ : syracuseStep 1259525 = 236161) (by norm_num)
theorem B1325069 : Blo 587289 1325069 := bbase (se 3 (by rfl) ⟨248450, by rfl⟩ : syracuseStep 1325069 = 496901) (by norm_num)
theorem B1325141 : Blo 587289 1325141 := bbase (se 8 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 1325141 = 15529) (by norm_num)
theorem B1489013 : Blo 587289 1489013 := bbase (se 5 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 1489013 = 139595) (by norm_num)
theorem B997501 : Blo 587289 997501 := bbase (se 3 (by rfl) ⟨187031, by rfl⟩ : syracuseStep 997501 = 374063) (by norm_num)
theorem B1325213 : Blo 587289 1325213 := bbase (se 3 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 1325213 = 496955) (by norm_num)
theorem B997589 : Blo 587289 997589 := bbase (se 7 (by rfl) ⟨11690, by rfl⟩ : syracuseStep 997589 = 23381) (by norm_num)
theorem B1325285 : Blo 587289 1325285 := bbase (se 4 (by rfl) ⟨124245, by rfl⟩ : syracuseStep 1325285 = 248491) (by norm_num)
theorem B3029237 : Blo 587289 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B1063165 : Blo 587289 1063165 := bbase (se 3 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 1063165 = 398687) (by norm_num)
theorem B1358093 : Blo 587289 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B2832661 : Blo 587289 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B1325357 : Blo 587289 1325357 := bbase (se 3 (by rfl) ⟨248504, by rfl⟩ : syracuseStep 1325357 = 497009) (by norm_num)
theorem B1489205 : Blo 587289 1489205 := bbase (se 5 (by rfl) ⟨69806, by rfl⟩ : syracuseStep 1489205 = 139613) (by norm_num)
theorem B997717 : Blo 587289 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B1325429 : Blo 587289 1325429 := bbase (se 5 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 1325429 = 124259) (by norm_num)
theorem B2242997 : Blo 587289 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B1325501 : Blo 587289 1325501 := bbase (se 3 (by rfl) ⟨248531, by rfl⟩ : syracuseStep 1325501 = 497063) (by norm_num)
theorem B1882597 : Blo 587289 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B1325573 : Blo 587289 1325573 := bbase (se 4 (by rfl) ⟨124272, by rfl⟩ : syracuseStep 1325573 = 248545) (by norm_num)
theorem B1325645 : Blo 587289 1325645 := bbase (se 3 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 1325645 = 497117) (by norm_num)
theorem B1260157 : Blo 587289 1260157 := bbase (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) (by norm_num)
theorem B1489549 : Blo 587289 1489549 := bbase (se 3 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 1489549 = 558581) (by norm_num)
theorem B1325717 : Blo 587289 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B2243285 : Blo 587289 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B1325789 : Blo 587289 1325789 := bbase (se 3 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 1325789 = 497171) (by norm_num)
theorem B1489661 : Blo 587289 1489661 := bbase (se 3 (by rfl) ⟨279311, by rfl⟩ : syracuseStep 1489661 = 558623) (by norm_num)
theorem B1325861 : Blo 587289 1325861 := bbase (se 4 (by rfl) ⟨124299, by rfl⟩ : syracuseStep 1325861 = 248599) (by norm_num)
theorem B1325933 : Blo 587289 1325933 := bbase (se 3 (by rfl) ⟨248612, by rfl⟩ : syracuseStep 1325933 = 497225) (by norm_num)
theorem B1882997 : Blo 587289 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B1326005 : Blo 587289 1326005 := bbase (se 5 (by rfl) ⟨62156, by rfl⟩ : syracuseStep 1326005 = 124313) (by norm_num)
theorem B1489853 : Blo 587289 1489853 := bbase (se 3 (by rfl) ⟨279347, by rfl⟩ : syracuseStep 1489853 = 558695) (by norm_num)
theorem B1326077 : Blo 587289 1326077 := bbase (se 3 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 1326077 = 497279) (by norm_num)
theorem B1326149 : Blo 587289 1326149 := bbase (se 4 (by rfl) ⟨124326, by rfl⟩ : syracuseStep 1326149 = 248653) (by norm_num)
theorem B1326221 : Blo 587289 1326221 := bbase (se 3 (by rfl) ⟨248666, by rfl⟩ : syracuseStep 1326221 = 497333) (by norm_num)
theorem B1326293 : Blo 587289 1326293 := bbase (se 7 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 1326293 = 31085) (by norm_num)
theorem B1490197 : Blo 587289 1490197 := bbase (se 6 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 1490197 = 69853) (by norm_num)
theorem B1326365 : Blo 587289 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B1064261 : Blo 587289 1064261 := bbase (se 4 (by rfl) ⟨99774, by rfl⟩ : syracuseStep 1064261 = 199549) (by norm_num)
theorem B1326437 : Blo 587289 1326437 := bbase (se 4 (by rfl) ⟨124353, by rfl⟩ : syracuseStep 1326437 = 248707) (by norm_num)
theorem B1490309 : Blo 587289 1490309 := bbase (se 4 (by rfl) ⟨139716, by rfl⟩ : syracuseStep 1490309 = 279433) (by norm_num)
theorem B1326509 : Blo 587289 1326509 := bbase (se 3 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 1326509 = 497441) (by norm_num)
theorem B1326581 : Blo 587289 1326581 := bbase (se 5 (by rfl) ⟨62183, by rfl⟩ : syracuseStep 1326581 = 124367) (by norm_num)
theorem B1261045 : Blo 587289 1261045 := bbase (se 5 (by rfl) ⟨59111, by rfl⟩ : syracuseStep 1261045 = 118223) (by norm_num)
theorem B605701 : Blo 587289 605701 := bbase (se 4 (by rfl) ⟨56784, by rfl⟩ : syracuseStep 605701 = 113569) (by norm_num)
theorem B1326653 : Blo 587289 1326653 := bbase (se 3 (by rfl) ⟨248747, by rfl⟩ : syracuseStep 1326653 = 497495) (by norm_num)
theorem B1490501 : Blo 587289 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B1261165 : Blo 587289 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B1326725 : Blo 587289 1326725 := bbase (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) (by norm_num)
theorem B1326797 : Blo 587289 1326797 := bbase (se 3 (by rfl) ⟨248774, by rfl⟩ : syracuseStep 1326797 = 497549) (by norm_num)
theorem B1326869 : Blo 587289 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B671557 : Blo 587289 671557 := bbase (se 4 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 671557 = 125917) (by norm_num)
theorem B1326941 : Blo 587289 1326941 := bbase (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) (by norm_num)
theorem B1261421 : Blo 587289 1261421 := bbase (se 3 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 1261421 = 473033) (by norm_num)
theorem B2244469 : Blo 587289 2244469 := bbase (se 5 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 2244469 = 210419) (by norm_num)
theorem B1490845 : Blo 587289 1490845 := bbase (se 3 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 1490845 = 559067) (by norm_num)
theorem B1327013 : Blo 587289 1327013 := bbase (se 4 (by rfl) ⟨124407, by rfl⟩ : syracuseStep 1327013 = 248815) (by norm_num)
theorem B671657 : Blo 587289 671657 := bbase (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) (by norm_num)
theorem B2015189 : Blo 587289 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1327085 : Blo 587289 1327085 := bbase (se 3 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 1327085 = 497657) (by norm_num)
theorem B1490957 : Blo 587289 1490957 := bbase (se 3 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 1490957 = 559109) (by norm_num)
theorem B1982501 : Blo 587289 1982501 := bbase (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) (by norm_num)
theorem B1327157 : Blo 587289 1327157 := bbase (se 5 (by rfl) ⟨62210, by rfl⟩ : syracuseStep 1327157 = 124421) (by norm_num)
theorem B606289 : Blo 587289 606289 := bbase (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) (by norm_num)
theorem B1327229 : Blo 587289 1327229 := bbase (se 3 (by rfl) ⟨248855, by rfl⟩ : syracuseStep 1327229 = 497711) (by norm_num)
theorem B2244773 : Blo 587289 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B1327301 : Blo 587289 1327301 := bbase (se 4 (by rfl) ⟨124434, by rfl⟩ : syracuseStep 1327301 = 248869) (by norm_num)
theorem B1491149 : Blo 587289 1491149 := bbase (se 3 (by rfl) ⟨279590, by rfl⟩ : syracuseStep 1491149 = 559181) (by norm_num)
theorem B1327373 : Blo 587289 1327373 := bbase (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) (by norm_num)
theorem B1589557 : Blo 587289 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1327445 : Blo 587289 1327445 := bbase (se 10 (by rfl) ⟨1944, by rfl⟩ : syracuseStep 1327445 = 3889) (by norm_num)
theorem B6472021 : Blo 587289 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B1589653 : Blo 587289 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1327517 : Blo 587289 1327517 := bbase (se 3 (by rfl) ⟨248909, by rfl⟩ : syracuseStep 1327517 = 497819) (by norm_num)
theorem B1982933 : Blo 587289 1982933 := bbase (se 7 (by rfl) ⟨23237, by rfl⟩ : syracuseStep 1982933 = 46475) (by norm_num)
theorem B1327589 : Blo 587289 1327589 := bbase (se 4 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 1327589 = 248923) (by norm_num)
theorem B1491493 : Blo 587289 1491493 := bbase (se 4 (by rfl) ⟨139827, by rfl⟩ : syracuseStep 1491493 = 279655) (by norm_num)
theorem B1327661 : Blo 587289 1327661 := bbase (se 3 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 1327661 = 497873) (by norm_num)
theorem B1327733 : Blo 587289 1327733 := bbase (se 5 (by rfl) ⟨62237, by rfl⟩ : syracuseStep 1327733 = 124475) (by norm_num)
theorem B1491605 : Blo 587289 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1327805 : Blo 587289 1327805 := bbase (se 3 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 1327805 = 497927) (by norm_num)
theorem B1262309 : Blo 587289 1262309 := bbase (se 4 (by rfl) ⟨118341, by rfl⟩ : syracuseStep 1262309 = 236683) (by norm_num)
theorem B1327877 : Blo 587289 1327877 := bbase (se 4 (by rfl) ⟨124488, by rfl⟩ : syracuseStep 1327877 = 248977) (by norm_num)
theorem B1327949 : Blo 587289 1327949 := bbase (se 3 (by rfl) ⟨248990, by rfl⟩ : syracuseStep 1327949 = 497981) (by norm_num)
theorem B1491797 : Blo 587289 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1983365 : Blo 587289 1983365 := bbase (se 4 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 1983365 = 371881) (by norm_num)
theorem B672661 : Blo 587289 672661 := bbase (se 6 (by rfl) ⟨15765, by rfl⟩ : syracuseStep 672661 = 31531) (by norm_num)
theorem B1328021 : Blo 587289 1328021 := bbase (se 6 (by rfl) ⟨31125, by rfl⟩ : syracuseStep 1328021 = 62251) (by norm_num)
theorem B672725 : Blo 587289 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B1262549 : Blo 587289 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B836573 : Blo 587289 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B1328093 : Blo 587289 1328093 := bbase (se 3 (by rfl) ⟨249017, by rfl⟩ : syracuseStep 1328093 = 498035) (by norm_num)
theorem B1328165 : Blo 587289 1328165 := bbase (se 4 (by rfl) ⟨124515, by rfl⟩ : syracuseStep 1328165 = 249031) (by norm_num)
theorem B1328237 : Blo 587289 1328237 := bbase (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) (by norm_num)
theorem B1492141 : Blo 587289 1492141 := bbase (se 3 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 1492141 = 559553) (by norm_num)
theorem B1328309 : Blo 587289 1328309 := bbase (se 5 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 1328309 = 124529) (by norm_num)
theorem B1328381 : Blo 587289 1328381 := bbase (se 3 (by rfl) ⟨249071, by rfl⟩ : syracuseStep 1328381 = 498143) (by norm_num)
theorem B1492253 : Blo 587289 1492253 := bbase (se 3 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 1492253 = 559595) (by norm_num)
theorem B1361197 : Blo 587289 1361197 := bbase (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) (by norm_num)
theorem B1983797 : Blo 587289 1983797 := bbase (se 5 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 1983797 = 185981) (by norm_num)
theorem B1328453 : Blo 587289 1328453 := bbase (se 4 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 1328453 = 249085) (by norm_num)
theorem B1328525 : Blo 587289 1328525 := bbase (se 3 (by rfl) ⟨249098, by rfl⟩ : syracuseStep 1328525 = 498197) (by norm_num)
theorem B10765781 : Blo 587289 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B1328597 : Blo 587289 1328597 := bbase (se 7 (by rfl) ⟨15569, by rfl⟩ : syracuseStep 1328597 = 31139) (by norm_num)
theorem B1492445 : Blo 587289 1492445 := bbase (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) (by norm_num)
theorem B1328669 : Blo 587289 1328669 := bbase (se 3 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 1328669 = 498251) (by norm_num)
theorem B1590821 : Blo 587289 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B1328741 : Blo 587289 1328741 := bbase (se 4 (by rfl) ⟨124569, by rfl⟩ : syracuseStep 1328741 = 249139) (by norm_num)
theorem B706205 : Blo 587289 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B1328813 : Blo 587289 1328813 := bbase (se 3 (by rfl) ⟨249152, by rfl⟩ : syracuseStep 1328813 = 498305) (by norm_num)
theorem B706253 : Blo 587289 706253 := bbase (se 3 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 706253 = 264845) (by norm_num)
theorem B837325 : Blo 587289 837325 := bbase (se 3 (by rfl) ⟨156998, by rfl⟩ : syracuseStep 837325 = 313997) (by norm_num)
theorem B1984229 : Blo 587289 1984229 := bbase (se 4 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 1984229 = 372043) (by norm_num)
theorem B1328885 : Blo 587289 1328885 := bbase (se 5 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 1328885 = 124583) (by norm_num)
theorem B3786517 : Blo 587289 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B4245301 : Blo 587289 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B1492789 : Blo 587289 1492789 := bbase (se 5 (by rfl) ⟨69974, by rfl⟩ : syracuseStep 1492789 = 139949) (by norm_num)
theorem B1328957 : Blo 587289 1328957 := bbase (se 3 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 1328957 = 498359) (by norm_num)
theorem B1329029 : Blo 587289 1329029 := bbase (se 4 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 1329029 = 249193) (by norm_num)
theorem B1492901 : Blo 587289 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1329101 : Blo 587289 1329101 := bbase (se 3 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 1329101 = 498413) (by norm_num)
theorem B1329173 : Blo 587289 1329173 := bbase (se 6 (by rfl) ⟨31152, by rfl⟩ : syracuseStep 1329173 = 62305) (by norm_num)
theorem B1329245 : Blo 587289 1329245 := bbase (se 3 (by rfl) ⟨249233, by rfl⟩ : syracuseStep 1329245 = 498467) (by norm_num)
theorem B1493093 : Blo 587289 1493093 := bbase (se 4 (by rfl) ⟨139977, by rfl⟩ : syracuseStep 1493093 = 279955) (by norm_num)
theorem B1984661 : Blo 587289 1984661 := bbase (se 6 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 1984661 = 93031) (by norm_num)
theorem B1329317 : Blo 587289 1329317 := bbase (se 4 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 1329317 = 249247) (by norm_num)
theorem B1329389 : Blo 587289 1329389 := bbase (se 3 (by rfl) ⟨249260, by rfl⟩ : syracuseStep 1329389 = 498521) (by norm_num)
theorem B706801 : Blo 587289 706801 := bbase (se 2 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 706801 = 530101) (by norm_num)
theorem B674065 : Blo 587289 674065 := bbase (se 2 (by rfl) ⟨252774, by rfl⟩ : syracuseStep 674065 = 505549) (by norm_num)
theorem B1329461 : Blo 587289 1329461 := bbase (se 5 (by rfl) ⟨62318, by rfl⟩ : syracuseStep 1329461 = 124637) (by norm_num)
theorem B2509157 : Blo 587289 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B1329533 : Blo 587289 1329533 := bbase (se 3 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 1329533 = 498575) (by norm_num)
theorem B1198469 : Blo 587289 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B674185 : Blo 587289 674185 := bbase (se 2 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 674185 = 505639) (by norm_num)
theorem B1493437 : Blo 587289 1493437 := bbase (se 3 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 1493437 = 560039) (by norm_num)
theorem B1329605 : Blo 587289 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B838117 : Blo 587289 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B1329677 : Blo 587289 1329677 := bbase (se 3 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 1329677 = 498629) (by norm_num)
theorem B1493549 : Blo 587289 1493549 := bbase (se 3 (by rfl) ⟨280040, by rfl⟩ : syracuseStep 1493549 = 560081) (by norm_num)
theorem B2837045 : Blo 587289 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B1985093 : Blo 587289 1985093 := bbase (se 4 (by rfl) ⟨186102, by rfl⟩ : syracuseStep 1985093 = 372205) (by norm_num)
theorem B1886789 : Blo 587289 1886789 := bbase (se 4 (by rfl) ⟨176886, by rfl⟩ : syracuseStep 1886789 = 353773) (by norm_num)
theorem B1329749 : Blo 587289 1329749 := bbase (se 8 (by rfl) ⟨7791, by rfl⟩ : syracuseStep 1329749 = 15583) (by norm_num)
theorem B1329821 : Blo 587289 1329821 := bbase (se 3 (by rfl) ⟨249341, by rfl⟩ : syracuseStep 1329821 = 498683) (by norm_num)
theorem B4475573 : Blo 587289 4475573 := bbase (se 5 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 4475573 = 419585) (by norm_num)
theorem B707281 : Blo 587289 707281 := bbase (se 2 (by rfl) ⟨265230, by rfl⟩ : syracuseStep 707281 = 530461) (by norm_num)
theorem B1329893 : Blo 587289 1329893 := bbase (se 4 (by rfl) ⟨124677, by rfl⟩ : syracuseStep 1329893 = 249355) (by norm_num)
theorem B1493741 : Blo 587289 1493741 := bbase (se 3 (by rfl) ⟨280076, by rfl⟩ : syracuseStep 1493741 = 560153) (by norm_num)
theorem B1723141 : Blo 587289 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B1329965 : Blo 587289 1329965 := bbase (se 3 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 1329965 = 498737) (by norm_num)
theorem B838453 : Blo 587289 838453 := bbase (se 5 (by rfl) ⟨39302, by rfl⟩ : syracuseStep 838453 = 78605) (by norm_num)
theorem B1330037 : Blo 587289 1330037 := bbase (se 5 (by rfl) ⟨62345, by rfl⟩ : syracuseStep 1330037 = 124691) (by norm_num)
theorem B1330109 : Blo 587289 1330109 := bbase (se 3 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 1330109 = 498791) (by norm_num)
theorem B674777 : Blo 587289 674777 := bbase (se 2 (by rfl) ⟨253041, by rfl⟩ : syracuseStep 674777 = 506083) (by norm_num)
theorem B1985525 : Blo 587289 1985525 := bbase (se 5 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 1985525 = 186143) (by norm_num)
theorem B1330181 : Blo 587289 1330181 := bbase (se 4 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 1330181 = 249409) (by norm_num)
theorem B838669 : Blo 587289 838669 := bbase (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) (by norm_num)
theorem B1494085 : Blo 587289 1494085 := bbase (se 4 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 1494085 = 280141) (by norm_num)
theorem B1330253 : Blo 587289 1330253 := bbase (se 3 (by rfl) ⟨249422, by rfl⟩ : syracuseStep 1330253 = 498845) (by norm_num)
theorem B1264765 : Blo 587289 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B3591317 : Blo 587289 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1330325 : Blo 587289 1330325 := bbase (se 6 (by rfl) ⟨31179, by rfl⟩ : syracuseStep 1330325 = 62359) (by norm_num)
theorem B1494197 : Blo 587289 1494197 := bbase (se 5 (by rfl) ⟨70040, by rfl⟩ : syracuseStep 1494197 = 140081) (by norm_num)
theorem B1330397 : Blo 587289 1330397 := bbase (se 3 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 1330397 = 498899) (by norm_num)
theorem B1363213 : Blo 587289 1363213 := bbase (se 3 (by rfl) ⟨255602, by rfl⟩ : syracuseStep 1363213 = 511205) (by norm_num)
theorem B1789285 : Blo 587289 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B1494389 : Blo 587289 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B839045 : Blo 587289 839045 := bbase (se 4 (by rfl) ⟨78660, by rfl⟩ : syracuseStep 839045 = 157321) (by norm_num)
theorem B1985957 : Blo 587289 1985957 := bbase (se 4 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 1985957 = 372367) (by norm_num)
theorem B708161 : Blo 587289 708161 := bbase (se 2 (by rfl) ⟨265560, by rfl⟩ : syracuseStep 708161 = 531121) (by norm_num)
theorem B3624533 : Blo 587289 3624533 := bbase (se 8 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 3624533 = 42475) (by norm_num)
theorem B1887877 : Blo 587289 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B708277 : Blo 587289 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B1494733 : Blo 587289 1494733 := bbase (se 3 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 1494733 = 560525) (by norm_num)
theorem B1494845 : Blo 587289 1494845 := bbase (se 3 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 1494845 = 560567) (by norm_num)
theorem B1986389 : Blo 587289 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B708473 : Blo 587289 708473 := bbase (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) (by norm_num)
theorem B3362741 : Blo 587289 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B7655381 : Blo 587289 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B1495037 : Blo 587289 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1593589 : Blo 587289 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1986821 : Blo 587289 1986821 := bbase (se 4 (by rfl) ⟨186264, by rfl⟩ : syracuseStep 1986821 = 372529) (by norm_num)
theorem B1495381 : Blo 587289 1495381 := bbase (se 10 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 1495381 = 4381) (by norm_num)
theorem B709021 : Blo 587289 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B1495493 : Blo 587289 1495493 := bbase (se 4 (by rfl) ⟨140202, by rfl⟩ : syracuseStep 1495493 = 280405) (by norm_num)
theorem B709165 : Blo 587289 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B1495685 : Blo 587289 1495685 := bbase (se 4 (by rfl) ⟨140220, by rfl⟩ : syracuseStep 1495685 = 280441) (by norm_num)
theorem B1987253 : Blo 587289 1987253 := bbase (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) (by norm_num)
theorem B1889045 : Blo 587289 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B840469 : Blo 587289 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B1496029 : Blo 587289 1496029 := bbase (se 3 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 1496029 = 561011) (by norm_num)
theorem B906277 : Blo 587289 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B1791013 : Blo 587289 1791013 := bbase (se 4 (by rfl) ⟨167907, by rfl⟩ : syracuseStep 1791013 = 335815) (by norm_num)
theorem B1496141 : Blo 587289 1496141 := bbase (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) (by norm_num)
theorem B1987685 : Blo 587289 1987685 := bbase (se 4 (by rfl) ⟨186345, by rfl⟩ : syracuseStep 1987685 = 372691) (by norm_num)
theorem B1135885 : Blo 587289 1135885 := bbase (se 3 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 1135885 = 425957) (by norm_num)
theorem B1496333 : Blo 587289 1496333 := bbase (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) (by norm_num)
theorem B841061 : Blo 587289 841061 := bbase (se 4 (by rfl) ⟨78849, by rfl⟩ : syracuseStep 841061 = 157699) (by norm_num)
theorem B841141 : Blo 587289 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B1529309 : Blo 587289 1529309 := bbase (se 3 (by rfl) ⟨286745, by rfl⟩ : syracuseStep 1529309 = 573491) (by norm_num)
theorem B1988117 : Blo 587289 1988117 := bbase (se 6 (by rfl) ⟨46596, by rfl⟩ : syracuseStep 1988117 = 93193) (by norm_num)
theorem B841261 : Blo 587289 841261 := bbase (se 3 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 841261 = 315473) (by norm_num)
theorem B2512453 : Blo 587289 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B710213 : Blo 587289 710213 := bbase (se 4 (by rfl) ⟨66582, by rfl⟩ : syracuseStep 710213 = 133165) (by norm_num)
theorem B1365581 : Blo 587289 1365581 := bbase (se 3 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 1365581 = 512093) (by norm_num)
theorem B1496677 : Blo 587289 1496677 := bbase (se 4 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 1496677 = 280627) (by norm_num)
theorem B841357 : Blo 587289 841357 := bbase (se 3 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 841357 = 315509) (by norm_num)
theorem B10082069 : Blo 587289 10082069 := bbase (se 6 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 10082069 = 472597) (by norm_num)
theorem B1595189 : Blo 587289 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B743357 : Blo 587289 743357 := bbase (se 3 (by rfl) ⟨139379, by rfl⟩ : syracuseStep 743357 = 278759) (by norm_num)
theorem B1988549 : Blo 587289 1988549 := bbase (se 4 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 1988549 = 372853) (by norm_num)
theorem B743413 : Blo 587289 743413 := bbase (se 5 (by rfl) ⟨34847, by rfl⟩ : syracuseStep 743413 = 69695) (by norm_num)
theorem B2414645 : Blo 587289 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B2021429 : Blo 587289 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B743509 : Blo 587289 743509 := bbase (se 8 (by rfl) ⟨4356, by rfl⟩ : syracuseStep 743509 = 8713) (by norm_num)
theorem B841853 : Blo 587289 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B743681 : Blo 587289 743681 := bbase (se 2 (by rfl) ⟨278880, by rfl⟩ : syracuseStep 743681 = 557761) (by norm_num)
theorem B1136933 : Blo 587289 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B743737 : Blo 587289 743737 := bbase (se 2 (by rfl) ⟨278901, by rfl⟩ : syracuseStep 743737 = 557803) (by norm_num)
theorem B1988981 : Blo 587289 1988981 := bbase (se 5 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 1988981 = 186467) (by norm_num)
theorem B11295125 : Blo 587289 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B743833 : Blo 587289 743833 := bbase (se 2 (by rfl) ⟨278937, by rfl⟩ : syracuseStep 743833 = 557875) (by norm_num)
theorem B744005 : Blo 587289 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B1890901 : Blo 587289 1890901 := bbase (se 8 (by rfl) ⟨11079, by rfl⟩ : syracuseStep 1890901 = 22159) (by norm_num)
theorem B744061 : Blo 587289 744061 := bbase (se 3 (by rfl) ⟨139511, by rfl⟩ : syracuseStep 744061 = 279023) (by norm_num)
theorem B744157 : Blo 587289 744157 := bbase (se 3 (by rfl) ⟨139529, by rfl⟩ : syracuseStep 744157 = 279059) (by norm_num)
theorem B1989413 : Blo 587289 1989413 := bbase (se 4 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 1989413 = 373015) (by norm_num)
theorem B744329 : Blo 587289 744329 := bbase (se 2 (by rfl) ⟨279123, by rfl⟩ : syracuseStep 744329 = 558247) (by norm_num)
theorem B1006501 : Blo 587289 1006501 := bbase (se 4 (by rfl) ⟨94359, by rfl⟩ : syracuseStep 1006501 = 188719) (by norm_num)
theorem B744385 : Blo 587289 744385 := bbase (se 2 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 744385 = 558289) (by norm_num)
theorem B744481 : Blo 587289 744481 := bbase (se 2 (by rfl) ⟨279180, by rfl⟩ : syracuseStep 744481 = 558361) (by norm_num)
theorem B1432733 : Blo 587289 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B744653 : Blo 587289 744653 := bbase (se 3 (by rfl) ⟨139622, by rfl⟩ : syracuseStep 744653 = 279245) (by norm_num)
theorem B1989845 : Blo 587289 1989845 := bbase (se 7 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 1989845 = 46637) (by norm_num)
theorem B744709 : Blo 587289 744709 := bbase (se 4 (by rfl) ⟨69816, by rfl⟩ : syracuseStep 744709 = 139633) (by norm_num)
theorem B4545877 : Blo 587289 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B744805 : Blo 587289 744805 := bbase (se 4 (by rfl) ⟨69825, by rfl⟩ : syracuseStep 744805 = 139651) (by norm_num)
theorem B941453 : Blo 587289 941453 := bbase (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) (by norm_num)
theorem B941549 : Blo 587289 941549 := bbase (se 3 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 941549 = 353081) (by norm_num)
theorem B941581 : Blo 587289 941581 := bbase (se 3 (by rfl) ⟨176546, by rfl⟩ : syracuseStep 941581 = 353093) (by norm_num)
theorem B744977 : Blo 587289 744977 := bbase (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) (by norm_num)
theorem B745033 : Blo 587289 745033 := bbase (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) (by norm_num)
theorem B1990277 : Blo 587289 1990277 := bbase (se 4 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 1990277 = 373177) (by norm_num)
theorem B1793701 : Blo 587289 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B745129 : Blo 587289 745129 := bbase (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) (by norm_num)
theorem B679657 : Blo 587289 679657 := bbase (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) (by norm_num)
theorem B2973509 : Blo 587289 2973509 := bbase (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) (by norm_num)
theorem B745301 : Blo 587289 745301 := bbase (se 9 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 745301 = 4367) (by norm_num)
theorem B5103445 : Blo 587289 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B745357 : Blo 587289 745357 := bbase (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) (by norm_num)
theorem B2547605 : Blo 587289 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B1892261 : Blo 587289 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B745453 : Blo 587289 745453 := bbase (se 3 (by rfl) ⟨139772, by rfl⟩ : syracuseStep 745453 = 279545) (by norm_num)
theorem B1990709 : Blo 587289 1990709 := bbase (se 5 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 1990709 = 186629) (by norm_num)
theorem B1531973 : Blo 587289 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B745625 : Blo 587289 745625 := bbase (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) (by norm_num)
theorem B745681 : Blo 587289 745681 := bbase (se 2 (by rfl) ⟨279630, by rfl⟩ : syracuseStep 745681 = 559261) (by norm_num)
theorem B745777 : Blo 587289 745777 := bbase (se 2 (by rfl) ⟨279666, by rfl⟩ : syracuseStep 745777 = 559333) (by norm_num)
theorem B745949 : Blo 587289 745949 := bbase (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) (by norm_num)
theorem B1991141 : Blo 587289 1991141 := bbase (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) (by norm_num)
theorem B2515445 : Blo 587289 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B746005 : Blo 587289 746005 := bbase (se 6 (by rfl) ⟨17484, by rfl⟩ : syracuseStep 746005 = 34969) (by norm_num)
theorem B746101 : Blo 587289 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B746273 : Blo 587289 746273 := bbase (se 2 (by rfl) ⟨279852, by rfl⟩ : syracuseStep 746273 = 559705) (by norm_num)
theorem B746329 : Blo 587289 746329 := bbase (se 2 (by rfl) ⟨279873, by rfl⟩ : syracuseStep 746329 = 559747) (by norm_num)
theorem B2384741 : Blo 587289 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B1991573 : Blo 587289 1991573 := bbase (se 6 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 1991573 = 93355) (by norm_num)
theorem B746425 : Blo 587289 746425 := bbase (se 2 (by rfl) ⟨279909, by rfl⟩ : syracuseStep 746425 = 559819) (by norm_num)
theorem B943093 : Blo 587289 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B2974805 : Blo 587289 2974805 := bbase (se 8 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 2974805 = 34861) (by norm_num)
theorem B746597 : Blo 587289 746597 := bbase (se 4 (by rfl) ⟨69993, by rfl⟩ : syracuseStep 746597 = 139987) (by norm_num)
theorem B746653 : Blo 587289 746653 := bbase (se 3 (by rfl) ⟨139997, by rfl⟩ : syracuseStep 746653 = 279995) (by norm_num)
theorem B746749 : Blo 587289 746749 := bbase (se 3 (by rfl) ⟨140015, by rfl⟩ : syracuseStep 746749 = 280031) (by norm_num)
theorem B1992005 : Blo 587289 1992005 := bbase (se 4 (by rfl) ⟨186750, by rfl⟩ : syracuseStep 1992005 = 373501) (by norm_num)
theorem B746921 : Blo 587289 746921 := bbase (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) (by norm_num)
theorem B746977 : Blo 587289 746977 := bbase (se 2 (by rfl) ⟨280116, by rfl⟩ : syracuseStep 746977 = 560233) (by norm_num)
theorem B2516453 : Blo 587289 2516453 := bbase (se 4 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 2516453 = 471835) (by norm_num)
theorem B1533421 : Blo 587289 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B747073 : Blo 587289 747073 := bbase (se 2 (by rfl) ⟨280152, by rfl⟩ : syracuseStep 747073 = 560305) (by norm_num)
theorem B5662325 : Blo 587289 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B943805 : Blo 587289 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B747245 : Blo 587289 747245 := bbase (se 3 (by rfl) ⟨140108, by rfl⟩ : syracuseStep 747245 = 280217) (by norm_num)
theorem B1992437 : Blo 587289 1992437 := bbase (se 5 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 1992437 = 186791) (by norm_num)
theorem B747301 : Blo 587289 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B747397 : Blo 587289 747397 := bbase (se 4 (by rfl) ⟨70068, by rfl⟩ : syracuseStep 747397 = 140137) (by norm_num)
theorem B1697813 : Blo 587289 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B747569 : Blo 587289 747569 := bbase (se 2 (by rfl) ⟨280338, by rfl⟩ : syracuseStep 747569 = 560677) (by norm_num)
theorem B1009757 : Blo 587289 1009757 := bbase (se 3 (by rfl) ⟨189329, by rfl⟩ : syracuseStep 1009757 = 378659) (by norm_num)
theorem B747625 : Blo 587289 747625 := bbase (se 2 (by rfl) ⟨280359, by rfl⟩ : syracuseStep 747625 = 560719) (by norm_num)
theorem B2386037 : Blo 587289 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B2418853 : Blo 587289 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B1992869 : Blo 587289 1992869 := bbase (se 4 (by rfl) ⟨186831, by rfl⟩ : syracuseStep 1992869 = 373663) (by norm_num)
theorem B747721 : Blo 587289 747721 := bbase (se 2 (by rfl) ⟨280395, by rfl⟩ : syracuseStep 747721 = 560791) (by norm_num)
theorem B4483349 : Blo 587289 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B944477 : Blo 587289 944477 := bbase (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) (by norm_num)
theorem B2976101 : Blo 587289 2976101 := bbase (se 4 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 2976101 = 558019) (by norm_num)
theorem B747893 : Blo 587289 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B747949 : Blo 587289 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B1272277 : Blo 587289 1272277 := bbase (se 7 (by rfl) ⟨14909, by rfl⟩ : syracuseStep 1272277 = 29819) (by norm_num)
theorem B748045 : Blo 587289 748045 := bbase (se 3 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 748045 = 280517) (by norm_num)
theorem B3074597 : Blo 587289 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B1993301 : Blo 587289 1993301 := bbase (se 8 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 1993301 = 23359) (by norm_num)
theorem B748217 : Blo 587289 748217 := bbase (se 2 (by rfl) ⟨280581, by rfl⟩ : syracuseStep 748217 = 561163) (by norm_num)
theorem B748273 : Blo 587289 748273 := bbase (se 2 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 748273 = 561205) (by norm_num)
theorem B944989 : Blo 587289 944989 := bbase (se 3 (by rfl) ⟨177185, by rfl⟩ : syracuseStep 944989 = 354371) (by norm_num)
theorem B1993733 : Blo 587289 1993733 := bbase (se 4 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 1993733 = 373825) (by norm_num)
theorem B1436741 : Blo 587289 1436741 := bbase (se 4 (by rfl) ⟨134694, by rfl⟩ : syracuseStep 1436741 = 269389) (by norm_num)
theorem B2518229 : Blo 587289 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B945445 : Blo 587289 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B1994165 : Blo 587289 1994165 := bbase (se 5 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 1994165 = 186953) (by norm_num)
theorem B2977397 : Blo 587289 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B1994597 : Blo 587289 1994597 := bbase (se 4 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 1994597 = 373987) (by norm_num)
theorem B946117 : Blo 587289 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B1274077 : Blo 587289 1274077 := bbase (se 3 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 1274077 = 477779) (by norm_num)
theorem B1995029 : Blo 587289 1995029 := bbase (se 6 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 1995029 = 93517) (by norm_num)
theorem B880949 : Blo 587289 880949 := bbase (se 5 (by rfl) ⟨41294, by rfl⟩ : syracuseStep 880949 = 82589) (by norm_num)
theorem B880973 : Blo 587289 880973 := bbase (se 3 (by rfl) ⟨165182, by rfl⟩ : syracuseStep 880973 = 330365) (by norm_num)
theorem B880997 : Blo 587289 880997 := bbase (se 4 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 880997 = 165187) (by norm_num)
theorem B946541 : Blo 587289 946541 := bbase (se 3 (by rfl) ⟨177476, by rfl⟩ : syracuseStep 946541 = 354953) (by norm_num)
theorem B881021 : Blo 587289 881021 := bbase (se 3 (by rfl) ⟨165191, by rfl⟩ : syracuseStep 881021 = 330383) (by norm_num)
theorem B881045 : Blo 587289 881045 := bbase (se 6 (by rfl) ⟨20649, by rfl⟩ : syracuseStep 881045 = 41299) (by norm_num)
theorem B881069 : Blo 587289 881069 := bbase (se 3 (by rfl) ⟨165200, by rfl⟩ : syracuseStep 881069 = 330401) (by norm_num)
theorem B881093 : Blo 587289 881093 := bbase (se 4 (by rfl) ⟨82602, by rfl⟩ : syracuseStep 881093 = 165205) (by norm_num)
theorem B881117 : Blo 587289 881117 := bbase (se 3 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 881117 = 330419) (by norm_num)
theorem B881141 : Blo 587289 881141 := bbase (se 5 (by rfl) ⟨41303, by rfl⟩ : syracuseStep 881141 = 82607) (by norm_num)
theorem B2126341 : Blo 587289 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B881165 : Blo 587289 881165 := bbase (se 3 (by rfl) ⟨165218, by rfl⟩ : syracuseStep 881165 = 330437) (by norm_num)
theorem B881189 : Blo 587289 881189 := bbase (se 4 (by rfl) ⟨82611, by rfl⟩ : syracuseStep 881189 = 165223) (by norm_num)
theorem B881213 : Blo 587289 881213 := bbase (se 3 (by rfl) ⟨165227, by rfl⟩ : syracuseStep 881213 = 330455) (by norm_num)
theorem B881237 : Blo 587289 881237 := bbase (se 8 (by rfl) ⟨5163, by rfl⟩ : syracuseStep 881237 = 10327) (by norm_num)
theorem B881261 : Blo 587289 881261 := bbase (se 3 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 881261 = 330473) (by norm_num)
theorem B881285 : Blo 587289 881285 := bbase (se 4 (by rfl) ⟨82620, by rfl⟩ : syracuseStep 881285 = 165241) (by norm_num)
theorem B946829 : Blo 587289 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B881309 : Blo 587289 881309 := bbase (se 3 (by rfl) ⟨165245, by rfl⟩ : syracuseStep 881309 = 330491) (by norm_num)
theorem B2552485 : Blo 587289 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B881333 : Blo 587289 881333 := bbase (se 5 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 881333 = 82625) (by norm_num)
theorem B1995461 : Blo 587289 1995461 := bbase (se 4 (by rfl) ⟨187074, by rfl⟩ : syracuseStep 1995461 = 374149) (by norm_num)
theorem B881357 : Blo 587289 881357 := bbase (se 3 (by rfl) ⟨165254, by rfl⟩ : syracuseStep 881357 = 330509) (by norm_num)
theorem B881381 : Blo 587289 881381 := bbase (se 4 (by rfl) ⟨82629, by rfl⟩ : syracuseStep 881381 = 165259) (by norm_num)
theorem B881405 : Blo 587289 881405 := bbase (se 3 (by rfl) ⟨165263, by rfl⟩ : syracuseStep 881405 = 330527) (by norm_num)
theorem B881429 : Blo 587289 881429 := bbase (se 6 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 881429 = 41317) (by norm_num)
theorem B881453 : Blo 587289 881453 := bbase (se 3 (by rfl) ⟨165272, by rfl⟩ : syracuseStep 881453 = 330545) (by norm_num)
theorem B881477 : Blo 587289 881477 := bbase (se 4 (by rfl) ⟨82638, by rfl⟩ : syracuseStep 881477 = 165277) (by norm_num)
theorem B881501 : Blo 587289 881501 := bbase (se 3 (by rfl) ⟨165281, by rfl⟩ : syracuseStep 881501 = 330563) (by norm_num)
theorem B881525 : Blo 587289 881525 := bbase (se 5 (by rfl) ⟨41321, by rfl⟩ : syracuseStep 881525 = 82643) (by norm_num)
theorem B2978693 : Blo 587289 2978693 := bbase (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) (by norm_num)
theorem B881549 : Blo 587289 881549 := bbase (se 3 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 881549 = 330581) (by norm_num)
theorem B881573 : Blo 587289 881573 := bbase (se 4 (by rfl) ⟨82647, by rfl⟩ : syracuseStep 881573 = 165295) (by norm_num)
theorem B881597 : Blo 587289 881597 := bbase (se 3 (by rfl) ⟨165299, by rfl⟩ : syracuseStep 881597 = 330599) (by norm_num)
theorem B881621 : Blo 587289 881621 := bbase (se 7 (by rfl) ⟨10331, by rfl⟩ : syracuseStep 881621 = 20663) (by norm_num)
theorem B881645 : Blo 587289 881645 := bbase (se 3 (by rfl) ⟨165308, by rfl⟩ : syracuseStep 881645 = 330617) (by norm_num)
theorem B881669 : Blo 587289 881669 := bbase (se 4 (by rfl) ⟨82656, by rfl⟩ : syracuseStep 881669 = 165313) (by norm_num)
theorem B881693 : Blo 587289 881693 := bbase (se 3 (by rfl) ⟨165317, by rfl⟩ : syracuseStep 881693 = 330635) (by norm_num)
theorem B881717 : Blo 587289 881717 := bbase (se 5 (by rfl) ⟨41330, by rfl⟩ : syracuseStep 881717 = 82661) (by norm_num)
theorem B881741 : Blo 587289 881741 := bbase (se 3 (by rfl) ⟨165326, by rfl⟩ : syracuseStep 881741 = 330653) (by norm_num)
theorem B881765 : Blo 587289 881765 := bbase (se 4 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 881765 = 165331) (by norm_num)
theorem B881789 : Blo 587289 881789 := bbase (se 3 (by rfl) ⟨165335, by rfl⟩ : syracuseStep 881789 = 330671) (by norm_num)
theorem B881813 : Blo 587289 881813 := bbase (se 6 (by rfl) ⟨20667, by rfl⟩ : syracuseStep 881813 = 41335) (by norm_num)
theorem B881837 : Blo 587289 881837 := bbase (se 3 (by rfl) ⟨165344, by rfl⟩ : syracuseStep 881837 = 330689) (by norm_num)
theorem B881861 : Blo 587289 881861 := bbase (se 4 (by rfl) ⟨82674, by rfl⟩ : syracuseStep 881861 = 165349) (by norm_num)
theorem B881885 : Blo 587289 881885 := bbase (se 3 (by rfl) ⟨165353, by rfl⟩ : syracuseStep 881885 = 330707) (by norm_num)
theorem B881909 : Blo 587289 881909 := bbase (se 5 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 881909 = 82679) (by norm_num)
theorem B881933 : Blo 587289 881933 := bbase (se 3 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 881933 = 330725) (by norm_num)
theorem B881957 : Blo 587289 881957 := bbase (se 4 (by rfl) ⟨82683, by rfl⟩ : syracuseStep 881957 = 165367) (by norm_num)
theorem B881981 : Blo 587289 881981 := bbase (se 3 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 881981 = 330743) (by norm_num)
theorem B882005 : Blo 587289 882005 := bbase (se 13 (by rfl) ⟨161, by rfl⟩ : syracuseStep 882005 = 323) (by norm_num)
theorem B882029 : Blo 587289 882029 := bbase (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) (by norm_num)
theorem B882053 : Blo 587289 882053 := bbase (se 4 (by rfl) ⟨82692, by rfl⟩ : syracuseStep 882053 = 165385) (by norm_num)
theorem B882077 : Blo 587289 882077 := bbase (se 3 (by rfl) ⟨165389, by rfl⟩ : syracuseStep 882077 = 330779) (by norm_num)
theorem B882101 : Blo 587289 882101 := bbase (se 5 (by rfl) ⟨41348, by rfl⟩ : syracuseStep 882101 = 82697) (by norm_num)
theorem B882125 : Blo 587289 882125 := bbase (se 3 (by rfl) ⟨165398, by rfl⟩ : syracuseStep 882125 = 330797) (by norm_num)
theorem B882149 : Blo 587289 882149 := bbase (se 4 (by rfl) ⟨82701, by rfl⟩ : syracuseStep 882149 = 165403) (by norm_num)
theorem B4257269 : Blo 587289 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B882173 : Blo 587289 882173 := bbase (se 3 (by rfl) ⟨165407, by rfl⟩ : syracuseStep 882173 = 330815) (by norm_num)
theorem B882197 : Blo 587289 882197 := bbase (se 6 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 882197 = 41353) (by norm_num)
theorem B882221 : Blo 587289 882221 := bbase (se 3 (by rfl) ⟨165416, by rfl⟩ : syracuseStep 882221 = 330833) (by norm_num)
theorem B882245 : Blo 587289 882245 := bbase (se 4 (by rfl) ⟨82710, by rfl⟩ : syracuseStep 882245 = 165421) (by norm_num)
theorem B882269 : Blo 587289 882269 := bbase (se 3 (by rfl) ⟨165425, by rfl⟩ : syracuseStep 882269 = 330851) (by norm_num)
theorem B882293 : Blo 587289 882293 := bbase (se 5 (by rfl) ⟨41357, by rfl⟩ : syracuseStep 882293 = 82715) (by norm_num)
theorem B1341053 : Blo 587289 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B1275517 : Blo 587289 1275517 := bbase (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) (by norm_num)
theorem B882317 : Blo 587289 882317 := bbase (se 3 (by rfl) ⟨165434, by rfl⟩ : syracuseStep 882317 = 330869) (by norm_num)
theorem B882341 : Blo 587289 882341 := bbase (se 4 (by rfl) ⟨82719, by rfl⟩ : syracuseStep 882341 = 165439) (by norm_num)
theorem B882365 : Blo 587289 882365 := bbase (se 3 (by rfl) ⟨165443, by rfl⟩ : syracuseStep 882365 = 330887) (by norm_num)
theorem B882389 : Blo 587289 882389 := bbase (se 7 (by rfl) ⟨10340, by rfl⟩ : syracuseStep 882389 = 20681) (by norm_num)
theorem B882413 : Blo 587289 882413 := bbase (se 3 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 882413 = 330905) (by norm_num)
theorem B882437 : Blo 587289 882437 := bbase (se 4 (by rfl) ⟨82728, by rfl⟩ : syracuseStep 882437 = 165457) (by norm_num)
theorem B882461 : Blo 587289 882461 := bbase (se 3 (by rfl) ⟨165461, by rfl⟩ : syracuseStep 882461 = 330923) (by norm_num)
theorem B882485 : Blo 587289 882485 := bbase (se 5 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 882485 = 82733) (by norm_num)
theorem B882509 : Blo 587289 882509 := bbase (se 3 (by rfl) ⟨165470, by rfl⟩ : syracuseStep 882509 = 330941) (by norm_num)
theorem B882533 : Blo 587289 882533 := bbase (se 4 (by rfl) ⟨82737, by rfl⟩ : syracuseStep 882533 = 165475) (by norm_num)
theorem B882557 : Blo 587289 882557 := bbase (se 3 (by rfl) ⟨165479, by rfl⟩ : syracuseStep 882557 = 330959) (by norm_num)
theorem B882581 : Blo 587289 882581 := bbase (se 6 (by rfl) ⟨20685, by rfl⟩ : syracuseStep 882581 = 41371) (by norm_num)
theorem B882605 : Blo 587289 882605 := bbase (se 3 (by rfl) ⟨165488, by rfl⟩ : syracuseStep 882605 = 330977) (by norm_num)
theorem B882629 : Blo 587289 882629 := bbase (se 4 (by rfl) ⟨82746, by rfl⟩ : syracuseStep 882629 = 165493) (by norm_num)
theorem B882653 : Blo 587289 882653 := bbase (se 3 (by rfl) ⟨165497, by rfl⟩ : syracuseStep 882653 = 330995) (by norm_num)
theorem B882677 : Blo 587289 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B882701 : Blo 587289 882701 := bbase (se 3 (by rfl) ⟨165506, by rfl⟩ : syracuseStep 882701 = 331013) (by norm_num)
theorem B882725 : Blo 587289 882725 := bbase (se 4 (by rfl) ⟨82755, by rfl⟩ : syracuseStep 882725 = 165511) (by norm_num)
theorem B882749 : Blo 587289 882749 := bbase (se 3 (by rfl) ⟨165515, by rfl⟩ : syracuseStep 882749 = 331031) (by norm_num)
theorem B882773 : Blo 587289 882773 := bbase (se 8 (by rfl) ⟨5172, by rfl⟩ : syracuseStep 882773 = 10345) (by norm_num)
theorem B882797 : Blo 587289 882797 := bbase (se 3 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 882797 = 331049) (by norm_num)
theorem B882821 : Blo 587289 882821 := bbase (se 4 (by rfl) ⟨82764, by rfl⟩ : syracuseStep 882821 = 165529) (by norm_num)
theorem B8485013 : Blo 587289 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B2979989 : Blo 587289 2979989 := bbase (se 6 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 2979989 = 139687) (by norm_num)
theorem B882845 : Blo 587289 882845 := bbase (se 3 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 882845 = 331067) (by norm_num)
theorem B882869 : Blo 587289 882869 := bbase (se 5 (by rfl) ⟨41384, by rfl⟩ : syracuseStep 882869 = 82769) (by norm_num)
theorem B882893 : Blo 587289 882893 := bbase (se 3 (by rfl) ⟨165542, by rfl⟩ : syracuseStep 882893 = 331085) (by norm_num)
theorem B882917 : Blo 587289 882917 := bbase (se 4 (by rfl) ⟨82773, by rfl⟩ : syracuseStep 882917 = 165547) (by norm_num)
theorem B6027509 : Blo 587289 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B882941 : Blo 587289 882941 := bbase (se 3 (by rfl) ⟨165551, by rfl⟩ : syracuseStep 882941 = 331103) (by norm_num)
theorem B882965 : Blo 587289 882965 := bbase (se 6 (by rfl) ⟨20694, by rfl⟩ : syracuseStep 882965 = 41389) (by norm_num)
theorem B882989 : Blo 587289 882989 := bbase (se 3 (by rfl) ⟨165560, by rfl⟩ : syracuseStep 882989 = 331121) (by norm_num)
theorem B883013 : Blo 587289 883013 := bbase (se 4 (by rfl) ⟨82782, by rfl⟩ : syracuseStep 883013 = 165565) (by norm_num)
theorem B883037 : Blo 587289 883037 := bbase (se 3 (by rfl) ⟨165569, by rfl⟩ : syracuseStep 883037 = 331139) (by norm_num)
theorem B883061 : Blo 587289 883061 := bbase (se 5 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 883061 = 82787) (by norm_num)
theorem B883085 : Blo 587289 883085 := bbase (se 3 (by rfl) ⟨165578, by rfl⟩ : syracuseStep 883085 = 331157) (by norm_num)
theorem B883109 : Blo 587289 883109 := bbase (se 4 (by rfl) ⟨82791, by rfl⟩ : syracuseStep 883109 = 165583) (by norm_num)
theorem B883133 : Blo 587289 883133 := bbase (se 3 (by rfl) ⟨165587, by rfl⟩ : syracuseStep 883133 = 331175) (by norm_num)
theorem B883157 : Blo 587289 883157 := bbase (se 7 (by rfl) ⟨10349, by rfl⟩ : syracuseStep 883157 = 20699) (by norm_num)
theorem B883181 : Blo 587289 883181 := bbase (se 3 (by rfl) ⟨165596, by rfl⟩ : syracuseStep 883181 = 331193) (by norm_num)
theorem B883205 : Blo 587289 883205 := bbase (se 4 (by rfl) ⟨82800, by rfl⟩ : syracuseStep 883205 = 165601) (by norm_num)
theorem B883229 : Blo 587289 883229 := bbase (se 3 (by rfl) ⟨165605, by rfl⟩ : syracuseStep 883229 = 331211) (by norm_num)
theorem B883253 : Blo 587289 883253 := bbase (se 5 (by rfl) ⟨41402, by rfl⟩ : syracuseStep 883253 = 82805) (by norm_num)
theorem B883277 : Blo 587289 883277 := bbase (se 3 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 883277 = 331229) (by norm_num)
theorem B8518229 : Blo 587289 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B883301 : Blo 587289 883301 := bbase (se 4 (by rfl) ⟨82809, by rfl⟩ : syracuseStep 883301 = 165619) (by norm_num)
theorem B883325 : Blo 587289 883325 := bbase (se 3 (by rfl) ⟨165623, by rfl⟩ : syracuseStep 883325 = 331247) (by norm_num)
theorem B883349 : Blo 587289 883349 := bbase (se 6 (by rfl) ⟨20703, by rfl⟩ : syracuseStep 883349 = 41407) (by norm_num)
theorem B1079957 : Blo 587289 1079957 := bbase (se 6 (by rfl) ⟨25311, by rfl⟩ : syracuseStep 1079957 = 50623) (by norm_num)
theorem B883373 : Blo 587289 883373 := bbase (se 3 (by rfl) ⟨165632, by rfl⟩ : syracuseStep 883373 = 331265) (by norm_num)
theorem B883397 : Blo 587289 883397 := bbase (se 4 (by rfl) ⟨82818, by rfl⟩ : syracuseStep 883397 = 165637) (by norm_num)
theorem B883421 : Blo 587289 883421 := bbase (se 3 (by rfl) ⟨165641, by rfl⟩ : syracuseStep 883421 = 331283) (by norm_num)
theorem B883445 : Blo 587289 883445 := bbase (se 5 (by rfl) ⟨41411, by rfl⟩ : syracuseStep 883445 = 82823) (by norm_num)
theorem B883469 : Blo 587289 883469 := bbase (se 3 (by rfl) ⟨165650, by rfl⟩ : syracuseStep 883469 = 331301) (by norm_num)
theorem B883493 : Blo 587289 883493 := bbase (se 4 (by rfl) ⟨82827, by rfl⟩ : syracuseStep 883493 = 165655) (by norm_num)
theorem B3767093 : Blo 587289 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B883517 : Blo 587289 883517 := bbase (se 3 (by rfl) ⟨165659, by rfl⟩ : syracuseStep 883517 = 331319) (by norm_num)
theorem B883541 : Blo 587289 883541 := bbase (se 9 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 883541 = 5177) (by norm_num)
theorem B883565 : Blo 587289 883565 := bbase (se 3 (by rfl) ⟨165668, by rfl⟩ : syracuseStep 883565 = 331337) (by norm_num)
theorem B883589 : Blo 587289 883589 := bbase (se 4 (by rfl) ⟨82836, by rfl⟩ : syracuseStep 883589 = 165673) (by norm_num)
theorem B883613 : Blo 587289 883613 := bbase (se 3 (by rfl) ⟨165677, by rfl⟩ : syracuseStep 883613 = 331355) (by norm_num)
theorem B883637 : Blo 587289 883637 := bbase (se 5 (by rfl) ⟨41420, by rfl⟩ : syracuseStep 883637 = 82841) (by norm_num)
theorem B883661 : Blo 587289 883661 := bbase (se 3 (by rfl) ⟨165686, by rfl⟩ : syracuseStep 883661 = 331373) (by norm_num)
theorem B883685 : Blo 587289 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B883709 : Blo 587289 883709 := bbase (se 3 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 883709 = 331391) (by norm_num)
theorem B883733 : Blo 587289 883733 := bbase (se 6 (by rfl) ⟨20712, by rfl⟩ : syracuseStep 883733 = 41425) (by norm_num)
theorem B883757 : Blo 587289 883757 := bbase (se 3 (by rfl) ⟨165704, by rfl⟩ : syracuseStep 883757 = 331409) (by norm_num)
theorem B883781 : Blo 587289 883781 := bbase (se 4 (by rfl) ⟨82854, by rfl⟩ : syracuseStep 883781 = 165709) (by norm_num)
theorem B883805 : Blo 587289 883805 := bbase (se 3 (by rfl) ⟨165713, by rfl⟩ : syracuseStep 883805 = 331427) (by norm_num)
theorem B883829 : Blo 587289 883829 := bbase (se 5 (by rfl) ⟨41429, by rfl⟩ : syracuseStep 883829 = 82859) (by norm_num)
theorem B883853 : Blo 587289 883853 := bbase (se 3 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 883853 = 331445) (by norm_num)
theorem B883877 : Blo 587289 883877 := bbase (se 4 (by rfl) ⟨82863, by rfl⟩ : syracuseStep 883877 = 165727) (by norm_num)
theorem B883901 : Blo 587289 883901 := bbase (se 3 (by rfl) ⟨165731, by rfl⟩ : syracuseStep 883901 = 331463) (by norm_num)
theorem B883925 : Blo 587289 883925 := bbase (se 7 (by rfl) ⟨10358, by rfl⟩ : syracuseStep 883925 = 20717) (by norm_num)
theorem B883949 : Blo 587289 883949 := bbase (se 3 (by rfl) ⟨165740, by rfl⟩ : syracuseStep 883949 = 331481) (by norm_num)
theorem B883973 : Blo 587289 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B883997 : Blo 587289 883997 := bbase (se 3 (by rfl) ⟨165749, by rfl⟩ : syracuseStep 883997 = 331499) (by norm_num)
theorem B884021 : Blo 587289 884021 := bbase (se 5 (by rfl) ⟨41438, by rfl⟩ : syracuseStep 884021 = 82877) (by norm_num)
theorem B884045 : Blo 587289 884045 := bbase (se 3 (by rfl) ⟨165758, by rfl⟩ : syracuseStep 884045 = 331517) (by norm_num)
theorem B884069 : Blo 587289 884069 := bbase (se 4 (by rfl) ⟨82881, by rfl⟩ : syracuseStep 884069 = 165763) (by norm_num)
theorem B884093 : Blo 587289 884093 := bbase (se 3 (by rfl) ⟨165767, by rfl⟩ : syracuseStep 884093 = 331535) (by norm_num)
theorem B2522501 : Blo 587289 2522501 := bbase (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) (by norm_num)
theorem B884117 : Blo 587289 884117 := bbase (se 6 (by rfl) ⟨20721, by rfl⟩ : syracuseStep 884117 = 41443) (by norm_num)
theorem B2981285 : Blo 587289 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B884141 : Blo 587289 884141 := bbase (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) (by norm_num)
theorem B884165 : Blo 587289 884165 := bbase (se 4 (by rfl) ⟨82890, by rfl⟩ : syracuseStep 884165 = 165781) (by norm_num)
theorem B16940501 : Blo 587289 16940501 := bbase (se 7 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 16940501 = 397043) (by norm_num)
theorem B884189 : Blo 587289 884189 := bbase (se 3 (by rfl) ⟨165785, by rfl⟩ : syracuseStep 884189 = 331571) (by norm_num)
theorem B884213 : Blo 587289 884213 := bbase (se 5 (by rfl) ⟨41447, by rfl⟩ : syracuseStep 884213 = 82895) (by norm_num)
theorem B884237 : Blo 587289 884237 := bbase (se 3 (by rfl) ⟨165794, by rfl⟩ : syracuseStep 884237 = 331589) (by norm_num)
theorem B884261 : Blo 587289 884261 := bbase (se 4 (by rfl) ⟨82899, by rfl⟩ : syracuseStep 884261 = 165799) (by norm_num)
theorem B884285 : Blo 587289 884285 := bbase (se 3 (by rfl) ⟨165803, by rfl⟩ : syracuseStep 884285 = 331607) (by norm_num)
theorem B884309 : Blo 587289 884309 := bbase (se 8 (by rfl) ⟨5181, by rfl⟩ : syracuseStep 884309 = 10363) (by norm_num)
theorem B884333 : Blo 587289 884333 := bbase (se 3 (by rfl) ⟨165812, by rfl⟩ : syracuseStep 884333 = 331625) (by norm_num)
theorem B884357 : Blo 587289 884357 := bbase (se 4 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 884357 = 165817) (by norm_num)
theorem B884381 : Blo 587289 884381 := bbase (se 3 (by rfl) ⟨165821, by rfl⟩ : syracuseStep 884381 = 331643) (by norm_num)
theorem B884405 : Blo 587289 884405 := bbase (se 5 (by rfl) ⟨41456, by rfl⟩ : syracuseStep 884405 = 82913) (by norm_num)
theorem B884429 : Blo 587289 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B851677 : Blo 587289 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B2391781 : Blo 587289 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B884453 : Blo 587289 884453 := bbase (se 4 (by rfl) ⟨82917, by rfl⟩ : syracuseStep 884453 = 165835) (by norm_num)
theorem B884477 : Blo 587289 884477 := bbase (se 3 (by rfl) ⟨165839, by rfl⟩ : syracuseStep 884477 = 331679) (by norm_num)
theorem B884501 : Blo 587289 884501 := bbase (se 6 (by rfl) ⟨20730, by rfl⟩ : syracuseStep 884501 = 41461) (by norm_num)
theorem B884525 : Blo 587289 884525 := bbase (se 3 (by rfl) ⟨165848, by rfl⟩ : syracuseStep 884525 = 331697) (by norm_num)
theorem B884549 : Blo 587289 884549 := bbase (se 4 (by rfl) ⟨82926, by rfl⟩ : syracuseStep 884549 = 165853) (by norm_num)
theorem B884573 : Blo 587289 884573 := bbase (se 3 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 884573 = 331715) (by norm_num)
theorem B884597 : Blo 587289 884597 := bbase (se 5 (by rfl) ⟨41465, by rfl⟩ : syracuseStep 884597 = 82931) (by norm_num)
theorem B884621 : Blo 587289 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B4030357 : Blo 587289 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B884645 : Blo 587289 884645 := bbase (se 4 (by rfl) ⟨82935, by rfl⟩ : syracuseStep 884645 = 165871) (by norm_num)
theorem B884669 : Blo 587289 884669 := bbase (se 3 (by rfl) ⟨165875, by rfl⟩ : syracuseStep 884669 = 331751) (by norm_num)
theorem B884693 : Blo 587289 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B884717 : Blo 587289 884717 := bbase (se 3 (by rfl) ⟨165884, by rfl⟩ : syracuseStep 884717 = 331769) (by norm_num)
theorem B589827 : Blo 587289 589827 := bstep (se 1 (by rfl) ⟨442370, by rfl⟩ : syracuseStep 589827 = 884741) B884741
theorem B884753 : Blo 587289 884753 := bstep (se 2 (by rfl) ⟨331782, by rfl⟩ : syracuseStep 884753 = 663565) B663565
theorem B589843 : Blo 587289 589843 := bstep (se 1 (by rfl) ⟨442382, by rfl⟩ : syracuseStep 589843 = 884765) B884765
theorem B884771 : Blo 587289 884771 := bstep (se 1 (by rfl) ⟨663578, by rfl⟩ : syracuseStep 884771 = 1327157) B1327157
theorem B589859 : Blo 587289 589859 := bstep (se 1 (by rfl) ⟨442394, by rfl⟩ : syracuseStep 589859 = 884789) B884789
theorem B589875 : Blo 587289 589875 := bstep (se 1 (by rfl) ⟨442406, by rfl⟩ : syracuseStep 589875 = 884813) B884813
theorem B884801 : Blo 587289 884801 := bstep (se 2 (by rfl) ⟨331800, by rfl⟩ : syracuseStep 884801 = 663601) B663601
theorem B589891 : Blo 587289 589891 := bstep (se 1 (by rfl) ⟨442418, by rfl⟩ : syracuseStep 589891 = 884837) B884837
theorem B884819 : Blo 587289 884819 := bstep (se 1 (by rfl) ⟨663614, by rfl⟩ : syracuseStep 884819 = 1327229) B1327229
theorem B589907 : Blo 587289 589907 := bstep (se 1 (by rfl) ⟨442430, by rfl⟩ : syracuseStep 589907 = 884861) B884861
theorem B589923 : Blo 587289 589923 := bstep (se 1 (by rfl) ⟨442442, by rfl⟩ : syracuseStep 589923 = 884885) B884885
theorem B884849 : Blo 587289 884849 := bstep (se 2 (by rfl) ⟨331818, by rfl⟩ : syracuseStep 884849 = 663637) B663637
theorem B589939 : Blo 587289 589939 := bstep (se 1 (by rfl) ⟨442454, by rfl⟩ : syracuseStep 589939 = 884909) B884909
theorem B884867 : Blo 587289 884867 := bstep (se 1 (by rfl) ⟨663650, by rfl⟩ : syracuseStep 884867 = 1327301) B1327301
theorem B589955 : Blo 587289 589955 := bstep (se 1 (by rfl) ⟨442466, by rfl⟩ : syracuseStep 589955 = 884933) B884933
theorem B589971 : Blo 587289 589971 := bstep (se 1 (by rfl) ⟨442478, by rfl⟩ : syracuseStep 589971 = 884957) B884957
theorem B884897 : Blo 587289 884897 := bstep (se 2 (by rfl) ⟨331836, by rfl⟩ : syracuseStep 884897 = 663673) B663673
theorem B589987 : Blo 587289 589987 := bstep (se 1 (by rfl) ⟨442490, by rfl⟩ : syracuseStep 589987 = 884981) B884981
theorem B884915 : Blo 587289 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B590003 : Blo 587289 590003 := bstep (se 1 (by rfl) ⟨442502, by rfl⟩ : syracuseStep 590003 = 885005) B885005
theorem B590019 : Blo 587289 590019 := bstep (se 1 (by rfl) ⟨442514, by rfl⟩ : syracuseStep 590019 = 885029) B885029
theorem B884945 : Blo 587289 884945 := bstep (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) B663709
theorem B590035 : Blo 587289 590035 := bstep (se 1 (by rfl) ⟨442526, by rfl⟩ : syracuseStep 590035 = 885053) B885053
theorem B884963 : Blo 587289 884963 := bstep (se 1 (by rfl) ⟨663722, by rfl⟩ : syracuseStep 884963 = 1327445) B1327445
theorem B590051 : Blo 587289 590051 := bstep (se 1 (by rfl) ⟨442538, by rfl⟩ : syracuseStep 590051 = 885077) B885077
theorem B590067 : Blo 587289 590067 := bstep (se 1 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 590067 = 885101) B885101
theorem B884993 : Blo 587289 884993 := bstep (se 2 (by rfl) ⟨331872, by rfl⟩ : syracuseStep 884993 = 663745) B663745
theorem B590083 : Blo 587289 590083 := bstep (se 1 (by rfl) ⟨442562, by rfl⟩ : syracuseStep 590083 = 885125) B885125
theorem B885011 : Blo 587289 885011 := bstep (se 1 (by rfl) ⟨663758, by rfl⟩ : syracuseStep 885011 = 1327517) B1327517
theorem B590099 : Blo 587289 590099 := bstep (se 1 (by rfl) ⟨442574, by rfl⟩ : syracuseStep 590099 = 885149) B885149
theorem B590115 : Blo 587289 590115 := bstep (se 1 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 590115 = 885173) B885173
theorem B885041 : Blo 587289 885041 := bstep (se 2 (by rfl) ⟨331890, by rfl⟩ : syracuseStep 885041 = 663781) B663781
theorem B590131 : Blo 587289 590131 := bstep (se 1 (by rfl) ⟨442598, by rfl⟩ : syracuseStep 590131 = 885197) B885197
theorem B885059 : Blo 587289 885059 := bstep (se 1 (by rfl) ⟨663794, by rfl⟩ : syracuseStep 885059 = 1327589) B1327589
theorem B590147 : Blo 587289 590147 := bstep (se 1 (by rfl) ⟨442610, by rfl⟩ : syracuseStep 590147 = 885221) B885221
theorem B590163 : Blo 587289 590163 := bstep (se 1 (by rfl) ⟨442622, by rfl⟩ : syracuseStep 590163 = 885245) B885245
theorem B885089 : Blo 587289 885089 := bstep (se 2 (by rfl) ⟨331908, by rfl⟩ : syracuseStep 885089 = 663817) B663817
theorem B590179 : Blo 587289 590179 := bstep (se 1 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 590179 = 885269) B885269
theorem B2982257 : Blo 587289 2982257 := bstep (se 2 (by rfl) ⟨1118346, by rfl⟩ : syracuseStep 2982257 = 2236693) B2236693
theorem B885107 : Blo 587289 885107 := bstep (se 1 (by rfl) ⟨663830, by rfl⟩ : syracuseStep 885107 = 1327661) B1327661
theorem B590195 : Blo 587289 590195 := bstep (se 1 (by rfl) ⟨442646, by rfl⟩ : syracuseStep 590195 = 885293) B885293
theorem B590211 : Blo 587289 590211 := bstep (se 1 (by rfl) ⟨442658, by rfl⟩ : syracuseStep 590211 = 885317) B885317
theorem B885137 : Blo 587289 885137 := bstep (se 2 (by rfl) ⟨331926, by rfl⟩ : syracuseStep 885137 = 663853) B663853
theorem B590227 : Blo 587289 590227 := bstep (se 1 (by rfl) ⟨442670, by rfl⟩ : syracuseStep 590227 = 885341) B885341
theorem B885155 : Blo 587289 885155 := bstep (se 1 (by rfl) ⟨663866, by rfl⟩ : syracuseStep 885155 = 1327733) B1327733
theorem B590243 : Blo 587289 590243 := bstep (se 1 (by rfl) ⟨442682, by rfl⟩ : syracuseStep 590243 = 885365) B885365
theorem B590259 : Blo 587289 590259 := bstep (se 1 (by rfl) ⟨442694, by rfl⟩ : syracuseStep 590259 = 885389) B885389
theorem B885185 : Blo 587289 885185 := bstep (se 2 (by rfl) ⟨331944, by rfl⟩ : syracuseStep 885185 = 663889) B663889
theorem B590275 : Blo 587289 590275 := bstep (se 1 (by rfl) ⟨442706, by rfl⟩ : syracuseStep 590275 = 885413) B885413
theorem B885203 : Blo 587289 885203 := bstep (se 1 (by rfl) ⟨663902, by rfl⟩ : syracuseStep 885203 = 1327805) B1327805
theorem B590291 : Blo 587289 590291 := bstep (se 1 (by rfl) ⟨442718, by rfl⟩ : syracuseStep 590291 = 885437) B885437
theorem B590307 : Blo 587289 590307 := bstep (se 1 (by rfl) ⟨442730, by rfl⟩ : syracuseStep 590307 = 885461) B885461
theorem B885233 : Blo 587289 885233 := bstep (se 2 (by rfl) ⟨331962, by rfl⟩ : syracuseStep 885233 = 663925) B663925
theorem B590323 : Blo 587289 590323 := bstep (se 1 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 590323 = 885485) B885485
theorem B885251 : Blo 587289 885251 := bstep (se 1 (by rfl) ⟨663938, by rfl⟩ : syracuseStep 885251 = 1327877) B1327877
theorem B590339 : Blo 587289 590339 := bstep (se 1 (by rfl) ⟨442754, by rfl⟩ : syracuseStep 590339 = 885509) B885509
theorem B590355 : Blo 587289 590355 := bstep (se 1 (by rfl) ⟨442766, by rfl⟩ : syracuseStep 590355 = 885533) B885533
theorem B885281 : Blo 587289 885281 := bstep (se 2 (by rfl) ⟨331980, by rfl⟩ : syracuseStep 885281 = 663961) B663961
theorem B590371 : Blo 587289 590371 := bstep (se 1 (by rfl) ⟨442778, by rfl⟩ : syracuseStep 590371 = 885557) B885557
theorem B885299 : Blo 587289 885299 := bstep (se 1 (by rfl) ⟨663974, by rfl⟩ : syracuseStep 885299 = 1327949) B1327949
theorem B590387 : Blo 587289 590387 := bstep (se 1 (by rfl) ⟨442790, by rfl⟩ : syracuseStep 590387 = 885581) B885581
theorem B590403 : Blo 587289 590403 := bstep (se 1 (by rfl) ⟨442802, by rfl⟩ : syracuseStep 590403 = 885605) B885605
theorem B885329 : Blo 587289 885329 := bstep (se 2 (by rfl) ⟨331998, by rfl⟩ : syracuseStep 885329 = 663997) B663997
theorem B590419 : Blo 587289 590419 := bstep (se 1 (by rfl) ⟨442814, by rfl⟩ : syracuseStep 590419 = 885629) B885629
theorem B885347 : Blo 587289 885347 := bstep (se 1 (by rfl) ⟨664010, by rfl⟩ : syracuseStep 885347 = 1328021) B1328021
theorem B590435 : Blo 587289 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B590451 : Blo 587289 590451 := bstep (se 1 (by rfl) ⟨442838, by rfl⟩ : syracuseStep 590451 = 885677) B885677
theorem B885377 : Blo 587289 885377 := bstep (se 2 (by rfl) ⟨332016, by rfl⟩ : syracuseStep 885377 = 664033) B664033
theorem B590467 : Blo 587289 590467 := bstep (se 1 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 590467 = 885701) B885701
theorem B885395 : Blo 587289 885395 := bstep (se 1 (by rfl) ⟨664046, by rfl⟩ : syracuseStep 885395 = 1328093) B1328093
theorem B590483 : Blo 587289 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B590499 : Blo 587289 590499 := bstep (se 1 (by rfl) ⟨442874, by rfl⟩ : syracuseStep 590499 = 885749) B885749
theorem B885425 : Blo 587289 885425 := bstep (se 2 (by rfl) ⟨332034, by rfl⟩ : syracuseStep 885425 = 664069) B664069
theorem B590515 : Blo 587289 590515 := bstep (se 1 (by rfl) ⟨442886, by rfl⟩ : syracuseStep 590515 = 885773) B885773
theorem B885443 : Blo 587289 885443 := bstep (se 1 (by rfl) ⟨664082, by rfl⟩ : syracuseStep 885443 = 1328165) B1328165
theorem B590531 : Blo 587289 590531 := bstep (se 1 (by rfl) ⟨442898, by rfl⟩ : syracuseStep 590531 = 885797) B885797
theorem B590547 : Blo 587289 590547 := bstep (se 1 (by rfl) ⟨442910, by rfl⟩ : syracuseStep 590547 = 885821) B885821
theorem B885473 : Blo 587289 885473 := bstep (se 2 (by rfl) ⟨332052, by rfl⟩ : syracuseStep 885473 = 664105) B664105
theorem B590563 : Blo 587289 590563 := bstep (se 1 (by rfl) ⟨442922, by rfl⟩ : syracuseStep 590563 = 885845) B885845
theorem B885491 : Blo 587289 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B590579 : Blo 587289 590579 := bstep (se 1 (by rfl) ⟨442934, by rfl⟩ : syracuseStep 590579 = 885869) B885869
theorem B590595 : Blo 587289 590595 := bstep (se 1 (by rfl) ⟨442946, by rfl⟩ : syracuseStep 590595 = 885893) B885893
theorem B885521 : Blo 587289 885521 := bstep (se 2 (by rfl) ⟨332070, by rfl⟩ : syracuseStep 885521 = 664141) B664141
theorem B590611 : Blo 587289 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B885539 : Blo 587289 885539 := bstep (se 1 (by rfl) ⟨664154, by rfl⟩ : syracuseStep 885539 = 1328309) B1328309
theorem B590627 : Blo 587289 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B590643 : Blo 587289 590643 := bstep (se 1 (by rfl) ⟨442982, by rfl⟩ : syracuseStep 590643 = 885965) B885965
theorem B885569 : Blo 587289 885569 := bstep (se 2 (by rfl) ⟨332088, by rfl⟩ : syracuseStep 885569 = 664177) B664177
theorem B590659 : Blo 587289 590659 := bstep (se 1 (by rfl) ⟨442994, by rfl⟩ : syracuseStep 590659 = 885989) B885989
theorem B885587 : Blo 587289 885587 := bstep (se 1 (by rfl) ⟨664190, by rfl⟩ : syracuseStep 885587 = 1328381) B1328381
theorem B590675 : Blo 587289 590675 := bstep (se 1 (by rfl) ⟨443006, by rfl⟩ : syracuseStep 590675 = 886013) B886013
theorem B590691 : Blo 587289 590691 := bstep (se 1 (by rfl) ⟨443018, by rfl⟩ : syracuseStep 590691 = 886037) B886037
theorem B885617 : Blo 587289 885617 := bstep (se 2 (by rfl) ⟨332106, by rfl⟩ : syracuseStep 885617 = 664213) B664213
theorem B590707 : Blo 587289 590707 := bstep (se 1 (by rfl) ⟨443030, by rfl⟩ : syracuseStep 590707 = 886061) B886061
theorem B885635 : Blo 587289 885635 := bstep (se 1 (by rfl) ⟨664226, by rfl⟩ : syracuseStep 885635 = 1328453) B1328453
theorem B590723 : Blo 587289 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B590739 : Blo 587289 590739 := bstep (se 1 (by rfl) ⟨443054, by rfl⟩ : syracuseStep 590739 = 886109) B886109
theorem B885665 : Blo 587289 885665 := bstep (se 2 (by rfl) ⟨332124, by rfl⟩ : syracuseStep 885665 = 664249) B664249
theorem B590755 : Blo 587289 590755 := bstep (se 1 (by rfl) ⟨443066, by rfl⟩ : syracuseStep 590755 = 886133) B886133
theorem B885683 : Blo 587289 885683 := bstep (se 1 (by rfl) ⟨664262, by rfl⟩ : syracuseStep 885683 = 1328525) B1328525
theorem B590771 : Blo 587289 590771 := bstep (se 1 (by rfl) ⟨443078, by rfl⟩ : syracuseStep 590771 = 886157) B886157
theorem B590787 : Blo 587289 590787 := bstep (se 1 (by rfl) ⟨443090, by rfl⟩ : syracuseStep 590787 = 886181) B886181
theorem B885713 : Blo 587289 885713 := bstep (se 2 (by rfl) ⟨332142, by rfl⟩ : syracuseStep 885713 = 664285) B664285
theorem B590803 : Blo 587289 590803 := bstep (se 1 (by rfl) ⟨443102, by rfl⟩ : syracuseStep 590803 = 886205) B886205
theorem B7177187 : Blo 587289 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B885731 : Blo 587289 885731 := bstep (se 1 (by rfl) ⟨664298, by rfl⟩ : syracuseStep 885731 = 1328597) B1328597
theorem B590819 : Blo 587289 590819 := bstep (se 1 (by rfl) ⟨443114, by rfl⟩ : syracuseStep 590819 = 886229) B886229
theorem B4031473 : Blo 587289 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B590835 : Blo 587289 590835 := bstep (se 1 (by rfl) ⟨443126, by rfl⟩ : syracuseStep 590835 = 886253) B886253
theorem B885761 : Blo 587289 885761 := bstep (se 2 (by rfl) ⟨332160, by rfl⟩ : syracuseStep 885761 = 664321) B664321
theorem B590851 : Blo 587289 590851 := bstep (se 1 (by rfl) ⟨443138, by rfl⟩ : syracuseStep 590851 = 886277) B886277
theorem B885779 : Blo 587289 885779 := bstep (se 1 (by rfl) ⟨664334, by rfl⟩ : syracuseStep 885779 = 1328669) B1328669
theorem B590867 : Blo 587289 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B590883 : Blo 587289 590883 := bstep (se 1 (by rfl) ⟨443162, by rfl⟩ : syracuseStep 590883 = 886325) B886325
theorem B885809 : Blo 587289 885809 := bstep (se 2 (by rfl) ⟨332178, by rfl⟩ : syracuseStep 885809 = 664357) B664357
theorem B590899 : Blo 587289 590899 := bstep (se 1 (by rfl) ⟨443174, by rfl⟩ : syracuseStep 590899 = 886349) B886349
theorem B1115203 : Blo 587289 1115203 := bstep (se 1 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 1115203 = 1672805) B1672805
theorem B885827 : Blo 587289 885827 := bstep (se 1 (by rfl) ⟨664370, by rfl⟩ : syracuseStep 885827 = 1328741) B1328741
theorem B590915 : Blo 587289 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B590931 : Blo 587289 590931 := bstep (se 1 (by rfl) ⟨443198, by rfl⟩ : syracuseStep 590931 = 886397) B886397
theorem B885857 : Blo 587289 885857 := bstep (se 2 (by rfl) ⟨332196, by rfl⟩ : syracuseStep 885857 = 664393) B664393
theorem B590947 : Blo 587289 590947 := bstep (se 1 (by rfl) ⟨443210, by rfl⟩ : syracuseStep 590947 = 886421) B886421
theorem B885875 : Blo 587289 885875 := bstep (se 1 (by rfl) ⟨664406, by rfl⟩ : syracuseStep 885875 = 1328813) B1328813
theorem B590963 : Blo 587289 590963 := bstep (se 1 (by rfl) ⟨443222, by rfl⟩ : syracuseStep 590963 = 886445) B886445
theorem B590979 : Blo 587289 590979 := bstep (se 1 (by rfl) ⟨443234, by rfl⟩ : syracuseStep 590979 = 886469) B886469
theorem B885905 : Blo 587289 885905 := bstep (se 2 (by rfl) ⟨332214, by rfl⟩ : syracuseStep 885905 = 664429) B664429
theorem B590995 : Blo 587289 590995 := bstep (se 1 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 590995 = 886493) B886493
theorem B885923 : Blo 587289 885923 := bstep (se 1 (by rfl) ⟨664442, by rfl⟩ : syracuseStep 885923 = 1328885) B1328885
theorem B591011 : Blo 587289 591011 := bstep (se 1 (by rfl) ⟨443258, by rfl⟩ : syracuseStep 591011 = 886517) B886517
theorem B591027 : Blo 587289 591027 := bstep (se 1 (by rfl) ⟨443270, by rfl⟩ : syracuseStep 591027 = 886541) B886541
theorem B885953 : Blo 587289 885953 := bstep (se 2 (by rfl) ⟨332232, by rfl⟩ : syracuseStep 885953 = 664465) B664465
theorem B591043 : Blo 587289 591043 := bstep (se 1 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 591043 = 886565) B886565
theorem B885971 : Blo 587289 885971 := bstep (se 1 (by rfl) ⟨664478, by rfl⟩ : syracuseStep 885971 = 1328957) B1328957
theorem B591059 : Blo 587289 591059 := bstep (se 1 (by rfl) ⟨443294, by rfl⟩ : syracuseStep 591059 = 886589) B886589
theorem B1115363 : Blo 587289 1115363 := bstep (se 1 (by rfl) ⟨836522, by rfl⟩ : syracuseStep 1115363 = 1673045) B1673045
theorem B591075 : Blo 587289 591075 := bstep (se 1 (by rfl) ⟨443306, by rfl⟩ : syracuseStep 591075 = 886613) B886613
theorem B886001 : Blo 587289 886001 := bstep (se 2 (by rfl) ⟨332250, by rfl⟩ : syracuseStep 886001 = 664501) B664501
theorem B591091 : Blo 587289 591091 := bstep (se 1 (by rfl) ⟨443318, by rfl⟩ : syracuseStep 591091 = 886637) B886637
theorem B886019 : Blo 587289 886019 := bstep (se 1 (by rfl) ⟨664514, by rfl⟩ : syracuseStep 886019 = 1329029) B1329029
theorem B591107 : Blo 587289 591107 := bstep (se 1 (by rfl) ⟨443330, by rfl⟩ : syracuseStep 591107 = 886661) B886661
theorem B591123 : Blo 587289 591123 := bstep (se 1 (by rfl) ⟨443342, by rfl⟩ : syracuseStep 591123 = 886685) B886685
theorem B886049 : Blo 587289 886049 := bstep (se 2 (by rfl) ⟨332268, by rfl⟩ : syracuseStep 886049 = 664537) B664537
theorem B591139 : Blo 587289 591139 := bstep (se 1 (by rfl) ⟨443354, by rfl⟩ : syracuseStep 591139 = 886709) B886709
theorem B886067 : Blo 587289 886067 := bstep (se 1 (by rfl) ⟨664550, by rfl⟩ : syracuseStep 886067 = 1329101) B1329101
theorem B591155 : Blo 587289 591155 := bstep (se 1 (by rfl) ⟨443366, by rfl⟩ : syracuseStep 591155 = 886733) B886733
theorem B591171 : Blo 587289 591171 := bstep (se 1 (by rfl) ⟨443378, by rfl⟩ : syracuseStep 591171 = 886757) B886757
theorem B886097 : Blo 587289 886097 := bstep (se 2 (by rfl) ⟨332286, by rfl⟩ : syracuseStep 886097 = 664573) B664573
theorem B591187 : Blo 587289 591187 := bstep (se 1 (by rfl) ⟨443390, by rfl⟩ : syracuseStep 591187 = 886781) B886781
theorem B886115 : Blo 587289 886115 := bstep (se 1 (by rfl) ⟨664586, by rfl⟩ : syracuseStep 886115 = 1329173) B1329173
theorem B591203 : Blo 587289 591203 := bstep (se 1 (by rfl) ⟨443402, by rfl⟩ : syracuseStep 591203 = 886805) B886805
theorem B591219 : Blo 587289 591219 := bstep (se 1 (by rfl) ⟨443414, by rfl⟩ : syracuseStep 591219 = 886829) B886829
theorem B886145 : Blo 587289 886145 := bstep (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) B664609
theorem B591235 : Blo 587289 591235 := bstep (se 1 (by rfl) ⟨443426, by rfl⟩ : syracuseStep 591235 = 886853) B886853
theorem B1672589 : Blo 587289 1672589 := bstep (se 3 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 1672589 = 627221) B627221
theorem B886163 : Blo 587289 886163 := bstep (se 1 (by rfl) ⟨664622, by rfl⟩ : syracuseStep 886163 = 1329245) B1329245
theorem B591251 : Blo 587289 591251 := bstep (se 1 (by rfl) ⟨443438, by rfl⟩ : syracuseStep 591251 = 886877) B886877
theorem B591267 : Blo 587289 591267 := bstep (se 1 (by rfl) ⟨443450, by rfl⟩ : syracuseStep 591267 = 886901) B886901
theorem B886193 : Blo 587289 886193 := bstep (se 2 (by rfl) ⟨332322, by rfl⟩ : syracuseStep 886193 = 664645) B664645
theorem B591283 : Blo 587289 591283 := bstep (se 1 (by rfl) ⟨443462, by rfl⟩ : syracuseStep 591283 = 886925) B886925
theorem B886211 : Blo 587289 886211 := bstep (se 1 (by rfl) ⟨664658, by rfl⟩ : syracuseStep 886211 = 1329317) B1329317
theorem B886241 : Blo 587289 886241 := bstep (se 2 (by rfl) ⟨332340, by rfl⟩ : syracuseStep 886241 = 664681) B664681
theorem B4785635 : Blo 587289 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B886259 : Blo 587289 886259 := bstep (se 1 (by rfl) ⟨664694, by rfl⟩ : syracuseStep 886259 = 1329389) B1329389
theorem B886289 : Blo 587289 886289 := bstep (se 2 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 886289 = 664717) B664717
theorem B886307 : Blo 587289 886307 := bstep (se 1 (by rfl) ⟨664730, by rfl⟩ : syracuseStep 886307 = 1329461) B1329461
theorem B886337 : Blo 587289 886337 := bstep (se 2 (by rfl) ⟨332376, by rfl⟩ : syracuseStep 886337 = 664753) B664753
theorem B1672771 : Blo 587289 1672771 := bstep (se 1 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 1672771 = 2509157) B2509157
theorem B886355 : Blo 587289 886355 := bstep (se 1 (by rfl) ⟨664766, by rfl⟩ : syracuseStep 886355 = 1329533) B1329533
theorem B5375587 : Blo 587289 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B886385 : Blo 587289 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B886403 : Blo 587289 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B886433 : Blo 587289 886433 := bstep (se 2 (by rfl) ⟨332412, by rfl⟩ : syracuseStep 886433 = 664825) B664825
theorem B886451 : Blo 587289 886451 := bstep (se 1 (by rfl) ⟨664838, by rfl⟩ : syracuseStep 886451 = 1329677) B1329677
theorem B2524877 : Blo 587289 2524877 := bstep (se 3 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 2524877 = 946829) B946829
theorem B886481 : Blo 587289 886481 := bstep (se 2 (by rfl) ⟨332430, by rfl⟩ : syracuseStep 886481 = 664861) B664861
theorem B886499 : Blo 587289 886499 := bstep (se 1 (by rfl) ⟨664874, by rfl⟩ : syracuseStep 886499 = 1329749) B1329749
theorem B886529 : Blo 587289 886529 := bstep (se 2 (by rfl) ⟨332448, by rfl⟩ : syracuseStep 886529 = 664897) B664897
theorem B886547 : Blo 587289 886547 := bstep (se 1 (by rfl) ⟨664910, by rfl⟩ : syracuseStep 886547 = 1329821) B1329821
theorem B2098979 : Blo 587289 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B2983715 : Blo 587289 2983715 := bstep (se 1 (by rfl) ⟨2237786, by rfl⟩ : syracuseStep 2983715 = 4475573) B4475573
theorem B886577 : Blo 587289 886577 := bstep (se 2 (by rfl) ⟨332466, by rfl⟩ : syracuseStep 886577 = 664933) B664933
theorem B886595 : Blo 587289 886595 := bstep (se 1 (by rfl) ⟨664946, by rfl⟩ : syracuseStep 886595 = 1329893) B1329893
theorem B886625 : Blo 587289 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B886643 : Blo 587289 886643 := bstep (se 1 (by rfl) ⟨664982, by rfl⟩ : syracuseStep 886643 = 1329965) B1329965
theorem B886673 : Blo 587289 886673 := bstep (se 2 (by rfl) ⟨332502, by rfl⟩ : syracuseStep 886673 = 665005) B665005
theorem B886691 : Blo 587289 886691 := bstep (se 1 (by rfl) ⟨665018, by rfl⟩ : syracuseStep 886691 = 1330037) B1330037
theorem B2230193 : Blo 587289 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B886721 : Blo 587289 886721 := bstep (se 2 (by rfl) ⟨332520, by rfl⟩ : syracuseStep 886721 = 665041) B665041
theorem B886739 : Blo 587289 886739 := bstep (se 1 (by rfl) ⟨665054, by rfl⟩ : syracuseStep 886739 = 1330109) B1330109
theorem B886769 : Blo 587289 886769 := bstep (se 2 (by rfl) ⟨332538, by rfl⟩ : syracuseStep 886769 = 665077) B665077
theorem B886787 : Blo 587289 886787 := bstep (se 1 (by rfl) ⟨665090, by rfl⟩ : syracuseStep 886787 = 1330181) B1330181
theorem B886817 : Blo 587289 886817 := bstep (se 2 (by rfl) ⟨332556, by rfl⟩ : syracuseStep 886817 = 665113) B665113
theorem B1673261 : Blo 587289 1673261 := bstep (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) B627473
theorem B886835 : Blo 587289 886835 := bstep (se 1 (by rfl) ⟨665126, by rfl⟩ : syracuseStep 886835 = 1330253) B1330253
theorem B886865 : Blo 587289 886865 := bstep (se 2 (by rfl) ⟨332574, by rfl⟩ : syracuseStep 886865 = 665149) B665149
theorem B2394211 : Blo 587289 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B886883 : Blo 587289 886883 := bstep (se 1 (by rfl) ⟨665162, by rfl⟩ : syracuseStep 886883 = 1330325) B1330325
theorem B886913 : Blo 587289 886913 := bstep (se 2 (by rfl) ⟨332592, by rfl⟩ : syracuseStep 886913 = 665185) B665185
theorem B1050769 : Blo 587289 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B886931 : Blo 587289 886931 := bstep (se 1 (by rfl) ⟨665198, by rfl⟩ : syracuseStep 886931 = 1330397) B1330397
theorem B1116433 : Blo 587289 1116433 := bstep (se 2 (by rfl) ⟨418662, by rfl⟩ : syracuseStep 1116433 = 837325) B837325
theorem B5048689 : Blo 587289 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B61049285 : Blo 587289 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B6785477 : Blo 587289 6785477 := bstep (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) B1272277
theorem B2230861 : Blo 587289 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B2984525 : Blo 587289 2984525 := bstep (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) B1119197
theorem B3181189 : Blo 587289 3181189 := bstep (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) B596473
theorem B11340485 : Blo 587289 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B1674445 : Blo 587289 1674445 := bstep (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) B627917
theorem B1117489 : Blo 587289 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B2231651 : Blo 587289 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B3346019 : Blo 587289 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B1019539 : Blo 587289 1019539 := bstep (se 1 (by rfl) ⟨764654, by rfl⟩ : syracuseStep 1019539 = 1529309) B1529309
theorem B2297521 : Blo 587289 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B1117891 : Blo 587289 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B1117937 : Blo 587289 1117937 := bstep (se 2 (by rfl) ⟨419226, by rfl⟩ : syracuseStep 1117937 = 838453) B838453
theorem B3772165 : Blo 587289 3772165 := bstep (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) B707281
theorem B6721379 : Blo 587289 6721379 := bstep (se 1 (by rfl) ⟨5041034, by rfl⟩ : syracuseStep 6721379 = 10082069) B10082069
theorem B7573445 : Blo 587289 7573445 := bstep (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) B1420021
theorem B6033379 : Blo 587289 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2232305 : Blo 587289 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B1118225 : Blo 587289 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B1609763 : Blo 587289 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B757955 : Blo 587289 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B1675505 : Blo 587289 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B3347021 : Blo 587289 3347021 := bstep (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) B1255133
theorem B1118947 : Blo 587289 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1676177 : Blo 587289 1676177 := bstep (se 2 (by rfl) ⟨628566, by rfl⟩ : syracuseStep 1676177 = 1257133) B1257133
theorem B627635 : Blo 587289 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B1119395 : Blo 587289 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B660739 : Blo 587289 660739 := bstep (se 1 (by rfl) ⟨495554, by rfl⟩ : syracuseStep 660739 = 991109) B991109
theorem B4461965 : Blo 587289 4461965 := bstep (se 3 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 4461965 = 1673237) B1673237
theorem B660883 : Blo 587289 660883 := bstep (se 1 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 660883 = 991325) B991325
theorem B2233763 : Blo 587289 2233763 := bstep (se 1 (by rfl) ⟨1675322, by rfl⟩ : syracuseStep 2233763 = 3350645) B3350645
theorem B2233777 : Blo 587289 2233777 := bstep (se 2 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 2233777 = 1675333) B1675333
theorem B2987441 : Blo 587289 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B1119683 : Blo 587289 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B661027 : Blo 587289 661027 := bstep (se 1 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 661027 = 991541) B991541
theorem B2692685 : Blo 587289 2692685 := bstep (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) B1009757
theorem B2823821 : Blo 587289 2823821 := bstep (se 3 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 2823821 = 1058933) B1058933
theorem B1676963 : Blo 587289 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B661171 : Blo 587289 661171 := bstep (se 1 (by rfl) ⟨495878, by rfl⟩ : syracuseStep 661171 = 991757) B991757
theorem B661315 : Blo 587289 661315 := bstep (se 1 (by rfl) ⟨495986, by rfl⟩ : syracuseStep 661315 = 991973) B991973
theorem B661459 : Blo 587289 661459 := bstep (se 1 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 661459 = 992189) B992189
theorem B1677293 : Blo 587289 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B1677361 : Blo 587289 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B661603 : Blo 587289 661603 := bstep (se 1 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 661603 = 992405) B992405
theorem B661747 : Blo 587289 661747 := bstep (se 1 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 661747 = 992621) B992621
theorem B1677635 : Blo 587289 1677635 := bstep (se 1 (by rfl) ⟨1258226, by rfl⟩ : syracuseStep 1677635 = 2516453) B2516453
theorem B1120625 : Blo 587289 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B661891 : Blo 587289 661891 := bstep (se 1 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 661891 = 992837) B992837
theorem B3774883 : Blo 587289 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B629203 : Blo 587289 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B4790755 : Blo 587289 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B662035 : Blo 587289 662035 := bstep (se 1 (by rfl) ⟨496526, by rfl⟩ : syracuseStep 662035 = 993053) B993053
theorem B662179 : Blo 587289 662179 := bstep (se 1 (by rfl) ⟨496634, by rfl⟩ : syracuseStep 662179 = 993269) B993269
theorem B662323 : Blo 587289 662323 := bstep (se 1 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 662323 = 993485) B993485
theorem B2235235 : Blo 587289 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B2988899 : Blo 587289 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B629651 : Blo 587289 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B596899 : Blo 587289 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B662467 : Blo 587289 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B1514513 : Blo 587289 1514513 := bstep (se 2 (by rfl) ⟨567942, by rfl⟩ : syracuseStep 1514513 = 1135885) B1135885
theorem B662611 : Blo 587289 662611 := bstep (se 1 (by rfl) ⟨496958, by rfl⟩ : syracuseStep 662611 = 993917) B993917
theorem B1678477 : Blo 587289 1678477 := bstep (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) B629429
theorem B662755 : Blo 587289 662755 := bstep (se 1 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 662755 = 994133) B994133
theorem B1121521 : Blo 587289 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B1678637 : Blo 587289 1678637 := bstep (se 3 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 1678637 = 629489) B629489
theorem B662899 : Blo 587289 662899 := bstep (se 1 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 662899 = 994349) B994349
theorem B957827 : Blo 587289 957827 := bstep (se 1 (by rfl) ⟨718370, by rfl⟩ : syracuseStep 957827 = 1436741) B1436741
theorem B1121681 : Blo 587289 1121681 := bstep (se 2 (by rfl) ⟨420630, by rfl⟩ : syracuseStep 1121681 = 841261) B841261
theorem B3349937 : Blo 587289 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B1678819 : Blo 587289 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B663043 : Blo 587289 663043 := bstep (se 1 (by rfl) ⟨497282, by rfl⟩ : syracuseStep 663043 = 994565) B994565
theorem B2825741 : Blo 587289 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B2989709 : Blo 587289 2989709 := bstep (se 3 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 2989709 = 1121141) B1121141
theorem B663187 : Blo 587289 663187 := bstep (se 1 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 663187 = 994781) B994781
theorem B663331 : Blo 587289 663331 := bstep (se 1 (by rfl) ⟨497498, by rfl⟩ : syracuseStep 663331 = 994997) B994997
theorem B1122083 : Blo 587289 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B991075 : Blo 587289 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B663475 : Blo 587289 663475 := bstep (se 1 (by rfl) ⟨497606, by rfl⟩ : syracuseStep 663475 = 995213) B995213
theorem B1417169 : Blo 587289 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B991217 : Blo 587289 991217 := bstep (se 2 (by rfl) ⟨371706, by rfl⟩ : syracuseStep 991217 = 743413) B743413
theorem B663619 : Blo 587289 663619 := bstep (se 1 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 663619 = 995429) B995429
theorem B598115 : Blo 587289 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B991345 : Blo 587289 991345 := bstep (se 2 (by rfl) ⟨371754, by rfl⟩ : syracuseStep 991345 = 743509) B743509
theorem B991379 : Blo 587289 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B663763 : Blo 587289 663763 := bstep (se 1 (by rfl) ⟨497822, by rfl⟩ : syracuseStep 663763 = 995645) B995645
theorem B4464881 : Blo 587289 4464881 := bstep (se 2 (by rfl) ⟨1674330, by rfl⟩ : syracuseStep 4464881 = 3348661) B3348661
theorem B631027 : Blo 587289 631027 := bstep (se 1 (by rfl) ⟨473270, by rfl⟩ : syracuseStep 631027 = 946541) B946541
theorem B794881 : Blo 587289 794881 := bstep (se 2 (by rfl) ⟨298080, by rfl⟩ : syracuseStep 794881 = 596161) B596161
theorem B991507 : Blo 587289 991507 := bstep (se 1 (by rfl) ⟨743630, by rfl⟩ : syracuseStep 991507 = 1487261) B1487261
theorem B1417553 : Blo 587289 1417553 := bstep (se 2 (by rfl) ⟨531582, by rfl⟩ : syracuseStep 1417553 = 1063165) B1063165
theorem B663907 : Blo 587289 663907 := bstep (se 1 (by rfl) ⟨497930, by rfl⟩ : syracuseStep 663907 = 995861) B995861
theorem B3776881 : Blo 587289 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B991649 : Blo 587289 991649 := bstep (se 2 (by rfl) ⟨371868, by rfl⟩ : syracuseStep 991649 = 743737) B743737
theorem B795043 : Blo 587289 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B664051 : Blo 587289 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B991777 : Blo 587289 991777 := bstep (se 2 (by rfl) ⟨371916, by rfl⟩ : syracuseStep 991777 = 743833) B743833
theorem B991811 : Blo 587289 991811 := bstep (se 1 (by rfl) ⟨743858, by rfl⟩ : syracuseStep 991811 = 1487717) B1487717
theorem B664195 : Blo 587289 664195 := bstep (se 1 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 664195 = 996293) B996293
theorem B991939 : Blo 587289 991939 := bstep (se 1 (by rfl) ⟨743954, by rfl⟩ : syracuseStep 991939 = 1487909) B1487909
theorem B664339 : Blo 587289 664339 := bstep (se 1 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 664339 = 996509) B996509
theorem B992081 : Blo 587289 992081 := bstep (se 2 (by rfl) ⟨372030, by rfl⟩ : syracuseStep 992081 = 744061) B744061
theorem B1680209 : Blo 587289 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B3351395 : Blo 587289 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B664483 : Blo 587289 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B992209 : Blo 587289 992209 := bstep (se 2 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 992209 = 744157) B744157
theorem B992243 : Blo 587289 992243 := bstep (se 1 (by rfl) ⟨744182, by rfl⟩ : syracuseStep 992243 = 1488365) B1488365
theorem B2237453 : Blo 587289 2237453 := bstep (se 3 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 2237453 = 839045) B839045
theorem B664627 : Blo 587289 664627 := bstep (se 1 (by rfl) ⟨498470, by rfl⟩ : syracuseStep 664627 = 996941) B996941
theorem B1254467 : Blo 587289 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B894035 : Blo 587289 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B992371 : Blo 587289 992371 := bstep (se 1 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 992371 = 1488557) B1488557
theorem B664771 : Blo 587289 664771 := bstep (se 1 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 664771 = 997157) B997157
theorem B992513 : Blo 587289 992513 := bstep (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) B744385
theorem B664915 : Blo 587289 664915 := bstep (se 1 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 664915 = 997373) B997373
theorem B992641 : Blo 587289 992641 := bstep (se 2 (by rfl) ⟨372240, by rfl⟩ : syracuseStep 992641 = 744481) B744481
theorem B992675 : Blo 587289 992675 := bstep (se 1 (by rfl) ⟨744506, by rfl⟩ : syracuseStep 992675 = 1489013) B1489013
theorem B665059 : Blo 587289 665059 := bstep (se 1 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 665059 = 997589) B997589
theorem B1058321 : Blo 587289 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B992803 : Blo 587289 992803 := bstep (se 1 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 992803 = 1489205) B1489205
theorem B992945 : Blo 587289 992945 := bstep (se 2 (by rfl) ⟨372354, by rfl⟩ : syracuseStep 992945 = 744709) B744709
theorem B5678819 : Blo 587289 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B1681165 : Blo 587289 1681165 := bstep (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) B630437
theorem B993073 : Blo 587289 993073 := bstep (se 2 (by rfl) ⟨372402, by rfl⟩ : syracuseStep 993073 = 744805) B744805
theorem B993107 : Blo 587289 993107 := bstep (se 1 (by rfl) ⟨744830, by rfl⟩ : syracuseStep 993107 = 1489661) B1489661
theorem B1255331 : Blo 587289 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B993235 : Blo 587289 993235 := bstep (se 1 (by rfl) ⟨744926, by rfl⟩ : syracuseStep 993235 = 1489853) B1489853
theorem B1681393 : Blo 587289 1681393 := bstep (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) B1261045
theorem B1255441 : Blo 587289 1255441 := bstep (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) B941581
theorem B12757013 : Blo 587289 12757013 := bstep (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) B597985
theorem B993377 : Blo 587289 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B1681553 : Blo 587289 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B993505 : Blo 587289 993505 := bstep (se 2 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 993505 = 745129) B745129
theorem B993539 : Blo 587289 993539 := bstep (se 1 (by rfl) ⟨745154, by rfl⟩ : syracuseStep 993539 = 1490309) B1490309
theorem B1681667 : Blo 587289 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B3189041 : Blo 587289 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B993667 : Blo 587289 993667 := bstep (se 1 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 993667 = 1490501) B1490501
theorem B895409 : Blo 587289 895409 := bstep (se 2 (by rfl) ⟨335778, by rfl⟩ : syracuseStep 895409 = 671557) B671557
theorem B2992625 : Blo 587289 2992625 := bstep (se 2 (by rfl) ⟨1122234, by rfl⟩ : syracuseStep 2992625 = 2244469) B2244469
theorem B993809 : Blo 587289 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B797249 : Blo 587289 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B993937 : Blo 587289 993937 := bstep (se 2 (by rfl) ⟨372726, by rfl⟩ : syracuseStep 993937 = 745453) B745453
theorem B1321649 : Blo 587289 1321649 := bstep (se 2 (by rfl) ⟨495618, by rfl⟩ : syracuseStep 1321649 = 991237) B991237
theorem B993971 : Blo 587289 993971 := bstep (se 1 (by rfl) ⟨745478, by rfl⟩ : syracuseStep 993971 = 1490957) B1490957
theorem B1321667 : Blo 587289 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B994099 : Blo 587289 994099 := bstep (se 1 (by rfl) ⟨745574, by rfl⟩ : syracuseStep 994099 = 1491149) B1491149
theorem B1420195 : Blo 587289 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B994241 : Blo 587289 994241 := bstep (se 2 (by rfl) ⟨372840, by rfl⟩ : syracuseStep 994241 = 745681) B745681
theorem B1321937 : Blo 587289 1321937 := bstep (se 2 (by rfl) ⟨495726, by rfl⟩ : syracuseStep 1321937 = 991453) B991453
theorem B1321955 : Blo 587289 1321955 := bstep (se 1 (by rfl) ⟨991466, by rfl⟩ : syracuseStep 1321955 = 1982933) B1982933
theorem B994369 : Blo 587289 994369 := bstep (se 2 (by rfl) ⟨372888, by rfl⟩ : syracuseStep 994369 = 745777) B745777
theorem B994403 : Blo 587289 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B8629361 : Blo 587289 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B994531 : Blo 587289 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B1682669 : Blo 587289 1682669 := bstep (se 3 (by rfl) ⟨315500, by rfl⟩ : syracuseStep 1682669 = 631001) B631001
theorem B1322225 : Blo 587289 1322225 := bstep (se 2 (by rfl) ⟨495834, by rfl⟩ : syracuseStep 1322225 = 991669) B991669
theorem B1322243 : Blo 587289 1322243 := bstep (se 1 (by rfl) ⟨991682, by rfl⟩ : syracuseStep 1322243 = 1983365) B1983365
theorem B994673 : Blo 587289 994673 := bstep (se 2 (by rfl) ⟨373002, by rfl⟩ : syracuseStep 994673 = 746005) B746005
theorem B6040973 : Blo 587289 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B1682851 : Blo 587289 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B994801 : Blo 587289 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B1322513 : Blo 587289 1322513 := bstep (se 2 (by rfl) ⟨495942, by rfl⟩ : syracuseStep 1322513 = 991885) B991885
theorem B994835 : Blo 587289 994835 := bstep (se 1 (by rfl) ⟨746126, by rfl⟩ : syracuseStep 994835 = 1492253) B1492253
theorem B1322531 : Blo 587289 1322531 := bstep (se 1 (by rfl) ⟨991898, by rfl⟩ : syracuseStep 1322531 = 1983797) B1983797
theorem B1683011 : Blo 587289 1683011 := bstep (se 1 (by rfl) ⟨1262258, by rfl⟩ : syracuseStep 1683011 = 2524517) B2524517
theorem B4763249 : Blo 587289 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B994963 : Blo 587289 994963 := bstep (se 1 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 994963 = 1492445) B1492445
theorem B1060547 : Blo 587289 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B995105 : Blo 587289 995105 := bstep (se 2 (by rfl) ⟨373164, by rfl⟩ : syracuseStep 995105 = 746329) B746329
theorem B1322801 : Blo 587289 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B1322819 : Blo 587289 1322819 := bstep (se 1 (by rfl) ⟨992114, by rfl⟩ : syracuseStep 1322819 = 1984229) B1984229
theorem B896881 : Blo 587289 896881 := bstep (se 2 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 896881 = 672661) B672661
theorem B2240369 : Blo 587289 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B995233 : Blo 587289 995233 := bstep (se 2 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 995233 = 746425) B746425
theorem B995267 : Blo 587289 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B1257457 : Blo 587289 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B995395 : Blo 587289 995395 := bstep (se 1 (by rfl) ⟨746546, by rfl⟩ : syracuseStep 995395 = 1493093) B1493093
theorem B1323089 : Blo 587289 1323089 := bstep (se 2 (by rfl) ⟨496158, by rfl⟩ : syracuseStep 1323089 = 992317) B992317
theorem B1323107 : Blo 587289 1323107 := bstep (se 1 (by rfl) ⟨992330, by rfl⟩ : syracuseStep 1323107 = 1984661) B1984661
theorem B1061009 : Blo 587289 1061009 := bstep (se 2 (by rfl) ⟨397878, by rfl⟩ : syracuseStep 1061009 = 795757) B795757
theorem B995537 : Blo 587289 995537 := bstep (se 2 (by rfl) ⟨373326, by rfl⟩ : syracuseStep 995537 = 746653) B746653
theorem B798979 : Blo 587289 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B995665 : Blo 587289 995665 := bstep (se 2 (by rfl) ⟨373374, by rfl⟩ : syracuseStep 995665 = 746749) B746749
theorem B1323377 : Blo 587289 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B995699 : Blo 587289 995699 := bstep (se 1 (by rfl) ⟨746774, by rfl⟩ : syracuseStep 995699 = 1493549) B1493549
theorem B1323395 : Blo 587289 1323395 := bstep (se 1 (by rfl) ⟨992546, by rfl⟩ : syracuseStep 1323395 = 1985093) B1985093
theorem B1257859 : Blo 587289 1257859 := bstep (se 1 (by rfl) ⟨943394, by rfl⟩ : syracuseStep 1257859 = 1886789) B1886789
theorem B1814929 : Blo 587289 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B1487281 : Blo 587289 1487281 := bstep (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) B1115461
theorem B995827 : Blo 587289 995827 := bstep (se 1 (by rfl) ⟨746870, by rfl⟩ : syracuseStep 995827 = 1493741) B1493741
theorem B995969 : Blo 587289 995969 := bstep (se 2 (by rfl) ⟨373488, by rfl⟩ : syracuseStep 995969 = 746977) B746977
theorem B1323665 : Blo 587289 1323665 := bstep (se 2 (by rfl) ⟨496374, by rfl⟩ : syracuseStep 1323665 = 992749) B992749
theorem B2044561 : Blo 587289 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B1323683 : Blo 587289 1323683 := bstep (se 1 (by rfl) ⟨992762, by rfl⟩ : syracuseStep 1323683 = 1985525) B1985525
theorem B1487555 : Blo 587289 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B996097 : Blo 587289 996097 := bstep (se 2 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 996097 = 747073) B747073
theorem B996131 : Blo 587289 996131 := bstep (se 1 (by rfl) ⟨747098, by rfl⟩ : syracuseStep 996131 = 1494197) B1494197
theorem B1487747 : Blo 587289 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B996259 : Blo 587289 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B1323953 : Blo 587289 1323953 := bstep (se 2 (by rfl) ⟨496482, by rfl⟩ : syracuseStep 1323953 = 992965) B992965
theorem B1323971 : Blo 587289 1323971 := bstep (se 1 (by rfl) ⟨992978, by rfl⟩ : syracuseStep 1323971 = 1985957) B1985957
theorem B996401 : Blo 587289 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B996529 : Blo 587289 996529 := bstep (se 2 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 996529 = 747397) B747397
theorem B1324241 : Blo 587289 1324241 := bstep (se 2 (by rfl) ⟨496590, by rfl⟩ : syracuseStep 1324241 = 993181) B993181
theorem B996563 : Blo 587289 996563 := bstep (se 1 (by rfl) ⟨747422, by rfl⟩ : syracuseStep 996563 = 1494845) B1494845
theorem B1324259 : Blo 587289 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B2241827 : Blo 587289 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B996691 : Blo 587289 996691 := bstep (se 1 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 996691 = 1495037) B1495037
theorem B5682545 : Blo 587289 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B2012561 : Blo 587289 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B996833 : Blo 587289 996833 := bstep (se 2 (by rfl) ⟨373812, by rfl⟩ : syracuseStep 996833 = 747625) B747625
theorem B1324529 : Blo 587289 1324529 := bstep (se 2 (by rfl) ⟨496698, by rfl⟩ : syracuseStep 1324529 = 993397) B993397
theorem B1324547 : Blo 587289 1324547 := bstep (se 1 (by rfl) ⟨993410, by rfl⟩ : syracuseStep 1324547 = 1986821) B1986821
theorem B3782213 : Blo 587289 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B996961 : Blo 587289 996961 := bstep (se 2 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 996961 = 747721) B747721
theorem B996995 : Blo 587289 996995 := bstep (se 1 (by rfl) ⟨747746, by rfl⟩ : syracuseStep 996995 = 1495493) B1495493
theorem B997123 : Blo 587289 997123 := bstep (se 1 (by rfl) ⟨747842, by rfl⟩ : syracuseStep 997123 = 1495685) B1495685
theorem B1324817 : Blo 587289 1324817 := bstep (se 2 (by rfl) ⟨496806, by rfl⟩ : syracuseStep 1324817 = 993613) B993613
theorem B1324835 : Blo 587289 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B1488689 : Blo 587289 1488689 := bstep (se 2 (by rfl) ⟨558258, by rfl⟩ : syracuseStep 1488689 = 1116517) B1116517
theorem B898913 : Blo 587289 898913 := bstep (se 2 (by rfl) ⟨337092, by rfl⟩ : syracuseStep 898913 = 674185) B674185
theorem B1488739 : Blo 587289 1488739 := bstep (se 1 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 1488739 = 2233109) B2233109
theorem B1259363 : Blo 587289 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B997265 : Blo 587289 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B1488881 : Blo 587289 1488881 := bstep (se 2 (by rfl) ⟨558330, by rfl⟩ : syracuseStep 1488881 = 1116661) B1116661
theorem B997393 : Blo 587289 997393 := bstep (se 2 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 997393 = 748045) B748045
theorem B1325105 : Blo 587289 1325105 := bstep (se 2 (by rfl) ⟨496914, by rfl⟩ : syracuseStep 1325105 = 993829) B993829
theorem B997427 : Blo 587289 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B1325123 : Blo 587289 1325123 := bstep (se 1 (by rfl) ⟨993842, by rfl⟩ : syracuseStep 1325123 = 1987685) B1987685
theorem B997555 : Blo 587289 997555 := bstep (se 1 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 997555 = 1496333) B1496333
theorem B2242829 : Blo 587289 2242829 := bstep (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) B841061
theorem B997697 : Blo 587289 997697 := bstep (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) B748273
theorem B1325393 : Blo 587289 1325393 := bstep (se 2 (by rfl) ⟨497022, by rfl⟩ : syracuseStep 1325393 = 994045) B994045
theorem B1325411 : Blo 587289 1325411 := bstep (se 1 (by rfl) ⟨994058, by rfl⟩ : syracuseStep 1325411 = 1988117) B1988117
theorem B1063459 : Blo 587289 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B1325681 : Blo 587289 1325681 := bstep (se 2 (by rfl) ⟨497130, by rfl⟩ : syracuseStep 1325681 = 994261) B994261
theorem B1325699 : Blo 587289 1325699 := bstep (se 1 (by rfl) ⟨994274, by rfl⟩ : syracuseStep 1325699 = 1988549) B1988549
theorem B1686353 : Blo 587289 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B1325969 : Blo 587289 1325969 := bstep (se 2 (by rfl) ⟨497238, by rfl⟩ : syracuseStep 1325969 = 994477) B994477
theorem B1325987 : Blo 587289 1325987 := bstep (se 1 (by rfl) ⟨994490, by rfl⟩ : syracuseStep 1325987 = 1988981) B1988981
theorem B1489873 : Blo 587289 1489873 := bstep (se 2 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 1489873 = 1117405) B1117405
theorem B1260593 : Blo 587289 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B1883213 : Blo 587289 1883213 := bstep (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) B706205
theorem B6438001 : Blo 587289 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B1326257 : Blo 587289 1326257 := bstep (se 2 (by rfl) ⟨497346, by rfl⟩ : syracuseStep 1326257 = 994693) B994693
theorem B1326275 : Blo 587289 1326275 := bstep (se 1 (by rfl) ⟨994706, by rfl⟩ : syracuseStep 1326275 = 1989413) B1989413
theorem B1883341 : Blo 587289 1883341 := bstep (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) B706253
theorem B1490147 : Blo 587289 1490147 := bstep (se 1 (by rfl) ⟨1117610, by rfl⟩ : syracuseStep 1490147 = 2235221) B2235221
theorem B1817891 : Blo 587289 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B1490339 : Blo 587289 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B1326545 : Blo 587289 1326545 := bstep (se 2 (by rfl) ⟨497454, by rfl⟩ : syracuseStep 1326545 = 994909) B994909
theorem B1326563 : Blo 587289 1326563 := bstep (se 1 (by rfl) ⟨994922, by rfl⟩ : syracuseStep 1326563 = 1989845) B1989845
theorem B1064497 : Blo 587289 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B1326833 : Blo 587289 1326833 := bstep (se 2 (by rfl) ⟨497562, by rfl⟩ : syracuseStep 1326833 = 995125) B995125
theorem B1326851 : Blo 587289 1326851 := bstep (se 1 (by rfl) ⟨995138, by rfl⟩ : syracuseStep 1326851 = 1990277) B1990277
theorem B1982285 : Blo 587289 1982285 := bstep (se 3 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 1982285 = 743357) B743357
theorem B1982339 : Blo 587289 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B1261489 : Blo 587289 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B1261507 : Blo 587289 1261507 := bstep (se 1 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 1261507 = 1892261) B1892261
theorem B1327121 : Blo 587289 1327121 := bstep (se 2 (by rfl) ⟨497670, by rfl⟩ : syracuseStep 1327121 = 995341) B995341
theorem B1327139 : Blo 587289 1327139 := bstep (se 1 (by rfl) ⟨995354, by rfl⟩ : syracuseStep 1327139 = 1990709) B1990709
theorem B5390477 : Blo 587289 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B1982609 : Blo 587289 1982609 := bstep (se 2 (by rfl) ⟨743478, by rfl⟩ : syracuseStep 1982609 = 1486957) B1486957
theorem B1327409 : Blo 587289 1327409 := bstep (se 2 (by rfl) ⟨497778, by rfl⟩ : syracuseStep 1327409 = 995557) B995557
theorem B1327427 : Blo 587289 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B2244941 : Blo 587289 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B1491281 : Blo 587289 1491281 := bstep (se 2 (by rfl) ⟨559230, by rfl⟩ : syracuseStep 1491281 = 1118461) B1118461
theorem B3064177 : Blo 587289 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B1491331 : Blo 587289 1491331 := bstep (se 1 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 1491331 = 2236997) B2236997
theorem B14336453 : Blo 587289 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B1491473 : Blo 587289 1491473 := bstep (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) B1118605
theorem B1589827 : Blo 587289 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B1327697 : Blo 587289 1327697 := bstep (se 2 (by rfl) ⟨497886, by rfl⟩ : syracuseStep 1327697 = 995773) B995773
theorem B1327715 : Blo 587289 1327715 := bstep (se 1 (by rfl) ⟨995786, by rfl⟩ : syracuseStep 1327715 = 1991573) B1991573
theorem B1983149 : Blo 587289 1983149 := bstep (se 3 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 1983149 = 743681) B743681
theorem B3621581 : Blo 587289 3621581 := bstep (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) B1358093
theorem B1983203 : Blo 587289 1983203 := bstep (se 1 (by rfl) ⟨1487402, by rfl⟩ : syracuseStep 1983203 = 2974805) B2974805
theorem B1327985 : Blo 587289 1327985 := bstep (se 2 (by rfl) ⟨497994, by rfl⟩ : syracuseStep 1327985 = 995989) B995989
theorem B1328003 : Blo 587289 1328003 := bstep (se 1 (by rfl) ⟨996002, by rfl⟩ : syracuseStep 1328003 = 1992005) B1992005
theorem B1983473 : Blo 587289 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1885187 : Blo 587289 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B836659 : Blo 587289 836659 := bstep (se 1 (by rfl) ⟨627494, by rfl⟩ : syracuseStep 836659 = 1254989) B1254989
theorem B1885315 : Blo 587289 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B1328273 : Blo 587289 1328273 := bstep (se 2 (by rfl) ⟨498102, by rfl⟩ : syracuseStep 1328273 = 996205) B996205
theorem B1328291 : Blo 587289 1328291 := bstep (se 1 (by rfl) ⟨996218, by rfl⟩ : syracuseStep 1328291 = 1992437) B1992437
theorem B705763 : Blo 587289 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B1885457 : Blo 587289 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B1131875 : Blo 587289 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B836995 : Blo 587289 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B1885571 : Blo 587289 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B1590691 : Blo 587289 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B1328561 : Blo 587289 1328561 := bstep (se 2 (by rfl) ⟨498210, by rfl⟩ : syracuseStep 1328561 = 996421) B996421
theorem B1328579 : Blo 587289 1328579 := bstep (se 1 (by rfl) ⟨996434, by rfl⟩ : syracuseStep 1328579 = 1992869) B1992869
theorem B1492465 : Blo 587289 1492465 := bstep (se 2 (by rfl) ⟨559674, by rfl⟩ : syracuseStep 1492465 = 1119349) B1119349
theorem B706051 : Blo 587289 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B1984013 : Blo 587289 1984013 := bstep (se 3 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 1984013 = 744005) B744005
theorem B1984067 : Blo 587289 1984067 := bstep (se 1 (by rfl) ⟨1488050, by rfl⟩ : syracuseStep 1984067 = 2976101) B2976101
theorem B3360325 : Blo 587289 3360325 := bstep (se 4 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 3360325 = 630061) B630061
theorem B2049731 : Blo 587289 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B1328849 : Blo 587289 1328849 := bstep (se 2 (by rfl) ⟨498318, by rfl⟩ : syracuseStep 1328849 = 996637) B996637
theorem B1328867 : Blo 587289 1328867 := bstep (se 1 (by rfl) ⟨996650, by rfl⟩ : syracuseStep 1328867 = 1993301) B1993301
theorem B1492739 : Blo 587289 1492739 := bstep (se 1 (by rfl) ⟨1119554, by rfl⟩ : syracuseStep 1492739 = 2239109) B2239109
theorem B1984337 : Blo 587289 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B837553 : Blo 587289 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B1492931 : Blo 587289 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B837587 : Blo 587289 837587 := bstep (se 1 (by rfl) ⟨628190, by rfl⟩ : syracuseStep 837587 = 1256381) B1256381
theorem B1329137 : Blo 587289 1329137 := bstep (se 2 (by rfl) ⟨498426, by rfl⟩ : syracuseStep 1329137 = 996853) B996853
theorem B1329155 : Blo 587289 1329155 := bstep (se 1 (by rfl) ⟨996866, by rfl⟩ : syracuseStep 1329155 = 1993733) B1993733
theorem B8505485 : Blo 587289 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1329425 : Blo 587289 1329425 := bstep (se 2 (by rfl) ⟨498534, by rfl⟩ : syracuseStep 1329425 = 997069) B997069
theorem B1329443 : Blo 587289 1329443 := bstep (se 1 (by rfl) ⟨997082, by rfl⟩ : syracuseStep 1329443 = 1994165) B1994165
theorem B1984877 : Blo 587289 1984877 := bstep (se 3 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 1984877 = 744329) B744329
theorem B1984931 : Blo 587289 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B838145 : Blo 587289 838145 := bstep (se 2 (by rfl) ⟨314304, by rfl⟩ : syracuseStep 838145 = 628609) B628609
theorem B1329713 : Blo 587289 1329713 := bstep (se 2 (by rfl) ⟨498642, by rfl⟩ : syracuseStep 1329713 = 997285) B997285
theorem B1329731 : Blo 587289 1329731 := bstep (se 1 (by rfl) ⟨997298, by rfl⟩ : syracuseStep 1329731 = 1994597) B1994597
theorem B838225 : Blo 587289 838225 := bstep (se 2 (by rfl) ⟨314334, by rfl⟩ : syracuseStep 838225 = 628669) B628669
theorem B1985201 : Blo 587289 1985201 := bstep (se 2 (by rfl) ⟨744450, by rfl⟩ : syracuseStep 1985201 = 1488901) B1488901
theorem B3230405 : Blo 587289 3230405 := bstep (se 4 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 3230405 = 605701) B605701
theorem B1330001 : Blo 587289 1330001 := bstep (se 2 (by rfl) ⟨498750, by rfl⟩ : syracuseStep 1330001 = 997501) B997501
theorem B1330019 : Blo 587289 1330019 := bstep (se 1 (by rfl) ⟨997514, by rfl⟩ : syracuseStep 1330019 = 1995029) B1995029
theorem B1493873 : Blo 587289 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B1493923 : Blo 587289 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B1494065 : Blo 587289 1494065 := bstep (se 2 (by rfl) ⟨560274, by rfl⟩ : syracuseStep 1494065 = 1120549) B1120549
theorem B3820621 : Blo 587289 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1887313 : Blo 587289 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B1330289 : Blo 587289 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B1330307 : Blo 587289 1330307 := bstep (se 1 (by rfl) ⟨997730, by rfl⟩ : syracuseStep 1330307 = 1995461) B1995461
theorem B1985741 : Blo 587289 1985741 := bstep (se 3 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 1985741 = 744653) B744653
theorem B1985795 : Blo 587289 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B2510129 : Blo 587289 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B839011 : Blo 587289 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B3362309 : Blo 587289 3362309 := bstep (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) B630433
theorem B1986065 : Blo 587289 1986065 := bstep (se 2 (by rfl) ⟨744774, by rfl⟩ : syracuseStep 1986065 = 1489549) B1489549
theorem B3395141 : Blo 587289 3395141 := bstep (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) B636589
theorem B2838179 : Blo 587289 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B839489 : Blo 587289 839489 := bstep (se 2 (by rfl) ⟨314808, by rfl⟩ : syracuseStep 839489 = 629617) B629617
theorem B4542277 : Blo 587289 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B839603 : Blo 587289 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B2510797 : Blo 587289 2510797 := bstep (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) B941549
theorem B839683 : Blo 587289 839683 := bstep (se 1 (by rfl) ⟨629762, by rfl⟩ : syracuseStep 839683 = 1259525) B1259525
theorem B1495057 : Blo 587289 1495057 := bstep (se 2 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 1495057 = 1121293) B1121293
theorem B1986605 : Blo 587289 1986605 := bstep (se 3 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 1986605 = 744977) B744977
theorem B5656675 : Blo 587289 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B1986659 : Blo 587289 1986659 := bstep (se 1 (by rfl) ⟨1489994, by rfl⟩ : syracuseStep 1986659 = 2979989) B2979989
theorem B4018339 : Blo 587289 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B2019491 : Blo 587289 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1888429 : Blo 587289 1888429 := bstep (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) B708161
theorem B1495331 : Blo 587289 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B1986929 : Blo 587289 1986929 := bstep (se 2 (by rfl) ⟨745098, by rfl⟩ : syracuseStep 1986929 = 1490197) B1490197
theorem B1495523 : Blo 587289 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B2511395 : Blo 587289 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B840241 : Blo 587289 840241 := bstep (se 2 (by rfl) ⟨315090, by rfl⟩ : syracuseStep 840241 = 630181) B630181
theorem B709507 : Blo 587289 709507 := bstep (se 1 (by rfl) ⟨532130, by rfl⟩ : syracuseStep 709507 = 1064261) B1064261
theorem B1987469 : Blo 587289 1987469 := bstep (se 3 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 1987469 = 745301) B745301
theorem B1987523 : Blo 587289 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B906209 : Blo 587289 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B11293667 : Blo 587289 11293667 := bstep (se 1 (by rfl) ⟨8470250, by rfl⟩ : syracuseStep 11293667 = 16940501) B16940501
theorem B1889261 : Blo 587289 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B1791085 : Blo 587289 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B6804593 : Blo 587289 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B1987793 : Blo 587289 1987793 := bstep (se 2 (by rfl) ⟨745422, by rfl⟩ : syracuseStep 1987793 = 1490845) B1490845
theorem B840947 : Blo 587289 840947 := bstep (se 1 (by rfl) ⟨630710, by rfl⟩ : syracuseStep 840947 = 1261421) B1261421
theorem B1496465 : Blo 587289 1496465 := bstep (se 2 (by rfl) ⟨561174, by rfl⟩ : syracuseStep 1496465 = 1122349) B1122349
theorem B808385 : Blo 587289 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B1496515 : Blo 587289 1496515 := bstep (se 1 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 1496515 = 2244773) B2244773
theorem B4085261 : Blo 587289 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B1496657 : Blo 587289 1496657 := bstep (se 2 (by rfl) ⟨561246, by rfl⟩ : syracuseStep 1496657 = 1122493) B1122493
theorem B1988333 : Blo 587289 1988333 := bstep (se 3 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 1988333 = 745625) B745625
theorem B2119409 : Blo 587289 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B1988387 : Blo 587289 1988387 := bstep (se 1 (by rfl) ⟨1491290, by rfl⟩ : syracuseStep 1988387 = 2982581) B2982581
theorem B2119537 : Blo 587289 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B841585 : Blo 587289 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B743347 : Blo 587289 743347 := bstep (se 1 (by rfl) ⟨557510, by rfl⟩ : syracuseStep 743347 = 1115021) B1115021
theorem B808915 : Blo 587289 808915 := bstep (se 1 (by rfl) ⟨606686, by rfl⟩ : syracuseStep 808915 = 1213373) B1213373
theorem B841699 : Blo 587289 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B1988657 : Blo 587289 1988657 := bstep (se 2 (by rfl) ⟨745746, by rfl⟩ : syracuseStep 1988657 = 1491493) B1491493
theorem B1792145 : Blo 587289 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1136963 : Blo 587289 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B743843 : Blo 587289 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B1989197 : Blo 587289 1989197 := bstep (se 3 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 1989197 = 745949) B745949
theorem B1989251 : Blo 587289 1989251 := bstep (se 1 (by rfl) ⟨1491938, by rfl⟩ : syracuseStep 1989251 = 2983877) B2983877
theorem B3595013 : Blo 587289 3595013 := bstep (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) B674065
theorem B1792835 : Blo 587289 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B1137539 : Blo 587289 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1989521 : Blo 587289 1989521 := bstep (se 2 (by rfl) ⟨746070, by rfl⟩ : syracuseStep 1989521 = 1492141) B1492141
theorem B1891363 : Blo 587289 1891363 := bstep (se 1 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 1891363 = 2837045) B2837045
theorem B744547 : Blo 587289 744547 := bstep (se 1 (by rfl) ⟨558410, by rfl⟩ : syracuseStep 744547 = 1116821) B1116821
theorem B1891505 : Blo 587289 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B744643 : Blo 587289 744643 := bstep (se 1 (by rfl) ⟨558482, by rfl⟩ : syracuseStep 744643 = 1116965) B1116965
theorem B3366157 : Blo 587289 3366157 := bstep (se 3 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 3366157 = 1262309) B1262309
theorem B1400113 : Blo 587289 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B1990061 : Blo 587289 1990061 := bstep (se 3 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 1990061 = 746273) B746273
theorem B1990115 : Blo 587289 1990115 := bstep (se 1 (by rfl) ⟨1492586, by rfl⟩ : syracuseStep 1990115 = 2985173) B2985173
theorem B941555 : Blo 587289 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B2973347 : Blo 587289 2973347 := bstep (se 1 (by rfl) ⟨2230010, by rfl⟩ : syracuseStep 2973347 = 4460021) B4460021
theorem B1597091 : Blo 587289 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B745139 : Blo 587289 745139 := bstep (se 1 (by rfl) ⟨558854, by rfl⟩ : syracuseStep 745139 = 1117709) B1117709
theorem B2416355 : Blo 587289 2416355 := bstep (se 1 (by rfl) ⟨1812266, by rfl⟩ : syracuseStep 2416355 = 3624533) B3624533
theorem B5660401 : Blo 587289 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B1990385 : Blo 587289 1990385 := bstep (se 2 (by rfl) ⟨746394, by rfl⟩ : syracuseStep 1990385 = 1492789) B1492789
theorem B1793933 : Blo 587289 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B5103587 : Blo 587289 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B4251761 : Blo 587289 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B2515171 : Blo 587289 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B1990925 : Blo 587289 1990925 := bstep (se 3 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 1990925 = 746597) B746597
theorem B942401 : Blo 587289 942401 := bstep (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) B706801
theorem B1990979 : Blo 587289 1990979 := bstep (se 1 (by rfl) ⟨1493234, by rfl⟩ : syracuseStep 1990979 = 2986469) B2986469
theorem B745843 : Blo 587289 745843 := bstep (se 1 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 745843 = 1118765) B1118765
theorem B2974157 : Blo 587289 2974157 := bstep (se 3 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 2974157 = 1115309) B1115309
theorem B745939 : Blo 587289 745939 := bstep (se 1 (by rfl) ⟨559454, by rfl⟩ : syracuseStep 745939 = 1118909) B1118909
theorem B1991249 : Blo 587289 1991249 := bstep (se 2 (by rfl) ⟨746718, by rfl⟩ : syracuseStep 1991249 = 1493437) B1493437
theorem B51602197 : Blo 587289 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B4481891 : Blo 587289 4481891 := bstep (se 1 (by rfl) ⟨3361418, by rfl⟩ : syracuseStep 4481891 = 6722837) B6722837
theorem B1696621 : Blo 587289 1696621 := bstep (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) B636233
theorem B746435 : Blo 587289 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B943139 : Blo 587289 943139 := bstep (se 1 (by rfl) ⟨707354, by rfl⟩ : syracuseStep 943139 = 1414709) B1414709
theorem B910387 : Blo 587289 910387 := bstep (se 1 (by rfl) ⟨682790, by rfl⟩ : syracuseStep 910387 = 1365581) B1365581
theorem B1795171 : Blo 587289 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B1991789 : Blo 587289 1991789 := bstep (se 3 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 1991789 = 746921) B746921
theorem B1991843 : Blo 587289 1991843 := bstep (se 1 (by rfl) ⟨1493882, by rfl⟩ : syracuseStep 1991843 = 2987765) B2987765
theorem B1992113 : Blo 587289 1992113 := bstep (se 2 (by rfl) ⟨747042, by rfl⟩ : syracuseStep 1992113 = 1494085) B1494085
theorem B1893901 : Blo 587289 1893901 := bstep (se 3 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 1893901 = 710213) B710213
theorem B7530083 : Blo 587289 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B747139 : Blo 587289 747139 := bstep (se 1 (by rfl) ⟨560354, by rfl⟩ : syracuseStep 747139 = 1120709) B1120709
theorem B747235 : Blo 587289 747235 := bstep (se 1 (by rfl) ⟨560426, by rfl⟩ : syracuseStep 747235 = 1120853) B1120853
theorem B2385713 : Blo 587289 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B5039941 : Blo 587289 5039941 := bstep (se 4 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 5039941 = 944989) B944989
theorem B1992653 : Blo 587289 1992653 := bstep (se 3 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 1992653 = 747245) B747245
theorem B944131 : Blo 587289 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B1992707 : Blo 587289 1992707 := bstep (se 1 (by rfl) ⟨1494530, by rfl⟩ : syracuseStep 1992707 = 2989061) B2989061
theorem B2517169 : Blo 587289 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B747731 : Blo 587289 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B944369 : Blo 587289 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B1992977 : Blo 587289 1992977 := bstep (se 2 (by rfl) ⟨747366, by rfl⟩ : syracuseStep 1992977 = 1494733) B1494733
theorem B944579 : Blo 587289 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B1698403 : Blo 587289 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B10775267 : Blo 587289 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B1993517 : Blo 587289 1993517 := bstep (se 3 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 1993517 = 747569) B747569
theorem B1010497 : Blo 587289 1010497 := bstep (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) B757873
theorem B3763043 : Blo 587289 3763043 := bstep (se 1 (by rfl) ⟨2822282, by rfl⟩ : syracuseStep 3763043 = 5644565) B5644565
theorem B1993571 : Blo 587289 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B1698769 : Blo 587289 1698769 := bstep (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) B1274077
theorem B2124785 : Blo 587289 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2583587 : Blo 587289 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B1993841 : Blo 587289 1993841 := bstep (se 2 (by rfl) ⟨747690, by rfl⟩ : syracuseStep 1993841 = 1495381) B1495381
theorem B1010819 : Blo 587289 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B945361 : Blo 587289 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B2977073 : Blo 587289 2977073 := bstep (se 2 (by rfl) ⟨1116402, by rfl⟩ : syracuseStep 2977073 = 2232805) B2232805
theorem B3403313 : Blo 587289 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B1994381 : Blo 587289 1994381 := bstep (se 3 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 1994381 = 747893) B747893
theorem B1994435 : Blo 587289 1994435 := bstep (se 1 (by rfl) ⟨1495826, by rfl⟩ : syracuseStep 1994435 = 2991653) B2991653
theorem B2387789 : Blo 587289 2387789 := bstep (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) B895421
theorem B2125709 : Blo 587289 2125709 := bstep (se 3 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 2125709 = 797141) B797141
theorem B1994705 : Blo 587289 1994705 := bstep (se 2 (by rfl) ⟨748014, by rfl⟩ : syracuseStep 1994705 = 1496029) B1496029
theorem B946163 : Blo 587289 946163 := bstep (se 1 (by rfl) ⟨709622, by rfl⟩ : syracuseStep 946163 = 1419245) B1419245
theorem B1208369 : Blo 587289 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B2388017 : Blo 587289 2388017 := bstep (se 2 (by rfl) ⟨895506, by rfl⟩ : syracuseStep 2388017 = 1791013) B1791013
theorem B7270469 : Blo 587289 7270469 := bstep (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) B1363213
theorem B880961 : Blo 587289 880961 := bstep (se 2 (by rfl) ⟨330360, by rfl⟩ : syracuseStep 880961 = 660721) B660721
theorem B880979 : Blo 587289 880979 := bstep (se 1 (by rfl) ⟨660734, by rfl⟩ : syracuseStep 880979 = 1321469) B1321469
theorem B881009 : Blo 587289 881009 := bstep (se 2 (by rfl) ⟨330378, by rfl⟩ : syracuseStep 881009 = 660757) B660757
theorem B881027 : Blo 587289 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B881057 : Blo 587289 881057 := bstep (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) B660793
theorem B881075 : Blo 587289 881075 := bstep (se 1 (by rfl) ⟨660806, by rfl⟩ : syracuseStep 881075 = 1321613) B1321613
theorem B1208771 : Blo 587289 1208771 := bstep (se 1 (by rfl) ⟨906578, by rfl⟩ : syracuseStep 1208771 = 1813157) B1813157
theorem B881105 : Blo 587289 881105 := bstep (se 2 (by rfl) ⟨330414, by rfl⟩ : syracuseStep 881105 = 660829) B660829
theorem B881123 : Blo 587289 881123 := bstep (se 1 (by rfl) ⟨660842, by rfl⟩ : syracuseStep 881123 = 1321685) B1321685
theorem B1995245 : Blo 587289 1995245 := bstep (se 3 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 1995245 = 748217) B748217
theorem B946675 : Blo 587289 946675 := bstep (se 1 (by rfl) ⟨710006, by rfl⟩ : syracuseStep 946675 = 1420013) B1420013
theorem B881153 : Blo 587289 881153 := bstep (se 2 (by rfl) ⟨330432, by rfl⟩ : syracuseStep 881153 = 660865) B660865
theorem B881171 : Blo 587289 881171 := bstep (se 1 (by rfl) ⟨660878, by rfl⟩ : syracuseStep 881171 = 1321757) B1321757
theorem B1995299 : Blo 587289 1995299 := bstep (se 1 (by rfl) ⟨1496474, by rfl⟩ : syracuseStep 1995299 = 2992949) B2992949
theorem B881201 : Blo 587289 881201 := bstep (se 2 (by rfl) ⟨330450, by rfl⟩ : syracuseStep 881201 = 660901) B660901
theorem B881219 : Blo 587289 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B881249 : Blo 587289 881249 := bstep (se 2 (by rfl) ⟨330468, by rfl⟩ : syracuseStep 881249 = 660937) B660937
theorem B848497 : Blo 587289 848497 := bstep (se 2 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 848497 = 636373) B636373
theorem B881267 : Blo 587289 881267 := bstep (se 1 (by rfl) ⟨660950, by rfl⟩ : syracuseStep 881267 = 1321901) B1321901
theorem B881297 : Blo 587289 881297 := bstep (se 2 (by rfl) ⟨330486, by rfl⟩ : syracuseStep 881297 = 660973) B660973
theorem B881315 : Blo 587289 881315 := bstep (se 1 (by rfl) ⟨660986, by rfl⟩ : syracuseStep 881315 = 1321973) B1321973
theorem B881345 : Blo 587289 881345 := bstep (se 2 (by rfl) ⟨330504, by rfl⟩ : syracuseStep 881345 = 661009) B661009
theorem B881363 : Blo 587289 881363 := bstep (se 1 (by rfl) ⟨661022, by rfl⟩ : syracuseStep 881363 = 1322045) B1322045
theorem B2978531 : Blo 587289 2978531 := bstep (se 1 (by rfl) ⟨2233898, by rfl⟩ : syracuseStep 2978531 = 4467797) B4467797
theorem B881393 : Blo 587289 881393 := bstep (se 2 (by rfl) ⟨330522, by rfl⟩ : syracuseStep 881393 = 661045) B661045
theorem B881411 : Blo 587289 881411 := bstep (se 1 (by rfl) ⟨661058, by rfl⟩ : syracuseStep 881411 = 1322117) B1322117
theorem B881441 : Blo 587289 881441 := bstep (se 2 (by rfl) ⟨330540, by rfl⟩ : syracuseStep 881441 = 661081) B661081
theorem B1995569 : Blo 587289 1995569 := bstep (se 2 (by rfl) ⟨748338, by rfl⟩ : syracuseStep 1995569 = 1496677) B1496677
theorem B881459 : Blo 587289 881459 := bstep (se 1 (by rfl) ⟨661094, by rfl⟩ : syracuseStep 881459 = 1322189) B1322189
theorem B881489 : Blo 587289 881489 := bstep (se 2 (by rfl) ⟨330558, by rfl⟩ : syracuseStep 881489 = 661117) B661117
theorem B1700689 : Blo 587289 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B881507 : Blo 587289 881507 := bstep (se 1 (by rfl) ⟨661130, by rfl⟩ : syracuseStep 881507 = 1322261) B1322261
theorem B881537 : Blo 587289 881537 := bstep (se 2 (by rfl) ⟨330576, by rfl⟩ : syracuseStep 881537 = 661153) B661153
theorem B881555 : Blo 587289 881555 := bstep (se 1 (by rfl) ⟨661166, by rfl⟩ : syracuseStep 881555 = 1322333) B1322333
theorem B881585 : Blo 587289 881585 := bstep (se 2 (by rfl) ⟨330594, by rfl⟩ : syracuseStep 881585 = 661189) B661189
theorem B881603 : Blo 587289 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B881633 : Blo 587289 881633 := bstep (se 2 (by rfl) ⟨330612, by rfl⟩ : syracuseStep 881633 = 661225) B661225
theorem B881651 : Blo 587289 881651 := bstep (se 1 (by rfl) ⟨661238, by rfl⟩ : syracuseStep 881651 = 1322477) B1322477
theorem B881681 : Blo 587289 881681 := bstep (se 2 (by rfl) ⟨330630, by rfl⟩ : syracuseStep 881681 = 661261) B661261
theorem B881699 : Blo 587289 881699 := bstep (se 1 (by rfl) ⟨661274, by rfl⟩ : syracuseStep 881699 = 1322549) B1322549
theorem B881729 : Blo 587289 881729 := bstep (se 2 (by rfl) ⟨330648, by rfl⟩ : syracuseStep 881729 = 661297) B661297
theorem B881747 : Blo 587289 881747 := bstep (se 1 (by rfl) ⟨661310, by rfl⟩ : syracuseStep 881747 = 1322621) B1322621
theorem B881777 : Blo 587289 881777 := bstep (se 2 (by rfl) ⟨330666, by rfl⟩ : syracuseStep 881777 = 661333) B661333
theorem B881795 : Blo 587289 881795 := bstep (se 1 (by rfl) ⟨661346, by rfl⟩ : syracuseStep 881795 = 1322693) B1322693
theorem B881825 : Blo 587289 881825 := bstep (se 2 (by rfl) ⟨330684, by rfl⟩ : syracuseStep 881825 = 661369) B661369
theorem B881843 : Blo 587289 881843 := bstep (se 1 (by rfl) ⟨661382, by rfl⟩ : syracuseStep 881843 = 1322765) B1322765
theorem B4027589 : Blo 587289 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B881873 : Blo 587289 881873 := bstep (se 2 (by rfl) ⟨330702, by rfl⟩ : syracuseStep 881873 = 661405) B661405
theorem B881891 : Blo 587289 881891 := bstep (se 1 (by rfl) ⟨661418, by rfl⟩ : syracuseStep 881891 = 1322837) B1322837
theorem B1799405 : Blo 587289 1799405 := bstep (se 3 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 1799405 = 674777) B674777
theorem B881921 : Blo 587289 881921 := bstep (se 2 (by rfl) ⟨330720, by rfl⟩ : syracuseStep 881921 = 661441) B661441
theorem B881939 : Blo 587289 881939 := bstep (se 1 (by rfl) ⟨661454, by rfl⟩ : syracuseStep 881939 = 1322909) B1322909
theorem B2389283 : Blo 587289 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B881969 : Blo 587289 881969 := bstep (se 2 (by rfl) ⟨330738, by rfl⟩ : syracuseStep 881969 = 661477) B661477
theorem B881987 : Blo 587289 881987 := bstep (se 1 (by rfl) ⟨661490, by rfl⟩ : syracuseStep 881987 = 1322981) B1322981
theorem B882017 : Blo 587289 882017 := bstep (se 2 (by rfl) ⟨330756, by rfl⟩ : syracuseStep 882017 = 661513) B661513
theorem B882035 : Blo 587289 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B882065 : Blo 587289 882065 := bstep (se 2 (by rfl) ⟨330774, by rfl⟩ : syracuseStep 882065 = 661549) B661549
theorem B882083 : Blo 587289 882083 := bstep (se 1 (by rfl) ⟨661562, by rfl⟩ : syracuseStep 882083 = 1323125) B1323125
theorem B882113 : Blo 587289 882113 := bstep (se 2 (by rfl) ⟨330792, by rfl⟩ : syracuseStep 882113 = 661585) B661585
theorem B882131 : Blo 587289 882131 := bstep (se 1 (by rfl) ⟨661598, by rfl⟩ : syracuseStep 882131 = 1323197) B1323197
theorem B882161 : Blo 587289 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B882179 : Blo 587289 882179 := bstep (se 1 (by rfl) ⟨661634, by rfl⟩ : syracuseStep 882179 = 1323269) B1323269
theorem B2979341 : Blo 587289 2979341 := bstep (se 3 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 2979341 = 1117253) B1117253
theorem B882209 : Blo 587289 882209 := bstep (se 2 (by rfl) ⟨330828, by rfl⟩ : syracuseStep 882209 = 661657) B661657
theorem B587299 : Blo 587289 587299 := bstep (se 1 (by rfl) ⟨440474, by rfl⟩ : syracuseStep 587299 = 880949) B880949
theorem B587315 : Blo 587289 587315 := bstep (se 1 (by rfl) ⟨440486, by rfl⟩ : syracuseStep 587315 = 880973) B880973
theorem B882227 : Blo 587289 882227 := bstep (se 1 (by rfl) ⟨661670, by rfl⟩ : syracuseStep 882227 = 1323341) B1323341
theorem B587331 : Blo 587289 587331 := bstep (se 1 (by rfl) ⟨440498, by rfl⟩ : syracuseStep 587331 = 880997) B880997
theorem B882257 : Blo 587289 882257 := bstep (se 2 (by rfl) ⟨330846, by rfl⟩ : syracuseStep 882257 = 661693) B661693
theorem B587347 : Blo 587289 587347 := bstep (se 1 (by rfl) ⟨440510, by rfl⟩ : syracuseStep 587347 = 881021) B881021
theorem B587363 : Blo 587289 587363 := bstep (se 1 (by rfl) ⟨440522, by rfl⟩ : syracuseStep 587363 = 881045) B881045
theorem B882275 : Blo 587289 882275 := bstep (se 1 (by rfl) ⟨661706, by rfl⟩ : syracuseStep 882275 = 1323413) B1323413
theorem B587379 : Blo 587289 587379 := bstep (se 1 (by rfl) ⟨440534, by rfl⟩ : syracuseStep 587379 = 881069) B881069
theorem B882305 : Blo 587289 882305 := bstep (se 2 (by rfl) ⟨330864, by rfl⟩ : syracuseStep 882305 = 661729) B661729
theorem B587395 : Blo 587289 587395 := bstep (se 1 (by rfl) ⟨440546, by rfl⟩ : syracuseStep 587395 = 881093) B881093
theorem B587411 : Blo 587289 587411 := bstep (se 1 (by rfl) ⟨440558, by rfl⟩ : syracuseStep 587411 = 881117) B881117
theorem B882323 : Blo 587289 882323 := bstep (se 1 (by rfl) ⟨661742, by rfl⟩ : syracuseStep 882323 = 1323485) B1323485
theorem B587427 : Blo 587289 587427 := bstep (se 1 (by rfl) ⟨440570, by rfl⟩ : syracuseStep 587427 = 881141) B881141
theorem B882353 : Blo 587289 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B587443 : Blo 587289 587443 := bstep (se 1 (by rfl) ⟨440582, by rfl⟩ : syracuseStep 587443 = 881165) B881165
theorem B587459 : Blo 587289 587459 := bstep (se 1 (by rfl) ⟨440594, by rfl⟩ : syracuseStep 587459 = 881189) B881189
theorem B882371 : Blo 587289 882371 := bstep (se 1 (by rfl) ⟨661778, by rfl⟩ : syracuseStep 882371 = 1323557) B1323557
theorem B587475 : Blo 587289 587475 := bstep (se 1 (by rfl) ⟨440606, by rfl⟩ : syracuseStep 587475 = 881213) B881213
theorem B882401 : Blo 587289 882401 := bstep (se 2 (by rfl) ⟨330900, by rfl⟩ : syracuseStep 882401 = 661801) B661801
theorem B587491 : Blo 587289 587491 := bstep (se 1 (by rfl) ⟨440618, by rfl⟩ : syracuseStep 587491 = 881237) B881237
theorem B587507 : Blo 587289 587507 := bstep (se 1 (by rfl) ⟨440630, by rfl⟩ : syracuseStep 587507 = 881261) B881261
theorem B882419 : Blo 587289 882419 := bstep (se 1 (by rfl) ⟨661814, by rfl⟩ : syracuseStep 882419 = 1323629) B1323629
theorem B587523 : Blo 587289 587523 := bstep (se 1 (by rfl) ⟨440642, by rfl⟩ : syracuseStep 587523 = 881285) B881285
theorem B882449 : Blo 587289 882449 := bstep (se 2 (by rfl) ⟨330918, by rfl⟩ : syracuseStep 882449 = 661837) B661837
theorem B587539 : Blo 587289 587539 := bstep (se 1 (by rfl) ⟨440654, by rfl⟩ : syracuseStep 587539 = 881309) B881309
theorem B587555 : Blo 587289 587555 := bstep (se 1 (by rfl) ⟨440666, by rfl⟩ : syracuseStep 587555 = 881333) B881333
theorem B882467 : Blo 587289 882467 := bstep (se 1 (by rfl) ⟨661850, by rfl⟩ : syracuseStep 882467 = 1323701) B1323701
theorem B587571 : Blo 587289 587571 := bstep (se 1 (by rfl) ⟨440678, by rfl⟩ : syracuseStep 587571 = 881357) B881357
theorem B882497 : Blo 587289 882497 := bstep (se 2 (by rfl) ⟨330936, by rfl⟩ : syracuseStep 882497 = 661873) B661873
theorem B587587 : Blo 587289 587587 := bstep (se 1 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 587587 = 881381) B881381
theorem B587603 : Blo 587289 587603 := bstep (se 1 (by rfl) ⟨440702, by rfl⟩ : syracuseStep 587603 = 881405) B881405
theorem B882515 : Blo 587289 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B587619 : Blo 587289 587619 := bstep (se 1 (by rfl) ⟨440714, by rfl⟩ : syracuseStep 587619 = 881429) B881429
theorem B882545 : Blo 587289 882545 := bstep (se 2 (by rfl) ⟨330954, by rfl⟩ : syracuseStep 882545 = 661909) B661909
theorem B587635 : Blo 587289 587635 := bstep (se 1 (by rfl) ⟨440726, by rfl⟩ : syracuseStep 587635 = 881453) B881453
theorem B587651 : Blo 587289 587651 := bstep (se 1 (by rfl) ⟨440738, by rfl⟩ : syracuseStep 587651 = 881477) B881477
theorem B882563 : Blo 587289 882563 := bstep (se 1 (by rfl) ⟨661922, by rfl⟩ : syracuseStep 882563 = 1323845) B1323845
theorem B587667 : Blo 587289 587667 := bstep (se 1 (by rfl) ⟨440750, by rfl⟩ : syracuseStep 587667 = 881501) B881501
theorem B882593 : Blo 587289 882593 := bstep (se 2 (by rfl) ⟨330972, by rfl⟩ : syracuseStep 882593 = 661945) B661945
theorem B587683 : Blo 587289 587683 := bstep (se 1 (by rfl) ⟨440762, by rfl⟩ : syracuseStep 587683 = 881525) B881525
theorem B587699 : Blo 587289 587699 := bstep (se 1 (by rfl) ⟨440774, by rfl⟩ : syracuseStep 587699 = 881549) B881549
theorem B882611 : Blo 587289 882611 := bstep (se 1 (by rfl) ⟨661958, by rfl⟩ : syracuseStep 882611 = 1323917) B1323917
theorem B587715 : Blo 587289 587715 := bstep (se 1 (by rfl) ⟨440786, by rfl⟩ : syracuseStep 587715 = 881573) B881573
theorem B882641 : Blo 587289 882641 := bstep (se 2 (by rfl) ⟨330990, by rfl⟩ : syracuseStep 882641 = 661981) B661981
theorem B587731 : Blo 587289 587731 := bstep (se 1 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 587731 = 881597) B881597
theorem B587747 : Blo 587289 587747 := bstep (se 1 (by rfl) ⟨440810, by rfl⟩ : syracuseStep 587747 = 881621) B881621
theorem B882659 : Blo 587289 882659 := bstep (se 1 (by rfl) ⟨661994, by rfl⟩ : syracuseStep 882659 = 1323989) B1323989
theorem B587763 : Blo 587289 587763 := bstep (se 1 (by rfl) ⟨440822, by rfl⟩ : syracuseStep 587763 = 881645) B881645
theorem B882689 : Blo 587289 882689 := bstep (se 2 (by rfl) ⟨331008, by rfl⟩ : syracuseStep 882689 = 662017) B662017
theorem B587779 : Blo 587289 587779 := bstep (se 1 (by rfl) ⟨440834, by rfl⟩ : syracuseStep 587779 = 881669) B881669
theorem B587795 : Blo 587289 587795 := bstep (se 1 (by rfl) ⟨440846, by rfl⟩ : syracuseStep 587795 = 881693) B881693
theorem B882707 : Blo 587289 882707 := bstep (se 1 (by rfl) ⟨662030, by rfl⟩ : syracuseStep 882707 = 1324061) B1324061
theorem B587811 : Blo 587289 587811 := bstep (se 1 (by rfl) ⟨440858, by rfl⟩ : syracuseStep 587811 = 881717) B881717
theorem B882737 : Blo 587289 882737 := bstep (se 2 (by rfl) ⟨331026, by rfl⟩ : syracuseStep 882737 = 662053) B662053
theorem B587827 : Blo 587289 587827 := bstep (se 1 (by rfl) ⟨440870, by rfl⟩ : syracuseStep 587827 = 881741) B881741
theorem B587843 : Blo 587289 587843 := bstep (se 1 (by rfl) ⟨440882, by rfl⟩ : syracuseStep 587843 = 881765) B881765
theorem B882755 : Blo 587289 882755 := bstep (se 1 (by rfl) ⟨662066, by rfl⟩ : syracuseStep 882755 = 1324133) B1324133
theorem B4487237 : Blo 587289 4487237 := bstep (se 4 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 4487237 = 841357) B841357
theorem B587859 : Blo 587289 587859 := bstep (se 1 (by rfl) ⟨440894, by rfl⟩ : syracuseStep 587859 = 881789) B881789
theorem B882785 : Blo 587289 882785 := bstep (se 2 (by rfl) ⟨331044, by rfl⟩ : syracuseStep 882785 = 662089) B662089
theorem B587875 : Blo 587289 587875 := bstep (se 1 (by rfl) ⟨440906, by rfl⟩ : syracuseStep 587875 = 881813) B881813
theorem B2521201 : Blo 587289 2521201 := bstep (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) B1890901
theorem B587891 : Blo 587289 587891 := bstep (se 1 (by rfl) ⟨440918, by rfl⟩ : syracuseStep 587891 = 881837) B881837
theorem B882803 : Blo 587289 882803 := bstep (se 1 (by rfl) ⟨662102, by rfl⟩ : syracuseStep 882803 = 1324205) B1324205
theorem B587907 : Blo 587289 587907 := bstep (se 1 (by rfl) ⟨440930, by rfl⟩ : syracuseStep 587907 = 881861) B881861
theorem B882833 : Blo 587289 882833 := bstep (se 2 (by rfl) ⟨331062, by rfl⟩ : syracuseStep 882833 = 662125) B662125
theorem B587923 : Blo 587289 587923 := bstep (se 1 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 587923 = 881885) B881885
theorem B587939 : Blo 587289 587939 := bstep (se 1 (by rfl) ⟨440954, by rfl⟩ : syracuseStep 587939 = 881909) B881909
theorem B882851 : Blo 587289 882851 := bstep (se 1 (by rfl) ⟨662138, by rfl⟩ : syracuseStep 882851 = 1324277) B1324277
theorem B587955 : Blo 587289 587955 := bstep (se 1 (by rfl) ⟨440966, by rfl⟩ : syracuseStep 587955 = 881933) B881933
theorem B882881 : Blo 587289 882881 := bstep (se 2 (by rfl) ⟨331080, by rfl⟩ : syracuseStep 882881 = 662161) B662161
theorem B587971 : Blo 587289 587971 := bstep (se 1 (by rfl) ⟨440978, by rfl⟩ : syracuseStep 587971 = 881957) B881957
theorem B587987 : Blo 587289 587987 := bstep (se 1 (by rfl) ⟨440990, by rfl⟩ : syracuseStep 587987 = 881981) B881981
theorem B882899 : Blo 587289 882899 := bstep (se 1 (by rfl) ⟨662174, by rfl⟩ : syracuseStep 882899 = 1324349) B1324349
theorem B588003 : Blo 587289 588003 := bstep (se 1 (by rfl) ⟨441002, by rfl⟩ : syracuseStep 588003 = 882005) B882005
theorem B882929 : Blo 587289 882929 := bstep (se 2 (by rfl) ⟨331098, by rfl⟩ : syracuseStep 882929 = 662197) B662197
theorem B588019 : Blo 587289 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B588035 : Blo 587289 588035 := bstep (se 1 (by rfl) ⟨441026, by rfl⟩ : syracuseStep 588035 = 882053) B882053
theorem B882947 : Blo 587289 882947 := bstep (se 1 (by rfl) ⟨662210, by rfl⟩ : syracuseStep 882947 = 1324421) B1324421
theorem B588051 : Blo 587289 588051 := bstep (se 1 (by rfl) ⟨441038, by rfl⟩ : syracuseStep 588051 = 882077) B882077
theorem B882977 : Blo 587289 882977 := bstep (se 2 (by rfl) ⟨331116, by rfl⟩ : syracuseStep 882977 = 662233) B662233
theorem B588067 : Blo 587289 588067 := bstep (se 1 (by rfl) ⟨441050, by rfl⟩ : syracuseStep 588067 = 882101) B882101
theorem B588083 : Blo 587289 588083 := bstep (se 1 (by rfl) ⟨441062, by rfl⟩ : syracuseStep 588083 = 882125) B882125
theorem B882995 : Blo 587289 882995 := bstep (se 1 (by rfl) ⟨662246, by rfl⟩ : syracuseStep 882995 = 1324493) B1324493
theorem B588099 : Blo 587289 588099 := bstep (se 1 (by rfl) ⟨441074, by rfl⟩ : syracuseStep 588099 = 882149) B882149
theorem B883025 : Blo 587289 883025 := bstep (se 2 (by rfl) ⟨331134, by rfl⟩ : syracuseStep 883025 = 662269) B662269
theorem B588115 : Blo 587289 588115 := bstep (se 1 (by rfl) ⟨441086, by rfl⟩ : syracuseStep 588115 = 882173) B882173
theorem B588131 : Blo 587289 588131 := bstep (se 1 (by rfl) ⟨441098, by rfl⟩ : syracuseStep 588131 = 882197) B882197
theorem B883043 : Blo 587289 883043 := bstep (se 1 (by rfl) ⟨662282, by rfl⟩ : syracuseStep 883043 = 1324565) B1324565
theorem B588147 : Blo 587289 588147 := bstep (se 1 (by rfl) ⟨441110, by rfl⟩ : syracuseStep 588147 = 882221) B882221
theorem B883073 : Blo 587289 883073 := bstep (se 2 (by rfl) ⟨331152, by rfl⟩ : syracuseStep 883073 = 662305) B662305
theorem B588163 : Blo 587289 588163 := bstep (se 1 (by rfl) ⟨441122, by rfl⟩ : syracuseStep 588163 = 882245) B882245
theorem B588179 : Blo 587289 588179 := bstep (se 1 (by rfl) ⟨441134, by rfl⟩ : syracuseStep 588179 = 882269) B882269
theorem B883091 : Blo 587289 883091 := bstep (se 1 (by rfl) ⟨662318, by rfl⟩ : syracuseStep 883091 = 1324637) B1324637
theorem B588195 : Blo 587289 588195 := bstep (se 1 (by rfl) ⟨441146, by rfl⟩ : syracuseStep 588195 = 882293) B882293
theorem B883121 : Blo 587289 883121 := bstep (se 2 (by rfl) ⟨331170, by rfl⟩ : syracuseStep 883121 = 662341) B662341
theorem B4028849 : Blo 587289 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B588211 : Blo 587289 588211 := bstep (se 1 (by rfl) ⟨441158, by rfl⟩ : syracuseStep 588211 = 882317) B882317
theorem B588227 : Blo 587289 588227 := bstep (se 1 (by rfl) ⟨441170, by rfl⟩ : syracuseStep 588227 = 882341) B882341
theorem B883139 : Blo 587289 883139 := bstep (se 1 (by rfl) ⟨662354, by rfl⟩ : syracuseStep 883139 = 1324709) B1324709
theorem B3766733 : Blo 587289 3766733 := bstep (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) B1412525
theorem B588243 : Blo 587289 588243 := bstep (se 1 (by rfl) ⟨441182, by rfl⟩ : syracuseStep 588243 = 882365) B882365
theorem B883169 : Blo 587289 883169 := bstep (se 2 (by rfl) ⟨331188, by rfl⟩ : syracuseStep 883169 = 662377) B662377
theorem B588259 : Blo 587289 588259 := bstep (se 1 (by rfl) ⟨441194, by rfl⟩ : syracuseStep 588259 = 882389) B882389
theorem B588275 : Blo 587289 588275 := bstep (se 1 (by rfl) ⟨441206, by rfl⟩ : syracuseStep 588275 = 882413) B882413
theorem B883187 : Blo 587289 883187 := bstep (se 1 (by rfl) ⟨662390, by rfl⟩ : syracuseStep 883187 = 1324781) B1324781
theorem B588291 : Blo 587289 588291 := bstep (se 1 (by rfl) ⟨441218, by rfl⟩ : syracuseStep 588291 = 882437) B882437
theorem B883217 : Blo 587289 883217 := bstep (se 2 (by rfl) ⟨331206, by rfl⟩ : syracuseStep 883217 = 662413) B662413
theorem B588307 : Blo 587289 588307 := bstep (se 1 (by rfl) ⟨441230, by rfl⟩ : syracuseStep 588307 = 882461) B882461
theorem B588323 : Blo 587289 588323 := bstep (se 1 (by rfl) ⟨441242, by rfl⟩ : syracuseStep 588323 = 882485) B882485
theorem B883235 : Blo 587289 883235 := bstep (se 1 (by rfl) ⟨662426, by rfl⟩ : syracuseStep 883235 = 1324853) B1324853
theorem B1342001 : Blo 587289 1342001 := bstep (se 2 (by rfl) ⟨503250, by rfl⟩ : syracuseStep 1342001 = 1006501) B1006501
theorem B588339 : Blo 587289 588339 := bstep (se 1 (by rfl) ⟨441254, by rfl⟩ : syracuseStep 588339 = 882509) B882509
theorem B883265 : Blo 587289 883265 := bstep (se 2 (by rfl) ⟨331224, by rfl⟩ : syracuseStep 883265 = 662449) B662449
theorem B588355 : Blo 587289 588355 := bstep (se 1 (by rfl) ⟨441266, by rfl⟩ : syracuseStep 588355 = 882533) B882533
theorem B588371 : Blo 587289 588371 := bstep (se 1 (by rfl) ⟨441278, by rfl⟩ : syracuseStep 588371 = 882557) B882557
theorem B883283 : Blo 587289 883283 := bstep (se 1 (by rfl) ⟨662462, by rfl⟩ : syracuseStep 883283 = 1324925) B1324925
theorem B588387 : Blo 587289 588387 := bstep (se 1 (by rfl) ⟨441290, by rfl⟩ : syracuseStep 588387 = 882581) B882581
theorem B883313 : Blo 587289 883313 := bstep (se 2 (by rfl) ⟨331242, by rfl⟩ : syracuseStep 883313 = 662485) B662485
theorem B588403 : Blo 587289 588403 := bstep (se 1 (by rfl) ⟨441302, by rfl⟩ : syracuseStep 588403 = 882605) B882605
theorem B588419 : Blo 587289 588419 := bstep (se 1 (by rfl) ⟨441314, by rfl⟩ : syracuseStep 588419 = 882629) B882629
theorem B883331 : Blo 587289 883331 := bstep (se 1 (by rfl) ⟨662498, by rfl⟩ : syracuseStep 883331 = 1324997) B1324997
theorem B588435 : Blo 587289 588435 := bstep (se 1 (by rfl) ⟨441326, by rfl⟩ : syracuseStep 588435 = 882653) B882653
theorem B883361 : Blo 587289 883361 := bstep (se 2 (by rfl) ⟨331260, by rfl⟩ : syracuseStep 883361 = 662521) B662521
theorem B588451 : Blo 587289 588451 := bstep (se 1 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 588451 = 882677) B882677
theorem B588467 : Blo 587289 588467 := bstep (se 1 (by rfl) ⟨441350, by rfl⟩ : syracuseStep 588467 = 882701) B882701
theorem B883379 : Blo 587289 883379 := bstep (se 1 (by rfl) ⟨662534, by rfl⟩ : syracuseStep 883379 = 1325069) B1325069
theorem B588483 : Blo 587289 588483 := bstep (se 1 (by rfl) ⟨441362, by rfl⟩ : syracuseStep 588483 = 882725) B882725
theorem B883409 : Blo 587289 883409 := bstep (se 2 (by rfl) ⟨331278, by rfl⟩ : syracuseStep 883409 = 662557) B662557
theorem B588499 : Blo 587289 588499 := bstep (se 1 (by rfl) ⟨441374, by rfl⟩ : syracuseStep 588499 = 882749) B882749
theorem B588515 : Blo 587289 588515 := bstep (se 1 (by rfl) ⟨441386, by rfl⟩ : syracuseStep 588515 = 882773) B882773
theorem B883427 : Blo 587289 883427 := bstep (se 1 (by rfl) ⟨662570, by rfl⟩ : syracuseStep 883427 = 1325141) B1325141
theorem B7568113 : Blo 587289 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B588531 : Blo 587289 588531 := bstep (se 1 (by rfl) ⟨441398, by rfl⟩ : syracuseStep 588531 = 882797) B882797
theorem B883457 : Blo 587289 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B588547 : Blo 587289 588547 := bstep (se 1 (by rfl) ⟨441410, by rfl⟩ : syracuseStep 588547 = 882821) B882821
theorem B588563 : Blo 587289 588563 := bstep (se 1 (by rfl) ⟨441422, by rfl⟩ : syracuseStep 588563 = 882845) B882845
theorem B883475 : Blo 587289 883475 := bstep (se 1 (by rfl) ⟨662606, by rfl⟩ : syracuseStep 883475 = 1325213) B1325213
theorem B588579 : Blo 587289 588579 := bstep (se 1 (by rfl) ⟨441434, by rfl⟩ : syracuseStep 588579 = 882869) B882869
theorem B883505 : Blo 587289 883505 := bstep (se 2 (by rfl) ⟨331314, by rfl⟩ : syracuseStep 883505 = 662629) B662629
theorem B588595 : Blo 587289 588595 := bstep (se 1 (by rfl) ⟨441446, by rfl⟩ : syracuseStep 588595 = 882893) B882893
theorem B588611 : Blo 587289 588611 := bstep (se 1 (by rfl) ⟨441458, by rfl⟩ : syracuseStep 588611 = 882917) B882917
theorem B883523 : Blo 587289 883523 := bstep (se 1 (by rfl) ⟨662642, by rfl⟩ : syracuseStep 883523 = 1325285) B1325285
theorem B588627 : Blo 587289 588627 := bstep (se 1 (by rfl) ⟨441470, by rfl⟩ : syracuseStep 588627 = 882941) B882941
theorem B883553 : Blo 587289 883553 := bstep (se 2 (by rfl) ⟨331332, by rfl⟩ : syracuseStep 883553 = 662665) B662665
theorem B588643 : Blo 587289 588643 := bstep (se 1 (by rfl) ⟨441482, by rfl⟩ : syracuseStep 588643 = 882965) B882965
theorem B588659 : Blo 587289 588659 := bstep (se 1 (by rfl) ⟨441494, by rfl⟩ : syracuseStep 588659 = 882989) B882989
theorem B883571 : Blo 587289 883571 := bstep (se 1 (by rfl) ⟨662678, by rfl⟩ : syracuseStep 883571 = 1325357) B1325357
theorem B588675 : Blo 587289 588675 := bstep (se 1 (by rfl) ⟨441506, by rfl⟩ : syracuseStep 588675 = 883013) B883013
theorem B883601 : Blo 587289 883601 := bstep (se 2 (by rfl) ⟨331350, by rfl⟩ : syracuseStep 883601 = 662701) B662701
theorem B588691 : Blo 587289 588691 := bstep (se 1 (by rfl) ⟨441518, by rfl⟩ : syracuseStep 588691 = 883037) B883037
theorem B588707 : Blo 587289 588707 := bstep (se 1 (by rfl) ⟨441530, by rfl⟩ : syracuseStep 588707 = 883061) B883061
theorem B883619 : Blo 587289 883619 := bstep (se 1 (by rfl) ⟨662714, by rfl⟩ : syracuseStep 883619 = 1325429) B1325429
theorem B588723 : Blo 587289 588723 := bstep (se 1 (by rfl) ⟨441542, by rfl⟩ : syracuseStep 588723 = 883085) B883085
theorem B883649 : Blo 587289 883649 := bstep (se 2 (by rfl) ⟨331368, by rfl⟩ : syracuseStep 883649 = 662737) B662737
theorem B588739 : Blo 587289 588739 := bstep (se 1 (by rfl) ⟨441554, by rfl⟩ : syracuseStep 588739 = 883109) B883109
theorem B588755 : Blo 587289 588755 := bstep (se 1 (by rfl) ⟨441566, by rfl⟩ : syracuseStep 588755 = 883133) B883133
theorem B883667 : Blo 587289 883667 := bstep (se 1 (by rfl) ⟨662750, by rfl⟩ : syracuseStep 883667 = 1325501) B1325501
theorem B588771 : Blo 587289 588771 := bstep (se 1 (by rfl) ⟨441578, by rfl⟩ : syracuseStep 588771 = 883157) B883157
theorem B883697 : Blo 587289 883697 := bstep (se 2 (by rfl) ⟨331386, by rfl⟩ : syracuseStep 883697 = 662773) B662773
theorem B588787 : Blo 587289 588787 := bstep (se 1 (by rfl) ⟨441590, by rfl⟩ : syracuseStep 588787 = 883181) B883181
theorem B588803 : Blo 587289 588803 := bstep (se 1 (by rfl) ⟨441602, by rfl⟩ : syracuseStep 588803 = 883205) B883205
theorem B883715 : Blo 587289 883715 := bstep (se 1 (by rfl) ⟨662786, by rfl⟩ : syracuseStep 883715 = 1325573) B1325573
theorem B588819 : Blo 587289 588819 := bstep (se 1 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 588819 = 883229) B883229
theorem B883745 : Blo 587289 883745 := bstep (se 2 (by rfl) ⟨331404, by rfl⟩ : syracuseStep 883745 = 662809) B662809
theorem B588835 : Blo 587289 588835 := bstep (se 1 (by rfl) ⟨441626, by rfl⟩ : syracuseStep 588835 = 883253) B883253
theorem B588851 : Blo 587289 588851 := bstep (se 1 (by rfl) ⟨441638, by rfl⟩ : syracuseStep 588851 = 883277) B883277
theorem B883763 : Blo 587289 883763 := bstep (se 1 (by rfl) ⟨662822, by rfl⟩ : syracuseStep 883763 = 1325645) B1325645
theorem B588867 : Blo 587289 588867 := bstep (se 1 (by rfl) ⟨441650, by rfl⟩ : syracuseStep 588867 = 883301) B883301
theorem B883793 : Blo 587289 883793 := bstep (se 2 (by rfl) ⟨331422, by rfl⟩ : syracuseStep 883793 = 662845) B662845
theorem B588883 : Blo 587289 588883 := bstep (se 1 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 588883 = 883325) B883325
theorem B588899 : Blo 587289 588899 := bstep (se 1 (by rfl) ⟨441674, by rfl⟩ : syracuseStep 588899 = 883349) B883349
theorem B883811 : Blo 587289 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B719971 : Blo 587289 719971 := bstep (se 1 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 719971 = 1079957) B1079957
theorem B6061169 : Blo 587289 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B588915 : Blo 587289 588915 := bstep (se 1 (by rfl) ⟨441686, by rfl⟩ : syracuseStep 588915 = 883373) B883373
theorem B883841 : Blo 587289 883841 := bstep (se 2 (by rfl) ⟨331440, by rfl⟩ : syracuseStep 883841 = 662881) B662881
theorem B588931 : Blo 587289 588931 := bstep (se 1 (by rfl) ⟨441698, by rfl⟩ : syracuseStep 588931 = 883397) B883397
theorem B588947 : Blo 587289 588947 := bstep (se 1 (by rfl) ⟨441710, by rfl⟩ : syracuseStep 588947 = 883421) B883421
theorem B883859 : Blo 587289 883859 := bstep (se 1 (by rfl) ⟨662894, by rfl⟩ : syracuseStep 883859 = 1325789) B1325789
theorem B588963 : Blo 587289 588963 := bstep (se 1 (by rfl) ⟨441722, by rfl⟩ : syracuseStep 588963 = 883445) B883445
theorem B883889 : Blo 587289 883889 := bstep (se 2 (by rfl) ⟨331458, by rfl⟩ : syracuseStep 883889 = 662917) B662917
theorem B588979 : Blo 587289 588979 := bstep (se 1 (by rfl) ⟨441734, by rfl⟩ : syracuseStep 588979 = 883469) B883469
theorem B588995 : Blo 587289 588995 := bstep (se 1 (by rfl) ⟨441746, by rfl⟩ : syracuseStep 588995 = 883493) B883493
theorem B883907 : Blo 587289 883907 := bstep (se 1 (by rfl) ⟨662930, by rfl⟩ : syracuseStep 883907 = 1325861) B1325861
theorem B589011 : Blo 587289 589011 := bstep (se 1 (by rfl) ⟨441758, by rfl⟩ : syracuseStep 589011 = 883517) B883517
theorem B883937 : Blo 587289 883937 := bstep (se 2 (by rfl) ⟨331476, by rfl⟩ : syracuseStep 883937 = 662953) B662953
theorem B589027 : Blo 587289 589027 := bstep (se 1 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 589027 = 883541) B883541
theorem B589043 : Blo 587289 589043 := bstep (se 1 (by rfl) ⟨441782, by rfl⟩ : syracuseStep 589043 = 883565) B883565
theorem B883955 : Blo 587289 883955 := bstep (se 1 (by rfl) ⟨662966, by rfl⟩ : syracuseStep 883955 = 1325933) B1325933
theorem B589059 : Blo 587289 589059 := bstep (se 1 (by rfl) ⟨441794, by rfl⟩ : syracuseStep 589059 = 883589) B883589
theorem B883985 : Blo 587289 883985 := bstep (se 2 (by rfl) ⟨331494, by rfl⟩ : syracuseStep 883985 = 662989) B662989
theorem B589075 : Blo 587289 589075 := bstep (se 1 (by rfl) ⟨441806, by rfl⟩ : syracuseStep 589075 = 883613) B883613
theorem B589091 : Blo 587289 589091 := bstep (se 1 (by rfl) ⟨441818, by rfl⟩ : syracuseStep 589091 = 883637) B883637
theorem B884003 : Blo 587289 884003 := bstep (se 1 (by rfl) ⟨663002, by rfl⟩ : syracuseStep 884003 = 1326005) B1326005
theorem B589107 : Blo 587289 589107 := bstep (se 1 (by rfl) ⟨441830, by rfl⟩ : syracuseStep 589107 = 883661) B883661
theorem B884033 : Blo 587289 884033 := bstep (se 2 (by rfl) ⟨331512, by rfl⟩ : syracuseStep 884033 = 663025) B663025
theorem B589123 : Blo 587289 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B589139 : Blo 587289 589139 := bstep (se 1 (by rfl) ⟨441854, by rfl⟩ : syracuseStep 589139 = 883709) B883709
theorem B884051 : Blo 587289 884051 := bstep (se 1 (by rfl) ⟨663038, by rfl⟩ : syracuseStep 884051 = 1326077) B1326077
theorem B589155 : Blo 587289 589155 := bstep (se 1 (by rfl) ⟨441866, by rfl⟩ : syracuseStep 589155 = 883733) B883733
theorem B884081 : Blo 587289 884081 := bstep (se 2 (by rfl) ⟨331530, by rfl⟩ : syracuseStep 884081 = 663061) B663061
theorem B589171 : Blo 587289 589171 := bstep (se 1 (by rfl) ⟨441878, by rfl⟩ : syracuseStep 589171 = 883757) B883757
theorem B589187 : Blo 587289 589187 := bstep (se 1 (by rfl) ⟨441890, by rfl⟩ : syracuseStep 589187 = 883781) B883781
theorem B884099 : Blo 587289 884099 := bstep (se 1 (by rfl) ⟨663074, by rfl⟩ : syracuseStep 884099 = 1326149) B1326149
theorem B589203 : Blo 587289 589203 := bstep (se 1 (by rfl) ⟨441902, by rfl⟩ : syracuseStep 589203 = 883805) B883805
theorem B884129 : Blo 587289 884129 := bstep (se 2 (by rfl) ⟨331548, by rfl⟩ : syracuseStep 884129 = 663097) B663097
theorem B589219 : Blo 587289 589219 := bstep (se 1 (by rfl) ⟨441914, by rfl⟩ : syracuseStep 589219 = 883829) B883829
theorem B589235 : Blo 587289 589235 := bstep (se 1 (by rfl) ⟨441926, by rfl⟩ : syracuseStep 589235 = 883853) B883853
theorem B884147 : Blo 587289 884147 := bstep (se 1 (by rfl) ⟨663110, by rfl⟩ : syracuseStep 884147 = 1326221) B1326221
theorem B589251 : Blo 587289 589251 := bstep (se 1 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 589251 = 883877) B883877
theorem B884177 : Blo 587289 884177 := bstep (se 2 (by rfl) ⟨331566, by rfl⟩ : syracuseStep 884177 = 663133) B663133
theorem B589267 : Blo 587289 589267 := bstep (se 1 (by rfl) ⟨441950, by rfl⟩ : syracuseStep 589267 = 883901) B883901
theorem B589283 : Blo 587289 589283 := bstep (se 1 (by rfl) ⟨441962, by rfl⟩ : syracuseStep 589283 = 883925) B883925
theorem B884195 : Blo 587289 884195 := bstep (se 1 (by rfl) ⟨663146, by rfl⟩ : syracuseStep 884195 = 1326293) B1326293
theorem B589299 : Blo 587289 589299 := bstep (se 1 (by rfl) ⟨441974, by rfl⟩ : syracuseStep 589299 = 883949) B883949
theorem B884225 : Blo 587289 884225 := bstep (se 2 (by rfl) ⟨331584, by rfl⟩ : syracuseStep 884225 = 663169) B663169
theorem B589315 : Blo 587289 589315 := bstep (se 1 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 589315 = 883973) B883973
theorem B589331 : Blo 587289 589331 := bstep (se 1 (by rfl) ⟨441998, by rfl⟩ : syracuseStep 589331 = 883997) B883997
theorem B884243 : Blo 587289 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B589347 : Blo 587289 589347 := bstep (se 1 (by rfl) ⟨442010, by rfl⟩ : syracuseStep 589347 = 884021) B884021
theorem B884273 : Blo 587289 884273 := bstep (se 2 (by rfl) ⟨331602, by rfl⟩ : syracuseStep 884273 = 663205) B663205
theorem B2391601 : Blo 587289 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B589363 : Blo 587289 589363 := bstep (se 1 (by rfl) ⟨442022, by rfl⟩ : syracuseStep 589363 = 884045) B884045
theorem B589379 : Blo 587289 589379 := bstep (se 1 (by rfl) ⟨442034, by rfl⟩ : syracuseStep 589379 = 884069) B884069
theorem B884291 : Blo 587289 884291 := bstep (se 1 (by rfl) ⟨663218, by rfl⟩ : syracuseStep 884291 = 1326437) B1326437
theorem B589395 : Blo 587289 589395 := bstep (se 1 (by rfl) ⟨442046, by rfl⟩ : syracuseStep 589395 = 884093) B884093
theorem B884321 : Blo 587289 884321 := bstep (se 2 (by rfl) ⟨331620, by rfl⟩ : syracuseStep 884321 = 663241) B663241
theorem B589411 : Blo 587289 589411 := bstep (se 1 (by rfl) ⟨442058, by rfl⟩ : syracuseStep 589411 = 884117) B884117
theorem B589427 : Blo 587289 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B884339 : Blo 587289 884339 := bstep (se 1 (by rfl) ⟨663254, by rfl⟩ : syracuseStep 884339 = 1326509) B1326509
theorem B589443 : Blo 587289 589443 := bstep (se 1 (by rfl) ⟨442082, by rfl⟩ : syracuseStep 589443 = 884165) B884165
theorem B884369 : Blo 587289 884369 := bstep (se 2 (by rfl) ⟨331638, by rfl⟩ : syracuseStep 884369 = 663277) B663277
theorem B589459 : Blo 587289 589459 := bstep (se 1 (by rfl) ⟨442094, by rfl⟩ : syracuseStep 589459 = 884189) B884189
theorem B884387 : Blo 587289 884387 := bstep (se 1 (by rfl) ⟨663290, by rfl⟩ : syracuseStep 884387 = 1326581) B1326581
theorem B589475 : Blo 587289 589475 := bstep (se 1 (by rfl) ⟨442106, by rfl⟩ : syracuseStep 589475 = 884213) B884213
theorem B589491 : Blo 587289 589491 := bstep (se 1 (by rfl) ⟨442118, by rfl⟩ : syracuseStep 589491 = 884237) B884237
theorem B884417 : Blo 587289 884417 := bstep (se 2 (by rfl) ⟨331656, by rfl⟩ : syracuseStep 884417 = 663313) B663313
theorem B589507 : Blo 587289 589507 := bstep (se 1 (by rfl) ⟨442130, by rfl⟩ : syracuseStep 589507 = 884261) B884261
theorem B589523 : Blo 587289 589523 := bstep (se 1 (by rfl) ⟨442142, by rfl⟩ : syracuseStep 589523 = 884285) B884285
theorem B884435 : Blo 587289 884435 := bstep (se 1 (by rfl) ⟨663326, by rfl⟩ : syracuseStep 884435 = 1326653) B1326653
theorem B589539 : Blo 587289 589539 := bstep (se 1 (by rfl) ⟨442154, by rfl⟩ : syracuseStep 589539 = 884309) B884309
theorem B884465 : Blo 587289 884465 := bstep (se 2 (by rfl) ⟨331674, by rfl⟩ : syracuseStep 884465 = 663349) B663349
theorem B589555 : Blo 587289 589555 := bstep (se 1 (by rfl) ⟨442166, by rfl⟩ : syracuseStep 589555 = 884333) B884333
theorem B589571 : Blo 587289 589571 := bstep (se 1 (by rfl) ⟨442178, by rfl⟩ : syracuseStep 589571 = 884357) B884357
theorem B884483 : Blo 587289 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B589587 : Blo 587289 589587 := bstep (se 1 (by rfl) ⟨442190, by rfl⟩ : syracuseStep 589587 = 884381) B884381
theorem B884513 : Blo 587289 884513 := bstep (se 2 (by rfl) ⟨331692, by rfl⟩ : syracuseStep 884513 = 663385) B663385
theorem B589603 : Blo 587289 589603 := bstep (se 1 (by rfl) ⟨442202, by rfl⟩ : syracuseStep 589603 = 884405) B884405
theorem B589619 : Blo 587289 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B884531 : Blo 587289 884531 := bstep (se 1 (by rfl) ⟨663398, by rfl⟩ : syracuseStep 884531 = 1326797) B1326797
theorem B589635 : Blo 587289 589635 := bstep (se 1 (by rfl) ⟨442226, by rfl⟩ : syracuseStep 589635 = 884453) B884453
theorem B884561 : Blo 587289 884561 := bstep (se 2 (by rfl) ⟨331710, by rfl⟩ : syracuseStep 884561 = 663421) B663421
theorem B589651 : Blo 587289 589651 := bstep (se 1 (by rfl) ⟨442238, by rfl⟩ : syracuseStep 589651 = 884477) B884477
theorem B589667 : Blo 587289 589667 := bstep (se 1 (by rfl) ⟨442250, by rfl⟩ : syracuseStep 589667 = 884501) B884501
theorem B884579 : Blo 587289 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B5373809 : Blo 587289 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B589683 : Blo 587289 589683 := bstep (se 1 (by rfl) ⟨442262, by rfl⟩ : syracuseStep 589683 = 884525) B884525
theorem B884609 : Blo 587289 884609 := bstep (se 2 (by rfl) ⟨331728, by rfl⟩ : syracuseStep 884609 = 663457) B663457
theorem B589699 : Blo 587289 589699 := bstep (se 1 (by rfl) ⟨442274, by rfl⟩ : syracuseStep 589699 = 884549) B884549
theorem B589715 : Blo 587289 589715 := bstep (se 1 (by rfl) ⟨442286, by rfl⟩ : syracuseStep 589715 = 884573) B884573
theorem B884627 : Blo 587289 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B589731 : Blo 587289 589731 := bstep (se 1 (by rfl) ⟨442298, by rfl⟩ : syracuseStep 589731 = 884597) B884597
theorem B884657 : Blo 587289 884657 := bstep (se 2 (by rfl) ⟨331746, by rfl⟩ : syracuseStep 884657 = 663493) B663493
theorem B589747 : Blo 587289 589747 := bstep (se 1 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 589747 = 884621) B884621
theorem B589763 : Blo 587289 589763 := bstep (se 1 (by rfl) ⟨442322, by rfl⟩ : syracuseStep 589763 = 884645) B884645
theorem B884675 : Blo 587289 884675 := bstep (se 1 (by rfl) ⟨663506, by rfl⟩ : syracuseStep 884675 = 1327013) B1327013
theorem B589779 : Blo 587289 589779 := bstep (se 1 (by rfl) ⟨442334, by rfl⟩ : syracuseStep 589779 = 884669) B884669
theorem B884705 : Blo 587289 884705 := bstep (se 2 (by rfl) ⟨331764, by rfl⟩ : syracuseStep 884705 = 663529) B663529
theorem B1343459 : Blo 587289 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B589795 : Blo 587289 589795 := bstep (se 1 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 589795 = 884693) B884693
theorem B589811 : Blo 587289 589811 := bstep (se 1 (by rfl) ⟨442358, by rfl⟩ : syracuseStep 589811 = 884717) B884717
theorem B884723 : Blo 587289 884723 := bstep (se 1 (by rfl) ⟨663542, by rfl⟩ : syracuseStep 884723 = 1327085) B1327085
theorem B884747 : Blo 587289 884747 := bstep (se 1 (by rfl) ⟨663560, by rfl⟩ : syracuseStep 884747 = 1327121) B1327121
theorem B589835 : Blo 587289 589835 := bstep (se 1 (by rfl) ⟨442376, by rfl⟩ : syracuseStep 589835 = 884753) B884753
theorem B884759 : Blo 587289 884759 := bstep (se 1 (by rfl) ⟨663569, by rfl⟩ : syracuseStep 884759 = 1327139) B1327139
theorem B589847 : Blo 587289 589847 := bstep (se 1 (by rfl) ⟨442385, by rfl⟩ : syracuseStep 589847 = 884771) B884771
theorem B589867 : Blo 587289 589867 := bstep (se 1 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 589867 = 884801) B884801
theorem B2981933 : Blo 587289 2981933 := bstep (se 3 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 2981933 = 1118225) B1118225
theorem B589879 : Blo 587289 589879 := bstep (se 1 (by rfl) ⟨442409, by rfl⟩ : syracuseStep 589879 = 884819) B884819
theorem B589899 : Blo 587289 589899 := bstep (se 1 (by rfl) ⟨442424, by rfl⟩ : syracuseStep 589899 = 884849) B884849
theorem B589911 : Blo 587289 589911 := bstep (se 1 (by rfl) ⟨442433, by rfl⟩ : syracuseStep 589911 = 884867) B884867
theorem B884825 : Blo 587289 884825 := bstep (se 2 (by rfl) ⟨331809, by rfl⟩ : syracuseStep 884825 = 663619) B663619
theorem B589931 : Blo 587289 589931 := bstep (se 1 (by rfl) ⟨442448, by rfl⟩ : syracuseStep 589931 = 884897) B884897
theorem B589943 : Blo 587289 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B589963 : Blo 587289 589963 := bstep (se 1 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 589963 = 884945) B884945
theorem B589975 : Blo 587289 589975 := bstep (se 1 (by rfl) ⟨442481, by rfl⟩ : syracuseStep 589975 = 884963) B884963
theorem B589995 : Blo 587289 589995 := bstep (se 1 (by rfl) ⟨442496, by rfl⟩ : syracuseStep 589995 = 884993) B884993
theorem B590007 : Blo 587289 590007 := bstep (se 1 (by rfl) ⟨442505, by rfl⟩ : syracuseStep 590007 = 885011) B885011
theorem B884939 : Blo 587289 884939 := bstep (se 1 (by rfl) ⟨663704, by rfl⟩ : syracuseStep 884939 = 1327409) B1327409
theorem B590027 : Blo 587289 590027 := bstep (se 1 (by rfl) ⟨442520, by rfl⟩ : syracuseStep 590027 = 885041) B885041
theorem B884951 : Blo 587289 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B590039 : Blo 587289 590039 := bstep (se 1 (by rfl) ⟨442529, by rfl⟩ : syracuseStep 590039 = 885059) B885059
theorem B590059 : Blo 587289 590059 := bstep (se 1 (by rfl) ⟨442544, by rfl⟩ : syracuseStep 590059 = 885089) B885089
theorem B590071 : Blo 587289 590071 := bstep (se 1 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 590071 = 885107) B885107
theorem B590091 : Blo 587289 590091 := bstep (se 1 (by rfl) ⟨442568, by rfl⟩ : syracuseStep 590091 = 885137) B885137
theorem B590103 : Blo 587289 590103 := bstep (se 1 (by rfl) ⟨442577, by rfl⟩ : syracuseStep 590103 = 885155) B885155
theorem B885017 : Blo 587289 885017 := bstep (se 2 (by rfl) ⟨331881, by rfl⟩ : syracuseStep 885017 = 663763) B663763
theorem B590123 : Blo 587289 590123 := bstep (se 1 (by rfl) ⟨442592, by rfl⟩ : syracuseStep 590123 = 885185) B885185
theorem B590135 : Blo 587289 590135 := bstep (se 1 (by rfl) ⟨442601, by rfl⟩ : syracuseStep 590135 = 885203) B885203
theorem B590155 : Blo 587289 590155 := bstep (se 1 (by rfl) ⟨442616, by rfl⟩ : syracuseStep 590155 = 885233) B885233
theorem B590167 : Blo 587289 590167 := bstep (se 1 (by rfl) ⟨442625, by rfl⟩ : syracuseStep 590167 = 885251) B885251
theorem B590187 : Blo 587289 590187 := bstep (se 1 (by rfl) ⟨442640, by rfl⟩ : syracuseStep 590187 = 885281) B885281
theorem B17170805 : Blo 587289 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B590199 : Blo 587289 590199 := bstep (se 1 (by rfl) ⟨442649, by rfl⟩ : syracuseStep 590199 = 885299) B885299
theorem B885131 : Blo 587289 885131 := bstep (se 1 (by rfl) ⟨663848, by rfl⟩ : syracuseStep 885131 = 1327697) B1327697
theorem B590219 : Blo 587289 590219 := bstep (se 1 (by rfl) ⟨442664, by rfl⟩ : syracuseStep 590219 = 885329) B885329
theorem B885143 : Blo 587289 885143 := bstep (se 1 (by rfl) ⟨663857, by rfl⟩ : syracuseStep 885143 = 1327715) B1327715
theorem B590231 : Blo 587289 590231 := bstep (se 1 (by rfl) ⟨442673, by rfl⟩ : syracuseStep 590231 = 885347) B885347
theorem B590251 : Blo 587289 590251 := bstep (se 1 (by rfl) ⟨442688, by rfl⟩ : syracuseStep 590251 = 885377) B885377
theorem B590263 : Blo 587289 590263 := bstep (se 1 (by rfl) ⟨442697, by rfl⟩ : syracuseStep 590263 = 885395) B885395
theorem B590283 : Blo 587289 590283 := bstep (se 1 (by rfl) ⟨442712, by rfl⟩ : syracuseStep 590283 = 885425) B885425
theorem B590295 : Blo 587289 590295 := bstep (se 1 (by rfl) ⟨442721, by rfl⟩ : syracuseStep 590295 = 885443) B885443
theorem B885209 : Blo 587289 885209 := bstep (se 2 (by rfl) ⟨331953, by rfl⟩ : syracuseStep 885209 = 663907) B663907
theorem B590315 : Blo 587289 590315 := bstep (se 1 (by rfl) ⟨442736, by rfl⟩ : syracuseStep 590315 = 885473) B885473
theorem B590327 : Blo 587289 590327 := bstep (se 1 (by rfl) ⟨442745, by rfl⟩ : syracuseStep 590327 = 885491) B885491
theorem B590347 : Blo 587289 590347 := bstep (se 1 (by rfl) ⟨442760, by rfl⟩ : syracuseStep 590347 = 885521) B885521
theorem B590359 : Blo 587289 590359 := bstep (se 1 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 590359 = 885539) B885539
theorem B590379 : Blo 587289 590379 := bstep (se 1 (by rfl) ⟨442784, by rfl⟩ : syracuseStep 590379 = 885569) B885569
theorem B590391 : Blo 587289 590391 := bstep (se 1 (by rfl) ⟨442793, by rfl⟩ : syracuseStep 590391 = 885587) B885587
theorem B885323 : Blo 587289 885323 := bstep (se 1 (by rfl) ⟨663992, by rfl⟩ : syracuseStep 885323 = 1327985) B1327985
theorem B590411 : Blo 587289 590411 := bstep (se 1 (by rfl) ⟨442808, by rfl⟩ : syracuseStep 590411 = 885617) B885617
theorem B885335 : Blo 587289 885335 := bstep (se 1 (by rfl) ⟨664001, by rfl⟩ : syracuseStep 885335 = 1328003) B1328003
theorem B590423 : Blo 587289 590423 := bstep (se 1 (by rfl) ⟨442817, by rfl⟩ : syracuseStep 590423 = 885635) B885635
theorem B590443 : Blo 587289 590443 := bstep (se 1 (by rfl) ⟨442832, by rfl⟩ : syracuseStep 590443 = 885665) B885665
theorem B590455 : Blo 587289 590455 := bstep (se 1 (by rfl) ⟨442841, by rfl⟩ : syracuseStep 590455 = 885683) B885683
theorem B590475 : Blo 587289 590475 := bstep (se 1 (by rfl) ⟨442856, by rfl⟩ : syracuseStep 590475 = 885713) B885713
theorem B4784791 : Blo 587289 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B590487 : Blo 587289 590487 := bstep (se 1 (by rfl) ⟨442865, by rfl⟩ : syracuseStep 590487 = 885731) B885731
theorem B885401 : Blo 587289 885401 := bstep (se 2 (by rfl) ⟨332025, by rfl⟩ : syracuseStep 885401 = 664051) B664051
theorem B590507 : Blo 587289 590507 := bstep (se 1 (by rfl) ⟨442880, by rfl⟩ : syracuseStep 590507 = 885761) B885761
theorem B590519 : Blo 587289 590519 := bstep (se 1 (by rfl) ⟨442889, by rfl⟩ : syracuseStep 590519 = 885779) B885779
theorem B590539 : Blo 587289 590539 := bstep (se 1 (by rfl) ⟨442904, by rfl⟩ : syracuseStep 590539 = 885809) B885809
theorem B590551 : Blo 587289 590551 := bstep (se 1 (by rfl) ⟨442913, by rfl⟩ : syracuseStep 590551 = 885827) B885827
theorem B590571 : Blo 587289 590571 := bstep (se 1 (by rfl) ⟨442928, by rfl⟩ : syracuseStep 590571 = 885857) B885857
theorem B590583 : Blo 587289 590583 := bstep (se 1 (by rfl) ⟨442937, by rfl⟩ : syracuseStep 590583 = 885875) B885875
theorem B885515 : Blo 587289 885515 := bstep (se 1 (by rfl) ⟨664136, by rfl⟩ : syracuseStep 885515 = 1328273) B1328273
theorem B590603 : Blo 587289 590603 := bstep (se 1 (by rfl) ⟨442952, by rfl⟩ : syracuseStep 590603 = 885905) B885905
theorem B885527 : Blo 587289 885527 := bstep (se 1 (by rfl) ⟨664145, by rfl⟩ : syracuseStep 885527 = 1328291) B1328291
theorem B590615 : Blo 587289 590615 := bstep (se 1 (by rfl) ⟨442961, by rfl⟩ : syracuseStep 590615 = 885923) B885923
theorem B590635 : Blo 587289 590635 := bstep (se 1 (by rfl) ⟨442976, by rfl⟩ : syracuseStep 590635 = 885953) B885953
theorem B590647 : Blo 587289 590647 := bstep (se 1 (by rfl) ⟨442985, by rfl⟩ : syracuseStep 590647 = 885971) B885971
theorem B590667 : Blo 587289 590667 := bstep (se 1 (by rfl) ⟨443000, by rfl⟩ : syracuseStep 590667 = 886001) B886001
theorem B885593 : Blo 587289 885593 := bstep (se 2 (by rfl) ⟨332097, by rfl⟩ : syracuseStep 885593 = 664195) B664195
theorem B590679 : Blo 587289 590679 := bstep (se 1 (by rfl) ⟨443009, by rfl⟩ : syracuseStep 590679 = 886019) B886019
theorem B590699 : Blo 587289 590699 := bstep (se 1 (by rfl) ⟨443024, by rfl⟩ : syracuseStep 590699 = 886049) B886049
theorem B590711 : Blo 587289 590711 := bstep (se 1 (by rfl) ⟨443033, by rfl⟩ : syracuseStep 590711 = 886067) B886067
theorem B590731 : Blo 587289 590731 := bstep (se 1 (by rfl) ⟨443048, by rfl⟩ : syracuseStep 590731 = 886097) B886097
theorem B590743 : Blo 587289 590743 := bstep (se 1 (by rfl) ⟨443057, by rfl⟩ : syracuseStep 590743 = 886115) B886115
theorem B590763 : Blo 587289 590763 := bstep (se 1 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 590763 = 886145) B886145
theorem B1115059 : Blo 587289 1115059 := bstep (se 1 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 1115059 = 1672589) B1672589
theorem B590775 : Blo 587289 590775 := bstep (se 1 (by rfl) ⟨443081, by rfl⟩ : syracuseStep 590775 = 886163) B886163
theorem B885707 : Blo 587289 885707 := bstep (se 1 (by rfl) ⟨664280, by rfl⟩ : syracuseStep 885707 = 1328561) B1328561
theorem B590795 : Blo 587289 590795 := bstep (se 1 (by rfl) ⟨443096, by rfl⟩ : syracuseStep 590795 = 886193) B886193
theorem B885719 : Blo 587289 885719 := bstep (se 1 (by rfl) ⟨664289, by rfl⟩ : syracuseStep 885719 = 1328579) B1328579
theorem B590807 : Blo 587289 590807 := bstep (se 1 (by rfl) ⟨443105, by rfl⟩ : syracuseStep 590807 = 886211) B886211
theorem B590827 : Blo 587289 590827 := bstep (se 1 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 590827 = 886241) B886241
theorem B590839 : Blo 587289 590839 := bstep (se 1 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 590839 = 886259) B886259
theorem B590859 : Blo 587289 590859 := bstep (se 1 (by rfl) ⟨443144, by rfl⟩ : syracuseStep 590859 = 886289) B886289
theorem B590871 : Blo 587289 590871 := bstep (se 1 (by rfl) ⟨443153, by rfl⟩ : syracuseStep 590871 = 886307) B886307
theorem B885785 : Blo 587289 885785 := bstep (se 2 (by rfl) ⟨332169, by rfl⟩ : syracuseStep 885785 = 664339) B664339
theorem B590891 : Blo 587289 590891 := bstep (se 1 (by rfl) ⟨443168, by rfl⟩ : syracuseStep 590891 = 886337) B886337
theorem B590903 : Blo 587289 590903 := bstep (se 1 (by rfl) ⟨443177, by rfl⟩ : syracuseStep 590903 = 886355) B886355
theorem B590923 : Blo 587289 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B590935 : Blo 587289 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B590955 : Blo 587289 590955 := bstep (se 1 (by rfl) ⟨443216, by rfl⟩ : syracuseStep 590955 = 886433) B886433
theorem B590967 : Blo 587289 590967 := bstep (se 1 (by rfl) ⟨443225, by rfl⟩ : syracuseStep 590967 = 886451) B886451
theorem B885899 : Blo 587289 885899 := bstep (se 1 (by rfl) ⟨664424, by rfl⟩ : syracuseStep 885899 = 1328849) B1328849
theorem B590987 : Blo 587289 590987 := bstep (se 1 (by rfl) ⟨443240, by rfl⟩ : syracuseStep 590987 = 886481) B886481
theorem B2262161 : Blo 587289 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B885911 : Blo 587289 885911 := bstep (se 1 (by rfl) ⟨664433, by rfl⟩ : syracuseStep 885911 = 1328867) B1328867
theorem B590999 : Blo 587289 590999 := bstep (se 1 (by rfl) ⟨443249, by rfl⟩ : syracuseStep 590999 = 886499) B886499
theorem B591019 : Blo 587289 591019 := bstep (se 1 (by rfl) ⟨443264, by rfl⟩ : syracuseStep 591019 = 886529) B886529
theorem B591031 : Blo 587289 591031 := bstep (se 1 (by rfl) ⟨443273, by rfl⟩ : syracuseStep 591031 = 886547) B886547
theorem B591051 : Blo 587289 591051 := bstep (se 1 (by rfl) ⟨443288, by rfl⟩ : syracuseStep 591051 = 886577) B886577
theorem B591063 : Blo 587289 591063 := bstep (se 1 (by rfl) ⟨443297, by rfl⟩ : syracuseStep 591063 = 886595) B886595
theorem B885977 : Blo 587289 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B591083 : Blo 587289 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B591095 : Blo 587289 591095 := bstep (se 1 (by rfl) ⟨443321, by rfl⟩ : syracuseStep 591095 = 886643) B886643
theorem B591115 : Blo 587289 591115 := bstep (se 1 (by rfl) ⟨443336, by rfl⟩ : syracuseStep 591115 = 886673) B886673
theorem B591127 : Blo 587289 591127 := bstep (se 1 (by rfl) ⟨443345, by rfl⟩ : syracuseStep 591127 = 886691) B886691
theorem B591147 : Blo 587289 591147 := bstep (se 1 (by rfl) ⟨443360, by rfl⟩ : syracuseStep 591147 = 886721) B886721
theorem B591159 : Blo 587289 591159 := bstep (se 1 (by rfl) ⟨443369, by rfl⟩ : syracuseStep 591159 = 886739) B886739
theorem B5375297 : Blo 587289 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B886091 : Blo 587289 886091 := bstep (se 1 (by rfl) ⟨664568, by rfl⟩ : syracuseStep 886091 = 1329137) B1329137
theorem B591179 : Blo 587289 591179 := bstep (se 1 (by rfl) ⟨443384, by rfl⟩ : syracuseStep 591179 = 886769) B886769
theorem B886103 : Blo 587289 886103 := bstep (se 1 (by rfl) ⟨664577, by rfl⟩ : syracuseStep 886103 = 1329155) B1329155
theorem B591191 : Blo 587289 591191 := bstep (se 1 (by rfl) ⟨443393, by rfl⟩ : syracuseStep 591191 = 886787) B886787
theorem B591211 : Blo 587289 591211 := bstep (se 1 (by rfl) ⟨443408, by rfl⟩ : syracuseStep 591211 = 886817) B886817
theorem B1115507 : Blo 587289 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B591223 : Blo 587289 591223 := bstep (se 1 (by rfl) ⟨443417, by rfl⟩ : syracuseStep 591223 = 886835) B886835
theorem B591243 : Blo 587289 591243 := bstep (se 1 (by rfl) ⟨443432, by rfl⟩ : syracuseStep 591243 = 886865) B886865
theorem B591255 : Blo 587289 591255 := bstep (se 1 (by rfl) ⟨443441, by rfl⟩ : syracuseStep 591255 = 886883) B886883
theorem B1115545 : Blo 587289 1115545 := bstep (se 2 (by rfl) ⟨418329, by rfl⟩ : syracuseStep 1115545 = 836659) B836659
theorem B1213849 : Blo 587289 1213849 := bstep (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) B910387
theorem B886169 : Blo 587289 886169 := bstep (se 2 (by rfl) ⟨332313, by rfl⟩ : syracuseStep 886169 = 664627) B664627
theorem B591275 : Blo 587289 591275 := bstep (se 1 (by rfl) ⟨443456, by rfl⟩ : syracuseStep 591275 = 886913) B886913
theorem B5670323 : Blo 587289 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B591287 : Blo 587289 591287 := bstep (se 1 (by rfl) ⟨443465, by rfl⟩ : syracuseStep 591287 = 886931) B886931
theorem B2393561 : Blo 587289 2393561 := bstep (se 2 (by rfl) ⟨897585, by rfl⟩ : syracuseStep 2393561 = 1795171) B1795171
theorem B886283 : Blo 587289 886283 := bstep (se 1 (by rfl) ⟨664712, by rfl⟩ : syracuseStep 886283 = 1329425) B1329425
theorem B886295 : Blo 587289 886295 := bstep (se 1 (by rfl) ⟨664721, by rfl⟩ : syracuseStep 886295 = 1329443) B1329443
theorem B886361 : Blo 587289 886361 := bstep (se 2 (by rfl) ⟨332385, by rfl⟩ : syracuseStep 886361 = 664771) B664771
theorem B40699523 : Blo 587289 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B4523651 : Blo 587289 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B886475 : Blo 587289 886475 := bstep (se 1 (by rfl) ⟨664856, by rfl⟩ : syracuseStep 886475 = 1329713) B1329713
theorem B886487 : Blo 587289 886487 := bstep (se 1 (by rfl) ⟨664865, by rfl⟩ : syracuseStep 886487 = 1329731) B1329731
theorem B886553 : Blo 587289 886553 := bstep (se 2 (by rfl) ⟨332457, by rfl⟩ : syracuseStep 886553 = 664915) B664915
theorem B1115993 : Blo 587289 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B886667 : Blo 587289 886667 := bstep (se 1 (by rfl) ⟨665000, by rfl⟩ : syracuseStep 886667 = 1330001) B1330001
theorem B886679 : Blo 587289 886679 := bstep (se 1 (by rfl) ⟨665009, by rfl⟩ : syracuseStep 886679 = 1330019) B1330019
theorem B886745 : Blo 587289 886745 := bstep (se 2 (by rfl) ⟨332529, by rfl⟩ : syracuseStep 886745 = 665059) B665059
theorem B2525201 : Blo 587289 2525201 := bstep (se 2 (by rfl) ⟨946950, by rfl⟩ : syracuseStep 2525201 = 1893901) B1893901
theorem B886859 : Blo 587289 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B886871 : Blo 587289 886871 := bstep (se 1 (by rfl) ⟨665153, by rfl⟩ : syracuseStep 886871 = 1330307) B1330307
theorem B2230361 : Blo 587289 2230361 := bstep (se 2 (by rfl) ⟨836385, by rfl⟩ : syracuseStep 2230361 = 1672771) B1672771
theorem B2263427 : Blo 587289 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B2230679 : Blo 587289 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B6719921 : Blo 587289 6719921 := bstep (se 2 (by rfl) ⟨2519970, by rfl⟩ : syracuseStep 6719921 = 5039941) B5039941
theorem B1673693 : Blo 587289 1673693 := bstep (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) B627635
theorem B1116737 : Blo 587289 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B5048963 : Blo 587289 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B1673921 : Blo 587289 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B1346327 : Blo 587289 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1117003 : Blo 587289 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B3345245 : Blo 587289 3345245 := bstep (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) B1254467
theorem B5671781 : Blo 587289 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B1674263 : Blo 587289 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B2231347 : Blo 587289 2231347 := bstep (se 1 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 2231347 = 3347021) B3347021
theorem B1117451 : Blo 587289 1117451 := bstep (se 1 (by rfl) ⟨838088, by rfl⟩ : syracuseStep 1117451 = 1676177) B1676177
theorem B1117633 : Blo 587289 1117633 := bstep (se 2 (by rfl) ⟨419112, by rfl⟩ : syracuseStep 1117633 = 838225) B838225
theorem B2264537 : Blo 587289 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B2723507 : Blo 587289 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B1347329 : Blo 587289 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B1117975 : Blo 587289 1117975 := bstep (se 1 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 1117975 = 1676963) B1676963
theorem B1412939 : Blo 587289 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B2985821 : Blo 587289 2985821 := bstep (se 3 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 2985821 = 1119683) B1119683
theorem B1118195 : Blo 587289 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B1118423 : Blo 587289 1118423 := bstep (se 1 (by rfl) ⟨838817, by rfl⟩ : syracuseStep 1118423 = 1677635) B1677635
theorem B2232593 : Blo 587289 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B1118681 : Blo 587289 1118681 := bstep (se 2 (by rfl) ⟨419505, by rfl⟩ : syracuseStep 1118681 = 839011) B839011
theorem B2396675 : Blo 587289 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B8622773 : Blo 587289 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B6361901 : Blo 587289 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B3183461 : Blo 587289 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B1119091 : Blo 587289 1119091 := bstep (se 1 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 1119091 = 1678637) B1678637
theorem B2233291 : Blo 587289 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B1610903 : Blo 587289 1610903 := bstep (se 1 (by rfl) ⟨1208177, by rfl⟩ : syracuseStep 1610903 = 2416355) B2416355
theorem B2233565 : Blo 587289 2233565 := bstep (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) B837587
theorem B3347729 : Blo 587289 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B1676609 : Blo 587289 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B660811 : Blo 587289 660811 := bstep (se 1 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 660811 = 991217) B991217
theorem B1119577 : Blo 587289 1119577 := bstep (se 2 (by rfl) ⟨419841, by rfl⟩ : syracuseStep 1119577 = 839683) B839683
theorem B660919 : Blo 587289 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B48534997 : Blo 587289 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B7542233 : Blo 587289 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B661099 : Blo 587289 661099 := bstep (se 1 (by rfl) ⟨495824, by rfl⟩ : syracuseStep 661099 = 991649) B991649
theorem B661207 : Blo 587289 661207 := bstep (se 1 (by rfl) ⟨495905, by rfl⟩ : syracuseStep 661207 = 991811) B991811
theorem B1677145 : Blo 587289 1677145 := bstep (se 2 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 1677145 = 1257859) B1257859
theorem B3839845 : Blo 587289 3839845 := bstep (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) B719971
theorem B661387 : Blo 587289 661387 := bstep (se 1 (by rfl) ⟨496040, by rfl⟩ : syracuseStep 661387 = 992081) B992081
theorem B1120139 : Blo 587289 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B2234263 : Blo 587289 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B2987927 : Blo 587289 2987927 := bstep (se 1 (by rfl) ⟨2240945, by rfl⟩ : syracuseStep 2987927 = 4481891) B4481891
theorem B661495 : Blo 587289 661495 := bstep (se 1 (by rfl) ⟨496121, by rfl⟩ : syracuseStep 661495 = 992243) B992243
theorem B628759 : Blo 587289 628759 := bstep (se 1 (by rfl) ⟨471569, by rfl⟩ : syracuseStep 628759 = 943139) B943139
theorem B1120321 : Blo 587289 1120321 := bstep (se 2 (by rfl) ⟨420120, by rfl⟩ : syracuseStep 1120321 = 840241) B840241
theorem B661675 : Blo 587289 661675 := bstep (se 1 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 661675 = 992513) B992513
theorem B2726081 : Blo 587289 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B661783 : Blo 587289 661783 := bstep (se 1 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 661783 = 992675) B992675
theorem B5020055 : Blo 587289 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B2267585 : Blo 587289 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B661963 : Blo 587289 661963 := bstep (se 1 (by rfl) ⟨496472, by rfl⟩ : syracuseStep 661963 = 992945) B992945
theorem B662071 : Blo 587289 662071 := bstep (se 1 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 662071 = 993107) B993107
theorem B2235053 : Blo 587289 2235053 := bstep (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) B838145
theorem B662251 : Blo 587289 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B1121035 : Blo 587289 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B629579 : Blo 587289 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B662359 : Blo 587289 662359 := bstep (se 1 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 662359 = 993539) B993539
theorem B1121111 : Blo 587289 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B596939 : Blo 587289 596939 := bstep (se 1 (by rfl) ⟨447704, by rfl⟩ : syracuseStep 596939 = 895409) B895409
theorem B662539 : Blo 587289 662539 := bstep (se 1 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 662539 = 993809) B993809
theorem B662647 : Blo 587289 662647 := bstep (se 1 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 662647 = 993971) B993971
theorem B7183511 : Blo 587289 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B662827 : Blo 587289 662827 := bstep (se 1 (by rfl) ⟨497120, by rfl⟩ : syracuseStep 662827 = 994241) B994241
theorem B1416523 : Blo 587289 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B662935 : Blo 587289 662935 := bstep (se 1 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 662935 = 994403) B994403
theorem B1121779 : Blo 587289 1121779 := bstep (se 1 (by rfl) ⟨841334, by rfl⟩ : syracuseStep 1121779 = 1682669) B1682669
theorem B4496941 : Blo 587289 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B663115 : Blo 587289 663115 := bstep (se 1 (by rfl) ⟨497336, by rfl⟩ : syracuseStep 663115 = 994673) B994673
theorem B663223 : Blo 587289 663223 := bstep (se 1 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 663223 = 994835) B994835
theorem B2268875 : Blo 587289 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B1122007 : Blo 587289 1122007 := bstep (se 1 (by rfl) ⟨841505, by rfl⟩ : syracuseStep 1122007 = 1683011) B1683011
theorem B1679069 : Blo 587289 1679069 := bstep (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) B629651
theorem B2826049 : Blo 587289 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1122113 : Blo 587289 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B663403 : Blo 587289 663403 := bstep (se 1 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 663403 = 995105) B995105
theorem B991129 : Blo 587289 991129 := bstep (se 2 (by rfl) ⟨371673, by rfl⟩ : syracuseStep 991129 = 743347) B743347
theorem B1417139 : Blo 587289 1417139 := bstep (se 1 (by rfl) ⟨1062854, by rfl⟩ : syracuseStep 1417139 = 2125709) B2125709
theorem B663511 : Blo 587289 663511 := bstep (se 1 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 663511 = 995267) B995267
theorem B1122265 : Blo 587289 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B630775 : Blo 587289 630775 := bstep (se 1 (by rfl) ⟨473081, by rfl⟩ : syracuseStep 630775 = 946163) B946163
theorem B2236481 : Blo 587289 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B663691 : Blo 587289 663691 := bstep (se 1 (by rfl) ⟨497768, by rfl⟩ : syracuseStep 663691 = 995537) B995537
theorem B663799 : Blo 587289 663799 := bstep (se 1 (by rfl) ⟨497849, by rfl⟩ : syracuseStep 663799 = 995699) B995699
theorem B2695517 : Blo 587289 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B663979 : Blo 587289 663979 := bstep (se 1 (by rfl) ⟨497984, by rfl⟩ : syracuseStep 663979 = 995969) B995969
theorem B991703 : Blo 587289 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B664087 : Blo 587289 664087 := bstep (se 1 (by rfl) ⟨498065, by rfl⟩ : syracuseStep 664087 = 996131) B996131
theorem B991831 : Blo 587289 991831 := bstep (se 1 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 991831 = 1487747) B1487747
theorem B664267 : Blo 587289 664267 := bstep (se 1 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 664267 = 996401) B996401
theorem B6693677 : Blo 587289 6693677 := bstep (se 3 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 6693677 = 2510129) B2510129
theorem B664375 : Blo 587289 664375 := bstep (se 1 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 664375 = 996563) B996563
theorem B664555 : Blo 587289 664555 := bstep (se 1 (by rfl) ⟨498416, by rfl⟩ : syracuseStep 664555 = 996833) B996833
theorem B664663 : Blo 587289 664663 := bstep (se 1 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 664663 = 996995) B996995
theorem B992459 : Blo 587289 992459 := bstep (se 1 (by rfl) ⟨744344, by rfl⟩ : syracuseStep 992459 = 1488689) B1488689
theorem B599275 : Blo 587289 599275 := bstep (se 1 (by rfl) ⟨449456, by rfl⟩ : syracuseStep 599275 = 898913) B898913
theorem B664843 : Blo 587289 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B992587 : Blo 587289 992587 := bstep (se 1 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 992587 = 1488881) B1488881
theorem B664951 : Blo 587289 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B2991491 : Blo 587289 2991491 := bstep (se 1 (by rfl) ⟨2243618, by rfl⟩ : syracuseStep 2991491 = 4487237) B4487237
theorem B992729 : Blo 587289 992729 := bstep (se 2 (by rfl) ⟨372273, by rfl⟩ : syracuseStep 992729 = 744547) B744547
theorem B2237969 : Blo 587289 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B665131 : Blo 587289 665131 := bstep (se 1 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 665131 = 997697) B997697
theorem B992857 : Blo 587289 992857 := bstep (se 2 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 992857 = 744643) B744643
theorem B894667 : Blo 587289 894667 := bstep (se 1 (by rfl) ⟨671000, by rfl⟩ : syracuseStep 894667 = 1342001) B1342001
theorem B2828125 : Blo 587289 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B2238425 : Blo 587289 2238425 := bstep (se 2 (by rfl) ⟨839409, by rfl⟩ : syracuseStep 2238425 = 1678819) B1678819
theorem B1255475 : Blo 587289 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B3188801 : Blo 587289 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B1419329 : Blo 587289 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B4040779 : Blo 587289 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B993431 : Blo 587289 993431 := bstep (se 1 (by rfl) ⟨745073, by rfl⟩ : syracuseStep 993431 = 1490147) B1490147
theorem B2238637 : Blo 587289 2238637 := bstep (se 3 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 2238637 = 839489) B839489
theorem B993559 : Blo 587289 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B7547201 : Blo 587289 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B1321433 : Blo 587289 1321433 := bstep (se 2 (by rfl) ⟨495537, by rfl⟩ : syracuseStep 1321433 = 991075) B991075
theorem B2238941 : Blo 587289 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B1321523 : Blo 587289 1321523 := bstep (se 1 (by rfl) ⟨991142, by rfl⟩ : syracuseStep 1321523 = 1982285) B1982285
theorem B1681985 : Blo 587289 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B3582539 : Blo 587289 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B1321559 : Blo 587289 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B1682009 : Blo 587289 1682009 := bstep (se 2 (by rfl) ⟨630753, by rfl⟩ : syracuseStep 1682009 = 1261507) B1261507
theorem B3582557 : Blo 587289 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B13609565 : Blo 587289 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B1321739 : Blo 587289 1321739 := bstep (se 1 (by rfl) ⟨991304, by rfl⟩ : syracuseStep 1321739 = 1982609) B1982609
theorem B3222317 : Blo 587289 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1321793 : Blo 587289 1321793 := bstep (se 2 (by rfl) ⟨495672, by rfl⟩ : syracuseStep 1321793 = 991345) B991345
theorem B994187 : Blo 587289 994187 := bstep (se 1 (by rfl) ⟨745640, by rfl⟩ : syracuseStep 994187 = 1491281) B1491281
theorem B3353561 : Blo 587289 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B1059841 : Blo 587289 1059841 := bstep (se 2 (by rfl) ⟨397440, by rfl⟩ : syracuseStep 1059841 = 794881) B794881
theorem B994315 : Blo 587289 994315 := bstep (se 1 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 994315 = 1491473) B1491473
theorem B1322009 : Blo 587289 1322009 := bstep (se 2 (by rfl) ⟨495753, by rfl⟩ : syracuseStep 1322009 = 991507) B991507
theorem B1322099 : Blo 587289 1322099 := bstep (se 1 (by rfl) ⟨991574, by rfl⟩ : syracuseStep 1322099 = 1983149) B1983149
theorem B1322135 : Blo 587289 1322135 := bstep (se 1 (by rfl) ⟨991601, by rfl⟩ : syracuseStep 1322135 = 1983203) B1983203
theorem B994457 : Blo 587289 994457 := bstep (se 2 (by rfl) ⟨372921, by rfl⟩ : syracuseStep 994457 = 745843) B745843
theorem B1060057 : Blo 587289 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B994585 : Blo 587289 994585 := bstep (se 2 (by rfl) ⟨372969, by rfl⟩ : syracuseStep 994585 = 745939) B745939
theorem B1322315 : Blo 587289 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1256791 : Blo 587289 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B1322369 : Blo 587289 1322369 := bstep (se 2 (by rfl) ⟨495888, by rfl⟩ : syracuseStep 1322369 = 991777) B991777
theorem B1256971 : Blo 587289 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B1257047 : Blo 587289 1257047 := bstep (se 1 (by rfl) ⟨942785, by rfl⟩ : syracuseStep 1257047 = 1885571) B1885571
theorem B1322585 : Blo 587289 1322585 := bstep (se 2 (by rfl) ⟨495969, by rfl⟩ : syracuseStep 1322585 = 991939) B991939
theorem B3190423 : Blo 587289 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B1322675 : Blo 587289 1322675 := bstep (se 1 (by rfl) ⟨992006, by rfl⟩ : syracuseStep 1322675 = 1984013) B1984013
theorem B1322711 : Blo 587289 1322711 := bstep (se 1 (by rfl) ⟨992033, by rfl⟩ : syracuseStep 1322711 = 1984067) B1984067
theorem B1683251 : Blo 587289 1683251 := bstep (se 1 (by rfl) ⟨1262438, by rfl⟩ : syracuseStep 1683251 = 2524877) B2524877
theorem B995159 : Blo 587289 995159 := bstep (se 1 (by rfl) ⟨746369, by rfl⟩ : syracuseStep 995159 = 1492739) B1492739
theorem B1322891 : Blo 587289 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B1322945 : Blo 587289 1322945 := bstep (se 2 (by rfl) ⟨496104, by rfl⟩ : syracuseStep 1322945 = 992209) B992209
theorem B1486795 : Blo 587289 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B995287 : Blo 587289 995287 := bstep (se 1 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 995287 = 1492931) B1492931
theorem B1486937 : Blo 587289 1486937 := bstep (se 2 (by rfl) ⟨557601, by rfl⟩ : syracuseStep 1486937 = 1115203) B1115203
theorem B1323161 : Blo 587289 1323161 := bstep (se 2 (by rfl) ⟨496185, by rfl⟩ : syracuseStep 1323161 = 992371) B992371
theorem B1323251 : Blo 587289 1323251 := bstep (se 1 (by rfl) ⟨992438, by rfl⟩ : syracuseStep 1323251 = 1984877) B1984877
theorem B1323287 : Blo 587289 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1323467 : Blo 587289 1323467 := bstep (se 1 (by rfl) ⟨992600, by rfl⟩ : syracuseStep 1323467 = 1985201) B1985201
theorem B1323521 : Blo 587289 1323521 := bstep (se 2 (by rfl) ⟨496320, by rfl⟩ : syracuseStep 1323521 = 992641) B992641
theorem B995915 : Blo 587289 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B996043 : Blo 587289 996043 := bstep (se 1 (by rfl) ⟨747032, by rfl⟩ : syracuseStep 996043 = 1494065) B1494065
theorem B1323737 : Blo 587289 1323737 := bstep (se 2 (by rfl) ⟨496401, by rfl⟩ : syracuseStep 1323737 = 992803) B992803
theorem B9679621 : Blo 587289 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B1323827 : Blo 587289 1323827 := bstep (se 1 (by rfl) ⟨992870, by rfl⟩ : syracuseStep 1323827 = 1985741) B1985741
theorem B1323863 : Blo 587289 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B996185 : Blo 587289 996185 := bstep (se 2 (by rfl) ⟨373569, by rfl⟩ : syracuseStep 996185 = 747139) B747139
theorem B1487767 : Blo 587289 1487767 := bstep (se 1 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 1487767 = 2231651) B2231651
theorem B996313 : Blo 587289 996313 := bstep (se 2 (by rfl) ⟨373617, by rfl⟩ : syracuseStep 996313 = 747235) B747235
theorem B2241539 : Blo 587289 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B1324043 : Blo 587289 1324043 := bstep (se 1 (by rfl) ⟨993032, by rfl⟩ : syracuseStep 1324043 = 1986065) B1986065
theorem B2241553 : Blo 587289 2241553 := bstep (se 2 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 2241553 = 1681165) B1681165
theorem B1324097 : Blo 587289 1324097 := bstep (se 2 (by rfl) ⟨496536, by rfl⟩ : syracuseStep 1324097 = 993073) B993073
theorem B1324313 : Blo 587289 1324313 := bstep (se 2 (by rfl) ⟨496617, by rfl⟩ : syracuseStep 1324313 = 993235) B993235
theorem B2241857 : Blo 587289 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B1488203 : Blo 587289 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B1258841 : Blo 587289 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B1324403 : Blo 587289 1324403 := bstep (se 1 (by rfl) ⟨993302, by rfl⟩ : syracuseStep 1324403 = 1986605) B1986605
theorem B1324439 : Blo 587289 1324439 := bstep (se 1 (by rfl) ⟨993329, by rfl⟩ : syracuseStep 1324439 = 1986659) B1986659
theorem B3192281 : Blo 587289 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B996887 : Blo 587289 996887 := bstep (se 1 (by rfl) ⟨747665, by rfl⟩ : syracuseStep 996887 = 1495331) B1495331
theorem B3356225 : Blo 587289 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1324619 : Blo 587289 1324619 := bstep (se 1 (by rfl) ⟨993464, by rfl⟩ : syracuseStep 1324619 = 1986929) B1986929
theorem B1324673 : Blo 587289 1324673 := bstep (se 2 (by rfl) ⟨496752, by rfl⟩ : syracuseStep 1324673 = 993505) B993505
theorem B997015 : Blo 587289 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B1488577 : Blo 587289 1488577 := bstep (se 2 (by rfl) ⟨558216, by rfl⟩ : syracuseStep 1488577 = 1116433) B1116433
theorem B6731585 : Blo 587289 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B1324889 : Blo 587289 1324889 := bstep (se 2 (by rfl) ⟨496833, by rfl⟩ : syracuseStep 1324889 = 993667) B993667
theorem B1324979 : Blo 587289 1324979 := bstep (se 1 (by rfl) ⟨993734, by rfl⟩ : syracuseStep 1324979 = 1987469) B1987469
theorem B1325015 : Blo 587289 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B2242525 : Blo 587289 2242525 := bstep (se 3 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 2242525 = 840947) B840947
theorem B604139 : Blo 587289 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B1259507 : Blo 587289 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B4536395 : Blo 587289 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B1325195 : Blo 587289 1325195 := bstep (se 1 (by rfl) ⟨993896, by rfl⟩ : syracuseStep 1325195 = 1987793) B1987793
theorem B4241585 : Blo 587289 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1325249 : Blo 587289 1325249 := bstep (se 2 (by rfl) ⟨496968, by rfl⟩ : syracuseStep 1325249 = 993937) B993937
theorem B997643 : Blo 587289 997643 := bstep (se 1 (by rfl) ⟨748232, by rfl⟩ : syracuseStep 997643 = 1496465) B1496465
theorem B1489175 : Blo 587289 1489175 := bstep (se 1 (by rfl) ⟨1116881, by rfl⟩ : syracuseStep 1489175 = 2233763) B2233763
theorem B12073333 : Blo 587289 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B997771 : Blo 587289 997771 := bstep (se 1 (by rfl) ⟨748328, by rfl⟩ : syracuseStep 997771 = 1496657) B1496657
theorem B1325465 : Blo 587289 1325465 := bstep (se 2 (by rfl) ⟨497049, by rfl⟩ : syracuseStep 1325465 = 994099) B994099
theorem B1882547 : Blo 587289 1882547 := bstep (se 1 (by rfl) ⟨1411910, by rfl⟩ : syracuseStep 1882547 = 2823821) B2823821
theorem B1325555 : Blo 587289 1325555 := bstep (se 1 (by rfl) ⟨994166, by rfl⟩ : syracuseStep 1325555 = 1988333) B1988333
theorem B1325591 : Blo 587289 1325591 := bstep (se 1 (by rfl) ⟨994193, by rfl⟩ : syracuseStep 1325591 = 1988387) B1988387
theorem B1325771 : Blo 587289 1325771 := bstep (se 1 (by rfl) ⟨994328, by rfl⟩ : syracuseStep 1325771 = 1988657) B1988657
theorem B1325825 : Blo 587289 1325825 := bstep (se 2 (by rfl) ⟨497184, by rfl⟩ : syracuseStep 1325825 = 994369) B994369
theorem B1194763 : Blo 587289 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B5094161 : Blo 587289 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1326041 : Blo 587289 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B1326131 : Blo 587289 1326131 := bstep (se 1 (by rfl) ⟨994598, by rfl⟩ : syracuseStep 1326131 = 1989197) B1989197
theorem B1489985 : Blo 587289 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B1326167 : Blo 587289 1326167 := bstep (se 1 (by rfl) ⟨994625, by rfl⟩ : syracuseStep 1326167 = 1989251) B1989251
theorem B2243801 : Blo 587289 2243801 := bstep (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) B1682851
theorem B1326347 : Blo 587289 1326347 := bstep (se 1 (by rfl) ⟨994760, by rfl⟩ : syracuseStep 1326347 = 1989521) B1989521
theorem B1326401 : Blo 587289 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B1261003 : Blo 587289 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B1359385 : Blo 587289 1359385 := bstep (se 2 (by rfl) ⟨509769, by rfl⟩ : syracuseStep 1359385 = 1019539) B1019539
theorem B1326617 : Blo 587289 1326617 := bstep (se 2 (by rfl) ⟨497481, by rfl⟩ : syracuseStep 1326617 = 994963) B994963
theorem B3063361 : Blo 587289 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B638551 : Blo 587289 638551 := bstep (se 1 (by rfl) ⟨478913, by rfl⟩ : syracuseStep 638551 = 957827) B957827
theorem B1490521 : Blo 587289 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B1326707 : Blo 587289 1326707 := bstep (se 1 (by rfl) ⟨995030, by rfl⟩ : syracuseStep 1326707 = 1990061) B1990061
theorem B1326743 : Blo 587289 1326743 := bstep (se 1 (by rfl) ⟨995057, by rfl⟩ : syracuseStep 1326743 = 1990115) B1990115
theorem B5029553 : Blo 587289 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B1883827 : Blo 587289 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B9060101 : Blo 587289 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B1982231 : Blo 587289 1982231 := bstep (se 1 (by rfl) ⟨1486673, by rfl⟩ : syracuseStep 1982231 = 2973347) B2973347
theorem B1195841 : Blo 587289 1195841 := bstep (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) B896881
theorem B1326923 : Blo 587289 1326923 := bstep (se 1 (by rfl) ⟨995192, by rfl⟩ : syracuseStep 1326923 = 1990385) B1990385
theorem B1326977 : Blo 587289 1326977 := bstep (se 2 (by rfl) ⟨497616, by rfl⟩ : syracuseStep 1326977 = 995233) B995233
theorem B1195955 : Blo 587289 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B8044505 : Blo 587289 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B2834507 : Blo 587289 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1327193 : Blo 587289 1327193 := bstep (se 2 (by rfl) ⟨497697, by rfl⟩ : syracuseStep 1327193 = 995395) B995395
theorem B1327283 : Blo 587289 1327283 := bstep (se 1 (by rfl) ⟨995462, by rfl⟩ : syracuseStep 1327283 = 1990925) B1990925
theorem B1327319 : Blo 587289 1327319 := bstep (se 1 (by rfl) ⟨995489, by rfl⟩ : syracuseStep 1327319 = 1990979) B1990979
theorem B5357785 : Blo 587289 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B1982771 : Blo 587289 1982771 := bstep (se 1 (by rfl) ⟨1487078, by rfl⟩ : syracuseStep 1982771 = 2974157) B2974157
theorem B1065305 : Blo 587289 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B1327499 : Blo 587289 1327499 := bstep (se 1 (by rfl) ⟨995624, by rfl⟩ : syracuseStep 1327499 = 1991249) B1991249
theorem B1327553 : Blo 587289 1327553 := bstep (se 2 (by rfl) ⟨497832, by rfl⟩ : syracuseStep 1327553 = 995665) B995665
theorem B1983041 : Blo 587289 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B1327769 : Blo 587289 1327769 := bstep (se 2 (by rfl) ⟨497913, by rfl⟩ : syracuseStep 1327769 = 995827) B995827
theorem B1262233 : Blo 587289 1262233 := bstep (se 2 (by rfl) ⟨473337, by rfl⟩ : syracuseStep 1262233 = 946675) B946675
theorem B1491635 : Blo 587289 1491635 := bstep (se 1 (by rfl) ⟨1118726, by rfl⟩ : syracuseStep 1491635 = 2237453) B2237453
theorem B1327859 : Blo 587289 1327859 := bstep (se 1 (by rfl) ⟨995894, by rfl⟩ : syracuseStep 1327859 = 1991789) B1991789
theorem B1327895 : Blo 587289 1327895 := bstep (se 1 (by rfl) ⟨995921, by rfl⟩ : syracuseStep 1327895 = 1991843) B1991843
theorem B1131329 : Blo 587289 1131329 := bstep (se 2 (by rfl) ⟨424248, by rfl⟩ : syracuseStep 1131329 = 848497) B848497
theorem B3031901 : Blo 587289 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B1328075 : Blo 587289 1328075 := bstep (se 1 (by rfl) ⟨996056, by rfl⟩ : syracuseStep 1328075 = 1992113) B1992113
theorem B1491929 : Blo 587289 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B1328129 : Blo 587289 1328129 := bstep (se 2 (by rfl) ⟨498048, by rfl⟩ : syracuseStep 1328129 = 996097) B996097
theorem B705547 : Blo 587289 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B1983581 : Blo 587289 1983581 := bstep (se 3 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 1983581 = 743843) B743843
theorem B3785879 : Blo 587289 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B1328345 : Blo 587289 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B836887 : Blo 587289 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B1328435 : Blo 587289 1328435 := bstep (se 1 (by rfl) ⟨996326, by rfl⟩ : syracuseStep 1328435 = 1992653) B1992653
theorem B1328471 : Blo 587289 1328471 := bstep (se 1 (by rfl) ⟨996353, by rfl⟩ : syracuseStep 1328471 = 1992707) B1992707
theorem B8504675 : Blo 587289 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B1328651 : Blo 587289 1328651 := bstep (se 1 (by rfl) ⟨996488, by rfl⟩ : syracuseStep 1328651 = 1992977) B1992977
theorem B1328705 : Blo 587289 1328705 := bstep (se 2 (by rfl) ⟨498264, by rfl⟩ : syracuseStep 1328705 = 996529) B996529
theorem B1328921 : Blo 587289 1328921 := bstep (se 2 (by rfl) ⟨498345, by rfl⟩ : syracuseStep 1328921 = 996691) B996691
theorem B1329011 : Blo 587289 1329011 := bstep (se 1 (by rfl) ⟨996758, by rfl⟩ : syracuseStep 1329011 = 1993517) B1993517
theorem B2508695 : Blo 587289 2508695 := bstep (se 1 (by rfl) ⟨1881521, by rfl⟩ : syracuseStep 2508695 = 3763043) B3763043
theorem B1329047 : Blo 587289 1329047 := bstep (se 1 (by rfl) ⟨996785, by rfl⟩ : syracuseStep 1329047 = 1993571) B1993571
theorem B1722391 : Blo 587289 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B5752907 : Blo 587289 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B1329227 : Blo 587289 1329227 := bstep (se 1 (by rfl) ⟨996920, by rfl⟩ : syracuseStep 1329227 = 1993841) B1993841
theorem B1329281 : Blo 587289 1329281 := bstep (se 2 (by rfl) ⟨498480, by rfl⟩ : syracuseStep 1329281 = 996961) B996961
theorem B1984715 : Blo 587289 1984715 := bstep (se 1 (by rfl) ⟨1488536, by rfl⟩ : syracuseStep 1984715 = 2977073) B2977073
theorem B1329497 : Blo 587289 1329497 := bstep (se 2 (by rfl) ⟨498561, by rfl⟩ : syracuseStep 1329497 = 997123) B997123
theorem B1329587 : Blo 587289 1329587 := bstep (se 1 (by rfl) ⟨997190, by rfl⟩ : syracuseStep 1329587 = 1994381) B1994381
theorem B1329623 : Blo 587289 1329623 := bstep (se 1 (by rfl) ⟨997217, by rfl⟩ : syracuseStep 1329623 = 1994435) B1994435
theorem B1984985 : Blo 587289 1984985 := bstep (se 2 (by rfl) ⟨744369, by rfl⟩ : syracuseStep 1984985 = 1488739) B1488739
theorem B1591859 : Blo 587289 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B1493579 : Blo 587289 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B1329803 : Blo 587289 1329803 := bstep (se 1 (by rfl) ⟨997352, by rfl⟩ : syracuseStep 1329803 = 1994705) B1994705
theorem B1329857 : Blo 587289 1329857 := bstep (se 2 (by rfl) ⟨498696, by rfl⟩ : syracuseStep 1329857 = 997393) B997393
theorem B1592011 : Blo 587289 1592011 := bstep (se 1 (by rfl) ⟨1194008, by rfl⟩ : syracuseStep 1592011 = 2388017) B2388017
theorem B707339 : Blo 587289 707339 := bstep (se 1 (by rfl) ⟨530504, by rfl⟩ : syracuseStep 707339 = 1061009) B1061009
theorem B3361601 : Blo 587289 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B1330073 : Blo 587289 1330073 := bstep (se 2 (by rfl) ⟨498777, by rfl⟩ : syracuseStep 1330073 = 997555) B997555
theorem B805847 : Blo 587289 805847 := bstep (se 1 (by rfl) ⟨604385, by rfl⟩ : syracuseStep 805847 = 1208771) B1208771
theorem B1330163 : Blo 587289 1330163 := bstep (se 1 (by rfl) ⟨997622, by rfl⟩ : syracuseStep 1330163 = 1995245) B1995245
theorem B1330199 : Blo 587289 1330199 := bstep (se 1 (by rfl) ⟨997649, by rfl⟩ : syracuseStep 1330199 = 1995299) B1995299
theorem B1985687 : Blo 587289 1985687 := bstep (se 1 (by rfl) ⟨1489265, by rfl⟩ : syracuseStep 1985687 = 2978531) B2978531
theorem B1330379 : Blo 587289 1330379 := bstep (se 1 (by rfl) ⟨997784, by rfl⟩ : syracuseStep 1330379 = 1995569) B1995569
theorem B5033177 : Blo 587289 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B838937 : Blo 587289 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B19123573 : Blo 587289 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B1199603 : Blo 587289 1199603 := bstep (se 1 (by rfl) ⟨899702, by rfl⟩ : syracuseStep 1199603 = 1799405) B1799405
theorem B1592855 : Blo 587289 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B1494551 : Blo 587289 1494551 := bstep (se 1 (by rfl) ⟨1120913, by rfl⟩ : syracuseStep 1494551 = 2241827) B2241827
theorem B3788363 : Blo 587289 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B1986227 : Blo 587289 1986227 := bstep (se 1 (by rfl) ⟨1489670, by rfl⟩ : syracuseStep 1986227 = 2979341) B2979341
theorem B839575 : Blo 587289 839575 := bstep (se 1 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 839575 = 1259363) B1259363
theorem B1986497 : Blo 587289 1986497 := bstep (se 2 (by rfl) ⟨744936, by rfl⟩ : syracuseStep 1986497 = 1489873) B1489873
theorem B2510813 : Blo 587289 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B1495219 : Blo 587289 1495219 := bstep (se 1 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 1495219 = 2242829) B2242829
theorem B2511121 : Blo 587289 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B2511155 : Blo 587289 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B1495361 : Blo 587289 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B1987037 : Blo 587289 1987037 := bstep (se 3 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 1987037 = 745139) B745139
theorem B840395 : Blo 587289 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B3593651 : Blo 587289 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B1496627 : Blo 587289 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1988171 : Blo 587289 1988171 := bstep (se 1 (by rfl) ⟨1491128, by rfl⟩ : syracuseStep 1988171 = 2982257) B2982257
theorem B1594973 : Blo 587289 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B9557635 : Blo 587289 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B841369 : Blo 587289 841369 := bstep (se 2 (by rfl) ⟨315513, by rfl⟩ : syracuseStep 841369 = 631027) B631027
theorem B2414387 : Blo 587289 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B4085569 : Blo 587289 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B5035841 : Blo 587289 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B1988441 : Blo 587289 1988441 := bstep (se 2 (by rfl) ⟨745665, by rfl⟩ : syracuseStep 1988441 = 1491331) B1491331
theorem B2021213 : Blo 587289 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B2119769 : Blo 587289 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B743575 : Blo 587289 743575 := bstep (se 1 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 743575 = 1115363) B1115363
theorem B2513069 : Blo 587289 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B68802929 : Blo 587289 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B1366487 : Blo 587289 1366487 := bstep (se 1 (by rfl) ⟨1024865, by rfl⟩ : syracuseStep 1366487 = 2049731) B2049731
theorem B1399319 : Blo 587289 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B1989143 : Blo 587289 1989143 := bstep (se 1 (by rfl) ⟨1491857, by rfl⟩ : syracuseStep 1989143 = 2983715) B2983715
theorem B2513753 : Blo 587289 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B1989683 : Blo 587289 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B2153603 : Blo 587289 2153603 := bstep (se 1 (by rfl) ⟨1615202, by rfl⟩ : syracuseStep 2153603 = 3230405) B3230405
theorem B7560323 : Blo 587289 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B2120921 : Blo 587289 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B1989953 : Blo 587289 1989953 := bstep (se 2 (by rfl) ⟨746232, by rfl⟩ : syracuseStep 1989953 = 1492465) B1492465
theorem B941401 : Blo 587289 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B4480433 : Blo 587289 4480433 := bstep (se 2 (by rfl) ⟨1680162, by rfl⟩ : syracuseStep 4480433 = 3360325) B3360325
theorem B7167449 : Blo 587289 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B745291 : Blo 587289 745291 := bstep (se 1 (by rfl) ⟨558968, by rfl⟩ : syracuseStep 745291 = 1117937) B1117937
theorem B1990493 : Blo 587289 1990493 := bstep (se 3 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 1990493 = 746435) B746435
theorem B4480919 : Blo 587289 4480919 := bstep (se 1 (by rfl) ⟨3360689, by rfl⟩ : syracuseStep 4480919 = 6721379) B6721379
theorem B1401025 : Blo 587289 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B2384093 : Blo 587289 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B7529111 : Blo 587289 7529111 := bstep (se 1 (by rfl) ⟨5646833, by rfl⟩ : syracuseStep 7529111 = 11293667) B11293667
theorem B2974481 : Blo 587289 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B746263 : Blo 587289 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B2974643 : Blo 587289 2974643 := bstep (se 1 (by rfl) ⟨2230982, by rfl⟩ : syracuseStep 2974643 = 4461965) B4461965
theorem B1991627 : Blo 587289 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B1795123 : Blo 587289 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B1991897 : Blo 587289 1991897 := bstep (se 2 (by rfl) ⟨746961, by rfl⟩ : syracuseStep 1991897 = 1493923) B1493923
theorem B1893593 : Blo 587289 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B2516417 : Blo 587289 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B747083 : Blo 587289 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B1992599 : Blo 587289 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B1009675 : Blo 587289 1009675 := bstep (se 1 (by rfl) ⟨757256, by rfl⟩ : syracuseStep 1009675 = 1514513) B1514513
theorem B747787 : Blo 587289 747787 := bstep (se 1 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 747787 = 1121681) B1121681
theorem B6056369 : Blo 587289 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B1993139 : Blo 587289 1993139 := bstep (se 1 (by rfl) ⟨1494854, by rfl⟩ : syracuseStep 1993139 = 2989709) B2989709
theorem B748055 : Blo 587289 748055 := bstep (se 1 (by rfl) ⟨561041, by rfl⟩ : syracuseStep 748055 = 1122083) B1122083
theorem B944779 : Blo 587289 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B1993409 : Blo 587289 1993409 := bstep (se 2 (by rfl) ⟨747528, by rfl⟩ : syracuseStep 1993409 = 1495057) B1495057
theorem B2976587 : Blo 587289 2976587 := bstep (se 1 (by rfl) ⟨2232440, by rfl⟩ : syracuseStep 2976587 = 4464881) B4464881
theorem B945035 : Blo 587289 945035 := bstep (se 1 (by rfl) ⟨708776, by rfl⟩ : syracuseStep 945035 = 1417553) B1417553
theorem B2517905 : Blo 587289 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B1993949 : Blo 587289 1993949 := bstep (se 3 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 1993949 = 747731) B747731
theorem B5041925 : Blo 587289 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B946009 : Blo 587289 946009 := bstep (se 2 (by rfl) ⟨354753, by rfl⟩ : syracuseStep 946009 = 709507) B709507
theorem B2518877 : Blo 587289 2518877 := bstep (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) B944579
theorem B3764069 : Blo 587289 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B2388113 : Blo 587289 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B2125997 : Blo 587289 2125997 := bstep (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) B797249
theorem B2126027 : Blo 587289 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B1995083 : Blo 587289 1995083 := bstep (se 1 (by rfl) ⟨1496312, by rfl⟩ : syracuseStep 1995083 = 2992625) B2992625
theorem B880985 : Blo 587289 880985 := bstep (se 2 (by rfl) ⟨330369, by rfl⟩ : syracuseStep 880985 = 660739) B660739
theorem B881099 : Blo 587289 881099 := bstep (se 1 (by rfl) ⟨660824, by rfl⟩ : syracuseStep 881099 = 1321649) B1321649
theorem B881111 : Blo 587289 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B881177 : Blo 587289 881177 := bstep (se 2 (by rfl) ⟨330441, by rfl⟩ : syracuseStep 881177 = 660883) B660883
theorem B2978369 : Blo 587289 2978369 := bstep (se 2 (by rfl) ⟨1116888, by rfl⟩ : syracuseStep 2978369 = 2233777) B2233777
theorem B1995353 : Blo 587289 1995353 := bstep (se 2 (by rfl) ⟨748257, by rfl⟩ : syracuseStep 1995353 = 1496515) B1496515
theorem B881291 : Blo 587289 881291 := bstep (se 1 (by rfl) ⟨660968, by rfl⟩ : syracuseStep 881291 = 1321937) B1321937
theorem B881303 : Blo 587289 881303 := bstep (se 1 (by rfl) ⟨660977, by rfl⟩ : syracuseStep 881303 = 1321955) B1321955
theorem B881369 : Blo 587289 881369 := bstep (se 2 (by rfl) ⟨330513, by rfl⟩ : syracuseStep 881369 = 661027) B661027
theorem B881483 : Blo 587289 881483 := bstep (se 1 (by rfl) ⟨661112, by rfl⟩ : syracuseStep 881483 = 1322225) B1322225
theorem B881495 : Blo 587289 881495 := bstep (se 1 (by rfl) ⟨661121, by rfl⟩ : syracuseStep 881495 = 1322243) B1322243
theorem B881561 : Blo 587289 881561 := bstep (se 2 (by rfl) ⟨330585, by rfl⟩ : syracuseStep 881561 = 661171) B661171
theorem B4027315 : Blo 587289 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B881675 : Blo 587289 881675 := bstep (se 1 (by rfl) ⟨661256, by rfl⟩ : syracuseStep 881675 = 1322513) B1322513
theorem B881687 : Blo 587289 881687 := bstep (se 1 (by rfl) ⟨661265, by rfl⟩ : syracuseStep 881687 = 1322531) B1322531
theorem B3175499 : Blo 587289 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B881753 : Blo 587289 881753 := bstep (se 2 (by rfl) ⟨330657, by rfl⟩ : syracuseStep 881753 = 661315) B661315
theorem B881867 : Blo 587289 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B881879 : Blo 587289 881879 := bstep (se 1 (by rfl) ⟨661409, by rfl⟩ : syracuseStep 881879 = 1322819) B1322819
theorem B881945 : Blo 587289 881945 := bstep (se 2 (by rfl) ⟨330729, by rfl⟩ : syracuseStep 881945 = 661459) B661459
theorem B1078553 : Blo 587289 1078553 := bstep (se 2 (by rfl) ⟨404457, by rfl⟩ : syracuseStep 1078553 = 808915) B808915
theorem B4846979 : Blo 587289 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B882059 : Blo 587289 882059 := bstep (se 1 (by rfl) ⟨661544, by rfl⟩ : syracuseStep 882059 = 1323089) B1323089
theorem B882071 : Blo 587289 882071 := bstep (se 1 (by rfl) ⟨661553, by rfl⟩ : syracuseStep 882071 = 1323107) B1323107
theorem B882137 : Blo 587289 882137 := bstep (se 2 (by rfl) ⟨330801, by rfl⟩ : syracuseStep 882137 = 661603) B661603
theorem B587307 : Blo 587289 587307 := bstep (se 1 (by rfl) ⟨440480, by rfl⟩ : syracuseStep 587307 = 880961) B880961
theorem B587319 : Blo 587289 587319 := bstep (se 1 (by rfl) ⟨440489, by rfl⟩ : syracuseStep 587319 = 880979) B880979
theorem B587339 : Blo 587289 587339 := bstep (se 1 (by rfl) ⟨440504, by rfl⟩ : syracuseStep 587339 = 881009) B881009
theorem B882251 : Blo 587289 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B587351 : Blo 587289 587351 := bstep (se 1 (by rfl) ⟨440513, by rfl⟩ : syracuseStep 587351 = 881027) B881027
theorem B882263 : Blo 587289 882263 := bstep (se 1 (by rfl) ⟨661697, by rfl⟩ : syracuseStep 882263 = 1323395) B1323395
theorem B587371 : Blo 587289 587371 := bstep (se 1 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 587371 = 881057) B881057
theorem B587383 : Blo 587289 587383 := bstep (se 1 (by rfl) ⟨440537, by rfl⟩ : syracuseStep 587383 = 881075) B881075
theorem B587403 : Blo 587289 587403 := bstep (se 1 (by rfl) ⟨440552, by rfl⟩ : syracuseStep 587403 = 881105) B881105
theorem B587415 : Blo 587289 587415 := bstep (se 1 (by rfl) ⟨440561, by rfl⟩ : syracuseStep 587415 = 881123) B881123
theorem B882329 : Blo 587289 882329 := bstep (se 2 (by rfl) ⟨330873, by rfl⟩ : syracuseStep 882329 = 661747) B661747
theorem B587435 : Blo 587289 587435 := bstep (se 1 (by rfl) ⟨440576, by rfl⟩ : syracuseStep 587435 = 881153) B881153
theorem B587447 : Blo 587289 587447 := bstep (se 1 (by rfl) ⟨440585, by rfl⟩ : syracuseStep 587447 = 881171) B881171
theorem B587467 : Blo 587289 587467 := bstep (se 1 (by rfl) ⟨440600, by rfl⟩ : syracuseStep 587467 = 881201) B881201
theorem B587479 : Blo 587289 587479 := bstep (se 1 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 587479 = 881219) B881219
theorem B587499 : Blo 587289 587499 := bstep (se 1 (by rfl) ⟨440624, by rfl⟩ : syracuseStep 587499 = 881249) B881249
theorem B587511 : Blo 587289 587511 := bstep (se 1 (by rfl) ⟨440633, by rfl⟩ : syracuseStep 587511 = 881267) B881267
theorem B587531 : Blo 587289 587531 := bstep (se 1 (by rfl) ⟨440648, by rfl⟩ : syracuseStep 587531 = 881297) B881297
theorem B882443 : Blo 587289 882443 := bstep (se 1 (by rfl) ⟨661832, by rfl⟩ : syracuseStep 882443 = 1323665) B1323665
theorem B587543 : Blo 587289 587543 := bstep (se 1 (by rfl) ⟨440657, by rfl⟩ : syracuseStep 587543 = 881315) B881315
theorem B882455 : Blo 587289 882455 := bstep (se 1 (by rfl) ⟨661841, by rfl⟩ : syracuseStep 882455 = 1323683) B1323683
theorem B587563 : Blo 587289 587563 := bstep (se 1 (by rfl) ⟨440672, by rfl⟩ : syracuseStep 587563 = 881345) B881345
theorem B587575 : Blo 587289 587575 := bstep (se 1 (by rfl) ⟨440681, by rfl⟩ : syracuseStep 587575 = 881363) B881363
theorem B587595 : Blo 587289 587595 := bstep (se 1 (by rfl) ⟨440696, by rfl⟩ : syracuseStep 587595 = 881393) B881393
theorem B587607 : Blo 587289 587607 := bstep (se 1 (by rfl) ⟨440705, by rfl⟩ : syracuseStep 587607 = 881411) B881411
theorem B882521 : Blo 587289 882521 := bstep (se 2 (by rfl) ⟨330945, by rfl⟩ : syracuseStep 882521 = 661891) B661891
theorem B587627 : Blo 587289 587627 := bstep (se 1 (by rfl) ⟨440720, by rfl⟩ : syracuseStep 587627 = 881441) B881441
theorem B587639 : Blo 587289 587639 := bstep (se 1 (by rfl) ⟨440729, by rfl⟩ : syracuseStep 587639 = 881459) B881459
theorem B587659 : Blo 587289 587659 := bstep (se 1 (by rfl) ⟨440744, by rfl⟩ : syracuseStep 587659 = 881489) B881489
theorem B587671 : Blo 587289 587671 := bstep (se 1 (by rfl) ⟨440753, by rfl⟩ : syracuseStep 587671 = 881507) B881507
theorem B587691 : Blo 587289 587691 := bstep (se 1 (by rfl) ⟨440768, by rfl⟩ : syracuseStep 587691 = 881537) B881537
theorem B587703 : Blo 587289 587703 := bstep (se 1 (by rfl) ⟨440777, by rfl⟩ : syracuseStep 587703 = 881555) B881555
theorem B587723 : Blo 587289 587723 := bstep (se 1 (by rfl) ⟨440792, by rfl⟩ : syracuseStep 587723 = 881585) B881585
theorem B882635 : Blo 587289 882635 := bstep (se 1 (by rfl) ⟨661976, by rfl⟩ : syracuseStep 882635 = 1323953) B1323953
theorem B587735 : Blo 587289 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B882647 : Blo 587289 882647 := bstep (se 1 (by rfl) ⟨661985, by rfl⟩ : syracuseStep 882647 = 1323971) B1323971
theorem B6387673 : Blo 587289 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B587755 : Blo 587289 587755 := bstep (se 1 (by rfl) ⟨440816, by rfl⟩ : syracuseStep 587755 = 881633) B881633
theorem B587767 : Blo 587289 587767 := bstep (se 1 (by rfl) ⟨440825, by rfl⟩ : syracuseStep 587767 = 881651) B881651
theorem B587787 : Blo 587289 587787 := bstep (se 1 (by rfl) ⟨440840, by rfl⟩ : syracuseStep 587787 = 881681) B881681
theorem B587799 : Blo 587289 587799 := bstep (se 1 (by rfl) ⟨440849, by rfl⟩ : syracuseStep 587799 = 881699) B881699
theorem B882713 : Blo 587289 882713 := bstep (se 2 (by rfl) ⟨331017, by rfl⟩ : syracuseStep 882713 = 662035) B662035
theorem B587819 : Blo 587289 587819 := bstep (se 1 (by rfl) ⟨440864, by rfl⟩ : syracuseStep 587819 = 881729) B881729
theorem B587831 : Blo 587289 587831 := bstep (se 1 (by rfl) ⟨440873, by rfl⟩ : syracuseStep 587831 = 881747) B881747
theorem B587851 : Blo 587289 587851 := bstep (se 1 (by rfl) ⟨440888, by rfl⟩ : syracuseStep 587851 = 881777) B881777
theorem B587863 : Blo 587289 587863 := bstep (se 1 (by rfl) ⟨440897, by rfl⟩ : syracuseStep 587863 = 881795) B881795
theorem B587883 : Blo 587289 587883 := bstep (se 1 (by rfl) ⟨440912, by rfl⟩ : syracuseStep 587883 = 881825) B881825
theorem B587895 : Blo 587289 587895 := bstep (se 1 (by rfl) ⟨440921, by rfl⟩ : syracuseStep 587895 = 881843) B881843
theorem B2685059 : Blo 587289 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B587915 : Blo 587289 587915 := bstep (se 1 (by rfl) ⟨440936, by rfl⟩ : syracuseStep 587915 = 881873) B881873
theorem B882827 : Blo 587289 882827 := bstep (se 1 (by rfl) ⟨662120, by rfl⟩ : syracuseStep 882827 = 1324241) B1324241
theorem B587927 : Blo 587289 587927 := bstep (se 1 (by rfl) ⟨440945, by rfl⟩ : syracuseStep 587927 = 881891) B881891
theorem B882839 : Blo 587289 882839 := bstep (se 1 (by rfl) ⟨662129, by rfl⟩ : syracuseStep 882839 = 1324259) B1324259
theorem B587947 : Blo 587289 587947 := bstep (se 1 (by rfl) ⟨440960, by rfl⟩ : syracuseStep 587947 = 881921) B881921
theorem B587959 : Blo 587289 587959 := bstep (se 1 (by rfl) ⟨440969, by rfl⟩ : syracuseStep 587959 = 881939) B881939
theorem B587979 : Blo 587289 587979 := bstep (se 1 (by rfl) ⟨440984, by rfl⟩ : syracuseStep 587979 = 881969) B881969
theorem B587991 : Blo 587289 587991 := bstep (se 1 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 587991 = 881987) B881987
theorem B882905 : Blo 587289 882905 := bstep (se 2 (by rfl) ⟨331089, by rfl⟩ : syracuseStep 882905 = 662179) B662179
theorem B588011 : Blo 587289 588011 := bstep (se 1 (by rfl) ⟨441008, by rfl⟩ : syracuseStep 588011 = 882017) B882017
theorem B588023 : Blo 587289 588023 := bstep (se 1 (by rfl) ⟨441017, by rfl⟩ : syracuseStep 588023 = 882035) B882035
theorem B588043 : Blo 587289 588043 := bstep (se 1 (by rfl) ⟨441032, by rfl⟩ : syracuseStep 588043 = 882065) B882065
theorem B1341707 : Blo 587289 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B588055 : Blo 587289 588055 := bstep (se 1 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 588055 = 882083) B882083
theorem B588075 : Blo 587289 588075 := bstep (se 1 (by rfl) ⟨441056, by rfl⟩ : syracuseStep 588075 = 882113) B882113
theorem B588087 : Blo 587289 588087 := bstep (se 1 (by rfl) ⟨441065, by rfl⟩ : syracuseStep 588087 = 882131) B882131
theorem B10090817 : Blo 587289 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B588107 : Blo 587289 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B883019 : Blo 587289 883019 := bstep (se 1 (by rfl) ⟨662264, by rfl⟩ : syracuseStep 883019 = 1324529) B1324529
theorem B588119 : Blo 587289 588119 := bstep (se 1 (by rfl) ⟨441089, by rfl⟩ : syracuseStep 588119 = 882179) B882179
theorem B883031 : Blo 587289 883031 := bstep (se 1 (by rfl) ⟨662273, by rfl⟩ : syracuseStep 883031 = 1324547) B1324547
theorem B588139 : Blo 587289 588139 := bstep (se 1 (by rfl) ⟨441104, by rfl⟩ : syracuseStep 588139 = 882209) B882209
theorem B588151 : Blo 587289 588151 := bstep (se 1 (by rfl) ⟨441113, by rfl⟩ : syracuseStep 588151 = 882227) B882227
theorem B2521475 : Blo 587289 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B588171 : Blo 587289 588171 := bstep (se 1 (by rfl) ⟨441128, by rfl⟩ : syracuseStep 588171 = 882257) B882257
theorem B588183 : Blo 587289 588183 := bstep (se 1 (by rfl) ⟨441137, by rfl⟩ : syracuseStep 588183 = 882275) B882275
theorem B883097 : Blo 587289 883097 := bstep (se 2 (by rfl) ⟨331161, by rfl⟩ : syracuseStep 883097 = 662323) B662323
theorem B588203 : Blo 587289 588203 := bstep (se 1 (by rfl) ⟨441152, by rfl⟩ : syracuseStep 588203 = 882305) B882305
theorem B588215 : Blo 587289 588215 := bstep (se 1 (by rfl) ⟨441161, by rfl⟩ : syracuseStep 588215 = 882323) B882323
theorem B588235 : Blo 587289 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B588247 : Blo 587289 588247 := bstep (se 1 (by rfl) ⟨441185, by rfl⟩ : syracuseStep 588247 = 882371) B882371
theorem B2980313 : Blo 587289 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B588267 : Blo 587289 588267 := bstep (se 1 (by rfl) ⟨441200, by rfl⟩ : syracuseStep 588267 = 882401) B882401
theorem B588279 : Blo 587289 588279 := bstep (se 1 (by rfl) ⟨441209, by rfl⟩ : syracuseStep 588279 = 882419) B882419
theorem B588299 : Blo 587289 588299 := bstep (se 1 (by rfl) ⟨441224, by rfl⟩ : syracuseStep 588299 = 882449) B882449
theorem B883211 : Blo 587289 883211 := bstep (se 1 (by rfl) ⟨662408, by rfl⟩ : syracuseStep 883211 = 1324817) B1324817
theorem B588311 : Blo 587289 588311 := bstep (se 1 (by rfl) ⟨441233, by rfl⟩ : syracuseStep 588311 = 882467) B882467
theorem B883223 : Blo 587289 883223 := bstep (se 1 (by rfl) ⟨662417, by rfl⟩ : syracuseStep 883223 = 1324835) B1324835
theorem B588331 : Blo 587289 588331 := bstep (se 1 (by rfl) ⟨441248, by rfl⟩ : syracuseStep 588331 = 882497) B882497
theorem B588343 : Blo 587289 588343 := bstep (se 1 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 588343 = 882515) B882515
theorem B588363 : Blo 587289 588363 := bstep (se 1 (by rfl) ⟨441272, by rfl⟩ : syracuseStep 588363 = 882545) B882545
theorem B588375 : Blo 587289 588375 := bstep (se 1 (by rfl) ⟨441281, by rfl⟩ : syracuseStep 588375 = 882563) B882563
theorem B883289 : Blo 587289 883289 := bstep (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) B662467
theorem B588395 : Blo 587289 588395 := bstep (se 1 (by rfl) ⟨441296, by rfl⟩ : syracuseStep 588395 = 882593) B882593
theorem B588407 : Blo 587289 588407 := bstep (se 1 (by rfl) ⟨441305, by rfl⟩ : syracuseStep 588407 = 882611) B882611
theorem B588427 : Blo 587289 588427 := bstep (se 1 (by rfl) ⟨441320, by rfl⟩ : syracuseStep 588427 = 882641) B882641
theorem B588439 : Blo 587289 588439 := bstep (se 1 (by rfl) ⟨441329, by rfl⟩ : syracuseStep 588439 = 882659) B882659
theorem B588459 : Blo 587289 588459 := bstep (se 1 (by rfl) ⟨441344, by rfl⟩ : syracuseStep 588459 = 882689) B882689
theorem B588471 : Blo 587289 588471 := bstep (se 1 (by rfl) ⟨441353, by rfl⟩ : syracuseStep 588471 = 882707) B882707
theorem B588491 : Blo 587289 588491 := bstep (se 1 (by rfl) ⟨441368, by rfl⟩ : syracuseStep 588491 = 882737) B882737
theorem B883403 : Blo 587289 883403 := bstep (se 1 (by rfl) ⟨662552, by rfl⟩ : syracuseStep 883403 = 1325105) B1325105
theorem B588503 : Blo 587289 588503 := bstep (se 1 (by rfl) ⟨441377, by rfl⟩ : syracuseStep 588503 = 882755) B882755
theorem B883415 : Blo 587289 883415 := bstep (se 1 (by rfl) ⟨662561, by rfl⟩ : syracuseStep 883415 = 1325123) B1325123
theorem B2521817 : Blo 587289 2521817 := bstep (se 2 (by rfl) ⟨945681, by rfl⟩ : syracuseStep 2521817 = 1891363) B1891363
theorem B588523 : Blo 587289 588523 := bstep (se 1 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 588523 = 882785) B882785
theorem B588535 : Blo 587289 588535 := bstep (se 1 (by rfl) ⟨441401, by rfl⟩ : syracuseStep 588535 = 882803) B882803
theorem B588555 : Blo 587289 588555 := bstep (se 1 (by rfl) ⟨441416, by rfl⟩ : syracuseStep 588555 = 882833) B882833
theorem B588567 : Blo 587289 588567 := bstep (se 1 (by rfl) ⟨441425, by rfl⟩ : syracuseStep 588567 = 882851) B882851
theorem B883481 : Blo 587289 883481 := bstep (se 2 (by rfl) ⟨331305, by rfl⟩ : syracuseStep 883481 = 662611) B662611
theorem B588587 : Blo 587289 588587 := bstep (se 1 (by rfl) ⟨441440, by rfl⟩ : syracuseStep 588587 = 882881) B882881
theorem B588599 : Blo 587289 588599 := bstep (se 1 (by rfl) ⟨441449, by rfl⟩ : syracuseStep 588599 = 882899) B882899
theorem B8584001 : Blo 587289 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B588619 : Blo 587289 588619 := bstep (se 1 (by rfl) ⟨441464, by rfl⟩ : syracuseStep 588619 = 882929) B882929
theorem B588631 : Blo 587289 588631 := bstep (se 1 (by rfl) ⟨441473, by rfl⟩ : syracuseStep 588631 = 882947) B882947
theorem B588651 : Blo 587289 588651 := bstep (se 1 (by rfl) ⟨441488, by rfl⟩ : syracuseStep 588651 = 882977) B882977
theorem B588663 : Blo 587289 588663 := bstep (se 1 (by rfl) ⟨441497, by rfl⟩ : syracuseStep 588663 = 882995) B882995
theorem B588683 : Blo 587289 588683 := bstep (se 1 (by rfl) ⟨441512, by rfl⟩ : syracuseStep 588683 = 883025) B883025
theorem B883595 : Blo 587289 883595 := bstep (se 1 (by rfl) ⟨662696, by rfl⟩ : syracuseStep 883595 = 1325393) B1325393
theorem B588695 : Blo 587289 588695 := bstep (se 1 (by rfl) ⟨441521, by rfl⟩ : syracuseStep 588695 = 883043) B883043
theorem B883607 : Blo 587289 883607 := bstep (se 1 (by rfl) ⟨662705, by rfl⟩ : syracuseStep 883607 = 1325411) B1325411
theorem B588715 : Blo 587289 588715 := bstep (se 1 (by rfl) ⟨441536, by rfl⟩ : syracuseStep 588715 = 883073) B883073
theorem B588727 : Blo 587289 588727 := bstep (se 1 (by rfl) ⟨441545, by rfl⟩ : syracuseStep 588727 = 883091) B883091
theorem B588747 : Blo 587289 588747 := bstep (se 1 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 588747 = 883121) B883121
theorem B2685899 : Blo 587289 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B588759 : Blo 587289 588759 := bstep (se 1 (by rfl) ⟨441569, by rfl⟩ : syracuseStep 588759 = 883139) B883139
theorem B883673 : Blo 587289 883673 := bstep (se 2 (by rfl) ⟨331377, by rfl⟩ : syracuseStep 883673 = 662755) B662755
theorem B588779 : Blo 587289 588779 := bstep (se 1 (by rfl) ⟨441584, by rfl⟩ : syracuseStep 588779 = 883169) B883169
theorem B588791 : Blo 587289 588791 := bstep (se 1 (by rfl) ⟨441593, by rfl⟩ : syracuseStep 588791 = 883187) B883187
theorem B588811 : Blo 587289 588811 := bstep (se 1 (by rfl) ⟨441608, by rfl⟩ : syracuseStep 588811 = 883217) B883217
theorem B4488209 : Blo 587289 4488209 := bstep (se 2 (by rfl) ⟨1683078, by rfl⟩ : syracuseStep 4488209 = 3366157) B3366157
theorem B588823 : Blo 587289 588823 := bstep (se 1 (by rfl) ⟨441617, by rfl⟩ : syracuseStep 588823 = 883235) B883235
theorem B588843 : Blo 587289 588843 := bstep (se 1 (by rfl) ⟨441632, by rfl⟩ : syracuseStep 588843 = 883265) B883265
theorem B588855 : Blo 587289 588855 := bstep (se 1 (by rfl) ⟨441641, by rfl⟩ : syracuseStep 588855 = 883283) B883283
theorem B1866817 : Blo 587289 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B588875 : Blo 587289 588875 := bstep (se 1 (by rfl) ⟨441656, by rfl⟩ : syracuseStep 588875 = 883313) B883313
theorem B883787 : Blo 587289 883787 := bstep (se 1 (by rfl) ⟨662840, by rfl⟩ : syracuseStep 883787 = 1325681) B1325681
theorem B588887 : Blo 587289 588887 := bstep (se 1 (by rfl) ⟨441665, by rfl⟩ : syracuseStep 588887 = 883331) B883331
theorem B883799 : Blo 587289 883799 := bstep (se 1 (by rfl) ⟨662849, by rfl⟩ : syracuseStep 883799 = 1325699) B1325699
theorem B7568477 : Blo 587289 7568477 := bstep (se 3 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 7568477 = 2838179) B2838179
theorem B4258909 : Blo 587289 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B588907 : Blo 587289 588907 := bstep (se 1 (by rfl) ⟨441680, by rfl⟩ : syracuseStep 588907 = 883361) B883361
theorem B588919 : Blo 587289 588919 := bstep (se 1 (by rfl) ⟨441689, by rfl⟩ : syracuseStep 588919 = 883379) B883379
theorem B588939 : Blo 587289 588939 := bstep (se 1 (by rfl) ⟨441704, by rfl⟩ : syracuseStep 588939 = 883409) B883409
theorem B588951 : Blo 587289 588951 := bstep (se 1 (by rfl) ⟨441713, by rfl⟩ : syracuseStep 588951 = 883427) B883427
theorem B883865 : Blo 587289 883865 := bstep (se 2 (by rfl) ⟨331449, by rfl⟩ : syracuseStep 883865 = 662899) B662899
theorem B588971 : Blo 587289 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B588983 : Blo 587289 588983 := bstep (se 1 (by rfl) ⟨441737, by rfl⟩ : syracuseStep 588983 = 883475) B883475
theorem B589003 : Blo 587289 589003 := bstep (se 1 (by rfl) ⟨441752, by rfl⟩ : syracuseStep 589003 = 883505) B883505
theorem B589015 : Blo 587289 589015 := bstep (se 1 (by rfl) ⟨441761, by rfl⟩ : syracuseStep 589015 = 883523) B883523
theorem B589035 : Blo 587289 589035 := bstep (se 1 (by rfl) ⟨441776, by rfl⟩ : syracuseStep 589035 = 883553) B883553
theorem B589047 : Blo 587289 589047 := bstep (se 1 (by rfl) ⟨441785, by rfl⟩ : syracuseStep 589047 = 883571) B883571
theorem B589067 : Blo 587289 589067 := bstep (se 1 (by rfl) ⟨441800, by rfl⟩ : syracuseStep 589067 = 883601) B883601
theorem B883979 : Blo 587289 883979 := bstep (se 1 (by rfl) ⟨662984, by rfl⟩ : syracuseStep 883979 = 1325969) B1325969
theorem B589079 : Blo 587289 589079 := bstep (se 1 (by rfl) ⟨441809, by rfl⟩ : syracuseStep 589079 = 883619) B883619
theorem B883991 : Blo 587289 883991 := bstep (se 1 (by rfl) ⟨662993, by rfl⟩ : syracuseStep 883991 = 1325987) B1325987
theorem B589099 : Blo 587289 589099 := bstep (se 1 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 589099 = 883649) B883649
theorem B589111 : Blo 587289 589111 := bstep (se 1 (by rfl) ⟨441833, by rfl⟩ : syracuseStep 589111 = 883667) B883667
theorem B589131 : Blo 587289 589131 := bstep (se 1 (by rfl) ⟨441848, by rfl⟩ : syracuseStep 589131 = 883697) B883697
theorem B589143 : Blo 587289 589143 := bstep (se 1 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 589143 = 883715) B883715
theorem B884057 : Blo 587289 884057 := bstep (se 2 (by rfl) ⟨331521, by rfl⟩ : syracuseStep 884057 = 663043) B663043
theorem B589163 : Blo 587289 589163 := bstep (se 1 (by rfl) ⟨441872, by rfl⟩ : syracuseStep 589163 = 883745) B883745
theorem B589175 : Blo 587289 589175 := bstep (se 1 (by rfl) ⟨441881, by rfl⟩ : syracuseStep 589175 = 883763) B883763
theorem B589195 : Blo 587289 589195 := bstep (se 1 (by rfl) ⟨441896, by rfl⟩ : syracuseStep 589195 = 883793) B883793
theorem B589207 : Blo 587289 589207 := bstep (se 1 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 589207 = 883811) B883811
theorem B589227 : Blo 587289 589227 := bstep (se 1 (by rfl) ⟨441920, by rfl⟩ : syracuseStep 589227 = 883841) B883841
theorem B589239 : Blo 587289 589239 := bstep (se 1 (by rfl) ⟨441929, by rfl⟩ : syracuseStep 589239 = 883859) B883859
theorem B589259 : Blo 587289 589259 := bstep (se 1 (by rfl) ⟨441944, by rfl⟩ : syracuseStep 589259 = 883889) B883889
theorem B884171 : Blo 587289 884171 := bstep (se 1 (by rfl) ⟨663128, by rfl⟩ : syracuseStep 884171 = 1326257) B1326257
theorem B589271 : Blo 587289 589271 := bstep (se 1 (by rfl) ⟨441953, by rfl⟩ : syracuseStep 589271 = 883907) B883907
theorem B884183 : Blo 587289 884183 := bstep (se 1 (by rfl) ⟨663137, by rfl⟩ : syracuseStep 884183 = 1326275) B1326275
theorem B589291 : Blo 587289 589291 := bstep (se 1 (by rfl) ⟨441968, by rfl⟩ : syracuseStep 589291 = 883937) B883937
theorem B589303 : Blo 587289 589303 := bstep (se 1 (by rfl) ⟨441977, by rfl⟩ : syracuseStep 589303 = 883955) B883955
theorem B589323 : Blo 587289 589323 := bstep (se 1 (by rfl) ⟨441992, by rfl⟩ : syracuseStep 589323 = 883985) B883985
theorem B589335 : Blo 587289 589335 := bstep (se 1 (by rfl) ⟨442001, by rfl⟩ : syracuseStep 589335 = 884003) B884003
theorem B1211927 : Blo 587289 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B884249 : Blo 587289 884249 := bstep (se 2 (by rfl) ⟨331593, by rfl⟩ : syracuseStep 884249 = 663187) B663187
theorem B589355 : Blo 587289 589355 := bstep (se 1 (by rfl) ⟨442016, by rfl⟩ : syracuseStep 589355 = 884033) B884033
theorem B589367 : Blo 587289 589367 := bstep (se 1 (by rfl) ⟨442025, by rfl⟩ : syracuseStep 589367 = 884051) B884051
theorem B589387 : Blo 587289 589387 := bstep (se 1 (by rfl) ⟨442040, by rfl⟩ : syracuseStep 589387 = 884081) B884081
theorem B589399 : Blo 587289 589399 := bstep (se 1 (by rfl) ⟨442049, by rfl⟩ : syracuseStep 589399 = 884099) B884099
theorem B589419 : Blo 587289 589419 := bstep (se 1 (by rfl) ⟨442064, by rfl⟩ : syracuseStep 589419 = 884129) B884129
theorem B589431 : Blo 587289 589431 := bstep (se 1 (by rfl) ⟨442073, by rfl⟩ : syracuseStep 589431 = 884147) B884147
theorem B589451 : Blo 587289 589451 := bstep (se 1 (by rfl) ⟨442088, by rfl⟩ : syracuseStep 589451 = 884177) B884177
theorem B884363 : Blo 587289 884363 := bstep (se 1 (by rfl) ⟨663272, by rfl⟩ : syracuseStep 884363 = 1326545) B1326545
theorem B589463 : Blo 587289 589463 := bstep (se 1 (by rfl) ⟨442097, by rfl⟩ : syracuseStep 589463 = 884195) B884195
theorem B884375 : Blo 587289 884375 := bstep (se 1 (by rfl) ⟨663281, by rfl⟩ : syracuseStep 884375 = 1326563) B1326563
theorem B589483 : Blo 587289 589483 := bstep (se 1 (by rfl) ⟨442112, by rfl⟩ : syracuseStep 589483 = 884225) B884225
theorem B589495 : Blo 587289 589495 := bstep (se 1 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 589495 = 884243) B884243
theorem B589515 : Blo 587289 589515 := bstep (se 1 (by rfl) ⟨442136, by rfl⟩ : syracuseStep 589515 = 884273) B884273
theorem B589527 : Blo 587289 589527 := bstep (se 1 (by rfl) ⟨442145, by rfl⟩ : syracuseStep 589527 = 884291) B884291
theorem B884441 : Blo 587289 884441 := bstep (se 2 (by rfl) ⟨331665, by rfl⟩ : syracuseStep 884441 = 663331) B663331
theorem B589547 : Blo 587289 589547 := bstep (se 1 (by rfl) ⟨442160, by rfl⟩ : syracuseStep 589547 = 884321) B884321
theorem B589559 : Blo 587289 589559 := bstep (se 1 (by rfl) ⟨442169, by rfl⟩ : syracuseStep 589559 = 884339) B884339
theorem B589579 : Blo 587289 589579 := bstep (se 1 (by rfl) ⟨442184, by rfl⟩ : syracuseStep 589579 = 884369) B884369
theorem B589591 : Blo 587289 589591 := bstep (se 1 (by rfl) ⟨442193, by rfl⟩ : syracuseStep 589591 = 884387) B884387
theorem B589611 : Blo 587289 589611 := bstep (se 1 (by rfl) ⟨442208, by rfl⟩ : syracuseStep 589611 = 884417) B884417
theorem B589623 : Blo 587289 589623 := bstep (se 1 (by rfl) ⟨442217, by rfl⟩ : syracuseStep 589623 = 884435) B884435
theorem B589643 : Blo 587289 589643 := bstep (se 1 (by rfl) ⟨442232, by rfl⟩ : syracuseStep 589643 = 884465) B884465
theorem B884555 : Blo 587289 884555 := bstep (se 1 (by rfl) ⟨663416, by rfl⟩ : syracuseStep 884555 = 1326833) B1326833
theorem B589655 : Blo 587289 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B884567 : Blo 587289 884567 := bstep (se 1 (by rfl) ⟨663425, by rfl⟩ : syracuseStep 884567 = 1326851) B1326851
theorem B589675 : Blo 587289 589675 := bstep (se 1 (by rfl) ⟨442256, by rfl⟩ : syracuseStep 589675 = 884513) B884513
theorem B589687 : Blo 587289 589687 := bstep (se 1 (by rfl) ⟨442265, by rfl⟩ : syracuseStep 589687 = 884531) B884531
theorem B589707 : Blo 587289 589707 := bstep (se 1 (by rfl) ⟨442280, by rfl⟩ : syracuseStep 589707 = 884561) B884561
theorem B589719 : Blo 587289 589719 := bstep (se 1 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 589719 = 884579) B884579
theorem B884633 : Blo 587289 884633 := bstep (se 2 (by rfl) ⟨331737, by rfl⟩ : syracuseStep 884633 = 663475) B663475
theorem B589739 : Blo 587289 589739 := bstep (se 1 (by rfl) ⟨442304, by rfl⟩ : syracuseStep 589739 = 884609) B884609
theorem B589751 : Blo 587289 589751 := bstep (se 1 (by rfl) ⟨442313, by rfl⟩ : syracuseStep 589751 = 884627) B884627
theorem B589771 : Blo 587289 589771 := bstep (se 1 (by rfl) ⟨442328, by rfl⟩ : syracuseStep 589771 = 884657) B884657
theorem B589783 : Blo 587289 589783 := bstep (se 1 (by rfl) ⟨442337, by rfl⟩ : syracuseStep 589783 = 884675) B884675
theorem B589803 : Blo 587289 589803 := bstep (se 1 (by rfl) ⟨442352, by rfl⟩ : syracuseStep 589803 = 884705) B884705
theorem B589815 : Blo 587289 589815 := bstep (se 1 (by rfl) ⟨442361, by rfl⟩ : syracuseStep 589815 = 884723) B884723
theorem B589831 : Blo 587289 589831 := bstep (se 1 (by rfl) ⟨442373, by rfl⟩ : syracuseStep 589831 = 884747) B884747
theorem B589839 : Blo 587289 589839 := bstep (se 1 (by rfl) ⟨442379, by rfl⟩ : syracuseStep 589839 = 884759) B884759
theorem B884795 : Blo 587289 884795 := bstep (se 1 (by rfl) ⟨663596, by rfl⟩ : syracuseStep 884795 = 1327193) B1327193
theorem B589883 : Blo 587289 589883 := bstep (se 1 (by rfl) ⟨442412, by rfl⟩ : syracuseStep 589883 = 884825) B884825
theorem B884855 : Blo 587289 884855 := bstep (se 1 (by rfl) ⟨663641, by rfl⟩ : syracuseStep 884855 = 1327283) B1327283
theorem B589959 : Blo 587289 589959 := bstep (se 1 (by rfl) ⟨442469, by rfl⟩ : syracuseStep 589959 = 884939) B884939
theorem B884879 : Blo 587289 884879 := bstep (se 1 (by rfl) ⟨663659, by rfl⟩ : syracuseStep 884879 = 1327319) B1327319
theorem B589967 : Blo 587289 589967 := bstep (se 1 (by rfl) ⟨442475, by rfl⟩ : syracuseStep 589967 = 884951) B884951
theorem B884921 : Blo 587289 884921 := bstep (se 2 (by rfl) ⟨331845, by rfl⟩ : syracuseStep 884921 = 663691) B663691
theorem B590011 : Blo 587289 590011 := bstep (se 1 (by rfl) ⟨442508, by rfl⟩ : syracuseStep 590011 = 885017) B885017
theorem B1868033 : Blo 587289 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B884999 : Blo 587289 884999 := bstep (se 1 (by rfl) ⟨663749, by rfl⟩ : syracuseStep 884999 = 1327499) B1327499
theorem B590087 : Blo 587289 590087 := bstep (se 1 (by rfl) ⟨442565, by rfl⟩ : syracuseStep 590087 = 885131) B885131
theorem B590095 : Blo 587289 590095 := bstep (se 1 (by rfl) ⟨442571, by rfl⟩ : syracuseStep 590095 = 885143) B885143
theorem B7143713 : Blo 587289 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B885035 : Blo 587289 885035 := bstep (se 1 (by rfl) ⟨663776, by rfl⟩ : syracuseStep 885035 = 1327553) B1327553
theorem B590139 : Blo 587289 590139 := bstep (se 1 (by rfl) ⟨442604, by rfl⟩ : syracuseStep 590139 = 885209) B885209
theorem B885065 : Blo 587289 885065 := bstep (se 2 (by rfl) ⟨331899, by rfl⟩ : syracuseStep 885065 = 663799) B663799
theorem B590215 : Blo 587289 590215 := bstep (se 1 (by rfl) ⟨442661, by rfl⟩ : syracuseStep 590215 = 885323) B885323
theorem B590223 : Blo 587289 590223 := bstep (se 1 (by rfl) ⟨442667, by rfl⟩ : syracuseStep 590223 = 885335) B885335
theorem B885179 : Blo 587289 885179 := bstep (se 1 (by rfl) ⟨663884, by rfl⟩ : syracuseStep 885179 = 1327769) B1327769
theorem B590267 : Blo 587289 590267 := bstep (se 1 (by rfl) ⟨442700, by rfl⟩ : syracuseStep 590267 = 885401) B885401
theorem B885239 : Blo 587289 885239 := bstep (se 1 (by rfl) ⟨663929, by rfl⟩ : syracuseStep 885239 = 1327859) B1327859
theorem B590343 : Blo 587289 590343 := bstep (se 1 (by rfl) ⟨442757, by rfl⟩ : syracuseStep 590343 = 885515) B885515
theorem B885263 : Blo 587289 885263 := bstep (se 1 (by rfl) ⟨663947, by rfl⟩ : syracuseStep 885263 = 1327895) B1327895
theorem B590351 : Blo 587289 590351 := bstep (se 1 (by rfl) ⟨442763, by rfl⟩ : syracuseStep 590351 = 885527) B885527
theorem B29000213 : Blo 587289 29000213 := bstep (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) B1359385
theorem B754219 : Blo 587289 754219 := bstep (se 1 (by rfl) ⟨565664, by rfl⟩ : syracuseStep 754219 = 1131329) B1131329
theorem B885305 : Blo 587289 885305 := bstep (se 2 (by rfl) ⟨331989, by rfl⟩ : syracuseStep 885305 = 663979) B663979
theorem B590395 : Blo 587289 590395 := bstep (se 1 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 590395 = 885593) B885593
theorem B885383 : Blo 587289 885383 := bstep (se 1 (by rfl) ⟨664037, by rfl⟩ : syracuseStep 885383 = 1328075) B1328075
theorem B590471 : Blo 587289 590471 := bstep (se 1 (by rfl) ⟨442853, by rfl⟩ : syracuseStep 590471 = 885707) B885707
theorem B590479 : Blo 587289 590479 := bstep (se 1 (by rfl) ⟨442859, by rfl⟩ : syracuseStep 590479 = 885719) B885719
theorem B885419 : Blo 587289 885419 := bstep (se 1 (by rfl) ⟨664064, by rfl⟩ : syracuseStep 885419 = 1328129) B1328129
theorem B590523 : Blo 587289 590523 := bstep (se 1 (by rfl) ⟨442892, by rfl⟩ : syracuseStep 590523 = 885785) B885785
theorem B885449 : Blo 587289 885449 := bstep (se 2 (by rfl) ⟨332043, by rfl⟩ : syracuseStep 885449 = 664087) B664087
theorem B590599 : Blo 587289 590599 := bstep (se 1 (by rfl) ⟨442949, by rfl⟩ : syracuseStep 590599 = 885899) B885899
theorem B1508107 : Blo 587289 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B590607 : Blo 587289 590607 := bstep (se 1 (by rfl) ⟨442955, by rfl⟩ : syracuseStep 590607 = 885911) B885911
theorem B2523919 : Blo 587289 2523919 := bstep (se 1 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 2523919 = 3785879) B3785879
theorem B885563 : Blo 587289 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B590651 : Blo 587289 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B885623 : Blo 587289 885623 := bstep (se 1 (by rfl) ⟨664217, by rfl⟩ : syracuseStep 885623 = 1328435) B1328435
theorem B590727 : Blo 587289 590727 := bstep (se 1 (by rfl) ⟨443045, by rfl⟩ : syracuseStep 590727 = 886091) B886091
theorem B885647 : Blo 587289 885647 := bstep (se 1 (by rfl) ⟨664235, by rfl⟩ : syracuseStep 885647 = 1328471) B1328471
theorem B590735 : Blo 587289 590735 := bstep (se 1 (by rfl) ⟨443051, by rfl⟩ : syracuseStep 590735 = 886103) B886103
theorem B5669783 : Blo 587289 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B885689 : Blo 587289 885689 := bstep (se 2 (by rfl) ⟨332133, by rfl⟩ : syracuseStep 885689 = 664267) B664267
theorem B590779 : Blo 587289 590779 := bstep (se 1 (by rfl) ⟨443084, by rfl⟩ : syracuseStep 590779 = 886169) B886169
theorem B885767 : Blo 587289 885767 := bstep (se 1 (by rfl) ⟨664325, by rfl⟩ : syracuseStep 885767 = 1328651) B1328651
theorem B590855 : Blo 587289 590855 := bstep (se 1 (by rfl) ⟨443141, by rfl⟩ : syracuseStep 590855 = 886283) B886283
theorem B590863 : Blo 587289 590863 := bstep (se 1 (by rfl) ⟨443147, by rfl⟩ : syracuseStep 590863 = 886295) B886295
theorem B885803 : Blo 587289 885803 := bstep (se 1 (by rfl) ⟨664352, by rfl⟩ : syracuseStep 885803 = 1328705) B1328705
theorem B590907 : Blo 587289 590907 := bstep (se 1 (by rfl) ⟨443180, by rfl⟩ : syracuseStep 590907 = 886361) B886361
theorem B885833 : Blo 587289 885833 := bstep (se 2 (by rfl) ⟨332187, by rfl⟩ : syracuseStep 885833 = 664375) B664375
theorem B3015767 : Blo 587289 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B590983 : Blo 587289 590983 := bstep (se 1 (by rfl) ⟨443237, by rfl⟩ : syracuseStep 590983 = 886475) B886475
theorem B590991 : Blo 587289 590991 := bstep (se 1 (by rfl) ⟨443243, by rfl⟩ : syracuseStep 590991 = 886487) B886487
theorem B885947 : Blo 587289 885947 := bstep (se 1 (by rfl) ⟨664460, by rfl⟩ : syracuseStep 885947 = 1328921) B1328921
theorem B591035 : Blo 587289 591035 := bstep (se 1 (by rfl) ⟨443276, by rfl⟩ : syracuseStep 591035 = 886553) B886553
theorem B886007 : Blo 587289 886007 := bstep (se 1 (by rfl) ⟨664505, by rfl⟩ : syracuseStep 886007 = 1329011) B1329011
theorem B591111 : Blo 587289 591111 := bstep (se 1 (by rfl) ⟨443333, by rfl⟩ : syracuseStep 591111 = 886667) B886667
theorem B1672463 : Blo 587289 1672463 := bstep (se 1 (by rfl) ⟨1254347, by rfl⟩ : syracuseStep 1672463 = 2508695) B2508695
theorem B886031 : Blo 587289 886031 := bstep (se 1 (by rfl) ⟨664523, by rfl⟩ : syracuseStep 886031 = 1329047) B1329047
theorem B591119 : Blo 587289 591119 := bstep (se 1 (by rfl) ⟨443339, by rfl⟩ : syracuseStep 591119 = 886679) B886679
theorem B886073 : Blo 587289 886073 := bstep (se 2 (by rfl) ⟨332277, by rfl⟩ : syracuseStep 886073 = 664555) B664555
theorem B591163 : Blo 587289 591163 := bstep (se 1 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 591163 = 886745) B886745
theorem B6391133 : Blo 587289 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B3835271 : Blo 587289 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B886151 : Blo 587289 886151 := bstep (se 1 (by rfl) ⟨664613, by rfl⟩ : syracuseStep 886151 = 1329227) B1329227
theorem B591239 : Blo 587289 591239 := bstep (se 1 (by rfl) ⟨443429, by rfl⟩ : syracuseStep 591239 = 886859) B886859
theorem B591247 : Blo 587289 591247 := bstep (se 1 (by rfl) ⟨443435, by rfl⟩ : syracuseStep 591247 = 886871) B886871
theorem B2393497 : Blo 587289 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B886187 : Blo 587289 886187 := bstep (se 1 (by rfl) ⟨664640, by rfl⟩ : syracuseStep 886187 = 1329281) B1329281
theorem B886217 : Blo 587289 886217 := bstep (se 2 (by rfl) ⟨332331, by rfl⟩ : syracuseStep 886217 = 664663) B664663
theorem B886331 : Blo 587289 886331 := bstep (se 1 (by rfl) ⟨664748, by rfl⟩ : syracuseStep 886331 = 1329497) B1329497
theorem B1508951 : Blo 587289 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B886391 : Blo 587289 886391 := bstep (se 1 (by rfl) ⟨664793, by rfl⟩ : syracuseStep 886391 = 1329587) B1329587
theorem B886415 : Blo 587289 886415 := bstep (se 1 (by rfl) ⟨664811, by rfl⟩ : syracuseStep 886415 = 1329623) B1329623
theorem B1115795 : Blo 587289 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B886457 : Blo 587289 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B1115849 : Blo 587289 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B886535 : Blo 587289 886535 := bstep (se 1 (by rfl) ⟨664901, by rfl⟩ : syracuseStep 886535 = 1329803) B1329803
theorem B1115947 : Blo 587289 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B886571 : Blo 587289 886571 := bstep (se 1 (by rfl) ⟨664928, by rfl⟩ : syracuseStep 886571 = 1329857) B1329857
theorem B886601 : Blo 587289 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B2230163 : Blo 587289 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B886715 : Blo 587289 886715 := bstep (se 1 (by rfl) ⟨665036, by rfl⟩ : syracuseStep 886715 = 1330073) B1330073
theorem B886775 : Blo 587289 886775 := bstep (se 1 (by rfl) ⟨665081, by rfl⟩ : syracuseStep 886775 = 1330163) B1330163
theorem B1116175 : Blo 587289 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B886799 : Blo 587289 886799 := bstep (se 1 (by rfl) ⟨665099, by rfl⟩ : syracuseStep 886799 = 1330199) B1330199
theorem B886841 : Blo 587289 886841 := bstep (se 2 (by rfl) ⟨332565, by rfl⟩ : syracuseStep 886841 = 665131) B665131
theorem B886919 : Blo 587289 886919 := bstep (se 1 (by rfl) ⟨665189, by rfl⟩ : syracuseStep 886919 = 1330379) B1330379
theorem B1509691 : Blo 587289 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B2525575 : Blo 587289 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B3770833 : Blo 587289 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1673875 : Blo 587289 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B1346233 : Blo 587289 1346233 := bstep (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) B1009675
theorem B1674103 : Blo 587289 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B2984849 : Blo 587289 2984849 := bstep (se 2 (by rfl) ⟨1119318, by rfl⟩ : syracuseStep 2984849 = 2238637) B2238637
theorem B2231819 : Blo 587289 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B1117739 : Blo 587289 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B1609591 : Blo 587289 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B1347475 : Blo 587289 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1413121 : Blo 587289 1413121 := bstep (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) B1059841
theorem B1413179 : Blo 587289 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B1675379 : Blo 587289 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B3346703 : Blo 587289 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B1511723 : Blo 587289 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B108532061 : Blo 587289 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B1675721 : Blo 587289 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B25498097 : Blo 587289 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B1675835 : Blo 587289 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B1675961 : Blo 587289 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B4789007 : Blo 587289 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1413947 : Blo 587289 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B2986955 : Blo 587289 2986955 := bstep (se 1 (by rfl) ⟨2240216, by rfl⟩ : syracuseStep 2986955 = 4480433) B4480433
theorem B1512583 : Blo 587289 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B1119433 : Blo 587289 1119433 := bstep (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) B839575
theorem B2987279 : Blo 587289 2987279 := bstep (se 1 (by rfl) ⟨2240459, by rfl⟩ : syracuseStep 2987279 = 4480919) B4480919
theorem B1611037 : Blo 587289 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B661135 : Blo 587289 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B3348161 : Blo 587289 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B5019407 : Blo 587289 5019407 := bstep (se 1 (by rfl) ⟨3764555, by rfl⟩ : syracuseStep 5019407 = 7529111) B7529111
theorem B22714181 : Blo 587289 22714181 := bstep (se 4 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 22714181 = 4258909) B4258909
theorem B4462451 : Blo 587289 4462451 := bstep (se 1 (by rfl) ⟨3346838, by rfl⟩ : syracuseStep 4462451 = 6693677) B6693677
theorem B661639 : Blo 587289 661639 := bstep (se 1 (by rfl) ⟨496229, by rfl⟩ : syracuseStep 661639 = 992459) B992459
theorem B1677611 : Blo 587289 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B661819 : Blo 587289 661819 := bstep (se 1 (by rfl) ⟨496364, by rfl⟩ : syracuseStep 661819 = 992729) B992729
theorem B2988737 : Blo 587289 2988737 := bstep (se 2 (by rfl) ⟨1120776, by rfl⟩ : syracuseStep 2988737 = 2241553) B2241553
theorem B662287 : Blo 587289 662287 := bstep (se 1 (by rfl) ⟨496715, by rfl⟩ : syracuseStep 662287 = 993431) B993431
theorem B4037579 : Blo 587289 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B1121339 : Blo 587289 1121339 := bstep (se 1 (by rfl) ⟨841004, by rfl⟩ : syracuseStep 1121339 = 1682009) B1682009
theorem B5020805 : Blo 587289 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B662791 : Blo 587289 662791 := bstep (se 1 (by rfl) ⟨497093, by rfl⟩ : syracuseStep 662791 = 994187) B994187
theorem B630023 : Blo 587289 630023 := bstep (se 1 (by rfl) ⟨472517, by rfl⟩ : syracuseStep 630023 = 945035) B945035
theorem B1678603 : Blo 587289 1678603 := bstep (se 1 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 1678603 = 2517905) B2517905
theorem B2235707 : Blo 587289 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B662971 : Blo 587289 662971 := bstep (se 1 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 662971 = 994457) B994457
theorem B1678877 : Blo 587289 1678877 := bstep (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) B629579
theorem B1121825 : Blo 587289 1121825 := bstep (se 2 (by rfl) ⟨420684, by rfl⟩ : syracuseStep 1121825 = 841369) B841369
theorem B5447425 : Blo 587289 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B2236193 : Blo 587289 2236193 := bstep (se 2 (by rfl) ⟨838572, by rfl⟩ : syracuseStep 2236193 = 1677145) B1677145
theorem B5119793 : Blo 587289 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B1122167 : Blo 587289 1122167 := bstep (se 1 (by rfl) ⟨841625, by rfl⟩ : syracuseStep 1122167 = 1683251) B1683251
theorem B663439 : Blo 587289 663439 := bstep (se 1 (by rfl) ⟨497579, by rfl⟩ : syracuseStep 663439 = 995159) B995159
theorem B2990033 : Blo 587289 2990033 := bstep (se 2 (by rfl) ⟨1121262, by rfl⟩ : syracuseStep 2990033 = 2242525) B2242525
theorem B991291 : Blo 587289 991291 := bstep (se 1 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 991291 = 1486937) B1486937
theorem B1417331 : Blo 587289 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B1417351 : Blo 587289 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B991433 : Blo 587289 991433 := bstep (se 2 (by rfl) ⟨371787, by rfl⟩ : syracuseStep 991433 = 743575) B743575
theorem B663943 : Blo 587289 663943 := bstep (se 1 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 663943 = 995915) B995915
theorem B16097777 : Blo 587289 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B664123 : Blo 587289 664123 := bstep (se 1 (by rfl) ⟨498092, by rfl⟩ : syracuseStep 664123 = 996185) B996185
theorem B2237165 : Blo 587289 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B992135 : Blo 587289 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B664591 : Blo 587289 664591 := bstep (se 1 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 664591 = 996887) B996887
theorem B2237483 : Blo 587289 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B3024263 : Blo 587289 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B2827723 : Blo 587289 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B665095 : Blo 587289 665095 := bstep (se 1 (by rfl) ⟨498821, by rfl⟩ : syracuseStep 665095 = 997643) B997643
theorem B992783 : Blo 587289 992783 := bstep (se 1 (by rfl) ⟨744587, by rfl⟩ : syracuseStep 992783 = 1489175) B1489175
theorem B6727211 : Blo 587289 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B1680983 : Blo 587289 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B1255031 : Blo 587289 1255031 := bstep (se 1 (by rfl) ⟨941273, by rfl⟩ : syracuseStep 1255031 = 1882547) B1882547
theorem B1681211 : Blo 587289 1681211 := bstep (se 1 (by rfl) ⟨1260908, by rfl⟩ : syracuseStep 1681211 = 2521817) B2521817
theorem B1681337 : Blo 587289 1681337 := bstep (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) B1261003
theorem B2992139 : Blo 587289 2992139 := bstep (se 1 (by rfl) ⟨2244104, by rfl⟩ : syracuseStep 2992139 = 4488209) B4488209
theorem B993323 : Blo 587289 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B6367349 : Blo 587289 6367349 := bstep (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) B596939
theorem B3188909 : Blo 587289 3188909 := bstep (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) B1195841
theorem B2992301 : Blo 587289 2992301 := bstep (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) B1122113
theorem B993721 : Blo 587289 993721 := bstep (se 2 (by rfl) ⟨372645, by rfl⟩ : syracuseStep 993721 = 745291) B745291
theorem B3353035 : Blo 587289 3353035 := bstep (se 1 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 3353035 = 5029553) B5029553
theorem B6040067 : Blo 587289 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B1321487 : Blo 587289 1321487 := bstep (se 1 (by rfl) ⟨991115, by rfl⟩ : syracuseStep 1321487 = 1982231) B1982231
theorem B1321505 : Blo 587289 1321505 := bstep (se 2 (by rfl) ⟨495564, by rfl⟩ : syracuseStep 1321505 = 991129) B991129
theorem B797303 : Blo 587289 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B9186085 : Blo 587289 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1321847 : Blo 587289 1321847 := bstep (se 1 (by rfl) ⟨991385, by rfl⟩ : syracuseStep 1321847 = 1982771) B1982771
theorem B11447203 : Blo 587289 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1322027 : Blo 587289 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B994423 : Blo 587289 994423 := bstep (se 1 (by rfl) ⟨745817, by rfl⟩ : syracuseStep 994423 = 1491635) B1491635
theorem B994619 : Blo 587289 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B1322387 : Blo 587289 1322387 := bstep (se 1 (by rfl) ⟨991790, by rfl⟩ : syracuseStep 1322387 = 1983581) B1983581
theorem B1322441 : Blo 587289 1322441 := bstep (se 2 (by rfl) ⟨495915, by rfl⟩ : syracuseStep 1322441 = 991831) B991831
theorem B1682977 : Blo 587289 1682977 := bstep (se 2 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 1682977 = 1262233) B1262233
theorem B3583531 : Blo 587289 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B3780215 : Blo 587289 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B995017 : Blo 587289 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B1486745 : Blo 587289 1486745 := bstep (se 2 (by rfl) ⟨557529, by rfl⟩ : syracuseStep 1486745 = 1115059) B1115059
theorem B1683467 : Blo 587289 1683467 := bstep (se 1 (by rfl) ⟨1262600, by rfl⟩ : syracuseStep 1683467 = 2525201) B2525201
theorem B1486907 : Blo 587289 1486907 := bstep (se 1 (by rfl) ⟨1115180, by rfl⟩ : syracuseStep 1486907 = 2230361) B2230361
theorem B1323143 : Blo 587289 1323143 := bstep (se 1 (by rfl) ⟨992357, by rfl⟩ : syracuseStep 1323143 = 1984715) B1984715
theorem B1487119 : Blo 587289 1487119 := bstep (se 1 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 1487119 = 2230679) B2230679
theorem B799033 : Blo 587289 799033 := bstep (se 2 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 799033 = 599275) B599275
theorem B1323323 : Blo 587289 1323323 := bstep (se 1 (by rfl) ⟨992492, by rfl⟩ : syracuseStep 1323323 = 1984985) B1984985
theorem B995719 : Blo 587289 995719 := bstep (se 1 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 995719 = 1493579) B1493579
theorem B1323449 : Blo 587289 1323449 := bstep (se 2 (by rfl) ⟨496293, by rfl⟩ : syracuseStep 1323449 = 992587) B992587
theorem B897551 : Blo 587289 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B2241053 : Blo 587289 2241053 := bstep (se 3 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 2241053 = 840395) B840395
theorem B1487393 : Blo 587289 1487393 := bstep (se 2 (by rfl) ⟨557772, by rfl⟩ : syracuseStep 1487393 = 1115545) B1115545
theorem B2241067 : Blo 587289 2241067 := bstep (se 1 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 2241067 = 3361601) B3361601
theorem B3781187 : Blo 587289 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B1323791 : Blo 587289 1323791 := bstep (se 1 (by rfl) ⟨992843, by rfl⟩ : syracuseStep 1323791 = 1985687) B1985687
theorem B1323809 : Blo 587289 1323809 := bstep (se 2 (by rfl) ⟨496428, by rfl⟩ : syracuseStep 1323809 = 992857) B992857
theorem B3355451 : Blo 587289 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B1192889 : Blo 587289 1192889 := bstep (se 2 (by rfl) ⟨447333, by rfl⟩ : syracuseStep 1192889 = 894667) B894667
theorem B799735 : Blo 587289 799735 := bstep (se 1 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 799735 = 1199603) B1199603
theorem B1061903 : Blo 587289 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B996367 : Blo 587289 996367 := bstep (se 1 (by rfl) ⟨747275, by rfl⟩ : syracuseStep 996367 = 1494551) B1494551
theorem B1324151 : Blo 587289 1324151 := bstep (se 1 (by rfl) ⟨993113, by rfl⟩ : syracuseStep 1324151 = 1986227) B1986227
theorem B1815671 : Blo 587289 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B898219 : Blo 587289 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B1324331 : Blo 587289 1324331 := bstep (se 1 (by rfl) ⟨993248, by rfl⟩ : syracuseStep 1324331 = 1986497) B1986497
theorem B5387705 : Blo 587289 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B1488395 : Blo 587289 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B996907 : Blo 587289 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B1324691 : Blo 587289 1324691 := bstep (se 1 (by rfl) ⟨993518, by rfl⟩ : syracuseStep 1324691 = 1987037) B1987037
theorem B997049 : Blo 587289 997049 := bstep (se 2 (by rfl) ⟨373893, by rfl⟩ : syracuseStep 997049 = 747787) B747787
theorem B1324745 : Blo 587289 1324745 := bstep (se 2 (by rfl) ⟨496779, by rfl⟩ : syracuseStep 1324745 = 993559) B993559
theorem B5748515 : Blo 587289 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B4241267 : Blo 587289 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B1489043 : Blo 587289 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1259705 : Blo 587289 1259705 := bstep (se 2 (by rfl) ⟨472389, by rfl⟩ : syracuseStep 1259705 = 944779) B944779
theorem B3356909 : Blo 587289 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B5028155 : Blo 587289 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B12925277 : Blo 587289 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B997751 : Blo 587289 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B1325447 : Blo 587289 1325447 := bstep (se 1 (by rfl) ⟨994085, by rfl⟩ : syracuseStep 1325447 = 1988171) B1988171
theorem B1063315 : Blo 587289 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1489337 : Blo 587289 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B9583069 : Blo 587289 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B3357227 : Blo 587289 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B1325627 : Blo 587289 1325627 := bstep (se 1 (by rfl) ⟨994220, by rfl⟩ : syracuseStep 1325627 = 1988441) B1988441
theorem B1325753 : Blo 587289 1325753 := bstep (se 2 (by rfl) ⟨497157, by rfl⟩ : syracuseStep 1325753 = 994315) B994315
theorem B1817387 : Blo 587289 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B932879 : Blo 587289 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B1326095 : Blo 587289 1326095 := bstep (se 1 (by rfl) ⟨994571, by rfl⟩ : syracuseStep 1326095 = 1989143) B1989143
theorem B1326113 : Blo 587289 1326113 := bstep (se 2 (by rfl) ⟨497292, by rfl⟩ : syracuseStep 1326113 = 994585) B994585
theorem B1490035 : Blo 587289 1490035 := bstep (se 1 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 1490035 = 2235053) B2235053
theorem B1490177 : Blo 587289 1490177 := bstep (se 2 (by rfl) ⟨558816, by rfl⟩ : syracuseStep 1490177 = 1117633) B1117633
theorem B1326455 : Blo 587289 1326455 := bstep (se 1 (by rfl) ⟨994841, by rfl⟩ : syracuseStep 1326455 = 1989683) B1989683
theorem B1326635 : Blo 587289 1326635 := bstep (se 1 (by rfl) ⟨994976, by rfl⟩ : syracuseStep 1326635 = 1989953) B1989953
theorem B1490633 : Blo 587289 1490633 := bstep (se 2 (by rfl) ⟨558987, by rfl⟩ : syracuseStep 1490633 = 1117975) B1117975
theorem B1261345 : Blo 587289 1261345 := bstep (se 2 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 1261345 = 946009) B946009
theorem B1326995 : Blo 587289 1326995 := bstep (se 1 (by rfl) ⟨995246, by rfl⟩ : syracuseStep 1326995 = 1990493) B1990493
theorem B1982393 : Blo 587289 1982393 := bstep (se 2 (by rfl) ⟨743397, by rfl⟩ : syracuseStep 1982393 = 1486795) B1486795
theorem B1327049 : Blo 587289 1327049 := bstep (se 2 (by rfl) ⟨497643, by rfl⟩ : syracuseStep 1327049 = 995287) B995287
theorem B3358685 : Blo 587289 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1490987 : Blo 587289 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B1589395 : Blo 587289 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B3784877 : Blo 587289 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B12927221 : Blo 587289 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B1982987 : Blo 587289 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B1983095 : Blo 587289 1983095 := bstep (se 1 (by rfl) ⟨1487321, by rfl⟩ : syracuseStep 1983095 = 2974643) B2974643
theorem B1327751 : Blo 587289 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B1327931 : Blo 587289 1327931 := bstep (se 1 (by rfl) ⟨995948, by rfl⟩ : syracuseStep 1327931 = 1991897) B1991897
theorem B1262395 : Blo 587289 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B1328057 : Blo 587289 1328057 := bstep (se 2 (by rfl) ⟨498021, by rfl⟩ : syracuseStep 1328057 = 996043) B996043
theorem B1491979 : Blo 587289 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B5653637 : Blo 587289 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B1492121 : Blo 587289 1492121 := bstep (se 2 (by rfl) ⟨559545, by rfl⟩ : syracuseStep 1492121 = 1119091) B1119091
theorem B1983689 : Blo 587289 1983689 := bstep (se 2 (by rfl) ⟨743883, by rfl⟩ : syracuseStep 1983689 = 1487767) B1487767
theorem B1328399 : Blo 587289 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B1328417 : Blo 587289 1328417 := bstep (se 2 (by rfl) ⟨498156, by rfl⟩ : syracuseStep 1328417 = 996313) B996313
theorem B1492283 : Blo 587289 1492283 := bstep (se 1 (by rfl) ⟨1119212, by rfl⟩ : syracuseStep 1492283 = 2238425) B2238425
theorem B836983 : Blo 587289 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B4244957 : Blo 587289 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B5031467 : Blo 587289 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B1328759 : Blo 587289 1328759 := bstep (se 1 (by rfl) ⟨996569, by rfl⟩ : syracuseStep 1328759 = 1993139) B1993139
theorem B1492627 : Blo 587289 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B1492769 : Blo 587289 1492769 := bstep (se 2 (by rfl) ⟨559788, by rfl⟩ : syracuseStep 1492769 = 1119577) B1119577
theorem B1328939 : Blo 587289 1328939 := bstep (se 1 (by rfl) ⟨996704, by rfl⟩ : syracuseStep 1328939 = 1993409) B1993409
theorem B2148211 : Blo 587289 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1984391 : Blo 587289 1984391 := bstep (se 1 (by rfl) ⟨1488293, by rfl⟩ : syracuseStep 1984391 = 2976587) B2976587
theorem B1886237 : Blo 587289 1886237 := bstep (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) B707339
theorem B6473861 : Blo 587289 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B1329299 : Blo 587289 1329299 := bstep (se 1 (by rfl) ⟨996974, by rfl⟩ : syracuseStep 1329299 = 1993949) B1993949
theorem B1329353 : Blo 587289 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B1984769 : Blo 587289 1984769 := bstep (se 2 (by rfl) ⟨744288, by rfl⟩ : syracuseStep 1984769 = 1488577) B1488577
theorem B838031 : Blo 587289 838031 := bstep (se 1 (by rfl) ⟨628523, by rfl⟩ : syracuseStep 838031 = 1257047) B1257047
theorem B3361283 : Blo 587289 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B2148925 : Blo 587289 2148925 := bstep (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) B805847
theorem B2509379 : Blo 587289 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B838345 : Blo 587289 838345 := bstep (se 2 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 838345 = 628759) B628759
theorem B1493761 : Blo 587289 1493761 := bstep (se 2 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 1493761 = 1120321) B1120321
theorem B1592075 : Blo 587289 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1330055 : Blo 587289 1330055 := bstep (se 1 (by rfl) ⟨997541, by rfl⟩ : syracuseStep 1330055 = 1995083) B1995083
theorem B1985579 : Blo 587289 1985579 := bstep (se 1 (by rfl) ⟨1489184, by rfl⟩ : syracuseStep 1985579 = 2978369) B2978369
theorem B1330235 : Blo 587289 1330235 := bstep (se 1 (by rfl) ⟨997676, by rfl⟩ : syracuseStep 1330235 = 1995353) B1995353
theorem B1330361 : Blo 587289 1330361 := bstep (se 2 (by rfl) ⟨498885, by rfl⟩ : syracuseStep 1330361 = 997771) B997771
theorem B1494359 : Blo 587289 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B2116999 : Blo 587289 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1494571 : Blo 587289 1494571 := bstep (se 1 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 1494571 = 2241857) B2241857
theorem B10047077 : Blo 587289 10047077 := bstep (se 4 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 10047077 = 1883827) B1883827
theorem B1593017 : Blo 587289 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B1494713 : Blo 587289 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B1790039 : Blo 587289 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1986875 : Blo 587289 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B1888697 : Blo 587289 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B3396107 : Blo 587289 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B5722667 : Blo 587289 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B4477517 : Blo 587289 4477517 := bstep (se 3 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 4477517 = 1679069) B1679069
theorem B1790599 : Blo 587289 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B1495705 : Blo 587289 1495705 := bstep (se 2 (by rfl) ⟨560889, by rfl⟩ : syracuseStep 1495705 = 1121779) B1121779
theorem B4084481 : Blo 587289 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1987361 : Blo 587289 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1495867 : Blo 587289 1495867 := bstep (se 1 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 1495867 = 2243801) B2243801
theorem B1496009 : Blo 587289 1496009 := bstep (se 2 (by rfl) ⟨561003, by rfl⟩ : syracuseStep 1496009 = 1122007) B1122007
theorem B1496353 : Blo 587289 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B5363003 : Blo 587289 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B841033 : Blo 587289 841033 := bstep (se 2 (by rfl) ⟨315387, by rfl⟩ : syracuseStep 841033 = 630775) B630775
theorem B1987955 : Blo 587289 1987955 := bstep (se 1 (by rfl) ⟨1490966, by rfl⟩ : syracuseStep 1987955 = 2981933) B2981933
theorem B1889671 : Blo 587289 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B710203 : Blo 587289 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B2021267 : Blo 587289 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B6379721 : Blo 587289 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B743671 : Blo 587289 743671 := bstep (se 1 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 743671 = 1115507) B1115507
theorem B1595707 : Blo 587289 1595707 := bstep (se 1 (by rfl) ⟨1196780, by rfl⟩ : syracuseStep 1595707 = 2393561) B2393561
theorem B743995 : Blo 587289 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B940729 : Blo 587289 940729 := bstep (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) B705547
theorem B4479947 : Blo 587289 4479947 := bstep (se 1 (by rfl) ⟨3359960, by rfl⟩ : syracuseStep 4479947 = 6719921) B6719921
theorem B744491 : Blo 587289 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B3365975 : Blo 587289 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B744967 : Blo 587289 744967 := bstep (se 1 (by rfl) ⟨558725, by rfl⟩ : syracuseStep 744967 = 1117451) B1117451
theorem B941959 : Blo 587289 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B1990547 : Blo 587289 1990547 := bstep (se 1 (by rfl) ⟨1492910, by rfl⟩ : syracuseStep 1990547 = 2985821) B2985821
theorem B745463 : Blo 587289 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B14311541 : Blo 587289 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B745615 : Blo 587289 745615 := bstep (se 1 (by rfl) ⟨559211, by rfl⟩ : syracuseStep 745615 = 1118423) B1118423
theorem B745787 : Blo 587289 745787 := bstep (se 1 (by rfl) ⟨559340, by rfl⟩ : syracuseStep 745787 = 1118681) B1118681
theorem B2122307 : Blo 587289 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B1073935 : Blo 587289 1073935 := bstep (se 1 (by rfl) ⟨805451, by rfl⟩ : syracuseStep 1073935 = 1610903) B1610903
theorem B2122681 : Blo 587289 2122681 := bstep (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) B1592011
theorem B746759 : Blo 587289 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B1991951 : Blo 587289 1991951 := bstep (se 1 (by rfl) ⟨1493963, by rfl⟩ : syracuseStep 1991951 = 2987927) B2987927
theorem B2975129 : Blo 587289 2975129 := bstep (se 2 (by rfl) ⟨1115673, by rfl⟩ : syracuseStep 2975129 = 2231347) B2231347
theorem B1992221 : Blo 587289 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B45868619 : Blo 587289 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B910991 : Blo 587289 910991 := bstep (se 1 (by rfl) ⟨683243, by rfl⟩ : syracuseStep 910991 = 1366487) B1366487
theorem B747407 : Blo 587289 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B1435735 : Blo 587289 1435735 := bstep (se 1 (by rfl) ⟨1076801, by rfl⟩ : syracuseStep 1435735 = 2153603) B2153603
theorem B5040215 : Blo 587289 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B4253897 : Blo 587289 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B4778299 : Blo 587289 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B944759 : Blo 587289 944759 := bstep (se 1 (by rfl) ⟨708569, by rfl⟩ : syracuseStep 944759 = 1417139) B1417139
theorem B1797011 : Blo 587289 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1993625 : Blo 587289 1993625 := bstep (se 2 (by rfl) ⟨747609, by rfl⟩ : syracuseStep 1993625 = 1495219) B1495219
theorem B9956357 : Blo 587289 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B1994327 : Blo 587289 1994327 := bstep (se 1 (by rfl) ⟨1495745, by rfl⟩ : syracuseStep 1994327 = 2991491) B2991491
theorem B12906161 : Blo 587289 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B5369753 : Blo 587289 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B2977721 : Blo 587289 2977721 := bstep (se 2 (by rfl) ⟨1116645, by rfl⟩ : syracuseStep 2977721 = 2233291) B2233291
theorem B2125867 : Blo 587289 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B1994813 : Blo 587289 1994813 := bstep (se 3 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 1994813 = 748055) B748055
theorem B4485293 : Blo 587289 4485293 := bstep (se 3 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 4485293 = 1681985) B1681985
theorem B880955 : Blo 587289 880955 := bstep (se 1 (by rfl) ⟨660716, by rfl⟩ : syracuseStep 880955 = 1321433) B1321433
theorem B881015 : Blo 587289 881015 := bstep (se 1 (by rfl) ⟨660761, by rfl⟩ : syracuseStep 881015 = 1321523) B1321523
theorem B2388359 : Blo 587289 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B881039 : Blo 587289 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B2388371 : Blo 587289 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B9073043 : Blo 587289 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B881081 : Blo 587289 881081 := bstep (se 2 (by rfl) ⟨330405, by rfl⟩ : syracuseStep 881081 = 660811) B660811
theorem B881159 : Blo 587289 881159 := bstep (se 1 (by rfl) ⟨660869, by rfl⟩ : syracuseStep 881159 = 1321739) B1321739
theorem B881195 : Blo 587289 881195 := bstep (se 1 (by rfl) ⟨660896, by rfl⟩ : syracuseStep 881195 = 1321793) B1321793
theorem B881225 : Blo 587289 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B64713329 : Blo 587289 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B881339 : Blo 587289 881339 := bstep (se 1 (by rfl) ⟨661004, by rfl⟩ : syracuseStep 881339 = 1322009) B1322009
theorem B881399 : Blo 587289 881399 := bstep (se 1 (by rfl) ⟨661049, by rfl⟩ : syracuseStep 881399 = 1322099) B1322099
theorem B881423 : Blo 587289 881423 := bstep (se 1 (by rfl) ⟨661067, by rfl⟩ : syracuseStep 881423 = 1322135) B1322135
theorem B881465 : Blo 587289 881465 := bstep (se 2 (by rfl) ⟨330549, by rfl⟩ : syracuseStep 881465 = 661099) B661099
theorem B12743513 : Blo 587289 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B881543 : Blo 587289 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B881579 : Blo 587289 881579 := bstep (se 1 (by rfl) ⟨661184, by rfl⟩ : syracuseStep 881579 = 1322369) B1322369
theorem B881609 : Blo 587289 881609 := bstep (se 2 (by rfl) ⟨330603, by rfl⟩ : syracuseStep 881609 = 661207) B661207
theorem B881723 : Blo 587289 881723 := bstep (se 1 (by rfl) ⟨661292, by rfl⟩ : syracuseStep 881723 = 1322585) B1322585
theorem B881783 : Blo 587289 881783 := bstep (se 1 (by rfl) ⟨661337, by rfl⟩ : syracuseStep 881783 = 1322675) B1322675
theorem B881807 : Blo 587289 881807 := bstep (se 1 (by rfl) ⟨661355, by rfl⟩ : syracuseStep 881807 = 1322711) B1322711
theorem B881849 : Blo 587289 881849 := bstep (se 2 (by rfl) ⟨330693, by rfl⟩ : syracuseStep 881849 = 661387) B661387
theorem B2979017 : Blo 587289 2979017 := bstep (se 2 (by rfl) ⟨1117131, by rfl⟩ : syracuseStep 2979017 = 2234263) B2234263
theorem B881927 : Blo 587289 881927 := bstep (se 1 (by rfl) ⟨661445, by rfl⟩ : syracuseStep 881927 = 1322891) B1322891
theorem B8516897 : Blo 587289 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B881963 : Blo 587289 881963 := bstep (se 1 (by rfl) ⟨661472, by rfl⟩ : syracuseStep 881963 = 1322945) B1322945
theorem B881993 : Blo 587289 881993 := bstep (se 2 (by rfl) ⟨330747, by rfl⟩ : syracuseStep 881993 = 661495) B661495
theorem B882107 : Blo 587289 882107 := bstep (se 1 (by rfl) ⟨661580, by rfl⟩ : syracuseStep 882107 = 1323161) B1323161
theorem B882167 : Blo 587289 882167 := bstep (se 1 (by rfl) ⟨661625, by rfl⟩ : syracuseStep 882167 = 1323251) B1323251
theorem B882191 : Blo 587289 882191 := bstep (se 1 (by rfl) ⟨661643, by rfl⟩ : syracuseStep 882191 = 1323287) B1323287
theorem B882233 : Blo 587289 882233 := bstep (se 2 (by rfl) ⟨330837, by rfl⟩ : syracuseStep 882233 = 661675) B661675
theorem B587323 : Blo 587289 587323 := bstep (se 1 (by rfl) ⟨440492, by rfl⟩ : syracuseStep 587323 = 880985) B880985
theorem B23983685 : Blo 587289 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B587399 : Blo 587289 587399 := bstep (se 1 (by rfl) ⟨440549, by rfl⟩ : syracuseStep 587399 = 881099) B881099
theorem B882311 : Blo 587289 882311 := bstep (se 1 (by rfl) ⟨661733, by rfl⟩ : syracuseStep 882311 = 1323467) B1323467
theorem B587407 : Blo 587289 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B882347 : Blo 587289 882347 := bstep (se 1 (by rfl) ⟨661760, by rfl⟩ : syracuseStep 882347 = 1323521) B1323521
theorem B587451 : Blo 587289 587451 := bstep (se 1 (by rfl) ⟨440588, by rfl⟩ : syracuseStep 587451 = 881177) B881177
theorem B882377 : Blo 587289 882377 := bstep (se 2 (by rfl) ⟨330891, by rfl⟩ : syracuseStep 882377 = 661783) B661783
theorem B587527 : Blo 587289 587527 := bstep (se 1 (by rfl) ⟨440645, by rfl⟩ : syracuseStep 587527 = 881291) B881291
theorem B587535 : Blo 587289 587535 := bstep (se 1 (by rfl) ⟨440651, by rfl⟩ : syracuseStep 587535 = 881303) B881303
theorem B587579 : Blo 587289 587579 := bstep (se 1 (by rfl) ⟨440684, by rfl⟩ : syracuseStep 587579 = 881369) B881369
theorem B882491 : Blo 587289 882491 := bstep (se 1 (by rfl) ⟨661868, by rfl⟩ : syracuseStep 882491 = 1323737) B1323737
theorem B882551 : Blo 587289 882551 := bstep (se 1 (by rfl) ⟨661913, by rfl⟩ : syracuseStep 882551 = 1323827) B1323827
theorem B587655 : Blo 587289 587655 := bstep (se 1 (by rfl) ⟨440741, by rfl⟩ : syracuseStep 587655 = 881483) B881483
theorem B587663 : Blo 587289 587663 := bstep (se 1 (by rfl) ⟨440747, by rfl⟩ : syracuseStep 587663 = 881495) B881495
theorem B882575 : Blo 587289 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B882617 : Blo 587289 882617 := bstep (se 2 (by rfl) ⟨330981, by rfl⟩ : syracuseStep 882617 = 661963) B661963
theorem B587707 : Blo 587289 587707 := bstep (se 1 (by rfl) ⟨440780, by rfl⟩ : syracuseStep 587707 = 881561) B881561
theorem B587783 : Blo 587289 587783 := bstep (se 1 (by rfl) ⟨440837, by rfl⟩ : syracuseStep 587783 = 881675) B881675
theorem B882695 : Blo 587289 882695 := bstep (se 1 (by rfl) ⟨662021, by rfl⟩ : syracuseStep 882695 = 1324043) B1324043
theorem B587791 : Blo 587289 587791 := bstep (se 1 (by rfl) ⟨440843, by rfl⟩ : syracuseStep 587791 = 881687) B881687
theorem B882731 : Blo 587289 882731 := bstep (se 1 (by rfl) ⟨662048, by rfl⟩ : syracuseStep 882731 = 1324097) B1324097
theorem B587835 : Blo 587289 587835 := bstep (se 1 (by rfl) ⟨440876, by rfl⟩ : syracuseStep 587835 = 881753) B881753
theorem B882761 : Blo 587289 882761 := bstep (se 2 (by rfl) ⟨331035, by rfl⟩ : syracuseStep 882761 = 662071) B662071
theorem B587911 : Blo 587289 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B587919 : Blo 587289 587919 := bstep (se 1 (by rfl) ⟨440939, by rfl⟩ : syracuseStep 587919 = 881879) B881879
theorem B587963 : Blo 587289 587963 := bstep (se 1 (by rfl) ⟨440972, by rfl⟩ : syracuseStep 587963 = 881945) B881945
theorem B882875 : Blo 587289 882875 := bstep (se 1 (by rfl) ⟨662156, by rfl⟩ : syracuseStep 882875 = 1324313) B1324313
theorem B719035 : Blo 587289 719035 := bstep (se 1 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 719035 = 1078553) B1078553
theorem B882935 : Blo 587289 882935 := bstep (se 1 (by rfl) ⟨662201, by rfl⟩ : syracuseStep 882935 = 1324403) B1324403
theorem B588039 : Blo 587289 588039 := bstep (se 1 (by rfl) ⟨441029, by rfl⟩ : syracuseStep 588039 = 882059) B882059
theorem B588047 : Blo 587289 588047 := bstep (se 1 (by rfl) ⟨441035, by rfl⟩ : syracuseStep 588047 = 882071) B882071
theorem B882959 : Blo 587289 882959 := bstep (se 1 (by rfl) ⟨662219, by rfl⟩ : syracuseStep 882959 = 1324439) B1324439
theorem B883001 : Blo 587289 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B2128187 : Blo 587289 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B588091 : Blo 587289 588091 := bstep (se 1 (by rfl) ⟨441068, by rfl⟩ : syracuseStep 588091 = 882137) B882137
theorem B588167 : Blo 587289 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B883079 : Blo 587289 883079 := bstep (se 1 (by rfl) ⟨662309, by rfl⟩ : syracuseStep 883079 = 1324619) B1324619
theorem B588175 : Blo 587289 588175 := bstep (se 1 (by rfl) ⟨441131, by rfl⟩ : syracuseStep 588175 = 882263) B882263
theorem B883115 : Blo 587289 883115 := bstep (se 1 (by rfl) ⟨662336, by rfl⟩ : syracuseStep 883115 = 1324673) B1324673
theorem B588219 : Blo 587289 588219 := bstep (se 1 (by rfl) ⟨441164, by rfl⟩ : syracuseStep 588219 = 882329) B882329
theorem B883145 : Blo 587289 883145 := bstep (se 2 (by rfl) ⟨331179, by rfl⟩ : syracuseStep 883145 = 662359) B662359
theorem B588295 : Blo 587289 588295 := bstep (se 1 (by rfl) ⟨441221, by rfl⟩ : syracuseStep 588295 = 882443) B882443
theorem B588303 : Blo 587289 588303 := bstep (se 1 (by rfl) ⟨441227, by rfl⟩ : syracuseStep 588303 = 882455) B882455
theorem B4487723 : Blo 587289 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B588347 : Blo 587289 588347 := bstep (se 1 (by rfl) ⟨441260, by rfl⟩ : syracuseStep 588347 = 882521) B882521
theorem B883259 : Blo 587289 883259 := bstep (se 1 (by rfl) ⟨662444, by rfl⟩ : syracuseStep 883259 = 1324889) B1324889
theorem B883319 : Blo 587289 883319 := bstep (se 1 (by rfl) ⟨662489, by rfl⟩ : syracuseStep 883319 = 1324979) B1324979
theorem B588423 : Blo 587289 588423 := bstep (se 1 (by rfl) ⟨441317, by rfl⟩ : syracuseStep 588423 = 882635) B882635
theorem B588431 : Blo 587289 588431 := bstep (se 1 (by rfl) ⟨441323, by rfl⟩ : syracuseStep 588431 = 882647) B882647
theorem B883343 : Blo 587289 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B883385 : Blo 587289 883385 := bstep (se 2 (by rfl) ⟨331269, by rfl⟩ : syracuseStep 883385 = 662539) B662539
theorem B588475 : Blo 587289 588475 := bstep (se 1 (by rfl) ⟨441356, by rfl⟩ : syracuseStep 588475 = 882713) B882713
theorem B588551 : Blo 587289 588551 := bstep (se 1 (by rfl) ⟨441413, by rfl⟩ : syracuseStep 588551 = 882827) B882827
theorem B883463 : Blo 587289 883463 := bstep (se 1 (by rfl) ⟨662597, by rfl⟩ : syracuseStep 883463 = 1325195) B1325195
theorem B588559 : Blo 587289 588559 := bstep (se 1 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 588559 = 882839) B882839
theorem B883499 : Blo 587289 883499 := bstep (se 1 (by rfl) ⟨662624, by rfl⟩ : syracuseStep 883499 = 1325249) B1325249
theorem B588603 : Blo 587289 588603 := bstep (se 1 (by rfl) ⟨441452, by rfl⟩ : syracuseStep 588603 = 882905) B882905
theorem B883529 : Blo 587289 883529 := bstep (se 2 (by rfl) ⟨331323, by rfl⟩ : syracuseStep 883529 = 662647) B662647
theorem B588679 : Blo 587289 588679 := bstep (se 1 (by rfl) ⟨441509, by rfl⟩ : syracuseStep 588679 = 883019) B883019
theorem B588687 : Blo 587289 588687 := bstep (se 1 (by rfl) ⟨441515, by rfl⟩ : syracuseStep 588687 = 883031) B883031
theorem B588731 : Blo 587289 588731 := bstep (se 1 (by rfl) ⟨441548, by rfl⟩ : syracuseStep 588731 = 883097) B883097
theorem B883643 : Blo 587289 883643 := bstep (se 1 (by rfl) ⟨662732, by rfl⟩ : syracuseStep 883643 = 1325465) B1325465
theorem B883703 : Blo 587289 883703 := bstep (se 1 (by rfl) ⟨662777, by rfl⟩ : syracuseStep 883703 = 1325555) B1325555
theorem B588807 : Blo 587289 588807 := bstep (se 1 (by rfl) ⟨441605, by rfl⟩ : syracuseStep 588807 = 883211) B883211
theorem B588815 : Blo 587289 588815 := bstep (se 1 (by rfl) ⟨441611, by rfl⟩ : syracuseStep 588815 = 883223) B883223
theorem B883727 : Blo 587289 883727 := bstep (se 1 (by rfl) ⟨662795, by rfl⟩ : syracuseStep 883727 = 1325591) B1325591
theorem B883769 : Blo 587289 883769 := bstep (se 2 (by rfl) ⟨331413, by rfl⟩ : syracuseStep 883769 = 662827) B662827
theorem B588859 : Blo 587289 588859 := bstep (se 1 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 588859 = 883289) B883289
theorem B588935 : Blo 587289 588935 := bstep (se 1 (by rfl) ⟨441701, by rfl⟩ : syracuseStep 588935 = 883403) B883403
theorem B883847 : Blo 587289 883847 := bstep (se 1 (by rfl) ⟨662885, by rfl⟩ : syracuseStep 883847 = 1325771) B1325771
theorem B588943 : Blo 587289 588943 := bstep (se 1 (by rfl) ⟨441707, by rfl⟩ : syracuseStep 588943 = 883415) B883415
theorem B883883 : Blo 587289 883883 := bstep (se 1 (by rfl) ⟨662912, by rfl⟩ : syracuseStep 883883 = 1325825) B1325825
theorem B588987 : Blo 587289 588987 := bstep (se 1 (by rfl) ⟨441740, by rfl⟩ : syracuseStep 588987 = 883481) B883481
theorem B883913 : Blo 587289 883913 := bstep (se 2 (by rfl) ⟨331467, by rfl⟩ : syracuseStep 883913 = 662935) B662935
theorem B589063 : Blo 587289 589063 := bstep (se 1 (by rfl) ⟨441797, by rfl⟩ : syracuseStep 589063 = 883595) B883595
theorem B589071 : Blo 587289 589071 := bstep (se 1 (by rfl) ⟨441803, by rfl⟩ : syracuseStep 589071 = 883607) B883607
theorem B589115 : Blo 587289 589115 := bstep (se 1 (by rfl) ⟨441836, by rfl⟩ : syracuseStep 589115 = 883673) B883673
theorem B884027 : Blo 587289 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B884087 : Blo 587289 884087 := bstep (se 1 (by rfl) ⟨663065, by rfl⟩ : syracuseStep 884087 = 1326131) B1326131
theorem B589191 : Blo 587289 589191 := bstep (se 1 (by rfl) ⟨441893, by rfl⟩ : syracuseStep 589191 = 883787) B883787
theorem B589199 : Blo 587289 589199 := bstep (se 1 (by rfl) ⟨441899, by rfl⟩ : syracuseStep 589199 = 883799) B883799
theorem B884111 : Blo 587289 884111 := bstep (se 1 (by rfl) ⟨663083, by rfl⟩ : syracuseStep 884111 = 1326167) B1326167
theorem B5045651 : Blo 587289 5045651 := bstep (se 1 (by rfl) ⟨3784238, by rfl⟩ : syracuseStep 5045651 = 7568477) B7568477
theorem B884153 : Blo 587289 884153 := bstep (se 2 (by rfl) ⟨331557, by rfl⟩ : syracuseStep 884153 = 663115) B663115
theorem B589243 : Blo 587289 589243 := bstep (se 1 (by rfl) ⟨441932, by rfl⟩ : syracuseStep 589243 = 883865) B883865
theorem B851401 : Blo 587289 851401 := bstep (se 2 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 851401 = 638551) B638551
theorem B589319 : Blo 587289 589319 := bstep (se 1 (by rfl) ⟨441989, by rfl⟩ : syracuseStep 589319 = 883979) B883979
theorem B884231 : Blo 587289 884231 := bstep (se 1 (by rfl) ⟨663173, by rfl⟩ : syracuseStep 884231 = 1326347) B1326347
theorem B589327 : Blo 587289 589327 := bstep (se 1 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 589327 = 883991) B883991
theorem B884267 : Blo 587289 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B589371 : Blo 587289 589371 := bstep (se 1 (by rfl) ⟨442028, by rfl⟩ : syracuseStep 589371 = 884057) B884057
theorem B884297 : Blo 587289 884297 := bstep (se 2 (by rfl) ⟨331611, by rfl⟩ : syracuseStep 884297 = 663223) B663223
theorem B6717005 : Blo 587289 6717005 := bstep (se 3 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 6717005 = 2518877) B2518877
theorem B589447 : Blo 587289 589447 := bstep (se 1 (by rfl) ⟨442085, by rfl⟩ : syracuseStep 589447 = 884171) B884171
theorem B589455 : Blo 587289 589455 := bstep (se 1 (by rfl) ⟨442091, by rfl⟩ : syracuseStep 589455 = 884183) B884183
theorem B589499 : Blo 587289 589499 := bstep (se 1 (by rfl) ⟨442124, by rfl⟩ : syracuseStep 589499 = 884249) B884249
theorem B884411 : Blo 587289 884411 := bstep (se 1 (by rfl) ⟨663308, by rfl⟩ : syracuseStep 884411 = 1326617) B1326617
theorem B884471 : Blo 587289 884471 := bstep (se 1 (by rfl) ⟨663353, by rfl⟩ : syracuseStep 884471 = 1326707) B1326707
theorem B3768065 : Blo 587289 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B589575 : Blo 587289 589575 := bstep (se 1 (by rfl) ⟨442181, by rfl⟩ : syracuseStep 589575 = 884363) B884363
theorem B589583 : Blo 587289 589583 := bstep (se 1 (by rfl) ⟨442187, by rfl⟩ : syracuseStep 589583 = 884375) B884375
theorem B884495 : Blo 587289 884495 := bstep (se 1 (by rfl) ⟨663371, by rfl⟩ : syracuseStep 884495 = 1326743) B1326743
theorem B884537 : Blo 587289 884537 := bstep (se 2 (by rfl) ⟨331701, by rfl⟩ : syracuseStep 884537 = 663403) B663403
theorem B589627 : Blo 587289 589627 := bstep (se 1 (by rfl) ⟨442220, by rfl⟩ : syracuseStep 589627 = 884441) B884441
theorem B589703 : Blo 587289 589703 := bstep (se 1 (by rfl) ⟨442277, by rfl⟩ : syracuseStep 589703 = 884555) B884555
theorem B884615 : Blo 587289 884615 := bstep (se 1 (by rfl) ⟨663461, by rfl⟩ : syracuseStep 884615 = 1326923) B1326923
theorem B589711 : Blo 587289 589711 := bstep (se 1 (by rfl) ⟨442283, by rfl⟩ : syracuseStep 589711 = 884567) B884567
theorem B884651 : Blo 587289 884651 := bstep (se 1 (by rfl) ⟨663488, by rfl⟩ : syracuseStep 884651 = 1326977) B1326977
theorem B589755 : Blo 587289 589755 := bstep (se 1 (by rfl) ⟨442316, by rfl⟩ : syracuseStep 589755 = 884633) B884633
theorem B884681 : Blo 587289 884681 := bstep (se 2 (by rfl) ⟨331755, by rfl⟩ : syracuseStep 884681 = 663511) B663511
theorem B589863 : Blo 587289 589863 := bstep (se 1 (by rfl) ⟨442397, by rfl⟩ : syracuseStep 589863 = 884795) B884795
theorem B589903 : Blo 587289 589903 := bstep (se 1 (by rfl) ⟨442427, by rfl⟩ : syracuseStep 589903 = 884855) B884855
theorem B589919 : Blo 587289 589919 := bstep (se 1 (by rfl) ⟨442439, by rfl⟩ : syracuseStep 589919 = 884879) B884879
theorem B2523251 : Blo 587289 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B589947 : Blo 587289 589947 := bstep (se 1 (by rfl) ⟨442460, by rfl⟩ : syracuseStep 589947 = 884921) B884921
theorem B8618147 : Blo 587289 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B589999 : Blo 587289 589999 := bstep (se 1 (by rfl) ⟨442499, by rfl⟩ : syracuseStep 589999 = 884999) B884999
theorem B590023 : Blo 587289 590023 := bstep (se 1 (by rfl) ⟨442517, by rfl⟩ : syracuseStep 590023 = 885035) B885035
theorem B590043 : Blo 587289 590043 := bstep (se 1 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 590043 = 885065) B885065
theorem B590119 : Blo 587289 590119 := bstep (se 1 (by rfl) ⟨442589, by rfl⟩ : syracuseStep 590119 = 885179) B885179
theorem B590159 : Blo 587289 590159 := bstep (se 1 (by rfl) ⟨442619, by rfl⟩ : syracuseStep 590159 = 885239) B885239
theorem B590175 : Blo 587289 590175 := bstep (se 1 (by rfl) ⟨442631, by rfl⟩ : syracuseStep 590175 = 885263) B885263
theorem B19333475 : Blo 587289 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B590203 : Blo 587289 590203 := bstep (se 1 (by rfl) ⟨442652, by rfl⟩ : syracuseStep 590203 = 885305) B885305
theorem B885167 : Blo 587289 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B590255 : Blo 587289 590255 := bstep (se 1 (by rfl) ⟨442691, by rfl⟩ : syracuseStep 590255 = 885383) B885383
theorem B590279 : Blo 587289 590279 := bstep (se 1 (by rfl) ⟨442709, by rfl⟩ : syracuseStep 590279 = 885419) B885419
theorem B590299 : Blo 587289 590299 := bstep (se 1 (by rfl) ⟨442724, by rfl⟩ : syracuseStep 590299 = 885449) B885449
theorem B885257 : Blo 587289 885257 := bstep (se 2 (by rfl) ⟨331971, by rfl⟩ : syracuseStep 885257 = 663943) B663943
theorem B885287 : Blo 587289 885287 := bstep (se 1 (by rfl) ⟨663965, by rfl⟩ : syracuseStep 885287 = 1327931) B1327931
theorem B590375 : Blo 587289 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B590415 : Blo 587289 590415 := bstep (se 1 (by rfl) ⟨442811, by rfl⟩ : syracuseStep 590415 = 885623) B885623
theorem B590431 : Blo 587289 590431 := bstep (se 1 (by rfl) ⟨442823, by rfl⟩ : syracuseStep 590431 = 885647) B885647
theorem B885371 : Blo 587289 885371 := bstep (se 1 (by rfl) ⟨664028, by rfl⟩ : syracuseStep 885371 = 1328057) B1328057
theorem B590459 : Blo 587289 590459 := bstep (se 1 (by rfl) ⟨442844, by rfl⟩ : syracuseStep 590459 = 885689) B885689
theorem B4981421 : Blo 587289 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B590511 : Blo 587289 590511 := bstep (se 1 (by rfl) ⟨442883, by rfl⟩ : syracuseStep 590511 = 885767) B885767
theorem B590535 : Blo 587289 590535 := bstep (se 1 (by rfl) ⟨442901, by rfl⟩ : syracuseStep 590535 = 885803) B885803
theorem B590555 : Blo 587289 590555 := bstep (se 1 (by rfl) ⟨442916, by rfl⟩ : syracuseStep 590555 = 885833) B885833
theorem B885497 : Blo 587289 885497 := bstep (se 2 (by rfl) ⟨332061, by rfl⟩ : syracuseStep 885497 = 664123) B664123
theorem B3769091 : Blo 587289 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B590631 : Blo 587289 590631 := bstep (se 1 (by rfl) ⟨442973, by rfl⟩ : syracuseStep 590631 = 885947) B885947
theorem B590671 : Blo 587289 590671 := bstep (se 1 (by rfl) ⟨443003, by rfl⟩ : syracuseStep 590671 = 886007) B886007
theorem B1114975 : Blo 587289 1114975 := bstep (se 1 (by rfl) ⟨836231, by rfl⟩ : syracuseStep 1114975 = 1672463) B1672463
theorem B885599 : Blo 587289 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B590687 : Blo 587289 590687 := bstep (se 1 (by rfl) ⟨443015, by rfl⟩ : syracuseStep 590687 = 886031) B886031
theorem B885611 : Blo 587289 885611 := bstep (se 1 (by rfl) ⟨664208, by rfl⟩ : syracuseStep 885611 = 1328417) B1328417
theorem B590715 : Blo 587289 590715 := bstep (se 1 (by rfl) ⟨443036, by rfl⟩ : syracuseStep 590715 = 886073) B886073
theorem B4260755 : Blo 587289 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B2556847 : Blo 587289 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B590767 : Blo 587289 590767 := bstep (se 1 (by rfl) ⟨443075, by rfl⟩ : syracuseStep 590767 = 886151) B886151
theorem B590791 : Blo 587289 590791 := bstep (se 1 (by rfl) ⟨443093, by rfl⟩ : syracuseStep 590791 = 886187) B886187
theorem B590811 : Blo 587289 590811 := bstep (se 1 (by rfl) ⟨443108, by rfl⟩ : syracuseStep 590811 = 886217) B886217
theorem B590887 : Blo 587289 590887 := bstep (se 1 (by rfl) ⟨443165, by rfl⟩ : syracuseStep 590887 = 886331) B886331
theorem B885839 : Blo 587289 885839 := bstep (se 1 (by rfl) ⟨664379, by rfl⟩ : syracuseStep 885839 = 1328759) B1328759
theorem B590927 : Blo 587289 590927 := bstep (se 1 (by rfl) ⟨443195, by rfl⟩ : syracuseStep 590927 = 886391) B886391
theorem B590943 : Blo 587289 590943 := bstep (se 1 (by rfl) ⟨443207, by rfl⟩ : syracuseStep 590943 = 886415) B886415
theorem B590971 : Blo 587289 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B591023 : Blo 587289 591023 := bstep (se 1 (by rfl) ⟨443267, by rfl⟩ : syracuseStep 591023 = 886535) B886535
theorem B885959 : Blo 587289 885959 := bstep (se 1 (by rfl) ⟨664469, by rfl⟩ : syracuseStep 885959 = 1328939) B1328939
theorem B591047 : Blo 587289 591047 := bstep (se 1 (by rfl) ⟨443285, by rfl⟩ : syracuseStep 591047 = 886571) B886571
theorem B591067 : Blo 587289 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B591143 : Blo 587289 591143 := bstep (se 1 (by rfl) ⟨443357, by rfl⟩ : syracuseStep 591143 = 886715) B886715
theorem B591183 : Blo 587289 591183 := bstep (se 1 (by rfl) ⟨443387, by rfl⟩ : syracuseStep 591183 = 886775) B886775
theorem B591199 : Blo 587289 591199 := bstep (se 1 (by rfl) ⟨443399, by rfl⟩ : syracuseStep 591199 = 886799) B886799
theorem B886121 : Blo 587289 886121 := bstep (se 2 (by rfl) ⟨332295, by rfl⟩ : syracuseStep 886121 = 664591) B664591
theorem B591227 : Blo 587289 591227 := bstep (se 1 (by rfl) ⟨443420, by rfl⟩ : syracuseStep 591227 = 886841) B886841
theorem B591279 : Blo 587289 591279 := bstep (se 1 (by rfl) ⟨443459, by rfl⟩ : syracuseStep 591279 = 886919) B886919
theorem B886199 : Blo 587289 886199 := bstep (se 1 (by rfl) ⟨664649, by rfl⟩ : syracuseStep 886199 = 1329299) B1329299
theorem B886235 : Blo 587289 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B1672919 : Blo 587289 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B886703 : Blo 587289 886703 := bstep (se 1 (by rfl) ⟨665027, by rfl⟩ : syracuseStep 886703 = 1330055) B1330055
theorem B3770297 : Blo 587289 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B886793 : Blo 587289 886793 := bstep (se 2 (by rfl) ⟨332547, by rfl⟩ : syracuseStep 886793 = 665095) B665095
theorem B886823 : Blo 587289 886823 := bstep (se 1 (by rfl) ⟨665117, by rfl⟩ : syracuseStep 886823 = 1330235) B1330235
theorem B886907 : Blo 587289 886907 := bstep (se 1 (by rfl) ⟨665180, by rfl⟩ : syracuseStep 886907 = 1330361) B1330361
theorem B3770525 : Blo 587289 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B1116919 : Blo 587289 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B2231135 : Blo 587289 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B72354707 : Blo 587289 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B1117147 : Blo 587289 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B1117223 : Blo 587289 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B2985011 : Blo 587289 2985011 := bstep (se 1 (by rfl) ⟨2238758, by rfl⟩ : syracuseStep 2985011 = 4477517) B4477517
theorem B1117307 : Blo 587289 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B2722987 : Blo 587289 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B2231833 : Blo 587289 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B3575335 : Blo 587289 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1117793 : Blo 587289 1117793 := bstep (se 2 (by rfl) ⟨419172, by rfl⟩ : syracuseStep 1117793 = 838345) B838345
theorem B2232107 : Blo 587289 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B2232137 : Blo 587289 2232137 := bstep (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) B1674103
theorem B3346271 : Blo 587289 3346271 := bstep (se 1 (by rfl) ⟨2509703, by rfl⟩ : syracuseStep 3346271 = 5019407) B5019407
theorem B15142787 : Blo 587289 15142787 := bstep (se 1 (by rfl) ⟨11357090, by rfl⟩ : syracuseStep 15142787 = 22714181) B22714181
theorem B15339413 : Blo 587289 15339413 := bstep (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) B719035
theorem B1347511 : Blo 587289 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2429309 : Blo 587289 2429309 := bstep (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) B910991
theorem B2986631 : Blo 587289 2986631 := bstep (se 1 (by rfl) ⟨2239973, by rfl⟩ : syracuseStep 2986631 = 4479947) B4479947
theorem B2691719 : Blo 587289 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B3347203 : Blo 587289 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B1119251 : Blo 587289 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B3413195 : Blo 587289 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B9541027 : Blo 587289 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B660955 : Blo 587289 660955 := bstep (se 1 (by rfl) ⟨495716, by rfl⟩ : syracuseStep 660955 = 991433) B991433
theorem B1414871 : Blo 587289 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B661423 : Blo 587289 661423 := bstep (se 1 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 661423 = 992135) B992135
theorem B8067109 : Blo 587289 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B2988089 : Blo 587289 2988089 := bstep (se 2 (by rfl) ⟨1120533, by rfl⟩ : syracuseStep 2988089 = 2241067) B2241067
theorem B4790501 : Blo 587289 4790501 := bstep (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) B898219
theorem B661855 : Blo 587289 661855 := bstep (se 1 (by rfl) ⟨496391, by rfl⟩ : syracuseStep 661855 = 992783) B992783
theorem B2234749 : Blo 587289 2234749 := bstep (se 3 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 2234749 = 838031) B838031
theorem B30579079 : Blo 587289 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B1120655 : Blo 587289 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B1120807 : Blo 587289 1120807 := bstep (se 1 (by rfl) ⟨840605, by rfl⟩ : syracuseStep 1120807 = 1681211) B1681211
theorem B1120891 : Blo 587289 1120891 := bstep (se 1 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 1120891 = 1681337) B1681337
theorem B662215 : Blo 587289 662215 := bstep (se 1 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 662215 = 993323) B993323
theorem B629839 : Blo 587289 629839 := bstep (se 1 (by rfl) ⟨472379, by rfl⟩ : syracuseStep 629839 = 944759) B944759
theorem B1121377 : Blo 587289 1121377 := bstep (se 2 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 1121377 = 841033) B841033
theorem B4463909 : Blo 587289 4463909 := bstep (se 4 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 4463909 = 836983) B836983
theorem B663079 : Blo 587289 663079 := bstep (se 1 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 663079 = 994619) B994619
theorem B991163 : Blo 587289 991163 := bstep (se 1 (by rfl) ⟨743372, by rfl⟩ : syracuseStep 991163 = 1486745) B1486745
theorem B3579835 : Blo 587289 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B1122311 : Blo 587289 1122311 := bstep (se 1 (by rfl) ⟨841733, by rfl⟩ : syracuseStep 1122311 = 1683467) B1683467
theorem B991271 : Blo 587289 991271 := bstep (se 1 (by rfl) ⟨743453, by rfl⟩ : syracuseStep 991271 = 1486907) B1486907
theorem B2990195 : Blo 587289 2990195 := bstep (se 1 (by rfl) ⟨2242646, by rfl⟩ : syracuseStep 2990195 = 4485293) B4485293
theorem B991561 : Blo 587289 991561 := bstep (se 2 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 991561 = 743671) B743671
theorem B598367 : Blo 587289 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B991595 : Blo 587289 991595 := bstep (se 1 (by rfl) ⟨743696, by rfl⟩ : syracuseStep 991595 = 1487393) B1487393
theorem B1417753 : Blo 587289 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B2236967 : Blo 587289 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B8495675 : Blo 587289 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B795259 : Blo 587289 795259 := bstep (se 1 (by rfl) ⟨596444, by rfl⟩ : syracuseStep 795259 = 1192889) B1192889
theorem B1680061 : Blo 587289 1680061 := bstep (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) B630023
theorem B991993 : Blo 587289 991993 := bstep (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) B743995
theorem B5677931 : Blo 587289 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B1254305 : Blo 587289 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B992263 : Blo 587289 992263 := bstep (se 1 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 992263 = 1488395) B1488395
theorem B664699 : Blo 587289 664699 := bstep (se 1 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 664699 = 997049) B997049
theorem B2827511 : Blo 587289 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B992695 : Blo 587289 992695 := bstep (se 1 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 992695 = 1489043) B1489043
theorem B2237939 : Blo 587289 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B3352103 : Blo 587289 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B1418791 : Blo 587289 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B665167 : Blo 587289 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B992891 : Blo 587289 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B2238137 : Blo 587289 2238137 := bstep (se 2 (by rfl) ⟨839301, by rfl⟩ : syracuseStep 2238137 = 1678603) B1678603
theorem B2238151 : Blo 587289 2238151 := bstep (se 1 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 2238151 = 3357227) B3357227
theorem B2991815 : Blo 587289 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B993289 : Blo 587289 993289 := bstep (se 2 (by rfl) ⟨372483, by rfl⟩ : syracuseStep 993289 = 744967) B744967
theorem B5023781 : Blo 587289 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B993451 : Blo 587289 993451 := bstep (se 1 (by rfl) ⟨745088, by rfl⟩ : syracuseStep 993451 = 1490177) B1490177
theorem B1681793 : Blo 587289 1681793 := bstep (se 2 (by rfl) ⟨630672, by rfl⟩ : syracuseStep 1681793 = 1261345) B1261345
theorem B993755 : Blo 587289 993755 := bstep (se 1 (by rfl) ⟨745316, by rfl⟩ : syracuseStep 993755 = 1490633) B1490633
theorem B1321595 : Blo 587289 1321595 := bstep (se 1 (by rfl) ⟨991196, by rfl⟩ : syracuseStep 1321595 = 1982393) B1982393
theorem B2239123 : Blo 587289 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B993991 : Blo 587289 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B1321721 : Blo 587289 1321721 := bstep (se 2 (by rfl) ⟨495645, by rfl⟩ : syracuseStep 1321721 = 991291) B991291
theorem B994153 : Blo 587289 994153 := bstep (se 2 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 994153 = 745615) B745615
theorem B4762475 : Blo 587289 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B1321991 : Blo 587289 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B1322063 : Blo 587289 1322063 := bstep (se 1 (by rfl) ⟨991547, by rfl⟩ : syracuseStep 1322063 = 1983095) B1983095
theorem B3779855 : Blo 587289 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B2010511 : Blo 587289 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B994747 : Blo 587289 994747 := bstep (se 1 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 994747 = 1492121) B1492121
theorem B1322459 : Blo 587289 1322459 := bstep (se 1 (by rfl) ⟨991844, by rfl⟩ : syracuseStep 1322459 = 1983689) B1983689
theorem B994855 : Blo 587289 994855 := bstep (se 1 (by rfl) ⟨746141, by rfl⟩ : syracuseStep 994855 = 1492283) B1492283
theorem B2829971 : Blo 587289 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B2010809 : Blo 587289 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B3354311 : Blo 587289 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B6368989 : Blo 587289 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B1683193 : Blo 587289 1683193 := bstep (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) B1262395
theorem B995179 : Blo 587289 995179 := bstep (se 1 (by rfl) ⟨746384, by rfl⟩ : syracuseStep 995179 = 1492769) B1492769
theorem B2830241 : Blo 587289 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B1322927 : Blo 587289 1322927 := bstep (se 1 (by rfl) ⟨992195, by rfl⟩ : syracuseStep 1322927 = 1984391) B1984391
theorem B1486775 : Blo 587289 1486775 := bstep (se 1 (by rfl) ⟨1115081, by rfl⟩ : syracuseStep 1486775 = 2230163) B2230163
theorem B1257491 : Blo 587289 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B9056285 : Blo 587289 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B1323179 : Blo 587289 1323179 := bstep (se 1 (by rfl) ⟨992384, by rfl⟩ : syracuseStep 1323179 = 1984769) B1984769
theorem B2240855 : Blo 587289 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B3191329 : Blo 587289 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B1323719 : Blo 587289 1323719 := bstep (se 1 (by rfl) ⟨992789, by rfl⟩ : syracuseStep 1323719 = 1985579) B1985579
theorem B996239 : Blo 587289 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B1487879 : Blo 587289 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B1487929 : Blo 587289 1487929 := bstep (se 2 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 1487929 = 1115947) B1115947
theorem B6698051 : Blo 587289 6698051 := bstep (se 1 (by rfl) ⟨5023538, by rfl⟩ : syracuseStep 6698051 = 10047077) B10047077
theorem B1062011 : Blo 587289 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B996475 : Blo 587289 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B1488233 : Blo 587289 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B1914313 : Blo 587289 1914313 := bstep (se 2 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 1914313 = 1435735) B1435735
theorem B1324583 : Blo 587289 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B3815111 : Blo 587289 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B2012921 : Blo 587289 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B6371065 : Blo 587289 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B3192671 : Blo 587289 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B1324907 : Blo 587289 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B1324961 : Blo 587289 1324961 := bstep (se 2 (by rfl) ⟨496860, by rfl⟩ : syracuseStep 1324961 = 993721) B993721
theorem B4470713 : Blo 587289 4470713 := bstep (se 2 (by rfl) ⟨1676517, by rfl⟩ : syracuseStep 4470713 = 3353035) B3353035
theorem B5027777 : Blo 587289 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B997339 : Blo 587289 997339 := bstep (se 1 (by rfl) ⟨748004, by rfl⟩ : syracuseStep 997339 = 1496009) B1496009
theorem B2865233 : Blo 587289 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B1325303 : Blo 587289 1325303 := bstep (se 1 (by rfl) ⟨993977, by rfl⟩ : syracuseStep 1325303 = 1987955) B1987955
theorem B1325897 : Blo 587289 1325897 := bstep (se 2 (by rfl) ⟨497211, by rfl⟩ : syracuseStep 1325897 = 994423) B994423
theorem B2243969 : Blo 587289 2243969 := bstep (se 2 (by rfl) ⟨841488, by rfl⟩ : syracuseStep 2243969 = 1682977) B1682977
theorem B2243983 : Blo 587289 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B1490471 : Blo 587289 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B1326689 : Blo 587289 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B2146121 : Blo 587289 2146121 := bstep (se 2 (by rfl) ⟨804795, by rfl⟩ : syracuseStep 2146121 = 1609591) B1609591
theorem B1490795 : Blo 587289 1490795 := bstep (se 1 (by rfl) ⟨1118096, by rfl⟩ : syracuseStep 1490795 = 2236193) B2236193
theorem B1327031 : Blo 587289 1327031 := bstep (se 1 (by rfl) ⟨995273, by rfl⟩ : syracuseStep 1327031 = 1990547) B1990547
theorem B1884161 : Blo 587289 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B2834489 : Blo 587289 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B10731851 : Blo 587289 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B1982825 : Blo 587289 1982825 := bstep (se 2 (by rfl) ⟨743559, by rfl⟩ : syracuseStep 1982825 = 1487119) B1487119
theorem B1065377 : Blo 587289 1065377 := bstep (se 2 (by rfl) ⟨399516, by rfl⟩ : syracuseStep 1065377 = 799033) B799033
theorem B1491443 : Blo 587289 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B1327625 : Blo 587289 1327625 := bstep (se 2 (by rfl) ⟨497859, by rfl⟩ : syracuseStep 1327625 = 995719) B995719
theorem B1491655 : Blo 587289 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B4473629 : Blo 587289 4473629 := bstep (se 3 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 4473629 = 1677611) B1677611
theorem B1327967 : Blo 587289 1327967 := bstep (se 1 (by rfl) ⟨995975, by rfl⟩ : syracuseStep 1327967 = 1991951) B1991951
theorem B2016175 : Blo 587289 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B1983419 : Blo 587289 1983419 := bstep (se 1 (by rfl) ⟨1487564, by rfl⟩ : syracuseStep 1983419 = 2975129) B2975129
theorem B1328147 : Blo 587289 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B836687 : Blo 587289 836687 := bstep (se 1 (by rfl) ⟨627515, by rfl⟩ : syracuseStep 836687 = 1255031) B1255031
theorem B1066313 : Blo 587289 1066313 := bstep (se 2 (by rfl) ⟨399867, by rfl⟩ : syracuseStep 1066313 = 799735) B799735
theorem B16106845 : Blo 587289 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B1328489 : Blo 587289 1328489 := bstep (se 2 (by rfl) ⟨498183, by rfl⟩ : syracuseStep 1328489 = 996367) B996367
theorem B3360143 : Blo 587289 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B4244899 : Blo 587289 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B2835931 : Blo 587289 2835931 := bstep (se 1 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 2835931 = 4253897) B4253897
theorem B1492577 : Blo 587289 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B2148049 : Blo 587289 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1198007 : Blo 587289 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1329083 : Blo 587289 1329083 := bstep (se 1 (by rfl) ⟨996812, by rfl⟩ : syracuseStep 1329083 = 1993625) B1993625
theorem B6637571 : Blo 587289 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B4245533 : Blo 587289 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B11290661 : Blo 587289 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B1329209 : Blo 587289 1329209 := bstep (se 2 (by rfl) ⟨498453, by rfl⟩ : syracuseStep 1329209 = 996907) B996907
theorem B4540805 : Blo 587289 4540805 := bstep (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) B851401
theorem B1329551 : Blo 587289 1329551 := bstep (se 1 (by rfl) ⟨997163, by rfl⟩ : syracuseStep 1329551 = 1994327) B1994327
theorem B8604107 : Blo 587289 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B1985147 : Blo 587289 1985147 := bstep (se 1 (by rfl) ⟨1488860, by rfl⟩ : syracuseStep 1985147 = 2977721) B2977721
theorem B1329875 : Blo 587289 1329875 := bstep (se 1 (by rfl) ⟨997406, by rfl⟩ : syracuseStep 1329875 = 1994813) B1994813
theorem B1985309 : Blo 587289 1985309 := bstep (se 3 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 1985309 = 744491) B744491
theorem B1592239 : Blo 587289 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B6048695 : Blo 587289 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B1494035 : Blo 587289 1494035 := bstep (se 1 (by rfl) ⟨1120526, by rfl⟩ : syracuseStep 1494035 = 2241053) B2241053
theorem B43142219 : Blo 587289 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B707935 : Blo 587289 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B1986011 : Blo 587289 1986011 := bstep (se 1 (by rfl) ⟨1489508, by rfl⟩ : syracuseStep 1986011 = 2979017) B2979017
theorem B3591803 : Blo 587289 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B839803 : Blo 587289 839803 := bstep (se 1 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 839803 = 1259705) B1259705
theorem B1986713 : Blo 587289 1986713 := bstep (se 2 (by rfl) ⟨745017, by rfl⟩ : syracuseStep 1986713 = 1490035) B1490035
theorem B11457125 : Blo 587289 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B3363767 : Blo 587289 3363767 := bstep (se 1 (by rfl) ⟨2522825, by rfl⟩ : syracuseStep 3363767 = 5045651) B5045651
theorem B7263233 : Blo 587289 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B4478003 : Blo 587289 4478003 := bstep (se 1 (by rfl) ⟨3358502, by rfl⟩ : syracuseStep 4478003 = 6717005) B6717005
theorem B2512043 : Blo 587289 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B1987901 : Blo 587289 1987901 := bstep (se 3 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 1987901 = 745463) B745463
theorem B1889801 : Blo 587289 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B2119193 : Blo 587289 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B4773437 : Blo 587289 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B1005625 : Blo 587289 1005625 := bstep (se 2 (by rfl) ⟨377109, by rfl⟩ : syracuseStep 1005625 = 754219) B754219
theorem B1988765 : Blo 587289 1988765 := bstep (se 3 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 1988765 = 745787) B745787
theorem B3365225 : Blo 587289 3365225 := bstep (se 2 (by rfl) ⟨1261959, by rfl⟩ : syracuseStep 3365225 = 2523919) B2523919
theorem B1005967 : Blo 587289 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B743899 : Blo 587289 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B5036525 : Blo 587289 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B1989305 : Blo 587289 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B4315907 : Blo 587289 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B8510437 : Blo 587289 8510437 := bstep (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) B1595707
theorem B1989899 : Blo 587289 1989899 := bstep (se 1 (by rfl) ⟨1492424, by rfl⟩ : syracuseStep 1989899 = 2984849) B2984849
theorem B1990169 : Blo 587289 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B942119 : Blo 587289 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B1007815 : Blo 587289 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B16998731 : Blo 587289 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B3367433 : Blo 587289 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B1991303 : Blo 587289 1991303 := bstep (se 1 (by rfl) ⟨1493477, by rfl⟩ : syracuseStep 1991303 = 2986955) B2986955
theorem B1991357 : Blo 587289 1991357 := bstep (se 3 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 1991357 = 746759) B746759
theorem B1991519 : Blo 587289 1991519 := bstep (se 1 (by rfl) ⟨1493639, by rfl⟩ : syracuseStep 1991519 = 2987279) B2987279
theorem B1794977 : Blo 587289 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B1991681 : Blo 587289 1991681 := bstep (se 2 (by rfl) ⟨746880, by rfl⟩ : syracuseStep 1991681 = 1493761) B1493761
theorem B12248113 : Blo 587289 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B15262937 : Blo 587289 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2974967 : Blo 587289 2974967 := bstep (se 1 (by rfl) ⟨2231225, by rfl⟩ : syracuseStep 2974967 = 4462451) B4462451
theorem B5727653 : Blo 587289 5727653 := bstep (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) B1073935
theorem B4253147 : Blo 587289 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B2975453 : Blo 587289 2975453 := bstep (se 3 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 2975453 = 1115795) B1115795
theorem B1992491 : Blo 587289 1992491 := bstep (se 1 (by rfl) ⟨1494368, by rfl⟩ : syracuseStep 1992491 = 2988737) B2988737
theorem B747559 : Blo 587289 747559 := bstep (se 1 (by rfl) ⟨560669, by rfl⟩ : syracuseStep 747559 = 1121339) B1121339
theorem B4778041 : Blo 587289 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B1992761 : Blo 587289 1992761 := bstep (se 2 (by rfl) ⟨747285, by rfl⟩ : syracuseStep 1992761 = 1494571) B1494571
theorem B747883 : Blo 587289 747883 := bstep (se 1 (by rfl) ⟨560912, by rfl⟩ : syracuseStep 747883 = 1121825) B1121825
theorem B1993085 : Blo 587289 1993085 := bstep (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) B747407
theorem B1796633 : Blo 587289 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B748111 : Blo 587289 748111 := bstep (se 1 (by rfl) ⟨561083, by rfl⟩ : syracuseStep 748111 = 1122167) B1122167
theorem B1993355 : Blo 587289 1993355 := bstep (se 1 (by rfl) ⟨1495016, by rfl⟩ : syracuseStep 1993355 = 2990033) B2990033
theorem B944887 : Blo 587289 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B2387465 : Blo 587289 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B1994273 : Blo 587289 1994273 := bstep (se 2 (by rfl) ⟨747852, by rfl⟩ : syracuseStep 1994273 = 1495705) B1495705
theorem B4484807 : Blo 587289 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B1994489 : Blo 587289 1994489 := bstep (se 2 (by rfl) ⟨747933, by rfl⟩ : syracuseStep 1994489 = 1495867) B1495867
theorem B1994759 : Blo 587289 1994759 := bstep (se 1 (by rfl) ⟨1496069, by rfl⟩ : syracuseStep 1994759 = 2992139) B2992139
theorem B2125939 : Blo 587289 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B1994867 : Blo 587289 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B2126141 : Blo 587289 2126141 := bstep (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) B797303
theorem B880991 : Blo 587289 880991 := bstep (se 1 (by rfl) ⟨660743, by rfl⟩ : syracuseStep 880991 = 1321487) B1321487
theorem B881003 : Blo 587289 881003 := bstep (se 1 (by rfl) ⟨660752, by rfl⟩ : syracuseStep 881003 = 1321505) B1321505
theorem B1995137 : Blo 587289 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B2519561 : Blo 587289 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B881231 : Blo 587289 881231 := bstep (se 1 (by rfl) ⟨660923, by rfl⟩ : syracuseStep 881231 = 1321847) B1321847
theorem B881351 : Blo 587289 881351 := bstep (se 1 (by rfl) ⟨661013, by rfl⟩ : syracuseStep 881351 = 1322027) B1322027
theorem B946937 : Blo 587289 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B881513 : Blo 587289 881513 := bstep (se 2 (by rfl) ⟨330567, by rfl⟩ : syracuseStep 881513 = 661135) B661135
theorem B881591 : Blo 587289 881591 := bstep (se 1 (by rfl) ⟨661193, by rfl⟩ : syracuseStep 881591 = 1322387) B1322387
theorem B881627 : Blo 587289 881627 := bstep (se 1 (by rfl) ⟨661220, by rfl⟩ : syracuseStep 881627 = 1322441) B1322441
theorem B2520143 : Blo 587289 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B882095 : Blo 587289 882095 := bstep (se 1 (by rfl) ⟨661571, by rfl⟩ : syracuseStep 882095 = 1323143) B1323143
theorem B882185 : Blo 587289 882185 := bstep (se 2 (by rfl) ⟨330819, by rfl⟩ : syracuseStep 882185 = 661639) B661639
theorem B587303 : Blo 587289 587303 := bstep (se 1 (by rfl) ⟨440477, by rfl⟩ : syracuseStep 587303 = 880955) B880955
theorem B882215 : Blo 587289 882215 := bstep (se 1 (by rfl) ⟨661661, by rfl⟩ : syracuseStep 882215 = 1323323) B1323323
theorem B587343 : Blo 587289 587343 := bstep (se 1 (by rfl) ⟨440507, by rfl⟩ : syracuseStep 587343 = 881015) B881015
theorem B587359 : Blo 587289 587359 := bstep (se 1 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 587359 = 881039) B881039
theorem B587387 : Blo 587289 587387 := bstep (se 1 (by rfl) ⟨440540, by rfl⟩ : syracuseStep 587387 = 881081) B881081
theorem B882299 : Blo 587289 882299 := bstep (se 1 (by rfl) ⟨661724, by rfl⟩ : syracuseStep 882299 = 1323449) B1323449
theorem B587439 : Blo 587289 587439 := bstep (se 1 (by rfl) ⟨440579, by rfl⟩ : syracuseStep 587439 = 881159) B881159
theorem B587463 : Blo 587289 587463 := bstep (se 1 (by rfl) ⟨440597, by rfl⟩ : syracuseStep 587463 = 881195) B881195
theorem B2520791 : Blo 587289 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B587483 : Blo 587289 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B882425 : Blo 587289 882425 := bstep (se 2 (by rfl) ⟨330909, by rfl⟩ : syracuseStep 882425 = 661819) B661819
theorem B587559 : Blo 587289 587559 := bstep (se 1 (by rfl) ⟨440669, by rfl⟩ : syracuseStep 587559 = 881339) B881339
theorem B587599 : Blo 587289 587599 := bstep (se 1 (by rfl) ⟨440699, by rfl⟩ : syracuseStep 587599 = 881399) B881399
theorem B587615 : Blo 587289 587615 := bstep (se 1 (by rfl) ⟨440711, by rfl⟩ : syracuseStep 587615 = 881423) B881423
theorem B882527 : Blo 587289 882527 := bstep (se 1 (by rfl) ⟨661895, by rfl⟩ : syracuseStep 882527 = 1323791) B1323791
theorem B882539 : Blo 587289 882539 := bstep (se 1 (by rfl) ⟨661904, by rfl⟩ : syracuseStep 882539 = 1323809) B1323809
theorem B587643 : Blo 587289 587643 := bstep (se 1 (by rfl) ⟨440732, by rfl⟩ : syracuseStep 587643 = 881465) B881465
theorem B587695 : Blo 587289 587695 := bstep (se 1 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 587695 = 881543) B881543
theorem B587719 : Blo 587289 587719 := bstep (se 1 (by rfl) ⟨440789, by rfl⟩ : syracuseStep 587719 = 881579) B881579
theorem B12777425 : Blo 587289 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B587739 : Blo 587289 587739 := bstep (se 1 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 587739 = 881609) B881609
theorem B587815 : Blo 587289 587815 := bstep (se 1 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 587815 = 881723) B881723
theorem B587855 : Blo 587289 587855 := bstep (se 1 (by rfl) ⟨440891, by rfl⟩ : syracuseStep 587855 = 881783) B881783
theorem B882767 : Blo 587289 882767 := bstep (se 1 (by rfl) ⟨662075, by rfl⟩ : syracuseStep 882767 = 1324151) B1324151
theorem B1210447 : Blo 587289 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B587871 : Blo 587289 587871 := bstep (se 1 (by rfl) ⟨440903, by rfl⟩ : syracuseStep 587871 = 881807) B881807
theorem B587899 : Blo 587289 587899 := bstep (se 1 (by rfl) ⟨440924, by rfl⟩ : syracuseStep 587899 = 881849) B881849
theorem B587951 : Blo 587289 587951 := bstep (se 1 (by rfl) ⟨440963, by rfl⟩ : syracuseStep 587951 = 881927) B881927
theorem B587975 : Blo 587289 587975 := bstep (se 1 (by rfl) ⟨440981, by rfl⟩ : syracuseStep 587975 = 881963) B881963
theorem B882887 : Blo 587289 882887 := bstep (se 1 (by rfl) ⟨662165, by rfl⟩ : syracuseStep 882887 = 1324331) B1324331
theorem B587995 : Blo 587289 587995 := bstep (se 1 (by rfl) ⟨440996, by rfl⟩ : syracuseStep 587995 = 881993) B881993
theorem B588071 : Blo 587289 588071 := bstep (se 1 (by rfl) ⟨441053, by rfl⟩ : syracuseStep 588071 = 882107) B882107
theorem B588111 : Blo 587289 588111 := bstep (se 1 (by rfl) ⟨441083, by rfl⟩ : syracuseStep 588111 = 882167) B882167
theorem B588127 : Blo 587289 588127 := bstep (se 1 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 588127 = 882191) B882191
theorem B883049 : Blo 587289 883049 := bstep (se 2 (by rfl) ⟨331143, by rfl⟩ : syracuseStep 883049 = 662287) B662287
theorem B588155 : Blo 587289 588155 := bstep (se 1 (by rfl) ⟨441116, by rfl⟩ : syracuseStep 588155 = 882233) B882233
theorem B15989123 : Blo 587289 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B588207 : Blo 587289 588207 := bstep (se 1 (by rfl) ⟨441155, by rfl⟩ : syracuseStep 588207 = 882311) B882311
theorem B883127 : Blo 587289 883127 := bstep (se 1 (by rfl) ⟨662345, by rfl⟩ : syracuseStep 883127 = 1324691) B1324691
theorem B588231 : Blo 587289 588231 := bstep (se 1 (by rfl) ⟨441173, by rfl⟩ : syracuseStep 588231 = 882347) B882347
theorem B588251 : Blo 587289 588251 := bstep (se 1 (by rfl) ⟨441188, by rfl⟩ : syracuseStep 588251 = 882377) B882377
theorem B883163 : Blo 587289 883163 := bstep (se 1 (by rfl) ⟨662372, by rfl⟩ : syracuseStep 883163 = 1324745) B1324745
theorem B3832343 : Blo 587289 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B588327 : Blo 587289 588327 := bstep (se 1 (by rfl) ⟨441245, by rfl⟩ : syracuseStep 588327 = 882491) B882491
theorem B588367 : Blo 587289 588367 := bstep (se 1 (by rfl) ⟨441275, by rfl⟩ : syracuseStep 588367 = 882551) B882551
theorem B588383 : Blo 587289 588383 := bstep (se 1 (by rfl) ⟨441287, by rfl⟩ : syracuseStep 588383 = 882575) B882575
theorem B588411 : Blo 587289 588411 := bstep (se 1 (by rfl) ⟨441308, by rfl⟩ : syracuseStep 588411 = 882617) B882617
theorem B588463 : Blo 587289 588463 := bstep (se 1 (by rfl) ⟨441347, by rfl⟩ : syracuseStep 588463 = 882695) B882695
theorem B588487 : Blo 587289 588487 := bstep (se 1 (by rfl) ⟨441365, by rfl⟩ : syracuseStep 588487 = 882731) B882731
theorem B588507 : Blo 587289 588507 := bstep (se 1 (by rfl) ⟨441380, by rfl⟩ : syracuseStep 588507 = 882761) B882761
theorem B2980637 : Blo 587289 2980637 := bstep (se 3 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 2980637 = 1117739) B1117739
theorem B588583 : Blo 587289 588583 := bstep (se 1 (by rfl) ⟨441437, by rfl⟩ : syracuseStep 588583 = 882875) B882875
theorem B588623 : Blo 587289 588623 := bstep (se 1 (by rfl) ⟨441467, by rfl⟩ : syracuseStep 588623 = 882935) B882935
theorem B588639 : Blo 587289 588639 := bstep (se 1 (by rfl) ⟨441479, by rfl⟩ : syracuseStep 588639 = 882959) B882959
theorem B588667 : Blo 587289 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B8616851 : Blo 587289 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B588719 : Blo 587289 588719 := bstep (se 1 (by rfl) ⟨441539, by rfl⟩ : syracuseStep 588719 = 883079) B883079
theorem B883631 : Blo 587289 883631 := bstep (se 1 (by rfl) ⟨662723, by rfl⟩ : syracuseStep 883631 = 1325447) B1325447
theorem B588743 : Blo 587289 588743 := bstep (se 1 (by rfl) ⟨441557, by rfl⟩ : syracuseStep 588743 = 883115) B883115
theorem B588763 : Blo 587289 588763 := bstep (se 1 (by rfl) ⟨441572, by rfl⟩ : syracuseStep 588763 = 883145) B883145
theorem B883721 : Blo 587289 883721 := bstep (se 2 (by rfl) ⟨331395, by rfl⟩ : syracuseStep 883721 = 662791) B662791
theorem B588839 : Blo 587289 588839 := bstep (se 1 (by rfl) ⟨441629, by rfl⟩ : syracuseStep 588839 = 883259) B883259
theorem B883751 : Blo 587289 883751 := bstep (se 1 (by rfl) ⟨662813, by rfl⟩ : syracuseStep 883751 = 1325627) B1325627
theorem B588879 : Blo 587289 588879 := bstep (se 1 (by rfl) ⟨441659, by rfl⟩ : syracuseStep 588879 = 883319) B883319
theorem B588895 : Blo 587289 588895 := bstep (se 1 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 588895 = 883343) B883343
theorem B588923 : Blo 587289 588923 := bstep (se 1 (by rfl) ⟨441692, by rfl⟩ : syracuseStep 588923 = 883385) B883385
theorem B883835 : Blo 587289 883835 := bstep (se 1 (by rfl) ⟨662876, by rfl⟩ : syracuseStep 883835 = 1325753) B1325753
theorem B588975 : Blo 587289 588975 := bstep (se 1 (by rfl) ⟨441731, by rfl⟩ : syracuseStep 588975 = 883463) B883463
theorem B588999 : Blo 587289 588999 := bstep (se 1 (by rfl) ⟨441749, by rfl⟩ : syracuseStep 588999 = 883499) B883499
theorem B1211591 : Blo 587289 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B589019 : Blo 587289 589019 := bstep (se 1 (by rfl) ⟨441764, by rfl⟩ : syracuseStep 589019 = 883529) B883529
theorem B883961 : Blo 587289 883961 := bstep (se 2 (by rfl) ⟨331485, by rfl⟩ : syracuseStep 883961 = 662971) B662971
theorem B589095 : Blo 587289 589095 := bstep (se 1 (by rfl) ⟨441821, by rfl⟩ : syracuseStep 589095 = 883643) B883643
theorem B589135 : Blo 587289 589135 := bstep (se 1 (by rfl) ⟨441851, by rfl⟩ : syracuseStep 589135 = 883703) B883703
theorem B621919 : Blo 587289 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B589151 : Blo 587289 589151 := bstep (se 1 (by rfl) ⟨441863, by rfl⟩ : syracuseStep 589151 = 883727) B883727
theorem B884063 : Blo 587289 884063 := bstep (se 1 (by rfl) ⟨663047, by rfl⟩ : syracuseStep 884063 = 1326095) B1326095
theorem B884075 : Blo 587289 884075 := bstep (se 1 (by rfl) ⟨663056, by rfl⟩ : syracuseStep 884075 = 1326113) B1326113
theorem B589179 : Blo 587289 589179 := bstep (se 1 (by rfl) ⟨441884, by rfl⟩ : syracuseStep 589179 = 883769) B883769
theorem B589231 : Blo 587289 589231 := bstep (se 1 (by rfl) ⟨441923, by rfl⟩ : syracuseStep 589231 = 883847) B883847
theorem B589255 : Blo 587289 589255 := bstep (se 1 (by rfl) ⟨441941, by rfl⟩ : syracuseStep 589255 = 883883) B883883
theorem B589275 : Blo 587289 589275 := bstep (se 1 (by rfl) ⟨441956, by rfl⟩ : syracuseStep 589275 = 883913) B883913
theorem B589351 : Blo 587289 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B589391 : Blo 587289 589391 := bstep (se 1 (by rfl) ⟨442043, by rfl⟩ : syracuseStep 589391 = 884087) B884087
theorem B884303 : Blo 587289 884303 := bstep (se 1 (by rfl) ⟨663227, by rfl⟩ : syracuseStep 884303 = 1326455) B1326455
theorem B589407 : Blo 587289 589407 := bstep (se 1 (by rfl) ⟨442055, by rfl⟩ : syracuseStep 589407 = 884111) B884111
theorem B589435 : Blo 587289 589435 := bstep (se 1 (by rfl) ⟨442076, by rfl⟩ : syracuseStep 589435 = 884153) B884153
theorem B589487 : Blo 587289 589487 := bstep (se 1 (by rfl) ⟨442115, by rfl⟩ : syracuseStep 589487 = 884231) B884231
theorem B589511 : Blo 587289 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B884423 : Blo 587289 884423 := bstep (se 1 (by rfl) ⟨663317, by rfl⟩ : syracuseStep 884423 = 1326635) B1326635
theorem B589531 : Blo 587289 589531 := bstep (se 1 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 589531 = 884297) B884297
theorem B589607 : Blo 587289 589607 := bstep (se 1 (by rfl) ⟨442205, by rfl⟩ : syracuseStep 589607 = 884411) B884411
theorem B589647 : Blo 587289 589647 := bstep (se 1 (by rfl) ⟨442235, by rfl⟩ : syracuseStep 589647 = 884471) B884471
theorem B589663 : Blo 587289 589663 := bstep (se 1 (by rfl) ⟨442247, by rfl⟩ : syracuseStep 589663 = 884495) B884495
theorem B884585 : Blo 587289 884585 := bstep (se 2 (by rfl) ⟨331719, by rfl⟩ : syracuseStep 884585 = 663439) B663439
theorem B589691 : Blo 587289 589691 := bstep (se 1 (by rfl) ⟨442268, by rfl⟩ : syracuseStep 589691 = 884537) B884537
theorem B589743 : Blo 587289 589743 := bstep (se 1 (by rfl) ⟨442307, by rfl⟩ : syracuseStep 589743 = 884615) B884615
theorem B884663 : Blo 587289 884663 := bstep (se 1 (by rfl) ⟨663497, by rfl⟩ : syracuseStep 884663 = 1326995) B1326995
theorem B589767 : Blo 587289 589767 := bstep (se 1 (by rfl) ⟨442325, by rfl⟩ : syracuseStep 589767 = 884651) B884651
theorem B589787 : Blo 587289 589787 := bstep (se 1 (by rfl) ⟨442340, by rfl⟩ : syracuseStep 589787 = 884681) B884681
theorem B884699 : Blo 587289 884699 := bstep (se 1 (by rfl) ⟨663524, by rfl⟩ : syracuseStep 884699 = 1327049) B1327049
theorem B1343753 : Blo 587289 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B590111 : Blo 587289 590111 := bstep (se 1 (by rfl) ⟨442583, by rfl⟩ : syracuseStep 590111 = 885167) B885167
theorem B885083 : Blo 587289 885083 := bstep (se 1 (by rfl) ⟨663812, by rfl⟩ : syracuseStep 885083 = 1327625) B1327625
theorem B590171 : Blo 587289 590171 := bstep (se 1 (by rfl) ⟨442628, by rfl⟩ : syracuseStep 590171 = 885257) B885257
theorem B590191 : Blo 587289 590191 := bstep (se 1 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 590191 = 885287) B885287
theorem B6455717 : Blo 587289 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B590247 : Blo 587289 590247 := bstep (se 1 (by rfl) ⟨442685, by rfl⟩ : syracuseStep 590247 = 885371) B885371
theorem B590331 : Blo 587289 590331 := bstep (se 1 (by rfl) ⟨442748, by rfl⟩ : syracuseStep 590331 = 885497) B885497
theorem B2982419 : Blo 587289 2982419 := bstep (se 1 (by rfl) ⟨2236814, by rfl⟩ : syracuseStep 2982419 = 4473629) B4473629
theorem B885311 : Blo 587289 885311 := bstep (se 1 (by rfl) ⟨663983, by rfl⟩ : syracuseStep 885311 = 1327967) B1327967
theorem B590399 : Blo 587289 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B590407 : Blo 587289 590407 := bstep (se 1 (by rfl) ⟨442805, by rfl⟩ : syracuseStep 590407 = 885611) B885611
theorem B885431 : Blo 587289 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B590559 : Blo 587289 590559 := bstep (se 1 (by rfl) ⟨442919, by rfl⟩ : syracuseStep 590559 = 885839) B885839
theorem B590639 : Blo 587289 590639 := bstep (se 1 (by rfl) ⟨442979, by rfl⟩ : syracuseStep 590639 = 885959) B885959
theorem B885659 : Blo 587289 885659 := bstep (se 1 (by rfl) ⟨664244, by rfl⟩ : syracuseStep 885659 = 1328489) B1328489
theorem B590747 : Blo 587289 590747 := bstep (se 1 (by rfl) ⟨443060, by rfl⟩ : syracuseStep 590747 = 886121) B886121
theorem B590799 : Blo 587289 590799 := bstep (se 1 (by rfl) ⟨443099, by rfl⟩ : syracuseStep 590799 = 886199) B886199
theorem B590823 : Blo 587289 590823 := bstep (se 1 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 590823 = 886235) B886235
theorem B1115279 : Blo 587289 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B2688233 : Blo 587289 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B3409129 : Blo 587289 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B591135 : Blo 587289 591135 := bstep (se 1 (by rfl) ⟨443351, by rfl⟩ : syracuseStep 591135 = 886703) B886703
theorem B886055 : Blo 587289 886055 := bstep (se 1 (by rfl) ⟨664541, by rfl⟩ : syracuseStep 886055 = 1329083) B1329083
theorem B4425047 : Blo 587289 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B591195 : Blo 587289 591195 := bstep (se 1 (by rfl) ⟨443396, by rfl⟩ : syracuseStep 591195 = 886793) B886793
theorem B591215 : Blo 587289 591215 := bstep (se 1 (by rfl) ⟨443411, by rfl⟩ : syracuseStep 591215 = 886823) B886823
theorem B886139 : Blo 587289 886139 := bstep (se 1 (by rfl) ⟨664604, by rfl⟩ : syracuseStep 886139 = 1329209) B1329209
theorem B591271 : Blo 587289 591271 := bstep (se 1 (by rfl) ⟨443453, by rfl⟩ : syracuseStep 591271 = 886907) B886907
theorem B886265 : Blo 587289 886265 := bstep (se 2 (by rfl) ⟨332349, by rfl⟩ : syracuseStep 886265 = 664699) B664699
theorem B886367 : Blo 587289 886367 := bstep (se 1 (by rfl) ⟨664775, by rfl⟩ : syracuseStep 886367 = 1329551) B1329551
theorem B5736071 : Blo 587289 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B886583 : Blo 587289 886583 := bstep (se 1 (by rfl) ⟨664937, by rfl⟩ : syracuseStep 886583 = 1329875) B1329875
theorem B48236471 : Blo 587289 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B4032463 : Blo 587289 4032463 := bstep (se 1 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 4032463 = 6048695) B6048695
theorem B2525165 : Blo 587289 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B886889 : Blo 587289 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B2984201 : Blo 587289 2984201 := bstep (se 2 (by rfl) ⟨1119075, by rfl⟩ : syracuseStep 2984201 = 2238151) B2238151
theorem B2394535 : Blo 587289 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B3344813 : Blo 587289 3344813 := bstep (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) B1254305
theorem B2230847 : Blo 587289 2230847 := bstep (se 1 (by rfl) ⟨1673135, by rfl⟩ : syracuseStep 2230847 = 3346271) B3346271
theorem B10095191 : Blo 587289 10095191 := bstep (se 1 (by rfl) ⟨7571393, by rfl⟩ : syracuseStep 10095191 = 15142787) B15142787
theorem B2231165 : Blo 587289 2231165 := bstep (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) B836687
theorem B7638083 : Blo 587289 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B2985335 : Blo 587289 2985335 := bstep (se 1 (by rfl) ⟨2239001, by rfl⟩ : syracuseStep 2985335 = 4478003) B4478003
theorem B1674695 : Blo 587289 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B2985497 : Blo 587289 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B1412795 : Blo 587289 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B3182291 : Blo 587289 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B8491985 : Blo 587289 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B660775 : Blo 587289 660775 := bstep (se 1 (by rfl) ⟨495581, by rfl⟩ : syracuseStep 660775 = 991163) B991163
theorem B660847 : Blo 587289 660847 := bstep (se 1 (by rfl) ⟨495635, by rfl⟩ : syracuseStep 660847 = 991271) B991271
theorem B628079 : Blo 587289 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B1119737 : Blo 587289 1119737 := bstep (se 2 (by rfl) ⟨419901, by rfl⟩ : syracuseStep 1119737 = 839803) B839803
theorem B661063 : Blo 587289 661063 := bstep (se 1 (by rfl) ⟨495797, by rfl⟩ : syracuseStep 661063 = 991595) B991595
theorem B14522597 : Blo 587289 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B4462937 : Blo 587289 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B42637661 : Blo 587289 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B2234735 : Blo 587289 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B2988413 : Blo 587289 2988413 := bstep (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) B1120655
theorem B661927 : Blo 587289 661927 := bstep (se 1 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 661927 = 992891) B992891
theorem B3349187 : Blo 587289 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B1121195 : Blo 587289 1121195 := bstep (se 1 (by rfl) ⟨840896, by rfl⟩ : syracuseStep 1121195 = 1681793) B1681793
theorem B662503 : Blo 587289 662503 := bstep (se 1 (by rfl) ⟨496877, by rfl⟩ : syracuseStep 662503 = 993755) B993755
theorem B12721369 : Blo 587289 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B11509085 : Blo 587289 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B10722725 : Blo 587289 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B8494753 : Blo 587289 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B2236207 : Blo 587289 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B2989871 : Blo 587289 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B991183 : Blo 587289 991183 := bstep (se 1 (by rfl) ⟨743387, by rfl⟩ : syracuseStep 991183 = 1486775) B1486775
theorem B6037523 : Blo 587289 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B10756145 : Blo 587289 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B1417427 : Blo 587289 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B1679707 : Blo 587289 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B40772105 : Blo 587289 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B664159 : Blo 587289 664159 := bstep (se 1 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 664159 = 996239) B996239
theorem B991865 : Blo 587289 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B991919 : Blo 587289 991919 := bstep (se 1 (by rfl) ⟨743939, by rfl⟩ : syracuseStep 991919 = 1487879) B1487879
theorem B4465367 : Blo 587289 4465367 := bstep (se 1 (by rfl) ⟨3349025, by rfl⟩ : syracuseStep 4465367 = 6698051) B6698051
theorem B1680095 : Blo 587289 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B992155 : Blo 587289 992155 := bstep (se 1 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 992155 = 1488233) B1488233
theorem B1680527 : Blo 587289 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B3351851 : Blo 587289 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B11347249 : Blo 587289 11347249 := bstep (se 2 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 11347249 = 8510437) B8510437
theorem B1910155 : Blo 587289 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B829225 : Blo 587289 829225 := bstep (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) B621919
theorem B2991977 : Blo 587289 2991977 := bstep (se 2 (by rfl) ⟨1121991, by rfl⟩ : syracuseStep 2991977 = 2243983) B2243983
theorem B5744567 : Blo 587289 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B993647 : Blo 587289 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B40905101 : Blo 587289 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B993863 : Blo 587289 993863 := bstep (se 1 (by rfl) ⟨745397, by rfl⟩ : syracuseStep 993863 = 1490795) B1490795
theorem B5024429 : Blo 587289 5024429 := bstep (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) B1884161
theorem B3353309 : Blo 587289 3353309 := bstep (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) B1257491
theorem B5745431 : Blo 587289 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B7154567 : Blo 587289 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B12888983 : Blo 587289 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B1321883 : Blo 587289 1321883 := bstep (se 1 (by rfl) ⟨991412, by rfl⟩ : syracuseStep 1321883 = 1982825) B1982825
theorem B6728669 : Blo 587289 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B994295 : Blo 587289 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B1322081 : Blo 587289 1322081 := bstep (se 2 (by rfl) ⟨495780, by rfl⟩ : syracuseStep 1322081 = 991561) B991561
theorem B3320947 : Blo 587289 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B1322279 : Blo 587289 1322279 := bstep (se 1 (by rfl) ⟨991709, by rfl⟩ : syracuseStep 1322279 = 1983419) B1983419
theorem B1060345 : Blo 587289 1060345 := bstep (se 2 (by rfl) ⟨397629, by rfl⟩ : syracuseStep 1060345 = 795259) B795259
theorem B2240081 : Blo 587289 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B2240095 : Blo 587289 2240095 := bstep (se 1 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 2240095 = 3360143) B3360143
theorem B1322657 : Blo 587289 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B995051 : Blo 587289 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B1486633 : Blo 587289 1486633 := bstep (se 2 (by rfl) ⟨557487, by rfl⟩ : syracuseStep 1486633 = 1114975) B1114975
theorem B798671 : Blo 587289 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B1323017 : Blo 587289 1323017 := bstep (se 2 (by rfl) ⟨496131, by rfl⟩ : syracuseStep 1323017 = 992263) B992263
theorem B2830355 : Blo 587289 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B16330817 : Blo 587289 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B3027203 : Blo 587289 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B1323431 : Blo 587289 1323431 := bstep (se 1 (by rfl) ⟨992573, by rfl⟩ : syracuseStep 1323431 = 1985147) B1985147
theorem B21475793 : Blo 587289 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B1323539 : Blo 587289 1323539 := bstep (se 1 (by rfl) ⟨992654, by rfl⟩ : syracuseStep 1323539 = 1985309) B1985309
theorem B1487423 : Blo 587289 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B1323593 : Blo 587289 1323593 := bstep (se 2 (by rfl) ⟨496347, by rfl⟩ : syracuseStep 1323593 = 992695) B992695
theorem B3781241 : Blo 587289 3781241 := bstep (se 2 (by rfl) ⟨1417965, by rfl⟩ : syracuseStep 3781241 = 2835931) B2835931
theorem B996023 : Blo 587289 996023 := bstep (se 1 (by rfl) ⟨747017, by rfl⟩ : syracuseStep 996023 = 1494035) B1494035
theorem B2864065 : Blo 587289 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1324007 : Blo 587289 1324007 := bstep (se 1 (by rfl) ⟨993005, by rfl⟩ : syracuseStep 1324007 = 1986011) B1986011
theorem B1488071 : Blo 587289 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B1488091 : Blo 587289 1488091 := bstep (se 1 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 1488091 = 2232137) B2232137
theorem B1324385 : Blo 587289 1324385 := bstep (se 2 (by rfl) ⟨496644, by rfl⟩ : syracuseStep 1324385 = 993289) B993289
theorem B996745 : Blo 587289 996745 := bstep (se 2 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 996745 = 747559) B747559
theorem B6370721 : Blo 587289 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B1324475 : Blo 587289 1324475 := bstep (se 1 (by rfl) ⟨993356, by rfl⟩ : syracuseStep 1324475 = 1986713) B1986713
theorem B1324601 : Blo 587289 1324601 := bstep (se 2 (by rfl) ⟨496725, by rfl⟩ : syracuseStep 1324601 = 993451) B993451
theorem B1619539 : Blo 587289 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B2832029 : Blo 587289 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B997177 : Blo 587289 997177 := bstep (se 2 (by rfl) ⟨373941, by rfl⟩ : syracuseStep 997177 = 747883) B747883
theorem B2242511 : Blo 587289 2242511 := bstep (se 1 (by rfl) ⟨1681883, by rfl⟩ : syracuseStep 2242511 = 3363767) B3363767
theorem B997481 : Blo 587289 997481 := bstep (se 2 (by rfl) ⟨374055, by rfl⟩ : syracuseStep 997481 = 748111) B748111
theorem B2275463 : Blo 587289 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B1325267 : Blo 587289 1325267 := bstep (se 1 (by rfl) ⟨993950, by rfl⟩ : syracuseStep 1325267 = 1987901) B1987901
theorem B1325321 : Blo 587289 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B1489225 : Blo 587289 1489225 := bstep (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) B1116919
theorem B1259849 : Blo 587289 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B1259867 : Blo 587289 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1325537 : Blo 587289 1325537 := bstep (se 2 (by rfl) ⟨497076, by rfl⟩ : syracuseStep 1325537 = 994153) B994153
theorem B1489529 : Blo 587289 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B1325843 : Blo 587289 1325843 := bstep (se 1 (by rfl) ⟨994382, by rfl⟩ : syracuseStep 1325843 = 1988765) B1988765
theorem B3193667 : Blo 587289 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B2243483 : Blo 587289 2243483 := bstep (se 1 (by rfl) ⟨1682612, by rfl⟩ : syracuseStep 2243483 = 3365225) B3365225
theorem B3357683 : Blo 587289 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B1326203 : Blo 587289 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1326329 : Blo 587289 1326329 := bstep (se 2 (by rfl) ⟨497373, by rfl⟩ : syracuseStep 1326329 = 994747) B994747
theorem B4767113 : Blo 587289 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B1326473 : Blo 587289 1326473 := bstep (se 2 (by rfl) ⟨497427, by rfl⟩ : syracuseStep 1326473 = 994855) B994855
theorem B1326599 : Blo 587289 1326599 := bstep (se 1 (by rfl) ⟨994949, by rfl⟩ : syracuseStep 1326599 = 1989899) B1989899
theorem B2244257 : Blo 587289 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B1326779 : Blo 587289 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B1326905 : Blo 587289 1326905 := bstep (se 2 (by rfl) ⟨497589, by rfl⟩ : syracuseStep 1326905 = 995179) B995179
theorem B2834585 : Blo 587289 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B2244955 : Blo 587289 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B1491311 : Blo 587289 1491311 := bstep (se 1 (by rfl) ⟨1118483, by rfl⟩ : syracuseStep 1491311 = 2236967) B2236967
theorem B3359141 : Blo 587289 3359141 := bstep (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) B629839
theorem B1327535 : Blo 587289 1327535 := bstep (se 1 (by rfl) ⟨995651, by rfl⟩ : syracuseStep 1327535 = 1991303) B1991303
theorem B1327571 : Blo 587289 1327571 := bstep (se 1 (by rfl) ⟨995678, by rfl⟩ : syracuseStep 1327571 = 1991357) B1991357
theorem B1327679 : Blo 587289 1327679 := bstep (se 1 (by rfl) ⟨995759, by rfl⟩ : syracuseStep 1327679 = 1991519) B1991519
theorem B3785287 : Blo 587289 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B1196651 : Blo 587289 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B1327787 : Blo 587289 1327787 := bstep (se 1 (by rfl) ⟨995840, by rfl⟩ : syracuseStep 1327787 = 1991681) B1991681
theorem B10175291 : Blo 587289 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1983311 : Blo 587289 1983311 := bstep (se 1 (by rfl) ⟨1487483, by rfl⟩ : syracuseStep 1983311 = 2974967) B2974967
theorem B1885007 : Blo 587289 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B3818435 : Blo 587289 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B2835431 : Blo 587289 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1491959 : Blo 587289 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1492091 : Blo 587289 1492091 := bstep (se 1 (by rfl) ⟨1119068, by rfl⟩ : syracuseStep 1492091 = 2238137) B2238137
theorem B1983635 : Blo 587289 1983635 := bstep (se 1 (by rfl) ⟨1487726, by rfl⟩ : syracuseStep 1983635 = 2975453) B2975453
theorem B1328327 : Blo 587289 1328327 := bstep (se 1 (by rfl) ⟨996245, by rfl⟩ : syracuseStep 1328327 = 1992491) B1992491
theorem B1328507 : Blo 587289 1328507 := bstep (se 1 (by rfl) ⟨996380, by rfl⟩ : syracuseStep 1328507 = 1992761) B1992761
theorem B1983905 : Blo 587289 1983905 := bstep (se 2 (by rfl) ⟨743964, by rfl⟩ : syracuseStep 1983905 = 1487929) B1487929
theorem B1328633 : Blo 587289 1328633 := bstep (se 2 (by rfl) ⟨498237, by rfl⟩ : syracuseStep 1328633 = 996475) B996475
theorem B1328723 : Blo 587289 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B1197755 : Blo 587289 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B1328903 : Blo 587289 1328903 := bstep (se 1 (by rfl) ⟨996677, by rfl⟩ : syracuseStep 1328903 = 1993355) B1993355
theorem B1591643 : Blo 587289 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B1329515 : Blo 587289 1329515 := bstep (se 1 (by rfl) ⟨997136, by rfl⟩ : syracuseStep 1329515 = 1994273) B1994273
theorem B1886647 : Blo 587289 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B1329659 : Blo 587289 1329659 := bstep (se 1 (by rfl) ⟨997244, by rfl⟩ : syracuseStep 1329659 = 1994489) B1994489
theorem B1886827 : Blo 587289 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B1329785 : Blo 587289 1329785 := bstep (se 2 (by rfl) ⟨498669, by rfl⟩ : syracuseStep 1329785 = 997339) B997339
theorem B1329839 : Blo 587289 1329839 := bstep (se 1 (by rfl) ⟨997379, by rfl⟩ : syracuseStep 1329839 = 1994759) B1994759
theorem B1329911 : Blo 587289 1329911 := bstep (se 1 (by rfl) ⟨997433, by rfl⟩ : syracuseStep 1329911 = 1994867) B1994867
theorem B1493903 : Blo 587289 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B1330091 : Blo 587289 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B1494409 : Blo 587289 1494409 := bstep (se 2 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 1494409 = 1120807) B1120807
theorem B1494521 : Blo 587289 1494521 := bstep (se 2 (by rfl) ⟨560445, by rfl⟩ : syracuseStep 1494521 = 1120891) B1120891
theorem B2543407 : Blo 587289 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B1495169 : Blo 587289 1495169 := bstep (se 2 (by rfl) ⟨560688, by rfl⟩ : syracuseStep 1495169 = 1121377) B1121377
theorem B5362157 : Blo 587289 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B1987091 : Blo 587289 1987091 := bstep (se 1 (by rfl) ⟨1490318, by rfl⟩ : syracuseStep 1987091 = 2980637) B2980637
theorem B807727 : Blo 587289 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B1495979 : Blo 587289 1495979 := bstep (se 1 (by rfl) ⟨1121984, by rfl⟩ : syracuseStep 1495979 = 2243969) B2243969
theorem B1430747 : Blo 587289 1430747 := bstep (se 1 (by rfl) ⟨1073060, by rfl⟩ : syracuseStep 1430747 = 2146121) B2146121
theorem B4773113 : Blo 587289 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B1889659 : Blo 587289 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B710251 : Blo 587289 710251 := bstep (se 1 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 710251 = 1065377) B1065377
theorem B2512727 : Blo 587289 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B2840503 : Blo 587289 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B710875 : Blo 587289 710875 := bstep (se 1 (by rfl) ⟨533156, by rfl⟩ : syracuseStep 710875 = 1066313) B1066313
theorem B1595645 : Blo 587289 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B1988873 : Blo 587289 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B2513531 : Blo 587289 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B7527107 : Blo 587289 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B2513683 : Blo 587289 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B5659865 : Blo 587289 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B744815 : Blo 587289 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B1990007 : Blo 587289 1990007 := bstep (se 1 (by rfl) ⟨1492505, by rfl⟩ : syracuseStep 1990007 = 2985011) B2985011
theorem B28761479 : Blo 587289 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1891721 : Blo 587289 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B744871 : Blo 587289 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B745195 : Blo 587289 745195 := bstep (se 1 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 745195 = 1117793) B1117793
theorem B7561349 : Blo 587289 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B1991087 : Blo 587289 1991087 := bstep (se 1 (by rfl) ⟨1493315, by rfl⟩ : syracuseStep 1991087 = 2986631) B2986631
theorem B1794479 : Blo 587289 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B4842155 : Blo 587289 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B746167 : Blo 587289 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B943247 : Blo 587289 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B2122985 : Blo 587289 2122985 := bstep (se 2 (by rfl) ⟨796119, by rfl⟩ : syracuseStep 2122985 = 1592239) B1592239
theorem B1992059 : Blo 587289 1992059 := bstep (se 1 (by rfl) ⟨1494044, by rfl⟩ : syracuseStep 1992059 = 2988089) B2988089
theorem B943913 : Blo 587289 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B2975777 : Blo 587289 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B2975939 : Blo 587289 2975939 := bstep (se 1 (by rfl) ⟨2231954, by rfl⟩ : syracuseStep 2975939 = 4463909) B4463909
theorem B1796681 : Blo 587289 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B748207 : Blo 587289 748207 := bstep (se 1 (by rfl) ⟨561155, by rfl⟩ : syracuseStep 748207 = 1122311) B1122311
theorem B1993463 : Blo 587289 1993463 := bstep (se 1 (by rfl) ⟨1495097, by rfl⟩ : syracuseStep 1993463 = 2990195) B2990195
theorem B11332487 : Blo 587289 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B5663783 : Blo 587289 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B4255105 : Blo 587289 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B1994543 : Blo 587289 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B881063 : Blo 587289 881063 := bstep (se 1 (by rfl) ⟨660797, by rfl⟩ : syracuseStep 881063 = 1321595) B1321595
theorem B881147 : Blo 587289 881147 := bstep (se 1 (by rfl) ⟨660860, by rfl⟩ : syracuseStep 881147 = 1321721) B1321721
theorem B3174983 : Blo 587289 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B2552417 : Blo 587289 2552417 := bstep (se 2 (by rfl) ⟨957156, by rfl⟩ : syracuseStep 2552417 = 1914313) B1914313
theorem B881273 : Blo 587289 881273 := bstep (se 2 (by rfl) ⟨330477, by rfl⟩ : syracuseStep 881273 = 660955) B660955
theorem B881327 : Blo 587289 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B881375 : Blo 587289 881375 := bstep (se 1 (by rfl) ⟨661031, by rfl⟩ : syracuseStep 881375 = 1322063) B1322063
theorem B2519903 : Blo 587289 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B881639 : Blo 587289 881639 := bstep (se 1 (by rfl) ⟨661229, by rfl⟩ : syracuseStep 881639 = 1322459) B1322459
theorem B881897 : Blo 587289 881897 := bstep (se 2 (by rfl) ⟨330711, by rfl⟩ : syracuseStep 881897 = 661423) B661423
theorem B881951 : Blo 587289 881951 := bstep (se 1 (by rfl) ⟨661463, by rfl⟩ : syracuseStep 881951 = 1322927) B1322927
theorem B1340833 : Blo 587289 1340833 := bstep (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) B1005625
theorem B882119 : Blo 587289 882119 := bstep (se 1 (by rfl) ⟨661589, by rfl⟩ : syracuseStep 882119 = 1323179) B1323179
theorem B587327 : Blo 587289 587327 := bstep (se 1 (by rfl) ⟨440495, by rfl⟩ : syracuseStep 587327 = 880991) B880991
theorem B587335 : Blo 587289 587335 := bstep (se 1 (by rfl) ⟨440501, by rfl⟩ : syracuseStep 587335 = 881003) B881003
theorem B587487 : Blo 587289 587487 := bstep (se 1 (by rfl) ⟨440615, by rfl⟩ : syracuseStep 587487 = 881231) B881231
theorem B882473 : Blo 587289 882473 := bstep (se 2 (by rfl) ⟨330927, by rfl⟩ : syracuseStep 882473 = 661855) B661855
theorem B587567 : Blo 587289 587567 := bstep (se 1 (by rfl) ⟨440675, by rfl⟩ : syracuseStep 587567 = 881351) B881351
theorem B882479 : Blo 587289 882479 := bstep (se 1 (by rfl) ⟨661859, by rfl⟩ : syracuseStep 882479 = 1323719) B1323719
theorem B2979665 : Blo 587289 2979665 := bstep (se 2 (by rfl) ⟨1117374, by rfl⟩ : syracuseStep 2979665 = 2234749) B2234749
theorem B1341289 : Blo 587289 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B587675 : Blo 587289 587675 := bstep (se 1 (by rfl) ⟨440756, by rfl⟩ : syracuseStep 587675 = 881513) B881513
theorem B587727 : Blo 587289 587727 := bstep (se 1 (by rfl) ⟨440795, by rfl⟩ : syracuseStep 587727 = 881591) B881591
theorem B587751 : Blo 587289 587751 := bstep (se 1 (by rfl) ⟨440813, by rfl⟩ : syracuseStep 587751 = 881627) B881627
theorem B882953 : Blo 587289 882953 := bstep (se 2 (by rfl) ⟨331107, by rfl⟩ : syracuseStep 882953 = 662215) B662215
theorem B588063 : Blo 587289 588063 := bstep (se 1 (by rfl) ⟨441047, by rfl⟩ : syracuseStep 588063 = 882095) B882095
theorem B588123 : Blo 587289 588123 := bstep (se 1 (by rfl) ⟨441092, by rfl⟩ : syracuseStep 588123 = 882185) B882185
theorem B588143 : Blo 587289 588143 := bstep (se 1 (by rfl) ⟨441107, by rfl⟩ : syracuseStep 588143 = 882215) B882215
theorem B883055 : Blo 587289 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B588199 : Blo 587289 588199 := bstep (se 1 (by rfl) ⟨441149, by rfl⟩ : syracuseStep 588199 = 882299) B882299
theorem B588283 : Blo 587289 588283 := bstep (se 1 (by rfl) ⟨441212, by rfl⟩ : syracuseStep 588283 = 882425) B882425
theorem B1341947 : Blo 587289 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B588351 : Blo 587289 588351 := bstep (se 1 (by rfl) ⟨441263, by rfl⟩ : syracuseStep 588351 = 882527) B882527
theorem B2128447 : Blo 587289 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B588359 : Blo 587289 588359 := bstep (se 1 (by rfl) ⟨441269, by rfl⟩ : syracuseStep 588359 = 882539) B882539
theorem B883271 : Blo 587289 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B883307 : Blo 587289 883307 := bstep (se 1 (by rfl) ⟨662480, by rfl⟩ : syracuseStep 883307 = 1324961) B1324961
theorem B2980475 : Blo 587289 2980475 := bstep (se 1 (by rfl) ⟨2235356, by rfl⟩ : syracuseStep 2980475 = 4470713) B4470713
theorem B8518283 : Blo 587289 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B588511 : Blo 587289 588511 := bstep (se 1 (by rfl) ⟨441383, by rfl⟩ : syracuseStep 588511 = 882767) B882767
theorem B588591 : Blo 587289 588591 := bstep (se 1 (by rfl) ⟨441443, by rfl⟩ : syracuseStep 588591 = 882887) B882887
theorem B883535 : Blo 587289 883535 := bstep (se 1 (by rfl) ⟨662651, by rfl⟩ : syracuseStep 883535 = 1325303) B1325303
theorem B588699 : Blo 587289 588699 := bstep (se 1 (by rfl) ⟨441524, by rfl⟩ : syracuseStep 588699 = 883049) B883049
theorem B588751 : Blo 587289 588751 := bstep (se 1 (by rfl) ⟨441563, by rfl⟩ : syracuseStep 588751 = 883127) B883127
theorem B588775 : Blo 587289 588775 := bstep (se 1 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 588775 = 883163) B883163
theorem B2554895 : Blo 587289 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B883931 : Blo 587289 883931 := bstep (se 1 (by rfl) ⟨662948, by rfl⟩ : syracuseStep 883931 = 1325897) B1325897
theorem B589087 : Blo 587289 589087 := bstep (se 1 (by rfl) ⟨441815, by rfl⟩ : syracuseStep 589087 = 883631) B883631
theorem B589147 : Blo 587289 589147 := bstep (se 1 (by rfl) ⟨441860, by rfl⟩ : syracuseStep 589147 = 883721) B883721
theorem B589167 : Blo 587289 589167 := bstep (se 1 (by rfl) ⟨441875, by rfl⟩ : syracuseStep 589167 = 883751) B883751
theorem B884105 : Blo 587289 884105 := bstep (se 2 (by rfl) ⟨331539, by rfl⟩ : syracuseStep 884105 = 663079) B663079
theorem B589223 : Blo 587289 589223 := bstep (se 1 (by rfl) ⟨441917, by rfl⟩ : syracuseStep 589223 = 883835) B883835
theorem B589307 : Blo 587289 589307 := bstep (se 1 (by rfl) ⟨441980, by rfl⟩ : syracuseStep 589307 = 883961) B883961
theorem B589375 : Blo 587289 589375 := bstep (se 1 (by rfl) ⟨442031, by rfl⟩ : syracuseStep 589375 = 884063) B884063
theorem B589383 : Blo 587289 589383 := bstep (se 1 (by rfl) ⟨442037, by rfl⟩ : syracuseStep 589383 = 884075) B884075
theorem B589535 : Blo 587289 589535 := bstep (se 1 (by rfl) ⟨442151, by rfl⟩ : syracuseStep 589535 = 884303) B884303
theorem B884459 : Blo 587289 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B589615 : Blo 587289 589615 := bstep (se 1 (by rfl) ⟨442211, by rfl⟩ : syracuseStep 589615 = 884423) B884423
theorem B589723 : Blo 587289 589723 := bstep (se 1 (by rfl) ⟨442292, by rfl⟩ : syracuseStep 589723 = 884585) B884585
theorem B589775 : Blo 587289 589775 := bstep (se 1 (by rfl) ⟨442331, by rfl⟩ : syracuseStep 589775 = 884663) B884663
theorem B884687 : Blo 587289 884687 := bstep (se 1 (by rfl) ⟨663515, by rfl⟩ : syracuseStep 884687 = 1327031) B1327031
theorem B589799 : Blo 587289 589799 := bstep (se 1 (by rfl) ⟨442349, by rfl⟩ : syracuseStep 589799 = 884699) B884699
theorem B590055 : Blo 587289 590055 := bstep (se 1 (by rfl) ⟨442541, by rfl⟩ : syracuseStep 590055 = 885083) B885083
theorem B885023 : Blo 587289 885023 := bstep (se 1 (by rfl) ⟨663767, by rfl⟩ : syracuseStep 885023 = 1327535) B1327535
theorem B885047 : Blo 587289 885047 := bstep (se 1 (by rfl) ⟨663785, by rfl⟩ : syracuseStep 885047 = 1327571) B1327571
theorem B885119 : Blo 587289 885119 := bstep (se 1 (by rfl) ⟨663839, by rfl⟩ : syracuseStep 885119 = 1327679) B1327679
theorem B590207 : Blo 587289 590207 := bstep (se 1 (by rfl) ⟨442655, by rfl⟩ : syracuseStep 590207 = 885311) B885311
theorem B885191 : Blo 587289 885191 := bstep (se 1 (by rfl) ⟨663893, by rfl⟩ : syracuseStep 885191 = 1327787) B1327787
theorem B590287 : Blo 587289 590287 := bstep (se 1 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 590287 = 885431) B885431
theorem B6783527 : Blo 587289 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B590439 : Blo 587289 590439 := bstep (se 1 (by rfl) ⟨442829, by rfl⟩ : syracuseStep 590439 = 885659) B885659
theorem B5047049 : Blo 587289 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B885545 : Blo 587289 885545 := bstep (se 2 (by rfl) ⟨332079, by rfl⟩ : syracuseStep 885545 = 664159) B664159
theorem B885551 : Blo 587289 885551 := bstep (se 1 (by rfl) ⟨664163, by rfl⟩ : syracuseStep 885551 = 1328327) B1328327
theorem B590703 : Blo 587289 590703 := bstep (se 1 (by rfl) ⟨443027, by rfl⟩ : syracuseStep 590703 = 886055) B886055
theorem B2950031 : Blo 587289 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B885671 : Blo 587289 885671 := bstep (se 1 (by rfl) ⟨664253, by rfl⟩ : syracuseStep 885671 = 1328507) B1328507
theorem B590759 : Blo 587289 590759 := bstep (se 1 (by rfl) ⟨443069, by rfl⟩ : syracuseStep 590759 = 886139) B886139
theorem B885755 : Blo 587289 885755 := bstep (se 1 (by rfl) ⟨664316, by rfl⟩ : syracuseStep 885755 = 1328633) B1328633
theorem B590843 : Blo 587289 590843 := bstep (se 1 (by rfl) ⟨443132, by rfl⟩ : syracuseStep 590843 = 886265) B886265
theorem B885815 : Blo 587289 885815 := bstep (se 1 (by rfl) ⟨664361, by rfl⟩ : syracuseStep 885815 = 1328723) B1328723
theorem B590911 : Blo 587289 590911 := bstep (se 1 (by rfl) ⟨443183, by rfl⟩ : syracuseStep 590911 = 886367) B886367
theorem B4785277 : Blo 587289 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B885935 : Blo 587289 885935 := bstep (se 1 (by rfl) ⟨664451, by rfl⟩ : syracuseStep 885935 = 1328903) B1328903
theorem B591055 : Blo 587289 591055 := bstep (se 1 (by rfl) ⟨443291, by rfl⟩ : syracuseStep 591055 = 886583) B886583
theorem B591259 : Blo 587289 591259 := bstep (se 1 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 591259 = 886889) B886889
theorem B886343 : Blo 587289 886343 := bstep (se 1 (by rfl) ⟨664757, by rfl⟩ : syracuseStep 886343 = 1329515) B1329515
theorem B2229875 : Blo 587289 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B886439 : Blo 587289 886439 := bstep (se 1 (by rfl) ⟨664829, by rfl⟩ : syracuseStep 886439 = 1329659) B1329659
theorem B886523 : Blo 587289 886523 := bstep (se 1 (by rfl) ⟨664892, by rfl⟩ : syracuseStep 886523 = 1329785) B1329785
theorem B886559 : Blo 587289 886559 := bstep (se 1 (by rfl) ⟨664919, by rfl⟩ : syracuseStep 886559 = 1329839) B1329839
theorem B886607 : Blo 587289 886607 := bstep (se 1 (by rfl) ⟨664955, by rfl⟩ : syracuseStep 886607 = 1329911) B1329911
theorem B886727 : Blo 587289 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B5376617 : Blo 587289 5376617 := bstep (se 2 (by rfl) ⟨2016231, by rfl⟩ : syracuseStep 5376617 = 4032463) B4032463
theorem B953831 : Blo 587289 953831 := bstep (se 1 (by rfl) ⟨715373, by rfl⟩ : syracuseStep 953831 = 1430747) B1430747
theorem B3182075 : Blo 587289 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B1675151 : Blo 587289 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B4427929 : Blo 587289 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B1675687 : Blo 587289 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B5018071 : Blo 587289 5018071 := bstep (se 1 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 5018071 = 7527107) B7527107
theorem B2232791 : Blo 587289 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B5673473 : Blo 587289 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B1413793 : Blo 587289 1413793 := bstep (se 2 (by rfl) ⟨530172, by rfl⟩ : syracuseStep 1413793 = 1060345) B1060345
theorem B2986793 : Blo 587289 2986793 := bstep (se 2 (by rfl) ⟨1120047, by rfl⟩ : syracuseStep 2986793 = 2240095) B2240095
theorem B3773243 : Blo 587289 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B19174319 : Blo 587289 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B7148483 : Blo 587289 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B661243 : Blo 587289 661243 := bstep (se 1 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 661243 = 991865) B991865
theorem B661279 : Blo 587289 661279 := bstep (se 1 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 661279 = 991919) B991919
theorem B1120063 : Blo 587289 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B628831 : Blo 587289 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B1415323 : Blo 587289 1415323 := bstep (se 1 (by rfl) ⟨1061492, by rfl⟩ : syracuseStep 1415323 = 2122985) B2122985
theorem B2234567 : Blo 587289 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B3578525 : Blo 587289 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B4791149 : Blo 587289 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B662431 : Blo 587289 662431 := bstep (se 1 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 662431 = 993647) B993647
theorem B662575 : Blo 587289 662575 := bstep (se 1 (by rfl) ⟨496931, by rfl⟩ : syracuseStep 662575 = 993863) B993863
theorem B3349619 : Blo 587289 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B2235539 : Blo 587289 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B8592655 : Blo 587289 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B662863 : Blo 587289 662863 := bstep (se 1 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 662863 = 994295) B994295
theorem B663367 : Blo 587289 663367 := bstep (se 1 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 663367 = 995051) B995051
theorem B10887211 : Blo 587289 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B991615 : Blo 587289 991615 := bstep (se 1 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 991615 = 1487423) B1487423
theorem B664015 : Blo 587289 664015 := bstep (se 1 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 664015 = 996023) B996023
theorem B1679935 : Blo 587289 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B992047 : Blo 587289 992047 := bstep (se 1 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 992047 = 1488071) B1488071
theorem B3351577 : Blo 587289 3351577 := bstep (se 2 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 3351577 = 2513683) B2513683
theorem B4465853 : Blo 587289 4465853 := bstep (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) B1674695
theorem B664987 : Blo 587289 664987 := bstep (se 1 (by rfl) ⟨498740, by rfl⟩ : syracuseStep 664987 = 997481) B997481
theorem B1516975 : Blo 587289 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B993019 : Blo 587289 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B5678855 : Blo 587289 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B7153541 : Blo 587289 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B993161 : Blo 587289 993161 := bstep (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) B744871
theorem B2238455 : Blo 587289 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B993593 : Blo 587289 993593 := bstep (se 2 (by rfl) ⟨372597, by rfl⟩ : syracuseStep 993593 = 745195) B745195
theorem B1321577 : Blo 587289 1321577 := bstep (se 2 (by rfl) ⟨495591, by rfl⟩ : syracuseStep 1321577 = 991183) B991183
theorem B895835 : Blo 587289 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B994207 : Blo 587289 994207 := bstep (se 1 (by rfl) ⟨745655, by rfl⟩ : syracuseStep 994207 = 1491311) B1491311
theorem B4303811 : Blo 587289 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B2239427 : Blo 587289 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B2239609 : Blo 587289 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B2993273 : Blo 587289 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B1322207 : Blo 587289 1322207 := bstep (se 1 (by rfl) ⟨991655, by rfl⟩ : syracuseStep 1322207 = 1983311) B1983311
theorem B1256671 : Blo 587289 1256671 := bstep (se 1 (by rfl) ⟨942503, by rfl⟩ : syracuseStep 1256671 = 1885007) B1885007
theorem B994639 : Blo 587289 994639 := bstep (se 1 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 994639 = 1491959) B1491959
theorem B994727 : Blo 587289 994727 := bstep (se 1 (by rfl) ⟨746045, by rfl⟩ : syracuseStep 994727 = 1492091) B1492091
theorem B1322423 : Blo 587289 1322423 := bstep (se 1 (by rfl) ⟨991817, by rfl⟩ : syracuseStep 1322423 = 1983635) B1983635
theorem B994889 : Blo 587289 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B1322603 : Blo 587289 1322603 := bstep (se 1 (by rfl) ⟨991952, by rfl⟩ : syracuseStep 1322603 = 1983905) B1983905
theorem B798503 : Blo 587289 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B1322873 : Blo 587289 1322873 := bstep (se 2 (by rfl) ⟨496077, by rfl⟩ : syracuseStep 1322873 = 992155) B992155
theorem B14299085 : Blo 587289 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B32157647 : Blo 587289 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B1683443 : Blo 587289 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B1061095 : Blo 587289 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B3191069 : Blo 587289 3191069 := bstep (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) B1196651
theorem B1487231 : Blo 587289 1487231 := bstep (se 1 (by rfl) ⟨1115423, by rfl⟩ : syracuseStep 1487231 = 2230847) B2230847
theorem B6730127 : Blo 587289 6730127 := bstep (se 1 (by rfl) ⟨5047595, by rfl⟩ : syracuseStep 6730127 = 10095191) B10095191
theorem B34550165 : Blo 587289 34550165 := bstep (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) B1619539
theorem B1487443 : Blo 587289 1487443 := bstep (se 1 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 1487443 = 2231165) B2231165
theorem B995935 : Blo 587289 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B5092055 : Blo 587289 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B996347 : Blo 587289 996347 := bstep (se 1 (by rfl) ⟨747260, by rfl⟩ : syracuseStep 996347 = 1494521) B1494521
theorem B996779 : Blo 587289 996779 := bstep (se 1 (by rfl) ⟨747584, by rfl⟩ : syracuseStep 996779 = 1495169) B1495169
theorem B1324727 : Blo 587289 1324727 := bstep (se 1 (by rfl) ⟨993545, by rfl⟩ : syracuseStep 1324727 = 1987091) B1987091
theorem B3192713 : Blo 587289 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B997319 : Blo 587289 997319 := bstep (se 1 (by rfl) ⟨747989, by rfl⟩ : syracuseStep 997319 = 1495979) B1495979
theorem B997609 : Blo 587289 997609 := bstep (se 2 (by rfl) ⟨374103, by rfl⟩ : syracuseStep 997609 = 748207) B748207
theorem B6699509 : Blo 587289 6699509 := bstep (se 5 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 6699509 = 628079) B628079
theorem B9681731 : Blo 587289 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B1063763 : Blo 587289 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1325915 : Blo 587289 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B28425107 : Blo 587289 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B1489823 : Blo 587289 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B1326671 : Blo 587289 1326671 := bstep (se 1 (by rfl) ⟨995003, by rfl⟩ : syracuseStep 1326671 = 1990007) B1990007
theorem B1982177 : Blo 587289 1982177 := bstep (se 2 (by rfl) ⟨743316, by rfl⟩ : syracuseStep 1982177 = 1486633) B1486633
theorem B15318845 : Blo 587289 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B1327391 : Blo 587289 1327391 := bstep (se 1 (by rfl) ⟨995543, by rfl⟩ : syracuseStep 1327391 = 1991087) B1991087
theorem B27181403 : Blo 587289 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B3228103 : Blo 587289 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B1328039 : Blo 587289 1328039 := bstep (se 1 (by rfl) ⟨996029, by rfl⟩ : syracuseStep 1328039 = 1992059) B1992059
theorem B3818753 : Blo 587289 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1983851 : Blo 587289 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B1983959 : Blo 587289 1983959 := bstep (se 1 (by rfl) ⟨1487969, by rfl⟩ : syracuseStep 1983959 = 2975939) B2975939
theorem B1984121 : Blo 587289 1984121 := bstep (se 2 (by rfl) ⟨744045, by rfl⟩ : syracuseStep 1984121 = 1488091) B1488091
theorem B1328975 : Blo 587289 1328975 := bstep (se 1 (by rfl) ⟨996731, by rfl⟩ : syracuseStep 1328975 = 1993463) B1993463
theorem B1328993 : Blo 587289 1328993 := bstep (se 2 (by rfl) ⟨498372, by rfl⟩ : syracuseStep 1328993 = 996745) B996745
theorem B1787777 : Blo 587289 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B4769711 : Blo 587289 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B7554991 : Blo 587289 7554991 := bstep (se 1 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 7554991 = 11332487) B11332487
theorem B1493387 : Blo 587289 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B1329569 : Blo 587289 1329569 := bstep (se 2 (by rfl) ⟨498588, by rfl⟩ : syracuseStep 1329569 = 997177) B997177
theorem B1329695 : Blo 587289 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B3787337 : Blo 587289 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B1886903 : Blo 587289 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B2018135 : Blo 587289 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B2116655 : Blo 587289 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B1985633 : Blo 587289 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B3788005 : Blo 587289 3788005 := bstep (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) B710251
theorem B2837929 : Blo 587289 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B30690893 : Blo 587289 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B4247147 : Blo 587289 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B1986173 : Blo 587289 1986173 := bstep (se 3 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 1986173 = 744815) B744815
theorem B1888019 : Blo 587289 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B1986443 : Blo 587289 1986443 := bstep (se 1 (by rfl) ⟨1489832, by rfl⟩ : syracuseStep 1986443 = 2979665) B2979665
theorem B1495007 : Blo 587289 1495007 := bstep (se 1 (by rfl) ⟨1121255, by rfl⟩ : syracuseStep 1495007 = 2242511) B2242511
theorem B839899 : Blo 587289 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B839911 : Blo 587289 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B16961825 : Blo 587289 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B1986983 : Blo 587289 1986983 := bstep (se 1 (by rfl) ⟨1490237, by rfl⟩ : syracuseStep 1986983 = 2980475) B2980475
theorem B1495655 : Blo 587289 1495655 := bstep (se 1 (by rfl) ⟨1121741, by rfl⟩ : syracuseStep 1495655 = 2243483) B2243483
theorem B11326337 : Blo 587289 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B1496171 : Blo 587289 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B1889723 : Blo 587289 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B1988279 : Blo 587289 1988279 := bstep (se 1 (by rfl) ⟨1491209, by rfl⟩ : syracuseStep 1988279 = 2982419) B2982419
theorem B1890287 : Blo 587289 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B743519 : Blo 587289 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B3824047 : Blo 587289 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B3791333 : Blo 587289 3791333 := bstep (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) B710875
theorem B1989467 : Blo 587289 1989467 := bstep (se 1 (by rfl) ⟨1492100, by rfl⟩ : syracuseStep 1989467 = 2984201) B2984201
theorem B4545505 : Blo 587289 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B15129665 : Blo 587289 15129665 := bstep (se 2 (by rfl) ⟨5673624, by rfl⟩ : syracuseStep 15129665 = 11347249) B11347249
theorem B2546873 : Blo 587289 2546873 := bstep (se 2 (by rfl) ⟨955077, by rfl⟩ : syracuseStep 2546873 = 1910155) B1910155
theorem B1990223 : Blo 587289 1990223 := bstep (se 1 (by rfl) ⟨1492667, by rfl⟩ : syracuseStep 1990223 = 2985335) B2985335
theorem B1990331 : Blo 587289 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B1105633 : Blo 587289 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B941863 : Blo 587289 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B2121527 : Blo 587289 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B10182493 : Blo 587289 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B4481405 : Blo 587289 4481405 := bstep (se 3 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 4481405 = 1680527) B1680527
theorem B2515529 : Blo 587289 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B7168621 : Blo 587289 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B5661323 : Blo 587289 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B2515769 : Blo 587289 2515769 := bstep (se 2 (by rfl) ⟨943413, by rfl⟩ : syracuseStep 2515769 = 1886827) B1886827
theorem B746491 : Blo 587289 746491 := bstep (se 1 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 746491 = 1119737) B1119737
theorem B2975291 : Blo 587289 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1992275 : Blo 587289 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B1992545 : Blo 587289 1992545 := bstep (se 2 (by rfl) ⟨747204, by rfl⟩ : syracuseStep 1992545 = 1494409) B1494409
theorem B747463 : Blo 587289 747463 := bstep (se 1 (by rfl) ⟨560597, by rfl⟩ : syracuseStep 747463 = 1121195) B1121195
theorem B2517101 : Blo 587289 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B1993247 : Blo 587289 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B4025015 : Blo 587289 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B7170763 : Blo 587289 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B5040899 : Blo 587289 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B944951 : Blo 587289 944951 := bstep (se 1 (by rfl) ⟨708713, by rfl⟩ : syracuseStep 944951 = 1417427) B1417427
theorem B2976911 : Blo 587289 2976911 := bstep (se 1 (by rfl) ⟨2232683, by rfl⟩ : syracuseStep 2976911 = 4465367) B4465367
theorem B109080269 : Blo 587289 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B1076969 : Blo 587289 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B1994651 : Blo 587289 1994651 := bstep (se 1 (by rfl) ⟨1495988, by rfl⟩ : syracuseStep 1994651 = 2991977) B2991977
theorem B881033 : Blo 587289 881033 := bstep (se 2 (by rfl) ⟨330387, by rfl⟩ : syracuseStep 881033 = 660775) B660775
theorem B881129 : Blo 587289 881129 := bstep (se 2 (by rfl) ⟨330423, by rfl⟩ : syracuseStep 881129 = 660847) B660847
theorem B2519545 : Blo 587289 2519545 := bstep (se 2 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 2519545 = 1889659) B1889659
theorem B3830287 : Blo 587289 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B881255 : Blo 587289 881255 := bstep (se 1 (by rfl) ⟨660941, by rfl⟩ : syracuseStep 881255 = 1321883) B1321883
theorem B4485779 : Blo 587289 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B881387 : Blo 587289 881387 := bstep (se 1 (by rfl) ⟨661040, by rfl⟩ : syracuseStep 881387 = 1322081) B1322081
theorem B881417 : Blo 587289 881417 := bstep (se 2 (by rfl) ⟨330531, by rfl⟩ : syracuseStep 881417 = 661063) B661063
theorem B881519 : Blo 587289 881519 := bstep (se 1 (by rfl) ⟨661139, by rfl⟩ : syracuseStep 881519 = 1322279) B1322279
theorem B881771 : Blo 587289 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B882011 : Blo 587289 882011 := bstep (se 1 (by rfl) ⟨661508, by rfl⟩ : syracuseStep 882011 = 1323017) B1323017
theorem B15103421 : Blo 587289 15103421 := bstep (se 3 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 15103421 = 5663783) B5663783
theorem B587375 : Blo 587289 587375 := bstep (se 1 (by rfl) ⟨440531, by rfl⟩ : syracuseStep 587375 = 881063) B881063
theorem B882287 : Blo 587289 882287 := bstep (se 1 (by rfl) ⟨661715, by rfl⟩ : syracuseStep 882287 = 1323431) B1323431
theorem B14317195 : Blo 587289 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B587431 : Blo 587289 587431 := bstep (se 1 (by rfl) ⟨440573, by rfl⟩ : syracuseStep 587431 = 881147) B881147
theorem B882359 : Blo 587289 882359 := bstep (se 1 (by rfl) ⟨661769, by rfl⟩ : syracuseStep 882359 = 1323539) B1323539
theorem B882395 : Blo 587289 882395 := bstep (se 1 (by rfl) ⟨661796, by rfl⟩ : syracuseStep 882395 = 1323593) B1323593
theorem B1701611 : Blo 587289 1701611 := bstep (se 1 (by rfl) ⟨1276208, by rfl⟩ : syracuseStep 1701611 = 2552417) B2552417
theorem B587515 : Blo 587289 587515 := bstep (se 1 (by rfl) ⟨440636, by rfl⟩ : syracuseStep 587515 = 881273) B881273
theorem B2520827 : Blo 587289 2520827 := bstep (se 1 (by rfl) ⟨1890620, by rfl⟩ : syracuseStep 2520827 = 3781241) B3781241
theorem B587551 : Blo 587289 587551 := bstep (se 1 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 587551 = 881327) B881327
theorem B587583 : Blo 587289 587583 := bstep (se 1 (by rfl) ⟨440687, by rfl⟩ : syracuseStep 587583 = 881375) B881375
theorem B882569 : Blo 587289 882569 := bstep (se 2 (by rfl) ⟨330963, by rfl⟩ : syracuseStep 882569 = 661927) B661927
theorem B587759 : Blo 587289 587759 := bstep (se 1 (by rfl) ⟨440819, by rfl⟩ : syracuseStep 587759 = 881639) B881639
theorem B882671 : Blo 587289 882671 := bstep (se 1 (by rfl) ⟨662003, by rfl⟩ : syracuseStep 882671 = 1324007) B1324007
theorem B587931 : Blo 587289 587931 := bstep (se 1 (by rfl) ⟨440948, by rfl⟩ : syracuseStep 587931 = 881897) B881897
theorem B587967 : Blo 587289 587967 := bstep (se 1 (by rfl) ⟨440975, by rfl⟩ : syracuseStep 587967 = 881951) B881951
theorem B882923 : Blo 587289 882923 := bstep (se 1 (by rfl) ⟨662192, by rfl⟩ : syracuseStep 882923 = 1324385) B1324385
theorem B882983 : Blo 587289 882983 := bstep (se 1 (by rfl) ⟨662237, by rfl⟩ : syracuseStep 882983 = 1324475) B1324475
theorem B588079 : Blo 587289 588079 := bstep (se 1 (by rfl) ⟨441059, by rfl⟩ : syracuseStep 588079 = 882119) B882119
theorem B12712301 : Blo 587289 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B5044589 : Blo 587289 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B883067 : Blo 587289 883067 := bstep (se 1 (by rfl) ⟨662300, by rfl⟩ : syracuseStep 883067 = 1324601) B1324601
theorem B588315 : Blo 587289 588315 := bstep (se 1 (by rfl) ⟨441236, by rfl⟩ : syracuseStep 588315 = 882473) B882473
theorem B588319 : Blo 587289 588319 := bstep (se 1 (by rfl) ⟨441239, by rfl⟩ : syracuseStep 588319 = 882479) B882479
theorem B883337 : Blo 587289 883337 := bstep (se 2 (by rfl) ⟨331251, by rfl⟩ : syracuseStep 883337 = 662503) B662503
theorem B883511 : Blo 587289 883511 := bstep (se 1 (by rfl) ⟨662633, by rfl⟩ : syracuseStep 883511 = 1325267) B1325267
theorem B588635 : Blo 587289 588635 := bstep (se 1 (by rfl) ⟨441476, by rfl⟩ : syracuseStep 588635 = 882953) B882953
theorem B883547 : Blo 587289 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B588703 : Blo 587289 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B13564837 : Blo 587289 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B883691 : Blo 587289 883691 := bstep (se 1 (by rfl) ⟨662768, by rfl⟩ : syracuseStep 883691 = 1325537) B1325537
theorem B588847 : Blo 587289 588847 := bstep (se 1 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 588847 = 883271) B883271
theorem B588871 : Blo 587289 588871 := bstep (se 1 (by rfl) ⟨441653, by rfl⟩ : syracuseStep 588871 = 883307) B883307
theorem B883895 : Blo 587289 883895 := bstep (se 1 (by rfl) ⟨662921, by rfl⟩ : syracuseStep 883895 = 1325843) B1325843
theorem B2129111 : Blo 587289 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B589023 : Blo 587289 589023 := bstep (se 1 (by rfl) ⟨441767, by rfl⟩ : syracuseStep 589023 = 883535) B883535
theorem B1703263 : Blo 587289 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B884135 : Blo 587289 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B589287 : Blo 587289 589287 := bstep (se 1 (by rfl) ⟨441965, by rfl⟩ : syracuseStep 589287 = 883931) B883931
theorem B884219 : Blo 587289 884219 := bstep (se 1 (by rfl) ⟨663164, by rfl⟩ : syracuseStep 884219 = 1326329) B1326329
theorem B589403 : Blo 587289 589403 := bstep (se 1 (by rfl) ⟨442052, by rfl⟩ : syracuseStep 589403 = 884105) B884105
theorem B884315 : Blo 587289 884315 := bstep (se 1 (by rfl) ⟨663236, by rfl⟩ : syracuseStep 884315 = 1326473) B1326473
theorem B884399 : Blo 587289 884399 := bstep (se 1 (by rfl) ⟨663299, by rfl⟩ : syracuseStep 884399 = 1326599) B1326599
theorem B2981609 : Blo 587289 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B884519 : Blo 587289 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B589639 : Blo 587289 589639 := bstep (se 1 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 589639 = 884459) B884459
theorem B884603 : Blo 587289 884603 := bstep (se 1 (by rfl) ⟨663452, by rfl⟩ : syracuseStep 884603 = 1326905) B1326905
theorem B2129789 : Blo 587289 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B589791 : Blo 587289 589791 := bstep (se 1 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 589791 = 884687) B884687
theorem B14516281 : Blo 587289 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B884927 : Blo 587289 884927 := bstep (se 1 (by rfl) ⟨663695, by rfl⟩ : syracuseStep 884927 = 1327391) B1327391
theorem B590015 : Blo 587289 590015 := bstep (se 1 (by rfl) ⟨442511, by rfl⟩ : syracuseStep 590015 = 885023) B885023
theorem B590031 : Blo 587289 590031 := bstep (se 1 (by rfl) ⟨442523, by rfl⟩ : syracuseStep 590031 = 885047) B885047
theorem B18120935 : Blo 587289 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B590079 : Blo 587289 590079 := bstep (se 1 (by rfl) ⟨442559, by rfl⟩ : syracuseStep 590079 = 885119) B885119
theorem B590127 : Blo 587289 590127 := bstep (se 1 (by rfl) ⟨442595, by rfl⟩ : syracuseStep 590127 = 885191) B885191
theorem B590363 : Blo 587289 590363 := bstep (se 1 (by rfl) ⟨442772, by rfl⟩ : syracuseStep 590363 = 885545) B885545
theorem B590367 : Blo 587289 590367 := bstep (se 1 (by rfl) ⟨442775, by rfl⟩ : syracuseStep 590367 = 885551) B885551
theorem B1966687 : Blo 587289 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B885353 : Blo 587289 885353 := bstep (se 2 (by rfl) ⟨332007, by rfl⟩ : syracuseStep 885353 = 664015) B664015
theorem B885359 : Blo 587289 885359 := bstep (se 1 (by rfl) ⟨664019, by rfl⟩ : syracuseStep 885359 = 1328039) B1328039
theorem B590447 : Blo 587289 590447 := bstep (se 1 (by rfl) ⟨442835, by rfl⟩ : syracuseStep 590447 = 885671) B885671
theorem B590503 : Blo 587289 590503 := bstep (se 1 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 590503 = 885755) B885755
theorem B590543 : Blo 587289 590543 := bstep (se 1 (by rfl) ⟨442907, by rfl⟩ : syracuseStep 590543 = 885815) B885815
theorem B590623 : Blo 587289 590623 := bstep (se 1 (by rfl) ⟨442967, by rfl⟩ : syracuseStep 590623 = 885935) B885935
theorem B590895 : Blo 587289 590895 := bstep (se 1 (by rfl) ⟨443171, by rfl⟩ : syracuseStep 590895 = 886343) B886343
theorem B590959 : Blo 587289 590959 := bstep (se 1 (by rfl) ⟨443219, by rfl⟩ : syracuseStep 590959 = 886439) B886439
theorem B591015 : Blo 587289 591015 := bstep (se 1 (by rfl) ⟨443261, by rfl⟩ : syracuseStep 591015 = 886523) B886523
theorem B591039 : Blo 587289 591039 := bstep (se 1 (by rfl) ⟨443279, by rfl⟩ : syracuseStep 591039 = 886559) B886559
theorem B885983 : Blo 587289 885983 := bstep (se 1 (by rfl) ⟨664487, by rfl⟩ : syracuseStep 885983 = 1328975) B1328975
theorem B591071 : Blo 587289 591071 := bstep (se 1 (by rfl) ⟨443303, by rfl⟩ : syracuseStep 591071 = 886607) B886607
theorem B885995 : Blo 587289 885995 := bstep (se 1 (by rfl) ⟨664496, by rfl⟩ : syracuseStep 885995 = 1328993) B1328993
theorem B3179807 : Blo 587289 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B591151 : Blo 587289 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B18089405 : Blo 587289 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B886379 : Blo 587289 886379 := bstep (se 1 (by rfl) ⟨664784, by rfl⟩ : syracuseStep 886379 = 1329569) B1329569
theorem B886463 : Blo 587289 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B886649 : Blo 587289 886649 := bstep (se 2 (by rfl) ⟨332493, by rfl⟩ : syracuseStep 886649 = 664987) B664987
theorem B1345423 : Blo 587289 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B1411103 : Blo 587289 1411103 := bstep (se 1 (by rfl) ⟨1058327, by rfl⟩ : syracuseStep 1411103 = 2116655) B2116655
theorem B1116767 : Blo 587289 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B11307883 : Blo 587289 11307883 := bstep (se 1 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 11307883 = 16961825) B16961825
theorem B12782879 : Blo 587289 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B7540229 : Blo 587289 7540229 := bstep (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) B1413793
theorem B2986145 : Blo 587289 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B1675561 : Blo 587289 1675561 := bstep (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) B1256671
theorem B5050673 : Blo 587289 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2233079 : Blo 587289 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B1414351 : Blo 587289 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B2987603 : Blo 587289 2987603 := bstep (se 1 (by rfl) ⟨2240702, by rfl⟩ : syracuseStep 2987603 = 4481405) B4481405
theorem B1414793 : Blo 587289 1414793 := bstep (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) B1061095
theorem B1119881 : Blo 587289 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B1677019 : Blo 587289 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B3774215 : Blo 587289 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B1677179 : Blo 587289 1677179 := bstep (se 1 (by rfl) ⟨1257884, by rfl⟩ : syracuseStep 1677179 = 2515769) B2515769
theorem B2234249 : Blo 587289 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B6690761 : Blo 587289 6690761 := bstep (se 2 (by rfl) ⟨2509035, by rfl⟩ : syracuseStep 6690761 = 5018071) B5018071
theorem B662107 : Blo 587289 662107 := bstep (se 1 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 662107 = 993161) B993161
theorem B1678067 : Blo 587289 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B10099565 : Blo 587289 10099565 := bstep (se 3 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 10099565 = 3787337) B3787337
theorem B662395 : Blo 587289 662395 := bstep (se 1 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 662395 = 993593) B993593
theorem B597223 : Blo 587289 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B663151 : Blo 587289 663151 := bstep (se 1 (by rfl) ⟨497363, by rfl⟩ : syracuseStep 663151 = 994727) B994727
theorem B663259 : Blo 587289 663259 := bstep (se 1 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 663259 = 994889) B994889
theorem B72720179 : Blo 587289 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B11476829 : Blo 587289 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B21438431 : Blo 587289 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B991487 : Blo 587289 991487 := bstep (se 1 (by rfl) ⟨743615, by rfl⟩ : syracuseStep 991487 = 1487231) B1487231
theorem B2990519 : Blo 587289 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B664231 : Blo 587289 664231 := bstep (se 1 (by rfl) ⟨498173, by rfl⟩ : syracuseStep 664231 = 996347) B996347
theorem B664519 : Blo 587289 664519 := bstep (se 1 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 664519 = 996779) B996779
theorem B10068947 : Blo 587289 10068947 := bstep (se 1 (by rfl) ⟨7551710, by rfl⟩ : syracuseStep 10068947 = 15103421) B15103421
theorem B1680551 : Blo 587289 1680551 := bstep (se 1 (by rfl) ⟨1260413, by rfl⟩ : syracuseStep 1680551 = 2520827) B2520827
theorem B664879 : Blo 587289 664879 := bstep (se 1 (by rfl) ⟨498659, by rfl⟩ : syracuseStep 664879 = 997319) B997319
theorem B4466339 : Blo 587289 4466339 := bstep (se 1 (by rfl) ⟨3349754, by rfl⟩ : syracuseStep 4466339 = 6699509) B6699509
theorem B2271017 : Blo 587289 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B18950071 : Blo 587289 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B993215 : Blo 587289 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B1419407 : Blo 587289 1419407 := bstep (se 1 (by rfl) ⟨1064555, by rfl⟩ : syracuseStep 1419407 = 2129111) B2129111
theorem B1255817 : Blo 587289 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B13576657 : Blo 587289 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1321451 : Blo 587289 1321451 := bstep (se 1 (by rfl) ⟨991088, by rfl⟩ : syracuseStep 1321451 = 1982177) B1982177
theorem B1419859 : Blo 587289 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B1322153 : Blo 587289 1322153 := bstep (se 2 (by rfl) ⟨495807, by rfl⟩ : syracuseStep 1322153 = 991615) B991615
theorem B4304137 : Blo 587289 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B2239913 : Blo 587289 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B1322567 : Blo 587289 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B1322639 : Blo 587289 1322639 := bstep (se 1 (by rfl) ⟨991979, by rfl⟩ : syracuseStep 1322639 = 1983959) B1983959
theorem B1322729 : Blo 587289 1322729 := bstep (se 2 (by rfl) ⟨496023, by rfl⟩ : syracuseStep 1322729 = 992047) B992047
theorem B1486583 : Blo 587289 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1322747 : Blo 587289 1322747 := bstep (se 1 (by rfl) ⟨992060, by rfl⟩ : syracuseStep 1322747 = 1984121) B1984121
theorem B1191851 : Blo 587289 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B995321 : Blo 587289 995321 := bstep (se 2 (by rfl) ⟨373245, by rfl⟩ : syracuseStep 995321 = 746491) B746491
theorem B4468769 : Blo 587289 4468769 := bstep (se 2 (by rfl) ⟨1675788, by rfl⟩ : syracuseStep 4468769 = 3351577) B3351577
theorem B995591 : Blo 587289 995591 := bstep (se 1 (by rfl) ⟨746693, by rfl⟩ : syracuseStep 995591 = 1493387) B1493387
theorem B3584411 : Blo 587289 3584411 := bstep (se 1 (by rfl) ⟨2688308, by rfl⟩ : syracuseStep 3584411 = 5376617) B5376617
theorem B1257935 : Blo 587289 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B1323755 : Blo 587289 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B635887 : Blo 587289 635887 := bstep (se 1 (by rfl) ⟨476915, by rfl⟩ : syracuseStep 635887 = 953831) B953831
theorem B1324025 : Blo 587289 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B20460595 : Blo 587289 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B2831431 : Blo 587289 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B1324115 : Blo 587289 1324115 := bstep (se 1 (by rfl) ⟨993086, by rfl⟩ : syracuseStep 1324115 = 1986173) B1986173
theorem B1258679 : Blo 587289 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B10073321 : Blo 587289 10073321 := bstep (se 2 (by rfl) ⟨3777495, by rfl⟩ : syracuseStep 10073321 = 7554991) B7554991
theorem B1324295 : Blo 587289 1324295 := bstep (se 1 (by rfl) ⟨993221, by rfl⟩ : syracuseStep 1324295 = 1986443) B1986443
theorem B996617 : Blo 587289 996617 := bstep (se 2 (by rfl) ⟨373731, by rfl⟩ : syracuseStep 996617 = 747463) B747463
theorem B996671 : Blo 587289 996671 := bstep (se 1 (by rfl) ⟨747503, by rfl⟩ : syracuseStep 996671 = 1495007) B1495007
theorem B1324655 : Blo 587289 1324655 := bstep (se 1 (by rfl) ⟨993491, by rfl⟩ : syracuseStep 1324655 = 1986983) B1986983
theorem B1488527 : Blo 587289 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B3782315 : Blo 587289 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B997103 : Blo 587289 997103 := bstep (se 1 (by rfl) ⟨747827, by rfl⟩ : syracuseStep 997103 = 1495655) B1495655
theorem B7550891 : Blo 587289 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B4765655 : Blo 587289 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B997447 : Blo 587289 997447 := bstep (se 1 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 997447 = 1496171) B1496171
theorem B1259815 : Blo 587289 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B1325519 : Blo 587289 1325519 := bstep (se 1 (by rfl) ⟨994139, by rfl⟩ : syracuseStep 1325519 = 1988279) B1988279
theorem B1325609 : Blo 587289 1325609 := bstep (se 2 (by rfl) ⟨497103, by rfl⟩ : syracuseStep 1325609 = 994207) B994207
theorem B1260191 : Blo 587289 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B1489711 : Blo 587289 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B1326185 : Blo 587289 1326185 := bstep (se 2 (by rfl) ⟨497319, by rfl⟩ : syracuseStep 1326185 = 994639) B994639
theorem B3783905 : Blo 587289 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B1326311 : Blo 587289 1326311 := bstep (se 1 (by rfl) ⟨994733, by rfl⟩ : syracuseStep 1326311 = 1989467) B1989467
theorem B3194099 : Blo 587289 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B1490359 : Blo 587289 1490359 := bstep (se 1 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 1490359 = 2235539) B2235539
theorem B1326815 : Blo 587289 1326815 := bstep (se 1 (by rfl) ⟨995111, by rfl⟩ : syracuseStep 1326815 = 1990223) B1990223
theorem B1326887 : Blo 587289 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B1982717 : Blo 587289 1982717 := bstep (se 3 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 1982717 = 743519) B743519
theorem B3359393 : Blo 587289 3359393 := bstep (se 2 (by rfl) ⟨1259772, by rfl⟩ : syracuseStep 3359393 = 2519545) B2519545
theorem B1983257 : Blo 587289 1983257 := bstep (se 2 (by rfl) ⟨743721, by rfl⟩ : syracuseStep 1983257 = 1487443) B1487443
theorem B1327913 : Blo 587289 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B1983527 : Blo 587289 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B1328183 : Blo 587289 1328183 := bstep (se 1 (by rfl) ⟨996137, by rfl⟩ : syracuseStep 1328183 = 1992275) B1992275
theorem B3785903 : Blo 587289 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B1328363 : Blo 587289 1328363 := bstep (se 1 (by rfl) ⟨996272, by rfl⟩ : syracuseStep 1328363 = 1992545) B1992545
theorem B4769027 : Blo 587289 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B10110221 : Blo 587289 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B1492303 : Blo 587289 1492303 := bstep (se 1 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 1492303 = 2238455) B2238455
theorem B1328831 : Blo 587289 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B3360599 : Blo 587289 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1492951 : Blo 587289 1492951 := bstep (se 1 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 1492951 = 2239427) B2239427
theorem B1984607 : Blo 587289 1984607 := bstep (se 1 (by rfl) ⟨1488455, by rfl⟩ : syracuseStep 1984607 = 2976911) B2976911
theorem B19089593 : Blo 587289 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B1493417 : Blo 587289 1493417 := bstep (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) B1120063
theorem B1329767 : Blo 587289 1329767 := bstep (se 1 (by rfl) ⟨997325, by rfl⟩ : syracuseStep 1329767 = 1994651) B1994651
theorem B838441 : Blo 587289 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B1887097 : Blo 587289 1887097 := bstep (se 2 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 1887097 = 1415323) B1415323
theorem B1330145 : Blo 587289 1330145 := bstep (se 2 (by rfl) ⟨498804, by rfl⟩ : syracuseStep 1330145 = 997609) B997609
theorem B3394703 : Blo 587289 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B5098729 : Blo 587289 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B1134407 : Blo 587289 1134407 := bstep (se 1 (by rfl) ⟨850805, by rfl⟩ : syracuseStep 1134407 = 1701611) B1701611
theorem B8474867 : Blo 587289 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B3363059 : Blo 587289 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B11456873 : Blo 587289 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B709175 : Blo 587289 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B1987739 : Blo 587289 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B10212563 : Blo 587289 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B3364699 : Blo 587289 3364699 := bstep (se 1 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 3364699 = 5047049) B5047049
theorem B23615621 : Blo 587289 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B9558161 : Blo 587289 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B2545835 : Blo 587289 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B4479461 : Blo 587289 4479461 := bstep (se 4 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 4479461 = 839899) B839899
theorem B6380369 : Blo 587289 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B2121383 : Blo 587289 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B1991195 : Blo 587289 1991195 := bstep (se 1 (by rfl) ⟨1493396, by rfl⟩ : syracuseStep 1991195 = 2986793) B2986793
theorem B2515495 : Blo 587289 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B9561017 : Blo 587289 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B2385683 : Blo 587289 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B10086443 : Blo 587289 10086443 := bstep (se 1 (by rfl) ⟨7564832, by rfl⟩ : syracuseStep 10086443 = 15129665) B15129665
theorem B1697915 : Blo 587289 1697915 := bstep (se 1 (by rfl) ⟨1273436, by rfl⟩ : syracuseStep 1697915 = 2546873) B2546873
theorem B5107049 : Blo 587289 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B2977235 : Blo 587289 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B881051 : Blo 587289 881051 := bstep (se 1 (by rfl) ⟨660788, by rfl⟩ : syracuseStep 881051 = 1321577) B1321577
theorem B2683343 : Blo 587289 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B1995515 : Blo 587289 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B2519869 : Blo 587289 2519869 := bstep (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) B944951
theorem B881471 : Blo 587289 881471 := bstep (se 1 (by rfl) ⟨661103, by rfl⟩ : syracuseStep 881471 = 1322207) B1322207
theorem B8090533 : Blo 587289 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B881615 : Blo 587289 881615 := bstep (se 1 (by rfl) ⟨661211, by rfl⟩ : syracuseStep 881615 = 1322423) B1322423
theorem B881657 : Blo 587289 881657 := bstep (se 2 (by rfl) ⟨330621, by rfl⟩ : syracuseStep 881657 = 661243) B661243
theorem B881705 : Blo 587289 881705 := bstep (se 2 (by rfl) ⟨330639, by rfl⟩ : syracuseStep 881705 = 661279) B661279
theorem B881735 : Blo 587289 881735 := bstep (se 1 (by rfl) ⟨661301, by rfl⟩ : syracuseStep 881735 = 1322603) B1322603
theorem B717979 : Blo 587289 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B881915 : Blo 587289 881915 := bstep (se 1 (by rfl) ⟨661436, by rfl⟩ : syracuseStep 881915 = 1322873) B1322873
theorem B9532723 : Blo 587289 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B2127379 : Blo 587289 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B587355 : Blo 587289 587355 := bstep (se 1 (by rfl) ⟨440516, by rfl⟩ : syracuseStep 587355 = 881033) B881033
theorem B4486751 : Blo 587289 4486751 := bstep (se 1 (by rfl) ⟨3365063, by rfl⟩ : syracuseStep 4486751 = 6730127) B6730127
theorem B23033443 : Blo 587289 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B587419 : Blo 587289 587419 := bstep (se 1 (by rfl) ⟨440564, by rfl⟩ : syracuseStep 587419 = 881129) B881129
theorem B587503 : Blo 587289 587503 := bstep (se 1 (by rfl) ⟨440627, by rfl⟩ : syracuseStep 587503 = 881255) B881255
theorem B587591 : Blo 587289 587591 := bstep (se 1 (by rfl) ⟨440693, by rfl⟩ : syracuseStep 587591 = 881387) B881387
theorem B587611 : Blo 587289 587611 := bstep (se 1 (by rfl) ⟨440708, by rfl⟩ : syracuseStep 587611 = 881417) B881417
theorem B587679 : Blo 587289 587679 := bstep (se 1 (by rfl) ⟨440759, by rfl⟩ : syracuseStep 587679 = 881519) B881519
theorem B587847 : Blo 587289 587847 := bstep (se 1 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 587847 = 881771) B881771
theorem B588007 : Blo 587289 588007 := bstep (se 1 (by rfl) ⟨441005, by rfl⟩ : syracuseStep 588007 = 882011) B882011
theorem B588191 : Blo 587289 588191 := bstep (se 1 (by rfl) ⟨441143, by rfl⟩ : syracuseStep 588191 = 882287) B882287
theorem B588239 : Blo 587289 588239 := bstep (se 1 (by rfl) ⟨441179, by rfl⟩ : syracuseStep 588239 = 882359) B882359
theorem B883151 : Blo 587289 883151 := bstep (se 1 (by rfl) ⟨662363, by rfl⟩ : syracuseStep 883151 = 1324727) B1324727
theorem B588263 : Blo 587289 588263 := bstep (se 1 (by rfl) ⟨441197, by rfl⟩ : syracuseStep 588263 = 882395) B882395
theorem B5896709 : Blo 587289 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B883241 : Blo 587289 883241 := bstep (se 2 (by rfl) ⟨331215, by rfl⟩ : syracuseStep 883241 = 662431) B662431
theorem B18086449 : Blo 587289 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B588379 : Blo 587289 588379 := bstep (se 1 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 588379 = 882569) B882569
theorem B2128475 : Blo 587289 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B6060673 : Blo 587289 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B588447 : Blo 587289 588447 := bstep (se 1 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 588447 = 882671) B882671
theorem B883433 : Blo 587289 883433 := bstep (se 2 (by rfl) ⟨331287, by rfl⟩ : syracuseStep 883433 = 662575) B662575
theorem B588615 : Blo 587289 588615 := bstep (se 1 (by rfl) ⟨441461, by rfl⟩ : syracuseStep 588615 = 882923) B882923
theorem B588655 : Blo 587289 588655 := bstep (se 1 (by rfl) ⟨441491, by rfl⟩ : syracuseStep 588655 = 882983) B882983
theorem B588711 : Blo 587289 588711 := bstep (se 1 (by rfl) ⟨441533, by rfl⟩ : syracuseStep 588711 = 883067) B883067
theorem B588891 : Blo 587289 588891 := bstep (se 1 (by rfl) ⟨441668, by rfl⟩ : syracuseStep 588891 = 883337) B883337
theorem B883817 : Blo 587289 883817 := bstep (se 2 (by rfl) ⟨331431, by rfl⟩ : syracuseStep 883817 = 662863) B662863
theorem B589007 : Blo 587289 589007 := bstep (se 1 (by rfl) ⟨441755, by rfl⟩ : syracuseStep 589007 = 883511) B883511
theorem B6454487 : Blo 587289 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B589031 : Blo 587289 589031 := bstep (se 1 (by rfl) ⟨441773, by rfl⟩ : syracuseStep 589031 = 883547) B883547
theorem B883943 : Blo 587289 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B589127 : Blo 587289 589127 := bstep (se 1 (by rfl) ⟨441845, by rfl⟩ : syracuseStep 589127 = 883691) B883691
theorem B2129341 : Blo 587289 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B589263 : Blo 587289 589263 := bstep (se 1 (by rfl) ⟨441947, by rfl⟩ : syracuseStep 589263 = 883895) B883895
theorem B589423 : Blo 587289 589423 := bstep (se 1 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 589423 = 884135) B884135
theorem B589479 : Blo 587289 589479 := bstep (se 1 (by rfl) ⟨442109, by rfl⟩ : syracuseStep 589479 = 884219) B884219
theorem B884447 : Blo 587289 884447 := bstep (se 1 (by rfl) ⟨663335, by rfl⟩ : syracuseStep 884447 = 1326671) B1326671
theorem B589543 : Blo 587289 589543 := bstep (se 1 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 589543 = 884315) B884315
theorem B884489 : Blo 587289 884489 := bstep (se 2 (by rfl) ⟨331683, by rfl⟩ : syracuseStep 884489 = 663367) B663367
theorem B589599 : Blo 587289 589599 := bstep (se 1 (by rfl) ⟨442199, by rfl⟩ : syracuseStep 589599 = 884399) B884399
theorem B589679 : Blo 587289 589679 := bstep (se 1 (by rfl) ⟨442259, by rfl⟩ : syracuseStep 589679 = 884519) B884519
theorem B589735 : Blo 587289 589735 := bstep (se 1 (by rfl) ⟨442301, by rfl⟩ : syracuseStep 589735 = 884603) B884603
theorem B4489181 : Blo 587289 4489181 := bstep (se 3 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 4489181 = 1683443) B1683443
theorem B589951 : Blo 587289 589951 := bstep (se 1 (by rfl) ⟨442463, by rfl⟩ : syracuseStep 589951 = 884927) B884927
theorem B590235 : Blo 587289 590235 := bstep (se 1 (by rfl) ⟨442676, by rfl⟩ : syracuseStep 590235 = 885353) B885353
theorem B590239 : Blo 587289 590239 := bstep (se 1 (by rfl) ⟨442679, by rfl⟩ : syracuseStep 590239 = 885359) B885359
theorem B885275 : Blo 587289 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B885455 : Blo 587289 885455 := bstep (se 1 (by rfl) ⟨664091, by rfl⟩ : syracuseStep 885455 = 1328183) B1328183
theorem B2523935 : Blo 587289 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B590655 : Blo 587289 590655 := bstep (se 1 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 590655 = 885983) B885983
theorem B885575 : Blo 587289 885575 := bstep (se 1 (by rfl) ⟨664181, by rfl⟩ : syracuseStep 885575 = 1328363) B1328363
theorem B590663 : Blo 587289 590663 := bstep (se 1 (by rfl) ⟨442997, by rfl⟩ : syracuseStep 590663 = 885995) B885995
theorem B3179351 : Blo 587289 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B885641 : Blo 587289 885641 := bstep (se 2 (by rfl) ⟨332115, by rfl⟩ : syracuseStep 885641 = 664231) B664231
theorem B12059603 : Blo 587289 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B590919 : Blo 587289 590919 := bstep (se 1 (by rfl) ⟨443189, by rfl⟩ : syracuseStep 590919 = 886379) B886379
theorem B885887 : Blo 587289 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B590975 : Blo 587289 590975 := bstep (se 1 (by rfl) ⟨443231, by rfl⟩ : syracuseStep 590975 = 886463) B886463
theorem B591099 : Blo 587289 591099 := bstep (se 1 (by rfl) ⟨443324, by rfl⟩ : syracuseStep 591099 = 886649) B886649
theorem B886025 : Blo 587289 886025 := bstep (se 2 (by rfl) ⟨332259, by rfl⟩ : syracuseStep 886025 = 664519) B664519
theorem B886505 : Blo 587289 886505 := bstep (se 2 (by rfl) ⟨332439, by rfl⟩ : syracuseStep 886505 = 664879) B664879
theorem B886511 : Blo 587289 886511 := bstep (se 1 (by rfl) ⟨664883, by rfl⟩ : syracuseStep 886511 = 1329767) B1329767
theorem B886763 : Blo 587289 886763 := bstep (se 1 (by rfl) ⟨665072, by rfl⟩ : syracuseStep 886763 = 1330145) B1330145
theorem B2263135 : Blo 587289 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B8521919 : Blo 587289 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B756271 : Blo 587289 756271 := bstep (se 1 (by rfl) ⟨567203, by rfl⟩ : syracuseStep 756271 = 1134407) B1134407
theorem B25266761 : Blo 587289 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B7637915 : Blo 587289 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B10488997 : Blo 587289 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B15077177 : Blo 587289 15077177 := bstep (se 2 (by rfl) ⟨5653941, by rfl⟩ : syracuseStep 15077177 = 11307883) B11307883
theorem B1118119 : Blo 587289 1118119 := bstep (se 1 (by rfl) ⟨838589, by rfl⟩ : syracuseStep 1118119 = 1677179) B1677179
theorem B4460507 : Blo 587289 4460507 := bstep (se 1 (by rfl) ⟨3345380, by rfl⟩ : syracuseStep 4460507 = 6690761) B6690761
theorem B2986307 : Blo 587289 2986307 := bstep (se 1 (by rfl) ⟨2239730, by rfl⟩ : syracuseStep 2986307 = 4479461) B4479461
theorem B5738849 : Blo 587289 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B3772781 : Blo 587289 3772781 := bstep (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) B1414793
theorem B1118711 : Blo 587289 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B10064573 : Blo 587289 10064573 := bstep (se 3 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 10064573 = 3774215) B3774215
theorem B1414255 : Blo 587289 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B14292287 : Blo 587289 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B660991 : Blo 587289 660991 := bstep (se 1 (by rfl) ⟨495743, by rfl⟩ : syracuseStep 660991 = 991487) B991487
theorem B2234081 : Blo 587289 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B6788893 : Blo 587289 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1120367 : Blo 587289 1120367 := bstep (se 1 (by rfl) ⟨840275, by rfl⟩ : syracuseStep 1120367 = 1680551) B1680551
theorem B7543205 : Blo 587289 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B3185189 : Blo 587289 3185189 := bstep (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) B597223
theorem B10787377 : Blo 587289 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B662143 : Blo 587289 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B6724295 : Blo 587289 6724295 := bstep (se 1 (by rfl) ⟨5043221, by rfl⟩ : syracuseStep 6724295 = 10086443) B10086443
theorem B3775241 : Blo 587289 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B957305 : Blo 587289 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B5675933 : Blo 587289 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B30711257 : Blo 587289 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B2236025 : Blo 587289 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B991055 : Blo 587289 991055 := bstep (se 1 (by rfl) ⟨743291, by rfl⟩ : syracuseStep 991055 = 1486583) B1486583
theorem B794567 : Blo 587289 794567 := bstep (se 1 (by rfl) ⟨595925, by rfl⟩ : syracuseStep 794567 = 1191851) B1191851
theorem B663547 : Blo 587289 663547 := bstep (se 1 (by rfl) ⟨497660, by rfl⟩ : syracuseStep 663547 = 995321) B995321
theorem B663727 : Blo 587289 663727 := bstep (se 1 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 663727 = 995591) B995591
theorem B1679753 : Blo 587289 1679753 := bstep (se 2 (by rfl) ⟨629907, by rfl⟩ : syracuseStep 1679753 = 1259815) B1259815
theorem B664411 : Blo 587289 664411 := bstep (se 1 (by rfl) ⟨498308, by rfl⟩ : syracuseStep 664411 = 996617) B996617
theorem B664447 : Blo 587289 664447 := bstep (se 1 (by rfl) ⟨498335, by rfl⟩ : syracuseStep 664447 = 996671) B996671
theorem B2991167 : Blo 587289 2991167 := bstep (se 1 (by rfl) ⟨2243375, by rfl⟩ : syracuseStep 2991167 = 4486751) B4486751
theorem B992351 : Blo 587289 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B664735 : Blo 587289 664735 := bstep (se 1 (by rfl) ⟨498551, by rfl⟩ : syracuseStep 664735 = 997103) B997103
theorem B4302991 : Blo 587289 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B2992787 : Blo 587289 2992787 := bstep (se 1 (by rfl) ⟨2244590, by rfl⟩ : syracuseStep 2992787 = 4489181) B4489181
theorem B1321811 : Blo 587289 1321811 := bstep (se 1 (by rfl) ⟨991358, by rfl⟩ : syracuseStep 1321811 = 1982717) B1982717
theorem B2239595 : Blo 587289 2239595 := bstep (se 1 (by rfl) ⟨1679696, by rfl⟩ : syracuseStep 2239595 = 3359393) B3359393
theorem B1322171 : Blo 587289 1322171 := bstep (se 1 (by rfl) ⟨991628, by rfl⟩ : syracuseStep 1322171 = 1983257) B1983257
theorem B1322351 : Blo 587289 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B3353993 : Blo 587289 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B3354493 : Blo 587289 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B2240399 : Blo 587289 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B1323071 : Blo 587289 1323071 := bstep (se 1 (by rfl) ⟨992303, by rfl⟩ : syracuseStep 1323071 = 1984607) B1984607
theorem B12726395 : Blo 587289 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B995611 : Blo 587289 995611 := bstep (se 1 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 995611 = 1493417) B1493417
theorem B5026819 : Blo 587289 5026819 := bstep (se 1 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 5026819 = 7540229) B7540229
theorem B5649911 : Blo 587289 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B2242039 : Blo 587289 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B3356477 : Blo 587289 3356477 := bstep (se 3 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 3356477 = 1258679) B1258679
theorem B1488719 : Blo 587289 1488719 := bstep (se 1 (by rfl) ⟨1116539, by rfl⟩ : syracuseStep 1488719 = 2233079) B2233079
theorem B18102209 : Blo 587289 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B1325159 : Blo 587289 1325159 := bstep (se 1 (by rfl) ⟨993869, by rfl⟩ : syracuseStep 1325159 = 1987739) B1987739
theorem B1489499 : Blo 587289 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B15743747 : Blo 587289 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B6372107 : Blo 587289 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B4471685 : Blo 587289 4471685 := bstep (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) B838441
theorem B6798305 : Blo 587289 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B6733043 : Blo 587289 6733043 := bstep (se 1 (by rfl) ⟨5049782, by rfl⟩ : syracuseStep 6733043 = 10099565) B10099565
theorem B48480119 : Blo 587289 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B7651219 : Blo 587289 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B3391397 : Blo 587289 3391397 := bstep (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) B635887
theorem B1327463 : Blo 587289 1327463 := bstep (se 1 (by rfl) ⟨995597, by rfl⟩ : syracuseStep 1327463 = 1991195) B1991195
theorem B6374011 : Blo 587289 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B3359825 : Blo 587289 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B1590455 : Blo 587289 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B27280793 : Blo 587289 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B1131943 : Blo 587289 1131943 := bstep (se 1 (by rfl) ⟨848957, by rfl⟩ : syracuseStep 1131943 = 1697915) B1697915
theorem B837211 : Blo 587289 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B2836505 : Blo 587289 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1493275 : Blo 587289 1493275 := bstep (se 1 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 1493275 = 2239913) B2239913
theorem B1984823 : Blo 587289 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B1329929 : Blo 587289 1329929 := bstep (se 2 (by rfl) ⟨498723, by rfl⟩ : syracuseStep 1329929 = 997447) B997447
theorem B1788895 : Blo 587289 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B1330343 : Blo 587289 1330343 := bstep (se 1 (by rfl) ⟨997757, by rfl⟩ : syracuseStep 1330343 = 1995515) B1995515
theorem B8080897 : Blo 587289 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B1986281 : Blo 587289 1986281 := bstep (se 2 (by rfl) ⟨744855, by rfl⟩ : syracuseStep 1986281 = 1489711) B1489711
theorem B5033927 : Blo 587289 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B840127 : Blo 587289 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B1987145 : Blo 587289 1987145 := bstep (se 2 (by rfl) ⟨745179, by rfl⟩ : syracuseStep 1987145 = 1490359) B1490359
theorem B2839121 : Blo 587289 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B19355041 : Blo 587289 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B12080623 : Blo 587289 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B6740147 : Blo 587289 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B2119871 : Blo 587289 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B940735 : Blo 587289 940735 := bstep (se 1 (by rfl) ⟨705551, by rfl⟩ : syracuseStep 940735 = 1411103) B1411103
theorem B1891133 : Blo 587289 1891133 := bstep (se 3 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 1891133 = 709175) B709175
theorem B1989737 : Blo 587289 1989737 := bstep (se 2 (by rfl) ⟨746151, by rfl⟩ : syracuseStep 1989737 = 1492303) B1492303
theorem B1793897 : Blo 587289 1793897 := bstep (se 2 (by rfl) ⟨672711, by rfl⟩ : syracuseStep 1793897 = 1345423) B1345423
theorem B1990601 : Blo 587289 1990601 := bstep (se 2 (by rfl) ⟨746475, by rfl⟩ : syracuseStep 1990601 = 1492951) B1492951
theorem B1990763 : Blo 587289 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B3367115 : Blo 587289 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1893145 : Blo 587289 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B6808375 : Blo 587289 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B1991735 : Blo 587289 1991735 := bstep (se 1 (by rfl) ⟨1493801, by rfl⟩ : syracuseStep 1991735 = 2987603) B2987603
theorem B746587 : Blo 587289 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B2516129 : Blo 587289 2516129 := bstep (se 2 (by rfl) ⟨943548, by rfl⟩ : syracuseStep 2516129 = 1887097) B1887097
theorem B4253579 : Blo 587289 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B6056045 : Blo 587289 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1993679 : Blo 587289 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B6712631 : Blo 587289 6712631 := bstep (se 1 (by rfl) ⟨5034473, by rfl⟩ : syracuseStep 6712631 = 10068947) B10068947
theorem B2977559 : Blo 587289 2977559 := bstep (se 1 (by rfl) ⟨2233169, by rfl⟩ : syracuseStep 2977559 = 4466339) B4466339
theorem B946271 : Blo 587289 946271 := bstep (se 1 (by rfl) ⟨709703, by rfl⟩ : syracuseStep 946271 = 1419407) B1419407
theorem B2978045 : Blo 587289 2978045 := bstep (se 3 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 2978045 = 1116767) B1116767
theorem B880967 : Blo 587289 880967 := bstep (se 1 (by rfl) ⟨660725, by rfl⟩ : syracuseStep 880967 = 1321451) B1321451
theorem B12710297 : Blo 587289 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B881435 : Blo 587289 881435 := bstep (se 1 (by rfl) ⟨661076, by rfl⟩ : syracuseStep 881435 = 1322153) B1322153
theorem B3404699 : Blo 587289 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B881711 : Blo 587289 881711 := bstep (se 1 (by rfl) ⟨661283, by rfl⟩ : syracuseStep 881711 = 1322567) B1322567
theorem B881759 : Blo 587289 881759 := bstep (se 1 (by rfl) ⟨661319, by rfl⟩ : syracuseStep 881759 = 1322639) B1322639
theorem B4486265 : Blo 587289 4486265 := bstep (se 2 (by rfl) ⟨1682349, by rfl⟩ : syracuseStep 4486265 = 3364699) B3364699
theorem B881819 : Blo 587289 881819 := bstep (se 1 (by rfl) ⟨661364, by rfl⟩ : syracuseStep 881819 = 1322729) B1322729
theorem B881831 : Blo 587289 881831 := bstep (se 1 (by rfl) ⟨661373, by rfl⟩ : syracuseStep 881831 = 1322747) B1322747
theorem B2979179 : Blo 587289 2979179 := bstep (se 1 (by rfl) ⟨2234384, by rfl⟩ : syracuseStep 2979179 = 4468769) B4468769
theorem B587367 : Blo 587289 587367 := bstep (se 1 (by rfl) ⟨440525, by rfl⟩ : syracuseStep 587367 = 881051) B881051
theorem B2389607 : Blo 587289 2389607 := bstep (se 1 (by rfl) ⟨1792205, by rfl⟩ : syracuseStep 2389607 = 3584411) B3584411
theorem B882503 : Blo 587289 882503 := bstep (se 1 (by rfl) ⟨661877, by rfl⟩ : syracuseStep 882503 = 1323755) B1323755
theorem B587647 : Blo 587289 587647 := bstep (se 1 (by rfl) ⟨440735, by rfl⟩ : syracuseStep 587647 = 881471) B881471
theorem B587743 : Blo 587289 587743 := bstep (se 1 (by rfl) ⟨440807, by rfl⟩ : syracuseStep 587743 = 881615) B881615
theorem B587771 : Blo 587289 587771 := bstep (se 1 (by rfl) ⟨440828, by rfl⟩ : syracuseStep 587771 = 881657) B881657
theorem B882683 : Blo 587289 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B587803 : Blo 587289 587803 := bstep (se 1 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 587803 = 881705) B881705
theorem B587823 : Blo 587289 587823 := bstep (se 1 (by rfl) ⟨440867, by rfl⟩ : syracuseStep 587823 = 881735) B881735
theorem B882743 : Blo 587289 882743 := bstep (se 1 (by rfl) ⟨662057, by rfl⟩ : syracuseStep 882743 = 1324115) B1324115
theorem B24115265 : Blo 587289 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B882809 : Blo 587289 882809 := bstep (se 2 (by rfl) ⟨331053, by rfl⟩ : syracuseStep 882809 = 662107) B662107
theorem B6715547 : Blo 587289 6715547 := bstep (se 1 (by rfl) ⟨5036660, by rfl⟩ : syracuseStep 6715547 = 10073321) B10073321
theorem B587943 : Blo 587289 587943 := bstep (se 1 (by rfl) ⟨440957, by rfl⟩ : syracuseStep 587943 = 881915) B881915
theorem B882863 : Blo 587289 882863 := bstep (se 1 (by rfl) ⟨662147, by rfl⟩ : syracuseStep 882863 = 1324295) B1324295
theorem B883103 : Blo 587289 883103 := bstep (se 1 (by rfl) ⟨662327, by rfl⟩ : syracuseStep 883103 = 1324655) B1324655
theorem B2521543 : Blo 587289 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B883193 : Blo 587289 883193 := bstep (se 2 (by rfl) ⟨331197, by rfl⟩ : syracuseStep 883193 = 662395) B662395
theorem B3177103 : Blo 587289 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B588767 : Blo 587289 588767 := bstep (se 1 (by rfl) ⟨441575, by rfl⟩ : syracuseStep 588767 = 883151) B883151
theorem B883679 : Blo 587289 883679 := bstep (se 1 (by rfl) ⟨662759, by rfl⟩ : syracuseStep 883679 = 1325519) B1325519
theorem B3931139 : Blo 587289 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B588827 : Blo 587289 588827 := bstep (se 1 (by rfl) ⟨441620, by rfl⟩ : syracuseStep 588827 = 883241) B883241
theorem B883739 : Blo 587289 883739 := bstep (se 1 (by rfl) ⟨662804, by rfl⟩ : syracuseStep 883739 = 1325609) B1325609
theorem B588955 : Blo 587289 588955 := bstep (se 1 (by rfl) ⟨441716, by rfl⟩ : syracuseStep 588955 = 883433) B883433
theorem B589211 : Blo 587289 589211 := bstep (se 1 (by rfl) ⟨441908, by rfl⟩ : syracuseStep 589211 = 883817) B883817
theorem B884123 : Blo 587289 884123 := bstep (se 1 (by rfl) ⟨663092, by rfl⟩ : syracuseStep 884123 = 1326185) B1326185
theorem B884201 : Blo 587289 884201 := bstep (se 2 (by rfl) ⟨331575, by rfl⟩ : syracuseStep 884201 = 663151) B663151
theorem B2522603 : Blo 587289 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B589295 : Blo 587289 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B884207 : Blo 587289 884207 := bstep (se 1 (by rfl) ⟨663155, by rfl⟩ : syracuseStep 884207 = 1326311) B1326311
theorem B2129399 : Blo 587289 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B884345 : Blo 587289 884345 := bstep (se 2 (by rfl) ⟨331629, by rfl⟩ : syracuseStep 884345 = 663259) B663259
theorem B589631 : Blo 587289 589631 := bstep (se 1 (by rfl) ⟨442223, by rfl⟩ : syracuseStep 589631 = 884447) B884447
theorem B884543 : Blo 587289 884543 := bstep (se 1 (by rfl) ⟨663407, by rfl⟩ : syracuseStep 884543 = 1326815) B1326815
theorem B589659 : Blo 587289 589659 := bstep (se 1 (by rfl) ⟨442244, by rfl⟩ : syracuseStep 589659 = 884489) B884489
theorem B884591 : Blo 587289 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B884969 : Blo 587289 884969 := bstep (se 2 (by rfl) ⟨331863, by rfl⟩ : syracuseStep 884969 = 663727) B663727
theorem B884975 : Blo 587289 884975 := bstep (se 1 (by rfl) ⟨663731, by rfl⟩ : syracuseStep 884975 = 1327463) B1327463
theorem B590183 : Blo 587289 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B590303 : Blo 587289 590303 := bstep (se 1 (by rfl) ⟨442727, by rfl⟩ : syracuseStep 590303 = 885455) B885455
theorem B590383 : Blo 587289 590383 := bstep (se 1 (by rfl) ⟨442787, by rfl⟩ : syracuseStep 590383 = 885575) B885575
theorem B590427 : Blo 587289 590427 := bstep (se 1 (by rfl) ⟨442820, by rfl⟩ : syracuseStep 590427 = 885641) B885641
theorem B590591 : Blo 587289 590591 := bstep (se 1 (by rfl) ⟨442943, by rfl⟩ : syracuseStep 590591 = 885887) B885887
theorem B590683 : Blo 587289 590683 := bstep (se 1 (by rfl) ⟨443012, by rfl⟩ : syracuseStep 590683 = 886025) B886025
theorem B18187195 : Blo 587289 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B2524193 : Blo 587289 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B9077833 : Blo 587289 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B885881 : Blo 587289 885881 := bstep (se 2 (by rfl) ⟨332205, by rfl⟩ : syracuseStep 885881 = 664411) B664411
theorem B591003 : Blo 587289 591003 := bstep (se 1 (by rfl) ⟨443252, by rfl⟩ : syracuseStep 591003 = 886505) B886505
theorem B591007 : Blo 587289 591007 := bstep (se 1 (by rfl) ⟨443255, by rfl⟩ : syracuseStep 591007 = 886511) B886511
theorem B885929 : Blo 587289 885929 := bstep (se 2 (by rfl) ⟨332223, by rfl⟩ : syracuseStep 885929 = 664447) B664447
theorem B2983229 : Blo 587289 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B591175 : Blo 587289 591175 := bstep (se 1 (by rfl) ⟨443381, by rfl⟩ : syracuseStep 591175 = 886763) B886763
theorem B886313 : Blo 587289 886313 := bstep (se 2 (by rfl) ⟨332367, by rfl⟩ : syracuseStep 886313 = 664735) B664735
theorem B16844507 : Blo 587289 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B886619 : Blo 587289 886619 := bstep (se 1 (by rfl) ⟨664964, by rfl⟩ : syracuseStep 886619 = 1329929) B1329929
theorem B1509257 : Blo 587289 1509257 := bstep (se 2 (by rfl) ⟨565971, by rfl⟩ : syracuseStep 1509257 = 1131943) B1131943
theorem B886895 : Blo 587289 886895 := bstep (se 1 (by rfl) ⟨665171, by rfl⟩ : syracuseStep 886895 = 1330343) B1330343
theorem B1116281 : Blo 587289 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B3017513 : Blo 587289 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B5737321 : Blo 587289 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B4493431 : Blo 587289 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B1413247 : Blo 587289 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B9540773 : Blo 587289 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B660703 : Blo 587289 660703 := bstep (se 1 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 660703 = 991055) B991055
theorem B1119835 : Blo 587289 1119835 := bstep (se 1 (by rfl) ⟨839876, by rfl⟩ : syracuseStep 1119835 = 1679753) B1679753
theorem B1120169 : Blo 587289 1120169 := bstep (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) B840127
theorem B661567 : Blo 587289 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B1677419 : Blo 587289 1677419 := bstep (se 1 (by rfl) ⟨1258064, by rfl⟩ : syracuseStep 1677419 = 2516129) B2516129
theorem B4037363 : Blo 587289 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B2989385 : Blo 587289 2989385 := bstep (se 2 (by rfl) ⟨1121019, by rfl⟩ : syracuseStep 2989385 = 2242039) B2242039
theorem B2235995 : Blo 587289 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B9051857 : Blo 587289 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B630847 : Blo 587289 630847 := bstep (se 1 (by rfl) ⟨473135, by rfl⟩ : syracuseStep 630847 = 946271) B946271
theorem B2269799 : Blo 587289 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B2990843 : Blo 587289 2990843 := bstep (se 1 (by rfl) ⟨2243132, by rfl⟩ : syracuseStep 2990843 = 4486265) B4486265
theorem B4236137 : Blo 587289 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B1254313 : Blo 587289 1254313 := bstep (se 2 (by rfl) ⟨470367, by rfl⟩ : syracuseStep 1254313 = 940735) B940735
theorem B2237651 : Blo 587289 2237651 := bstep (se 1 (by rfl) ⟨1678238, by rfl⟩ : syracuseStep 2237651 = 3356477) B3356477
theorem B992479 : Blo 587289 992479 := bstep (se 1 (by rfl) ⟨744359, by rfl⟩ : syracuseStep 992479 = 1488719) B1488719
theorem B992999 : Blo 587289 992999 := bstep (se 1 (by rfl) ⟨744749, by rfl⟩ : syracuseStep 992999 = 1489499) B1489499
theorem B10495831 : Blo 587289 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B4532203 : Blo 587289 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B1681735 : Blo 587289 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B1419599 : Blo 587289 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B10201625 : Blo 587289 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B32320079 : Blo 587289 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B1682623 : Blo 587289 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B8039735 : Blo 587289 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B2239883 : Blo 587289 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B1060303 : Blo 587289 1060303 := bstep (se 1 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 1060303 = 1590455) B1590455
theorem B8498681 : Blo 587289 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B33894125 : Blo 587289 33894125 := bstep (se 3 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 33894125 = 12710297) B12710297
theorem B995449 : Blo 587289 995449 := bstep (se 2 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 995449 = 746587) B746587
theorem B5681279 : Blo 587289 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B1323215 : Blo 587289 1323215 := bstep (se 1 (by rfl) ⟨992411, by rfl⟩ : syracuseStep 1323215 = 1984823) B1984823
theorem B1324187 : Blo 587289 1324187 := bstep (se 1 (by rfl) ⟨993140, by rfl⟩ : syracuseStep 1324187 = 1986281) B1986281
theorem B3355951 : Blo 587289 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B1324763 : Blo 587289 1324763 := bstep (se 1 (by rfl) ⟨993572, by rfl⟩ : syracuseStep 1324763 = 1987145) B1987145
theorem B1489387 : Blo 587289 1489387 := bstep (se 1 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 1489387 = 2234081) B2234081
theorem B5028803 : Blo 587289 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B1260755 : Blo 587289 1260755 := bstep (se 1 (by rfl) ⟨945566, by rfl⟩ : syracuseStep 1260755 = 1891133) B1891133
theorem B3783955 : Blo 587289 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B1326491 : Blo 587289 1326491 := bstep (se 1 (by rfl) ⟨994868, by rfl⟩ : syracuseStep 1326491 = 1989737) B1989737
theorem B1490683 : Blo 587289 1490683 := bstep (se 1 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 1490683 = 2236025) B2236025
theorem B4472657 : Blo 587289 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B1490825 : Blo 587289 1490825 := bstep (se 2 (by rfl) ⟨559059, by rfl⟩ : syracuseStep 1490825 = 1118119) B1118119
theorem B1195931 : Blo 587289 1195931 := bstep (se 1 (by rfl) ⟨896948, by rfl⟩ : syracuseStep 1195931 = 1793897) B1793897
theorem B1327067 : Blo 587289 1327067 := bstep (se 1 (by rfl) ⟨995300, by rfl⟩ : syracuseStep 1327067 = 1990601) B1990601
theorem B1327175 : Blo 587289 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B2244743 : Blo 587289 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B1327481 : Blo 587289 1327481 := bstep (se 2 (by rfl) ⟨497805, by rfl⟩ : syracuseStep 1327481 = 995611) B995611
theorem B1327823 : Blo 587289 1327823 := bstep (se 1 (by rfl) ⟨995867, by rfl⟩ : syracuseStep 1327823 = 1991735) B1991735
theorem B2835719 : Blo 587289 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B6702425 : Blo 587289 6702425 := bstep (se 2 (by rfl) ⟨2513409, by rfl⟩ : syracuseStep 6702425 = 5026819) B5026819
theorem B1885673 : Blo 587289 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B25806721 : Blo 587289 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B1329119 : Blo 587289 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B16107497 : Blo 587289 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B1493063 : Blo 587289 1493063 := bstep (se 1 (by rfl) ⟨1119797, by rfl⟩ : syracuseStep 1493063 = 2239595) B2239595
theorem B4475087 : Blo 587289 4475087 := bstep (se 1 (by rfl) ⟨3356315, by rfl⟩ : syracuseStep 4475087 = 6712631) B6712631
theorem B20367773 : Blo 587289 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B1985039 : Blo 587289 1985039 := bstep (se 1 (by rfl) ⟨1488779, by rfl⟩ : syracuseStep 1985039 = 2977559) B2977559
theorem B1493599 : Blo 587289 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1985363 : Blo 587289 1985363 := bstep (se 1 (by rfl) ⟨1489022, by rfl⟩ : syracuseStep 1985363 = 2978045) B2978045
theorem B3362057 : Blo 587289 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B1986119 : Blo 587289 1986119 := bstep (se 1 (by rfl) ⟨1489589, by rfl⟩ : syracuseStep 1986119 = 2979179) B2979179
theorem B1593071 : Blo 587289 1593071 := bstep (se 1 (by rfl) ⟨1194803, by rfl⟩ : syracuseStep 1593071 = 2389607) B2389607
theorem B16076843 : Blo 587289 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B4477031 : Blo 587289 4477031 := bstep (se 1 (by rfl) ⟨3357773, by rfl⟩ : syracuseStep 4477031 = 6715547) B6715547
theorem B4248071 : Blo 587289 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B193090229 : Blo 587289 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B2118845 : Blo 587289 2118845 := bstep (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) B794567
theorem B8478269 : Blo 587289 8478269 := bstep (se 3 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 8478269 = 3179351) B3179351
theorem B10051451 : Blo 587289 10051451 := bstep (se 1 (by rfl) ⟨7538588, by rfl⟩ : syracuseStep 10051451 = 15077177) B15077177
theorem B2973671 : Blo 587289 2973671 := bstep (se 1 (by rfl) ⟨2230253, by rfl⟩ : syracuseStep 2973671 = 4460507) B4460507
theorem B1990871 : Blo 587289 1990871 := bstep (se 1 (by rfl) ⟨1493153, by rfl⟩ : syracuseStep 1990871 = 2986307) B2986307
theorem B3825899 : Blo 587289 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B2515187 : Blo 587289 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B1991033 : Blo 587289 1991033 := bstep (se 2 (by rfl) ⟨746637, by rfl⟩ : syracuseStep 1991033 = 1493275) B1493275
theorem B1892747 : Blo 587289 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B6709715 : Blo 587289 6709715 := bstep (se 1 (by rfl) ⟨5032286, by rfl⟩ : syracuseStep 6709715 = 10064573) B10064573
theorem B1008361 : Blo 587289 1008361 := bstep (se 2 (by rfl) ⟨378135, by rfl⟩ : syracuseStep 1008361 = 756271) B756271
theorem B9528191 : Blo 587289 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B746911 : Blo 587289 746911 := bstep (se 1 (by rfl) ⟨560183, by rfl⟩ : syracuseStep 746911 = 1120367) B1120367
theorem B13985329 : Blo 587289 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B2123459 : Blo 587289 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B4482863 : Blo 587289 4482863 := bstep (se 1 (by rfl) ⟨3362147, by rfl⟩ : syracuseStep 4482863 = 6724295) B6724295
theorem B2516827 : Blo 587289 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B10774529 : Blo 587289 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B20474171 : Blo 587289 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B7564013 : Blo 587289 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B1994111 : Blo 587289 1994111 := bstep (se 1 (by rfl) ⟨1495583, by rfl⟩ : syracuseStep 1994111 = 2991167) B2991167
theorem B1995191 : Blo 587289 1995191 := bstep (se 1 (by rfl) ⟨1496393, by rfl⟩ : syracuseStep 1995191 = 2992787) B2992787
theorem B881207 : Blo 587289 881207 := bstep (se 1 (by rfl) ⟨660905, by rfl⟩ : syracuseStep 881207 = 1321811) B1321811
theorem B881321 : Blo 587289 881321 := bstep (se 2 (by rfl) ⟨330495, by rfl⟩ : syracuseStep 881321 = 660991) B660991
theorem B881447 : Blo 587289 881447 := bstep (se 1 (by rfl) ⟨661085, by rfl⟩ : syracuseStep 881447 = 1322171) B1322171
theorem B881567 : Blo 587289 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B2552813 : Blo 587289 2552813 := bstep (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) B957305
theorem B882047 : Blo 587289 882047 := bstep (se 1 (by rfl) ⟨661535, by rfl⟩ : syracuseStep 882047 = 1323071) B1323071
theorem B8484263 : Blo 587289 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B587311 : Blo 587289 587311 := bstep (se 1 (by rfl) ⟨440483, by rfl⟩ : syracuseStep 587311 = 880967) B880967
theorem B587623 : Blo 587289 587623 := bstep (se 1 (by rfl) ⟨440717, by rfl⟩ : syracuseStep 587623 = 881435) B881435
theorem B587807 : Blo 587289 587807 := bstep (se 1 (by rfl) ⟨440855, by rfl⟩ : syracuseStep 587807 = 881711) B881711
theorem B587839 : Blo 587289 587839 := bstep (se 1 (by rfl) ⟨440879, by rfl⟩ : syracuseStep 587839 = 881759) B881759
theorem B14383169 : Blo 587289 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B587879 : Blo 587289 587879 := bstep (se 1 (by rfl) ⟨440909, by rfl⟩ : syracuseStep 587879 = 881819) B881819
theorem B587887 : Blo 587289 587887 := bstep (se 1 (by rfl) ⟨440915, by rfl⟩ : syracuseStep 587887 = 881831) B881831
theorem B882857 : Blo 587289 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B3766607 : Blo 587289 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B588335 : Blo 587289 588335 := bstep (se 1 (by rfl) ⟨441251, by rfl⟩ : syracuseStep 588335 = 882503) B882503
theorem B588455 : Blo 587289 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B588495 : Blo 587289 588495 := bstep (se 1 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 588495 = 882743) B882743
theorem B883439 : Blo 587289 883439 := bstep (se 1 (by rfl) ⟨662579, by rfl⟩ : syracuseStep 883439 = 1325159) B1325159
theorem B588539 : Blo 587289 588539 := bstep (se 1 (by rfl) ⟨441404, by rfl⟩ : syracuseStep 588539 = 882809) B882809
theorem B588575 : Blo 587289 588575 := bstep (se 1 (by rfl) ⟨441431, by rfl⟩ : syracuseStep 588575 = 882863) B882863
theorem B588735 : Blo 587289 588735 := bstep (se 1 (by rfl) ⟨441551, by rfl⟩ : syracuseStep 588735 = 883103) B883103
theorem B588795 : Blo 587289 588795 := bstep (se 1 (by rfl) ⟨441596, by rfl⟩ : syracuseStep 588795 = 883193) B883193
theorem B2981123 : Blo 587289 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B589119 : Blo 587289 589119 := bstep (se 1 (by rfl) ⟨441839, by rfl⟩ : syracuseStep 589119 = 883679) B883679
theorem B2620759 : Blo 587289 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B589159 : Blo 587289 589159 := bstep (se 1 (by rfl) ⟨441869, by rfl⟩ : syracuseStep 589159 = 883739) B883739
theorem B4488695 : Blo 587289 4488695 := bstep (se 1 (by rfl) ⟨3366521, by rfl⟩ : syracuseStep 4488695 = 6733043) B6733043
theorem B589415 : Blo 587289 589415 := bstep (se 1 (by rfl) ⟨442061, by rfl⟩ : syracuseStep 589415 = 884123) B884123
theorem B589467 : Blo 587289 589467 := bstep (se 1 (by rfl) ⟨442100, by rfl⟩ : syracuseStep 589467 = 884201) B884201
theorem B589471 : Blo 587289 589471 := bstep (se 1 (by rfl) ⟨442103, by rfl⟩ : syracuseStep 589471 = 884207) B884207
theorem B589563 : Blo 587289 589563 := bstep (se 1 (by rfl) ⟨442172, by rfl⟩ : syracuseStep 589563 = 884345) B884345
theorem B589695 : Blo 587289 589695 := bstep (se 1 (by rfl) ⟨442271, by rfl⟩ : syracuseStep 589695 = 884543) B884543
theorem B589727 : Blo 587289 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B2260931 : Blo 587289 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B884729 : Blo 587289 884729 := bstep (se 2 (by rfl) ⟨331773, by rfl⟩ : syracuseStep 884729 = 663547) B663547
theorem B884783 : Blo 587289 884783 := bstep (se 1 (by rfl) ⟨663587, by rfl⟩ : syracuseStep 884783 = 1327175) B1327175
theorem B589979 : Blo 587289 589979 := bstep (se 1 (by rfl) ⟨442484, by rfl⟩ : syracuseStep 589979 = 884969) B884969
theorem B589983 : Blo 587289 589983 := bstep (se 1 (by rfl) ⟨442487, by rfl⟩ : syracuseStep 589983 = 884975) B884975
theorem B884987 : Blo 587289 884987 := bstep (se 1 (by rfl) ⟨663740, by rfl⟩ : syracuseStep 884987 = 1327481) B1327481
theorem B885215 : Blo 587289 885215 := bstep (se 1 (by rfl) ⟨663911, by rfl⟩ : syracuseStep 885215 = 1327823) B1327823
theorem B590587 : Blo 587289 590587 := bstep (se 1 (by rfl) ⟨442940, by rfl⟩ : syracuseStep 590587 = 885881) B885881
theorem B590619 : Blo 587289 590619 := bstep (se 1 (by rfl) ⟨442964, by rfl⟩ : syracuseStep 590619 = 885929) B885929
theorem B1344481 : Blo 587289 1344481 := bstep (se 2 (by rfl) ⟨504180, by rfl⟩ : syracuseStep 1344481 = 1008361) B1008361
theorem B590875 : Blo 587289 590875 := bstep (se 1 (by rfl) ⟨443156, by rfl⟩ : syracuseStep 590875 = 886313) B886313
theorem B1672417 : Blo 587289 1672417 := bstep (se 2 (by rfl) ⟨627156, by rfl⟩ : syracuseStep 1672417 = 1254313) B1254313
theorem B591079 : Blo 587289 591079 := bstep (se 1 (by rfl) ⟨443309, by rfl⟩ : syracuseStep 591079 = 886619) B886619
theorem B24249593 : Blo 587289 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B886079 : Blo 587289 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B591263 : Blo 587289 591263 := bstep (se 1 (by rfl) ⟨443447, by rfl⟩ : syracuseStep 591263 = 886895) B886895
theorem B2983391 : Blo 587289 2983391 := bstep (se 1 (by rfl) ⟨2237543, by rfl⟩ : syracuseStep 2983391 = 4475087) B4475087
theorem B18647105 : Blo 587289 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B13994441 : Blo 587289 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B34408961 : Blo 587289 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B10717895 : Blo 587289 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B2984687 : Blo 587289 2984687 := bstep (se 1 (by rfl) ⟨2238515, by rfl⟩ : syracuseStep 2984687 = 4477031) B4477031
theorem B6360515 : Blo 587289 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B1412563 : Blo 587289 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B1118279 : Blo 587289 1118279 := bstep (se 1 (by rfl) ⟨838709, by rfl⟩ : syracuseStep 1118279 = 1677419) B1677419
theorem B2691575 : Blo 587289 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B1413737 : Blo 587289 1413737 := bstep (se 2 (by rfl) ⟨530151, by rfl⟩ : syracuseStep 1413737 = 1060303) B1060303
theorem B2987117 : Blo 587289 2987117 := bstep (se 3 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 2987117 = 1120169) B1120169
theorem B6034571 : Blo 587289 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1676791 : Blo 587289 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B1513199 : Blo 587289 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B2824091 : Blo 587289 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B1415639 : Blo 587289 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B661999 : Blo 587289 661999 := bstep (se 1 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 661999 = 992999) B992999
theorem B2988575 : Blo 587289 2988575 := bstep (se 1 (by rfl) ⟨2241431, by rfl⟩ : syracuseStep 2988575 = 4482863) B4482863
theorem B7183019 : Blo 587289 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B3352535 : Blo 587289 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B2992463 : Blo 587289 2992463 := bstep (se 1 (by rfl) ⟨2244347, by rfl⟩ : syracuseStep 2992463 = 4488695) B4488695
theorem B993883 : Blo 587289 993883 := bstep (se 1 (by rfl) ⟨745412, by rfl⟩ : syracuseStep 993883 = 1490825) B1490825
theorem B797287 : Blo 587289 797287 := bstep (se 1 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 797287 = 1195931) B1195931
theorem B1682795 : Blo 587289 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B4468283 : Blo 587289 4468283 := bstep (se 1 (by rfl) ⟨3351212, by rfl⟩ : syracuseStep 4468283 = 6702425) B6702425
theorem B1257115 : Blo 587289 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B995375 : Blo 587289 995375 := bstep (se 1 (by rfl) ⟨746531, by rfl⟩ : syracuseStep 995375 = 1493063) B1493063
theorem B12103777 : Blo 587289 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B13578515 : Blo 587289 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B1323305 : Blo 587289 1323305 := bstep (se 2 (by rfl) ⟨496239, by rfl⟩ : syracuseStep 1323305 = 992479) B992479
theorem B1323359 : Blo 587289 1323359 := bstep (se 1 (by rfl) ⟨992519, by rfl⟩ : syracuseStep 1323359 = 1985039) B1985039
theorem B995881 : Blo 587289 995881 := bstep (se 2 (by rfl) ⟨373455, by rfl⟩ : syracuseStep 995881 = 746911) B746911
theorem B1323575 : Blo 587289 1323575 := bstep (se 1 (by rfl) ⟨992681, by rfl⟩ : syracuseStep 1323575 = 1985363) B1985363
theorem B2241371 : Blo 587289 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B1324079 : Blo 587289 1324079 := bstep (se 1 (by rfl) ⟨993059, by rfl⟩ : syracuseStep 1324079 = 1986119) B1986119
theorem B3355769 : Blo 587289 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B1062047 : Blo 587289 1062047 := bstep (se 1 (by rfl) ⟨796535, by rfl⟩ : syracuseStep 1062047 = 1593071) B1593071
theorem B6042937 : Blo 587289 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B2832047 : Blo 587289 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B2242313 : Blo 587289 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B128726819 : Blo 587289 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B7649761 : Blo 587289 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B2243497 : Blo 587289 2243497 := bstep (se 2 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 2243497 = 1682623) B1682623
theorem B5652179 : Blo 587289 5652179 := bstep (se 1 (by rfl) ⟨4239134, by rfl⟩ : syracuseStep 5652179 = 8478269) B8478269
theorem B1490663 : Blo 587289 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B6700967 : Blo 587289 6700967 := bstep (se 1 (by rfl) ⟨5025725, by rfl⟩ : syracuseStep 6700967 = 10051451) B10051451
theorem B1982447 : Blo 587289 1982447 := bstep (se 1 (by rfl) ⟨1486835, by rfl⟩ : syracuseStep 1982447 = 2973671) B2973671
theorem B1327247 : Blo 587289 1327247 := bstep (se 1 (by rfl) ⟨995435, by rfl⟩ : syracuseStep 1327247 = 1990871) B1990871
theorem B1327265 : Blo 587289 1327265 := bstep (se 2 (by rfl) ⟨497724, by rfl⟩ : syracuseStep 1327265 = 995449) B995449
theorem B1884329 : Blo 587289 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B1327355 : Blo 587289 1327355 := bstep (se 1 (by rfl) ⟨995516, by rfl⟩ : syracuseStep 1327355 = 1991033) B1991033
theorem B1261831 : Blo 587289 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B4473143 : Blo 587289 4473143 := bstep (se 1 (by rfl) ⟨3354857, by rfl⟩ : syracuseStep 4473143 = 6709715) B6709715
theorem B1491767 : Blo 587289 1491767 := bstep (se 1 (by rfl) ⟨1118825, by rfl⟩ : syracuseStep 1491767 = 2237651) B2237651
theorem B13649447 : Blo 587289 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B6801083 : Blo 587289 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B21546719 : Blo 587289 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B4474601 : Blo 587289 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B8046701 : Blo 587289 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B1493113 : Blo 587289 1493113 := bstep (se 2 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 1493113 = 1119835) B1119835
theorem B5359823 : Blo 587289 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B1329407 : Blo 587289 1329407 := bstep (se 1 (by rfl) ⟨997055, by rfl⟩ : syracuseStep 1329407 = 1994111) B1994111
theorem B1493255 : Blo 587289 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B22596083 : Blo 587289 22596083 := bstep (se 1 (by rfl) ⟨16947062, by rfl⟩ : syracuseStep 22596083 = 33894125) B33894125
theorem B3787519 : Blo 587289 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B1330127 : Blo 587289 1330127 := bstep (se 1 (by rfl) ⟨997595, by rfl⟩ : syracuseStep 1330127 = 1995191) B1995191
theorem B1985849 : Blo 587289 1985849 := bstep (se 2 (by rfl) ⟨744693, by rfl⟩ : syracuseStep 1985849 = 1489387) B1489387
theorem B5656175 : Blo 587289 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B9588779 : Blo 587289 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B2511071 : Blo 587289 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B3494345 : Blo 587289 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B840503 : Blo 587289 840503 := bstep (se 1 (by rfl) ⟨630377, by rfl⟩ : syracuseStep 840503 = 1260755) B1260755
theorem B1987415 : Blo 587289 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B1987577 : Blo 587289 1987577 := bstep (se 2 (by rfl) ⟨745341, by rfl⟩ : syracuseStep 1987577 = 1490683) B1490683
theorem B1496495 : Blo 587289 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3364517 : Blo 587289 3364517 := bstep (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) B630847
theorem B1890479 : Blo 587289 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B1988819 : Blo 587289 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B11229671 : Blo 587289 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B1006171 : Blo 587289 1006171 := bstep (se 1 (by rfl) ⟨754628, by rfl⟩ : syracuseStep 1006171 = 1509257) B1509257
theorem B10738331 : Blo 587289 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B1991465 : Blo 587289 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B1992923 : Blo 587289 1992923 := bstep (se 1 (by rfl) ⟨1494692, by rfl⟩ : syracuseStep 1992923 = 2989385) B2989385
theorem B2550599 : Blo 587289 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B5991241 : Blo 587289 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B2976749 : Blo 587289 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B1993895 : Blo 587289 1993895 := bstep (se 1 (by rfl) ⟨1495421, by rfl⟩ : syracuseStep 1993895 = 2990843) B2990843
theorem B6352127 : Blo 587289 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B946399 : Blo 587289 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B880937 : Blo 587289 880937 := bstep (se 2 (by rfl) ⟨330351, by rfl⟩ : syracuseStep 880937 = 660703) B660703
theorem B5042675 : Blo 587289 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B5665787 : Blo 587289 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B882089 : Blo 587289 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B882143 : Blo 587289 882143 := bstep (se 1 (by rfl) ⟨661607, by rfl⟩ : syracuseStep 882143 = 1323215) B1323215
theorem B587471 : Blo 587289 587471 := bstep (se 1 (by rfl) ⟨440603, by rfl⟩ : syracuseStep 587471 = 881207) B881207
theorem B587547 : Blo 587289 587547 := bstep (se 1 (by rfl) ⟨440660, by rfl⟩ : syracuseStep 587547 = 881321) B881321
theorem B587631 : Blo 587289 587631 := bstep (se 1 (by rfl) ⟨440723, by rfl⟩ : syracuseStep 587631 = 881447) B881447
theorem B587711 : Blo 587289 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B1701875 : Blo 587289 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B882791 : Blo 587289 882791 := bstep (se 1 (by rfl) ⟨662093, by rfl⟩ : syracuseStep 882791 = 1324187) B1324187
theorem B588031 : Blo 587289 588031 := bstep (se 1 (by rfl) ⟨441023, by rfl⟩ : syracuseStep 588031 = 882047) B882047
theorem B883175 : Blo 587289 883175 := bstep (se 1 (by rfl) ⟨662381, by rfl⟩ : syracuseStep 883175 = 1324763) B1324763
theorem B588571 : Blo 587289 588571 := bstep (se 1 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 588571 = 882857) B882857
theorem B5045273 : Blo 587289 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B588959 : Blo 587289 588959 := bstep (se 1 (by rfl) ⟨441719, by rfl⟩ : syracuseStep 588959 = 883439) B883439
theorem B884327 : Blo 587289 884327 := bstep (se 1 (by rfl) ⟨663245, by rfl⟩ : syracuseStep 884327 = 1326491) B1326491
theorem B6029149 : Blo 587289 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B2981771 : Blo 587289 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B884711 : Blo 587289 884711 := bstep (se 1 (by rfl) ⟨663533, by rfl⟩ : syracuseStep 884711 = 1327067) B1327067
theorem B589819 : Blo 587289 589819 := bstep (se 1 (by rfl) ⟨442364, by rfl⟩ : syracuseStep 589819 = 884729) B884729
theorem B589855 : Blo 587289 589855 := bstep (se 1 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 589855 = 884783) B884783
theorem B884831 : Blo 587289 884831 := bstep (se 1 (by rfl) ⟨663623, by rfl⟩ : syracuseStep 884831 = 1327247) B1327247
theorem B884843 : Blo 587289 884843 := bstep (se 1 (by rfl) ⟨663632, by rfl⟩ : syracuseStep 884843 = 1327265) B1327265
theorem B884903 : Blo 587289 884903 := bstep (se 1 (by rfl) ⟨663677, by rfl⟩ : syracuseStep 884903 = 1327355) B1327355
theorem B589991 : Blo 587289 589991 := bstep (se 1 (by rfl) ⟨442493, by rfl⟩ : syracuseStep 589991 = 884987) B884987
theorem B2982095 : Blo 587289 2982095 := bstep (se 1 (by rfl) ⟨2236571, by rfl⟩ : syracuseStep 2982095 = 4473143) B4473143
theorem B590143 : Blo 587289 590143 := bstep (se 1 (by rfl) ⟨442607, by rfl⟩ : syracuseStep 590143 = 885215) B885215
theorem B590719 : Blo 587289 590719 := bstep (se 1 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 590719 = 886079) B886079
theorem B2983067 : Blo 587289 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B3573215 : Blo 587289 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B886271 : Blo 587289 886271 := bstep (se 1 (by rfl) ⟨664703, by rfl⟩ : syracuseStep 886271 = 1329407) B1329407
theorem B2229889 : Blo 587289 2229889 := bstep (se 2 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 2229889 = 1672417) B1672417
theorem B22939307 : Blo 587289 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B7145263 : Blo 587289 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B886751 : Blo 587289 886751 := bstep (se 1 (by rfl) ⟨665063, by rfl⟩ : syracuseStep 886751 = 1330127) B1330127
theorem B3770783 : Blo 587289 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B6392519 : Blo 587289 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B1674047 : Blo 587289 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B5050025 : Blo 587289 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B4035197 : Blo 587289 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B1676153 : Blo 587289 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B2235023 : Blo 587289 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B2235721 : Blo 587289 2235721 := bstep (se 2 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 2235721 = 1676791) B1676791
theorem B4234751 : Blo 587289 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B1121863 : Blo 587289 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B663583 : Blo 587289 663583 := bstep (se 1 (by rfl) ⟨497687, by rfl⟩ : syracuseStep 663583 = 995375) B995375
theorem B9052343 : Blo 587289 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B10199681 : Blo 587289 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B3777191 : Blo 587289 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B2237179 : Blo 587289 2237179 := bstep (se 1 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 2237179 = 3355769) B3355769
theorem B2991329 : Blo 587289 2991329 := bstep (se 2 (by rfl) ⟨1121748, by rfl⟩ : syracuseStep 2991329 = 2243497) B2243497
theorem B8038865 : Blo 587289 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B993775 : Blo 587289 993775 := bstep (se 1 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 993775 = 1490663) B1490663
theorem B4467311 : Blo 587289 4467311 := bstep (se 1 (by rfl) ⟨3350483, by rfl⟩ : syracuseStep 4467311 = 6700967) B6700967
theorem B1321631 : Blo 587289 1321631 := bstep (se 1 (by rfl) ⟨991223, by rfl⟩ : syracuseStep 1321631 = 1982447) B1982447
theorem B1256219 : Blo 587289 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B1682441 : Blo 587289 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B994511 : Blo 587289 994511 := bstep (se 1 (by rfl) ⟨745883, by rfl⟩ : syracuseStep 994511 = 1491767) B1491767
theorem B16166395 : Blo 587289 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B4534055 : Blo 587289 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B14364479 : Blo 587289 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B9318253 : Blo 587289 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B995503 : Blo 587289 995503 := bstep (se 1 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 995503 = 1493255) B1493255
theorem B2241341 : Blo 587289 2241341 := bstep (se 3 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 2241341 = 840503) B840503
theorem B1323899 : Blo 587289 1323899 := bstep (se 1 (by rfl) ⟨992924, by rfl⟩ : syracuseStep 1323899 = 1985849) B1985849
theorem B4240343 : Blo 587289 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B1324943 : Blo 587289 1324943 := bstep (se 1 (by rfl) ⟨993707, by rfl⟩ : syracuseStep 1324943 = 1987415) B1987415
theorem B1325051 : Blo 587289 1325051 := bstep (se 1 (by rfl) ⟨993788, by rfl⟩ : syracuseStep 1325051 = 1987577) B1987577
theorem B1325177 : Blo 587289 1325177 := bstep (se 2 (by rfl) ⟨496941, by rfl⟩ : syracuseStep 1325177 = 993883) B993883
theorem B1063049 : Blo 587289 1063049 := bstep (se 2 (by rfl) ⟨398643, by rfl⟩ : syracuseStep 1063049 = 797287) B797287
theorem B997663 : Blo 587289 997663 := bstep (se 1 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 997663 = 1496495) B1496495
theorem B2243011 : Blo 587289 2243011 := bstep (se 1 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 2243011 = 3364517) B3364517
theorem B1882727 : Blo 587289 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B1325879 : Blo 587289 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B7486447 : Blo 587289 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B7158887 : Blo 587289 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B1883417 : Blo 587289 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B4538333 : Blo 587289 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B16138369 : Blo 587289 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B49725613 : Blo 587289 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B1261865 : Blo 587289 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B1327643 : Blo 587289 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B1327841 : Blo 587289 1327841 := bstep (se 2 (by rfl) ⟨497940, by rfl⟩ : syracuseStep 1327841 = 995881) B995881
theorem B1328615 : Blo 587289 1328615 := bstep (se 1 (by rfl) ⟨996461, by rfl⟩ : syracuseStep 1328615 = 1992923) B1992923
theorem B19154717 : Blo 587289 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B1984499 : Blo 587289 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B1329263 : Blo 587289 1329263 := bstep (se 1 (by rfl) ⟨996947, by rfl⟩ : syracuseStep 1329263 = 1993895) B1993895
theorem B3361783 : Blo 587289 3361783 := bstep (se 1 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 3361783 = 5042675) B5042675
theorem B1494247 : Blo 587289 1494247 := bstep (se 1 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 1494247 = 2241371) B2241371
theorem B708031 : Blo 587289 708031 := bstep (se 1 (by rfl) ⟨531023, by rfl⟩ : syracuseStep 708031 = 1062047) B1062047
theorem B1888031 : Blo 587289 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B1494875 : Blo 587289 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B3363515 : Blo 587289 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B1987847 : Blo 587289 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B1988927 : Blo 587289 1988927 := bstep (se 1 (by rfl) ⟨1491695, by rfl⟩ : syracuseStep 1988927 = 2983391) B2983391
theorem B9099631 : Blo 587289 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B5364467 : Blo 587289 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B9329627 : Blo 587289 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B15064055 : Blo 587289 15064055 := bstep (se 1 (by rfl) ⟨11298041, by rfl⟩ : syracuseStep 15064055 = 22596083) B22596083
theorem B1989791 : Blo 587289 1989791 := bstep (se 1 (by rfl) ⟨1492343, by rfl⟩ : syracuseStep 1989791 = 2984687) B2984687
theorem B745519 : Blo 587289 745519 := bstep (se 1 (by rfl) ⟨559139, by rfl⟩ : syracuseStep 745519 = 1118279) B1118279
theorem B1990817 : Blo 587289 1990817 := bstep (se 2 (by rfl) ⟨746556, by rfl⟩ : syracuseStep 1990817 = 1493113) B1493113
theorem B1794383 : Blo 587289 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B942491 : Blo 587289 942491 := bstep (se 1 (by rfl) ⟨706868, by rfl⟩ : syracuseStep 942491 = 1413737) B1413737
theorem B5366245 : Blo 587289 5366245 := bstep (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) B1006171
theorem B1991411 : Blo 587289 1991411 := bstep (se 1 (by rfl) ⟨1493558, by rfl⟩ : syracuseStep 1991411 = 2987117) B2987117
theorem B4023047 : Blo 587289 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B7988321 : Blo 587289 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B943759 : Blo 587289 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B1992383 : Blo 587289 1992383 := bstep (se 1 (by rfl) ⟨1494287, by rfl⟩ : syracuseStep 1992383 = 2988575) B2988575
theorem B7170565 : Blo 587289 7170565 := bstep (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) B1344481
theorem B5041277 : Blo 587289 5041277 := bstep (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) B1890479
theorem B1994975 : Blo 587289 1994975 := bstep (se 1 (by rfl) ⟨1496231, by rfl⟩ : syracuseStep 1994975 = 2992463) B2992463
theorem B8057249 : Blo 587289 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1700399 : Blo 587289 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B2978855 : Blo 587289 2978855 := bstep (se 1 (by rfl) ⟨2234141, by rfl⟩ : syracuseStep 2978855 = 4468283) B4468283
theorem B587291 : Blo 587289 587291 := bstep (se 1 (by rfl) ⟨440468, by rfl⟩ : syracuseStep 587291 = 880937) B880937
theorem B882203 : Blo 587289 882203 := bstep (se 1 (by rfl) ⟨661652, by rfl⟩ : syracuseStep 882203 = 1323305) B1323305
theorem B882239 : Blo 587289 882239 := bstep (se 1 (by rfl) ⟨661679, by rfl⟩ : syracuseStep 882239 = 1323359) B1323359
theorem B882383 : Blo 587289 882383 := bstep (se 1 (by rfl) ⟨661787, by rfl⟩ : syracuseStep 882383 = 1323575) B1323575
theorem B882665 : Blo 587289 882665 := bstep (se 2 (by rfl) ⟨330999, by rfl⟩ : syracuseStep 882665 = 661999) B661999
theorem B882719 : Blo 587289 882719 := bstep (se 1 (by rfl) ⟨662039, by rfl⟩ : syracuseStep 882719 = 1324079) B1324079
theorem B588059 : Blo 587289 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B588095 : Blo 587289 588095 := bstep (se 1 (by rfl) ⟨441071, by rfl⟩ : syracuseStep 588095 = 882143) B882143
theorem B85817879 : Blo 587289 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B588527 : Blo 587289 588527 := bstep (se 1 (by rfl) ⟨441395, by rfl⟩ : syracuseStep 588527 = 882791) B882791
theorem B588783 : Blo 587289 588783 := bstep (se 1 (by rfl) ⟨441587, by rfl⟩ : syracuseStep 588783 = 883175) B883175
theorem B589551 : Blo 587289 589551 := bstep (se 1 (by rfl) ⟨442163, by rfl⟩ : syracuseStep 589551 = 884327) B884327
theorem B3768119 : Blo 587289 3768119 := bstep (se 1 (by rfl) ⟨2826089, by rfl⟩ : syracuseStep 3768119 = 5652179) B5652179
theorem B589807 : Blo 587289 589807 := bstep (se 1 (by rfl) ⟨442355, by rfl⟩ : syracuseStep 589807 = 884711) B884711
theorem B884777 : Blo 587289 884777 := bstep (se 2 (by rfl) ⟨331791, by rfl⟩ : syracuseStep 884777 = 663583) B663583
theorem B589887 : Blo 587289 589887 := bstep (se 1 (by rfl) ⟨442415, by rfl⟩ : syracuseStep 589887 = 884831) B884831
theorem B589895 : Blo 587289 589895 := bstep (se 1 (by rfl) ⟨442421, by rfl⟩ : syracuseStep 589895 = 884843) B884843
theorem B589935 : Blo 587289 589935 := bstep (se 1 (by rfl) ⟨442451, by rfl⟩ : syracuseStep 589935 = 884903) B884903
theorem B885095 : Blo 587289 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B885227 : Blo 587289 885227 := bstep (se 1 (by rfl) ⟨663920, by rfl⟩ : syracuseStep 885227 = 1327841) B1327841
theorem B885743 : Blo 587289 885743 := bstep (se 1 (by rfl) ⟨664307, by rfl⟩ : syracuseStep 885743 = 1328615) B1328615
theorem B2982905 : Blo 587289 2982905 := bstep (se 2 (by rfl) ⟨1118589, by rfl⟩ : syracuseStep 2982905 = 2237179) B2237179
theorem B590847 : Blo 587289 590847 := bstep (se 1 (by rfl) ⟨443135, by rfl⟩ : syracuseStep 590847 = 886271) B886271
theorem B591167 : Blo 587289 591167 := bstep (se 1 (by rfl) ⟨443375, by rfl⟩ : syracuseStep 591167 = 886751) B886751
theorem B886175 : Blo 587289 886175 := bstep (se 1 (by rfl) ⟨664631, by rfl⟩ : syracuseStep 886175 = 1329263) B1329263
theorem B4261679 : Blo 587289 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B1116031 : Blo 587289 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B2690131 : Blo 587289 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B3576311 : Blo 587289 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B2823167 : Blo 587289 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B12424337 : Blo 587289 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B6034895 : Blo 587289 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B628327 : Blo 587289 628327 := bstep (se 1 (by rfl) ⟨471245, by rfl⟩ : syracuseStep 628327 = 942491) B942491
theorem B1121627 : Blo 587289 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B663007 : Blo 587289 663007 := bstep (se 1 (by rfl) ⟨497255, by rfl⟩ : syracuseStep 663007 = 994511) B994511
theorem B3776165 : Blo 587289 3776165 := bstep (se 4 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 3776165 = 708031) B708031
theorem B3022703 : Blo 587289 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B9576319 : Blo 587289 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B24879005 : Blo 587289 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B12132841 : Blo 587289 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B2990681 : Blo 587289 2990681 := bstep (se 2 (by rfl) ⟨1121505, by rfl⟩ : syracuseStep 2990681 = 2243011) B2243011
theorem B2826895 : Blo 587289 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B5022445 : Blo 587289 5022445 := bstep (se 3 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 5022445 = 1883417) B1883417
theorem B1255151 : Blo 587289 1255151 := bstep (se 1 (by rfl) ⟨941363, by rfl⟩ : syracuseStep 1255151 = 1882727) B1882727
theorem B3025555 : Blo 587289 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B994025 : Blo 587289 994025 := bstep (se 2 (by rfl) ⟨372759, by rfl⟩ : syracuseStep 994025 = 745519) B745519
theorem B66300817 : Blo 587289 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B7154993 : Blo 587289 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B1322999 : Blo 587289 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B10728125 : Blo 587289 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1258345 : Blo 587289 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B4469741 : Blo 587289 4469741 := bstep (se 3 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 4469741 = 1676153) B1676153
theorem B1258687 : Blo 587289 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B996583 : Blo 587289 996583 := bstep (se 1 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 996583 = 1494875) B1494875
theorem B2242343 : Blo 587289 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B1325033 : Blo 587289 1325033 := bstep (se 2 (by rfl) ⟨496887, by rfl⟩ : syracuseStep 1325033 = 993775) B993775
theorem B1325231 : Blo 587289 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B1325951 : Blo 587289 1325951 := bstep (se 1 (by rfl) ⟨994463, by rfl⟩ : syracuseStep 1325951 = 1988927) B1988927
theorem B1490015 : Blo 587289 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B10042703 : Blo 587289 10042703 := bstep (se 1 (by rfl) ⟨7532027, by rfl⟩ : syracuseStep 10042703 = 15064055) B15064055
theorem B1326527 : Blo 587289 1326527 := bstep (se 1 (by rfl) ⟨994895, by rfl⟩ : syracuseStep 1326527 = 1989791) B1989791
theorem B1327211 : Blo 587289 1327211 := bstep (se 1 (by rfl) ⟨995408, by rfl⟩ : syracuseStep 1327211 = 1990817) B1990817
theorem B1196255 : Blo 587289 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1327337 : Blo 587289 1327337 := bstep (se 2 (by rfl) ⟨497751, by rfl⟩ : syracuseStep 1327337 = 995503) B995503
theorem B2834797 : Blo 587289 2834797 := bstep (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) B1063049
theorem B6799787 : Blo 587289 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B1327607 : Blo 587289 1327607 := bstep (se 1 (by rfl) ⟨995705, by rfl⟩ : syracuseStep 1327607 = 1991411) B1991411
theorem B5325547 : Blo 587289 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B1328255 : Blo 587289 1328255 := bstep (se 1 (by rfl) ⟨996191, by rfl⟩ : syracuseStep 1328255 = 1992383) B1992383
theorem B5359243 : Blo 587289 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B837479 : Blo 587289 837479 := bstep (se 1 (by rfl) ⟨628109, by rfl⟩ : syracuseStep 837479 = 1256219) B1256219
theorem B3360851 : Blo 587289 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B1329983 : Blo 587289 1329983 := bstep (se 1 (by rfl) ⟨997487, by rfl⟩ : syracuseStep 1329983 = 1994975) B1994975
theorem B1133599 : Blo 587289 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B1330217 : Blo 587289 1330217 := bstep (se 2 (by rfl) ⟨498831, by rfl⟩ : syracuseStep 1330217 = 997663) B997663
theorem B1494227 : Blo 587289 1494227 := bstep (se 1 (by rfl) ⟨1120670, by rfl⟩ : syracuseStep 1494227 = 2241341) B2241341
theorem B1985903 : Blo 587289 1985903 := bstep (se 1 (by rfl) ⟨1489427, by rfl⟩ : syracuseStep 1985903 = 2978855) B2978855
theorem B9981929 : Blo 587289 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B4772591 : Blo 587289 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B1495817 : Blo 587289 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B2512079 : Blo 587289 2512079 := bstep (se 1 (by rfl) ⟨1884059, by rfl⟩ : syracuseStep 2512079 = 3768119) B3768119
theorem B1988063 : Blo 587289 1988063 := bstep (se 1 (by rfl) ⟨1491047, by rfl⟩ : syracuseStep 1988063 = 2982095) B2982095
theorem B21517825 : Blo 587289 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B1988711 : Blo 587289 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B3364973 : Blo 587289 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B2382143 : Blo 587289 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B15292871 : Blo 587289 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B12769811 : Blo 587289 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B2513855 : Blo 587289 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B2973185 : Blo 587289 2973185 := bstep (se 2 (by rfl) ⟨1114944, by rfl⟩ : syracuseStep 2973185 = 2229889) B2229889
theorem B9527017 : Blo 587289 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B3366683 : Blo 587289 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B9560753 : Blo 587289 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B4482377 : Blo 587289 4482377 := bstep (se 2 (by rfl) ⟨1680891, by rfl⟩ : syracuseStep 4482377 = 3361783) B3361783
theorem B1992329 : Blo 587289 1992329 := bstep (se 2 (by rfl) ⟨747123, by rfl⟩ : syracuseStep 1992329 = 1494247) B1494247
theorem B21555193 : Blo 587289 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B2518127 : Blo 587289 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B1994219 : Blo 587289 1994219 := bstep (se 1 (by rfl) ⟨1495664, by rfl⟩ : syracuseStep 1994219 = 2991329) B2991329
theorem B2978207 : Blo 587289 2978207 := bstep (se 1 (by rfl) ⟨2233655, by rfl⟩ : syracuseStep 2978207 = 4467311) B4467311
theorem B881087 : Blo 587289 881087 := bstep (se 1 (by rfl) ⟨660815, by rfl⟩ : syracuseStep 881087 = 1321631) B1321631
theorem B5371499 : Blo 587289 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B882599 : Blo 587289 882599 := bstep (se 1 (by rfl) ⟨661949, by rfl⟩ : syracuseStep 882599 = 1323899) B1323899
theorem B588135 : Blo 587289 588135 := bstep (se 1 (by rfl) ⟨441101, by rfl⟩ : syracuseStep 588135 = 882203) B882203
theorem B588159 : Blo 587289 588159 := bstep (se 1 (by rfl) ⟨441119, by rfl⟩ : syracuseStep 588159 = 882239) B882239
theorem B588255 : Blo 587289 588255 := bstep (se 1 (by rfl) ⟨441191, by rfl⟩ : syracuseStep 588255 = 882383) B882383
theorem B883295 : Blo 587289 883295 := bstep (se 1 (by rfl) ⟨662471, by rfl⟩ : syracuseStep 883295 = 1324943) B1324943
theorem B588443 : Blo 587289 588443 := bstep (se 1 (by rfl) ⟨441332, by rfl⟩ : syracuseStep 588443 = 882665) B882665
theorem B883367 : Blo 587289 883367 := bstep (se 1 (by rfl) ⟨662525, by rfl⟩ : syracuseStep 883367 = 1325051) B1325051
theorem B588479 : Blo 587289 588479 := bstep (se 1 (by rfl) ⟨441359, by rfl⟩ : syracuseStep 588479 = 882719) B882719
theorem B883451 : Blo 587289 883451 := bstep (se 1 (by rfl) ⟨662588, by rfl⟩ : syracuseStep 883451 = 1325177) B1325177
theorem B57211919 : Blo 587289 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B2980961 : Blo 587289 2980961 := bstep (se 2 (by rfl) ⟨1117860, by rfl⟩ : syracuseStep 2980961 = 2235721) B2235721
theorem B883919 : Blo 587289 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B589851 : Blo 587289 589851 := bstep (se 1 (by rfl) ⟨442388, by rfl⟩ : syracuseStep 589851 = 884777) B884777
theorem B884807 : Blo 587289 884807 := bstep (se 1 (by rfl) ⟨663605, by rfl⟩ : syracuseStep 884807 = 1327211) B1327211
theorem B884891 : Blo 587289 884891 := bstep (se 1 (by rfl) ⟨663668, by rfl⟩ : syracuseStep 884891 = 1327337) B1327337
theorem B590063 : Blo 587289 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B590151 : Blo 587289 590151 := bstep (se 1 (by rfl) ⟨442613, by rfl⟩ : syracuseStep 590151 = 885227) B885227
theorem B885071 : Blo 587289 885071 := bstep (se 1 (by rfl) ⟨663803, by rfl⟩ : syracuseStep 885071 = 1327607) B1327607
theorem B590495 : Blo 587289 590495 := bstep (se 1 (by rfl) ⟨442871, by rfl⟩ : syracuseStep 590495 = 885743) B885743
theorem B885503 : Blo 587289 885503 := bstep (se 1 (by rfl) ⟨664127, by rfl⟩ : syracuseStep 885503 = 1328255) B1328255
theorem B3769193 : Blo 587289 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B590783 : Blo 587289 590783 := bstep (se 1 (by rfl) ⟨443087, by rfl⟩ : syracuseStep 590783 = 886175) B886175
theorem B886655 : Blo 587289 886655 := bstep (se 1 (by rfl) ⟨664991, by rfl⟩ : syracuseStep 886655 = 1329983) B1329983
theorem B886811 : Blo 587289 886811 := bstep (se 1 (by rfl) ⟨665108, by rfl⟩ : syracuseStep 886811 = 1330217) B1330217
theorem B7145657 : Blo 587289 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B6654619 : Blo 587289 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B28740257 : Blo 587289 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B3181727 : Blo 587289 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B1674719 : Blo 587289 1674719 := bstep (se 1 (by rfl) ⟨1256039, by rfl⟩ : syracuseStep 1674719 = 2512079) B2512079
theorem B1511465 : Blo 587289 1511465 := bstep (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) B1133599
theorem B10195247 : Blo 587289 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B1675903 : Blo 587289 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B2233277 : Blo 587289 2233277 := bstep (se 3 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 2233277 = 837479) B837479
theorem B16586003 : Blo 587289 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B2988251 : Blo 587289 2988251 := bstep (se 1 (by rfl) ⟨2241188, by rfl⟩ : syracuseStep 2988251 = 4482377) B4482377
theorem B1678249 : Blo 587289 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B662683 : Blo 587289 662683 := bstep (se 1 (by rfl) ⟨497012, by rfl⟩ : syracuseStep 662683 = 994025) B994025
theorem B1678751 : Blo 587289 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B7152083 : Blo 587289 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B3351077 : Blo 587289 3351077 := bstep (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) B628327
theorem B19079981 : Blo 587289 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B2991005 : Blo 587289 2991005 := bstep (se 3 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 2991005 = 1121627) B1121627
theorem B3580999 : Blo 587289 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B993343 : Blo 587289 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B6695135 : Blo 587289 6695135 := bstep (se 1 (by rfl) ⟨5021351, by rfl⟩ : syracuseStep 6695135 = 10042703) B10042703
theorem B4533191 : Blo 587289 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B3779729 : Blo 587289 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B3190013 : Blo 587289 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B6696593 : Blo 587289 6696593 := bstep (se 2 (by rfl) ⟨2511222, by rfl⟩ : syracuseStep 6696593 = 5022445) B5022445
theorem B2240567 : Blo 587289 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B996151 : Blo 587289 996151 := bstep (se 1 (by rfl) ⟨747113, by rfl⟩ : syracuseStep 996151 = 1494227) B1494227
theorem B1323935 : Blo 587289 1323935 := bstep (se 1 (by rfl) ⟨992951, by rfl⟩ : syracuseStep 1323935 = 1985903) B1985903
theorem B1488041 : Blo 587289 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B997211 : Blo 587289 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B1882111 : Blo 587289 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B1325375 : Blo 587289 1325375 := bstep (se 1 (by rfl) ⟨994031, by rfl⟩ : syracuseStep 1325375 = 1988063) B1988063
theorem B1325807 : Blo 587289 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B2243315 : Blo 587289 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B3586841 : Blo 587289 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B1982123 : Blo 587289 1982123 := bstep (se 1 (by rfl) ⟨1486592, by rfl⟩ : syracuseStep 1982123 = 2973185) B2973185
theorem B2244455 : Blo 587289 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B2015135 : Blo 587289 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B6373835 : Blo 587289 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B1328219 : Blo 587289 1328219 := bstep (se 1 (by rfl) ⟨996164, by rfl⟩ : syracuseStep 1328219 = 1992329) B1992329
theorem B836767 : Blo 587289 836767 := bstep (se 1 (by rfl) ⟨627575, by rfl⟩ : syracuseStep 836767 = 1255151) B1255151
theorem B1328777 : Blo 587289 1328777 := bstep (se 2 (by rfl) ⟨498291, by rfl⟩ : syracuseStep 1328777 = 996583) B996583
theorem B28690433 : Blo 587289 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B1329479 : Blo 587289 1329479 := bstep (se 1 (by rfl) ⟨997109, by rfl⟩ : syracuseStep 1329479 = 1994219) B1994219
theorem B1985471 : Blo 587289 1985471 := bstep (se 1 (by rfl) ⟨1489103, by rfl⟩ : syracuseStep 1985471 = 2978207) B2978207
theorem B1494895 : Blo 587289 1494895 := bstep (se 1 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 1494895 = 2242343) B2242343
theorem B1987307 : Blo 587289 1987307 := bstep (se 1 (by rfl) ⟨1490480, by rfl⟩ : syracuseStep 1987307 = 2980961) B2980961
theorem B12702689 : Blo 587289 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B12768425 : Blo 587289 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B16177121 : Blo 587289 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B1988603 : Blo 587289 1988603 := bstep (se 1 (by rfl) ⟨1491452, by rfl⟩ : syracuseStep 1988603 = 2982905) B2982905
theorem B7100729 : Blo 587289 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B2841119 : Blo 587289 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B2384207 : Blo 587289 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B64545173 : Blo 587289 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B8282891 : Blo 587289 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B4023263 : Blo 587289 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B88401089 : Blo 587289 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B8513207 : Blo 587289 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B6711173 : Blo 587289 6711173 := bstep (se 4 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 6711173 = 1258345) B1258345
theorem B2517443 : Blo 587289 2517443 := bstep (se 1 (by rfl) ⟨1888082, by rfl⟩ : syracuseStep 2517443 = 3776165) B3776165
theorem B1993787 : Blo 587289 1993787 := bstep (se 1 (by rfl) ⟨1495340, by rfl⟩ : syracuseStep 1993787 = 2990681) B2990681
theorem B6352381 : Blo 587289 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B881999 : Blo 587289 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B587391 : Blo 587289 587391 := bstep (se 1 (by rfl) ⟨440543, by rfl⟩ : syracuseStep 587391 = 881087) B881087
theorem B2979827 : Blo 587289 2979827 := bstep (se 1 (by rfl) ⟨2234870, by rfl⟩ : syracuseStep 2979827 = 4469741) B4469741
theorem B588399 : Blo 587289 588399 := bstep (se 1 (by rfl) ⟨441299, by rfl⟩ : syracuseStep 588399 = 882599) B882599
theorem B883355 : Blo 587289 883355 := bstep (se 1 (by rfl) ⟨662516, by rfl⟩ : syracuseStep 883355 = 1325033) B1325033
theorem B883487 : Blo 587289 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B588863 : Blo 587289 588863 := bstep (se 1 (by rfl) ⟨441647, by rfl⟩ : syracuseStep 588863 = 883295) B883295
theorem B588911 : Blo 587289 588911 := bstep (se 1 (by rfl) ⟨441683, by rfl⟩ : syracuseStep 588911 = 883367) B883367
theorem B588967 : Blo 587289 588967 := bstep (se 1 (by rfl) ⟨441725, by rfl⟩ : syracuseStep 588967 = 883451) B883451
theorem B883967 : Blo 587289 883967 := bstep (se 1 (by rfl) ⟨662975, by rfl⟩ : syracuseStep 883967 = 1325951) B1325951
theorem B884009 : Blo 587289 884009 := bstep (se 2 (by rfl) ⟨331503, by rfl⟩ : syracuseStep 884009 = 663007) B663007
theorem B38141279 : Blo 587289 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B589279 : Blo 587289 589279 := bstep (se 1 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 589279 = 883919) B883919
theorem B884351 : Blo 587289 884351 := bstep (se 1 (by rfl) ⟨663263, by rfl⟩ : syracuseStep 884351 = 1326527) B1326527
theorem B589871 : Blo 587289 589871 := bstep (se 1 (by rfl) ⟨442403, by rfl⟩ : syracuseStep 589871 = 884807) B884807
theorem B589927 : Blo 587289 589927 := bstep (se 1 (by rfl) ⟨442445, by rfl⟩ : syracuseStep 589927 = 884891) B884891
theorem B4030573 : Blo 587289 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B590047 : Blo 587289 590047 := bstep (se 1 (by rfl) ⟨442535, by rfl⟩ : syracuseStep 590047 = 885071) B885071
theorem B590335 : Blo 587289 590335 := bstep (se 1 (by rfl) ⟨442751, by rfl⟩ : syracuseStep 590335 = 885503) B885503
theorem B885479 : Blo 587289 885479 := bstep (se 1 (by rfl) ⟨664109, by rfl⟩ : syracuseStep 885479 = 1328219) B1328219
theorem B885851 : Blo 587289 885851 := bstep (se 1 (by rfl) ⟨664388, by rfl⟩ : syracuseStep 885851 = 1328777) B1328777
theorem B591103 : Blo 587289 591103 := bstep (se 1 (by rfl) ⟨443327, by rfl⟩ : syracuseStep 591103 = 886655) B886655
theorem B591207 : Blo 587289 591207 := bstep (se 1 (by rfl) ⟨443405, by rfl⟩ : syracuseStep 591207 = 886811) B886811
theorem B1115689 : Blo 587289 1115689 := bstep (se 2 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 1115689 = 836767) B836767
theorem B886319 : Blo 587289 886319 := bstep (se 1 (by rfl) ⟨664739, by rfl⟩ : syracuseStep 886319 = 1329479) B1329479
theorem B22087709 : Blo 587289 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B1116479 : Blo 587289 1116479 := bstep (se 1 (by rfl) ⟨837359, by rfl⟩ : syracuseStep 1116479 = 1674719) B1674719
theorem B235736237 : Blo 587289 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B35491301 : Blo 587289 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B10784747 : Blo 587289 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B1119167 : Blo 587289 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B43030115 : Blo 587289 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B2234051 : Blo 587289 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B12719987 : Blo 587289 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B2234537 : Blo 587289 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B5675471 : Blo 587289 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B4463423 : Blo 587289 4463423 := bstep (se 1 (by rfl) ⟨3347567, by rfl⟩ : syracuseStep 4463423 = 6695135) B6695135
theorem B1678295 : Blo 587289 1678295 := bstep (se 1 (by rfl) ⟨1258721, by rfl⟩ : syracuseStep 1678295 = 2517443) B2517443
theorem B3022127 : Blo 587289 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B4464395 : Blo 587289 4464395 := bstep (se 1 (by rfl) ⟨3348296, by rfl⟩ : syracuseStep 4464395 = 6696593) B6696593
theorem B992027 : Blo 587289 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B2237665 : Blo 587289 2237665 := bstep (se 2 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 2237665 = 1678249) B1678249
theorem B664807 : Blo 587289 664807 := bstep (se 1 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 664807 = 997211) B997211
theorem B1321415 : Blo 587289 1321415 := bstep (se 1 (by rfl) ⟨991061, by rfl⟩ : syracuseStep 1321415 = 1982123) B1982123
theorem B4763771 : Blo 587289 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B1323647 : Blo 587289 1323647 := bstep (se 1 (by rfl) ⟨992735, by rfl⟩ : syracuseStep 1323647 = 1985471) B1985471
theorem B1324457 : Blo 587289 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B6796831 : Blo 587289 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1324871 : Blo 587289 1324871 := bstep (se 1 (by rfl) ⟨993653, by rfl⟩ : syracuseStep 1324871 = 1987307) B1987307
theorem B1488851 : Blo 587289 1488851 := bstep (se 1 (by rfl) ⟨1116638, by rfl⟩ : syracuseStep 1488851 = 2233277) B2233277
theorem B8468459 : Blo 587289 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B1325735 : Blo 587289 1325735 := bstep (se 1 (by rfl) ⟨994301, by rfl⟩ : syracuseStep 1325735 = 1988603) B1988603
theorem B4733819 : Blo 587289 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B8469841 : Blo 587289 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B1589471 : Blo 587289 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B4768055 : Blo 587289 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B1328201 : Blo 587289 1328201 := bstep (se 2 (by rfl) ⟨498075, by rfl⟩ : syracuseStep 1328201 = 996151) B996151
theorem B4474115 : Blo 587289 4474115 := bstep (se 1 (by rfl) ⟨3355586, by rfl⟩ : syracuseStep 4474115 = 6711173) B6711173
theorem B1329191 : Blo 587289 1329191 := bstep (se 1 (by rfl) ⟨996893, by rfl⟩ : syracuseStep 1329191 = 1993787) B1993787
theorem B2509481 : Blo 587289 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B1493711 : Blo 587289 1493711 := bstep (se 1 (by rfl) ⟨1120283, by rfl⟩ : syracuseStep 1493711 = 2240567) B2240567
theorem B1986551 : Blo 587289 1986551 := bstep (se 1 (by rfl) ⟨1489913, by rfl⟩ : syracuseStep 1986551 = 2979827) B2979827
theorem B1495543 : Blo 587289 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B1496303 : Blo 587289 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B4249223 : Blo 587289 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B2512795 : Blo 587289 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B19126955 : Blo 587289 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B19160171 : Blo 587289 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B2121151 : Blo 587289 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B44229341 : Blo 587289 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B8512283 : Blo 587289 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B1992167 : Blo 587289 1992167 := bstep (se 1 (by rfl) ⟨1494125, by rfl⟩ : syracuseStep 1992167 = 2988251) B2988251
theorem B1894079 : Blo 587289 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B1993193 : Blo 587289 1993193 := bstep (se 2 (by rfl) ⟨747447, by rfl⟩ : syracuseStep 1993193 = 1494895) B1494895
theorem B19098661 : Blo 587289 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B1994003 : Blo 587289 1994003 := bstep (se 1 (by rfl) ⟨1495502, by rfl⟩ : syracuseStep 1994003 = 2991005) B2991005
theorem B2682175 : Blo 587289 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B2519819 : Blo 587289 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B2126675 : Blo 587289 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B882623 : Blo 587289 882623 := bstep (se 1 (by rfl) ⟨661967, by rfl⟩ : syracuseStep 882623 = 1323935) B1323935
theorem B587999 : Blo 587289 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B883577 : Blo 587289 883577 := bstep (se 2 (by rfl) ⟨331341, by rfl⟩ : syracuseStep 883577 = 662683) B662683
theorem B883583 : Blo 587289 883583 := bstep (se 1 (by rfl) ⟨662687, by rfl⟩ : syracuseStep 883583 = 1325375) B1325375
theorem B588903 : Blo 587289 588903 := bstep (se 1 (by rfl) ⟨441677, by rfl⟩ : syracuseStep 588903 = 883355) B883355
theorem B883871 : Blo 587289 883871 := bstep (se 1 (by rfl) ⟨662903, by rfl⟩ : syracuseStep 883871 = 1325807) B1325807
theorem B2391227 : Blo 587289 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B588991 : Blo 587289 588991 := bstep (se 1 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 588991 = 883487) B883487
theorem B589311 : Blo 587289 589311 := bstep (se 1 (by rfl) ⟨441983, by rfl⟩ : syracuseStep 589311 = 883967) B883967
theorem B589339 : Blo 587289 589339 := bstep (se 1 (by rfl) ⟨442004, by rfl⟩ : syracuseStep 589339 = 884009) B884009
theorem B25427519 : Blo 587289 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B589567 : Blo 587289 589567 := bstep (se 1 (by rfl) ⟨442175, by rfl⟩ : syracuseStep 589567 = 884351) B884351
theorem B1343423 : Blo 587289 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B5374097 : Blo 587289 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B3178703 : Blo 587289 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B235602229 : Blo 587289 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B590319 : Blo 587289 590319 := bstep (se 1 (by rfl) ⟨442739, by rfl⟩ : syracuseStep 590319 = 885479) B885479
theorem B885467 : Blo 587289 885467 := bstep (se 1 (by rfl) ⟨664100, by rfl⟩ : syracuseStep 885467 = 1328201) B1328201
theorem B590567 : Blo 587289 590567 := bstep (se 1 (by rfl) ⟨442925, by rfl⟩ : syracuseStep 590567 = 885851) B885851
theorem B2982743 : Blo 587289 2982743 := bstep (se 1 (by rfl) ⟨2237057, by rfl⟩ : syracuseStep 2982743 = 4474115) B4474115
theorem B590879 : Blo 587289 590879 := bstep (se 1 (by rfl) ⟨443159, by rfl⟩ : syracuseStep 590879 = 886319) B886319
theorem B886127 : Blo 587289 886127 := bstep (se 1 (by rfl) ⟨664595, by rfl⟩ : syracuseStep 886127 = 1329191) B1329191
theorem B2983553 : Blo 587289 2983553 := bstep (se 2 (by rfl) ⟨1118832, by rfl⟩ : syracuseStep 2983553 = 2237665) B2237665
theorem B886409 : Blo 587289 886409 := bstep (se 2 (by rfl) ⟨332403, by rfl⟩ : syracuseStep 886409 = 664807) B664807
theorem B1672987 : Blo 587289 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B157157491 : Blo 587289 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B5671133 : Blo 587289 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B23660867 : Blo 587289 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B25464881 : Blo 587289 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B3576233 : Blo 587289 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B12751303 : Blo 587289 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B1118863 : Blo 587289 1118863 := bstep (se 1 (by rfl) ⟨839147, by rfl⟩ : syracuseStep 1118863 = 1678295) B1678295
theorem B661351 : Blo 587289 661351 := bstep (se 1 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 661351 = 992027) B992027
theorem B5674855 : Blo 587289 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B3350393 : Blo 587289 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B1679879 : Blo 587289 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B992567 : Blo 587289 992567 := bstep (se 1 (by rfl) ⟨744425, by rfl⟩ : syracuseStep 992567 = 1488851) B1488851
theorem B5645639 : Blo 587289 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B3155879 : Blo 587289 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B2828201 : Blo 587289 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B16951679 : Blo 587289 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B3582461 : Blo 587289 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B1059647 : Blo 587289 1059647 := bstep (se 1 (by rfl) ⟨794735, by rfl⟩ : syracuseStep 1059647 = 1589471) B1589471
theorem B995807 : Blo 587289 995807 := bstep (se 1 (by rfl) ⟨746855, by rfl⟩ : syracuseStep 995807 = 1493711) B1493711
theorem B1487585 : Blo 587289 1487585 := bstep (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) B1115689
theorem B7189831 : Blo 587289 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B1324367 : Blo 587289 1324367 := bstep (se 1 (by rfl) ⟨993275, by rfl⟩ : syracuseStep 1324367 = 1986551) B1986551
theorem B997535 : Blo 587289 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B28686743 : Blo 587289 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B2832815 : Blo 587289 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B1489367 : Blo 587289 1489367 := bstep (se 1 (by rfl) ⟨1117025, by rfl⟩ : syracuseStep 1489367 = 2234051) B2234051
theorem B1489691 : Blo 587289 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B3783647 : Blo 587289 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B2014751 : Blo 587289 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B1328111 : Blo 587289 1328111 := bstep (se 1 (by rfl) ⟨996083, by rfl⟩ : syracuseStep 1328111 = 1992167) B1992167
theorem B1262719 : Blo 587289 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B1328795 : Blo 587289 1328795 := bstep (se 1 (by rfl) ⟨996596, by rfl⟩ : syracuseStep 1328795 = 1993193) B1993193
theorem B9062441 : Blo 587289 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1329335 : Blo 587289 1329335 := bstep (se 1 (by rfl) ⟨997001, by rfl⟩ : syracuseStep 1329335 = 1994003) B1994003
theorem B11293121 : Blo 587289 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1594151 : Blo 587289 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B744319 : Blo 587289 744319 := bstep (se 1 (by rfl) ⟨558239, by rfl⟩ : syracuseStep 744319 = 1116479) B1116479
theorem B746111 : Blo 587289 746111 := bstep (se 1 (by rfl) ⟨559583, by rfl⟩ : syracuseStep 746111 = 1119167) B1119167
theorem B8479991 : Blo 587289 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B2975615 : Blo 587289 2975615 := bstep (se 1 (by rfl) ⟨2231711, by rfl⟩ : syracuseStep 2975615 = 4463423) B4463423
theorem B12773447 : Blo 587289 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B2976263 : Blo 587289 2976263 := bstep (se 1 (by rfl) ⟨2232197, by rfl⟩ : syracuseStep 2976263 = 4464395) B4464395
theorem B29486227 : Blo 587289 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B1994057 : Blo 587289 1994057 := bstep (se 2 (by rfl) ⟨747771, by rfl⟩ : syracuseStep 1994057 = 1495543) B1495543
theorem B880943 : Blo 587289 880943 := bstep (se 1 (by rfl) ⟨660707, by rfl⟩ : syracuseStep 880943 = 1321415) B1321415
theorem B3175847 : Blo 587289 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B882431 : Blo 587289 882431 := bstep (se 1 (by rfl) ⟨661823, by rfl⟩ : syracuseStep 882431 = 1323647) B1323647
theorem B882971 : Blo 587289 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B883247 : Blo 587289 883247 := bstep (se 1 (by rfl) ⟨662435, by rfl⟩ : syracuseStep 883247 = 1324871) B1324871
theorem B588415 : Blo 587289 588415 := bstep (se 1 (by rfl) ⟨441311, by rfl⟩ : syracuseStep 588415 = 882623) B882623
theorem B883823 : Blo 587289 883823 := bstep (se 1 (by rfl) ⟨662867, by rfl⟩ : syracuseStep 883823 = 1325735) B1325735
theorem B589051 : Blo 587289 589051 := bstep (se 1 (by rfl) ⟨441788, by rfl⟩ : syracuseStep 589051 = 883577) B883577
theorem B589055 : Blo 587289 589055 := bstep (se 1 (by rfl) ⟨441791, by rfl⟩ : syracuseStep 589055 = 883583) B883583
theorem B589247 : Blo 587289 589247 := bstep (se 1 (by rfl) ⟨441935, by rfl⟩ : syracuseStep 589247 = 883871) B883871
theorem B590311 : Blo 587289 590311 := bstep (se 1 (by rfl) ⟨442733, by rfl⟩ : syracuseStep 590311 = 885467) B885467
theorem B885407 : Blo 587289 885407 := bstep (se 1 (by rfl) ⟨664055, by rfl⟩ : syracuseStep 885407 = 1328111) B1328111
theorem B590751 : Blo 587289 590751 := bstep (se 1 (by rfl) ⟨443063, by rfl⟩ : syracuseStep 590751 = 886127) B886127
theorem B590939 : Blo 587289 590939 := bstep (se 1 (by rfl) ⟨443204, by rfl⟩ : syracuseStep 590939 = 886409) B886409
theorem B885863 : Blo 587289 885863 := bstep (se 1 (by rfl) ⟨664397, by rfl⟩ : syracuseStep 885863 = 1328795) B1328795
theorem B886223 : Blo 587289 886223 := bstep (se 1 (by rfl) ⟨664667, by rfl⟩ : syracuseStep 886223 = 1329335) B1329335
theorem B2230649 : Blo 587289 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B16976587 : Blo 587289 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B7541869 : Blo 587289 7541869 := bstep (se 3 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 7541869 = 2828201) B2828201
theorem B2233595 : Blo 587289 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B1119919 : Blo 587289 1119919 := bstep (se 1 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 1119919 = 1679879) B1679879
theorem B661711 : Blo 587289 661711 := bstep (se 1 (by rfl) ⟨496283, by rfl⟩ : syracuseStep 661711 = 992567) B992567
theorem B2825725 : Blo 587289 2825725 := bstep (se 3 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 2825725 = 1059647) B1059647
theorem B663871 : Blo 587289 663871 := bstep (se 1 (by rfl) ⟨497903, by rfl⟩ : syracuseStep 663871 = 995807) B995807
theorem B991723 : Blo 587289 991723 := bstep (se 1 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 991723 = 1487585) B1487585
theorem B992425 : Blo 587289 992425 := bstep (se 2 (by rfl) ⟨372159, by rfl⟩ : syracuseStep 992425 = 744319) B744319
theorem B665023 : Blo 587289 665023 := bstep (se 1 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 665023 = 997535) B997535
theorem B992911 : Blo 587289 992911 := bstep (se 1 (by rfl) ⟨744683, by rfl⟩ : syracuseStep 992911 = 1489367) B1489367
theorem B993127 : Blo 587289 993127 := bstep (se 1 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 993127 = 1489691) B1489691
theorem B3582731 : Blo 587289 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B6041627 : Blo 587289 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B3780755 : Blo 587289 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B1062767 : Blo 587289 1062767 := bstep (se 1 (by rfl) ⟨797075, by rfl⟩ : syracuseStep 1062767 = 1594151) B1594151
theorem B6734501 : Blo 587289 6734501 := bstep (se 4 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 6734501 = 1262719) B1262719
theorem B5653327 : Blo 587289 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B63095645 : Blo 587289 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B1491817 : Blo 587289 1491817 := bstep (se 2 (by rfl) ⟨559431, by rfl⟩ : syracuseStep 1491817 = 1118863) B1118863
theorem B1983743 : Blo 587289 1983743 := bstep (se 1 (by rfl) ⟨1487807, by rfl⟩ : syracuseStep 1983743 = 2975615) B2975615
theorem B1984175 : Blo 587289 1984175 := bstep (se 1 (by rfl) ⟨1488131, by rfl⟩ : syracuseStep 1984175 = 2976263) B2976263
theorem B9586441 : Blo 587289 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B1329371 : Blo 587289 1329371 := bstep (se 1 (by rfl) ⟨997028, by rfl⟩ : syracuseStep 1329371 = 1994057) B1994057
theorem B2117231 : Blo 587289 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B19124495 : Blo 587289 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B1888543 : Blo 587289 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B2119135 : Blo 587289 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B314136305 : Blo 587289 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B1988495 : Blo 587289 1988495 := bstep (se 1 (by rfl) ⟨1491371, by rfl⟩ : syracuseStep 1988495 = 2982743) B2982743
theorem B1989035 : Blo 587289 1989035 := bstep (se 1 (by rfl) ⟨1491776, by rfl⟩ : syracuseStep 1989035 = 2983553) B2983553
theorem B1989629 : Blo 587289 1989629 := bstep (se 3 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 1989629 = 746111) B746111
theorem B209543321 : Blo 587289 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B2384155 : Blo 587289 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B7528747 : Blo 587289 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B39314969 : Blo 587289 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B8415677 : Blo 587289 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B17001737 : Blo 587289 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B3763759 : Blo 587289 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B8515631 : Blo 587289 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B11301119 : Blo 587289 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B2388307 : Blo 587289 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B881801 : Blo 587289 881801 := bstep (se 2 (by rfl) ⟨330675, by rfl⟩ : syracuseStep 881801 = 661351) B661351
theorem B7566473 : Blo 587289 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B587295 : Blo 587289 587295 := bstep (se 1 (by rfl) ⟨440471, by rfl⟩ : syracuseStep 587295 = 880943) B880943
theorem B882911 : Blo 587289 882911 := bstep (se 1 (by rfl) ⟨662183, by rfl⟩ : syracuseStep 882911 = 1324367) B1324367
theorem B588287 : Blo 587289 588287 := bstep (se 1 (by rfl) ⟨441215, by rfl⟩ : syracuseStep 588287 = 882431) B882431
theorem B5372669 : Blo 587289 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B588647 : Blo 587289 588647 := bstep (se 1 (by rfl) ⟨441485, by rfl⟩ : syracuseStep 588647 = 882971) B882971
theorem B588831 : Blo 587289 588831 := bstep (se 1 (by rfl) ⟨441623, by rfl⟩ : syracuseStep 588831 = 883247) B883247
theorem B2522431 : Blo 587289 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B589215 : Blo 587289 589215 := bstep (se 1 (by rfl) ⟨441911, by rfl⟩ : syracuseStep 589215 = 883823) B883823
theorem B3178873 : Blo 587289 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B885161 : Blo 587289 885161 := bstep (se 2 (by rfl) ⟨331935, by rfl⟩ : syracuseStep 885161 = 663871) B663871
theorem B590271 : Blo 587289 590271 := bstep (se 1 (by rfl) ⟨442703, by rfl⟩ : syracuseStep 590271 = 885407) B885407
theorem B4489667 : Blo 587289 4489667 := bstep (se 1 (by rfl) ⟨3367250, by rfl⟩ : syracuseStep 4489667 = 6734501) B6734501
theorem B590575 : Blo 587289 590575 := bstep (se 1 (by rfl) ⟨442931, by rfl⟩ : syracuseStep 590575 = 885863) B885863
theorem B590815 : Blo 587289 590815 := bstep (se 1 (by rfl) ⟨443111, by rfl⟩ : syracuseStep 590815 = 886223) B886223
theorem B7537769 : Blo 587289 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B886247 : Blo 587289 886247 := bstep (se 1 (by rfl) ⟨664685, by rfl⟩ : syracuseStep 886247 = 1329371) B1329371
theorem B886697 : Blo 587289 886697 := bstep (se 2 (by rfl) ⟨332511, by rfl⟩ : syracuseStep 886697 = 665023) B665023
theorem B12781921 : Blo 587289 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B1411487 : Blo 587289 1411487 := bstep (se 1 (by rfl) ⟨1058615, by rfl⟩ : syracuseStep 1411487 = 2117231) B2117231
theorem B12749663 : Blo 587289 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B209424203 : Blo 587289 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B5018345 : Blo 587289 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B139695547 : Blo 587289 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B3184409 : Blo 587289 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B5610451 : Blo 587289 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B2825513 : Blo 587289 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B5677087 : Blo 587289 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B3581779 : Blo 587289 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B10038329 : Blo 587289 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B1322297 : Blo 587289 1322297 := bstep (se 2 (by rfl) ⟨495861, by rfl⟩ : syracuseStep 1322297 = 991723) B991723
theorem B1322495 : Blo 587289 1322495 := bstep (se 1 (by rfl) ⟨991871, by rfl⟩ : syracuseStep 1322495 = 1983743) B1983743
theorem B1322783 : Blo 587289 1322783 := bstep (se 1 (by rfl) ⟨992087, by rfl⟩ : syracuseStep 1322783 = 1984175) B1984175
theorem B1323233 : Blo 587289 1323233 := bstep (se 2 (by rfl) ⟨496212, by rfl⟩ : syracuseStep 1323233 = 992425) B992425
theorem B1487099 : Blo 587289 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B1323881 : Blo 587289 1323881 := bstep (se 2 (by rfl) ⟨496455, by rfl⟩ : syracuseStep 1323881 = 992911) B992911
theorem B1324169 : Blo 587289 1324169 := bstep (se 2 (by rfl) ⟨496563, by rfl⟩ : syracuseStep 1324169 = 993127) B993127
theorem B1489063 : Blo 587289 1489063 := bstep (se 1 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 1489063 = 2233595) B2233595
theorem B1325663 : Blo 587289 1325663 := bstep (se 1 (by rfl) ⟨994247, by rfl⟩ : syracuseStep 1325663 = 1988495) B1988495
theorem B1326023 : Blo 587289 1326023 := bstep (se 1 (by rfl) ⟨994517, by rfl⟩ : syracuseStep 1326023 = 1989035) B1989035
theorem B1326419 : Blo 587289 1326419 := bstep (se 1 (by rfl) ⟨994814, by rfl⟩ : syracuseStep 1326419 = 1989629) B1989629
theorem B2834045 : Blo 587289 2834045 := bstep (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) B1062767
theorem B1493225 : Blo 587289 1493225 := bstep (se 2 (by rfl) ⟨559959, by rfl⟩ : syracuseStep 1493225 = 1119919) B1119919
theorem B3363241 : Blo 587289 3363241 := bstep (se 2 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 3363241 = 2522431) B2522431
theorem B1989089 : Blo 587289 1989089 := bstep (se 2 (by rfl) ⟨745908, by rfl⟩ : syracuseStep 1989089 = 1491817) B1491817
theorem B168255053 : Blo 587289 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B22635449 : Blo 587289 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B2518057 : Blo 587289 2518057 := bstep (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) B1888543
theorem B26209979 : Blo 587289 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B10055825 : Blo 587289 10055825 := bstep (se 2 (by rfl) ⟨3770934, by rfl⟩ : syracuseStep 10055825 = 7541869) B7541869
theorem B2388487 : Blo 587289 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B11334491 : Blo 587289 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B4027751 : Blo 587289 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B2520503 : Blo 587289 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B7534079 : Blo 587289 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B882281 : Blo 587289 882281 := bstep (se 2 (by rfl) ⟨330855, by rfl⟩ : syracuseStep 882281 = 661711) B661711
theorem B587867 : Blo 587289 587867 := bstep (se 1 (by rfl) ⟨440900, by rfl⟩ : syracuseStep 587867 = 881801) B881801
theorem B5044315 : Blo 587289 5044315 := bstep (se 1 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 5044315 = 7566473) B7566473
theorem B588607 : Blo 587289 588607 := bstep (se 1 (by rfl) ⟨441455, by rfl⟩ : syracuseStep 588607 = 882911) B882911
theorem B3767633 : Blo 587289 3767633 := bstep (se 2 (by rfl) ⟨1412862, by rfl⟩ : syracuseStep 3767633 = 2825725) B2825725
theorem B7569449 : Blo 587289 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B590107 : Blo 587289 590107 := bstep (se 1 (by rfl) ⟨442580, by rfl⟩ : syracuseStep 590107 = 885161) B885161
theorem B590831 : Blo 587289 590831 := bstep (se 1 (by rfl) ⟨443123, by rfl⟩ : syracuseStep 590831 = 886247) B886247
theorem B591131 : Blo 587289 591131 := bstep (se 1 (by rfl) ⟨443348, by rfl⟩ : syracuseStep 591131 = 886697) B886697
theorem B17042561 : Blo 587289 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B3345563 : Blo 587289 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B112170035 : Blo 587289 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B3184649 : Blo 587289 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B186260729 : Blo 587289 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B6692219 : Blo 587289 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B17473319 : Blo 587289 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B6725753 : Blo 587289 6725753 := bstep (se 2 (by rfl) ⟨2522157, by rfl⟩ : syracuseStep 6725753 = 5044315) B5044315
theorem B991399 : Blo 587289 991399 := bstep (se 1 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 991399 = 1487099) B1487099
theorem B1680335 : Blo 587289 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B5022719 : Blo 587289 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B7480601 : Blo 587289 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B2993111 : Blo 587289 2993111 := bstep (se 1 (by rfl) ⟨2244833, by rfl⟩ : syracuseStep 2993111 = 4489667) B4489667
theorem B4238497 : Blo 587289 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B5025179 : Blo 587289 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B995483 : Blo 587289 995483 := bstep (se 1 (by rfl) ⟨746612, by rfl⟩ : syracuseStep 995483 = 1493225) B1493225
theorem B8499775 : Blo 587289 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B3357409 : Blo 587289 3357409 := bstep (se 2 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 3357409 = 2518057) B2518057
theorem B1326059 : Blo 587289 1326059 := bstep (se 1 (by rfl) ⟨994544, by rfl⟩ : syracuseStep 1326059 = 1989089) B1989089
theorem B1883675 : Blo 587289 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B15090299 : Blo 587289 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B6703883 : Blo 587289 6703883 := bstep (se 1 (by rfl) ⟨5027912, by rfl⟩ : syracuseStep 6703883 = 10055825) B10055825
theorem B1985417 : Blo 587289 1985417 := bstep (se 2 (by rfl) ⟨744531, by rfl⟩ : syracuseStep 1985417 = 1489063) B1489063
theorem B7556327 : Blo 587289 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B2511755 : Blo 587289 2511755 := bstep (se 1 (by rfl) ⟨1883816, by rfl⟩ : syracuseStep 2511755 = 3767633) B3767633
theorem B1889363 : Blo 587289 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B940991 : Blo 587289 940991 := bstep (se 1 (by rfl) ⟨705743, by rfl⟩ : syracuseStep 940991 = 1411487) B1411487
theorem B4775705 : Blo 587289 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B139616135 : Blo 587289 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B2122939 : Blo 587289 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B4484321 : Blo 587289 4484321 := bstep (se 2 (by rfl) ⟨1681620, by rfl⟩ : syracuseStep 4484321 = 3363241) B3363241
theorem B881531 : Blo 587289 881531 := bstep (se 1 (by rfl) ⟨661148, by rfl⟩ : syracuseStep 881531 = 1322297) B1322297
theorem B881663 : Blo 587289 881663 := bstep (se 1 (by rfl) ⟨661247, by rfl⟩ : syracuseStep 881663 = 1322495) B1322495
theorem B881855 : Blo 587289 881855 := bstep (se 1 (by rfl) ⟨661391, by rfl⟩ : syracuseStep 881855 = 1322783) B1322783
theorem B882155 : Blo 587289 882155 := bstep (se 1 (by rfl) ⟨661616, by rfl⟩ : syracuseStep 882155 = 1323233) B1323233
theorem B882587 : Blo 587289 882587 := bstep (se 1 (by rfl) ⟨661940, by rfl⟩ : syracuseStep 882587 = 1323881) B1323881
theorem B882779 : Blo 587289 882779 := bstep (se 1 (by rfl) ⟨662084, by rfl⟩ : syracuseStep 882779 = 1324169) B1324169
theorem B2685167 : Blo 587289 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B588187 : Blo 587289 588187 := bstep (se 1 (by rfl) ⟨441140, by rfl⟩ : syracuseStep 588187 = 882281) B882281
theorem B883775 : Blo 587289 883775 := bstep (se 1 (by rfl) ⟨662831, by rfl⟩ : syracuseStep 883775 = 1325663) B1325663
theorem B884015 : Blo 587289 884015 := bstep (se 1 (by rfl) ⟨663011, by rfl⟩ : syracuseStep 884015 = 1326023) B1326023
theorem B884279 : Blo 587289 884279 := bstep (se 1 (by rfl) ⟨663209, by rfl⟩ : syracuseStep 884279 = 1326419) B1326419
theorem B5046299 : Blo 587289 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B10060199 : Blo 587289 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B2230375 : Blo 587289 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B1674503 : Blo 587289 1674503 := bstep (se 1 (by rfl) ⟨1255877, by rfl⟩ : syracuseStep 1674503 = 2511755) B2511755
theorem B74780023 : Blo 587289 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B4461479 : Blo 587289 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B3183803 : Blo 587289 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B1120223 : Blo 587289 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B3348479 : Blo 587289 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B4987067 : Blo 587289 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B2989547 : Blo 587289 2989547 := bstep (se 1 (by rfl) ⟨2242160, by rfl⟩ : syracuseStep 2989547 = 4484321) B4484321
theorem B3350119 : Blo 587289 3350119 := bstep (se 1 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 3350119 = 5025179) B5025179
theorem B663655 : Blo 587289 663655 := bstep (se 1 (by rfl) ⟨497741, by rfl⟩ : syracuseStep 663655 = 995483) B995483
theorem B1255783 : Blo 587289 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B1321865 : Blo 587289 1321865 := bstep (se 2 (by rfl) ⟨495699, by rfl⟩ : syracuseStep 1321865 = 991399) B991399
theorem B4469255 : Blo 587289 4469255 := bstep (se 1 (by rfl) ⟨3351941, by rfl⟩ : syracuseStep 4469255 = 6703883) B6703883
theorem B1323611 : Blo 587289 1323611 := bstep (se 1 (by rfl) ⟨992708, by rfl⟩ : syracuseStep 1323611 = 1985417) B1985417
theorem B5651329 : Blo 587289 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B11648879 : Blo 587289 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B93077423 : Blo 587289 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B11322341 : Blo 587289 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B2509309 : Blo 587289 2509309 := bstep (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) B940991
theorem B4476545 : Blo 587289 4476545 := bstep (se 2 (by rfl) ⟨1678704, by rfl⟩ : syracuseStep 4476545 = 3357409) B3357409
theorem B1790111 : Blo 587289 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B11361707 : Blo 587289 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B5037551 : Blo 587289 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B5038301 : Blo 587289 5038301 := bstep (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) B1889363
theorem B2123099 : Blo 587289 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B4483835 : Blo 587289 4483835 := bstep (se 1 (by rfl) ⟨3362876, by rfl⟩ : syracuseStep 4483835 = 6725753) B6725753
theorem B11333033 : Blo 587289 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B1995407 : Blo 587289 1995407 := bstep (se 1 (by rfl) ⟨1496555, by rfl⟩ : syracuseStep 1995407 = 2993111) B2993111
theorem B587687 : Blo 587289 587687 := bstep (se 1 (by rfl) ⟨440765, by rfl⟩ : syracuseStep 587687 = 881531) B881531
theorem B496695277 : Blo 587289 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B587775 : Blo 587289 587775 := bstep (se 1 (by rfl) ⟨440831, by rfl⟩ : syracuseStep 587775 = 881663) B881663
theorem B587903 : Blo 587289 587903 := bstep (se 1 (by rfl) ⟨440927, by rfl⟩ : syracuseStep 587903 = 881855) B881855
theorem B588103 : Blo 587289 588103 := bstep (se 1 (by rfl) ⟨441077, by rfl⟩ : syracuseStep 588103 = 882155) B882155
theorem B588391 : Blo 587289 588391 := bstep (se 1 (by rfl) ⟨441293, by rfl⟩ : syracuseStep 588391 = 882587) B882587
theorem B588519 : Blo 587289 588519 := bstep (se 1 (by rfl) ⟨441389, by rfl⟩ : syracuseStep 588519 = 882779) B882779
theorem B884039 : Blo 587289 884039 := bstep (se 1 (by rfl) ⟨663029, by rfl⟩ : syracuseStep 884039 = 1326059) B1326059
theorem B589183 : Blo 587289 589183 := bstep (se 1 (by rfl) ⟨441887, by rfl⟩ : syracuseStep 589183 = 883775) B883775
theorem B589343 : Blo 587289 589343 := bstep (se 1 (by rfl) ⟨442007, by rfl⟩ : syracuseStep 589343 = 884015) B884015
theorem B589519 : Blo 587289 589519 := bstep (se 1 (by rfl) ⟨442139, by rfl⟩ : syracuseStep 589519 = 884279) B884279
theorem B884873 : Blo 587289 884873 := bstep (se 2 (by rfl) ⟨331827, by rfl⟩ : syracuseStep 884873 = 663655) B663655
theorem B1116335 : Blo 587289 1116335 := bstep (se 1 (by rfl) ⟨837251, by rfl⟩ : syracuseStep 1116335 = 1674503) B1674503
theorem B2984363 : Blo 587289 2984363 := bstep (se 1 (by rfl) ⟨2238272, by rfl⟩ : syracuseStep 2984363 = 4476545) B4476545
theorem B1674377 : Blo 587289 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B3345745 : Blo 587289 3345745 := bstep (se 2 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 3345745 = 2509309) B2509309
theorem B2232319 : Blo 587289 2232319 := bstep (se 1 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 2232319 = 3348479) B3348479
theorem B7574471 : Blo 587289 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B1415399 : Blo 587289 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B2989223 : Blo 587289 2989223 := bstep (se 1 (by rfl) ⟨2241917, by rfl⟩ : syracuseStep 2989223 = 4483835) B4483835
theorem B4466825 : Blo 587289 4466825 := bstep (se 2 (by rfl) ⟨1675059, by rfl⟩ : syracuseStep 4466825 = 3350119) B3350119
theorem B7548227 : Blo 587289 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B53195381 : Blo 587289 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B3358367 : Blo 587289 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B3358867 : Blo 587289 3358867 := bstep (se 1 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 3358867 = 5038301) B5038301
theorem B7555355 : Blo 587289 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B662260369 : Blo 587289 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B1330271 : Blo 587289 1330271 := bstep (se 1 (by rfl) ⟨997703, by rfl⟩ : syracuseStep 1330271 = 1995407) B1995407
theorem B62051615 : Blo 587289 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B3364199 : Blo 587289 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B6706799 : Blo 587289 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B4773629 : Blo 587289 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B2973833 : Blo 587289 2973833 := bstep (se 2 (by rfl) ⟨1115187, by rfl⟩ : syracuseStep 2973833 = 2230375) B2230375
theorem B2974319 : Blo 587289 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B2122535 : Blo 587289 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B746815 : Blo 587289 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B99706697 : Blo 587289 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B1993031 : Blo 587289 1993031 := bstep (se 1 (by rfl) ⟨1494773, by rfl⟩ : syracuseStep 1993031 = 2989547) B2989547
theorem B881243 : Blo 587289 881243 := bstep (se 1 (by rfl) ⟨660932, by rfl⟩ : syracuseStep 881243 = 1321865) B1321865
theorem B2979503 : Blo 587289 2979503 := bstep (se 1 (by rfl) ⟨2234627, by rfl⟩ : syracuseStep 2979503 = 4469255) B4469255
theorem B882407 : Blo 587289 882407 := bstep (se 1 (by rfl) ⟨661805, by rfl⟩ : syracuseStep 882407 = 1323611) B1323611
theorem B7535105 : Blo 587289 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B589359 : Blo 587289 589359 := bstep (se 1 (by rfl) ⟨442019, by rfl⟩ : syracuseStep 589359 = 884039) B884039
theorem B7765919 : Blo 587289 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B589915 : Blo 587289 589915 := bstep (se 1 (by rfl) ⟨442436, by rfl⟩ : syracuseStep 589915 = 884873) B884873
theorem B886847 : Blo 587289 886847 := bstep (se 1 (by rfl) ⟨665135, by rfl⟩ : syracuseStep 886847 = 1330271) B1330271
theorem B1116251 : Blo 587289 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B5049647 : Blo 587289 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B3182419 : Blo 587289 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B4460993 : Blo 587289 4460993 := bstep (se 2 (by rfl) ⟨1672872, by rfl⟩ : syracuseStep 4460993 = 3345745) B3345745
theorem B3774397 : Blo 587289 3774397 := bstep (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) B1415399
theorem B35463587 : Blo 587289 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B5023403 : Blo 587289 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B2238911 : Blo 587289 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B995753 : Blo 587289 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B41367743 : Blo 587289 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B883013825 : Blo 587289 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B2242799 : Blo 587289 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B4471199 : Blo 587289 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B1982555 : Blo 587289 1982555 := bstep (se 1 (by rfl) ⟨1486916, by rfl⟩ : syracuseStep 1982555 = 2973833) B2973833
theorem B1982879 : Blo 587289 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B66471131 : Blo 587289 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B1328687 : Blo 587289 1328687 := bstep (se 1 (by rfl) ⟨996515, by rfl⟩ : syracuseStep 1328687 = 1993031) B1993031
theorem B5032151 : Blo 587289 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B1986335 : Blo 587289 1986335 := bstep (se 1 (by rfl) ⟨1489751, by rfl⟩ : syracuseStep 1986335 = 2979503) B2979503
theorem B4478489 : Blo 587289 4478489 := bstep (se 2 (by rfl) ⟨1679433, by rfl⟩ : syracuseStep 4478489 = 3358867) B3358867
theorem B744223 : Blo 587289 744223 := bstep (se 1 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 744223 = 1116335) B1116335
theorem B5036903 : Blo 587289 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B1989575 : Blo 587289 1989575 := bstep (se 1 (by rfl) ⟨1492181, by rfl⟩ : syracuseStep 1989575 = 2984363) B2984363
theorem B5660093 : Blo 587289 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B1992815 : Blo 587289 1992815 := bstep (se 1 (by rfl) ⟨1494611, by rfl⟩ : syracuseStep 1992815 = 2989223) B2989223
theorem B2976425 : Blo 587289 2976425 := bstep (se 2 (by rfl) ⟨1116159, by rfl⟩ : syracuseStep 2976425 = 2232319) B2232319
theorem B2977883 : Blo 587289 2977883 := bstep (se 1 (by rfl) ⟨2233412, by rfl⟩ : syracuseStep 2977883 = 4466825) B4466825
theorem B587495 : Blo 587289 587495 := bstep (se 1 (by rfl) ⟨440621, by rfl⟩ : syracuseStep 587495 = 881243) B881243
theorem B588271 : Blo 587289 588271 := bstep (se 1 (by rfl) ⟨441203, by rfl⟩ : syracuseStep 588271 = 882407) B882407
theorem B5177279 : Blo 587289 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B885791 : Blo 587289 885791 := bstep (se 1 (by rfl) ⟨664343, by rfl⟩ : syracuseStep 885791 = 1328687) B1328687
theorem B591231 : Blo 587289 591231 := bstep (se 1 (by rfl) ⟨443423, by rfl⟩ : syracuseStep 591231 = 886847) B886847
theorem B2985659 : Blo 587289 2985659 := bstep (se 1 (by rfl) ⟨2239244, by rfl⟩ : syracuseStep 2985659 = 4478489) B4478489
theorem B378278261 : Blo 587289 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B3773395 : Blo 587289 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B3348935 : Blo 587289 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B663835 : Blo 587289 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B992297 : Blo 587289 992297 := bstep (se 2 (by rfl) ⟨372111, by rfl⟩ : syracuseStep 992297 = 744223) B744223
theorem B13806077 : Blo 587289 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B1321703 : Blo 587289 1321703 := bstep (se 1 (by rfl) ⟨991277, by rfl⟩ : syracuseStep 1321703 = 1982555) B1982555
theorem B1321919 : Blo 587289 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B44314087 : Blo 587289 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B3354767 : Blo 587289 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B1324223 : Blo 587289 1324223 := bstep (se 1 (by rfl) ⟨993167, by rfl⟩ : syracuseStep 1324223 = 1986335) B1986335
theorem B3357935 : Blo 587289 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B1326383 : Blo 587289 1326383 := bstep (se 1 (by rfl) ⟨994787, by rfl⟩ : syracuseStep 1326383 = 1989575) B1989575
theorem B4243225 : Blo 587289 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B1328543 : Blo 587289 1328543 := bstep (se 1 (by rfl) ⟨996407, by rfl⟩ : syracuseStep 1328543 = 1992815) B1992815
theorem B1492607 : Blo 587289 1492607 := bstep (se 1 (by rfl) ⟨1119455, by rfl⟩ : syracuseStep 1492607 = 2238911) B2238911
theorem B1984283 : Blo 587289 1984283 := bstep (se 1 (by rfl) ⟨1488212, by rfl⟩ : syracuseStep 1984283 = 2976425) B2976425
theorem B5032529 : Blo 587289 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B1985255 : Blo 587289 1985255 := bstep (se 1 (by rfl) ⟨1488941, by rfl⟩ : syracuseStep 1985255 = 2977883) B2977883
theorem B27578495 : Blo 587289 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B1495199 : Blo 587289 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B744167 : Blo 587289 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B3366431 : Blo 587289 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B2973995 : Blo 587289 2973995 := bstep (se 1 (by rfl) ⟨2230496, by rfl⟩ : syracuseStep 2973995 = 4460993) B4460993
theorem B588675883 : Blo 587289 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B2980799 : Blo 587289 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B885113 : Blo 587289 885113 := bstep (se 2 (by rfl) ⟨331917, by rfl⟩ : syracuseStep 885113 = 663835) B663835
theorem B590527 : Blo 587289 590527 := bstep (se 1 (by rfl) ⟨442895, by rfl⟩ : syracuseStep 590527 = 885791) B885791
theorem B885695 : Blo 587289 885695 := bstep (se 1 (by rfl) ⟨664271, by rfl⟩ : syracuseStep 885695 = 1328543) B1328543
theorem B18385663 : Blo 587289 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B252185507 : Blo 587289 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B2232623 : Blo 587289 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B59085449 : Blo 587289 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B661531 : Blo 587289 661531 := bstep (se 1 (by rfl) ⟨496148, by rfl⟩ : syracuseStep 661531 = 992297) B992297
theorem B2236511 : Blo 587289 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B784901177 : Blo 587289 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B2238623 : Blo 587289 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B995071 : Blo 587289 995071 := bstep (se 1 (by rfl) ⟨746303, by rfl⟩ : syracuseStep 995071 = 1492607) B1492607
theorem B1322855 : Blo 587289 1322855 := bstep (se 1 (by rfl) ⟨992141, by rfl⟩ : syracuseStep 1322855 = 1984283) B1984283
theorem B3355019 : Blo 587289 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B1323503 : Blo 587289 1323503 := bstep (se 1 (by rfl) ⟨992627, by rfl⟩ : syracuseStep 1323503 = 1985255) B1985255
theorem B996799 : Blo 587289 996799 := bstep (se 1 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 996799 = 1495199) B1495199
theorem B2244287 : Blo 587289 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B1982663 : Blo 587289 1982663 := bstep (se 1 (by rfl) ⟨1486997, by rfl⟩ : syracuseStep 1982663 = 2973995) B2973995
theorem B5031193 : Blo 587289 5031193 := bstep (se 2 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 5031193 = 3773395) B3773395
theorem B36816205 : Blo 587289 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B1984445 : Blo 587289 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B1987199 : Blo 587289 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B5657633 : Blo 587289 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B1990439 : Blo 587289 1990439 := bstep (se 1 (by rfl) ⟨1492829, by rfl⟩ : syracuseStep 1990439 = 2985659) B2985659
theorem B881135 : Blo 587289 881135 := bstep (se 1 (by rfl) ⟨660851, by rfl⟩ : syracuseStep 881135 = 1321703) B1321703
theorem B881279 : Blo 587289 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B882815 : Blo 587289 882815 := bstep (se 1 (by rfl) ⟨662111, by rfl⟩ : syracuseStep 882815 = 1324223) B1324223
theorem B884255 : Blo 587289 884255 := bstep (se 1 (by rfl) ⟨663191, by rfl⟩ : syracuseStep 884255 = 1326383) B1326383
theorem B590075 : Blo 587289 590075 := bstep (se 1 (by rfl) ⟨442556, by rfl⟩ : syracuseStep 590075 = 885113) B885113
theorem B590463 : Blo 587289 590463 := bstep (se 1 (by rfl) ⟨442847, by rfl⟩ : syracuseStep 590463 = 885695) B885695
theorem B49088273 : Blo 587289 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B39390299 : Blo 587289 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B3771755 : Blo 587289 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B24514217 : Blo 587289 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B2236679 : Blo 587289 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B1321775 : Blo 587289 1321775 := bstep (se 1 (by rfl) ⟨991331, by rfl⟩ : syracuseStep 1321775 = 1982663) B1982663
theorem B1322963 : Blo 587289 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B1488415 : Blo 587289 1488415 := bstep (se 1 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 1488415 = 2232623) B2232623
theorem B1324799 : Blo 587289 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B1326761 : Blo 587289 1326761 := bstep (se 2 (by rfl) ⟨497535, by rfl⟩ : syracuseStep 1326761 = 995071) B995071
theorem B1326959 : Blo 587289 1326959 := bstep (se 1 (by rfl) ⟨995219, by rfl⟩ : syracuseStep 1326959 = 1990439) B1990439
theorem B1491007 : Blo 587289 1491007 := bstep (se 1 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 1491007 = 2236511) B2236511
theorem B1492415 : Blo 587289 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B1329065 : Blo 587289 1329065 := bstep (se 2 (by rfl) ⟨498399, by rfl⟩ : syracuseStep 1329065 = 996799) B996799
theorem B1496191 : Blo 587289 1496191 := bstep (se 1 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 1496191 = 2244287) B2244287
theorem B6708257 : Blo 587289 6708257 := bstep (se 2 (by rfl) ⟨2515596, by rfl⟩ : syracuseStep 6708257 = 5031193) B5031193
theorem B168123671 : Blo 587289 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B523267451 : Blo 587289 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B881903 : Blo 587289 881903 := bstep (se 1 (by rfl) ⟨661427, by rfl⟩ : syracuseStep 881903 = 1322855) B1322855
theorem B882041 : Blo 587289 882041 := bstep (se 2 (by rfl) ⟨330765, by rfl⟩ : syracuseStep 882041 = 661531) B661531
theorem B587423 : Blo 587289 587423 := bstep (se 1 (by rfl) ⟨440567, by rfl⟩ : syracuseStep 587423 = 881135) B881135
theorem B882335 : Blo 587289 882335 := bstep (se 1 (by rfl) ⟨661751, by rfl⟩ : syracuseStep 882335 = 1323503) B1323503
theorem B587519 : Blo 587289 587519 := bstep (se 1 (by rfl) ⟨440639, by rfl⟩ : syracuseStep 587519 = 881279) B881279
theorem B588543 : Blo 587289 588543 := bstep (se 1 (by rfl) ⟨441407, by rfl⟩ : syracuseStep 588543 = 882815) B882815
theorem B589503 : Blo 587289 589503 := bstep (se 1 (by rfl) ⟨442127, by rfl⟩ : syracuseStep 589503 = 884255) B884255
theorem B886043 : Blo 587289 886043 := bstep (se 1 (by rfl) ⟨664532, by rfl⟩ : syracuseStep 886043 = 1329065) B1329065
theorem B523608245 : Blo 587289 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B994943 : Blo 587289 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B26260199 : Blo 587289 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B4472171 : Blo 587289 4472171 := bstep (se 1 (by rfl) ⟨3354128, by rfl⟩ : syracuseStep 4472171 = 6708257) B6708257
theorem B112082447 : Blo 587289 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B1491119 : Blo 587289 1491119 := bstep (se 1 (by rfl) ⟨1118339, by rfl⟩ : syracuseStep 1491119 = 2236679) B2236679
theorem B1984553 : Blo 587289 1984553 := bstep (se 2 (by rfl) ⟨744207, by rfl⟩ : syracuseStep 1984553 = 1488415) B1488415
theorem B1988009 : Blo 587289 1988009 := bstep (se 2 (by rfl) ⟨745503, by rfl⟩ : syracuseStep 1988009 = 1491007) B1491007
theorem B2514503 : Blo 587289 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B16342811 : Blo 587289 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B1994921 : Blo 587289 1994921 := bstep (se 2 (by rfl) ⟨748095, by rfl⟩ : syracuseStep 1994921 = 1496191) B1496191
theorem B881183 : Blo 587289 881183 := bstep (se 1 (by rfl) ⟨660887, by rfl⟩ : syracuseStep 881183 = 1321775) B1321775
theorem B348844967 : Blo 587289 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B881975 : Blo 587289 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B587935 : Blo 587289 587935 := bstep (se 1 (by rfl) ⟨440951, by rfl⟩ : syracuseStep 587935 = 881903) B881903
theorem B588027 : Blo 587289 588027 := bstep (se 1 (by rfl) ⟨441020, by rfl⟩ : syracuseStep 588027 = 882041) B882041
theorem B588223 : Blo 587289 588223 := bstep (se 1 (by rfl) ⟨441167, by rfl⟩ : syracuseStep 588223 = 882335) B882335
theorem B883199 : Blo 587289 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B884507 : Blo 587289 884507 := bstep (se 1 (by rfl) ⟨663380, by rfl⟩ : syracuseStep 884507 = 1326761) B1326761
theorem B884639 : Blo 587289 884639 := bstep (se 1 (by rfl) ⟨663479, by rfl⟩ : syracuseStep 884639 = 1326959) B1326959
theorem B590695 : Blo 587289 590695 := bstep (se 1 (by rfl) ⟨443021, by rfl⟩ : syracuseStep 590695 = 886043) B886043
theorem B663295 : Blo 587289 663295 := bstep (se 1 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 663295 = 994943) B994943
theorem B17506799 : Blo 587289 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B232563311 : Blo 587289 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B74721631 : Blo 587289 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B994079 : Blo 587289 994079 := bstep (se 1 (by rfl) ⟨745559, by rfl⟩ : syracuseStep 994079 = 1491119) B1491119
theorem B1323035 : Blo 587289 1323035 := bstep (se 1 (by rfl) ⟨992276, by rfl⟩ : syracuseStep 1323035 = 1984553) B1984553
theorem B1325339 : Blo 587289 1325339 := bstep (se 1 (by rfl) ⟨994004, by rfl⟩ : syracuseStep 1325339 = 1988009) B1988009
theorem B10895207 : Blo 587289 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B1329947 : Blo 587289 1329947 := bstep (se 1 (by rfl) ⟨997460, by rfl⟩ : syracuseStep 1329947 = 1994921) B1994921
theorem B6705341 : Blo 587289 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B349072163 : Blo 587289 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B587455 : Blo 587289 587455 := bstep (se 1 (by rfl) ⟨440591, by rfl⟩ : syracuseStep 587455 = 881183) B881183
theorem B587983 : Blo 587289 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B588799 : Blo 587289 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B2981447 : Blo 587289 2981447 := bstep (se 1 (by rfl) ⟨2236085, by rfl⟩ : syracuseStep 2981447 = 4472171) B4472171
theorem B589671 : Blo 587289 589671 := bstep (se 1 (by rfl) ⟨442253, by rfl⟩ : syracuseStep 589671 = 884507) B884507
theorem B589759 : Blo 587289 589759 := bstep (se 1 (by rfl) ⟨442319, by rfl⟩ : syracuseStep 589759 = 884639) B884639
theorem B886631 : Blo 587289 886631 := bstep (se 1 (by rfl) ⟨664973, by rfl⟩ : syracuseStep 886631 = 1329947) B1329947
theorem B11671199 : Blo 587289 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B662719 : Blo 587289 662719 := bstep (se 1 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 662719 = 994079) B994079
theorem B4470227 : Blo 587289 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B99628841 : Blo 587289 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B155042207 : Blo 587289 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B29053885 : Blo 587289 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B1987631 : Blo 587289 1987631 := bstep (se 1 (by rfl) ⟨1490723, by rfl⟩ : syracuseStep 1987631 = 2981447) B2981447
theorem B232714775 : Blo 587289 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B882023 : Blo 587289 882023 := bstep (se 1 (by rfl) ⟨661517, by rfl⟩ : syracuseStep 882023 = 1323035) B1323035
theorem B883559 : Blo 587289 883559 := bstep (se 1 (by rfl) ⟨662669, by rfl⟩ : syracuseStep 883559 = 1325339) B1325339
theorem B884393 : Blo 587289 884393 := bstep (se 2 (by rfl) ⟨331647, by rfl⟩ : syracuseStep 884393 = 663295) B663295
theorem B591087 : Blo 587289 591087 := bstep (se 1 (by rfl) ⟨443315, by rfl⟩ : syracuseStep 591087 = 886631) B886631
theorem B38738513 : Blo 587289 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B103361471 : Blo 587289 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B1325087 : Blo 587289 1325087 := bstep (se 1 (by rfl) ⟨993815, by rfl⟩ : syracuseStep 1325087 = 1987631) B1987631
theorem B7780799 : Blo 587289 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B155143183 : Blo 587289 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B588015 : Blo 587289 588015 := bstep (se 1 (by rfl) ⟨441011, by rfl⟩ : syracuseStep 588015 = 882023) B882023
theorem B2980151 : Blo 587289 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B66419227 : Blo 587289 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B883625 : Blo 587289 883625 := bstep (se 2 (by rfl) ⟨331359, by rfl⟩ : syracuseStep 883625 = 662719) B662719
theorem B589039 : Blo 587289 589039 := bstep (se 1 (by rfl) ⟨441779, by rfl⟩ : syracuseStep 589039 = 883559) B883559
theorem B589595 : Blo 587289 589595 := bstep (se 1 (by rfl) ⟨442196, by rfl⟩ : syracuseStep 589595 = 884393) B884393
theorem B25825675 : Blo 587289 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B5187199 : Blo 587289 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B88558969 : Blo 587289 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B1986767 : Blo 587289 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B206857577 : Blo 587289 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B68907647 : Blo 587289 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B883391 : Blo 587289 883391 := bstep (se 1 (by rfl) ⟨662543, by rfl⟩ : syracuseStep 883391 = 1325087) B1325087
theorem B589083 : Blo 587289 589083 := bstep (se 1 (by rfl) ⟨441812, by rfl⟩ : syracuseStep 589083 = 883625) B883625
theorem B6916265 : Blo 587289 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B1324511 : Blo 587289 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B118078625 : Blo 587289 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B137905051 : Blo 587289 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B34434233 : Blo 587289 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B45938431 : Blo 587289 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B588927 : Blo 587289 588927 := bstep (se 1 (by rfl) ⟨441695, by rfl⟩ : syracuseStep 588927 = 883391) B883391
theorem B61251241 : Blo 587289 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B78719083 : Blo 587289 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B183873401 : Blo 587289 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B22956155 : Blo 587289 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B4610843 : Blo 587289 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B883007 : Blo 587289 883007 := bstep (se 1 (by rfl) ⟨662255, by rfl⟩ : syracuseStep 883007 = 1324511) B1324511
theorem B15304103 : Blo 587289 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B81668321 : Blo 587289 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B419835109 : Blo 587289 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B3073895 : Blo 587289 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B122582267 : Blo 587289 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B588671 : Blo 587289 588671 := bstep (se 1 (by rfl) ⟨441503, by rfl⟩ : syracuseStep 588671 = 883007) B883007
theorem B559780145 : Blo 587289 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B10202735 : Blo 587289 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B2049263 : Blo 587289 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B54445547 : Blo 587289 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B81721511 : Blo 587289 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B6801823 : Blo 587289 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B54481007 : Blo 587289 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B1366175 : Blo 587289 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B36297031 : Blo 587289 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B373186763 : Blo 587289 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B36320671 : Blo 587289 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B248791175 : Blo 587289 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B9069097 : Blo 587289 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B910783 : Blo 587289 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B48396041 : Blo 587289 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B12092129 : Blo 587289 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B4857509 : Blo 587289 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B32264027 : Blo 587289 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B165860783 : Blo 587289 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B48427561 : Blo 587289 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B8061419 : Blo 587289 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B258280325 : Blo 587289 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B21509351 : Blo 587289 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B110573855 : Blo 587289 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B3238339 : Blo 587289 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B5374279 : Blo 587289 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B14339567 : Blo 587289 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B73715903 : Blo 587289 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B172186883 : Blo 587289 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B4317785 : Blo 587289 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B114791255 : Blo 587289 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B7165705 : Blo 587289 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B9559711 : Blo 587289 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B49143935 : Blo 587289 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B2878523 : Blo 587289 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B131050493 : Blo 587289 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B76527503 : Blo 587289 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B1919015 : Blo 587289 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B9554273 : Blo 587289 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B12746281 : Blo 587289 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B1279343 : Blo 587289 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B87366995 : Blo 587289 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B6369515 : Blo 587289 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B16995041 : Blo 587289 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B51018335 : Blo 587289 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B852895 : Blo 587289 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B58244663 : Blo 587289 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B4246343 : Blo 587289 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B11330027 : Blo 587289 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B34012223 : Blo 587289 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B2830895 : Blo 587289 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B7553351 : Blo 587289 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B4548773 : Blo 587289 4548773 := bstep (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) B852895
theorem B22674815 : Blo 587289 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B38829775 : Blo 587289 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B15116543 : Blo 587289 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B3032515 : Blo 587289 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B1887263 : Blo 587289 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B5035567 : Blo 587289 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B51773033 : Blo 587289 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B34515355 : Blo 587289 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B4043353 : Blo 587289 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B1258175 : Blo 587289 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B10077695 : Blo 587289 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B6714089 : Blo 587289 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B6718463 : Blo 587289 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B46020473 : Blo 587289 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B5391137 : Blo 587289 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B838783 : Blo 587289 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B4476059 : Blo 587289 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B2984039 : Blo 587289 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B1118377 : Blo 587289 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B30680315 : Blo 587289 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B3594091 : Blo 587289 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B4478975 : Blo 587289 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B2985983 : Blo 587289 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B20453543 : Blo 587289 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B4792121 : Blo 587289 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B1491169 : Blo 587289 1491169 := bstep (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) B1118377
theorem B1989359 : Blo 587289 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B13635695 : Blo 587289 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B1326239 : Blo 587289 1326239 := bstep (se 1 (by rfl) ⟨994679, by rfl⟩ : syracuseStep 1326239 = 1989359) B1989359
theorem B3194747 : Blo 587289 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B1988225 : Blo 587289 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B1990655 : Blo 587289 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B9090463 : Blo 587289 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B1325483 : Blo 587289 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B1327103 : Blo 587289 1327103 := bstep (se 1 (by rfl) ⟨995327, by rfl⟩ : syracuseStep 1327103 = 1990655) B1990655
theorem B884159 : Blo 587289 884159 := bstep (se 1 (by rfl) ⟨663119, by rfl⟩ : syracuseStep 884159 = 1326239) B1326239
theorem B2129831 : Blo 587289 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1419887 : Blo 587289 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B12120617 : Blo 587289 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B883655 : Blo 587289 883655 := bstep (se 1 (by rfl) ⟨662741, by rfl⟩ : syracuseStep 883655 = 1325483) B1325483
theorem B589439 : Blo 587289 589439 := bstep (se 1 (by rfl) ⟨442079, by rfl⟩ : syracuseStep 589439 = 884159) B884159
theorem B884735 : Blo 587289 884735 := bstep (se 1 (by rfl) ⟨663551, by rfl⟩ : syracuseStep 884735 = 1327103) B1327103
theorem B3786365 : Blo 587289 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B589823 : Blo 587289 589823 := bstep (se 1 (by rfl) ⟨442367, by rfl⟩ : syracuseStep 589823 = 884735) B884735
theorem B8080411 : Blo 587289 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B589103 : Blo 587289 589103 := bstep (se 1 (by rfl) ⟨441827, by rfl⟩ : syracuseStep 589103 = 883655) B883655
theorem B2524243 : Blo 587289 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B10773881 : Blo 587289 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B7182587 : Blo 587289 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B3365657 : Blo 587289 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B4788391 : Blo 587289 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B2243771 : Blo 587289 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1495847 : Blo 587289 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B6384521 : Blo 587289 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B997231 : Blo 587289 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B4256347 : Blo 587289 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5675129 : Blo 587289 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B1329641 : Blo 587289 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B886427 : Blo 587289 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B3783419 : Blo 587289 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B590951 : Blo 587289 590951 := bstep (se 1 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 590951 = 886427) B886427
theorem B2522279 : Blo 587289 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B1681519 : Blo 587289 1681519 := bstep (se 1 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 1681519 = 2522279) B2522279
theorem B2242025 : Blo 587289 2242025 := bstep (se 2 (by rfl) ⟨840759, by rfl⟩ : syracuseStep 2242025 = 1681519) B1681519
theorem B1494683 : Blo 587289 1494683 := bstep (se 1 (by rfl) ⟨1121012, by rfl⟩ : syracuseStep 1494683 = 2242025) B2242025
theorem B996455 : Blo 587289 996455 := bstep (se 1 (by rfl) ⟨747341, by rfl⟩ : syracuseStep 996455 = 1494683) B1494683
theorem B664303 : Blo 587289 664303 := bstep (se 1 (by rfl) ⟨498227, by rfl⟩ : syracuseStep 664303 = 996455) B996455
theorem B885737 : Blo 587289 885737 := bstep (se 2 (by rfl) ⟨332151, by rfl⟩ : syracuseStep 885737 = 664303) B664303
theorem B590491 : Blo 587289 590491 := bstep (se 1 (by rfl) ⟨442868, by rfl⟩ : syracuseStep 590491 = 885737) B885737

theorem C0 (j : ℕ) (h1 : 146822 ≤ j) (h2 : j ≤ 147521) : Blo 587289 (4 * j + 3) := by
  interval_cases j
  · exact B587291
  · exact B587295
  · exact B587299
  · exact B587303
  · exact B587307
  · exact B587311
  · exact B587315
  · exact B587319
  · exact B587323
  · exact B587327
  · exact B587331
  · exact B587335
  · exact B587339
  · exact B587343
  · exact B587347
  · exact B587351
  · exact B587355
  · exact B587359
  · exact B587363
  · exact B587367
  · exact B587371
  · exact B587375
  · exact B587379
  · exact B587383
  · exact B587387
  · exact B587391
  · exact B587395
  · exact B587399
  · exact B587403
  · exact B587407
  · exact B587411
  · exact B587415
  · exact B587419
  · exact B587423
  · exact B587427
  · exact B587431
  · exact B587435
  · exact B587439
  · exact B587443
  · exact B587447
  · exact B587451
  · exact B587455
  · exact B587459
  · exact B587463
  · exact B587467
  · exact B587471
  · exact B587475
  · exact B587479
  · exact B587483
  · exact B587487
  · exact B587491
  · exact B587495
  · exact B587499
  · exact B587503
  · exact B587507
  · exact B587511
  · exact B587515
  · exact B587519
  · exact B587523
  · exact B587527
  · exact B587531
  · exact B587535
  · exact B587539
  · exact B587543
  · exact B587547
  · exact B587551
  · exact B587555
  · exact B587559
  · exact B587563
  · exact B587567
  · exact B587571
  · exact B587575
  · exact B587579
  · exact B587583
  · exact B587587
  · exact B587591
  · exact B587595
  · exact B587599
  · exact B587603
  · exact B587607
  · exact B587611
  · exact B587615
  · exact B587619
  · exact B587623
  · exact B587627
  · exact B587631
  · exact B587635
  · exact B587639
  · exact B587643
  · exact B587647
  · exact B587651
  · exact B587655
  · exact B587659
  · exact B587663
  · exact B587667
  · exact B587671
  · exact B587675
  · exact B587679
  · exact B587683
  · exact B587687
  · exact B587691
  · exact B587695
  · exact B587699
  · exact B587703
  · exact B587707
  · exact B587711
  · exact B587715
  · exact B587719
  · exact B587723
  · exact B587727
  · exact B587731
  · exact B587735
  · exact B587739
  · exact B587743
  · exact B587747
  · exact B587751
  · exact B587755
  · exact B587759
  · exact B587763
  · exact B587767
  · exact B587771
  · exact B587775
  · exact B587779
  · exact B587783
  · exact B587787
  · exact B587791
  · exact B587795
  · exact B587799
  · exact B587803
  · exact B587807
  · exact B587811
  · exact B587815
  · exact B587819
  · exact B587823
  · exact B587827
  · exact B587831
  · exact B587835
  · exact B587839
  · exact B587843
  · exact B587847
  · exact B587851
  · exact B587855
  · exact B587859
  · exact B587863
  · exact B587867
  · exact B587871
  · exact B587875
  · exact B587879
  · exact B587883
  · exact B587887
  · exact B587891
  · exact B587895
  · exact B587899
  · exact B587903
  · exact B587907
  · exact B587911
  · exact B587915
  · exact B587919
  · exact B587923
  · exact B587927
  · exact B587931
  · exact B587935
  · exact B587939
  · exact B587943
  · exact B587947
  · exact B587951
  · exact B587955
  · exact B587959
  · exact B587963
  · exact B587967
  · exact B587971
  · exact B587975
  · exact B587979
  · exact B587983
  · exact B587987
  · exact B587991
  · exact B587995
  · exact B587999
  · exact B588003
  · exact B588007
  · exact B588011
  · exact B588015
  · exact B588019
  · exact B588023
  · exact B588027
  · exact B588031
  · exact B588035
  · exact B588039
  · exact B588043
  · exact B588047
  · exact B588051
  · exact B588055
  · exact B588059
  · exact B588063
  · exact B588067
  · exact B588071
  · exact B588075
  · exact B588079
  · exact B588083
  · exact B588087
  · exact B588091
  · exact B588095
  · exact B588099
  · exact B588103
  · exact B588107
  · exact B588111
  · exact B588115
  · exact B588119
  · exact B588123
  · exact B588127
  · exact B588131
  · exact B588135
  · exact B588139
  · exact B588143
  · exact B588147
  · exact B588151
  · exact B588155
  · exact B588159
  · exact B588163
  · exact B588167
  · exact B588171
  · exact B588175
  · exact B588179
  · exact B588183
  · exact B588187
  · exact B588191
  · exact B588195
  · exact B588199
  · exact B588203
  · exact B588207
  · exact B588211
  · exact B588215
  · exact B588219
  · exact B588223
  · exact B588227
  · exact B588231
  · exact B588235
  · exact B588239
  · exact B588243
  · exact B588247
  · exact B588251
  · exact B588255
  · exact B588259
  · exact B588263
  · exact B588267
  · exact B588271
  · exact B588275
  · exact B588279
  · exact B588283
  · exact B588287
  · exact B588291
  · exact B588295
  · exact B588299
  · exact B588303
  · exact B588307
  · exact B588311
  · exact B588315
  · exact B588319
  · exact B588323
  · exact B588327
  · exact B588331
  · exact B588335
  · exact B588339
  · exact B588343
  · exact B588347
  · exact B588351
  · exact B588355
  · exact B588359
  · exact B588363
  · exact B588367
  · exact B588371
  · exact B588375
  · exact B588379
  · exact B588383
  · exact B588387
  · exact B588391
  · exact B588395
  · exact B588399
  · exact B588403
  · exact B588407
  · exact B588411
  · exact B588415
  · exact B588419
  · exact B588423
  · exact B588427
  · exact B588431
  · exact B588435
  · exact B588439
  · exact B588443
  · exact B588447
  · exact B588451
  · exact B588455
  · exact B588459
  · exact B588463
  · exact B588467
  · exact B588471
  · exact B588475
  · exact B588479
  · exact B588483
  · exact B588487
  · exact B588491
  · exact B588495
  · exact B588499
  · exact B588503
  · exact B588507
  · exact B588511
  · exact B588515
  · exact B588519
  · exact B588523
  · exact B588527
  · exact B588531
  · exact B588535
  · exact B588539
  · exact B588543
  · exact B588547
  · exact B588551
  · exact B588555
  · exact B588559
  · exact B588563
  · exact B588567
  · exact B588571
  · exact B588575
  · exact B588579
  · exact B588583
  · exact B588587
  · exact B588591
  · exact B588595
  · exact B588599
  · exact B588603
  · exact B588607
  · exact B588611
  · exact B588615
  · exact B588619
  · exact B588623
  · exact B588627
  · exact B588631
  · exact B588635
  · exact B588639
  · exact B588643
  · exact B588647
  · exact B588651
  · exact B588655
  · exact B588659
  · exact B588663
  · exact B588667
  · exact B588671
  · exact B588675
  · exact B588679
  · exact B588683
  · exact B588687
  · exact B588691
  · exact B588695
  · exact B588699
  · exact B588703
  · exact B588707
  · exact B588711
  · exact B588715
  · exact B588719
  · exact B588723
  · exact B588727
  · exact B588731
  · exact B588735
  · exact B588739
  · exact B588743
  · exact B588747
  · exact B588751
  · exact B588755
  · exact B588759
  · exact B588763
  · exact B588767
  · exact B588771
  · exact B588775
  · exact B588779
  · exact B588783
  · exact B588787
  · exact B588791
  · exact B588795
  · exact B588799
  · exact B588803
  · exact B588807
  · exact B588811
  · exact B588815
  · exact B588819
  · exact B588823
  · exact B588827
  · exact B588831
  · exact B588835
  · exact B588839
  · exact B588843
  · exact B588847
  · exact B588851
  · exact B588855
  · exact B588859
  · exact B588863
  · exact B588867
  · exact B588871
  · exact B588875
  · exact B588879
  · exact B588883
  · exact B588887
  · exact B588891
  · exact B588895
  · exact B588899
  · exact B588903
  · exact B588907
  · exact B588911
  · exact B588915
  · exact B588919
  · exact B588923
  · exact B588927
  · exact B588931
  · exact B588935
  · exact B588939
  · exact B588943
  · exact B588947
  · exact B588951
  · exact B588955
  · exact B588959
  · exact B588963
  · exact B588967
  · exact B588971
  · exact B588975
  · exact B588979
  · exact B588983
  · exact B588987
  · exact B588991
  · exact B588995
  · exact B588999
  · exact B589003
  · exact B589007
  · exact B589011
  · exact B589015
  · exact B589019
  · exact B589023
  · exact B589027
  · exact B589031
  · exact B589035
  · exact B589039
  · exact B589043
  · exact B589047
  · exact B589051
  · exact B589055
  · exact B589059
  · exact B589063
  · exact B589067
  · exact B589071
  · exact B589075
  · exact B589079
  · exact B589083
  · exact B589087
  · exact B589091
  · exact B589095
  · exact B589099
  · exact B589103
  · exact B589107
  · exact B589111
  · exact B589115
  · exact B589119
  · exact B589123
  · exact B589127
  · exact B589131
  · exact B589135
  · exact B589139
  · exact B589143
  · exact B589147
  · exact B589151
  · exact B589155
  · exact B589159
  · exact B589163
  · exact B589167
  · exact B589171
  · exact B589175
  · exact B589179
  · exact B589183
  · exact B589187
  · exact B589191
  · exact B589195
  · exact B589199
  · exact B589203
  · exact B589207
  · exact B589211
  · exact B589215
  · exact B589219
  · exact B589223
  · exact B589227
  · exact B589231
  · exact B589235
  · exact B589239
  · exact B589243
  · exact B589247
  · exact B589251
  · exact B589255
  · exact B589259
  · exact B589263
  · exact B589267
  · exact B589271
  · exact B589275
  · exact B589279
  · exact B589283
  · exact B589287
  · exact B589291
  · exact B589295
  · exact B589299
  · exact B589303
  · exact B589307
  · exact B589311
  · exact B589315
  · exact B589319
  · exact B589323
  · exact B589327
  · exact B589331
  · exact B589335
  · exact B589339
  · exact B589343
  · exact B589347
  · exact B589351
  · exact B589355
  · exact B589359
  · exact B589363
  · exact B589367
  · exact B589371
  · exact B589375
  · exact B589379
  · exact B589383
  · exact B589387
  · exact B589391
  · exact B589395
  · exact B589399
  · exact B589403
  · exact B589407
  · exact B589411
  · exact B589415
  · exact B589419
  · exact B589423
  · exact B589427
  · exact B589431
  · exact B589435
  · exact B589439
  · exact B589443
  · exact B589447
  · exact B589451
  · exact B589455
  · exact B589459
  · exact B589463
  · exact B589467
  · exact B589471
  · exact B589475
  · exact B589479
  · exact B589483
  · exact B589487
  · exact B589491
  · exact B589495
  · exact B589499
  · exact B589503
  · exact B589507
  · exact B589511
  · exact B589515
  · exact B589519
  · exact B589523
  · exact B589527
  · exact B589531
  · exact B589535
  · exact B589539
  · exact B589543
  · exact B589547
  · exact B589551
  · exact B589555
  · exact B589559
  · exact B589563
  · exact B589567
  · exact B589571
  · exact B589575
  · exact B589579
  · exact B589583
  · exact B589587
  · exact B589591
  · exact B589595
  · exact B589599
  · exact B589603
  · exact B589607
  · exact B589611
  · exact B589615
  · exact B589619
  · exact B589623
  · exact B589627
  · exact B589631
  · exact B589635
  · exact B589639
  · exact B589643
  · exact B589647
  · exact B589651
  · exact B589655
  · exact B589659
  · exact B589663
  · exact B589667
  · exact B589671
  · exact B589675
  · exact B589679
  · exact B589683
  · exact B589687
  · exact B589691
  · exact B589695
  · exact B589699
  · exact B589703
  · exact B589707
  · exact B589711
  · exact B589715
  · exact B589719
  · exact B589723
  · exact B589727
  · exact B589731
  · exact B589735
  · exact B589739
  · exact B589743
  · exact B589747
  · exact B589751
  · exact B589755
  · exact B589759
  · exact B589763
  · exact B589767
  · exact B589771
  · exact B589775
  · exact B589779
  · exact B589783
  · exact B589787
  · exact B589791
  · exact B589795
  · exact B589799
  · exact B589803
  · exact B589807
  · exact B589811
  · exact B589815
  · exact B589819
  · exact B589823
  · exact B589827
  · exact B589831
  · exact B589835
  · exact B589839
  · exact B589843
  · exact B589847
  · exact B589851
  · exact B589855
  · exact B589859
  · exact B589863
  · exact B589867
  · exact B589871
  · exact B589875
  · exact B589879
  · exact B589883
  · exact B589887
  · exact B589891
  · exact B589895
  · exact B589899
  · exact B589903
  · exact B589907
  · exact B589911
  · exact B589915
  · exact B589919
  · exact B589923
  · exact B589927
  · exact B589931
  · exact B589935
  · exact B589939
  · exact B589943
  · exact B589947
  · exact B589951
  · exact B589955
  · exact B589959
  · exact B589963
  · exact B589967
  · exact B589971
  · exact B589975
  · exact B589979
  · exact B589983
  · exact B589987
  · exact B589991
  · exact B589995
  · exact B589999
  · exact B590003
  · exact B590007
  · exact B590011
  · exact B590015
  · exact B590019
  · exact B590023
  · exact B590027
  · exact B590031
  · exact B590035
  · exact B590039
  · exact B590043
  · exact B590047
  · exact B590051
  · exact B590055
  · exact B590059
  · exact B590063
  · exact B590067
  · exact B590071
  · exact B590075
  · exact B590079
  · exact B590083
  · exact B590087

theorem C1 (j : ℕ) (h1 : 147522 ≤ j) (h2 : j ≤ 147821) : Blo 587289 (4 * j + 3) := by
  interval_cases j
  · exact B590091
  · exact B590095
  · exact B590099
  · exact B590103
  · exact B590107
  · exact B590111
  · exact B590115
  · exact B590119
  · exact B590123
  · exact B590127
  · exact B590131
  · exact B590135
  · exact B590139
  · exact B590143
  · exact B590147
  · exact B590151
  · exact B590155
  · exact B590159
  · exact B590163
  · exact B590167
  · exact B590171
  · exact B590175
  · exact B590179
  · exact B590183
  · exact B590187
  · exact B590191
  · exact B590195
  · exact B590199
  · exact B590203
  · exact B590207
  · exact B590211
  · exact B590215
  · exact B590219
  · exact B590223
  · exact B590227
  · exact B590231
  · exact B590235
  · exact B590239
  · exact B590243
  · exact B590247
  · exact B590251
  · exact B590255
  · exact B590259
  · exact B590263
  · exact B590267
  · exact B590271
  · exact B590275
  · exact B590279
  · exact B590283
  · exact B590287
  · exact B590291
  · exact B590295
  · exact B590299
  · exact B590303
  · exact B590307
  · exact B590311
  · exact B590315
  · exact B590319
  · exact B590323
  · exact B590327
  · exact B590331
  · exact B590335
  · exact B590339
  · exact B590343
  · exact B590347
  · exact B590351
  · exact B590355
  · exact B590359
  · exact B590363
  · exact B590367
  · exact B590371
  · exact B590375
  · exact B590379
  · exact B590383
  · exact B590387
  · exact B590391
  · exact B590395
  · exact B590399
  · exact B590403
  · exact B590407
  · exact B590411
  · exact B590415
  · exact B590419
  · exact B590423
  · exact B590427
  · exact B590431
  · exact B590435
  · exact B590439
  · exact B590443
  · exact B590447
  · exact B590451
  · exact B590455
  · exact B590459
  · exact B590463
  · exact B590467
  · exact B590471
  · exact B590475
  · exact B590479
  · exact B590483
  · exact B590487
  · exact B590491
  · exact B590495
  · exact B590499
  · exact B590503
  · exact B590507
  · exact B590511
  · exact B590515
  · exact B590519
  · exact B590523
  · exact B590527
  · exact B590531
  · exact B590535
  · exact B590539
  · exact B590543
  · exact B590547
  · exact B590551
  · exact B590555
  · exact B590559
  · exact B590563
  · exact B590567
  · exact B590571
  · exact B590575
  · exact B590579
  · exact B590583
  · exact B590587
  · exact B590591
  · exact B590595
  · exact B590599
  · exact B590603
  · exact B590607
  · exact B590611
  · exact B590615
  · exact B590619
  · exact B590623
  · exact B590627
  · exact B590631
  · exact B590635
  · exact B590639
  · exact B590643
  · exact B590647
  · exact B590651
  · exact B590655
  · exact B590659
  · exact B590663
  · exact B590667
  · exact B590671
  · exact B590675
  · exact B590679
  · exact B590683
  · exact B590687
  · exact B590691
  · exact B590695
  · exact B590699
  · exact B590703
  · exact B590707
  · exact B590711
  · exact B590715
  · exact B590719
  · exact B590723
  · exact B590727
  · exact B590731
  · exact B590735
  · exact B590739
  · exact B590743
  · exact B590747
  · exact B590751
  · exact B590755
  · exact B590759
  · exact B590763
  · exact B590767
  · exact B590771
  · exact B590775
  · exact B590779
  · exact B590783
  · exact B590787
  · exact B590791
  · exact B590795
  · exact B590799
  · exact B590803
  · exact B590807
  · exact B590811
  · exact B590815
  · exact B590819
  · exact B590823
  · exact B590827
  · exact B590831
  · exact B590835
  · exact B590839
  · exact B590843
  · exact B590847
  · exact B590851
  · exact B590855
  · exact B590859
  · exact B590863
  · exact B590867
  · exact B590871
  · exact B590875
  · exact B590879
  · exact B590883
  · exact B590887
  · exact B590891
  · exact B590895
  · exact B590899
  · exact B590903
  · exact B590907
  · exact B590911
  · exact B590915
  · exact B590919
  · exact B590923
  · exact B590927
  · exact B590931
  · exact B590935
  · exact B590939
  · exact B590943
  · exact B590947
  · exact B590951
  · exact B590955
  · exact B590959
  · exact B590963
  · exact B590967
  · exact B590971
  · exact B590975
  · exact B590979
  · exact B590983
  · exact B590987
  · exact B590991
  · exact B590995
  · exact B590999
  · exact B591003
  · exact B591007
  · exact B591011
  · exact B591015
  · exact B591019
  · exact B591023
  · exact B591027
  · exact B591031
  · exact B591035
  · exact B591039
  · exact B591043
  · exact B591047
  · exact B591051
  · exact B591055
  · exact B591059
  · exact B591063
  · exact B591067
  · exact B591071
  · exact B591075
  · exact B591079
  · exact B591083
  · exact B591087
  · exact B591091
  · exact B591095
  · exact B591099
  · exact B591103
  · exact B591107
  · exact B591111
  · exact B591115
  · exact B591119
  · exact B591123
  · exact B591127
  · exact B591131
  · exact B591135
  · exact B591139
  · exact B591143
  · exact B591147
  · exact B591151
  · exact B591155
  · exact B591159
  · exact B591163
  · exact B591167
  · exact B591171
  · exact B591175
  · exact B591179
  · exact B591183
  · exact B591187
  · exact B591191
  · exact B591195
  · exact B591199
  · exact B591203
  · exact B591207
  · exact B591211
  · exact B591215
  · exact B591219
  · exact B591223
  · exact B591227
  · exact B591231
  · exact B591235
  · exact B591239
  · exact B591243
  · exact B591247
  · exact B591251
  · exact B591255
  · exact B591259
  · exact B591263
  · exact B591267
  · exact B591271
  · exact B591275
  · exact B591279
  · exact B591283
  · exact B591287

theorem solution (m : ℕ) (hlo : 587289 ≤ m) (hhi : m ≤ 591289) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 146822 ≤ j := by omega
    have hj2 : j ≤ 147821 := by omega
    have hb : Blo 587289 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 147522 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
