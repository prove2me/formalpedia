-- Prove2me | solution 1 for syracuse_descends_range_1228432_1230432
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:01.71751+00:00
-- url     : https://prove2.me/submissions/7970208e-50a9-421c-a678-70d7bce007ec

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


theorem B1843205 : Blo 1228432 1843205 := bbase (se 4 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 1843205 = 345601) (by norm_num)
theorem B9469973 : Blo 1228432 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B1843229 : Blo 1228432 1843229 := bbase (se 3 (by rfl) ⟨345605, by rfl⟩ : syracuseStep 1843229 = 691211) (by norm_num)
theorem B1843253 : Blo 1228432 1843253 := bbase (se 5 (by rfl) ⟨86402, by rfl⟩ : syracuseStep 1843253 = 172805) (by norm_num)
theorem B1245241 : Blo 1228432 1245241 := bbase (se 2 (by rfl) ⟨466965, by rfl⟩ : syracuseStep 1245241 = 933931) (by norm_num)
theorem B1843277 : Blo 1228432 1843277 := bbase (se 3 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 1843277 = 691229) (by norm_num)
theorem B1843301 : Blo 1228432 1843301 := bbase (se 4 (by rfl) ⟨172809, by rfl⟩ : syracuseStep 1843301 = 345619) (by norm_num)
theorem B1556597 : Blo 1228432 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B1843325 : Blo 1228432 1843325 := bbase (se 3 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 1843325 = 691247) (by norm_num)
theorem B3113093 : Blo 1228432 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B1843349 : Blo 1228432 1843349 := bbase (se 6 (by rfl) ⟨43203, by rfl⟩ : syracuseStep 1843349 = 86407) (by norm_num)
theorem B1401001 : Blo 1228432 1401001 := bbase (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) (by norm_num)
theorem B1843373 : Blo 1228432 1843373 := bbase (se 3 (by rfl) ⟨345632, by rfl⟩ : syracuseStep 1843373 = 691265) (by norm_num)
theorem B1556653 : Blo 1228432 1556653 := bbase (se 3 (by rfl) ⟨291872, by rfl⟩ : syracuseStep 1556653 = 583745) (by norm_num)
theorem B1843397 : Blo 1228432 1843397 := bbase (se 4 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 1843397 = 345637) (by norm_num)
theorem B1843421 : Blo 1228432 1843421 := bbase (se 3 (by rfl) ⟨345641, by rfl⟩ : syracuseStep 1843421 = 691283) (by norm_num)
theorem B1843445 : Blo 1228432 1843445 := bbase (se 5 (by rfl) ⟨86411, by rfl⟩ : syracuseStep 1843445 = 172823) (by norm_num)
theorem B1843469 : Blo 1228432 1843469 := bbase (se 3 (by rfl) ⟨345650, by rfl⟩ : syracuseStep 1843469 = 691301) (by norm_num)
theorem B1556749 : Blo 1228432 1556749 := bbase (se 3 (by rfl) ⟨291890, by rfl⟩ : syracuseStep 1556749 = 583781) (by norm_num)
theorem B9969941 : Blo 1228432 9969941 := bbase (se 6 (by rfl) ⟨233670, by rfl⟩ : syracuseStep 9969941 = 467341) (by norm_num)
theorem B1843493 : Blo 1228432 1843493 := bbase (se 4 (by rfl) ⟨172827, by rfl⟩ : syracuseStep 1843493 = 345655) (by norm_num)
theorem B1843517 : Blo 1228432 1843517 := bbase (se 3 (by rfl) ⟨345659, by rfl⟩ : syracuseStep 1843517 = 691319) (by norm_num)
theorem B1843541 : Blo 1228432 1843541 := bbase (se 10 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 1843541 = 5401) (by norm_num)
theorem B1843565 : Blo 1228432 1843565 := bbase (se 3 (by rfl) ⟨345668, by rfl⟩ : syracuseStep 1843565 = 691337) (by norm_num)
theorem B1843589 : Blo 1228432 1843589 := bbase (se 4 (by rfl) ⟨172836, by rfl⟩ : syracuseStep 1843589 = 345673) (by norm_num)
theorem B2245013 : Blo 1228432 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B1843613 : Blo 1228432 1843613 := bbase (se 3 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 1843613 = 691355) (by norm_num)
theorem B2130349 : Blo 1228432 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B1843637 : Blo 1228432 1843637 := bbase (se 5 (by rfl) ⟨86420, by rfl⟩ : syracuseStep 1843637 = 172841) (by norm_num)
theorem B1556921 : Blo 1228432 1556921 := bbase (se 2 (by rfl) ⟨583845, by rfl⟩ : syracuseStep 1556921 = 1167691) (by norm_num)
theorem B2245069 : Blo 1228432 2245069 := bbase (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) (by norm_num)
theorem B1843661 : Blo 1228432 1843661 := bbase (se 3 (by rfl) ⟨345686, by rfl⟩ : syracuseStep 1843661 = 691373) (by norm_num)
theorem B2073053 : Blo 1228432 2073053 := bbase (se 3 (by rfl) ⟨388697, by rfl⟩ : syracuseStep 2073053 = 777395) (by norm_num)
theorem B3113437 : Blo 1228432 3113437 := bbase (se 3 (by rfl) ⟨583769, by rfl⟩ : syracuseStep 3113437 = 1167539) (by norm_num)
theorem B1843685 : Blo 1228432 1843685 := bbase (se 4 (by rfl) ⟨172845, by rfl⟩ : syracuseStep 1843685 = 345691) (by norm_num)
theorem B1556977 : Blo 1228432 1556977 := bbase (se 2 (by rfl) ⟨583866, by rfl⟩ : syracuseStep 1556977 = 1167733) (by norm_num)
theorem B1843709 : Blo 1228432 1843709 := bbase (se 3 (by rfl) ⟨345695, by rfl⟩ : syracuseStep 1843709 = 691391) (by norm_num)
theorem B1843733 : Blo 1228432 1843733 := bbase (se 6 (by rfl) ⟨43212, by rfl⟩ : syracuseStep 1843733 = 86425) (by norm_num)
theorem B6226469 : Blo 1228432 6226469 := bbase (se 4 (by rfl) ⟨583731, by rfl⟩ : syracuseStep 6226469 = 1167463) (by norm_num)
theorem B1843757 : Blo 1228432 1843757 := bbase (se 3 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 1843757 = 691409) (by norm_num)
theorem B9970229 : Blo 1228432 9970229 := bbase (se 5 (by rfl) ⟨467354, by rfl⟩ : syracuseStep 9970229 = 934709) (by norm_num)
theorem B1843781 : Blo 1228432 1843781 := bbase (se 4 (by rfl) ⟨172854, by rfl⟩ : syracuseStep 1843781 = 345709) (by norm_num)
theorem B3113549 : Blo 1228432 3113549 := bbase (se 3 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 3113549 = 1167581) (by norm_num)
theorem B1557073 : Blo 1228432 1557073 := bbase (se 2 (by rfl) ⟨583902, by rfl⟩ : syracuseStep 1557073 = 1167805) (by norm_num)
theorem B2073181 : Blo 1228432 2073181 := bbase (se 3 (by rfl) ⟨388721, by rfl⟩ : syracuseStep 2073181 = 777443) (by norm_num)
theorem B1843805 : Blo 1228432 1843805 := bbase (se 3 (by rfl) ⟨345713, by rfl⟩ : syracuseStep 1843805 = 691427) (by norm_num)
theorem B1843829 : Blo 1228432 1843829 := bbase (se 5 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 1843829 = 172859) (by norm_num)
theorem B1843853 : Blo 1228432 1843853 := bbase (se 3 (by rfl) ⟨345722, by rfl⟩ : syracuseStep 1843853 = 691445) (by norm_num)
theorem B1843877 : Blo 1228432 1843877 := bbase (se 4 (by rfl) ⟨172863, by rfl⟩ : syracuseStep 1843877 = 345727) (by norm_num)
theorem B1401517 : Blo 1228432 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B2335405 : Blo 1228432 2335405 := bbase (se 3 (by rfl) ⟨437888, by rfl⟩ : syracuseStep 2335405 = 875777) (by norm_num)
theorem B2073269 : Blo 1228432 2073269 := bbase (se 5 (by rfl) ⟨97184, by rfl⟩ : syracuseStep 2073269 = 194369) (by norm_num)
theorem B3498677 : Blo 1228432 3498677 := bbase (se 5 (by rfl) ⟨164000, by rfl⟩ : syracuseStep 3498677 = 328001) (by norm_num)
theorem B1843901 : Blo 1228432 1843901 := bbase (se 3 (by rfl) ⟨345731, by rfl⟩ : syracuseStep 1843901 = 691463) (by norm_num)
theorem B1843925 : Blo 1228432 1843925 := bbase (se 7 (by rfl) ⟨21608, by rfl⟩ : syracuseStep 1843925 = 43217) (by norm_num)
theorem B1843949 : Blo 1228432 1843949 := bbase (se 3 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 1843949 = 691481) (by norm_num)
theorem B1557245 : Blo 1228432 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B1843973 : Blo 1228432 1843973 := bbase (se 4 (by rfl) ⟨172872, by rfl⟩ : syracuseStep 1843973 = 345745) (by norm_num)
theorem B3113741 : Blo 1228432 3113741 := bbase (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) (by norm_num)
theorem B1843997 : Blo 1228432 1843997 := bbase (se 3 (by rfl) ⟨345749, by rfl⟩ : syracuseStep 1843997 = 691499) (by norm_num)
theorem B5251877 : Blo 1228432 5251877 := bbase (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) (by norm_num)
theorem B2073397 : Blo 1228432 2073397 := bbase (se 5 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 2073397 = 194381) (by norm_num)
theorem B1844021 : Blo 1228432 1844021 := bbase (se 5 (by rfl) ⟨86438, by rfl⟩ : syracuseStep 1844021 = 172877) (by norm_num)
theorem B2335549 : Blo 1228432 2335549 := bbase (se 3 (by rfl) ⟨437915, by rfl⟩ : syracuseStep 2335549 = 875831) (by norm_num)
theorem B1844045 : Blo 1228432 1844045 := bbase (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) (by norm_num)
theorem B2491229 : Blo 1228432 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B1844069 : Blo 1228432 1844069 := bbase (se 4 (by rfl) ⟨172881, by rfl⟩ : syracuseStep 1844069 = 345763) (by norm_num)
theorem B1844093 : Blo 1228432 1844093 := bbase (se 3 (by rfl) ⟨345767, by rfl⟩ : syracuseStep 1844093 = 691535) (by norm_num)
theorem B2073485 : Blo 1228432 2073485 := bbase (se 3 (by rfl) ⟨388778, by rfl⟩ : syracuseStep 2073485 = 777557) (by norm_num)
theorem B1844117 : Blo 1228432 1844117 := bbase (se 6 (by rfl) ⟨43221, by rfl⟩ : syracuseStep 1844117 = 86443) (by norm_num)
theorem B1844141 : Blo 1228432 1844141 := bbase (se 3 (by rfl) ⟨345776, by rfl⟩ : syracuseStep 1844141 = 691553) (by norm_num)
theorem B2245573 : Blo 1228432 2245573 := bbase (se 4 (by rfl) ⟨210522, by rfl⟩ : syracuseStep 2245573 = 421045) (by norm_num)
theorem B1844165 : Blo 1228432 1844165 := bbase (se 4 (by rfl) ⟨172890, by rfl⟩ : syracuseStep 1844165 = 345781) (by norm_num)
theorem B1262557 : Blo 1228432 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1844189 : Blo 1228432 1844189 := bbase (se 3 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 1844189 = 691571) (by norm_num)
theorem B2335709 : Blo 1228432 2335709 := bbase (se 3 (by rfl) ⟨437945, by rfl⟩ : syracuseStep 2335709 = 875891) (by norm_num)
theorem B1844213 : Blo 1228432 1844213 := bbase (se 5 (by rfl) ⟨86447, by rfl⟩ : syracuseStep 1844213 = 172895) (by norm_num)
theorem B2073613 : Blo 1228432 2073613 := bbase (se 3 (by rfl) ⟨388802, by rfl⟩ : syracuseStep 2073613 = 777605) (by norm_num)
theorem B1844237 : Blo 1228432 1844237 := bbase (se 3 (by rfl) ⟨345794, by rfl⟩ : syracuseStep 1844237 = 691589) (by norm_num)
theorem B14001173 : Blo 1228432 14001173 := bbase (se 6 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 14001173 = 656305) (by norm_num)
theorem B1844261 : Blo 1228432 1844261 := bbase (se 4 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 1844261 = 345799) (by norm_num)
theorem B1844285 : Blo 1228432 1844285 := bbase (se 3 (by rfl) ⟨345803, by rfl⟩ : syracuseStep 1844285 = 691607) (by norm_num)
theorem B1844309 : Blo 1228432 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B1311833 : Blo 1228432 1311833 := bbase (se 2 (by rfl) ⟨491937, by rfl⟩ : syracuseStep 1311833 = 983875) (by norm_num)
theorem B3499109 : Blo 1228432 3499109 := bbase (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) (by norm_num)
theorem B2073701 : Blo 1228432 2073701 := bbase (se 4 (by rfl) ⟨194409, by rfl⟩ : syracuseStep 2073701 = 388819) (by norm_num)
theorem B3114085 : Blo 1228432 3114085 := bbase (se 4 (by rfl) ⟨291945, by rfl⟩ : syracuseStep 3114085 = 583891) (by norm_num)
theorem B1844333 : Blo 1228432 1844333 := bbase (se 3 (by rfl) ⟨345812, by rfl⟩ : syracuseStep 1844333 = 691625) (by norm_num)
theorem B4670581 : Blo 1228432 4670581 := bbase (se 5 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 4670581 = 437867) (by norm_num)
theorem B2335853 : Blo 1228432 2335853 := bbase (se 3 (by rfl) ⟨437972, by rfl⟩ : syracuseStep 2335853 = 875945) (by norm_num)
theorem B1844357 : Blo 1228432 1844357 := bbase (se 4 (by rfl) ⟨172908, by rfl⟩ : syracuseStep 1844357 = 345817) (by norm_num)
theorem B1844381 : Blo 1228432 1844381 := bbase (se 3 (by rfl) ⟨345821, by rfl⟩ : syracuseStep 1844381 = 691643) (by norm_num)
theorem B1844405 : Blo 1228432 1844405 := bbase (se 5 (by rfl) ⟨86456, by rfl⟩ : syracuseStep 1844405 = 172913) (by norm_num)
theorem B1844429 : Blo 1228432 1844429 := bbase (se 3 (by rfl) ⟨345830, by rfl⟩ : syracuseStep 1844429 = 691661) (by norm_num)
theorem B4146389 : Blo 1228432 4146389 := bbase (se 7 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 4146389 = 97181) (by norm_num)
theorem B3114197 : Blo 1228432 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B1311961 : Blo 1228432 1311961 := bbase (se 2 (by rfl) ⟨491985, by rfl⟩ : syracuseStep 1311961 = 983971) (by norm_num)
theorem B2073829 : Blo 1228432 2073829 := bbase (se 4 (by rfl) ⟨194421, by rfl⟩ : syracuseStep 2073829 = 388843) (by norm_num)
theorem B1844453 : Blo 1228432 1844453 := bbase (se 4 (by rfl) ⟨172917, by rfl⟩ : syracuseStep 1844453 = 345835) (by norm_num)
theorem B1844477 : Blo 1228432 1844477 := bbase (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) (by norm_num)
theorem B1844501 : Blo 1228432 1844501 := bbase (se 6 (by rfl) ⟨43230, by rfl⟩ : syracuseStep 1844501 = 86461) (by norm_num)
theorem B3196189 : Blo 1228432 3196189 := bbase (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) (by norm_num)
theorem B1844525 : Blo 1228432 1844525 := bbase (se 3 (by rfl) ⟨345848, by rfl⟩ : syracuseStep 1844525 = 691697) (by norm_num)
theorem B1402169 : Blo 1228432 1402169 := bbase (se 2 (by rfl) ⟨525813, by rfl⟩ : syracuseStep 1402169 = 1051627) (by norm_num)
theorem B2073917 : Blo 1228432 2073917 := bbase (se 3 (by rfl) ⟨388859, by rfl⟩ : syracuseStep 2073917 = 777719) (by norm_num)
theorem B1844549 : Blo 1228432 1844549 := bbase (se 4 (by rfl) ⟨172926, by rfl⟩ : syracuseStep 1844549 = 345853) (by norm_num)
theorem B7882069 : Blo 1228432 7882069 := bbase (se 12 (by rfl) ⟨2886, by rfl⟩ : syracuseStep 7882069 = 5773) (by norm_num)
theorem B1844573 : Blo 1228432 1844573 := bbase (se 3 (by rfl) ⟨345857, by rfl⟩ : syracuseStep 1844573 = 691715) (by norm_num)
theorem B1844597 : Blo 1228432 1844597 := bbase (se 5 (by rfl) ⟨86465, by rfl⟩ : syracuseStep 1844597 = 172931) (by norm_num)
theorem B1844621 : Blo 1228432 1844621 := bbase (se 3 (by rfl) ⟨345866, by rfl⟩ : syracuseStep 1844621 = 691733) (by norm_num)
theorem B3114389 : Blo 1228432 3114389 := bbase (se 6 (by rfl) ⟨72993, by rfl⟩ : syracuseStep 3114389 = 145987) (by norm_num)
theorem B1844645 : Blo 1228432 1844645 := bbase (se 4 (by rfl) ⟨172935, by rfl⟩ : syracuseStep 1844645 = 345871) (by norm_num)
theorem B4670885 : Blo 1228432 4670885 := bbase (se 4 (by rfl) ⟨437895, by rfl⟩ : syracuseStep 4670885 = 875791) (by norm_num)
theorem B1476029 : Blo 1228432 1476029 := bbase (se 3 (by rfl) ⟨276755, by rfl⟩ : syracuseStep 1476029 = 553511) (by norm_num)
theorem B2074045 : Blo 1228432 2074045 := bbase (se 3 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 2074045 = 777767) (by norm_num)
theorem B1844669 : Blo 1228432 1844669 := bbase (se 3 (by rfl) ⟨345875, by rfl⟩ : syracuseStep 1844669 = 691751) (by norm_num)
theorem B13469141 : Blo 1228432 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B1844693 : Blo 1228432 1844693 := bbase (se 7 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 1844693 = 43235) (by norm_num)
theorem B1844717 : Blo 1228432 1844717 := bbase (se 3 (by rfl) ⟨345884, by rfl⟩ : syracuseStep 1844717 = 691769) (by norm_num)
theorem B1246709 : Blo 1228432 1246709 := bbase (se 5 (by rfl) ⟨58439, by rfl⟩ : syracuseStep 1246709 = 116879) (by norm_num)
theorem B1844741 : Blo 1228432 1844741 := bbase (se 4 (by rfl) ⟨172944, by rfl⟩ : syracuseStep 1844741 = 345889) (by norm_num)
theorem B2074133 : Blo 1228432 2074133 := bbase (se 6 (by rfl) ⟨48612, by rfl⟩ : syracuseStep 2074133 = 97225) (by norm_num)
theorem B1844765 : Blo 1228432 1844765 := bbase (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) (by norm_num)
theorem B1844789 : Blo 1228432 1844789 := bbase (se 5 (by rfl) ⟨86474, by rfl⟩ : syracuseStep 1844789 = 172949) (by norm_num)
theorem B1844813 : Blo 1228432 1844813 := bbase (se 3 (by rfl) ⟨345902, by rfl⟩ : syracuseStep 1844813 = 691805) (by norm_num)
theorem B3737173 : Blo 1228432 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B1402465 : Blo 1228432 1402465 := bbase (se 2 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 1402465 = 1051849) (by norm_num)
theorem B1844837 : Blo 1228432 1844837 := bbase (se 4 (by rfl) ⟨172953, by rfl⟩ : syracuseStep 1844837 = 345907) (by norm_num)
theorem B1894013 : Blo 1228432 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B1844861 : Blo 1228432 1844861 := bbase (se 3 (by rfl) ⟨345911, by rfl⟩ : syracuseStep 1844861 = 691823) (by norm_num)
theorem B4146821 : Blo 1228432 4146821 := bbase (se 4 (by rfl) ⟨388764, by rfl⟩ : syracuseStep 4146821 = 777529) (by norm_num)
theorem B1312405 : Blo 1228432 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2074261 : Blo 1228432 2074261 := bbase (se 6 (by rfl) ⟨48615, by rfl⟩ : syracuseStep 2074261 = 97231) (by norm_num)
theorem B1844885 : Blo 1228432 1844885 := bbase (se 6 (by rfl) ⟨43239, by rfl⟩ : syracuseStep 1844885 = 86479) (by norm_num)
theorem B1844909 : Blo 1228432 1844909 := bbase (se 3 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 1844909 = 691841) (by norm_num)
theorem B1844933 : Blo 1228432 1844933 := bbase (se 4 (by rfl) ⟨172962, by rfl⟩ : syracuseStep 1844933 = 345925) (by norm_num)
theorem B1844957 : Blo 1228432 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B2074349 : Blo 1228432 2074349 := bbase (se 3 (by rfl) ⟨388940, by rfl⟩ : syracuseStep 2074349 = 777881) (by norm_num)
theorem B1844981 : Blo 1228432 1844981 := bbase (se 5 (by rfl) ⟨86483, by rfl⟩ : syracuseStep 1844981 = 172967) (by norm_num)
theorem B1967885 : Blo 1228432 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B1312525 : Blo 1228432 1312525 := bbase (se 3 (by rfl) ⟨246098, by rfl⟩ : syracuseStep 1312525 = 492197) (by norm_num)
theorem B1845005 : Blo 1228432 1845005 := bbase (se 3 (by rfl) ⟨345938, by rfl⟩ : syracuseStep 1845005 = 691877) (by norm_num)
theorem B1845029 : Blo 1228432 1845029 := bbase (se 4 (by rfl) ⟨172971, by rfl⟩ : syracuseStep 1845029 = 345943) (by norm_num)
theorem B6227765 : Blo 1228432 6227765 := bbase (se 5 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 6227765 = 583853) (by norm_num)
theorem B1845053 : Blo 1228432 1845053 := bbase (se 3 (by rfl) ⟨345947, by rfl⟩ : syracuseStep 1845053 = 691895) (by norm_num)
theorem B1247057 : Blo 1228432 1247057 := bbase (se 2 (by rfl) ⟨467646, by rfl⟩ : syracuseStep 1247057 = 935293) (by norm_num)
theorem B3499861 : Blo 1228432 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B1845077 : Blo 1228432 1845077 := bbase (se 9 (by rfl) ⟨5405, by rfl⟩ : syracuseStep 1845077 = 10811) (by norm_num)
theorem B2074477 : Blo 1228432 2074477 := bbase (se 3 (by rfl) ⟨388964, by rfl⟩ : syracuseStep 2074477 = 777929) (by norm_num)
theorem B1845101 : Blo 1228432 1845101 := bbase (se 3 (by rfl) ⟨345956, by rfl⟩ : syracuseStep 1845101 = 691913) (by norm_num)
theorem B1845125 : Blo 1228432 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B1845149 : Blo 1228432 1845149 := bbase (se 3 (by rfl) ⟨345965, by rfl⟩ : syracuseStep 1845149 = 691931) (by norm_num)
theorem B1845173 : Blo 1228432 1845173 := bbase (se 5 (by rfl) ⟨86492, by rfl⟩ : syracuseStep 1845173 = 172985) (by norm_num)
theorem B2525117 : Blo 1228432 2525117 := bbase (se 3 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 2525117 = 946919) (by norm_num)
theorem B2074565 : Blo 1228432 2074565 := bbase (se 4 (by rfl) ⟨194490, by rfl⟩ : syracuseStep 2074565 = 388981) (by norm_num)
theorem B1845197 : Blo 1228432 1845197 := bbase (se 3 (by rfl) ⟨345974, by rfl⟩ : syracuseStep 1845197 = 691949) (by norm_num)
theorem B1845221 : Blo 1228432 1845221 := bbase (se 4 (by rfl) ⟨172989, by rfl⟩ : syracuseStep 1845221 = 345979) (by norm_num)
theorem B1845245 : Blo 1228432 1845245 := bbase (se 3 (by rfl) ⟨345983, by rfl⟩ : syracuseStep 1845245 = 691967) (by norm_num)
theorem B1312777 : Blo 1228432 1312777 := bbase (se 2 (by rfl) ⟨492291, by rfl⟩ : syracuseStep 1312777 = 984583) (by norm_num)
theorem B1312781 : Blo 1228432 1312781 := bbase (se 3 (by rfl) ⟨246146, by rfl⟩ : syracuseStep 1312781 = 492293) (by norm_num)
theorem B1845269 : Blo 1228432 1845269 := bbase (se 6 (by rfl) ⟨43248, by rfl⟩ : syracuseStep 1845269 = 86497) (by norm_num)
theorem B1845293 : Blo 1228432 1845293 := bbase (se 3 (by rfl) ⟨345992, by rfl⟩ : syracuseStep 1845293 = 691985) (by norm_num)
theorem B4147253 : Blo 1228432 4147253 := bbase (se 5 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 4147253 = 388805) (by norm_num)
theorem B2074693 : Blo 1228432 2074693 := bbase (se 4 (by rfl) ⟨194502, by rfl⟩ : syracuseStep 2074693 = 389005) (by norm_num)
theorem B1845317 : Blo 1228432 1845317 := bbase (se 4 (by rfl) ⟨172998, by rfl⟩ : syracuseStep 1845317 = 345997) (by norm_num)
theorem B1845341 : Blo 1228432 1845341 := bbase (se 3 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 1845341 = 692003) (by norm_num)
theorem B1476721 : Blo 1228432 1476721 := bbase (se 2 (by rfl) ⟨553770, by rfl⟩ : syracuseStep 1476721 = 1107541) (by norm_num)
theorem B1476725 : Blo 1228432 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B1845365 : Blo 1228432 1845365 := bbase (se 5 (by rfl) ⟨86501, by rfl⟩ : syracuseStep 1845365 = 173003) (by norm_num)
theorem B1845389 : Blo 1228432 1845389 := bbase (se 3 (by rfl) ⟨346010, by rfl⟩ : syracuseStep 1845389 = 692021) (by norm_num)
theorem B2074781 : Blo 1228432 2074781 := bbase (se 3 (by rfl) ⟨389021, by rfl⟩ : syracuseStep 2074781 = 778043) (by norm_num)
theorem B1845413 : Blo 1228432 1845413 := bbase (se 4 (by rfl) ⟨173007, by rfl⟩ : syracuseStep 1845413 = 346015) (by norm_num)
theorem B4729013 : Blo 1228432 4729013 := bbase (se 5 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 4729013 = 443345) (by norm_num)
theorem B2803901 : Blo 1228432 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B1845437 : Blo 1228432 1845437 := bbase (se 3 (by rfl) ⟨346019, by rfl⟩ : syracuseStep 1845437 = 692039) (by norm_num)
theorem B6219989 : Blo 1228432 6219989 := bbase (se 7 (by rfl) ⟨72890, by rfl⟩ : syracuseStep 6219989 = 145781) (by norm_num)
theorem B1845461 : Blo 1228432 1845461 := bbase (se 7 (by rfl) ⟨21626, by rfl⟩ : syracuseStep 1845461 = 43253) (by norm_num)
theorem B1845485 : Blo 1228432 1845485 := bbase (se 3 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 1845485 = 692057) (by norm_num)
theorem B1845509 : Blo 1228432 1845509 := bbase (se 4 (by rfl) ⟨173016, by rfl⟩ : syracuseStep 1845509 = 346033) (by norm_num)
theorem B2803981 : Blo 1228432 2803981 := bbase (se 3 (by rfl) ⟨525746, by rfl⟩ : syracuseStep 2803981 = 1051493) (by norm_num)
theorem B2074909 : Blo 1228432 2074909 := bbase (se 3 (by rfl) ⟨389045, by rfl⟩ : syracuseStep 2074909 = 778091) (by norm_num)
theorem B1845533 : Blo 1228432 1845533 := bbase (se 3 (by rfl) ⟨346037, by rfl⟩ : syracuseStep 1845533 = 692075) (by norm_num)
theorem B1845557 : Blo 1228432 1845557 := bbase (se 5 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 1845557 = 173021) (by norm_num)
theorem B1845581 : Blo 1228432 1845581 := bbase (se 3 (by rfl) ⟨346046, by rfl⟩ : syracuseStep 1845581 = 692093) (by norm_num)
theorem B1845605 : Blo 1228432 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B2074997 : Blo 1228432 2074997 := bbase (se 5 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 2074997 = 194531) (by norm_num)
theorem B1845629 : Blo 1228432 1845629 := bbase (se 3 (by rfl) ⟨346055, by rfl⟩ : syracuseStep 1845629 = 692111) (by norm_num)
theorem B4147685 : Blo 1228432 4147685 := bbase (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) (by norm_num)
theorem B2214389 : Blo 1228432 2214389 := bbase (se 5 (by rfl) ⟨103799, by rfl⟩ : syracuseStep 2214389 = 207599) (by norm_num)
theorem B2075125 : Blo 1228432 2075125 := bbase (se 5 (by rfl) ⟨97271, by rfl⟩ : syracuseStep 2075125 = 194543) (by norm_num)
theorem B5253653 : Blo 1228432 5253653 := bbase (se 6 (by rfl) ⟨123132, by rfl⟩ : syracuseStep 5253653 = 246265) (by norm_num)
theorem B3156533 : Blo 1228432 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B1313345 : Blo 1228432 1313345 := bbase (se 2 (by rfl) ⟨492504, by rfl⟩ : syracuseStep 1313345 = 985009) (by norm_num)
theorem B2214469 : Blo 1228432 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B2075213 : Blo 1228432 2075213 := bbase (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) (by norm_num)
theorem B2493013 : Blo 1228432 2493013 := bbase (se 8 (by rfl) ⟨14607, by rfl⟩ : syracuseStep 2493013 = 29215) (by norm_num)
theorem B2624093 : Blo 1228432 2624093 := bbase (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) (by norm_num)
theorem B1477225 : Blo 1228432 1477225 := bbase (se 2 (by rfl) ⟨553959, by rfl⟩ : syracuseStep 1477225 = 1107919) (by norm_num)
theorem B2951797 : Blo 1228432 2951797 := bbase (se 5 (by rfl) ⟨138365, by rfl⟩ : syracuseStep 2951797 = 276731) (by norm_num)
theorem B1419973 : Blo 1228432 1419973 := bbase (se 4 (by rfl) ⟨133122, by rfl⟩ : syracuseStep 1419973 = 266245) (by norm_num)
theorem B2075341 : Blo 1228432 2075341 := bbase (se 3 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 2075341 = 778253) (by norm_num)
theorem B2624213 : Blo 1228432 2624213 := bbase (se 7 (by rfl) ⟨30752, by rfl⟩ : syracuseStep 2624213 = 61505) (by norm_num)
theorem B1968877 : Blo 1228432 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B1313533 : Blo 1228432 1313533 := bbase (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) (by norm_num)
theorem B4205317 : Blo 1228432 4205317 := bbase (se 4 (by rfl) ⟨394248, by rfl⟩ : syracuseStep 4205317 = 788497) (by norm_num)
theorem B5253893 : Blo 1228432 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B2075429 : Blo 1228432 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B4148117 : Blo 1228432 4148117 := bbase (se 6 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 4148117 = 194443) (by norm_num)
theorem B2075557 : Blo 1228432 2075557 := bbase (se 4 (by rfl) ⟨194583, by rfl⟩ : syracuseStep 2075557 = 389167) (by norm_num)
theorem B1870757 : Blo 1228432 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B1477609 : Blo 1228432 1477609 := bbase (se 2 (by rfl) ⟨554103, by rfl⟩ : syracuseStep 1477609 = 1108207) (by norm_num)
theorem B2075645 : Blo 1228432 2075645 := bbase (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) (by norm_num)
theorem B6229061 : Blo 1228432 6229061 := bbase (se 4 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 6229061 = 1167949) (by norm_num)
theorem B3940933 : Blo 1228432 3940933 := bbase (se 4 (by rfl) ⟨369462, by rfl⟩ : syracuseStep 3940933 = 738925) (by norm_num)
theorem B2075773 : Blo 1228432 2075773 := bbase (se 3 (by rfl) ⟨389207, by rfl⟩ : syracuseStep 2075773 = 778415) (by norm_num)
theorem B5909669 : Blo 1228432 5909669 := bbase (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) (by norm_num)
theorem B2763989 : Blo 1228432 2763989 := bbase (se 7 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 2763989 = 64781) (by norm_num)
theorem B2075861 : Blo 1228432 2075861 := bbase (se 7 (by rfl) ⟨24326, by rfl⟩ : syracuseStep 2075861 = 48653) (by norm_num)
theorem B2952413 : Blo 1228432 2952413 := bbase (se 3 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 2952413 = 1107155) (by norm_num)
theorem B3935461 : Blo 1228432 3935461 := bbase (se 4 (by rfl) ⟨368949, by rfl⟩ : syracuseStep 3935461 = 737899) (by norm_num)
theorem B2764061 : Blo 1228432 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B2493725 : Blo 1228432 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B4148549 : Blo 1228432 4148549 := bbase (se 4 (by rfl) ⟨388926, by rfl⟩ : syracuseStep 4148549 = 777853) (by norm_num)
theorem B2624845 : Blo 1228432 2624845 := bbase (se 3 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 2624845 = 984317) (by norm_num)
theorem B56773973 : Blo 1228432 56773973 := bbase (se 11 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 56773973 = 83165) (by norm_num)
theorem B2075989 : Blo 1228432 2075989 := bbase (se 11 (by rfl) ⟨1520, by rfl⟩ : syracuseStep 2075989 = 3041) (by norm_num)
theorem B2764133 : Blo 1228432 2764133 := bbase (se 4 (by rfl) ⟨259137, by rfl⟩ : syracuseStep 2764133 = 518275) (by norm_num)
theorem B1969525 : Blo 1228432 1969525 := bbase (se 5 (by rfl) ⟨92321, by rfl⟩ : syracuseStep 1969525 = 184643) (by norm_num)
theorem B20999573 : Blo 1228432 20999573 := bbase (se 6 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 20999573 = 984355) (by norm_num)
theorem B2952605 : Blo 1228432 2952605 := bbase (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) (by norm_num)
theorem B2764205 : Blo 1228432 2764205 := bbase (se 3 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 2764205 = 1036577) (by norm_num)
theorem B2076077 : Blo 1228432 2076077 := bbase (se 3 (by rfl) ⟨389264, by rfl⟩ : syracuseStep 2076077 = 778529) (by norm_num)
theorem B6221285 : Blo 1228432 6221285 := bbase (se 4 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 6221285 = 1166491) (by norm_num)
theorem B2764277 : Blo 1228432 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B2952701 : Blo 1228432 2952701 := bbase (se 3 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 2952701 = 1107263) (by norm_num)
theorem B2076205 : Blo 1228432 2076205 := bbase (se 3 (by rfl) ⟨389288, by rfl⟩ : syracuseStep 2076205 = 778577) (by norm_num)
theorem B2764349 : Blo 1228432 2764349 := bbase (se 3 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 2764349 = 1036631) (by norm_num)
theorem B2215549 : Blo 1228432 2215549 := bbase (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) (by norm_num)
theorem B2764421 : Blo 1228432 2764421 := bbase (se 4 (by rfl) ⟨259164, by rfl⟩ : syracuseStep 2764421 = 518329) (by norm_num)
theorem B2076293 : Blo 1228432 2076293 := bbase (se 4 (by rfl) ⟨194652, by rfl⟩ : syracuseStep 2076293 = 389305) (by norm_num)
theorem B7876277 : Blo 1228432 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B2764493 : Blo 1228432 2764493 := bbase (se 3 (by rfl) ⟨518342, by rfl⟩ : syracuseStep 2764493 = 1036685) (by norm_num)
theorem B4148981 : Blo 1228432 4148981 := bbase (se 5 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 4148981 = 388967) (by norm_num)
theorem B2215693 : Blo 1228432 2215693 := bbase (se 3 (by rfl) ⟨415442, by rfl⟩ : syracuseStep 2215693 = 830885) (by norm_num)
theorem B2764565 : Blo 1228432 2764565 := bbase (se 6 (by rfl) ⟨64794, by rfl⟩ : syracuseStep 2764565 = 129589) (by norm_num)
theorem B2764637 : Blo 1228432 2764637 := bbase (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) (by norm_num)
theorem B6647669 : Blo 1228432 6647669 := bbase (se 5 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 6647669 = 623219) (by norm_num)
theorem B4665221 : Blo 1228432 4665221 := bbase (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) (by norm_num)
theorem B2764709 : Blo 1228432 2764709 := bbase (se 4 (by rfl) ⟨259191, by rfl⟩ : syracuseStep 2764709 = 518383) (by norm_num)
theorem B2215853 : Blo 1228432 2215853 := bbase (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) (by norm_num)
theorem B2764781 : Blo 1228432 2764781 := bbase (se 3 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 2764781 = 1036793) (by norm_num)
theorem B3936293 : Blo 1228432 3936293 := bbase (se 4 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 3936293 = 738055) (by norm_num)
theorem B2764853 : Blo 1228432 2764853 := bbase (se 5 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 2764853 = 259205) (by norm_num)
theorem B2101373 : Blo 1228432 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B2764925 : Blo 1228432 2764925 := bbase (se 3 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 2764925 = 1036847) (by norm_num)
theorem B4665509 : Blo 1228432 4665509 := bbase (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) (by norm_num)
theorem B4149413 : Blo 1228432 4149413 := bbase (se 4 (by rfl) ⟨389007, by rfl⟩ : syracuseStep 4149413 = 778015) (by norm_num)
theorem B2764997 : Blo 1228432 2764997 := bbase (se 4 (by rfl) ⟨259218, by rfl⟩ : syracuseStep 2764997 = 518437) (by norm_num)
theorem B2625733 : Blo 1228432 2625733 := bbase (se 4 (by rfl) ⟨246162, by rfl⟩ : syracuseStep 2625733 = 492325) (by norm_num)
theorem B2101453 : Blo 1228432 2101453 := bbase (se 3 (by rfl) ⟨394022, by rfl⟩ : syracuseStep 2101453 = 788045) (by norm_num)
theorem B2765069 : Blo 1228432 2765069 := bbase (se 3 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 2765069 = 1036901) (by norm_num)
theorem B1970453 : Blo 1228432 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B2101565 : Blo 1228432 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B2625853 : Blo 1228432 2625853 := bbase (se 3 (by rfl) ⟨492347, by rfl⟩ : syracuseStep 2625853 = 984695) (by norm_num)
theorem B2765141 : Blo 1228432 2765141 := bbase (se 10 (by rfl) ⟨4050, by rfl⟩ : syracuseStep 2765141 = 8101) (by norm_num)
theorem B9343349 : Blo 1228432 9343349 := bbase (se 5 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 9343349 = 875939) (by norm_num)
theorem B2765213 : Blo 1228432 2765213 := bbase (se 3 (by rfl) ⟨518477, by rfl⟩ : syracuseStep 2765213 = 1036955) (by norm_num)
theorem B4493765 : Blo 1228432 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B2765285 : Blo 1228432 2765285 := bbase (se 4 (by rfl) ⟨259245, by rfl⟩ : syracuseStep 2765285 = 518491) (by norm_num)
theorem B2765357 : Blo 1228432 2765357 := bbase (se 3 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 2765357 = 1037009) (by norm_num)
theorem B2626109 : Blo 1228432 2626109 := bbase (se 3 (by rfl) ⟨492395, by rfl⟩ : syracuseStep 2626109 = 984791) (by norm_num)
theorem B4149845 : Blo 1228432 4149845 := bbase (se 8 (by rfl) ⟨24315, by rfl⟩ : syracuseStep 4149845 = 48631) (by norm_num)
theorem B1577569 : Blo 1228432 1577569 := bbase (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) (by norm_num)
theorem B5247605 : Blo 1228432 5247605 := bbase (se 5 (by rfl) ⟨245981, by rfl⟩ : syracuseStep 5247605 = 491963) (by norm_num)
theorem B2765429 : Blo 1228432 2765429 := bbase (se 5 (by rfl) ⟨129629, by rfl⟩ : syracuseStep 2765429 = 259259) (by norm_num)
theorem B3502709 : Blo 1228432 3502709 := bbase (se 5 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 3502709 = 328379) (by norm_num)
theorem B3109549 : Blo 1228432 3109549 := bbase (se 3 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 3109549 = 1166081) (by norm_num)
theorem B4207285 : Blo 1228432 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B2765501 : Blo 1228432 2765501 := bbase (se 3 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 2765501 = 1037063) (by norm_num)
theorem B1970909 : Blo 1228432 1970909 := bbase (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) (by norm_num)
theorem B1577713 : Blo 1228432 1577713 := bbase (se 2 (by rfl) ⟨591642, by rfl⟩ : syracuseStep 1577713 = 1183285) (by norm_num)
theorem B6222581 : Blo 1228432 6222581 := bbase (se 5 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 6222581 = 583367) (by norm_num)
theorem B2765573 : Blo 1228432 2765573 := bbase (se 4 (by rfl) ⟨259272, by rfl⟩ : syracuseStep 2765573 = 518545) (by norm_num)
theorem B9335573 : Blo 1228432 9335573 := bbase (se 6 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 9335573 = 437605) (by norm_num)
theorem B3109661 : Blo 1228432 3109661 := bbase (se 3 (by rfl) ⟨583061, by rfl⟩ : syracuseStep 3109661 = 1166123) (by norm_num)
theorem B2765645 : Blo 1228432 2765645 := bbase (se 3 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 2765645 = 1037117) (by norm_num)
theorem B2765717 : Blo 1228432 2765717 := bbase (se 6 (by rfl) ⟨64821, by rfl⟩ : syracuseStep 2765717 = 129643) (by norm_num)
theorem B3109853 : Blo 1228432 3109853 := bbase (se 3 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 3109853 = 1166195) (by norm_num)
theorem B2765789 : Blo 1228432 2765789 := bbase (se 3 (by rfl) ⟨518585, by rfl⟩ : syracuseStep 2765789 = 1037171) (by norm_num)
theorem B4150277 : Blo 1228432 4150277 := bbase (se 4 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 4150277 = 778177) (by norm_num)
theorem B23622677 : Blo 1228432 23622677 := bbase (se 6 (by rfl) ⟨553656, by rfl⟩ : syracuseStep 23622677 = 1107313) (by norm_num)
theorem B2765861 : Blo 1228432 2765861 := bbase (se 4 (by rfl) ⟨259299, by rfl⟩ : syracuseStep 2765861 = 518599) (by norm_num)
theorem B10237013 : Blo 1228432 10237013 := bbase (se 8 (by rfl) ⟨59982, by rfl⟩ : syracuseStep 10237013 = 119965) (by norm_num)
theorem B8983637 : Blo 1228432 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B2765933 : Blo 1228432 2765933 := bbase (se 3 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 2765933 = 1037225) (by norm_num)
theorem B1578097 : Blo 1228432 1578097 := bbase (se 2 (by rfl) ⟨591786, by rfl⟩ : syracuseStep 1578097 = 1183573) (by norm_num)
theorem B2766005 : Blo 1228432 2766005 := bbase (se 5 (by rfl) ⟨129656, by rfl⟩ : syracuseStep 2766005 = 259313) (by norm_num)
theorem B1750261 : Blo 1228432 1750261 := bbase (se 5 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 1750261 = 164087) (by norm_num)
theorem B2766077 : Blo 1228432 2766077 := bbase (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) (by norm_num)
theorem B3110197 : Blo 1228432 3110197 := bbase (se 5 (by rfl) ⟨145790, by rfl⟩ : syracuseStep 3110197 = 291581) (by norm_num)
theorem B4666693 : Blo 1228432 4666693 := bbase (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) (by norm_num)
theorem B2766149 : Blo 1228432 2766149 := bbase (se 4 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 2766149 = 518653) (by norm_num)
theorem B2766221 : Blo 1228432 2766221 := bbase (se 3 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 2766221 = 1037333) (by norm_num)
theorem B3110309 : Blo 1228432 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B4150709 : Blo 1228432 4150709 := bbase (se 5 (by rfl) ⟨194564, by rfl⟩ : syracuseStep 4150709 = 389129) (by norm_num)
theorem B2626997 : Blo 1228432 2626997 := bbase (se 5 (by rfl) ⟨123140, by rfl⟩ : syracuseStep 2626997 = 246281) (by norm_num)
theorem B2766293 : Blo 1228432 2766293 := bbase (se 7 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 2766293 = 64835) (by norm_num)
theorem B6313477 : Blo 1228432 6313477 := bbase (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) (by norm_num)
theorem B2766365 : Blo 1228432 2766365 := bbase (se 3 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 2766365 = 1037387) (by norm_num)
theorem B6649397 : Blo 1228432 6649397 := bbase (se 5 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 6649397 = 623381) (by norm_num)
theorem B2332253 : Blo 1228432 2332253 := bbase (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) (by norm_num)
theorem B3110501 : Blo 1228432 3110501 := bbase (se 4 (by rfl) ⟨291609, by rfl⟩ : syracuseStep 3110501 = 583219) (by norm_num)
theorem B2766437 : Blo 1228432 2766437 := bbase (se 4 (by rfl) ⟨259353, by rfl⟩ : syracuseStep 2766437 = 518707) (by norm_num)
theorem B4666997 : Blo 1228432 4666997 := bbase (se 5 (by rfl) ⟨218765, by rfl⟩ : syracuseStep 4666997 = 437531) (by norm_num)
theorem B1382017 : Blo 1228432 1382017 := bbase (se 2 (by rfl) ⟨518256, by rfl⟩ : syracuseStep 1382017 = 1036513) (by norm_num)
theorem B1382053 : Blo 1228432 1382053 := bbase (se 4 (by rfl) ⟨129567, by rfl⟩ : syracuseStep 1382053 = 259135) (by norm_num)
theorem B2627237 : Blo 1228432 2627237 := bbase (se 4 (by rfl) ⟨246303, by rfl⟩ : syracuseStep 2627237 = 492607) (by norm_num)
theorem B2766509 : Blo 1228432 2766509 := bbase (se 3 (by rfl) ⟨518720, by rfl⟩ : syracuseStep 2766509 = 1037441) (by norm_num)
theorem B4732613 : Blo 1228432 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B1382089 : Blo 1228432 1382089 := bbase (se 2 (by rfl) ⟨518283, by rfl⟩ : syracuseStep 1382089 = 1036567) (by norm_num)
theorem B4429541 : Blo 1228432 4429541 := bbase (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) (by norm_num)
theorem B1382125 : Blo 1228432 1382125 := bbase (se 3 (by rfl) ⟨259148, by rfl⟩ : syracuseStep 1382125 = 518297) (by norm_num)
theorem B2332405 : Blo 1228432 2332405 := bbase (se 5 (by rfl) ⟨109331, by rfl⟩ : syracuseStep 2332405 = 218663) (by norm_num)
theorem B2766581 : Blo 1228432 2766581 := bbase (se 5 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 2766581 = 259367) (by norm_num)
theorem B1382161 : Blo 1228432 1382161 := bbase (se 2 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 1382161 = 1036621) (by norm_num)
theorem B1382197 : Blo 1228432 1382197 := bbase (se 5 (by rfl) ⟨64790, by rfl⟩ : syracuseStep 1382197 = 129581) (by norm_num)
theorem B7001909 : Blo 1228432 7001909 := bbase (se 5 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 7001909 = 656429) (by norm_num)
theorem B2766653 : Blo 1228432 2766653 := bbase (se 3 (by rfl) ⟨518747, by rfl⟩ : syracuseStep 2766653 = 1037495) (by norm_num)
theorem B1750853 : Blo 1228432 1750853 := bbase (se 4 (by rfl) ⟨164142, by rfl⟩ : syracuseStep 1750853 = 328285) (by norm_num)
theorem B1382233 : Blo 1228432 1382233 := bbase (se 2 (by rfl) ⟨518337, by rfl⟩ : syracuseStep 1382233 = 1036675) (by norm_num)
theorem B4151141 : Blo 1228432 4151141 := bbase (se 4 (by rfl) ⟨389169, by rfl⟩ : syracuseStep 4151141 = 778339) (by norm_num)
theorem B3938165 : Blo 1228432 3938165 := bbase (se 5 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 3938165 = 369203) (by norm_num)
theorem B1382269 : Blo 1228432 1382269 := bbase (se 3 (by rfl) ⟨259175, by rfl⟩ : syracuseStep 1382269 = 518351) (by norm_num)
theorem B2955133 : Blo 1228432 2955133 := bbase (se 3 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 2955133 = 1108175) (by norm_num)
theorem B2766725 : Blo 1228432 2766725 := bbase (se 4 (by rfl) ⟨259380, by rfl⟩ : syracuseStep 2766725 = 518761) (by norm_num)
theorem B1750933 : Blo 1228432 1750933 := bbase (se 6 (by rfl) ⟨41037, by rfl⟩ : syracuseStep 1750933 = 82075) (by norm_num)
theorem B1382305 : Blo 1228432 1382305 := bbase (se 2 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 1382305 = 1036729) (by norm_num)
theorem B3110845 : Blo 1228432 3110845 := bbase (se 3 (by rfl) ⟨583283, by rfl⟩ : syracuseStep 3110845 = 1166567) (by norm_num)
theorem B1382341 : Blo 1228432 1382341 := bbase (se 4 (by rfl) ⟨129594, by rfl⟩ : syracuseStep 1382341 = 259189) (by norm_num)
theorem B2766797 : Blo 1228432 2766797 := bbase (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) (by norm_num)
theorem B1382377 : Blo 1228432 1382377 := bbase (se 2 (by rfl) ⟨518391, by rfl⟩ : syracuseStep 1382377 = 1036783) (by norm_num)
theorem B4429829 : Blo 1228432 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B6223877 : Blo 1228432 6223877 := bbase (se 4 (by rfl) ⟨583488, by rfl⟩ : syracuseStep 6223877 = 1166977) (by norm_num)
theorem B1382413 : Blo 1228432 1382413 := bbase (se 3 (by rfl) ⟨259202, by rfl⟩ : syracuseStep 1382413 = 518405) (by norm_num)
theorem B1751053 : Blo 1228432 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B2766869 : Blo 1228432 2766869 := bbase (se 6 (by rfl) ⟨64848, by rfl⟩ : syracuseStep 2766869 = 129697) (by norm_num)
theorem B2332709 : Blo 1228432 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B3110957 : Blo 1228432 3110957 := bbase (se 3 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 3110957 = 1166609) (by norm_num)
theorem B1382449 : Blo 1228432 1382449 := bbase (se 2 (by rfl) ⟨518418, by rfl⟩ : syracuseStep 1382449 = 1036837) (by norm_num)
theorem B1382485 : Blo 1228432 1382485 := bbase (se 8 (by rfl) ⟨8100, by rfl⟩ : syracuseStep 1382485 = 16201) (by norm_num)
theorem B2766941 : Blo 1228432 2766941 := bbase (se 3 (by rfl) ⟨518801, by rfl⟩ : syracuseStep 2766941 = 1037603) (by norm_num)
theorem B1751149 : Blo 1228432 1751149 := bbase (se 3 (by rfl) ⟨328340, by rfl⟩ : syracuseStep 1751149 = 656681) (by norm_num)
theorem B1382521 : Blo 1228432 1382521 := bbase (se 2 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 1382521 = 1036891) (by norm_num)
theorem B1382557 : Blo 1228432 1382557 := bbase (se 3 (by rfl) ⟨259229, by rfl⟩ : syracuseStep 1382557 = 518459) (by norm_num)
theorem B2627741 : Blo 1228432 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B2767013 : Blo 1228432 2767013 := bbase (se 4 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 2767013 = 518815) (by norm_num)
theorem B2627749 : Blo 1228432 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B1382593 : Blo 1228432 1382593 := bbase (se 2 (by rfl) ⟨518472, by rfl⟩ : syracuseStep 1382593 = 1036945) (by norm_num)
theorem B2955469 : Blo 1228432 2955469 := bbase (se 3 (by rfl) ⟨554150, by rfl⟩ : syracuseStep 2955469 = 1108301) (by norm_num)
theorem B1382629 : Blo 1228432 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B3111149 : Blo 1228432 3111149 := bbase (se 3 (by rfl) ⟨583340, by rfl⟩ : syracuseStep 3111149 = 1166681) (by norm_num)
theorem B2767085 : Blo 1228432 2767085 := bbase (se 3 (by rfl) ⟨518828, by rfl⟩ : syracuseStep 2767085 = 1037657) (by norm_num)
theorem B1382665 : Blo 1228432 1382665 := bbase (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) (by norm_num)
theorem B4151573 : Blo 1228432 4151573 := bbase (se 6 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 4151573 = 194605) (by norm_num)
theorem B1382701 : Blo 1228432 1382701 := bbase (se 3 (by rfl) ⟨259256, by rfl⟩ : syracuseStep 1382701 = 518513) (by norm_num)
theorem B2767157 : Blo 1228432 2767157 := bbase (se 5 (by rfl) ⟨129710, by rfl⟩ : syracuseStep 2767157 = 259421) (by norm_num)
theorem B1382737 : Blo 1228432 1382737 := bbase (se 2 (by rfl) ⟨518526, by rfl⟩ : syracuseStep 1382737 = 1037053) (by norm_num)
theorem B1382773 : Blo 1228432 1382773 := bbase (se 5 (by rfl) ⟨64817, by rfl⟩ : syracuseStep 1382773 = 129635) (by norm_num)
theorem B1554805 : Blo 1228432 1554805 := bbase (se 5 (by rfl) ⟨72881, by rfl⟩ : syracuseStep 1554805 = 145763) (by norm_num)
theorem B2767229 : Blo 1228432 2767229 := bbase (se 3 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 2767229 = 1037711) (by norm_num)
theorem B1382809 : Blo 1228432 1382809 := bbase (se 2 (by rfl) ⟨518553, by rfl⟩ : syracuseStep 1382809 = 1037107) (by norm_num)
theorem B1382845 : Blo 1228432 1382845 := bbase (se 3 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 1382845 = 518567) (by norm_num)
theorem B2275781 : Blo 1228432 2275781 := bbase (se 4 (by rfl) ⟨213354, by rfl⟩ : syracuseStep 2275781 = 426709) (by norm_num)
theorem B2767301 : Blo 1228432 2767301 := bbase (se 4 (by rfl) ⟨259434, by rfl⟩ : syracuseStep 2767301 = 518869) (by norm_num)
theorem B1382881 : Blo 1228432 1382881 := bbase (se 2 (by rfl) ⟨518580, by rfl⟩ : syracuseStep 1382881 = 1037161) (by norm_num)
theorem B1382917 : Blo 1228432 1382917 := bbase (se 4 (by rfl) ⟨129648, by rfl⟩ : syracuseStep 1382917 = 259297) (by norm_num)
theorem B2767373 : Blo 1228432 2767373 := bbase (se 3 (by rfl) ⟨518882, by rfl⟩ : syracuseStep 2767373 = 1037765) (by norm_num)
theorem B1554977 : Blo 1228432 1554977 := bbase (se 2 (by rfl) ⟨583116, by rfl⟩ : syracuseStep 1554977 = 1166233) (by norm_num)
theorem B1382953 : Blo 1228432 1382953 := bbase (se 2 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 1382953 = 1037215) (by norm_num)
theorem B3111493 : Blo 1228432 3111493 := bbase (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) (by norm_num)
theorem B1382989 : Blo 1228432 1382989 := bbase (se 3 (by rfl) ⟨259310, by rfl⟩ : syracuseStep 1382989 = 518621) (by norm_num)
theorem B2767445 : Blo 1228432 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B1555033 : Blo 1228432 1555033 := bbase (se 2 (by rfl) ⟨583137, by rfl⟩ : syracuseStep 1555033 = 1166275) (by norm_num)
theorem B1751645 : Blo 1228432 1751645 := bbase (se 3 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 1751645 = 656867) (by norm_num)
theorem B1383025 : Blo 1228432 1383025 := bbase (se 2 (by rfl) ⟨518634, by rfl⟩ : syracuseStep 1383025 = 1037269) (by norm_num)
theorem B1383061 : Blo 1228432 1383061 := bbase (se 6 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 1383061 = 64831) (by norm_num)
theorem B2767517 : Blo 1228432 2767517 := bbase (se 3 (by rfl) ⟨518909, by rfl⟩ : syracuseStep 2767517 = 1037819) (by norm_num)
theorem B3111605 : Blo 1228432 3111605 := bbase (se 5 (by rfl) ⟨145856, by rfl⟩ : syracuseStep 3111605 = 291713) (by norm_num)
theorem B1555129 : Blo 1228432 1555129 := bbase (se 2 (by rfl) ⟨583173, by rfl⟩ : syracuseStep 1555129 = 1166347) (by norm_num)
theorem B1383097 : Blo 1228432 1383097 := bbase (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) (by norm_num)
theorem B4152005 : Blo 1228432 4152005 := bbase (se 4 (by rfl) ⟨389250, by rfl⟩ : syracuseStep 4152005 = 778501) (by norm_num)
theorem B1383133 : Blo 1228432 1383133 := bbase (se 3 (by rfl) ⟨259337, by rfl⟩ : syracuseStep 1383133 = 518675) (by norm_num)
theorem B2767589 : Blo 1228432 2767589 := bbase (se 4 (by rfl) ⟨259461, by rfl⟩ : syracuseStep 2767589 = 518923) (by norm_num)
theorem B1383169 : Blo 1228432 1383169 := bbase (se 2 (by rfl) ⟨518688, by rfl⟩ : syracuseStep 1383169 = 1037377) (by norm_num)
theorem B2333461 : Blo 1228432 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B1383205 : Blo 1228432 1383205 := bbase (se 4 (by rfl) ⟨129675, by rfl⟩ : syracuseStep 1383205 = 259351) (by norm_num)
theorem B2767661 : Blo 1228432 2767661 := bbase (se 3 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 2767661 = 1037873) (by norm_num)
theorem B2956085 : Blo 1228432 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B1383241 : Blo 1228432 1383241 := bbase (se 2 (by rfl) ⟨518715, by rfl⟩ : syracuseStep 1383241 = 1037431) (by norm_num)
theorem B1555301 : Blo 1228432 1555301 := bbase (se 4 (by rfl) ⟨145809, by rfl⟩ : syracuseStep 1555301 = 291619) (by norm_num)
theorem B1383277 : Blo 1228432 1383277 := bbase (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) (by norm_num)
theorem B3111797 : Blo 1228432 3111797 := bbase (se 5 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 3111797 = 291731) (by norm_num)
theorem B4733813 : Blo 1228432 4733813 := bbase (se 5 (by rfl) ⟨221897, by rfl⟩ : syracuseStep 4733813 = 443795) (by norm_num)
theorem B2767733 : Blo 1228432 2767733 := bbase (se 5 (by rfl) ⟨129737, by rfl⟩ : syracuseStep 2767733 = 259475) (by norm_num)
theorem B1383313 : Blo 1228432 1383313 := bbase (se 2 (by rfl) ⟨518742, by rfl⟩ : syracuseStep 1383313 = 1037485) (by norm_num)
theorem B1555357 : Blo 1228432 1555357 := bbase (se 3 (by rfl) ⟨291629, by rfl⟩ : syracuseStep 1555357 = 583259) (by norm_num)
theorem B2333605 : Blo 1228432 2333605 := bbase (se 4 (by rfl) ⟨218775, by rfl⟩ : syracuseStep 2333605 = 437551) (by norm_num)
theorem B1383349 : Blo 1228432 1383349 := bbase (se 5 (by rfl) ⟨64844, by rfl⟩ : syracuseStep 1383349 = 129689) (by norm_num)
theorem B2767805 : Blo 1228432 2767805 := bbase (se 3 (by rfl) ⟨518963, by rfl⟩ : syracuseStep 2767805 = 1037927) (by norm_num)
theorem B1383385 : Blo 1228432 1383385 := bbase (se 2 (by rfl) ⟨518769, by rfl⟩ : syracuseStep 1383385 = 1037539) (by norm_num)
theorem B2104301 : Blo 1228432 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B1555453 : Blo 1228432 1555453 := bbase (se 3 (by rfl) ⟨291647, by rfl⟩ : syracuseStep 1555453 = 583295) (by norm_num)
theorem B1383421 : Blo 1228432 1383421 := bbase (se 3 (by rfl) ⟨259391, by rfl⟩ : syracuseStep 1383421 = 518783) (by norm_num)
theorem B2767877 : Blo 1228432 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B1383457 : Blo 1228432 1383457 := bbase (se 2 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 1383457 = 1037593) (by norm_num)
theorem B2333765 : Blo 1228432 2333765 := bbase (se 4 (by rfl) ⟨218790, by rfl⟩ : syracuseStep 2333765 = 437581) (by norm_num)
theorem B1383493 : Blo 1228432 1383493 := bbase (se 4 (by rfl) ⟨129702, by rfl⟩ : syracuseStep 1383493 = 259405) (by norm_num)
theorem B2767949 : Blo 1228432 2767949 := bbase (se 3 (by rfl) ⟨518990, by rfl⟩ : syracuseStep 2767949 = 1037981) (by norm_num)
theorem B1383529 : Blo 1228432 1383529 := bbase (se 2 (by rfl) ⟨518823, by rfl⟩ : syracuseStep 1383529 = 1037647) (by norm_num)
theorem B4152437 : Blo 1228432 4152437 := bbase (se 5 (by rfl) ⟨194645, by rfl⟩ : syracuseStep 4152437 = 389291) (by norm_num)
theorem B1383565 : Blo 1228432 1383565 := bbase (se 3 (by rfl) ⟨259418, by rfl⟩ : syracuseStep 1383565 = 518837) (by norm_num)
theorem B2768021 : Blo 1228432 2768021 := bbase (se 6 (by rfl) ⟨64875, by rfl⟩ : syracuseStep 2768021 = 129751) (by norm_num)
theorem B1555625 : Blo 1228432 1555625 := bbase (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) (by norm_num)
theorem B1383601 : Blo 1228432 1383601 := bbase (se 2 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 1383601 = 1037701) (by norm_num)
theorem B3153077 : Blo 1228432 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B3112141 : Blo 1228432 3112141 := bbase (se 3 (by rfl) ⟨583526, by rfl⟩ : syracuseStep 3112141 = 1167053) (by norm_num)
theorem B2333909 : Blo 1228432 2333909 := bbase (se 7 (by rfl) ⟨27350, by rfl⟩ : syracuseStep 2333909 = 54701) (by norm_num)
theorem B1383637 : Blo 1228432 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B2768093 : Blo 1228432 2768093 := bbase (se 3 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 2768093 = 1038035) (by norm_num)
theorem B1555681 : Blo 1228432 1555681 := bbase (se 2 (by rfl) ⟨583380, by rfl⟩ : syracuseStep 1555681 = 1166761) (by norm_num)
theorem B1383673 : Blo 1228432 1383673 := bbase (se 2 (by rfl) ⟨518877, by rfl⟩ : syracuseStep 1383673 = 1037755) (by norm_num)
theorem B6225173 : Blo 1228432 6225173 := bbase (se 6 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 6225173 = 291805) (by norm_num)
theorem B2366741 : Blo 1228432 2366741 := bbase (se 6 (by rfl) ⟨55470, by rfl⟩ : syracuseStep 2366741 = 110941) (by norm_num)
theorem B1383709 : Blo 1228432 1383709 := bbase (se 3 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 1383709 = 518891) (by norm_num)
theorem B2768165 : Blo 1228432 2768165 := bbase (se 4 (by rfl) ⟨259515, by rfl⟩ : syracuseStep 2768165 = 519031) (by norm_num)
theorem B3112253 : Blo 1228432 3112253 := bbase (se 3 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 3112253 = 1167095) (by norm_num)
theorem B1555777 : Blo 1228432 1555777 := bbase (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) (by norm_num)
theorem B1383745 : Blo 1228432 1383745 := bbase (se 2 (by rfl) ⟨518904, by rfl⟩ : syracuseStep 1383745 = 1037809) (by norm_num)
theorem B1383781 : Blo 1228432 1383781 := bbase (se 4 (by rfl) ⟨129729, by rfl⟩ : syracuseStep 1383781 = 259459) (by norm_num)
theorem B2768237 : Blo 1228432 2768237 := bbase (se 3 (by rfl) ⟨519044, by rfl⟩ : syracuseStep 2768237 = 1038089) (by norm_num)
theorem B1383817 : Blo 1228432 1383817 := bbase (se 2 (by rfl) ⟨518931, by rfl⟩ : syracuseStep 1383817 = 1037863) (by norm_num)
theorem B1383853 : Blo 1228432 1383853 := bbase (se 3 (by rfl) ⟨259472, by rfl⟩ : syracuseStep 1383853 = 518945) (by norm_num)
theorem B6651317 : Blo 1228432 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B2768309 : Blo 1228432 2768309 := bbase (se 5 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 2768309 = 259529) (by norm_num)
theorem B1383889 : Blo 1228432 1383889 := bbase (se 2 (by rfl) ⟨518958, by rfl⟩ : syracuseStep 1383889 = 1037917) (by norm_num)
theorem B1842653 : Blo 1228432 1842653 := bbase (se 3 (by rfl) ⟨345497, by rfl⟩ : syracuseStep 1842653 = 690995) (by norm_num)
theorem B1555949 : Blo 1228432 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B1842677 : Blo 1228432 1842677 := bbase (se 5 (by rfl) ⟨86375, by rfl⟩ : syracuseStep 1842677 = 172751) (by norm_num)
theorem B2334197 : Blo 1228432 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1383925 : Blo 1228432 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B3112445 : Blo 1228432 3112445 := bbase (se 3 (by rfl) ⟨583583, by rfl⟩ : syracuseStep 3112445 = 1167167) (by norm_num)
theorem B2768381 : Blo 1228432 2768381 := bbase (se 3 (by rfl) ⟨519071, by rfl⟩ : syracuseStep 2768381 = 1038143) (by norm_num)
theorem B4554245 : Blo 1228432 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B1842701 : Blo 1228432 1842701 := bbase (se 3 (by rfl) ⟨345506, by rfl⟩ : syracuseStep 1842701 = 691013) (by norm_num)
theorem B1383961 : Blo 1228432 1383961 := bbase (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) (by norm_num)
theorem B1842725 : Blo 1228432 1842725 := bbase (se 4 (by rfl) ⟨172755, by rfl⟩ : syracuseStep 1842725 = 345511) (by norm_num)
theorem B1556005 : Blo 1228432 1556005 := bbase (se 4 (by rfl) ⟨145875, by rfl⟩ : syracuseStep 1556005 = 291751) (by norm_num)
theorem B10649141 : Blo 1228432 10649141 := bbase (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) (by norm_num)
theorem B1842749 : Blo 1228432 1842749 := bbase (se 3 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 1842749 = 691031) (by norm_num)
theorem B1383997 : Blo 1228432 1383997 := bbase (se 3 (by rfl) ⟨259499, by rfl⟩ : syracuseStep 1383997 = 518999) (by norm_num)
theorem B2768453 : Blo 1228432 2768453 := bbase (se 4 (by rfl) ⟨259542, by rfl⟩ : syracuseStep 2768453 = 519085) (by norm_num)
theorem B1842773 : Blo 1228432 1842773 := bbase (se 8 (by rfl) ⟨10797, by rfl⟩ : syracuseStep 1842773 = 21595) (by norm_num)
theorem B1384033 : Blo 1228432 1384033 := bbase (se 2 (by rfl) ⟨519012, by rfl⟩ : syracuseStep 1384033 = 1038025) (by norm_num)
theorem B1842797 : Blo 1228432 1842797 := bbase (se 3 (by rfl) ⟨345524, by rfl⟩ : syracuseStep 1842797 = 691049) (by norm_num)
theorem B5987957 : Blo 1228432 5987957 := bbase (se 5 (by rfl) ⟨280685, by rfl⟩ : syracuseStep 5987957 = 561371) (by norm_num)
theorem B1842821 : Blo 1228432 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B1556101 : Blo 1228432 1556101 := bbase (se 4 (by rfl) ⟨145884, by rfl⟩ : syracuseStep 1556101 = 291769) (by norm_num)
theorem B1384069 : Blo 1228432 1384069 := bbase (se 4 (by rfl) ⟨129756, by rfl⟩ : syracuseStep 1384069 = 259513) (by norm_num)
theorem B3325573 : Blo 1228432 3325573 := bbase (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) (by norm_num)
theorem B2334349 : Blo 1228432 2334349 := bbase (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) (by norm_num)
theorem B8412821 : Blo 1228432 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B1842845 : Blo 1228432 1842845 := bbase (se 3 (by rfl) ⟨345533, by rfl⟩ : syracuseStep 1842845 = 691067) (by norm_num)
theorem B1384105 : Blo 1228432 1384105 := bbase (se 2 (by rfl) ⟨519039, by rfl⟩ : syracuseStep 1384105 = 1038079) (by norm_num)
theorem B1842869 : Blo 1228432 1842869 := bbase (se 5 (by rfl) ⟨86384, by rfl⟩ : syracuseStep 1842869 = 172769) (by norm_num)
theorem B4669109 : Blo 1228432 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B1842893 : Blo 1228432 1842893 := bbase (se 3 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 1842893 = 691085) (by norm_num)
theorem B1384141 : Blo 1228432 1384141 := bbase (se 3 (by rfl) ⟨259526, by rfl⟩ : syracuseStep 1384141 = 519053) (by norm_num)
theorem B1842917 : Blo 1228432 1842917 := bbase (se 4 (by rfl) ⟨172773, by rfl⟩ : syracuseStep 1842917 = 345547) (by norm_num)
theorem B1384177 : Blo 1228432 1384177 := bbase (se 2 (by rfl) ⟨519066, by rfl⟩ : syracuseStep 1384177 = 1038133) (by norm_num)
theorem B1842941 : Blo 1228432 1842941 := bbase (se 3 (by rfl) ⟨345551, by rfl⟩ : syracuseStep 1842941 = 691103) (by norm_num)
theorem B1842965 : Blo 1228432 1842965 := bbase (se 6 (by rfl) ⟨43194, by rfl⟩ : syracuseStep 1842965 = 86389) (by norm_num)
theorem B1384213 : Blo 1228432 1384213 := bbase (se 6 (by rfl) ⟨32442, by rfl⟩ : syracuseStep 1384213 = 64885) (by norm_num)
theorem B1842989 : Blo 1228432 1842989 := bbase (se 3 (by rfl) ⟨345560, by rfl⟩ : syracuseStep 1842989 = 691121) (by norm_num)
theorem B1556273 : Blo 1228432 1556273 := bbase (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) (by norm_num)
theorem B7094069 : Blo 1228432 7094069 := bbase (se 5 (by rfl) ⟨332534, by rfl⟩ : syracuseStep 7094069 = 665069) (by norm_num)
theorem B1843013 : Blo 1228432 1843013 := bbase (se 4 (by rfl) ⟨172782, by rfl⟩ : syracuseStep 1843013 = 345565) (by norm_num)
theorem B3112789 : Blo 1228432 3112789 := bbase (se 9 (by rfl) ⟨9119, by rfl⟩ : syracuseStep 3112789 = 18239) (by norm_num)
theorem B1843037 : Blo 1228432 1843037 := bbase (se 3 (by rfl) ⟨345569, by rfl⟩ : syracuseStep 1843037 = 691139) (by norm_num)
theorem B1556329 : Blo 1228432 1556329 := bbase (se 2 (by rfl) ⟨583623, by rfl⟩ : syracuseStep 1556329 = 1167247) (by norm_num)
theorem B1843061 : Blo 1228432 1843061 := bbase (se 5 (by rfl) ⟨86393, by rfl⟩ : syracuseStep 1843061 = 172787) (by norm_num)
theorem B1843085 : Blo 1228432 1843085 := bbase (se 3 (by rfl) ⟨345578, by rfl⟩ : syracuseStep 1843085 = 691157) (by norm_num)
theorem B1843109 : Blo 1228432 1843109 := bbase (se 4 (by rfl) ⟨172791, by rfl⟩ : syracuseStep 1843109 = 345583) (by norm_num)
theorem B1843133 : Blo 1228432 1843133 := bbase (se 3 (by rfl) ⟨345587, by rfl⟩ : syracuseStep 1843133 = 691175) (by norm_num)
theorem B2334653 : Blo 1228432 2334653 := bbase (se 3 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 2334653 = 875495) (by norm_num)
theorem B3112901 : Blo 1228432 3112901 := bbase (se 4 (by rfl) ⟨291834, by rfl⟩ : syracuseStep 3112901 = 583669) (by norm_num)
theorem B1556425 : Blo 1228432 1556425 := bbase (se 2 (by rfl) ⟨583659, by rfl⟩ : syracuseStep 1556425 = 1167319) (by norm_num)
theorem B1843157 : Blo 1228432 1843157 := bbase (se 7 (by rfl) ⟨21599, by rfl⟩ : syracuseStep 1843157 = 43199) (by norm_num)
theorem B4669397 : Blo 1228432 4669397 := bbase (se 7 (by rfl) ⟨54719, by rfl⟩ : syracuseStep 4669397 = 109439) (by norm_num)
theorem B2736101 : Blo 1228432 2736101 := bbase (se 4 (by rfl) ⟨256509, by rfl⟩ : syracuseStep 2736101 = 513019) (by norm_num)
theorem B1843181 : Blo 1228432 1843181 := bbase (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) (by norm_num)
theorem B1228803 : Blo 1228432 1228803 := bstep (se 1 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 1228803 = 1843205) B1843205
theorem B11812877 : Blo 1228432 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B1843217 : Blo 1228432 1843217 := bstep (se 2 (by rfl) ⟨691206, by rfl⟩ : syracuseStep 1843217 = 1382413) B1382413
theorem B2334737 : Blo 1228432 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B1228819 : Blo 1228432 1228819 := bstep (se 1 (by rfl) ⟨921614, by rfl⟩ : syracuseStep 1228819 = 1843229) B1843229
theorem B1843235 : Blo 1228432 1843235 := bstep (se 1 (by rfl) ⟨1382426, by rfl⟩ : syracuseStep 1843235 = 2764853) B2764853
theorem B1228835 : Blo 1228432 1228835 := bstep (se 1 (by rfl) ⟨921626, by rfl⟩ : syracuseStep 1228835 = 1843253) B1843253
theorem B1228851 : Blo 1228432 1228851 := bstep (se 1 (by rfl) ⟨921638, by rfl⟩ : syracuseStep 1228851 = 1843277) B1843277
theorem B1843265 : Blo 1228432 1843265 := bstep (se 2 (by rfl) ⟨691224, by rfl⟩ : syracuseStep 1843265 = 1382449) B1382449
theorem B1228867 : Blo 1228432 1228867 := bstep (se 1 (by rfl) ⟨921650, by rfl⟩ : syracuseStep 1228867 = 1843301) B1843301
theorem B1400915 : Blo 1228432 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1843283 : Blo 1228432 1843283 := bstep (se 1 (by rfl) ⟨1382462, by rfl⟩ : syracuseStep 1843283 = 2764925) B2764925
theorem B1228883 : Blo 1228432 1228883 := bstep (se 1 (by rfl) ⟨921662, by rfl⟩ : syracuseStep 1228883 = 1843325) B1843325
theorem B1228899 : Blo 1228432 1228899 := bstep (se 1 (by rfl) ⟨921674, by rfl⟩ : syracuseStep 1228899 = 1843349) B1843349
theorem B1843313 : Blo 1228432 1843313 := bstep (se 2 (by rfl) ⟨691242, by rfl⟩ : syracuseStep 1843313 = 1382485) B1382485
theorem B1228915 : Blo 1228432 1228915 := bstep (se 1 (by rfl) ⟨921686, by rfl⟩ : syracuseStep 1228915 = 1843373) B1843373
theorem B1843331 : Blo 1228432 1843331 := bstep (se 1 (by rfl) ⟨1382498, by rfl⟩ : syracuseStep 1843331 = 2764997) B2764997
theorem B1228931 : Blo 1228432 1228931 := bstep (se 1 (by rfl) ⟨921698, by rfl⟩ : syracuseStep 1228931 = 1843397) B1843397
theorem B1228947 : Blo 1228432 1228947 := bstep (se 1 (by rfl) ⟨921710, by rfl⟩ : syracuseStep 1228947 = 1843421) B1843421
theorem B1843361 : Blo 1228432 1843361 := bstep (se 2 (by rfl) ⟨691260, by rfl⟩ : syracuseStep 1843361 = 1382521) B1382521
theorem B1228963 : Blo 1228432 1228963 := bstep (se 1 (by rfl) ⟨921722, by rfl⟩ : syracuseStep 1228963 = 1843445) B1843445
theorem B1843379 : Blo 1228432 1843379 := bstep (se 1 (by rfl) ⟨1382534, by rfl⟩ : syracuseStep 1843379 = 2765069) B2765069
theorem B1228979 : Blo 1228432 1228979 := bstep (se 1 (by rfl) ⟨921734, by rfl⟩ : syracuseStep 1228979 = 1843469) B1843469
theorem B1228995 : Blo 1228432 1228995 := bstep (se 1 (by rfl) ⟨921746, by rfl⟩ : syracuseStep 1228995 = 1843493) B1843493
theorem B1843409 : Blo 1228432 1843409 := bstep (se 2 (by rfl) ⟨691278, by rfl⟩ : syracuseStep 1843409 = 1382557) B1382557
theorem B1229011 : Blo 1228432 1229011 := bstep (se 1 (by rfl) ⟨921758, by rfl⟩ : syracuseStep 1229011 = 1843517) B1843517
theorem B1843427 : Blo 1228432 1843427 := bstep (se 1 (by rfl) ⟨1382570, by rfl⟩ : syracuseStep 1843427 = 2765141) B2765141
theorem B1229027 : Blo 1228432 1229027 := bstep (se 1 (by rfl) ⟨921770, by rfl⟩ : syracuseStep 1229027 = 1843541) B1843541
theorem B3498221 : Blo 1228432 3498221 := bstep (se 3 (by rfl) ⟨655916, by rfl⟩ : syracuseStep 3498221 = 1311833) B1311833
theorem B1229043 : Blo 1228432 1229043 := bstep (se 1 (by rfl) ⟨921782, by rfl⟩ : syracuseStep 1229043 = 1843565) B1843565
theorem B1843457 : Blo 1228432 1843457 := bstep (se 2 (by rfl) ⟨691296, by rfl⟩ : syracuseStep 1843457 = 1382593) B1382593
theorem B1229059 : Blo 1228432 1229059 := bstep (se 1 (by rfl) ⟨921794, by rfl⟩ : syracuseStep 1229059 = 1843589) B1843589
theorem B3940625 : Blo 1228432 3940625 := bstep (se 2 (by rfl) ⟨1477734, by rfl⟩ : syracuseStep 3940625 = 2955469) B2955469
theorem B1843475 : Blo 1228432 1843475 := bstep (se 1 (by rfl) ⟨1382606, by rfl⟩ : syracuseStep 1843475 = 2765213) B2765213
theorem B1229075 : Blo 1228432 1229075 := bstep (se 1 (by rfl) ⟨921806, by rfl⟩ : syracuseStep 1229075 = 1843613) B1843613
theorem B1229091 : Blo 1228432 1229091 := bstep (se 1 (by rfl) ⟨921818, by rfl⟩ : syracuseStep 1229091 = 1843637) B1843637
theorem B1843505 : Blo 1228432 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B1229107 : Blo 1228432 1229107 := bstep (se 1 (by rfl) ⟨921830, by rfl⟩ : syracuseStep 1229107 = 1843661) B1843661
theorem B1843523 : Blo 1228432 1843523 := bstep (se 1 (by rfl) ⟨1382642, by rfl⟩ : syracuseStep 1843523 = 2765285) B2765285
theorem B1229123 : Blo 1228432 1229123 := bstep (se 1 (by rfl) ⟨921842, by rfl⟩ : syracuseStep 1229123 = 1843685) B1843685
theorem B1229139 : Blo 1228432 1229139 := bstep (se 1 (by rfl) ⟨921854, by rfl⟩ : syracuseStep 1229139 = 1843709) B1843709
theorem B1843553 : Blo 1228432 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B1229155 : Blo 1228432 1229155 := bstep (se 1 (by rfl) ⟨921866, by rfl⟩ : syracuseStep 1229155 = 1843733) B1843733
theorem B1843571 : Blo 1228432 1843571 := bstep (se 1 (by rfl) ⟨1382678, by rfl⟩ : syracuseStep 1843571 = 2765357) B2765357
theorem B1229171 : Blo 1228432 1229171 := bstep (se 1 (by rfl) ⟨921878, by rfl⟩ : syracuseStep 1229171 = 1843757) B1843757
theorem B1229187 : Blo 1228432 1229187 := bstep (se 1 (by rfl) ⟨921890, by rfl⟩ : syracuseStep 1229187 = 1843781) B1843781
theorem B1843601 : Blo 1228432 1843601 := bstep (se 2 (by rfl) ⟨691350, by rfl⟩ : syracuseStep 1843601 = 1382701) B1382701
theorem B1229203 : Blo 1228432 1229203 := bstep (se 1 (by rfl) ⟨921902, by rfl⟩ : syracuseStep 1229203 = 1843805) B1843805
theorem B3498403 : Blo 1228432 3498403 := bstep (se 1 (by rfl) ⟨2623802, by rfl⟩ : syracuseStep 3498403 = 5247605) B5247605
theorem B1843619 : Blo 1228432 1843619 := bstep (se 1 (by rfl) ⟨1382714, by rfl⟩ : syracuseStep 1843619 = 2765429) B2765429
theorem B1229219 : Blo 1228432 1229219 := bstep (se 1 (by rfl) ⟨921914, by rfl⟩ : syracuseStep 1229219 = 1843829) B1843829
theorem B2335139 : Blo 1228432 2335139 := bstep (se 1 (by rfl) ⟨1751354, by rfl⟩ : syracuseStep 2335139 = 3502709) B3502709
theorem B1229235 : Blo 1228432 1229235 := bstep (se 1 (by rfl) ⟨921926, by rfl⟩ : syracuseStep 1229235 = 1843853) B1843853
theorem B1843649 : Blo 1228432 1843649 := bstep (se 2 (by rfl) ⟨691368, by rfl⟩ : syracuseStep 1843649 = 1382737) B1382737
theorem B1229251 : Blo 1228432 1229251 := bstep (se 1 (by rfl) ⟨921938, by rfl⟩ : syracuseStep 1229251 = 1843877) B1843877
theorem B1843667 : Blo 1228432 1843667 := bstep (se 1 (by rfl) ⟨1382750, by rfl⟩ : syracuseStep 1843667 = 2765501) B2765501
theorem B1229267 : Blo 1228432 1229267 := bstep (se 1 (by rfl) ⟨921950, by rfl⟩ : syracuseStep 1229267 = 1843901) B1843901
theorem B1229283 : Blo 1228432 1229283 := bstep (se 1 (by rfl) ⟨921962, by rfl⟩ : syracuseStep 1229283 = 1843925) B1843925
theorem B2073073 : Blo 1228432 2073073 := bstep (se 2 (by rfl) ⟨777402, by rfl⟩ : syracuseStep 2073073 = 1554805) B1554805
theorem B1843697 : Blo 1228432 1843697 := bstep (se 2 (by rfl) ⟨691386, by rfl⟩ : syracuseStep 1843697 = 1382773) B1382773
theorem B1229299 : Blo 1228432 1229299 := bstep (se 1 (by rfl) ⟨921974, by rfl⟩ : syracuseStep 1229299 = 1843949) B1843949
theorem B1843715 : Blo 1228432 1843715 := bstep (se 1 (by rfl) ⟨1382786, by rfl⟩ : syracuseStep 1843715 = 2765573) B2765573
theorem B1229315 : Blo 1228432 1229315 := bstep (se 1 (by rfl) ⟨921986, by rfl⟩ : syracuseStep 1229315 = 1843973) B1843973
theorem B2073107 : Blo 1228432 2073107 := bstep (se 1 (by rfl) ⟨1554830, by rfl⟩ : syracuseStep 2073107 = 3109661) B3109661
theorem B1229331 : Blo 1228432 1229331 := bstep (se 1 (by rfl) ⟨921998, by rfl⟩ : syracuseStep 1229331 = 1843997) B1843997
theorem B1843745 : Blo 1228432 1843745 := bstep (se 2 (by rfl) ⟨691404, by rfl⟩ : syracuseStep 1843745 = 1382809) B1382809
theorem B1229347 : Blo 1228432 1229347 := bstep (se 1 (by rfl) ⟨922010, by rfl⟩ : syracuseStep 1229347 = 1844021) B1844021
theorem B1843763 : Blo 1228432 1843763 := bstep (se 1 (by rfl) ⟨1382822, by rfl⟩ : syracuseStep 1843763 = 2765645) B2765645
theorem B1229363 : Blo 1228432 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B1229379 : Blo 1228432 1229379 := bstep (se 1 (by rfl) ⟨922034, by rfl⟩ : syracuseStep 1229379 = 1844069) B1844069
theorem B9339461 : Blo 1228432 9339461 := bstep (se 4 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 9339461 = 1751149) B1751149
theorem B1843793 : Blo 1228432 1843793 := bstep (se 2 (by rfl) ⟨691422, by rfl⟩ : syracuseStep 1843793 = 1382845) B1382845
theorem B1229395 : Blo 1228432 1229395 := bstep (se 1 (by rfl) ⟨922046, by rfl⟩ : syracuseStep 1229395 = 1844093) B1844093
theorem B1843811 : Blo 1228432 1843811 := bstep (se 1 (by rfl) ⟨1382858, by rfl⟩ : syracuseStep 1843811 = 2765717) B2765717
theorem B1229411 : Blo 1228432 1229411 := bstep (se 1 (by rfl) ⟨922058, by rfl⟩ : syracuseStep 1229411 = 1844117) B1844117
theorem B1229427 : Blo 1228432 1229427 := bstep (se 1 (by rfl) ⟨922070, by rfl⟩ : syracuseStep 1229427 = 1844141) B1844141
theorem B1843841 : Blo 1228432 1843841 := bstep (se 2 (by rfl) ⟨691440, by rfl⟩ : syracuseStep 1843841 = 1382881) B1382881
theorem B1229443 : Blo 1228432 1229443 := bstep (se 1 (by rfl) ⟨922082, by rfl⟩ : syracuseStep 1229443 = 1844165) B1844165
theorem B2073235 : Blo 1228432 2073235 := bstep (se 1 (by rfl) ⟨1554926, by rfl⟩ : syracuseStep 2073235 = 3109853) B3109853
theorem B1843859 : Blo 1228432 1843859 := bstep (se 1 (by rfl) ⟨1382894, by rfl⟩ : syracuseStep 1843859 = 2765789) B2765789
theorem B1229459 : Blo 1228432 1229459 := bstep (se 1 (by rfl) ⟨922094, by rfl⟩ : syracuseStep 1229459 = 1844189) B1844189
theorem B1557139 : Blo 1228432 1557139 := bstep (se 1 (by rfl) ⟨1167854, by rfl⟩ : syracuseStep 1557139 = 2335709) B2335709
theorem B1229475 : Blo 1228432 1229475 := bstep (se 1 (by rfl) ⟨922106, by rfl⟩ : syracuseStep 1229475 = 1844213) B1844213
theorem B1843889 : Blo 1228432 1843889 := bstep (se 2 (by rfl) ⟨691458, by rfl⟩ : syracuseStep 1843889 = 1382917) B1382917
theorem B1229491 : Blo 1228432 1229491 := bstep (se 1 (by rfl) ⟨922118, by rfl⟩ : syracuseStep 1229491 = 1844237) B1844237
theorem B1843907 : Blo 1228432 1843907 := bstep (se 1 (by rfl) ⟨1382930, by rfl⟩ : syracuseStep 1843907 = 2765861) B2765861
theorem B1229507 : Blo 1228432 1229507 := bstep (se 1 (by rfl) ⟨922130, by rfl⟩ : syracuseStep 1229507 = 1844261) B1844261
theorem B1229523 : Blo 1228432 1229523 := bstep (se 1 (by rfl) ⟨922142, by rfl⟩ : syracuseStep 1229523 = 1844285) B1844285
theorem B53207765 : Blo 1228432 53207765 := bstep (se 7 (by rfl) ⟨623528, by rfl⟩ : syracuseStep 53207765 = 1247057) B1247057
theorem B1843937 : Blo 1228432 1843937 := bstep (se 2 (by rfl) ⟨691476, by rfl⟩ : syracuseStep 1843937 = 1382953) B1382953
theorem B6824675 : Blo 1228432 6824675 := bstep (se 1 (by rfl) ⟨5118506, by rfl⟩ : syracuseStep 6824675 = 10237013) B10237013
theorem B1229539 : Blo 1228432 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B5989091 : Blo 1228432 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B1843955 : Blo 1228432 1843955 := bstep (se 1 (by rfl) ⟨1382966, by rfl⟩ : syracuseStep 1843955 = 2765933) B2765933
theorem B1229555 : Blo 1228432 1229555 := bstep (se 1 (by rfl) ⟨922166, by rfl⟩ : syracuseStep 1229555 = 1844333) B1844333
theorem B1557235 : Blo 1228432 1557235 := bstep (se 1 (by rfl) ⟨1167926, by rfl⟩ : syracuseStep 1557235 = 2335853) B2335853
theorem B1229571 : Blo 1228432 1229571 := bstep (se 1 (by rfl) ⟨922178, by rfl⟩ : syracuseStep 1229571 = 1844357) B1844357
theorem B1843985 : Blo 1228432 1843985 := bstep (se 2 (by rfl) ⟨691494, by rfl⟩ : syracuseStep 1843985 = 1382989) B1382989
theorem B1229587 : Blo 1228432 1229587 := bstep (se 1 (by rfl) ⟨922190, by rfl⟩ : syracuseStep 1229587 = 1844381) B1844381
theorem B2073377 : Blo 1228432 2073377 := bstep (se 2 (by rfl) ⟨777516, by rfl⟩ : syracuseStep 2073377 = 1555033) B1555033
theorem B1844003 : Blo 1228432 1844003 := bstep (se 1 (by rfl) ⟨1383002, by rfl⟩ : syracuseStep 1844003 = 2766005) B2766005
theorem B1229603 : Blo 1228432 1229603 := bstep (se 1 (by rfl) ⟨922202, by rfl⟩ : syracuseStep 1229603 = 1844405) B1844405
theorem B1229619 : Blo 1228432 1229619 := bstep (se 1 (by rfl) ⟨922214, by rfl⟩ : syracuseStep 1229619 = 1844429) B1844429
theorem B1844033 : Blo 1228432 1844033 := bstep (se 2 (by rfl) ⟨691512, by rfl⟩ : syracuseStep 1844033 = 1383025) B1383025
theorem B1229635 : Blo 1228432 1229635 := bstep (se 1 (by rfl) ⟨922226, by rfl⟩ : syracuseStep 1229635 = 1844453) B1844453
theorem B5604173 : Blo 1228432 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B1844051 : Blo 1228432 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B1229651 : Blo 1228432 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B1229667 : Blo 1228432 1229667 := bstep (se 1 (by rfl) ⟨922250, by rfl⟩ : syracuseStep 1229667 = 1844501) B1844501
theorem B1844081 : Blo 1228432 1844081 := bstep (se 2 (by rfl) ⟨691530, by rfl⟩ : syracuseStep 1844081 = 1383061) B1383061
theorem B1229683 : Blo 1228432 1229683 := bstep (se 1 (by rfl) ⟨922262, by rfl⟩ : syracuseStep 1229683 = 1844525) B1844525
theorem B1844099 : Blo 1228432 1844099 := bstep (se 1 (by rfl) ⟨1383074, by rfl⟩ : syracuseStep 1844099 = 2766149) B2766149
theorem B1229699 : Blo 1228432 1229699 := bstep (se 1 (by rfl) ⟨922274, by rfl⟩ : syracuseStep 1229699 = 1844549) B1844549
theorem B151397261 : Blo 1228432 151397261 := bstep (se 3 (by rfl) ⟨28386986, by rfl⟩ : syracuseStep 151397261 = 56773973) B56773973
theorem B4146065 : Blo 1228432 4146065 := bstep (se 2 (by rfl) ⟨1554774, by rfl⟩ : syracuseStep 4146065 = 3109549) B3109549
theorem B1868689 : Blo 1228432 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1229715 : Blo 1228432 1229715 := bstep (se 1 (by rfl) ⟨922286, by rfl⟩ : syracuseStep 1229715 = 1844573) B1844573
theorem B3113873 : Blo 1228432 3113873 := bstep (se 2 (by rfl) ⟨1167702, by rfl⟩ : syracuseStep 3113873 = 2335405) B2335405
theorem B2073505 : Blo 1228432 2073505 := bstep (se 2 (by rfl) ⟨777564, by rfl⟩ : syracuseStep 2073505 = 1555129) B1555129
theorem B1844129 : Blo 1228432 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B1229731 : Blo 1228432 1229731 := bstep (se 1 (by rfl) ⟨922298, by rfl⟩ : syracuseStep 1229731 = 1844597) B1844597
theorem B1844147 : Blo 1228432 1844147 := bstep (se 1 (by rfl) ⟨1383110, by rfl⟩ : syracuseStep 1844147 = 2766221) B2766221
theorem B1229747 : Blo 1228432 1229747 := bstep (se 1 (by rfl) ⟨922310, by rfl⟩ : syracuseStep 1229747 = 1844621) B1844621
theorem B2073539 : Blo 1228432 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B1229763 : Blo 1228432 1229763 := bstep (se 1 (by rfl) ⟨922322, by rfl⟩ : syracuseStep 1229763 = 1844645) B1844645
theorem B22438853 : Blo 1228432 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B3113923 : Blo 1228432 3113923 := bstep (se 1 (by rfl) ⟨2335442, by rfl⟩ : syracuseStep 3113923 = 4670885) B4670885
theorem B1844177 : Blo 1228432 1844177 := bstep (se 2 (by rfl) ⟨691566, by rfl⟩ : syracuseStep 1844177 = 1383133) B1383133
theorem B1229779 : Blo 1228432 1229779 := bstep (se 1 (by rfl) ⟨922334, by rfl⟩ : syracuseStep 1229779 = 1844669) B1844669
theorem B8979427 : Blo 1228432 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B1844195 : Blo 1228432 1844195 := bstep (se 1 (by rfl) ⟨1383146, by rfl⟩ : syracuseStep 1844195 = 2766293) B2766293
theorem B1229795 : Blo 1228432 1229795 := bstep (se 1 (by rfl) ⟨922346, by rfl⟩ : syracuseStep 1229795 = 1844693) B1844693
theorem B1229811 : Blo 1228432 1229811 := bstep (se 1 (by rfl) ⟨922358, by rfl⟩ : syracuseStep 1229811 = 1844717) B1844717
theorem B1844225 : Blo 1228432 1844225 := bstep (se 2 (by rfl) ⟨691584, by rfl⟩ : syracuseStep 1844225 = 1383169) B1383169
theorem B1229827 : Blo 1228432 1229827 := bstep (se 1 (by rfl) ⟨922370, by rfl⟩ : syracuseStep 1229827 = 1844741) B1844741
theorem B1844243 : Blo 1228432 1844243 := bstep (se 1 (by rfl) ⟨1383182, by rfl⟩ : syracuseStep 1844243 = 2766365) B2766365
theorem B1229843 : Blo 1228432 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B1229859 : Blo 1228432 1229859 := bstep (se 1 (by rfl) ⟨922394, by rfl⟩ : syracuseStep 1229859 = 1844789) B1844789
theorem B4432931 : Blo 1228432 4432931 := bstep (se 1 (by rfl) ⟨3324698, by rfl⟩ : syracuseStep 4432931 = 6649397) B6649397
theorem B1844273 : Blo 1228432 1844273 := bstep (se 2 (by rfl) ⟨691602, by rfl⟩ : syracuseStep 1844273 = 1383205) B1383205
theorem B1229875 : Blo 1228432 1229875 := bstep (se 1 (by rfl) ⟨922406, by rfl⟩ : syracuseStep 1229875 = 1844813) B1844813
theorem B2073667 : Blo 1228432 2073667 := bstep (se 1 (by rfl) ⟨1555250, by rfl⟩ : syracuseStep 2073667 = 3110501) B3110501
theorem B1844291 : Blo 1228432 1844291 := bstep (se 1 (by rfl) ⟨1383218, by rfl⟩ : syracuseStep 1844291 = 2766437) B2766437
theorem B11207749 : Blo 1228432 11207749 := bstep (se 4 (by rfl) ⟨1050726, by rfl⟩ : syracuseStep 11207749 = 2101453) B2101453
theorem B1229891 : Blo 1228432 1229891 := bstep (se 1 (by rfl) ⟨922418, by rfl⟩ : syracuseStep 1229891 = 1844837) B1844837
theorem B3114065 : Blo 1228432 3114065 := bstep (se 2 (by rfl) ⟨1167774, by rfl⟩ : syracuseStep 3114065 = 2335549) B2335549
theorem B1262675 : Blo 1228432 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B1229907 : Blo 1228432 1229907 := bstep (se 1 (by rfl) ⟨922430, by rfl⟩ : syracuseStep 1229907 = 1844861) B1844861
theorem B1844321 : Blo 1228432 1844321 := bstep (se 2 (by rfl) ⟨691620, by rfl⟩ : syracuseStep 1844321 = 1383241) B1383241
theorem B1229923 : Blo 1228432 1229923 := bstep (se 1 (by rfl) ⟨922442, by rfl⟩ : syracuseStep 1229923 = 1844885) B1844885
theorem B1844339 : Blo 1228432 1844339 := bstep (se 1 (by rfl) ⟨1383254, by rfl⟩ : syracuseStep 1844339 = 2766509) B2766509
theorem B1229939 : Blo 1228432 1229939 := bstep (se 1 (by rfl) ⟨922454, by rfl⟩ : syracuseStep 1229939 = 1844909) B1844909
theorem B3155075 : Blo 1228432 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B1229955 : Blo 1228432 1229955 := bstep (se 1 (by rfl) ⟨922466, by rfl⟩ : syracuseStep 1229955 = 1844933) B1844933
theorem B7005325 : Blo 1228432 7005325 := bstep (se 3 (by rfl) ⟨1313498, by rfl⟩ : syracuseStep 7005325 = 2626997) B2626997
theorem B1844369 : Blo 1228432 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B1229971 : Blo 1228432 1229971 := bstep (se 1 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 1229971 = 1844957) B1844957
theorem B1844387 : Blo 1228432 1844387 := bstep (se 1 (by rfl) ⟨1383290, by rfl⟩ : syracuseStep 1844387 = 2766581) B2766581
theorem B1229987 : Blo 1228432 1229987 := bstep (se 1 (by rfl) ⟨922490, by rfl⟩ : syracuseStep 1229987 = 1844981) B1844981
theorem B1311923 : Blo 1228432 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B1230003 : Blo 1228432 1230003 := bstep (se 1 (by rfl) ⟨922502, by rfl⟩ : syracuseStep 1230003 = 1845005) B1845005
theorem B1844417 : Blo 1228432 1844417 := bstep (se 2 (by rfl) ⟨691656, by rfl⟩ : syracuseStep 1844417 = 1383313) B1383313
theorem B1230019 : Blo 1228432 1230019 := bstep (se 1 (by rfl) ⟨922514, by rfl⟩ : syracuseStep 1230019 = 1845029) B1845029
theorem B2073809 : Blo 1228432 2073809 := bstep (se 2 (by rfl) ⟨777678, by rfl⟩ : syracuseStep 2073809 = 1555357) B1555357
theorem B1844435 : Blo 1228432 1844435 := bstep (se 1 (by rfl) ⟨1383326, by rfl⟩ : syracuseStep 1844435 = 2766653) B2766653
theorem B1230035 : Blo 1228432 1230035 := bstep (se 1 (by rfl) ⟨922526, by rfl⟩ : syracuseStep 1230035 = 1845053) B1845053
theorem B1230051 : Blo 1228432 1230051 := bstep (se 1 (by rfl) ⟨922538, by rfl⟩ : syracuseStep 1230051 = 1845077) B1845077
theorem B1844465 : Blo 1228432 1844465 := bstep (se 2 (by rfl) ⟨691674, by rfl⟩ : syracuseStep 1844465 = 1383349) B1383349
theorem B1230067 : Blo 1228432 1230067 := bstep (se 1 (by rfl) ⟨922550, by rfl⟩ : syracuseStep 1230067 = 1845101) B1845101
theorem B1844483 : Blo 1228432 1844483 := bstep (se 1 (by rfl) ⟨1383362, by rfl⟩ : syracuseStep 1844483 = 2766725) B2766725
theorem B1230083 : Blo 1228432 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B1230099 : Blo 1228432 1230099 := bstep (se 1 (by rfl) ⟨922574, by rfl⟩ : syracuseStep 1230099 = 1845149) B1845149
theorem B1844513 : Blo 1228432 1844513 := bstep (se 2 (by rfl) ⟨691692, by rfl⟩ : syracuseStep 1844513 = 1383385) B1383385
theorem B1230115 : Blo 1228432 1230115 := bstep (se 1 (by rfl) ⟨922586, by rfl⟩ : syracuseStep 1230115 = 1845173) B1845173
theorem B1844531 : Blo 1228432 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B1230131 : Blo 1228432 1230131 := bstep (se 1 (by rfl) ⟨922598, by rfl⟩ : syracuseStep 1230131 = 1845197) B1845197
theorem B1230147 : Blo 1228432 1230147 := bstep (se 1 (by rfl) ⟨922610, by rfl⟩ : syracuseStep 1230147 = 1845221) B1845221
theorem B2073937 : Blo 1228432 2073937 := bstep (se 2 (by rfl) ⟨777726, by rfl⟩ : syracuseStep 2073937 = 1555453) B1555453
theorem B1844561 : Blo 1228432 1844561 := bstep (se 2 (by rfl) ⟨691710, by rfl⟩ : syracuseStep 1844561 = 1383421) B1383421
theorem B1230163 : Blo 1228432 1230163 := bstep (se 1 (by rfl) ⟨922622, by rfl⟩ : syracuseStep 1230163 = 1845245) B1845245
theorem B1844579 : Blo 1228432 1844579 := bstep (se 1 (by rfl) ⟨1383434, by rfl⟩ : syracuseStep 1844579 = 2766869) B2766869
theorem B1230179 : Blo 1228432 1230179 := bstep (se 1 (by rfl) ⟨922634, by rfl⟩ : syracuseStep 1230179 = 1845269) B1845269
theorem B2073971 : Blo 1228432 2073971 := bstep (se 1 (by rfl) ⟨1555478, by rfl⟩ : syracuseStep 2073971 = 3110957) B3110957
theorem B1230195 : Blo 1228432 1230195 := bstep (se 1 (by rfl) ⟨922646, by rfl⟩ : syracuseStep 1230195 = 1845293) B1845293
theorem B1844609 : Blo 1228432 1844609 := bstep (se 2 (by rfl) ⟨691728, by rfl⟩ : syracuseStep 1844609 = 1383457) B1383457
theorem B1230211 : Blo 1228432 1230211 := bstep (se 1 (by rfl) ⟨922658, by rfl⟩ : syracuseStep 1230211 = 1845317) B1845317
theorem B1844627 : Blo 1228432 1844627 := bstep (se 1 (by rfl) ⟨1383470, by rfl⟩ : syracuseStep 1844627 = 2766941) B2766941
theorem B1230227 : Blo 1228432 1230227 := bstep (se 1 (by rfl) ⟨922670, by rfl⟩ : syracuseStep 1230227 = 1845341) B1845341
theorem B1230243 : Blo 1228432 1230243 := bstep (se 1 (by rfl) ⟨922682, by rfl⟩ : syracuseStep 1230243 = 1845365) B1845365
theorem B4146605 : Blo 1228432 4146605 := bstep (se 3 (by rfl) ⟨777488, by rfl⟩ : syracuseStep 4146605 = 1554977) B1554977
theorem B1844657 : Blo 1228432 1844657 := bstep (se 2 (by rfl) ⟨691746, by rfl⟩ : syracuseStep 1844657 = 1383493) B1383493
theorem B1230259 : Blo 1228432 1230259 := bstep (se 1 (by rfl) ⟨922694, by rfl⟩ : syracuseStep 1230259 = 1845389) B1845389
theorem B1844675 : Blo 1228432 1844675 := bstep (se 1 (by rfl) ⟨1383506, by rfl⟩ : syracuseStep 1844675 = 2767013) B2767013
theorem B1230275 : Blo 1228432 1230275 := bstep (se 1 (by rfl) ⟨922706, by rfl⟩ : syracuseStep 1230275 = 1845413) B1845413
theorem B1230291 : Blo 1228432 1230291 := bstep (se 1 (by rfl) ⟨922718, by rfl⟩ : syracuseStep 1230291 = 1845437) B1845437
theorem B1844705 : Blo 1228432 1844705 := bstep (se 2 (by rfl) ⟨691764, by rfl⟩ : syracuseStep 1844705 = 1383529) B1383529
theorem B4146659 : Blo 1228432 4146659 := bstep (se 1 (by rfl) ⟨3109994, by rfl⟩ : syracuseStep 4146659 = 6219989) B6219989
theorem B1230307 : Blo 1228432 1230307 := bstep (se 1 (by rfl) ⟨922730, by rfl⟩ : syracuseStep 1230307 = 1845461) B1845461
theorem B6227441 : Blo 1228432 6227441 := bstep (se 2 (by rfl) ⟨2335290, by rfl⟩ : syracuseStep 6227441 = 4670581) B4670581
theorem B2074099 : Blo 1228432 2074099 := bstep (se 1 (by rfl) ⟨1555574, by rfl⟩ : syracuseStep 2074099 = 3111149) B3111149
theorem B1844723 : Blo 1228432 1844723 := bstep (se 1 (by rfl) ⟨1383542, by rfl⟩ : syracuseStep 1844723 = 2767085) B2767085
theorem B1230323 : Blo 1228432 1230323 := bstep (se 1 (by rfl) ⟨922742, by rfl⟩ : syracuseStep 1230323 = 1845485) B1845485
theorem B1230339 : Blo 1228432 1230339 := bstep (se 1 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 1230339 = 1845509) B1845509
theorem B1844753 : Blo 1228432 1844753 := bstep (se 2 (by rfl) ⟨691782, by rfl⟩ : syracuseStep 1844753 = 1383565) B1383565
theorem B1230355 : Blo 1228432 1230355 := bstep (se 1 (by rfl) ⟨922766, by rfl⟩ : syracuseStep 1230355 = 1845533) B1845533
theorem B1844771 : Blo 1228432 1844771 := bstep (se 1 (by rfl) ⟨1383578, by rfl⟩ : syracuseStep 1844771 = 2767157) B2767157
theorem B1230371 : Blo 1228432 1230371 := bstep (se 1 (by rfl) ⟨922778, by rfl⟩ : syracuseStep 1230371 = 1845557) B1845557
theorem B1230387 : Blo 1228432 1230387 := bstep (se 1 (by rfl) ⟨922790, by rfl⟩ : syracuseStep 1230387 = 1845581) B1845581
theorem B1844801 : Blo 1228432 1844801 := bstep (se 2 (by rfl) ⟨691800, by rfl⟩ : syracuseStep 1844801 = 1383601) B1383601
theorem B1230403 : Blo 1228432 1230403 := bstep (se 1 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 1230403 = 1845605) B1845605
theorem B6219341 : Blo 1228432 6219341 := bstep (se 3 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 6219341 = 2332253) B2332253
theorem B4671053 : Blo 1228432 4671053 := bstep (se 3 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 4671053 = 1751645) B1751645
theorem B1844819 : Blo 1228432 1844819 := bstep (se 1 (by rfl) ⟨1383614, by rfl⟩ : syracuseStep 1844819 = 2767229) B2767229
theorem B1230419 : Blo 1228432 1230419 := bstep (se 1 (by rfl) ⟨922814, by rfl⟩ : syracuseStep 1230419 = 1845629) B1845629
theorem B1844849 : Blo 1228432 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B2074241 : Blo 1228432 2074241 := bstep (se 2 (by rfl) ⟨777840, by rfl⟩ : syracuseStep 2074241 = 1555681) B1555681
theorem B1844867 : Blo 1228432 1844867 := bstep (se 1 (by rfl) ⟨1383650, by rfl⟩ : syracuseStep 1844867 = 2767301) B2767301
theorem B1844897 : Blo 1228432 1844897 := bstep (se 2 (by rfl) ⟨691836, by rfl⟩ : syracuseStep 1844897 = 1383673) B1383673
theorem B1844915 : Blo 1228432 1844915 := bstep (se 1 (by rfl) ⟨1383686, by rfl⟩ : syracuseStep 1844915 = 2767373) B2767373
theorem B4261585 : Blo 1228432 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B1844945 : Blo 1228432 1844945 := bstep (se 2 (by rfl) ⟨691854, by rfl⟩ : syracuseStep 1844945 = 1383709) B1383709
theorem B1844963 : Blo 1228432 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B4146929 : Blo 1228432 4146929 := bstep (se 2 (by rfl) ⟨1555098, by rfl⟩ : syracuseStep 4146929 = 3110197) B3110197
theorem B2074369 : Blo 1228432 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B1844993 : Blo 1228432 1844993 := bstep (se 2 (by rfl) ⟨691872, by rfl⟩ : syracuseStep 1844993 = 1383745) B1383745
theorem B3499793 : Blo 1228432 3499793 := bstep (se 2 (by rfl) ⟨1312422, by rfl⟩ : syracuseStep 3499793 = 2624845) B2624845
theorem B1845011 : Blo 1228432 1845011 := bstep (se 1 (by rfl) ⟨1383758, by rfl⟩ : syracuseStep 1845011 = 2767517) B2767517
theorem B2074403 : Blo 1228432 2074403 := bstep (se 1 (by rfl) ⟨1555802, by rfl⟩ : syracuseStep 2074403 = 3111605) B3111605
theorem B1845041 : Blo 1228432 1845041 := bstep (se 2 (by rfl) ⟨691890, by rfl⟩ : syracuseStep 1845041 = 1383781) B1383781
theorem B1845059 : Blo 1228432 1845059 := bstep (se 1 (by rfl) ⟨1383794, by rfl⟩ : syracuseStep 1845059 = 2767589) B2767589
theorem B1845089 : Blo 1228432 1845089 := bstep (se 2 (by rfl) ⟨691908, by rfl⟩ : syracuseStep 1845089 = 1383817) B1383817
theorem B1845107 : Blo 1228432 1845107 := bstep (se 1 (by rfl) ⟨1383830, by rfl⟩ : syracuseStep 1845107 = 2767661) B2767661
theorem B1845137 : Blo 1228432 1845137 := bstep (se 2 (by rfl) ⟨691926, by rfl⟩ : syracuseStep 1845137 = 1383853) B1383853
theorem B2074531 : Blo 1228432 2074531 := bstep (se 1 (by rfl) ⟨1555898, by rfl⟩ : syracuseStep 2074531 = 3111797) B3111797
theorem B1845155 : Blo 1228432 1845155 := bstep (se 1 (by rfl) ⟨1383866, by rfl⟩ : syracuseStep 1845155 = 2767733) B2767733
theorem B1845185 : Blo 1228432 1845185 := bstep (se 2 (by rfl) ⟨691944, by rfl⟩ : syracuseStep 1845185 = 1383889) B1383889
theorem B1247171 : Blo 1228432 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B1845203 : Blo 1228432 1845203 := bstep (se 1 (by rfl) ⟨1383902, by rfl⟩ : syracuseStep 1845203 = 2767805) B2767805
theorem B1845233 : Blo 1228432 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B1402867 : Blo 1228432 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B1845251 : Blo 1228432 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B29919253 : Blo 1228432 29919253 := bstep (se 6 (by rfl) ⟨701232, by rfl⟩ : syracuseStep 29919253 = 1402465) B1402465
theorem B1845281 : Blo 1228432 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B2074673 : Blo 1228432 2074673 := bstep (se 2 (by rfl) ⟨778002, by rfl⟩ : syracuseStep 2074673 = 1556005) B1556005
theorem B1845299 : Blo 1228432 1845299 := bstep (se 1 (by rfl) ⟨1383974, by rfl⟩ : syracuseStep 1845299 = 2767949) B2767949
theorem B1845329 : Blo 1228432 1845329 := bstep (se 2 (by rfl) ⟨691998, by rfl⟩ : syracuseStep 1845329 = 1383997) B1383997
theorem B1845347 : Blo 1228432 1845347 := bstep (se 1 (by rfl) ⟨1384010, by rfl⟩ : syracuseStep 1845347 = 2768021) B2768021
theorem B4982897 : Blo 1228432 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B1845377 : Blo 1228432 1845377 := bstep (se 2 (by rfl) ⟨692016, by rfl⟩ : syracuseStep 1845377 = 1384033) B1384033
theorem B1968275 : Blo 1228432 1968275 := bstep (se 1 (by rfl) ⟨1476206, by rfl⟩ : syracuseStep 1968275 = 2952413) B2952413
theorem B1845395 : Blo 1228432 1845395 := bstep (se 1 (by rfl) ⟨1384046, by rfl⟩ : syracuseStep 1845395 = 2768093) B2768093
theorem B2074801 : Blo 1228432 2074801 := bstep (se 2 (by rfl) ⟨778050, by rfl⟩ : syracuseStep 2074801 = 1556101) B1556101
theorem B1845425 : Blo 1228432 1845425 := bstep (se 2 (by rfl) ⟨692034, by rfl⟩ : syracuseStep 1845425 = 1384069) B1384069
theorem B4434097 : Blo 1228432 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B1845443 : Blo 1228432 1845443 := bstep (se 1 (by rfl) ⟨1384082, by rfl⟩ : syracuseStep 1845443 = 2768165) B2768165
theorem B2074835 : Blo 1228432 2074835 := bstep (se 1 (by rfl) ⟨1556126, by rfl⟩ : syracuseStep 2074835 = 3112253) B3112253
theorem B1845473 : Blo 1228432 1845473 := bstep (se 2 (by rfl) ⟨692052, by rfl⟩ : syracuseStep 1845473 = 1384105) B1384105
theorem B1845491 : Blo 1228432 1845491 := bstep (se 1 (by rfl) ⟨1384118, by rfl⟩ : syracuseStep 1845491 = 2768237) B2768237
theorem B4147469 : Blo 1228432 4147469 := bstep (se 3 (by rfl) ⟨777650, by rfl⟩ : syracuseStep 4147469 = 1555301) B1555301
theorem B1845521 : Blo 1228432 1845521 := bstep (se 2 (by rfl) ⟨692070, by rfl⟩ : syracuseStep 1845521 = 1384141) B1384141
theorem B1968403 : Blo 1228432 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B4434211 : Blo 1228432 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1845539 : Blo 1228432 1845539 := bstep (se 1 (by rfl) ⟨1384154, by rfl⟩ : syracuseStep 1845539 = 2768309) B2768309
theorem B1845569 : Blo 1228432 1845569 := bstep (se 2 (by rfl) ⟨692088, by rfl⟩ : syracuseStep 1845569 = 1384177) B1384177
theorem B4147523 : Blo 1228432 4147523 := bstep (se 1 (by rfl) ⟨3110642, by rfl⟩ : syracuseStep 4147523 = 6221285) B6221285
theorem B1968467 : Blo 1228432 1968467 := bstep (se 1 (by rfl) ⟨1476350, by rfl⟩ : syracuseStep 1968467 = 2952701) B2952701
theorem B2074963 : Blo 1228432 2074963 := bstep (se 1 (by rfl) ⟨1556222, by rfl⟩ : syracuseStep 2074963 = 3112445) B3112445
theorem B1845587 : Blo 1228432 1845587 := bstep (se 1 (by rfl) ⟨1384190, by rfl⟩ : syracuseStep 1845587 = 2768381) B2768381
theorem B1845617 : Blo 1228432 1845617 := bstep (se 2 (by rfl) ⟨692106, by rfl⟩ : syracuseStep 1845617 = 1384213) B1384213
theorem B1845635 : Blo 1228432 1845635 := bstep (se 1 (by rfl) ⟨1384226, by rfl⟩ : syracuseStep 1845635 = 2768453) B2768453
theorem B2075105 : Blo 1228432 2075105 := bstep (se 2 (by rfl) ⟨778164, by rfl⟩ : syracuseStep 2075105 = 1556329) B1556329
theorem B4729379 : Blo 1228432 4729379 := bstep (se 1 (by rfl) ⟨3547034, by rfl⟩ : syracuseStep 4729379 = 7094069) B7094069
theorem B4147793 : Blo 1228432 4147793 := bstep (se 2 (by rfl) ⟨1555422, by rfl⟩ : syracuseStep 4147793 = 3110845) B3110845
theorem B2075233 : Blo 1228432 2075233 := bstep (se 2 (by rfl) ⟨778212, by rfl⟩ : syracuseStep 2075233 = 1556425) B1556425
theorem B1477235 : Blo 1228432 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B2075267 : Blo 1228432 2075267 := bstep (se 1 (by rfl) ⟨1556450, by rfl⟩ : syracuseStep 2075267 = 3112901) B3112901
theorem B2624195 : Blo 1228432 2624195 := bstep (se 1 (by rfl) ⟨1968146, by rfl⟩ : syracuseStep 2624195 = 3936293) B3936293
theorem B3500749 : Blo 1228432 3500749 := bstep (se 3 (by rfl) ⟨656390, by rfl⟩ : syracuseStep 3500749 = 1312781) B1312781
theorem B2075395 : Blo 1228432 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1968961 : Blo 1228432 1968961 := bstep (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) B1476721
theorem B6646627 : Blo 1228432 6646627 := bstep (se 1 (by rfl) ⟨4984970, by rfl⟩ : syracuseStep 6646627 = 9969941) B9969941
theorem B2075537 : Blo 1228432 2075537 := bstep (se 2 (by rfl) ⟨778326, by rfl⟩ : syracuseStep 2075537 = 1556653) B1556653
theorem B6228899 : Blo 1228432 6228899 := bstep (se 1 (by rfl) ⟨4671674, by rfl⟩ : syracuseStep 6228899 = 9343349) B9343349
theorem B3500977 : Blo 1228432 3500977 := bstep (se 2 (by rfl) ⟨1312866, by rfl⟩ : syracuseStep 3500977 = 2625733) B2625733
theorem B3738641 : Blo 1228432 3738641 := bstep (se 2 (by rfl) ⟨1401990, by rfl⟩ : syracuseStep 3738641 = 2803981) B2803981
theorem B2075665 : Blo 1228432 2075665 := bstep (se 2 (by rfl) ⟨778374, by rfl⟩ : syracuseStep 2075665 = 1556749) B1556749
theorem B2075699 : Blo 1228432 2075699 := bstep (se 1 (by rfl) ⟨1556774, by rfl⟩ : syracuseStep 2075699 = 3113549) B3113549
theorem B7007309 : Blo 1228432 7007309 := bstep (se 3 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 7007309 = 2627741) B2627741
theorem B3501137 : Blo 1228432 3501137 := bstep (se 2 (by rfl) ⟨1312926, by rfl⟩ : syracuseStep 3501137 = 2625853) B2625853
theorem B4148333 : Blo 1228432 4148333 := bstep (se 3 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 4148333 = 1555625) B1555625
theorem B1313939 : Blo 1228432 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B4148387 : Blo 1228432 4148387 := bstep (se 1 (by rfl) ⟨3111290, by rfl⟩ : syracuseStep 4148387 = 6222581) B6222581
theorem B2075827 : Blo 1228432 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B3501251 : Blo 1228432 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B2993425 : Blo 1228432 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B2075969 : Blo 1228432 2075969 := bstep (se 2 (by rfl) ⟨778488, by rfl⟩ : syracuseStep 2075969 = 1556977) B1556977
theorem B15748451 : Blo 1228432 15748451 := bstep (se 1 (by rfl) ⟨11811338, by rfl⟩ : syracuseStep 15748451 = 23622677) B23622677
theorem B9334115 : Blo 1228432 9334115 := bstep (se 1 (by rfl) ⟨7000586, by rfl⟩ : syracuseStep 9334115 = 14001173) B14001173
theorem B5254541 : Blo 1228432 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B2952625 : Blo 1228432 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B4148657 : Blo 1228432 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B5254577 : Blo 1228432 5254577 := bstep (se 2 (by rfl) ⟨1970466, by rfl⟩ : syracuseStep 5254577 = 3940933) B3940933
theorem B2076097 : Blo 1228432 2076097 := bstep (se 2 (by rfl) ⟨778536, by rfl⟩ : syracuseStep 2076097 = 1557073) B1557073
theorem B6999493 : Blo 1228432 6999493 := bstep (se 4 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 6999493 = 1312405) B1312405
theorem B2764241 : Blo 1228432 2764241 := bstep (se 2 (by rfl) ⟨1036590, by rfl⟩ : syracuseStep 2764241 = 2073181) B2073181
theorem B1969633 : Blo 1228432 1969633 := bstep (se 2 (by rfl) ⟨738612, by rfl⟩ : syracuseStep 1969633 = 1477225) B1477225
theorem B2764259 : Blo 1228432 2764259 := bstep (se 1 (by rfl) ⟨2073194, by rfl⟩ : syracuseStep 2764259 = 4146389) B4146389
theorem B2076131 : Blo 1228432 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B3739117 : Blo 1228432 3739117 := bstep (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) B1402169
theorem B3935729 : Blo 1228432 3935729 := bstep (se 2 (by rfl) ⟨1475898, by rfl⟩ : syracuseStep 3935729 = 2951797) B2951797
theorem B29888021 : Blo 1228432 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B2076259 : Blo 1228432 2076259 := bstep (se 1 (by rfl) ⟨1557194, by rfl⟩ : syracuseStep 2076259 = 3114389) B3114389
theorem B5607089 : Blo 1228432 5607089 := bstep (se 2 (by rfl) ⟨2102658, by rfl⟩ : syracuseStep 5607089 = 4205317) B4205317
theorem B7573189 : Blo 1228432 7573189 := bstep (se 4 (by rfl) ⟨709986, by rfl⟩ : syracuseStep 7573189 = 1419973) B1419973
theorem B2764529 : Blo 1228432 2764529 := bstep (se 2 (by rfl) ⟨1036698, by rfl⟩ : syracuseStep 2764529 = 2073397) B2073397
theorem B2764547 : Blo 1228432 2764547 := bstep (se 1 (by rfl) ⟨2073410, by rfl⟩ : syracuseStep 2764547 = 4146821) B4146821
theorem B2953027 : Blo 1228432 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B3936077 : Blo 1228432 3936077 := bstep (se 3 (by rfl) ⟨738014, by rfl⟩ : syracuseStep 3936077 = 1476029) B1476029
theorem B2625443 : Blo 1228432 2625443 := bstep (se 1 (by rfl) ⟨1969082, by rfl⟩ : syracuseStep 2625443 = 3938165) B3938165
theorem B4149197 : Blo 1228432 4149197 := bstep (se 3 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 4149197 = 1555949) B1555949
theorem B1683409 : Blo 1228432 1683409 := bstep (se 2 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 1683409 = 1262557) B1262557
theorem B4149251 : Blo 1228432 4149251 := bstep (se 1 (by rfl) ⟨3111938, by rfl⟩ : syracuseStep 4149251 = 6223877) B6223877
theorem B12144653 : Blo 1228432 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B2764817 : Blo 1228432 2764817 := bstep (se 2 (by rfl) ⟨1036806, by rfl⟩ : syracuseStep 2764817 = 2073613) B2073613
theorem B2764835 : Blo 1228432 2764835 := bstep (se 1 (by rfl) ⟨2073626, by rfl⟩ : syracuseStep 2764835 = 4147253) B4147253
theorem B11817029 : Blo 1228432 11817029 := bstep (se 4 (by rfl) ⟨1107846, by rfl⟩ : syracuseStep 11817029 = 2215693) B2215693
theorem B26587277 : Blo 1228432 26587277 := bstep (se 3 (by rfl) ⟨4985114, by rfl⟩ : syracuseStep 26587277 = 9970229) B9970229
theorem B3502253 : Blo 1228432 3502253 := bstep (se 3 (by rfl) ⟨656672, by rfl⟩ : syracuseStep 3502253 = 1313345) B1313345
theorem B4149521 : Blo 1228432 4149521 := bstep (se 2 (by rfl) ⟨1556070, by rfl⟩ : syracuseStep 4149521 = 3112141) B3112141
theorem B1749281 : Blo 1228432 1749281 := bstep (se 2 (by rfl) ⟨655980, by rfl⟩ : syracuseStep 1749281 = 1311961) B1311961
theorem B5247281 : Blo 1228432 5247281 := bstep (se 2 (by rfl) ⟨1967730, by rfl⟩ : syracuseStep 5247281 = 3935461) B3935461
theorem B2765105 : Blo 1228432 2765105 := bstep (se 2 (by rfl) ⟨1036914, by rfl⟩ : syracuseStep 2765105 = 2073829) B2073829
theorem B2765123 : Blo 1228432 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B3502435 : Blo 1228432 3502435 := bstep (se 1 (by rfl) ⟨2626826, by rfl⟩ : syracuseStep 3502435 = 5253653) B5253653
theorem B1749395 : Blo 1228432 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B6222257 : Blo 1228432 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B1749475 : Blo 1228432 1749475 := bstep (se 1 (by rfl) ⟨1312106, by rfl⟩ : syracuseStep 1749475 = 2624213) B2624213
theorem B2626033 : Blo 1228432 2626033 := bstep (se 2 (by rfl) ⟨984762, by rfl⟩ : syracuseStep 2626033 = 1969525) B1969525
theorem B3502595 : Blo 1228432 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B1970723 : Blo 1228432 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B2765393 : Blo 1228432 2765393 := bstep (se 2 (by rfl) ⟨1037022, by rfl⟩ : syracuseStep 2765393 = 2074045) B2074045
theorem B2765411 : Blo 1228432 2765411 := bstep (se 1 (by rfl) ⟨2074058, by rfl⟩ : syracuseStep 2765411 = 4148117) B4148117
theorem B8417969 : Blo 1228432 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B2102051 : Blo 1228432 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B4150061 : Blo 1228432 4150061 := bstep (se 3 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 4150061 = 1556273) B1556273
theorem B2954065 : Blo 1228432 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B4150115 : Blo 1228432 4150115 := bstep (se 1 (by rfl) ⟨3112586, by rfl⟩ : syracuseStep 4150115 = 6225173) B6225173
theorem B1577827 : Blo 1228432 1577827 := bstep (se 1 (by rfl) ⟨1183370, by rfl⟩ : syracuseStep 1577827 = 2366741) B2366741
theorem B2765681 : Blo 1228432 2765681 := bstep (se 2 (by rfl) ⟨1037130, by rfl⟩ : syracuseStep 2765681 = 2074261) B2074261
theorem B2765699 : Blo 1228432 2765699 := bstep (se 1 (by rfl) ⟨2074274, by rfl⟩ : syracuseStep 2765699 = 4148549) B4148549
theorem B3109873 : Blo 1228432 3109873 := bstep (se 2 (by rfl) ⟨1166202, by rfl⟩ : syracuseStep 3109873 = 2332405) B2332405
theorem B1750033 : Blo 1228432 1750033 := bstep (se 2 (by rfl) ⟨656262, by rfl⟩ : syracuseStep 1750033 = 1312525) B1312525
theorem B7099427 : Blo 1228432 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B5608547 : Blo 1228432 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B4666481 : Blo 1228432 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B4150385 : Blo 1228432 4150385 := bstep (se 2 (by rfl) ⟨1556394, by rfl⟩ : syracuseStep 4150385 = 3112789) B3112789
theorem B2765969 : Blo 1228432 2765969 := bstep (se 2 (by rfl) ⟨1037238, by rfl⟩ : syracuseStep 2765969 = 2074477) B2074477
theorem B2765987 : Blo 1228432 2765987 := bstep (se 1 (by rfl) ⟨2074490, by rfl⟩ : syracuseStep 2765987 = 4148981) B4148981
theorem B3110147 : Blo 1228432 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B7296269 : Blo 1228432 7296269 := bstep (se 3 (by rfl) ⟨1368050, by rfl⟩ : syracuseStep 7296269 = 2736101) B2736101
theorem B6313315 : Blo 1228432 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B7001477 : Blo 1228432 7001477 := bstep (se 4 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 7001477 = 1312777) B1312777
theorem B1660321 : Blo 1228432 1660321 := bstep (se 2 (by rfl) ⟨622620, by rfl⟩ : syracuseStep 1660321 = 1245241) B1245241
theorem B2766257 : Blo 1228432 2766257 := bstep (se 2 (by rfl) ⟨1037346, by rfl⟩ : syracuseStep 2766257 = 2074693) B2074693
theorem B3110339 : Blo 1228432 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B2766275 : Blo 1228432 2766275 := bstep (se 1 (by rfl) ⟨2074706, by rfl⟩ : syracuseStep 2766275 = 4149413) B4149413
theorem B3503665 : Blo 1228432 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B1496675 : Blo 1228432 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B3937933 : Blo 1228432 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B4150925 : Blo 1228432 4150925 := bstep (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) B1556597
theorem B1382035 : Blo 1228432 1382035 := bstep (se 1 (by rfl) ⟨1036526, by rfl⟩ : syracuseStep 1382035 = 2073053) B2073053
theorem B4150979 : Blo 1228432 4150979 := bstep (se 1 (by rfl) ⟨3113234, by rfl⟩ : syracuseStep 4150979 = 6226469) B6226469
theorem B2766545 : Blo 1228432 2766545 := bstep (se 2 (by rfl) ⟨1037454, by rfl⟩ : syracuseStep 2766545 = 2074909) B2074909
theorem B1750739 : Blo 1228432 1750739 := bstep (se 1 (by rfl) ⟨1313054, by rfl⟩ : syracuseStep 1750739 = 2626109) B2626109
theorem B2766563 : Blo 1228432 2766563 := bstep (se 1 (by rfl) ⟨2074922, by rfl⟩ : syracuseStep 2766563 = 4149845) B4149845
theorem B1382179 : Blo 1228432 1382179 := bstep (se 1 (by rfl) ⟨1036634, by rfl⟩ : syracuseStep 1382179 = 2073269) B2073269
theorem B2332451 : Blo 1228432 2332451 := bstep (se 1 (by rfl) ⟨1749338, by rfl⟩ : syracuseStep 2332451 = 3498677) B3498677
theorem B7477069 : Blo 1228432 7477069 := bstep (se 3 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 7477069 = 2803901) B2803901
theorem B6223715 : Blo 1228432 6223715 := bstep (se 1 (by rfl) ⟨4667786, by rfl⟩ : syracuseStep 6223715 = 9335573) B9335573
theorem B2840465 : Blo 1228432 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1660819 : Blo 1228432 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B1382323 : Blo 1228432 1382323 := bstep (se 1 (by rfl) ⟨1036742, by rfl⟩ : syracuseStep 1382323 = 2073485) B2073485
theorem B4151249 : Blo 1228432 4151249 := bstep (se 2 (by rfl) ⟨1556718, by rfl⟩ : syracuseStep 4151249 = 3113437) B3113437
theorem B2766833 : Blo 1228432 2766833 := bstep (se 2 (by rfl) ⟨1037562, by rfl⟩ : syracuseStep 2766833 = 2075125) B2075125
theorem B2766851 : Blo 1228432 2766851 := bstep (se 1 (by rfl) ⟨2075138, by rfl⟩ : syracuseStep 2766851 = 4150277) B4150277
theorem B2332739 : Blo 1228432 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B1382467 : Blo 1228432 1382467 := bstep (se 1 (by rfl) ⟨1036850, by rfl⟩ : syracuseStep 1382467 = 2073701) B2073701
theorem B6649933 : Blo 1228432 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B3324017 : Blo 1228432 3324017 := bstep (se 2 (by rfl) ⟨1246506, by rfl⟩ : syracuseStep 3324017 = 2493013) B2493013
theorem B2103425 : Blo 1228432 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B1382611 : Blo 1228432 1382611 := bstep (se 1 (by rfl) ⟨1036958, by rfl⟩ : syracuseStep 1382611 = 2073917) B2073917
theorem B2767121 : Blo 1228432 2767121 := bstep (se 2 (by rfl) ⟨1037670, by rfl⟩ : syracuseStep 2767121 = 2075341) B2075341
theorem B2767139 : Blo 1228432 2767139 := bstep (se 1 (by rfl) ⟨2075354, by rfl⟩ : syracuseStep 2767139 = 4150709) B4150709
theorem B2103617 : Blo 1228432 2103617 := bstep (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) B1577713
theorem B1751377 : Blo 1228432 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B1382755 : Blo 1228432 1382755 := bstep (se 1 (by rfl) ⟨1037066, by rfl⟩ : syracuseStep 1382755 = 2074133) B2074133
theorem B3111281 : Blo 1228432 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B3111331 : Blo 1228432 3111331 := bstep (se 1 (by rfl) ⟨2333498, by rfl⟩ : syracuseStep 3111331 = 4666997) B4666997
theorem B1751491 : Blo 1228432 1751491 := bstep (se 1 (by rfl) ⟨1313618, by rfl⟩ : syracuseStep 1751491 = 2627237) B2627237
theorem B4151789 : Blo 1228432 4151789 := bstep (se 3 (by rfl) ⟨778460, by rfl⟩ : syracuseStep 4151789 = 1556921) B1556921
theorem B1382899 : Blo 1228432 1382899 := bstep (se 1 (by rfl) ⟨1037174, by rfl⟩ : syracuseStep 1382899 = 2074349) B2074349
theorem B6068749 : Blo 1228432 6068749 := bstep (se 3 (by rfl) ⟨1137890, by rfl⟩ : syracuseStep 6068749 = 2275781) B2275781
theorem B11983373 : Blo 1228432 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B4667939 : Blo 1228432 4667939 := bstep (se 1 (by rfl) ⟨3500954, by rfl⟩ : syracuseStep 4667939 = 7001909) B7001909
theorem B4151843 : Blo 1228432 4151843 := bstep (se 1 (by rfl) ⟨3113882, by rfl⟩ : syracuseStep 4151843 = 6227765) B6227765
theorem B3111473 : Blo 1228432 3111473 := bstep (se 2 (by rfl) ⟨1166802, by rfl⟩ : syracuseStep 3111473 = 2333605) B2333605
theorem B2767409 : Blo 1228432 2767409 := bstep (se 2 (by rfl) ⟨1037778, by rfl⟩ : syracuseStep 2767409 = 2075557) B2075557
theorem B63871541 : Blo 1228432 63871541 := bstep (se 5 (by rfl) ⟨2993978, by rfl⟩ : syracuseStep 63871541 = 5987957) B5987957
theorem B2767427 : Blo 1228432 2767427 := bstep (se 1 (by rfl) ⟨2075570, by rfl⟩ : syracuseStep 2767427 = 4151141) B4151141
theorem B10500677 : Blo 1228432 10500677 := bstep (se 4 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 10500677 = 1968877) B1968877
theorem B1383043 : Blo 1228432 1383043 := bstep (se 1 (by rfl) ⟨1037282, by rfl⟩ : syracuseStep 1383043 = 2074565) B2074565
theorem B5905037 : Blo 1228432 5905037 := bstep (se 3 (by rfl) ⟨1107194, by rfl⟩ : syracuseStep 5905037 = 2214389) B2214389
theorem B6224525 : Blo 1228432 6224525 := bstep (se 3 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 6224525 = 2334197) B2334197
theorem B3324557 : Blo 1228432 3324557 := bstep (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) B1246709
theorem B1555139 : Blo 1228432 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1383187 : Blo 1228432 1383187 := bstep (se 1 (by rfl) ⟨1037390, by rfl⟩ : syracuseStep 1383187 = 2074781) B2074781
theorem B3152675 : Blo 1228432 3152675 := bstep (se 1 (by rfl) ⟨2364506, by rfl⟩ : syracuseStep 3152675 = 4729013) B4729013
theorem B4152113 : Blo 1228432 4152113 := bstep (se 2 (by rfl) ⟨1557042, by rfl⟩ : syracuseStep 4152113 = 3114085) B3114085
theorem B2104129 : Blo 1228432 2104129 := bstep (se 2 (by rfl) ⟨789048, by rfl⟩ : syracuseStep 2104129 = 1578097) B1578097
theorem B2767697 : Blo 1228432 2767697 := bstep (se 2 (by rfl) ⟨1037886, by rfl⟩ : syracuseStep 2767697 = 2075773) B2075773
theorem B2767715 : Blo 1228432 2767715 := bstep (se 1 (by rfl) ⟨2075786, by rfl⟩ : syracuseStep 2767715 = 4151573) B4151573
theorem B1383331 : Blo 1228432 1383331 := bstep (se 1 (by rfl) ⟨1037498, by rfl⟩ : syracuseStep 1383331 = 2074997) B2074997
theorem B2333681 : Blo 1228432 2333681 := bstep (se 2 (by rfl) ⟨875130, by rfl⟩ : syracuseStep 2333681 = 1750261) B1750261
theorem B2104355 : Blo 1228432 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B1383475 : Blo 1228432 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B10509425 : Blo 1228432 10509425 := bstep (se 2 (by rfl) ⟨3941034, by rfl⟩ : syracuseStep 10509425 = 7882069) B7882069
theorem B2767985 : Blo 1228432 2767985 := bstep (se 2 (by rfl) ⟨1037994, by rfl⟩ : syracuseStep 2767985 = 2075989) B2075989
theorem B2768003 : Blo 1228432 2768003 := bstep (se 1 (by rfl) ⟨2076002, by rfl⟩ : syracuseStep 2768003 = 4152005) B4152005
theorem B1383619 : Blo 1228432 1383619 := bstep (se 1 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 1383619 = 2075429) B2075429
theorem B26934581 : Blo 1228432 26934581 := bstep (se 5 (by rfl) ⟨1262558, by rfl⟩ : syracuseStep 26934581 = 2525117) B2525117
theorem B4152653 : Blo 1228432 4152653 := bstep (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) B1557245
theorem B1383763 : Blo 1228432 1383763 := bstep (se 1 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 1383763 = 2075645) B2075645
theorem B1555843 : Blo 1228432 1555843 := bstep (se 1 (by rfl) ⟨1166882, by rfl⟩ : syracuseStep 1555843 = 2333765) B2333765
theorem B4152707 : Blo 1228432 4152707 := bstep (se 1 (by rfl) ⟨3114530, by rfl⟩ : syracuseStep 4152707 = 6229061) B6229061
theorem B2768273 : Blo 1228432 2768273 := bstep (se 2 (by rfl) ⟨1038102, by rfl⟩ : syracuseStep 2768273 = 2076205) B2076205
theorem B2768291 : Blo 1228432 2768291 := bstep (se 1 (by rfl) ⟨2076218, by rfl⟩ : syracuseStep 2768291 = 4152437) B4152437
theorem B3939779 : Blo 1228432 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B1842659 : Blo 1228432 1842659 := bstep (se 1 (by rfl) ⟨1381994, by rfl⟩ : syracuseStep 1842659 = 2763989) B2763989
theorem B1555939 : Blo 1228432 1555939 := bstep (se 1 (by rfl) ⟨1166954, by rfl⟩ : syracuseStep 1555939 = 2333909) B2333909
theorem B1383907 : Blo 1228432 1383907 := bstep (se 1 (by rfl) ⟨1037930, by rfl⟩ : syracuseStep 1383907 = 2075861) B2075861
theorem B1842689 : Blo 1228432 1842689 := bstep (se 2 (by rfl) ⟨691008, by rfl⟩ : syracuseStep 1842689 = 1382017) B1382017
theorem B4668941 : Blo 1228432 4668941 := bstep (se 3 (by rfl) ⟨875426, by rfl⟩ : syracuseStep 4668941 = 1750853) B1750853
theorem B3112465 : Blo 1228432 3112465 := bstep (se 2 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 3112465 = 2334349) B2334349
theorem B1842707 : Blo 1228432 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B1842737 : Blo 1228432 1842737 := bstep (se 2 (by rfl) ⟨691026, by rfl⟩ : syracuseStep 1842737 = 1382053) B1382053
theorem B1842755 : Blo 1228432 1842755 := bstep (se 1 (by rfl) ⟨1382066, by rfl⟩ : syracuseStep 1842755 = 2764133) B2764133
theorem B1842785 : Blo 1228432 1842785 := bstep (se 2 (by rfl) ⟨691044, by rfl⟩ : syracuseStep 1842785 = 1382089) B1382089
theorem B13999715 : Blo 1228432 13999715 := bstep (se 1 (by rfl) ⟨10499786, by rfl⟩ : syracuseStep 13999715 = 20999573) B20999573
theorem B1842803 : Blo 1228432 1842803 := bstep (se 1 (by rfl) ⟨1382102, by rfl⟩ : syracuseStep 1842803 = 2764205) B2764205
theorem B1384051 : Blo 1228432 1384051 := bstep (se 1 (by rfl) ⟨1038038, by rfl⟩ : syracuseStep 1384051 = 2076077) B2076077
theorem B12623501 : Blo 1228432 12623501 := bstep (se 3 (by rfl) ⟨2366906, by rfl⟩ : syracuseStep 12623501 = 4733813) B4733813
theorem B1842833 : Blo 1228432 1842833 := bstep (se 2 (by rfl) ⟨691062, by rfl⟩ : syracuseStep 1842833 = 1382125) B1382125
theorem B1228435 : Blo 1228432 1228435 := bstep (se 1 (by rfl) ⟨921326, by rfl⟩ : syracuseStep 1228435 = 1842653) B1842653
theorem B1228451 : Blo 1228432 1228451 := bstep (se 1 (by rfl) ⟨921338, by rfl⟩ : syracuseStep 1228451 = 1842677) B1842677
theorem B1842851 : Blo 1228432 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B1228467 : Blo 1228432 1228467 := bstep (se 1 (by rfl) ⟨921350, by rfl⟩ : syracuseStep 1228467 = 1842701) B1842701
theorem B1842881 : Blo 1228432 1842881 := bstep (se 2 (by rfl) ⟨691080, by rfl⟩ : syracuseStep 1842881 = 1382161) B1382161
theorem B1228483 : Blo 1228432 1228483 := bstep (se 1 (by rfl) ⟨921362, by rfl⟩ : syracuseStep 1228483 = 1842725) B1842725
theorem B11976389 : Blo 1228432 11976389 := bstep (se 4 (by rfl) ⟨1122786, by rfl⟩ : syracuseStep 11976389 = 2245573) B2245573
theorem B1228499 : Blo 1228432 1228499 := bstep (se 1 (by rfl) ⟨921374, by rfl⟩ : syracuseStep 1228499 = 1842749) B1842749
theorem B1842899 : Blo 1228432 1842899 := bstep (se 1 (by rfl) ⟨1382174, by rfl⟩ : syracuseStep 1842899 = 2764349) B2764349
theorem B1228515 : Blo 1228432 1228515 := bstep (se 1 (by rfl) ⟨921386, by rfl⟩ : syracuseStep 1228515 = 1842773) B1842773
theorem B1842929 : Blo 1228432 1842929 := bstep (se 2 (by rfl) ⟨691098, by rfl⟩ : syracuseStep 1842929 = 1382197) B1382197
theorem B1228531 : Blo 1228432 1228531 := bstep (se 1 (by rfl) ⟨921398, by rfl⟩ : syracuseStep 1228531 = 1842797) B1842797
theorem B1228547 : Blo 1228432 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B1842947 : Blo 1228432 1842947 := bstep (se 1 (by rfl) ⟨1382210, by rfl⟩ : syracuseStep 1842947 = 2764421) B2764421
theorem B1384195 : Blo 1228432 1384195 := bstep (se 1 (by rfl) ⟨1038146, by rfl⟩ : syracuseStep 1384195 = 2076293) B2076293
theorem B1228563 : Blo 1228432 1228563 := bstep (se 1 (by rfl) ⟨921422, by rfl⟩ : syracuseStep 1228563 = 1842845) B1842845
theorem B1842977 : Blo 1228432 1842977 := bstep (se 2 (by rfl) ⟨691116, by rfl⟩ : syracuseStep 1842977 = 1382233) B1382233
theorem B1228579 : Blo 1228432 1228579 := bstep (se 1 (by rfl) ⟨921434, by rfl⟩ : syracuseStep 1228579 = 1842869) B1842869
theorem B5250851 : Blo 1228432 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B3112739 : Blo 1228432 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B1228595 : Blo 1228432 1228595 := bstep (se 1 (by rfl) ⟨921446, by rfl⟩ : syracuseStep 1228595 = 1842893) B1842893
theorem B1842995 : Blo 1228432 1842995 := bstep (se 1 (by rfl) ⟨1382246, by rfl⟩ : syracuseStep 1842995 = 2764493) B2764493
theorem B1228611 : Blo 1228432 1228611 := bstep (se 1 (by rfl) ⟨921458, by rfl⟩ : syracuseStep 1228611 = 1842917) B1842917
theorem B1843025 : Blo 1228432 1843025 := bstep (se 2 (by rfl) ⟨691134, by rfl⟩ : syracuseStep 1843025 = 1382269) B1382269
theorem B3940177 : Blo 1228432 3940177 := bstep (se 2 (by rfl) ⟨1477566, by rfl⟩ : syracuseStep 3940177 = 2955133) B2955133
theorem B1228627 : Blo 1228432 1228627 := bstep (se 1 (by rfl) ⟨921470, by rfl⟩ : syracuseStep 1228627 = 1842941) B1842941
theorem B1228643 : Blo 1228432 1228643 := bstep (se 1 (by rfl) ⟨921482, by rfl⟩ : syracuseStep 1228643 = 1842965) B1842965
theorem B1843043 : Blo 1228432 1843043 := bstep (se 1 (by rfl) ⟨1382282, by rfl⟩ : syracuseStep 1843043 = 2764565) B2764565
theorem B2334577 : Blo 1228432 2334577 := bstep (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) B1750933
theorem B1228659 : Blo 1228432 1228659 := bstep (se 1 (by rfl) ⟨921494, by rfl⟩ : syracuseStep 1228659 = 1842989) B1842989
theorem B1843073 : Blo 1228432 1843073 := bstep (se 2 (by rfl) ⟨691152, by rfl⟩ : syracuseStep 1843073 = 1382305) B1382305
theorem B1228675 : Blo 1228432 1228675 := bstep (se 1 (by rfl) ⟨921506, by rfl⟩ : syracuseStep 1228675 = 1843013) B1843013
theorem B7880581 : Blo 1228432 7880581 := bstep (se 4 (by rfl) ⟨738804, by rfl⟩ : syracuseStep 7880581 = 1477609) B1477609
theorem B1228691 : Blo 1228432 1228691 := bstep (se 1 (by rfl) ⟨921518, by rfl⟩ : syracuseStep 1228691 = 1843037) B1843037
theorem B1843091 : Blo 1228432 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1228707 : Blo 1228432 1228707 := bstep (se 1 (by rfl) ⟨921530, by rfl⟩ : syracuseStep 1228707 = 1843061) B1843061
theorem B4431779 : Blo 1228432 4431779 := bstep (se 1 (by rfl) ⟨3323834, by rfl⟩ : syracuseStep 4431779 = 6647669) B6647669
theorem B1843121 : Blo 1228432 1843121 := bstep (se 2 (by rfl) ⟨691170, by rfl⟩ : syracuseStep 1843121 = 1382341) B1382341
theorem B1228723 : Blo 1228432 1228723 := bstep (se 1 (by rfl) ⟨921542, by rfl⟩ : syracuseStep 1228723 = 1843085) B1843085
theorem B1228739 : Blo 1228432 1228739 := bstep (se 1 (by rfl) ⟨921554, by rfl⟩ : syracuseStep 1228739 = 1843109) B1843109
theorem B1843139 : Blo 1228432 1843139 := bstep (se 1 (by rfl) ⟨1382354, by rfl⟩ : syracuseStep 1843139 = 2764709) B2764709
theorem B1228755 : Blo 1228432 1228755 := bstep (se 1 (by rfl) ⟨921566, by rfl⟩ : syracuseStep 1228755 = 1843133) B1843133
theorem B1556435 : Blo 1228432 1556435 := bstep (se 1 (by rfl) ⟨1167326, by rfl⟩ : syracuseStep 1556435 = 2334653) B2334653
theorem B1843169 : Blo 1228432 1843169 := bstep (se 2 (by rfl) ⟨691188, by rfl⟩ : syracuseStep 1843169 = 1382377) B1382377
theorem B1228771 : Blo 1228432 1228771 := bstep (se 1 (by rfl) ⟨921578, by rfl⟩ : syracuseStep 1228771 = 1843157) B1843157
theorem B3112931 : Blo 1228432 3112931 := bstep (se 1 (by rfl) ⟨2334698, by rfl⟩ : syracuseStep 3112931 = 4669397) B4669397
theorem B1228787 : Blo 1228432 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1843187 : Blo 1228432 1843187 := bstep (se 1 (by rfl) ⟨1382390, by rfl⟩ : syracuseStep 1843187 = 2764781) B2764781
theorem B1843211 : Blo 1228432 1843211 := bstep (se 1 (by rfl) ⟨1382408, by rfl⟩ : syracuseStep 1843211 = 2764817) B2764817
theorem B1228811 : Blo 1228432 1228811 := bstep (se 1 (by rfl) ⟨921608, by rfl⟩ : syracuseStep 1228811 = 1843217) B1843217
theorem B1556491 : Blo 1228432 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B1843223 : Blo 1228432 1843223 := bstep (se 1 (by rfl) ⟨1382417, by rfl⟩ : syracuseStep 1843223 = 2764835) B2764835
theorem B1228823 : Blo 1228432 1228823 := bstep (se 1 (by rfl) ⟨921617, by rfl⟩ : syracuseStep 1228823 = 1843235) B1843235
theorem B1228843 : Blo 1228432 1228843 := bstep (se 1 (by rfl) ⟨921632, by rfl⟩ : syracuseStep 1228843 = 1843265) B1843265
theorem B1228855 : Blo 1228432 1228855 := bstep (se 1 (by rfl) ⟨921641, by rfl⟩ : syracuseStep 1228855 = 1843283) B1843283
theorem B1228875 : Blo 1228432 1228875 := bstep (se 1 (by rfl) ⟨921656, by rfl⟩ : syracuseStep 1228875 = 1843313) B1843313
theorem B1228887 : Blo 1228432 1228887 := bstep (se 1 (by rfl) ⟨921665, by rfl⟩ : syracuseStep 1228887 = 1843331) B1843331
theorem B1843289 : Blo 1228432 1843289 := bstep (se 2 (by rfl) ⟨691233, by rfl⟩ : syracuseStep 1843289 = 1382467) B1382467
theorem B1228907 : Blo 1228432 1228907 := bstep (se 1 (by rfl) ⟨921680, by rfl⟩ : syracuseStep 1228907 = 1843361) B1843361
theorem B2334835 : Blo 1228432 2334835 := bstep (se 1 (by rfl) ⟨1751126, by rfl⟩ : syracuseStep 2334835 = 3502253) B3502253
theorem B1228919 : Blo 1228432 1228919 := bstep (se 1 (by rfl) ⟨921689, by rfl⟩ : syracuseStep 1228919 = 1843379) B1843379
theorem B1228939 : Blo 1228432 1228939 := bstep (se 1 (by rfl) ⟨921704, by rfl⟩ : syracuseStep 1228939 = 1843409) B1843409
theorem B1228951 : Blo 1228432 1228951 := bstep (se 1 (by rfl) ⟨921713, by rfl⟩ : syracuseStep 1228951 = 1843427) B1843427
theorem B1228971 : Blo 1228432 1228971 := bstep (se 1 (by rfl) ⟨921728, by rfl⟩ : syracuseStep 1228971 = 1843457) B1843457
theorem B39878837 : Blo 1228432 39878837 := bstep (se 5 (by rfl) ⟨1869320, by rfl⟩ : syracuseStep 39878837 = 3738641) B3738641
theorem B1228983 : Blo 1228432 1228983 := bstep (se 1 (by rfl) ⟨921737, by rfl⟩ : syracuseStep 1228983 = 1843475) B1843475
theorem B3498187 : Blo 1228432 3498187 := bstep (se 1 (by rfl) ⟨2623640, by rfl⟩ : syracuseStep 3498187 = 5247281) B5247281
theorem B1843403 : Blo 1228432 1843403 := bstep (se 1 (by rfl) ⟨1382552, by rfl⟩ : syracuseStep 1843403 = 2765105) B2765105
theorem B1229003 : Blo 1228432 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B1843415 : Blo 1228432 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B1229015 : Blo 1228432 1229015 := bstep (se 1 (by rfl) ⟨921761, by rfl⟩ : syracuseStep 1229015 = 1843523) B1843523
theorem B3735773 : Blo 1228432 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B3367133 : Blo 1228432 3367133 := bstep (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) B1262675
theorem B1229035 : Blo 1228432 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B1229047 : Blo 1228432 1229047 := bstep (se 1 (by rfl) ⟨921785, by rfl⟩ : syracuseStep 1229047 = 1843571) B1843571
theorem B1229067 : Blo 1228432 1229067 := bstep (se 1 (by rfl) ⟨921800, by rfl⟩ : syracuseStep 1229067 = 1843601) B1843601
theorem B1229079 : Blo 1228432 1229079 := bstep (se 1 (by rfl) ⟨921809, by rfl⟩ : syracuseStep 1229079 = 1843619) B1843619
theorem B1556759 : Blo 1228432 1556759 := bstep (se 1 (by rfl) ⟨1167569, by rfl⟩ : syracuseStep 1556759 = 2335139) B2335139
theorem B1843481 : Blo 1228432 1843481 := bstep (se 2 (by rfl) ⟨691305, by rfl⟩ : syracuseStep 1843481 = 1382611) B1382611
theorem B1229099 : Blo 1228432 1229099 := bstep (se 1 (by rfl) ⟨921824, by rfl⟩ : syracuseStep 1229099 = 1843649) B1843649
theorem B1229111 : Blo 1228432 1229111 := bstep (se 1 (by rfl) ⟨921833, by rfl⟩ : syracuseStep 1229111 = 1843667) B1843667
theorem B1229131 : Blo 1228432 1229131 := bstep (se 1 (by rfl) ⟨921848, by rfl⟩ : syracuseStep 1229131 = 1843697) B1843697
theorem B1229143 : Blo 1228432 1229143 := bstep (se 1 (by rfl) ⟨921857, by rfl⟩ : syracuseStep 1229143 = 1843715) B1843715
theorem B2335063 : Blo 1228432 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1229163 : Blo 1228432 1229163 := bstep (se 1 (by rfl) ⟨921872, by rfl⟩ : syracuseStep 1229163 = 1843745) B1843745
theorem B50446709 : Blo 1228432 50446709 := bstep (se 5 (by rfl) ⟨2364689, by rfl⟩ : syracuseStep 50446709 = 4729379) B4729379
theorem B1229175 : Blo 1228432 1229175 := bstep (se 1 (by rfl) ⟨921881, by rfl⟩ : syracuseStep 1229175 = 1843763) B1843763
theorem B6226307 : Blo 1228432 6226307 := bstep (se 1 (by rfl) ⟨4669730, by rfl⟩ : syracuseStep 6226307 = 9339461) B9339461
theorem B1843595 : Blo 1228432 1843595 := bstep (se 1 (by rfl) ⟨1382696, by rfl⟩ : syracuseStep 1843595 = 2765393) B2765393
theorem B1229195 : Blo 1228432 1229195 := bstep (se 1 (by rfl) ⟨921896, by rfl⟩ : syracuseStep 1229195 = 1843793) B1843793
theorem B1843607 : Blo 1228432 1843607 := bstep (se 1 (by rfl) ⟨1382705, by rfl⟩ : syracuseStep 1843607 = 2765411) B2765411
theorem B1229207 : Blo 1228432 1229207 := bstep (se 1 (by rfl) ⟨921905, by rfl⟩ : syracuseStep 1229207 = 1843811) B1843811
theorem B1229227 : Blo 1228432 1229227 := bstep (se 1 (by rfl) ⟨921920, by rfl⟩ : syracuseStep 1229227 = 1843841) B1843841
theorem B1229239 : Blo 1228432 1229239 := bstep (se 1 (by rfl) ⟨921929, by rfl⟩ : syracuseStep 1229239 = 1843859) B1843859
theorem B2335169 : Blo 1228432 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1229259 : Blo 1228432 1229259 := bstep (se 1 (by rfl) ⟨921944, by rfl⟩ : syracuseStep 1229259 = 1843889) B1843889
theorem B5611979 : Blo 1228432 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B1229271 : Blo 1228432 1229271 := bstep (se 1 (by rfl) ⟨921953, by rfl⟩ : syracuseStep 1229271 = 1843907) B1843907
theorem B1843673 : Blo 1228432 1843673 := bstep (se 2 (by rfl) ⟨691377, by rfl⟩ : syracuseStep 1843673 = 1382755) B1382755
theorem B3498461 : Blo 1228432 3498461 := bstep (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) B1311923
theorem B4669913 : Blo 1228432 4669913 := bstep (se 2 (by rfl) ⟨1751217, by rfl⟩ : syracuseStep 4669913 = 3502435) B3502435
theorem B35471843 : Blo 1228432 35471843 := bstep (se 1 (by rfl) ⟨26603882, by rfl⟩ : syracuseStep 35471843 = 53207765) B53207765
theorem B1229291 : Blo 1228432 1229291 := bstep (se 1 (by rfl) ⟨921968, by rfl⟩ : syracuseStep 1229291 = 1843937) B1843937
theorem B1229303 : Blo 1228432 1229303 := bstep (se 1 (by rfl) ⟨921977, by rfl⟩ : syracuseStep 1229303 = 1843955) B1843955
theorem B1229323 : Blo 1228432 1229323 := bstep (se 1 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 1229323 = 1843985) B1843985
theorem B1401367 : Blo 1228432 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B1229335 : Blo 1228432 1229335 := bstep (se 1 (by rfl) ⟨922001, by rfl⟩ : syracuseStep 1229335 = 1844003) B1844003
theorem B1229355 : Blo 1228432 1229355 := bstep (se 1 (by rfl) ⟨922016, by rfl⟩ : syracuseStep 1229355 = 1844033) B1844033
theorem B3736115 : Blo 1228432 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B1229367 : Blo 1228432 1229367 := bstep (se 1 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 1229367 = 1844051) B1844051
theorem B1843787 : Blo 1228432 1843787 := bstep (se 1 (by rfl) ⟨1382840, by rfl⟩ : syracuseStep 1843787 = 2765681) B2765681
theorem B1229387 : Blo 1228432 1229387 := bstep (se 1 (by rfl) ⟨922040, by rfl⟩ : syracuseStep 1229387 = 1844081) B1844081
theorem B1843799 : Blo 1228432 1843799 := bstep (se 1 (by rfl) ⟨1382849, by rfl⟩ : syracuseStep 1843799 = 2765699) B2765699
theorem B1229399 : Blo 1228432 1229399 := bstep (se 1 (by rfl) ⟨922049, by rfl⟩ : syracuseStep 1229399 = 1844099) B1844099
theorem B2335321 : Blo 1228432 2335321 := bstep (se 2 (by rfl) ⟨875745, by rfl⟩ : syracuseStep 2335321 = 1751491) B1751491
theorem B1229419 : Blo 1228432 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B1229431 : Blo 1228432 1229431 := bstep (se 1 (by rfl) ⟨922073, by rfl⟩ : syracuseStep 1229431 = 1844147) B1844147
theorem B14959235 : Blo 1228432 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1229451 : Blo 1228432 1229451 := bstep (se 1 (by rfl) ⟨922088, by rfl⟩ : syracuseStep 1229451 = 1844177) B1844177
theorem B1229463 : Blo 1228432 1229463 := bstep (se 1 (by rfl) ⟨922097, by rfl⟩ : syracuseStep 1229463 = 1844195) B1844195
theorem B1843865 : Blo 1228432 1843865 := bstep (se 2 (by rfl) ⟨691449, by rfl⟩ : syracuseStep 1843865 = 1382899) B1382899
theorem B1229483 : Blo 1228432 1229483 := bstep (se 1 (by rfl) ⟨922112, by rfl⟩ : syracuseStep 1229483 = 1844225) B1844225
theorem B1229495 : Blo 1228432 1229495 := bstep (se 1 (by rfl) ⟨922121, by rfl⟩ : syracuseStep 1229495 = 1844243) B1844243
theorem B1229515 : Blo 1228432 1229515 := bstep (se 1 (by rfl) ⟨922136, by rfl⟩ : syracuseStep 1229515 = 1844273) B1844273
theorem B19456717 : Blo 1228432 19456717 := bstep (se 3 (by rfl) ⟨3648134, by rfl⟩ : syracuseStep 19456717 = 7296269) B7296269
theorem B1229527 : Blo 1228432 1229527 := bstep (se 1 (by rfl) ⟨922145, by rfl⟩ : syracuseStep 1229527 = 1844291) B1844291
theorem B1229547 : Blo 1228432 1229547 := bstep (se 1 (by rfl) ⟨922160, by rfl⟩ : syracuseStep 1229547 = 1844321) B1844321
theorem B1229559 : Blo 1228432 1229559 := bstep (se 1 (by rfl) ⟨922169, by rfl⟩ : syracuseStep 1229559 = 1844339) B1844339
theorem B1843979 : Blo 1228432 1843979 := bstep (se 1 (by rfl) ⟨1382984, by rfl⟩ : syracuseStep 1843979 = 2765969) B2765969
theorem B1229579 : Blo 1228432 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B1843991 : Blo 1228432 1843991 := bstep (se 1 (by rfl) ⟨1382993, by rfl⟩ : syracuseStep 1843991 = 2765987) B2765987
theorem B1229591 : Blo 1228432 1229591 := bstep (se 1 (by rfl) ⟨922193, by rfl⟩ : syracuseStep 1229591 = 1844387) B1844387
theorem B1229611 : Blo 1228432 1229611 := bstep (se 1 (by rfl) ⟨922208, by rfl⟩ : syracuseStep 1229611 = 1844417) B1844417
theorem B1229623 : Blo 1228432 1229623 := bstep (se 1 (by rfl) ⟨922217, by rfl⟩ : syracuseStep 1229623 = 1844435) B1844435
theorem B1229643 : Blo 1228432 1229643 := bstep (se 1 (by rfl) ⟨922232, by rfl⟩ : syracuseStep 1229643 = 1844465) B1844465
theorem B2073431 : Blo 1228432 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B1844057 : Blo 1228432 1844057 := bstep (se 2 (by rfl) ⟨691521, by rfl⟩ : syracuseStep 1844057 = 1383043) B1383043
theorem B1229655 : Blo 1228432 1229655 := bstep (se 1 (by rfl) ⟨922241, by rfl⟩ : syracuseStep 1229655 = 1844483) B1844483
theorem B1229675 : Blo 1228432 1229675 := bstep (se 1 (by rfl) ⟨922256, by rfl⟩ : syracuseStep 1229675 = 1844513) B1844513
theorem B1229687 : Blo 1228432 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1229707 : Blo 1228432 1229707 := bstep (se 1 (by rfl) ⟨922280, by rfl⟩ : syracuseStep 1229707 = 1844561) B1844561
theorem B1229719 : Blo 1228432 1229719 := bstep (se 1 (by rfl) ⟨922289, by rfl⟩ : syracuseStep 1229719 = 1844579) B1844579
theorem B1229739 : Blo 1228432 1229739 := bstep (se 1 (by rfl) ⟨922304, by rfl⟩ : syracuseStep 1229739 = 1844609) B1844609
theorem B1229751 : Blo 1228432 1229751 := bstep (se 1 (by rfl) ⟨922313, by rfl⟩ : syracuseStep 1229751 = 1844627) B1844627
theorem B1844171 : Blo 1228432 1844171 := bstep (se 1 (by rfl) ⟨1383128, by rfl⟩ : syracuseStep 1844171 = 2766257) B2766257
theorem B1229771 : Blo 1228432 1229771 := bstep (se 1 (by rfl) ⟨922328, by rfl⟩ : syracuseStep 1229771 = 1844657) B1844657
theorem B2073559 : Blo 1228432 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B1844183 : Blo 1228432 1844183 := bstep (se 1 (by rfl) ⟨1383137, by rfl⟩ : syracuseStep 1844183 = 2766275) B2766275
theorem B1229783 : Blo 1228432 1229783 := bstep (se 1 (by rfl) ⟨922337, by rfl⟩ : syracuseStep 1229783 = 1844675) B1844675
theorem B1229803 : Blo 1228432 1229803 := bstep (se 1 (by rfl) ⟨922352, by rfl⟩ : syracuseStep 1229803 = 1844705) B1844705
theorem B1229815 : Blo 1228432 1229815 := bstep (se 1 (by rfl) ⟨922361, by rfl⟩ : syracuseStep 1229815 = 1844723) B1844723
theorem B1229835 : Blo 1228432 1229835 := bstep (se 1 (by rfl) ⟨922376, by rfl⟩ : syracuseStep 1229835 = 1844753) B1844753
theorem B1229847 : Blo 1228432 1229847 := bstep (se 1 (by rfl) ⟨922385, by rfl⟩ : syracuseStep 1229847 = 1844771) B1844771
theorem B1844249 : Blo 1228432 1844249 := bstep (se 2 (by rfl) ⟨691593, by rfl⟩ : syracuseStep 1844249 = 1383187) B1383187
theorem B1229867 : Blo 1228432 1229867 := bstep (se 1 (by rfl) ⟨922400, by rfl⟩ : syracuseStep 1229867 = 1844801) B1844801
theorem B4146227 : Blo 1228432 4146227 := bstep (se 1 (by rfl) ⟨3109670, by rfl⟩ : syracuseStep 4146227 = 6219341) B6219341
theorem B3114035 : Blo 1228432 3114035 := bstep (se 1 (by rfl) ⟨2335526, by rfl⟩ : syracuseStep 3114035 = 4671053) B4671053
theorem B1229879 : Blo 1228432 1229879 := bstep (se 1 (by rfl) ⟨922409, by rfl⟩ : syracuseStep 1229879 = 1844819) B1844819
theorem B1229899 : Blo 1228432 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B1229911 : Blo 1228432 1229911 := bstep (se 1 (by rfl) ⟨922433, by rfl⟩ : syracuseStep 1229911 = 1844867) B1844867
theorem B1229931 : Blo 1228432 1229931 := bstep (se 1 (by rfl) ⟨922448, by rfl⟩ : syracuseStep 1229931 = 1844897) B1844897
theorem B1229943 : Blo 1228432 1229943 := bstep (se 1 (by rfl) ⟨922457, by rfl⟩ : syracuseStep 1229943 = 1844915) B1844915
theorem B1844363 : Blo 1228432 1844363 := bstep (se 1 (by rfl) ⟨1383272, by rfl⟩ : syracuseStep 1844363 = 2766545) B2766545
theorem B1229963 : Blo 1228432 1229963 := bstep (se 1 (by rfl) ⟨922472, by rfl⟩ : syracuseStep 1229963 = 1844945) B1844945
theorem B1844375 : Blo 1228432 1844375 := bstep (se 1 (by rfl) ⟨1383281, by rfl⟩ : syracuseStep 1844375 = 2766563) B2766563
theorem B1229975 : Blo 1228432 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B1229995 : Blo 1228432 1229995 := bstep (se 1 (by rfl) ⟨922496, by rfl⟩ : syracuseStep 1229995 = 1844993) B1844993
theorem B1230007 : Blo 1228432 1230007 := bstep (se 1 (by rfl) ⟨922505, by rfl⟩ : syracuseStep 1230007 = 1845011) B1845011
theorem B1230027 : Blo 1228432 1230027 := bstep (se 1 (by rfl) ⟨922520, by rfl⟩ : syracuseStep 1230027 = 1845041) B1845041
theorem B1230039 : Blo 1228432 1230039 := bstep (se 1 (by rfl) ⟨922529, by rfl⟩ : syracuseStep 1230039 = 1845059) B1845059
theorem B1844441 : Blo 1228432 1844441 := bstep (se 2 (by rfl) ⟨691665, by rfl⟩ : syracuseStep 1844441 = 1383331) B1383331
theorem B1230059 : Blo 1228432 1230059 := bstep (se 1 (by rfl) ⟨922544, by rfl⟩ : syracuseStep 1230059 = 1845089) B1845089
theorem B1230071 : Blo 1228432 1230071 := bstep (se 1 (by rfl) ⟨922553, by rfl⟩ : syracuseStep 1230071 = 1845107) B1845107
theorem B1230091 : Blo 1228432 1230091 := bstep (se 1 (by rfl) ⟨922568, by rfl⟩ : syracuseStep 1230091 = 1845137) B1845137
theorem B1230103 : Blo 1228432 1230103 := bstep (se 1 (by rfl) ⟨922577, by rfl⟩ : syracuseStep 1230103 = 1845155) B1845155
theorem B1230123 : Blo 1228432 1230123 := bstep (se 1 (by rfl) ⟨922592, by rfl⟩ : syracuseStep 1230123 = 1845185) B1845185
theorem B10495277 : Blo 1228432 10495277 := bstep (se 3 (by rfl) ⟨1967864, by rfl⟩ : syracuseStep 10495277 = 3935729) B3935729
theorem B1230135 : Blo 1228432 1230135 := bstep (se 1 (by rfl) ⟨922601, by rfl⟩ : syracuseStep 1230135 = 1845203) B1845203
theorem B4146497 : Blo 1228432 4146497 := bstep (se 2 (by rfl) ⟨1554936, by rfl⟩ : syracuseStep 4146497 = 3109873) B3109873
theorem B1844555 : Blo 1228432 1844555 := bstep (se 1 (by rfl) ⟨1383416, by rfl⟩ : syracuseStep 1844555 = 2766833) B2766833
theorem B1230155 : Blo 1228432 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B1844567 : Blo 1228432 1844567 := bstep (se 1 (by rfl) ⟨1383425, by rfl⟩ : syracuseStep 1844567 = 2766851) B2766851
theorem B1230167 : Blo 1228432 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B1230187 : Blo 1228432 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B1230199 : Blo 1228432 1230199 := bstep (se 1 (by rfl) ⟨922649, by rfl⟩ : syracuseStep 1230199 = 1845299) B1845299
theorem B1230219 : Blo 1228432 1230219 := bstep (se 1 (by rfl) ⟨922664, by rfl⟩ : syracuseStep 1230219 = 1845329) B1845329
theorem B1230231 : Blo 1228432 1230231 := bstep (se 1 (by rfl) ⟨922673, by rfl⟩ : syracuseStep 1230231 = 1845347) B1845347
theorem B1844633 : Blo 1228432 1844633 := bstep (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) B1383475
theorem B1402283 : Blo 1228432 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B1230251 : Blo 1228432 1230251 := bstep (se 1 (by rfl) ⟨922688, by rfl⟩ : syracuseStep 1230251 = 1845377) B1845377
theorem B14943665 : Blo 1228432 14943665 := bstep (se 2 (by rfl) ⟨5603874, by rfl⟩ : syracuseStep 14943665 = 11207749) B11207749
theorem B1312183 : Blo 1228432 1312183 := bstep (se 1 (by rfl) ⟨984137, by rfl⟩ : syracuseStep 1312183 = 1968275) B1968275
theorem B1230263 : Blo 1228432 1230263 := bstep (se 1 (by rfl) ⟨922697, by rfl⟩ : syracuseStep 1230263 = 1845395) B1845395
theorem B1230283 : Blo 1228432 1230283 := bstep (se 1 (by rfl) ⟨922712, by rfl⟩ : syracuseStep 1230283 = 1845425) B1845425
theorem B1230295 : Blo 1228432 1230295 := bstep (se 1 (by rfl) ⟨922721, by rfl⟩ : syracuseStep 1230295 = 1845443) B1845443
theorem B1230315 : Blo 1228432 1230315 := bstep (se 1 (by rfl) ⟨922736, by rfl⟩ : syracuseStep 1230315 = 1845473) B1845473
theorem B1230327 : Blo 1228432 1230327 := bstep (se 1 (by rfl) ⟨922745, by rfl⟩ : syracuseStep 1230327 = 1845491) B1845491
theorem B1844747 : Blo 1228432 1844747 := bstep (se 1 (by rfl) ⟨1383560, by rfl⟩ : syracuseStep 1844747 = 2767121) B2767121
theorem B1230347 : Blo 1228432 1230347 := bstep (se 1 (by rfl) ⟨922760, by rfl⟩ : syracuseStep 1230347 = 1845521) B1845521
theorem B9340433 : Blo 1228432 9340433 := bstep (se 2 (by rfl) ⟨3502662, by rfl⟩ : syracuseStep 9340433 = 7005325) B7005325
theorem B1844759 : Blo 1228432 1844759 := bstep (se 1 (by rfl) ⟨1383569, by rfl⟩ : syracuseStep 1844759 = 2767139) B2767139
theorem B1230359 : Blo 1228432 1230359 := bstep (se 1 (by rfl) ⟨922769, by rfl⟩ : syracuseStep 1230359 = 1845539) B1845539
theorem B1230379 : Blo 1228432 1230379 := bstep (se 1 (by rfl) ⟨922784, by rfl⟩ : syracuseStep 1230379 = 1845569) B1845569
theorem B1230391 : Blo 1228432 1230391 := bstep (se 1 (by rfl) ⟨922793, by rfl⟩ : syracuseStep 1230391 = 1845587) B1845587
theorem B2074187 : Blo 1228432 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B1230411 : Blo 1228432 1230411 := bstep (se 1 (by rfl) ⟨922808, by rfl⟩ : syracuseStep 1230411 = 1845617) B1845617
theorem B1230423 : Blo 1228432 1230423 := bstep (se 1 (by rfl) ⟨922817, by rfl⟩ : syracuseStep 1230423 = 1845635) B1845635
theorem B1844825 : Blo 1228432 1844825 := bstep (se 2 (by rfl) ⟨691809, by rfl⟩ : syracuseStep 1844825 = 1383619) B1383619
theorem B3991133 : Blo 1228432 3991133 := bstep (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) B1496675
theorem B7988915 : Blo 1228432 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B2074315 : Blo 1228432 2074315 := bstep (se 1 (by rfl) ⟨1555736, by rfl⟩ : syracuseStep 2074315 = 3111473) B3111473
theorem B1844939 : Blo 1228432 1844939 := bstep (se 1 (by rfl) ⟨1383704, by rfl⟩ : syracuseStep 1844939 = 2767409) B2767409
theorem B1844951 : Blo 1228432 1844951 := bstep (se 1 (by rfl) ⟨1383713, by rfl⟩ : syracuseStep 1844951 = 2767427) B2767427
theorem B1845017 : Blo 1228432 1845017 := bstep (se 2 (by rfl) ⟨691881, by rfl⟩ : syracuseStep 1845017 = 1383763) B1383763
theorem B2074457 : Blo 1228432 2074457 := bstep (se 2 (by rfl) ⟨777921, by rfl⟩ : syracuseStep 2074457 = 1555843) B1555843
theorem B6997853 : Blo 1228432 6997853 := bstep (se 3 (by rfl) ⟨1312097, by rfl⟩ : syracuseStep 6997853 = 2624195) B2624195
theorem B4147037 : Blo 1228432 4147037 := bstep (se 3 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 4147037 = 1555139) B1555139
theorem B1845131 : Blo 1228432 1845131 := bstep (se 1 (by rfl) ⟨1383848, by rfl⟩ : syracuseStep 1845131 = 2767697) B2767697
theorem B1845143 : Blo 1228432 1845143 := bstep (se 1 (by rfl) ⟨1383857, by rfl⟩ : syracuseStep 1845143 = 2767715) B2767715
theorem B9332657 : Blo 1228432 9332657 := bstep (se 2 (by rfl) ⟨3499746, by rfl⟩ : syracuseStep 9332657 = 6999493) B6999493
theorem B2074585 : Blo 1228432 2074585 := bstep (se 2 (by rfl) ⟨777969, by rfl⟩ : syracuseStep 2074585 = 1555939) B1555939
theorem B1845209 : Blo 1228432 1845209 := bstep (se 2 (by rfl) ⟨691953, by rfl⟩ : syracuseStep 1845209 = 1383907) B1383907
theorem B1402903 : Blo 1228432 1402903 := bstep (se 1 (by rfl) ⟨1052177, by rfl⟩ : syracuseStep 1402903 = 2104355) B2104355
theorem B4671539 : Blo 1228432 4671539 := bstep (se 1 (by rfl) ⟨3503654, by rfl⟩ : syracuseStep 4671539 = 7007309) B7007309
theorem B4671553 : Blo 1228432 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B7006283 : Blo 1228432 7006283 := bstep (se 1 (by rfl) ⟨5254712, by rfl⟩ : syracuseStep 7006283 = 10509425) B10509425
theorem B1845323 : Blo 1228432 1845323 := bstep (se 1 (by rfl) ⟨1383992, by rfl⟩ : syracuseStep 1845323 = 2767985) B2767985
theorem B1845335 : Blo 1228432 1845335 := bstep (se 1 (by rfl) ⟨1384001, by rfl⟩ : syracuseStep 1845335 = 2768003) B2768003
theorem B1845401 : Blo 1228432 1845401 := bstep (se 2 (by rfl) ⟨692025, by rfl⟩ : syracuseStep 1845401 = 1384051) B1384051
theorem B1845515 : Blo 1228432 1845515 := bstep (se 1 (by rfl) ⟨1384136, by rfl⟩ : syracuseStep 1845515 = 2768273) B2768273
theorem B1845527 : Blo 1228432 1845527 := bstep (se 1 (by rfl) ⟨1384145, by rfl⟩ : syracuseStep 1845527 = 2768291) B2768291
theorem B1845593 : Blo 1228432 1845593 := bstep (se 2 (by rfl) ⟨692097, by rfl⟩ : syracuseStep 1845593 = 1384195) B1384195
theorem B19925347 : Blo 1228432 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B63883637 : Blo 1228432 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B9333143 : Blo 1228432 9333143 := bstep (se 1 (by rfl) ⟨6999857, by rfl⟩ : syracuseStep 9333143 = 13999715) B13999715
theorem B8415667 : Blo 1228432 8415667 := bstep (se 1 (by rfl) ⟨6311750, by rfl⟩ : syracuseStep 8415667 = 12623501) B12623501
theorem B5253569 : Blo 1228432 5253569 := bstep (se 2 (by rfl) ⟨1970088, by rfl⟩ : syracuseStep 5253569 = 3940177) B3940177
theorem B3738059 : Blo 1228432 3738059 := bstep (se 1 (by rfl) ⟨2803544, by rfl⟩ : syracuseStep 3738059 = 5607089) B5607089
theorem B3500567 : Blo 1228432 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B2075159 : Blo 1228432 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B2214425 : Blo 1228432 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B2624051 : Blo 1228432 2624051 := bstep (se 1 (by rfl) ⟨1968038, by rfl⟩ : syracuseStep 2624051 = 3936077) B3936077
theorem B2075287 : Blo 1228432 2075287 := bstep (se 1 (by rfl) ⟨1556465, by rfl⟩ : syracuseStep 2075287 = 3112931) B3112931
theorem B1870489 : Blo 1228432 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B7875251 : Blo 1228432 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B8096435 : Blo 1228432 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B8866577 : Blo 1228432 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B6220637 : Blo 1228432 6220637 := bstep (se 3 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 6220637 = 2332739) B2332739
theorem B4148171 : Blo 1228432 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B1313815 : Blo 1228432 1313815 := bstep (se 1 (by rfl) ⟨985361, by rfl⟩ : syracuseStep 1313815 = 1970723) B1970723
theorem B2624537 : Blo 1228432 2624537 := bstep (se 2 (by rfl) ⟨984201, by rfl⟩ : syracuseStep 2624537 = 1968403) B1968403
theorem B4664537 : Blo 1228432 4664537 := bstep (se 2 (by rfl) ⟨1749201, by rfl⟩ : syracuseStep 4664537 = 3498403) B3498403
theorem B4148441 : Blo 1228432 4148441 := bstep (se 2 (by rfl) ⟨1555665, by rfl⟩ : syracuseStep 4148441 = 3111331) B3111331
theorem B2764043 : Blo 1228432 2764043 := bstep (se 1 (by rfl) ⟨2073032, by rfl⟩ : syracuseStep 2764043 = 4146065) B4146065
theorem B2075915 : Blo 1228432 2075915 := bstep (se 1 (by rfl) ⟨1556936, by rfl⟩ : syracuseStep 2075915 = 3113873) B3113873
theorem B2764097 : Blo 1228432 2764097 := bstep (se 2 (by rfl) ⟨1036536, by rfl⟩ : syracuseStep 2764097 = 2073073) B2073073
theorem B3501377 : Blo 1228432 3501377 := bstep (se 2 (by rfl) ⟨1313016, by rfl⟩ : syracuseStep 3501377 = 2626033) B2626033
theorem B2076043 : Blo 1228432 2076043 := bstep (se 1 (by rfl) ⟨1557032, by rfl⟩ : syracuseStep 2076043 = 3114065) B3114065
theorem B3739031 : Blo 1228432 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B4664749 : Blo 1228432 4664749 := bstep (se 3 (by rfl) ⟨874640, by rfl⟩ : syracuseStep 4664749 = 1749281) B1749281
theorem B2764313 : Blo 1228432 2764313 := bstep (se 2 (by rfl) ⟨1036617, by rfl⟩ : syracuseStep 2764313 = 2073235) B2073235
theorem B2076185 : Blo 1228432 2076185 := bstep (se 2 (by rfl) ⟨778569, by rfl⟩ : syracuseStep 2076185 = 1557139) B1557139
theorem B2764403 : Blo 1228432 2764403 := bstep (se 1 (by rfl) ⟨2073302, by rfl⟩ : syracuseStep 2764403 = 4146605) B4146605
theorem B2764439 : Blo 1228432 2764439 := bstep (se 1 (by rfl) ⟨2073329, by rfl⟩ : syracuseStep 2764439 = 4146659) B4146659
theorem B2076313 : Blo 1228432 2076313 := bstep (se 2 (by rfl) ⟨778617, by rfl⟩ : syracuseStep 2076313 = 1557235) B1557235
theorem B4665053 : Blo 1228432 4665053 := bstep (se 3 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 4665053 = 1749395) B1749395
theorem B2625281 : Blo 1228432 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B2764619 : Blo 1228432 2764619 := bstep (se 1 (by rfl) ⟨2073464, by rfl⟩ : syracuseStep 2764619 = 4146929) B4146929
theorem B2764673 : Blo 1228432 2764673 := bstep (se 2 (by rfl) ⟨1036752, by rfl⟩ : syracuseStep 2764673 = 2073505) B2073505
theorem B4149143 : Blo 1228432 4149143 := bstep (se 1 (by rfl) ⟨3111857, by rfl⟩ : syracuseStep 4149143 = 6223715) B6223715
theorem B11972569 : Blo 1228432 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B3321931 : Blo 1228432 3321931 := bstep (se 1 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 3321931 = 4982897) B4982897
theorem B2216011 : Blo 1228432 2216011 := bstep (se 1 (by rfl) ⟨1662008, by rfl⟩ : syracuseStep 2216011 = 3324017) B3324017
theorem B2764889 : Blo 1228432 2764889 := bstep (se 2 (by rfl) ⟨1036833, by rfl⟩ : syracuseStep 2764889 = 2073667) B2073667
theorem B2764979 : Blo 1228432 2764979 := bstep (se 1 (by rfl) ⟨2073734, by rfl⟩ : syracuseStep 2764979 = 4147469) B4147469
theorem B2765015 : Blo 1228432 2765015 := bstep (se 1 (by rfl) ⟨2073761, by rfl⟩ : syracuseStep 2765015 = 4147523) B4147523
theorem B15749477 : Blo 1228432 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B7000451 : Blo 1228432 7000451 := bstep (se 1 (by rfl) ⟨5250338, by rfl⟩ : syracuseStep 7000451 = 10500677) B10500677
theorem B2765195 : Blo 1228432 2765195 := bstep (se 1 (by rfl) ⟨2073896, by rfl⟩ : syracuseStep 2765195 = 4147793) B4147793
theorem B3936691 : Blo 1228432 3936691 := bstep (se 1 (by rfl) ⟨2952518, by rfl⟩ : syracuseStep 3936691 = 5905037) B5905037
theorem B4149683 : Blo 1228432 4149683 := bstep (se 1 (by rfl) ⟨3112262, by rfl⟩ : syracuseStep 4149683 = 6224525) B6224525
theorem B2216371 : Blo 1228432 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B2765249 : Blo 1228432 2765249 := bstep (se 2 (by rfl) ⟨1036968, by rfl⟩ : syracuseStep 2765249 = 2073937) B2073937
theorem B8417753 : Blo 1228432 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B2101783 : Blo 1228432 2101783 := bstep (se 1 (by rfl) ⟨1576337, by rfl⟩ : syracuseStep 2101783 = 3152675) B3152675
theorem B3936833 : Blo 1228432 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B18199133 : Blo 1228432 18199133 := bstep (se 3 (by rfl) ⟨3412337, by rfl⟩ : syracuseStep 18199133 = 6824675) B6824675
theorem B2626177 : Blo 1228432 2626177 := bstep (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) B1969633
theorem B4985489 : Blo 1228432 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B2765465 : Blo 1228432 2765465 := bstep (se 2 (by rfl) ⟨1037049, by rfl⟩ : syracuseStep 2765465 = 2074099) B2074099
theorem B4149953 : Blo 1228432 4149953 := bstep (se 2 (by rfl) ⟨1556232, by rfl⟩ : syracuseStep 4149953 = 3112465) B3112465
theorem B2765555 : Blo 1228432 2765555 := bstep (se 1 (by rfl) ⟨2074166, by rfl⟩ : syracuseStep 2765555 = 4148333) B4148333
theorem B9966341 : Blo 1228432 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2765591 : Blo 1228432 2765591 := bstep (se 1 (by rfl) ⟨2074193, by rfl⟩ : syracuseStep 2765591 = 4148387) B4148387
theorem B10498967 : Blo 1228432 10498967 := bstep (se 1 (by rfl) ⟨7874225, by rfl⟩ : syracuseStep 10498967 = 15748451) B15748451
theorem B6222743 : Blo 1228432 6222743 := bstep (se 1 (by rfl) ⟨4667057, by rfl⟩ : syracuseStep 6222743 = 9334115) B9334115
theorem B10097585 : Blo 1228432 10097585 := bstep (se 2 (by rfl) ⟨3786594, by rfl⟩ : syracuseStep 10097585 = 7573189) B7573189
theorem B3503027 : Blo 1228432 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B5682113 : Blo 1228432 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B2765771 : Blo 1228432 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B3503051 : Blo 1228432 3503051 := bstep (se 1 (by rfl) ⟨2627288, by rfl⟩ : syracuseStep 3503051 = 5254577) B5254577
theorem B2626519 : Blo 1228432 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B2765825 : Blo 1228432 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B7574573 : Blo 1228432 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B7984259 : Blo 1228432 7984259 := bstep (se 1 (by rfl) ⟨5988194, by rfl⟩ : syracuseStep 7984259 = 11976389) B11976389
theorem B10507441 : Blo 1228432 10507441 := bstep (se 2 (by rfl) ⟨3940290, by rfl⟩ : syracuseStep 10507441 = 7880581) B7880581
theorem B2766041 : Blo 1228432 2766041 := bstep (se 2 (by rfl) ⟨1037265, by rfl⟩ : syracuseStep 2766041 = 2074531) B2074531
theorem B4150493 : Blo 1228432 4150493 := bstep (se 3 (by rfl) ⟨778217, by rfl⟩ : syracuseStep 4150493 = 1556435) B1556435
theorem B1750295 : Blo 1228432 1750295 := bstep (se 1 (by rfl) ⟨1312721, by rfl⟩ : syracuseStep 1750295 = 2625443) B2625443
theorem B2954519 : Blo 1228432 2954519 := bstep (se 1 (by rfl) ⟨2215889, by rfl⟩ : syracuseStep 2954519 = 4431779) B4431779
theorem B2766131 : Blo 1228432 2766131 := bstep (se 1 (by rfl) ⟨2074598, by rfl⟩ : syracuseStep 2766131 = 4149197) B4149197
theorem B2766167 : Blo 1228432 2766167 := bstep (se 1 (by rfl) ⟨2074625, by rfl⟩ : syracuseStep 2766167 = 4149251) B4149251
theorem B39892337 : Blo 1228432 39892337 := bstep (se 2 (by rfl) ⟨14959626, by rfl⟩ : syracuseStep 39892337 = 29919253) B29919253
theorem B7878019 : Blo 1228432 7878019 := bstep (se 1 (by rfl) ⟨5908514, by rfl⟩ : syracuseStep 7878019 = 11817029) B11817029
theorem B17724851 : Blo 1228432 17724851 := bstep (se 1 (by rfl) ⟨13293638, by rfl⟩ : syracuseStep 17724851 = 26587277) B26587277
theorem B2332147 : Blo 1228432 2332147 := bstep (se 1 (by rfl) ⟨1749110, by rfl⟩ : syracuseStep 2332147 = 3498221) B3498221
theorem B2766347 : Blo 1228432 2766347 := bstep (se 1 (by rfl) ⟨2074760, by rfl⟩ : syracuseStep 2766347 = 4149521) B4149521
theorem B2627083 : Blo 1228432 2627083 := bstep (se 1 (by rfl) ⟨1970312, by rfl⟩ : syracuseStep 2627083 = 3940625) B3940625
theorem B2766401 : Blo 1228432 2766401 := bstep (se 2 (by rfl) ⟨1037400, by rfl⟩ : syracuseStep 2766401 = 2074801) B2074801
theorem B5912129 : Blo 1228432 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B1382071 : Blo 1228432 1382071 := bstep (se 1 (by rfl) ⟨1036553, by rfl⟩ : syracuseStep 1382071 = 2073107) B2073107
theorem B5912281 : Blo 1228432 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B3503837 : Blo 1228432 3503837 := bstep (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) B1313939
theorem B2766617 : Blo 1228432 2766617 := bstep (se 2 (by rfl) ⟨1037481, by rfl⟩ : syracuseStep 2766617 = 2074963) B2074963
theorem B1382251 : Blo 1228432 1382251 := bstep (se 1 (by rfl) ⟨1036688, by rfl⟩ : syracuseStep 1382251 = 2073377) B2073377
theorem B2766707 : Blo 1228432 2766707 := bstep (se 1 (by rfl) ⟨2075030, by rfl⟩ : syracuseStep 2766707 = 4150061) B4150061
theorem B2766743 : Blo 1228432 2766743 := bstep (se 1 (by rfl) ⟨2075057, by rfl⟩ : syracuseStep 2766743 = 4150115) B4150115
theorem B100931507 : Blo 1228432 100931507 := bstep (se 1 (by rfl) ⟨75698630, by rfl⟩ : syracuseStep 100931507 = 151397261) B151397261
theorem B1382359 : Blo 1228432 1382359 := bstep (se 1 (by rfl) ⟨1036769, by rfl⟩ : syracuseStep 1382359 = 2073539) B2073539
theorem B2332633 : Blo 1228432 2332633 := bstep (se 2 (by rfl) ⟨874737, by rfl⟩ : syracuseStep 2332633 = 1749475) B1749475
theorem B8091665 : Blo 1228432 8091665 := bstep (se 2 (by rfl) ⟨3034374, by rfl⟩ : syracuseStep 8091665 = 6068749) B6068749
theorem B4732951 : Blo 1228432 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B2955287 : Blo 1228432 2955287 := bstep (se 1 (by rfl) ⟨2216465, by rfl⟩ : syracuseStep 2955287 = 4432931) B4432931
theorem B3110987 : Blo 1228432 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B2766923 : Blo 1228432 2766923 := bstep (se 1 (by rfl) ⟨2075192, by rfl⟩ : syracuseStep 2766923 = 4150385) B4150385
theorem B2103383 : Blo 1228432 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B2766977 : Blo 1228432 2766977 := bstep (se 2 (by rfl) ⟨1037616, by rfl⟩ : syracuseStep 2766977 = 2075233) B2075233
theorem B1382539 : Blo 1228432 1382539 := bstep (se 1 (by rfl) ⟨1036904, by rfl⟩ : syracuseStep 1382539 = 2073809) B2073809
theorem B5609645 : Blo 1228432 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B5249245 : Blo 1228432 5249245 := bstep (se 3 (by rfl) ⟨984233, by rfl⟩ : syracuseStep 5249245 = 1968467) B1968467
theorem B1382647 : Blo 1228432 1382647 := bstep (se 1 (by rfl) ⟨1036985, by rfl⟩ : syracuseStep 1382647 = 2073971) B2073971
theorem B4667651 : Blo 1228432 4667651 := bstep (se 1 (by rfl) ⟨3500738, by rfl⟩ : syracuseStep 4667651 = 7001477) B7001477
theorem B4667665 : Blo 1228432 4667665 := bstep (se 2 (by rfl) ⟨1750374, by rfl⟩ : syracuseStep 4667665 = 3500749) B3500749
theorem B4151627 : Blo 1228432 4151627 := bstep (se 1 (by rfl) ⟨3113720, by rfl⟩ : syracuseStep 4151627 = 6227441) B6227441
theorem B2767193 : Blo 1228432 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1382827 : Blo 1228432 1382827 := bstep (se 1 (by rfl) ⟨1037120, by rfl⟩ : syracuseStep 1382827 = 2074241) B2074241
theorem B2767283 : Blo 1228432 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B3938753 : Blo 1228432 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B2767319 : Blo 1228432 2767319 := bstep (se 1 (by rfl) ⟨2075489, by rfl⟩ : syracuseStep 2767319 = 4150979) B4150979
theorem B8862169 : Blo 1228432 8862169 := bstep (se 2 (by rfl) ⟨3323313, by rfl⟩ : syracuseStep 8862169 = 6646627) B6646627
theorem B2103769 : Blo 1228432 2103769 := bstep (se 2 (by rfl) ⟨788913, by rfl⟩ : syracuseStep 2103769 = 1577827) B1577827
theorem B2333195 : Blo 1228432 2333195 := bstep (se 1 (by rfl) ⟨1749896, by rfl⟩ : syracuseStep 2333195 = 3499793) B3499793
theorem B1554967 : Blo 1228432 1554967 := bstep (se 1 (by rfl) ⟨1166225, by rfl⟩ : syracuseStep 1554967 = 2332451) B2332451
theorem B1382935 : Blo 1228432 1382935 := bstep (se 1 (by rfl) ⟨1037201, by rfl⟩ : syracuseStep 1382935 = 2074403) B2074403
theorem B4667969 : Blo 1228432 4667969 := bstep (se 2 (by rfl) ⟨1750488, by rfl⟩ : syracuseStep 4667969 = 3500977) B3500977
theorem B4151897 : Blo 1228432 4151897 := bstep (se 2 (by rfl) ⟨1556961, by rfl⟩ : syracuseStep 4151897 = 3113923) B3113923
theorem B2767499 : Blo 1228432 2767499 := bstep (se 1 (by rfl) ⟨2075624, by rfl⟩ : syracuseStep 2767499 = 4151249) B4151249
theorem B2333377 : Blo 1228432 2333377 := bstep (se 2 (by rfl) ⟨875016, by rfl⟩ : syracuseStep 2333377 = 1750033) B1750033
theorem B2767553 : Blo 1228432 2767553 := bstep (se 2 (by rfl) ⟨1037832, by rfl⟩ : syracuseStep 2767553 = 2075665) B2075665
theorem B1383115 : Blo 1228432 1383115 := bstep (se 1 (by rfl) ⟨1037336, by rfl⟩ : syracuseStep 1383115 = 2074673) B2074673
theorem B15964933 : Blo 1228432 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B1383223 : Blo 1228432 1383223 := bstep (se 1 (by rfl) ⟨1037417, by rfl⟩ : syracuseStep 1383223 = 2074835) B2074835
theorem B2767769 : Blo 1228432 2767769 := bstep (se 2 (by rfl) ⟨1037913, by rfl⟩ : syracuseStep 2767769 = 2075827) B2075827
theorem B3939293 : Blo 1228432 3939293 := bstep (se 3 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 3939293 = 1477235) B1477235
theorem B1383403 : Blo 1228432 1383403 := bstep (se 1 (by rfl) ⟨1037552, by rfl⟩ : syracuseStep 1383403 = 2075105) B2075105
theorem B2767859 : Blo 1228432 2767859 := bstep (se 1 (by rfl) ⟨2075894, by rfl⟩ : syracuseStep 2767859 = 4151789) B4151789
theorem B11222021 : Blo 1228432 11222021 := bstep (se 4 (by rfl) ⟨1052064, by rfl⟩ : syracuseStep 11222021 = 2104129) B2104129
theorem B3111959 : Blo 1228432 3111959 := bstep (se 1 (by rfl) ⟨2333969, by rfl⟩ : syracuseStep 3111959 = 4667939) B4667939
theorem B2767895 : Blo 1228432 2767895 := bstep (se 1 (by rfl) ⟨2075921, by rfl⟩ : syracuseStep 2767895 = 4151843) B4151843
theorem B42581027 : Blo 1228432 42581027 := bstep (se 1 (by rfl) ⟨31935770, by rfl⟩ : syracuseStep 42581027 = 63871541) B63871541
theorem B1383511 : Blo 1228432 1383511 := bstep (se 1 (by rfl) ⟨1037633, by rfl⟩ : syracuseStep 1383511 = 2075267) B2075267
theorem B2768075 : Blo 1228432 2768075 := bstep (se 1 (by rfl) ⟨2076056, by rfl⟩ : syracuseStep 2768075 = 4152113) B4152113
theorem B4668637 : Blo 1228432 4668637 := bstep (se 3 (by rfl) ⟨875369, by rfl⟩ : syracuseStep 4668637 = 1750739) B1750739
theorem B2768129 : Blo 1228432 2768129 := bstep (se 2 (by rfl) ⟨1038048, by rfl⟩ : syracuseStep 2768129 = 2076097) B2076097
theorem B1383691 : Blo 1228432 1383691 := bstep (se 1 (by rfl) ⟨1037768, by rfl⟩ : syracuseStep 1383691 = 2075537) B2075537
theorem B4152599 : Blo 1228432 4152599 := bstep (se 1 (by rfl) ⟨3114449, by rfl⟩ : syracuseStep 4152599 = 6228899) B6228899
theorem B1555787 : Blo 1228432 1555787 := bstep (se 1 (by rfl) ⟨1166840, by rfl⟩ : syracuseStep 1555787 = 2333681) B2333681
theorem B1383799 : Blo 1228432 1383799 := bstep (se 1 (by rfl) ⟨1037849, by rfl⟩ : syracuseStep 1383799 = 2075699) B2075699
theorem B2334091 : Blo 1228432 2334091 := bstep (se 1 (by rfl) ⟨1750568, by rfl⟩ : syracuseStep 2334091 = 3501137) B3501137
theorem B2334167 : Blo 1228432 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B2768345 : Blo 1228432 2768345 := bstep (se 2 (by rfl) ⟨1038129, by rfl⟩ : syracuseStep 2768345 = 2076259) B2076259
theorem B8855045 : Blo 1228432 8855045 := bstep (se 4 (by rfl) ⟨830160, by rfl⟩ : syracuseStep 8855045 = 1660321) B1660321
theorem B5250577 : Blo 1228432 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B1842713 : Blo 1228432 1842713 := bstep (se 2 (by rfl) ⟨691017, by rfl⟩ : syracuseStep 1842713 = 1382035) B1382035
theorem B17956387 : Blo 1228432 17956387 := bstep (se 1 (by rfl) ⟨13467290, by rfl⟩ : syracuseStep 17956387 = 26934581) B26934581
theorem B1383979 : Blo 1228432 1383979 := bstep (se 1 (by rfl) ⟨1037984, by rfl⟩ : syracuseStep 1383979 = 2075969) B2075969
theorem B2768435 : Blo 1228432 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B2768471 : Blo 1228432 2768471 := bstep (se 1 (by rfl) ⟨2076353, by rfl⟩ : syracuseStep 2768471 = 4152707) B4152707
theorem B1842827 : Blo 1228432 1842827 := bstep (se 1 (by rfl) ⟨1382120, by rfl⟩ : syracuseStep 1842827 = 2764241) B2764241
theorem B1228439 : Blo 1228432 1228439 := bstep (se 1 (by rfl) ⟨921329, by rfl⟩ : syracuseStep 1228439 = 1842659) B1842659
theorem B1842839 : Blo 1228432 1842839 := bstep (se 1 (by rfl) ⟨1382129, by rfl⟩ : syracuseStep 1842839 = 2764259) B2764259
theorem B1384087 : Blo 1228432 1384087 := bstep (se 1 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 1384087 = 2076131) B2076131
theorem B1228459 : Blo 1228432 1228459 := bstep (se 1 (by rfl) ⟨921344, by rfl⟩ : syracuseStep 1228459 = 1842689) B1842689
theorem B3112627 : Blo 1228432 3112627 := bstep (se 1 (by rfl) ⟨2334470, by rfl⟩ : syracuseStep 3112627 = 4668941) B4668941
theorem B1228471 : Blo 1228432 1228471 := bstep (se 1 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 1228471 = 1842707) B1842707
theorem B1228491 : Blo 1228432 1228491 := bstep (se 1 (by rfl) ⟨921368, by rfl⟩ : syracuseStep 1228491 = 1842737) B1842737
theorem B1228503 : Blo 1228432 1228503 := bstep (se 1 (by rfl) ⟨921377, by rfl⟩ : syracuseStep 1228503 = 1842755) B1842755
theorem B1842905 : Blo 1228432 1842905 := bstep (se 2 (by rfl) ⟨691089, by rfl⟩ : syracuseStep 1842905 = 1382179) B1382179
theorem B1228523 : Blo 1228432 1228523 := bstep (se 1 (by rfl) ⟨921392, by rfl⟩ : syracuseStep 1228523 = 1842785) B1842785
theorem B1228535 : Blo 1228432 1228535 := bstep (se 1 (by rfl) ⟨921401, by rfl⟩ : syracuseStep 1228535 = 1842803) B1842803
theorem B1228555 : Blo 1228432 1228555 := bstep (se 1 (by rfl) ⟨921416, by rfl⟩ : syracuseStep 1228555 = 1842833) B1842833
theorem B9969425 : Blo 1228432 9969425 := bstep (se 2 (by rfl) ⟨3738534, by rfl⟩ : syracuseStep 9969425 = 7477069) B7477069
theorem B1228567 : Blo 1228432 1228567 := bstep (se 1 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 1228567 = 1842851) B1842851
theorem B1228587 : Blo 1228432 1228587 := bstep (se 1 (by rfl) ⟨921440, by rfl⟩ : syracuseStep 1228587 = 1842881) B1842881
theorem B1228599 : Blo 1228432 1228599 := bstep (se 1 (by rfl) ⟨921449, by rfl⟩ : syracuseStep 1228599 = 1842899) B1842899
theorem B3112769 : Blo 1228432 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B1228619 : Blo 1228432 1228619 := bstep (se 1 (by rfl) ⟨921464, by rfl⟩ : syracuseStep 1228619 = 1842929) B1842929
theorem B1843019 : Blo 1228432 1843019 := bstep (se 1 (by rfl) ⟨1382264, by rfl⟩ : syracuseStep 1843019 = 2764529) B2764529
theorem B1228631 : Blo 1228432 1228631 := bstep (se 1 (by rfl) ⟨921473, by rfl⟩ : syracuseStep 1228631 = 1842947) B1842947
theorem B1843031 : Blo 1228432 1843031 := bstep (se 1 (by rfl) ⟨1382273, by rfl⟩ : syracuseStep 1843031 = 2764547) B2764547
theorem B3325789 : Blo 1228432 3325789 := bstep (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) B1247171
theorem B1228651 : Blo 1228432 1228651 := bstep (se 1 (by rfl) ⟨921488, by rfl⟩ : syracuseStep 1228651 = 1842977) B1842977
theorem B1228663 : Blo 1228432 1228663 := bstep (se 1 (by rfl) ⟨921497, by rfl⟩ : syracuseStep 1228663 = 1842995) B1842995
theorem B1228683 : Blo 1228432 1228683 := bstep (se 1 (by rfl) ⟨921512, by rfl⟩ : syracuseStep 1228683 = 1843025) B1843025
theorem B1228695 : Blo 1228432 1228695 := bstep (se 1 (by rfl) ⟨921521, by rfl⟩ : syracuseStep 1228695 = 1843043) B1843043
theorem B1843097 : Blo 1228432 1843097 := bstep (se 2 (by rfl) ⟨691161, by rfl⟩ : syracuseStep 1843097 = 1382323) B1382323
theorem B1228715 : Blo 1228432 1228715 := bstep (se 1 (by rfl) ⟨921536, by rfl⟩ : syracuseStep 1228715 = 1843073) B1843073
theorem B1228727 : Blo 1228432 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B2244545 : Blo 1228432 2244545 := bstep (se 2 (by rfl) ⟨841704, by rfl⟩ : syracuseStep 2244545 = 1683409) B1683409
theorem B1228747 : Blo 1228432 1228747 := bstep (se 1 (by rfl) ⟨921560, by rfl⟩ : syracuseStep 1228747 = 1843121) B1843121
theorem B1228759 : Blo 1228432 1228759 := bstep (se 1 (by rfl) ⟨921569, by rfl⟩ : syracuseStep 1228759 = 1843139) B1843139
theorem B1228779 : Blo 1228432 1228779 := bstep (se 1 (by rfl) ⟨921584, by rfl⟩ : syracuseStep 1228779 = 1843169) B1843169
theorem B1228791 : Blo 1228432 1228791 := bstep (se 1 (by rfl) ⟨921593, by rfl⟩ : syracuseStep 1228791 = 1843187) B1843187
theorem B1228807 : Blo 1228432 1228807 := bstep (se 1 (by rfl) ⟨921605, by rfl⟩ : syracuseStep 1228807 = 1843211) B1843211
theorem B1228815 : Blo 1228432 1228815 := bstep (se 1 (by rfl) ⟨921611, by rfl⟩ : syracuseStep 1228815 = 1843223) B1843223
theorem B29925389 : Blo 1228432 29925389 := bstep (se 3 (by rfl) ⟨5611010, by rfl⟩ : syracuseStep 29925389 = 11222021) B11222021
theorem B1843259 : Blo 1228432 1843259 := bstep (se 1 (by rfl) ⟨1382444, by rfl⟩ : syracuseStep 1843259 = 2764889) B2764889
theorem B1228859 : Blo 1228432 1228859 := bstep (se 1 (by rfl) ⟨921644, by rfl⟩ : syracuseStep 1228859 = 1843289) B1843289
theorem B1843319 : Blo 1228432 1843319 := bstep (se 1 (by rfl) ⟨1382489, by rfl⟩ : syracuseStep 1843319 = 2764979) B2764979
theorem B1228935 : Blo 1228432 1228935 := bstep (se 1 (by rfl) ⟨921701, by rfl⟩ : syracuseStep 1228935 = 1843403) B1843403
theorem B1843343 : Blo 1228432 1843343 := bstep (se 1 (by rfl) ⟨1382507, by rfl⟩ : syracuseStep 1843343 = 2765015) B2765015
theorem B1228943 : Blo 1228432 1228943 := bstep (se 1 (by rfl) ⟨921707, by rfl⟩ : syracuseStep 1228943 = 1843415) B1843415
theorem B2490515 : Blo 1228432 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B2244755 : Blo 1228432 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B3113113 : Blo 1228432 3113113 := bstep (se 2 (by rfl) ⟨1167417, by rfl⟩ : syracuseStep 3113113 = 2334835) B2334835
theorem B1843385 : Blo 1228432 1843385 := bstep (se 2 (by rfl) ⟨691269, by rfl⟩ : syracuseStep 1843385 = 1382539) B1382539
theorem B1228987 : Blo 1228432 1228987 := bstep (se 1 (by rfl) ⟨921740, by rfl⟩ : syracuseStep 1228987 = 1843481) B1843481
theorem B1843463 : Blo 1228432 1843463 := bstep (se 1 (by rfl) ⟨1382597, by rfl⟩ : syracuseStep 1843463 = 2765195) B2765195
theorem B1229063 : Blo 1228432 1229063 := bstep (se 1 (by rfl) ⟨921797, by rfl⟩ : syracuseStep 1229063 = 1843595) B1843595
theorem B1229071 : Blo 1228432 1229071 := bstep (se 1 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 1229071 = 1843607) B1843607
theorem B1843499 : Blo 1228432 1843499 := bstep (se 1 (by rfl) ⟨1382624, by rfl⟩ : syracuseStep 1843499 = 2765249) B2765249
theorem B1229115 : Blo 1228432 1229115 := bstep (se 1 (by rfl) ⟨921836, by rfl⟩ : syracuseStep 1229115 = 1843673) B1843673
theorem B3113275 : Blo 1228432 3113275 := bstep (se 1 (by rfl) ⟨2334956, by rfl⟩ : syracuseStep 3113275 = 4669913) B4669913
theorem B5611835 : Blo 1228432 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B1843529 : Blo 1228432 1843529 := bstep (se 2 (by rfl) ⟨691323, by rfl⟩ : syracuseStep 1843529 = 1382647) B1382647
theorem B2490743 : Blo 1228432 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B1229191 : Blo 1228432 1229191 := bstep (se 1 (by rfl) ⟨921893, by rfl⟩ : syracuseStep 1229191 = 1843787) B1843787
theorem B1229199 : Blo 1228432 1229199 := bstep (se 1 (by rfl) ⟨921899, by rfl⟩ : syracuseStep 1229199 = 1843799) B1843799
theorem B12132755 : Blo 1228432 12132755 := bstep (se 1 (by rfl) ⟨9099566, by rfl⟩ : syracuseStep 12132755 = 18199133) B18199133
theorem B1843643 : Blo 1228432 1843643 := bstep (se 1 (by rfl) ⟨1382732, by rfl⟩ : syracuseStep 1843643 = 2765465) B2765465
theorem B1229243 : Blo 1228432 1229243 := bstep (se 1 (by rfl) ⟨921932, by rfl⟩ : syracuseStep 1229243 = 1843865) B1843865
theorem B3113417 : Blo 1228432 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B26567129 : Blo 1228432 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B1843703 : Blo 1228432 1843703 := bstep (se 1 (by rfl) ⟨1382777, by rfl⟩ : syracuseStep 1843703 = 2765555) B2765555
theorem B6644227 : Blo 1228432 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1229319 : Blo 1228432 1229319 := bstep (se 1 (by rfl) ⟨921989, by rfl⟩ : syracuseStep 1229319 = 1843979) B1843979
theorem B1843727 : Blo 1228432 1843727 := bstep (se 1 (by rfl) ⟨1382795, by rfl⟩ : syracuseStep 1843727 = 2765591) B2765591
theorem B1229327 : Blo 1228432 1229327 := bstep (se 1 (by rfl) ⟨921995, by rfl⟩ : syracuseStep 1229327 = 1843991) B1843991
theorem B1843769 : Blo 1228432 1843769 := bstep (se 2 (by rfl) ⟨691413, by rfl⟩ : syracuseStep 1843769 = 1382827) B1382827
theorem B1229371 : Blo 1228432 1229371 := bstep (se 1 (by rfl) ⟨922028, by rfl⟩ : syracuseStep 1229371 = 1844057) B1844057
theorem B1843847 : Blo 1228432 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B1229447 : Blo 1228432 1229447 := bstep (se 1 (by rfl) ⟨922085, by rfl⟩ : syracuseStep 1229447 = 1844171) B1844171
theorem B2335367 : Blo 1228432 2335367 := bstep (se 1 (by rfl) ⟨1751525, by rfl⟩ : syracuseStep 2335367 = 3503051) B3503051
theorem B1229455 : Blo 1228432 1229455 := bstep (se 1 (by rfl) ⟨922091, by rfl⟩ : syracuseStep 1229455 = 1844183) B1844183
theorem B1843883 : Blo 1228432 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B1229499 : Blo 1228432 1229499 := bstep (se 1 (by rfl) ⟨922124, by rfl⟩ : syracuseStep 1229499 = 1844249) B1844249
theorem B2073289 : Blo 1228432 2073289 := bstep (se 2 (by rfl) ⟨777483, by rfl⟩ : syracuseStep 2073289 = 1554967) B1554967
theorem B2802377 : Blo 1228432 2802377 := bstep (se 2 (by rfl) ⟨1050891, by rfl⟩ : syracuseStep 2802377 = 2101783) B2101783
theorem B1868489 : Blo 1228432 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B1843913 : Blo 1228432 1843913 := bstep (se 2 (by rfl) ⟨691467, by rfl⟩ : syracuseStep 1843913 = 1382935) B1382935
theorem B1229575 : Blo 1228432 1229575 := bstep (se 1 (by rfl) ⟨922181, by rfl⟩ : syracuseStep 1229575 = 1844363) B1844363
theorem B1229583 : Blo 1228432 1229583 := bstep (se 1 (by rfl) ⟨922187, by rfl⟩ : syracuseStep 1229583 = 1844375) B1844375
theorem B3113761 : Blo 1228432 3113761 := bstep (se 2 (by rfl) ⟨1167660, by rfl⟩ : syracuseStep 3113761 = 2335321) B2335321
theorem B1844027 : Blo 1228432 1844027 := bstep (se 1 (by rfl) ⟨1383020, by rfl⟩ : syracuseStep 1844027 = 2766041) B2766041
theorem B1229627 : Blo 1228432 1229627 := bstep (se 1 (by rfl) ⟨922220, by rfl⟩ : syracuseStep 1229627 = 1844441) B1844441
theorem B6996851 : Blo 1228432 6996851 := bstep (se 1 (by rfl) ⟨5247638, by rfl⟩ : syracuseStep 6996851 = 10495277) B10495277
theorem B1844087 : Blo 1228432 1844087 := bstep (se 1 (by rfl) ⟨1383065, by rfl⟩ : syracuseStep 1844087 = 2766131) B2766131
theorem B1229703 : Blo 1228432 1229703 := bstep (se 1 (by rfl) ⟨922277, by rfl⟩ : syracuseStep 1229703 = 1844555) B1844555
theorem B1844111 : Blo 1228432 1844111 := bstep (se 1 (by rfl) ⟨1383083, by rfl⟩ : syracuseStep 1844111 = 2766167) B2766167
theorem B1229711 : Blo 1228432 1229711 := bstep (se 1 (by rfl) ⟨922283, by rfl⟩ : syracuseStep 1229711 = 1844567) B1844567
theorem B1844153 : Blo 1228432 1844153 := bstep (se 2 (by rfl) ⟨691557, by rfl⟩ : syracuseStep 1844153 = 1383115) B1383115
theorem B1229755 : Blo 1228432 1229755 := bstep (se 1 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 1229755 = 1844633) B1844633
theorem B9962443 : Blo 1228432 9962443 := bstep (se 1 (by rfl) ⟨7471832, by rfl⟩ : syracuseStep 9962443 = 14943665) B14943665
theorem B1844231 : Blo 1228432 1844231 := bstep (se 1 (by rfl) ⟨1383173, by rfl⟩ : syracuseStep 1844231 = 2766347) B2766347
theorem B1229831 : Blo 1228432 1229831 := bstep (se 1 (by rfl) ⟨922373, by rfl⟩ : syracuseStep 1229831 = 1844747) B1844747
theorem B6226955 : Blo 1228432 6226955 := bstep (se 1 (by rfl) ⟨4670216, by rfl⟩ : syracuseStep 6226955 = 9340433) B9340433
theorem B1229839 : Blo 1228432 1229839 := bstep (se 1 (by rfl) ⟨922379, by rfl⟩ : syracuseStep 1229839 = 1844759) B1844759
theorem B1844267 : Blo 1228432 1844267 := bstep (se 1 (by rfl) ⟨1383200, by rfl⟩ : syracuseStep 1844267 = 2766401) B2766401
theorem B3941419 : Blo 1228432 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B1229883 : Blo 1228432 1229883 := bstep (se 1 (by rfl) ⟨922412, by rfl⟩ : syracuseStep 1229883 = 1844825) B1844825
theorem B1844297 : Blo 1228432 1844297 := bstep (se 2 (by rfl) ⟨691611, by rfl⟩ : syracuseStep 1844297 = 1383223) B1383223
theorem B31532165 : Blo 1228432 31532165 := bstep (se 4 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 31532165 = 5912281) B5912281
theorem B1229959 : Blo 1228432 1229959 := bstep (se 1 (by rfl) ⟨922469, by rfl⟩ : syracuseStep 1229959 = 1844939) B1844939
theorem B1229967 : Blo 1228432 1229967 := bstep (se 1 (by rfl) ⟨922475, by rfl⟩ : syracuseStep 1229967 = 1844951) B1844951
theorem B2335891 : Blo 1228432 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B10503341 : Blo 1228432 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B6227117 : Blo 1228432 6227117 := bstep (se 3 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 6227117 = 2335169) B2335169
theorem B1844411 : Blo 1228432 1844411 := bstep (se 1 (by rfl) ⟨1383308, by rfl⟩ : syracuseStep 1844411 = 2766617) B2766617
theorem B1230011 : Blo 1228432 1230011 := bstep (se 1 (by rfl) ⟨922508, by rfl⟩ : syracuseStep 1230011 = 1845017) B1845017
theorem B1844471 : Blo 1228432 1844471 := bstep (se 1 (by rfl) ⟨1383353, by rfl⟩ : syracuseStep 1844471 = 2766707) B2766707
theorem B1230087 : Blo 1228432 1230087 := bstep (se 1 (by rfl) ⟨922565, by rfl⟩ : syracuseStep 1230087 = 1845131) B1845131
theorem B1844495 : Blo 1228432 1844495 := bstep (se 1 (by rfl) ⟨1383371, by rfl⟩ : syracuseStep 1844495 = 2766743) B2766743
theorem B1230095 : Blo 1228432 1230095 := bstep (se 1 (by rfl) ⟨922571, by rfl⟩ : syracuseStep 1230095 = 1845143) B1845143
theorem B1844537 : Blo 1228432 1844537 := bstep (se 2 (by rfl) ⟨691701, by rfl⟩ : syracuseStep 1844537 = 1383403) B1383403
theorem B1230139 : Blo 1228432 1230139 := bstep (se 1 (by rfl) ⟨922604, by rfl⟩ : syracuseStep 1230139 = 1845209) B1845209
theorem B3114359 : Blo 1228432 3114359 := bstep (se 1 (by rfl) ⟨2335769, by rfl⟩ : syracuseStep 3114359 = 4671539) B4671539
theorem B2073991 : Blo 1228432 2073991 := bstep (se 1 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 2073991 = 3110987) B3110987
theorem B1844615 : Blo 1228432 1844615 := bstep (se 1 (by rfl) ⟨1383461, by rfl⟩ : syracuseStep 1844615 = 2766923) B2766923
theorem B4670855 : Blo 1228432 4670855 := bstep (se 1 (by rfl) ⟨3503141, by rfl⟩ : syracuseStep 4670855 = 7006283) B7006283
theorem B1230215 : Blo 1228432 1230215 := bstep (se 1 (by rfl) ⟨922661, by rfl⟩ : syracuseStep 1230215 = 1845323) B1845323
theorem B1230223 : Blo 1228432 1230223 := bstep (se 1 (by rfl) ⟨922667, by rfl⟩ : syracuseStep 1230223 = 1845335) B1845335
theorem B1844651 : Blo 1228432 1844651 := bstep (se 1 (by rfl) ⟨1383488, by rfl⟩ : syracuseStep 1844651 = 2766977) B2766977
theorem B1230267 : Blo 1228432 1230267 := bstep (se 1 (by rfl) ⟨922700, by rfl⟩ : syracuseStep 1230267 = 1845401) B1845401
theorem B1844681 : Blo 1228432 1844681 := bstep (se 2 (by rfl) ⟨691755, by rfl⟩ : syracuseStep 1844681 = 1383511) B1383511
theorem B1230343 : Blo 1228432 1230343 := bstep (se 1 (by rfl) ⟨922757, by rfl⟩ : syracuseStep 1230343 = 1845515) B1845515
theorem B1230351 : Blo 1228432 1230351 := bstep (se 1 (by rfl) ⟨922763, by rfl⟩ : syracuseStep 1230351 = 1845527) B1845527
theorem B1844795 : Blo 1228432 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B1230395 : Blo 1228432 1230395 := bstep (se 1 (by rfl) ⟨922796, by rfl⟩ : syracuseStep 1230395 = 1845593) B1845593
theorem B14009921 : Blo 1228432 14009921 := bstep (se 2 (by rfl) ⟨5253720, by rfl⟩ : syracuseStep 14009921 = 10507441) B10507441
theorem B10643021 : Blo 1228432 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B1844855 : Blo 1228432 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B2492039 : Blo 1228432 2492039 := bstep (se 1 (by rfl) ⟨1869029, by rfl⟩ : syracuseStep 2492039 = 3738059) B3738059
theorem B1844879 : Blo 1228432 1844879 := bstep (se 1 (by rfl) ⟨1383659, by rfl⟩ : syracuseStep 1844879 = 2767319) B2767319
theorem B1844921 : Blo 1228432 1844921 := bstep (se 2 (by rfl) ⟨691845, by rfl⟩ : syracuseStep 1844921 = 1383691) B1383691
theorem B1844999 : Blo 1228432 1844999 := bstep (se 1 (by rfl) ⟨1383749, by rfl⟩ : syracuseStep 1844999 = 2767499) B2767499
theorem B1845035 : Blo 1228432 1845035 := bstep (se 1 (by rfl) ⟨1383776, by rfl⟩ : syracuseStep 1845035 = 2767553) B2767553
theorem B17737541 : Blo 1228432 17737541 := bstep (se 4 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 17737541 = 3325789) B3325789
theorem B1845065 : Blo 1228432 1845065 := bstep (se 2 (by rfl) ⟨691899, by rfl⟩ : syracuseStep 1845065 = 1383799) B1383799
theorem B10504025 : Blo 1228432 10504025 := bstep (se 2 (by rfl) ⟨3939009, by rfl⟩ : syracuseStep 10504025 = 7878019) B7878019
theorem B6219665 : Blo 1228432 6219665 := bstep (se 2 (by rfl) ⟨2332374, by rfl⟩ : syracuseStep 6219665 = 4664749) B4664749
theorem B4147091 : Blo 1228432 4147091 := bstep (se 1 (by rfl) ⟨3110318, by rfl⟩ : syracuseStep 4147091 = 6220637) B6220637
theorem B1845179 : Blo 1228432 1845179 := bstep (se 1 (by rfl) ⟨1383884, by rfl⟩ : syracuseStep 1845179 = 2767769) B2767769
theorem B1845239 : Blo 1228432 1845239 := bstep (se 1 (by rfl) ⟨1383929, by rfl⟩ : syracuseStep 1845239 = 2767859) B2767859
theorem B2074639 : Blo 1228432 2074639 := bstep (se 1 (by rfl) ⟨1555979, by rfl⟩ : syracuseStep 2074639 = 3111959) B3111959
theorem B1845263 : Blo 1228432 1845263 := bstep (se 1 (by rfl) ⟨1383947, by rfl⟩ : syracuseStep 1845263 = 2767895) B2767895
theorem B28387351 : Blo 1228432 28387351 := bstep (se 1 (by rfl) ⟨21290513, by rfl⟩ : syracuseStep 28387351 = 42581027) B42581027
theorem B1845305 : Blo 1228432 1845305 := bstep (se 2 (by rfl) ⟨691989, by rfl⟩ : syracuseStep 1845305 = 1383979) B1383979
theorem B1845383 : Blo 1228432 1845383 := bstep (se 1 (by rfl) ⟨1384037, by rfl⟩ : syracuseStep 1845383 = 2768075) B2768075
theorem B1845419 : Blo 1228432 1845419 := bstep (se 1 (by rfl) ⟨1384064, by rfl⟩ : syracuseStep 1845419 = 2768129) B2768129
theorem B1845449 : Blo 1228432 1845449 := bstep (se 2 (by rfl) ⟨692043, by rfl⟩ : syracuseStep 1845449 = 1384087) B1384087
theorem B2492687 : Blo 1228432 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B6998309 : Blo 1228432 6998309 := bstep (se 4 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 6998309 = 1312183) B1312183
theorem B1845563 : Blo 1228432 1845563 := bstep (se 1 (by rfl) ⟨1384172, by rfl⟩ : syracuseStep 1845563 = 2768345) B2768345
theorem B1845623 : Blo 1228432 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B1845647 : Blo 1228432 1845647 := bstep (se 1 (by rfl) ⟨1384235, by rfl⟩ : syracuseStep 1845647 = 2768471) B2768471
theorem B9341405 : Blo 1228432 9341405 := bstep (se 3 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 9341405 = 3503027) B3503027
theorem B6646283 : Blo 1228432 6646283 := bstep (se 1 (by rfl) ⟨4984712, by rfl⟩ : syracuseStep 6646283 = 9969425) B9969425
theorem B2075179 : Blo 1228432 2075179 := bstep (se 1 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 2075179 = 3112769) B3112769
theorem B2075321 : Blo 1228432 2075321 := bstep (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) B1556491
theorem B6310601 : Blo 1228432 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B6228737 : Blo 1228432 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B26585891 : Blo 1228432 26585891 := bstep (se 1 (by rfl) ⟨19939418, by rfl⟩ : syracuseStep 26585891 = 39878837) B39878837
theorem B7482149 : Blo 1228432 7482149 := bstep (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) B1402903
theorem B33631139 : Blo 1228432 33631139 := bstep (se 1 (by rfl) ⟨25223354, by rfl⟩ : syracuseStep 33631139 = 50446709) B50446709
theorem B4664249 : Blo 1228432 4664249 := bstep (se 2 (by rfl) ⟨1749093, by rfl⟩ : syracuseStep 4664249 = 3498187) B3498187
theorem B6998993 : Blo 1228432 6998993 := bstep (se 2 (by rfl) ⟨2624622, by rfl⟩ : syracuseStep 6998993 = 5249245) B5249245
theorem B2624555 : Blo 1228432 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B9972823 : Blo 1228432 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B6999311 : Blo 1228432 6999311 := bstep (se 1 (by rfl) ⟨5249483, by rfl⟩ : syracuseStep 6999311 = 10498967) B10498967
theorem B4148495 : Blo 1228432 4148495 := bstep (se 1 (by rfl) ⟨3111371, by rfl⟩ : syracuseStep 4148495 = 6222743) B6222743
theorem B11816225 : Blo 1228432 11816225 := bstep (se 2 (by rfl) ⟨4431084, by rfl⟩ : syracuseStep 11816225 = 8862169) B8862169
theorem B2805025 : Blo 1228432 2805025 := bstep (se 2 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 2805025 = 2103769) B2103769
theorem B3788075 : Blo 1228432 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B5049715 : Blo 1228432 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B2764151 : Blo 1228432 2764151 := bstep (se 1 (by rfl) ⟨2073113, by rfl⟩ : syracuseStep 2764151 = 4146227) B4146227
theorem B2076023 : Blo 1228432 2076023 := bstep (se 1 (by rfl) ⟨1557017, by rfl⟩ : syracuseStep 2076023 = 3114035) B3114035
theorem B3501569 : Blo 1228432 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B1969679 : Blo 1228432 1969679 := bstep (se 1 (by rfl) ⟨1477259, by rfl⟩ : syracuseStep 1969679 = 2954519) B2954519
theorem B4148765 : Blo 1228432 4148765 := bstep (se 3 (by rfl) ⟨777893, by rfl⟩ : syracuseStep 4148765 = 1555787) B1555787
theorem B2493985 : Blo 1228432 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B2764331 : Blo 1228432 2764331 := bstep (se 1 (by rfl) ⟨2073248, by rfl⟩ : syracuseStep 2764331 = 4146497) B4146497
theorem B26594891 : Blo 1228432 26594891 := bstep (se 1 (by rfl) ⟨19946168, by rfl⟩ : syracuseStep 26594891 = 39892337) B39892337
theorem B11816567 : Blo 1228432 11816567 := bstep (se 1 (by rfl) ⟨8862425, by rfl⟩ : syracuseStep 11816567 = 17724851) B17724851
theorem B21286577 : Blo 1228432 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B3739421 : Blo 1228432 3739421 := bstep (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) B1402283
theorem B4665235 : Blo 1228432 4665235 := bstep (se 1 (by rfl) ⟨3498926, by rfl⟩ : syracuseStep 4665235 = 6997853) B6997853
theorem B2764691 : Blo 1228432 2764691 := bstep (se 1 (by rfl) ⟨2073518, by rfl⟩ : syracuseStep 2764691 = 4147037) B4147037
theorem B2764745 : Blo 1228432 2764745 := bstep (se 2 (by rfl) ⟨1036779, by rfl⟩ : syracuseStep 2764745 = 2073559) B2073559
theorem B3502025 : Blo 1228432 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B6221771 : Blo 1228432 6221771 := bstep (se 1 (by rfl) ⟨4666328, by rfl⟩ : syracuseStep 6221771 = 9332657) B9332657
theorem B5394443 : Blo 1228432 5394443 := bstep (se 1 (by rfl) ⟨4045832, by rfl⟩ : syracuseStep 5394443 = 8091665) B8091665
theorem B1970191 : Blo 1228432 1970191 := bstep (se 1 (by rfl) ⟨1477643, by rfl⟩ : syracuseStep 1970191 = 2955287) B2955287
theorem B3739763 : Blo 1228432 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B6222095 : Blo 1228432 6222095 := bstep (se 1 (by rfl) ⟨4666571, by rfl⟩ : syracuseStep 6222095 = 9333143) B9333143
theorem B3502379 : Blo 1228432 3502379 := bstep (se 1 (by rfl) ⟨2626784, by rfl⟩ : syracuseStep 3502379 = 5253569) B5253569
theorem B1749367 : Blo 1228432 1749367 := bstep (se 1 (by rfl) ⟨1312025, by rfl⟩ : syracuseStep 1749367 = 2624051) B2624051
theorem B21303773 : Blo 1228432 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B5911051 : Blo 1228432 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B2765447 : Blo 1228432 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B2626195 : Blo 1228432 2626195 := bstep (se 1 (by rfl) ⟨1969646, by rfl⟩ : syracuseStep 2626195 = 3939293) B3939293
theorem B3109529 : Blo 1228432 3109529 := bstep (se 2 (by rfl) ⟨1166073, by rfl⟩ : syracuseStep 3109529 = 2332147) B2332147
theorem B3502777 : Blo 1228432 3502777 := bstep (se 2 (by rfl) ⟨1313541, by rfl⟩ : syracuseStep 3502777 = 2627083) B2627083
theorem B1749691 : Blo 1228432 1749691 := bstep (se 1 (by rfl) ⟨1312268, by rfl⟩ : syracuseStep 1749691 = 2624537) B2624537
theorem B7000769 : Blo 1228432 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B23941849 : Blo 1228432 23941849 := bstep (se 2 (by rfl) ⟨8978193, by rfl⟩ : syracuseStep 23941849 = 17956387) B17956387
theorem B3109691 : Blo 1228432 3109691 := bstep (se 1 (by rfl) ⟨2332268, by rfl⟩ : syracuseStep 3109691 = 4664537) B4664537
theorem B2765627 : Blo 1228432 2765627 := bstep (se 1 (by rfl) ⟨2074220, by rfl⟩ : syracuseStep 2765627 = 4148441) B4148441
theorem B4150169 : Blo 1228432 4150169 := bstep (se 2 (by rfl) ⟨1556313, by rfl⟩ : syracuseStep 4150169 = 3112627) B3112627
theorem B2765753 : Blo 1228432 2765753 := bstep (se 2 (by rfl) ⟨1037157, by rfl⟩ : syracuseStep 2765753 = 2074315) B2074315
theorem B5903363 : Blo 1228432 5903363 := bstep (se 1 (by rfl) ⟨4427522, by rfl⟩ : syracuseStep 5903363 = 8855045) B8855045
theorem B3110035 : Blo 1228432 3110035 := bstep (se 1 (by rfl) ⟨2332526, by rfl⟩ : syracuseStep 3110035 = 4665053) B4665053
theorem B1750187 : Blo 1228432 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B2766095 : Blo 1228432 2766095 := bstep (se 1 (by rfl) ⟨2074571, by rfl⟩ : syracuseStep 2766095 = 4149143) B4149143
theorem B3110177 : Blo 1228432 3110177 := bstep (se 2 (by rfl) ⟨1166316, by rfl⟩ : syracuseStep 3110177 = 2332633) B2332633
theorem B15963425 : Blo 1228432 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B2766113 : Blo 1228432 2766113 := bstep (se 2 (by rfl) ⟨1037292, by rfl⟩ : syracuseStep 2766113 = 2074585) B2074585
theorem B1496363 : Blo 1228432 1496363 := bstep (se 1 (by rfl) ⟨1122272, by rfl⟩ : syracuseStep 1496363 = 2244545) B2244545
theorem B4429241 : Blo 1228432 4429241 := bstep (se 2 (by rfl) ⟨1660965, by rfl⟩ : syracuseStep 4429241 = 3321931) B3321931
theorem B2954681 : Blo 1228432 2954681 := bstep (se 2 (by rfl) ⟨1108005, by rfl⟩ : syracuseStep 2954681 = 2216011) B2216011
theorem B5609021 : Blo 1228432 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B10499651 : Blo 1228432 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B4666967 : Blo 1228432 4666967 := bstep (se 1 (by rfl) ⟨3500225, by rfl⟩ : syracuseStep 4666967 = 7000451) B7000451
theorem B4150871 : Blo 1228432 4150871 := bstep (se 1 (by rfl) ⟨3113153, by rfl⟩ : syracuseStep 4150871 = 6226307) B6226307
theorem B2766455 : Blo 1228432 2766455 := bstep (se 1 (by rfl) ⟨2074841, by rfl⟩ : syracuseStep 2766455 = 4149683) B4149683
theorem B3741319 : Blo 1228432 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B2332307 : Blo 1228432 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B23647895 : Blo 1228432 23647895 := bstep (se 1 (by rfl) ⟨17735921, by rfl⟩ : syracuseStep 23647895 = 35471843) B35471843
theorem B6223553 : Blo 1228432 6223553 := bstep (se 2 (by rfl) ⟨2333832, by rfl⟩ : syracuseStep 6223553 = 4667665) B4667665
theorem B2766635 : Blo 1228432 2766635 := bstep (se 1 (by rfl) ⟨2074976, by rfl⟩ : syracuseStep 2766635 = 4149953) B4149953
theorem B1382287 : Blo 1228432 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B5248921 : Blo 1228432 5248921 := bstep (se 2 (by rfl) ⟨1968345, by rfl⟩ : syracuseStep 5248921 = 3936691) B3936691
theorem B2955161 : Blo 1228432 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B11220889 : Blo 1228432 11220889 := bstep (se 2 (by rfl) ⟨4207833, by rfl⟩ : syracuseStep 11220889 = 8415667) B8415667
theorem B6731723 : Blo 1228432 6731723 := bstep (se 1 (by rfl) ⟨5048792, by rfl⟩ : syracuseStep 6731723 = 10097585) B10097585
theorem B4667453 : Blo 1228432 4667453 := bstep (se 3 (by rfl) ⟨875147, by rfl⟩ : syracuseStep 4667453 = 1750295) B1750295
theorem B4151357 : Blo 1228432 4151357 := bstep (se 3 (by rfl) ⟨778379, by rfl⟩ : syracuseStep 4151357 = 1556759) B1556759
theorem B5322839 : Blo 1228432 5322839 := bstep (se 1 (by rfl) ⟨3992129, by rfl⟩ : syracuseStep 5322839 = 7984259) B7984259
theorem B2766995 : Blo 1228432 2766995 := bstep (se 1 (by rfl) ⟨2075246, by rfl⟩ : syracuseStep 2766995 = 4150493) B4150493
theorem B2767049 : Blo 1228432 2767049 := bstep (se 2 (by rfl) ⟨1037643, by rfl⟩ : syracuseStep 2767049 = 2075287) B2075287
theorem B3111169 : Blo 1228432 3111169 := bstep (se 2 (by rfl) ⟨1166688, by rfl⟩ : syracuseStep 3111169 = 2333377) B2333377
theorem B25942289 : Blo 1228432 25942289 := bstep (se 2 (by rfl) ⟨9728358, by rfl⟩ : syracuseStep 25942289 = 19456717) B19456717
theorem B1382791 : Blo 1228432 1382791 := bstep (se 1 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 1382791 = 2074187) B2074187
theorem B1382971 : Blo 1228432 1382971 := bstep (se 1 (by rfl) ⟨1037228, by rfl⟩ : syracuseStep 1382971 = 2074457) B2074457
theorem B67287671 : Blo 1228432 67287671 := bstep (se 1 (by rfl) ⟨50465753, by rfl⟩ : syracuseStep 67287671 = 100931507) B100931507
theorem B1751753 : Blo 1228432 1751753 := bstep (se 2 (by rfl) ⟨656907, by rfl⟩ : syracuseStep 1751753 = 1313815) B1313815
theorem B5905133 : Blo 1228432 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B3111767 : Blo 1228432 3111767 := bstep (se 1 (by rfl) ⟨2333825, by rfl⟩ : syracuseStep 3111767 = 4667651) B4667651
theorem B2767751 : Blo 1228432 2767751 := bstep (se 1 (by rfl) ⟨2075813, by rfl⟩ : syracuseStep 2767751 = 4151627) B4151627
theorem B42589091 : Blo 1228432 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B6224849 : Blo 1228432 6224849 := bstep (se 2 (by rfl) ⟨2334318, by rfl⟩ : syracuseStep 6224849 = 4668637) B4668637
theorem B1555463 : Blo 1228432 1555463 := bstep (se 1 (by rfl) ⟨1166597, by rfl⟩ : syracuseStep 1555463 = 2333195) B2333195
theorem B2333711 : Blo 1228432 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1383439 : Blo 1228432 1383439 := bstep (se 1 (by rfl) ⟨1037579, by rfl⟩ : syracuseStep 1383439 = 2075159) B2075159
theorem B3111979 : Blo 1228432 3111979 := bstep (se 1 (by rfl) ⟨2333984, by rfl⟩ : syracuseStep 3111979 = 4667969) B4667969
theorem B13294637 : Blo 1228432 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B2767931 : Blo 1228432 2767931 := bstep (se 1 (by rfl) ⟨2075948, by rfl⟩ : syracuseStep 2767931 = 4151897) B4151897
theorem B5250167 : Blo 1228432 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B5397623 : Blo 1228432 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B3112121 : Blo 1228432 3112121 := bstep (se 2 (by rfl) ⟨1167045, by rfl⟩ : syracuseStep 3112121 = 2334091) B2334091
theorem B2768057 : Blo 1228432 2768057 := bstep (se 2 (by rfl) ⟨1038021, by rfl⟩ : syracuseStep 2768057 = 2076043) B2076043
theorem B1842695 : Blo 1228432 1842695 := bstep (se 1 (by rfl) ⟨1382021, by rfl⟩ : syracuseStep 1842695 = 2764043) B2764043
theorem B1383943 : Blo 1228432 1383943 := bstep (se 1 (by rfl) ⟨1037957, by rfl⟩ : syracuseStep 1383943 = 2075915) B2075915
theorem B2768399 : Blo 1228432 2768399 := bstep (se 1 (by rfl) ⟨2076299, by rfl⟩ : syracuseStep 2768399 = 4152599) B4152599
theorem B2768417 : Blo 1228432 2768417 := bstep (se 2 (by rfl) ⟨1038156, by rfl⟩ : syracuseStep 2768417 = 2076313) B2076313
theorem B1842731 : Blo 1228432 1842731 := bstep (se 1 (by rfl) ⟨1382048, by rfl⟩ : syracuseStep 1842731 = 2764097) B2764097
theorem B2334251 : Blo 1228432 2334251 := bstep (se 1 (by rfl) ⟨1750688, by rfl⟩ : syracuseStep 2334251 = 3501377) B3501377
theorem B1842761 : Blo 1228432 1842761 := bstep (se 2 (by rfl) ⟨691035, by rfl⟩ : syracuseStep 1842761 = 1382071) B1382071
theorem B1556111 : Blo 1228432 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1228475 : Blo 1228432 1228475 := bstep (se 1 (by rfl) ⟨921356, by rfl⟩ : syracuseStep 1228475 = 1842713) B1842713
theorem B1842875 : Blo 1228432 1842875 := bstep (se 1 (by rfl) ⟨1382156, by rfl⟩ : syracuseStep 1842875 = 2764313) B2764313
theorem B1384123 : Blo 1228432 1384123 := bstep (se 1 (by rfl) ⟨1038092, by rfl⟩ : syracuseStep 1384123 = 2076185) B2076185
theorem B1842935 : Blo 1228432 1842935 := bstep (se 1 (by rfl) ⟨1382201, by rfl⟩ : syracuseStep 1842935 = 2764403) B2764403
theorem B1228551 : Blo 1228432 1228551 := bstep (se 1 (by rfl) ⟨921413, by rfl⟩ : syracuseStep 1228551 = 1842827) B1842827
theorem B1228559 : Blo 1228432 1228559 := bstep (se 1 (by rfl) ⟨921419, by rfl⟩ : syracuseStep 1228559 = 1842839) B1842839
theorem B1842959 : Blo 1228432 1842959 := bstep (se 1 (by rfl) ⟨1382219, by rfl⟩ : syracuseStep 1842959 = 2764439) B2764439
theorem B1843001 : Blo 1228432 1843001 := bstep (se 2 (by rfl) ⟨691125, by rfl⟩ : syracuseStep 1843001 = 1382251) B1382251
theorem B1228603 : Blo 1228432 1228603 := bstep (se 1 (by rfl) ⟨921452, by rfl⟩ : syracuseStep 1228603 = 1842905) B1842905
theorem B1228679 : Blo 1228432 1228679 := bstep (se 1 (by rfl) ⟨921509, by rfl⟩ : syracuseStep 1228679 = 1843019) B1843019
theorem B1843079 : Blo 1228432 1843079 := bstep (se 1 (by rfl) ⟨1382309, by rfl⟩ : syracuseStep 1843079 = 2764619) B2764619
theorem B1228687 : Blo 1228432 1228687 := bstep (se 1 (by rfl) ⟨921515, by rfl⟩ : syracuseStep 1228687 = 1843031) B1843031
theorem B1843115 : Blo 1228432 1843115 := bstep (se 1 (by rfl) ⟨1382336, by rfl⟩ : syracuseStep 1843115 = 2764673) B2764673
theorem B1228731 : Blo 1228432 1228731 := bstep (se 1 (by rfl) ⟨921548, by rfl⟩ : syracuseStep 1228731 = 1843097) B1843097
theorem B1843145 : Blo 1228432 1843145 := bstep (se 2 (by rfl) ⟨691179, by rfl⟩ : syracuseStep 1843145 = 1382359) B1382359
theorem B14385181 : Blo 1228432 14385181 := bstep (se 3 (by rfl) ⟨2697221, by rfl⟩ : syracuseStep 14385181 = 5394443) B5394443
theorem B1228839 : Blo 1228432 1228839 := bstep (se 1 (by rfl) ⟨921629, by rfl⟩ : syracuseStep 1228839 = 1843259) B1843259
theorem B1228879 : Blo 1228432 1228879 := bstep (se 1 (by rfl) ⟨921659, by rfl⟩ : syracuseStep 1228879 = 1843319) B1843319
theorem B1228895 : Blo 1228432 1228895 := bstep (se 1 (by rfl) ⟨921671, by rfl⟩ : syracuseStep 1228895 = 1843343) B1843343
theorem B1228923 : Blo 1228432 1228923 := bstep (se 1 (by rfl) ⟨921692, by rfl⟩ : syracuseStep 1228923 = 1843385) B1843385
theorem B1228975 : Blo 1228432 1228975 := bstep (se 1 (by rfl) ⟨921731, by rfl⟩ : syracuseStep 1228975 = 1843463) B1843463
theorem B1228999 : Blo 1228432 1228999 := bstep (se 1 (by rfl) ⟨921749, by rfl⟩ : syracuseStep 1228999 = 1843499) B1843499
theorem B2334919 : Blo 1228432 2334919 := bstep (se 1 (by rfl) ⟨1751189, by rfl⟩ : syracuseStep 2334919 = 3502379) B3502379
theorem B1229019 : Blo 1228432 1229019 := bstep (se 1 (by rfl) ⟨921764, by rfl⟩ : syracuseStep 1229019 = 1843529) B1843529
theorem B1229095 : Blo 1228432 1229095 := bstep (se 1 (by rfl) ⟨921821, by rfl⟩ : syracuseStep 1229095 = 1843643) B1843643
theorem B17711419 : Blo 1228432 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B1229135 : Blo 1228432 1229135 := bstep (se 1 (by rfl) ⟨921851, by rfl⟩ : syracuseStep 1229135 = 1843703) B1843703
theorem B1229151 : Blo 1228432 1229151 := bstep (se 1 (by rfl) ⟨921863, by rfl⟩ : syracuseStep 1229151 = 1843727) B1843727
theorem B1229179 : Blo 1228432 1229179 := bstep (se 1 (by rfl) ⟨921884, by rfl⟩ : syracuseStep 1229179 = 1843769) B1843769
theorem B1843631 : Blo 1228432 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B1229231 : Blo 1228432 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B1556911 : Blo 1228432 1556911 := bstep (se 1 (by rfl) ⟨1167683, by rfl⟩ : syracuseStep 1556911 = 2335367) B2335367
theorem B2073019 : Blo 1228432 2073019 := bstep (se 1 (by rfl) ⟨1554764, by rfl⟩ : syracuseStep 2073019 = 3109529) B3109529
theorem B1229255 : Blo 1228432 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B1868251 : Blo 1228432 1868251 := bstep (se 1 (by rfl) ⟨1401188, by rfl⟩ : syracuseStep 1868251 = 2802377) B2802377
theorem B1245659 : Blo 1228432 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B1229275 : Blo 1228432 1229275 := bstep (se 1 (by rfl) ⟨921956, by rfl⟩ : syracuseStep 1229275 = 1843913) B1843913
theorem B1843721 : Blo 1228432 1843721 := bstep (se 2 (by rfl) ⟨691395, by rfl⟩ : syracuseStep 1843721 = 1382791) B1382791
theorem B2073127 : Blo 1228432 2073127 := bstep (se 1 (by rfl) ⟨1554845, by rfl⟩ : syracuseStep 2073127 = 3109691) B3109691
theorem B1843751 : Blo 1228432 1843751 := bstep (se 1 (by rfl) ⟨1382813, by rfl⟩ : syracuseStep 1843751 = 2765627) B2765627
theorem B1229351 : Blo 1228432 1229351 := bstep (se 1 (by rfl) ⟨922013, by rfl⟩ : syracuseStep 1229351 = 1844027) B1844027
theorem B1229391 : Blo 1228432 1229391 := bstep (se 1 (by rfl) ⟨922043, by rfl⟩ : syracuseStep 1229391 = 1844087) B1844087
theorem B1229407 : Blo 1228432 1229407 := bstep (se 1 (by rfl) ⟨922055, by rfl⟩ : syracuseStep 1229407 = 1844111) B1844111
theorem B1843835 : Blo 1228432 1843835 := bstep (se 1 (by rfl) ⟨1382876, by rfl⟩ : syracuseStep 1843835 = 2765753) B2765753
theorem B1229435 : Blo 1228432 1229435 := bstep (se 1 (by rfl) ⟨922076, by rfl⟩ : syracuseStep 1229435 = 1844153) B1844153
theorem B1229487 : Blo 1228432 1229487 := bstep (se 1 (by rfl) ⟨922115, by rfl⟩ : syracuseStep 1229487 = 1844231) B1844231
theorem B7881401 : Blo 1228432 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B1229511 : Blo 1228432 1229511 := bstep (se 1 (by rfl) ⟨922133, by rfl⟩ : syracuseStep 1229511 = 1844267) B1844267
theorem B1229531 : Blo 1228432 1229531 := bstep (se 1 (by rfl) ⟨922148, by rfl⟩ : syracuseStep 1229531 = 1844297) B1844297
theorem B1843961 : Blo 1228432 1843961 := bstep (se 2 (by rfl) ⟨691485, by rfl⟩ : syracuseStep 1843961 = 1382971) B1382971
theorem B21021443 : Blo 1228432 21021443 := bstep (se 1 (by rfl) ⟨15766082, by rfl⟩ : syracuseStep 21021443 = 31532165) B31532165
theorem B1229607 : Blo 1228432 1229607 := bstep (se 1 (by rfl) ⟨922205, by rfl⟩ : syracuseStep 1229607 = 1844411) B1844411
theorem B1229647 : Blo 1228432 1229647 := bstep (se 1 (by rfl) ⟨922235, by rfl⟩ : syracuseStep 1229647 = 1844471) B1844471
theorem B1844063 : Blo 1228432 1844063 := bstep (se 1 (by rfl) ⟨1383047, by rfl⟩ : syracuseStep 1844063 = 2766095) B2766095
theorem B1229663 : Blo 1228432 1229663 := bstep (se 1 (by rfl) ⟨922247, by rfl⟩ : syracuseStep 1229663 = 1844495) B1844495
theorem B2073451 : Blo 1228432 2073451 := bstep (se 1 (by rfl) ⟨1555088, by rfl⟩ : syracuseStep 2073451 = 3110177) B3110177
theorem B10642283 : Blo 1228432 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B1844075 : Blo 1228432 1844075 := bstep (se 1 (by rfl) ⟨1383056, by rfl⟩ : syracuseStep 1844075 = 2766113) B2766113
theorem B1229691 : Blo 1228432 1229691 := bstep (se 1 (by rfl) ⟨922268, by rfl⟩ : syracuseStep 1229691 = 1844537) B1844537
theorem B4670369 : Blo 1228432 4670369 := bstep (se 2 (by rfl) ⟨1751388, by rfl⟩ : syracuseStep 4670369 = 3502777) B3502777
theorem B1229743 : Blo 1228432 1229743 := bstep (se 1 (by rfl) ⟨922307, by rfl⟩ : syracuseStep 1229743 = 1844615) B1844615
theorem B3113903 : Blo 1228432 3113903 := bstep (se 1 (by rfl) ⟨2335427, by rfl⟩ : syracuseStep 3113903 = 4670855) B4670855
theorem B1229767 : Blo 1228432 1229767 := bstep (se 1 (by rfl) ⟨922325, by rfl⟩ : syracuseStep 1229767 = 1844651) B1844651
theorem B1229787 : Blo 1228432 1229787 := bstep (se 1 (by rfl) ⟨922340, by rfl⟩ : syracuseStep 1229787 = 1844681) B1844681
theorem B9331685 : Blo 1228432 9331685 := bstep (se 4 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 9331685 = 1749691) B1749691
theorem B1229863 : Blo 1228432 1229863 := bstep (se 1 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 1229863 = 1844795) B1844795
theorem B9339947 : Blo 1228432 9339947 := bstep (se 1 (by rfl) ⟨7004960, by rfl⟩ : syracuseStep 9339947 = 14009921) B14009921
theorem B7095347 : Blo 1228432 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B1844303 : Blo 1228432 1844303 := bstep (se 1 (by rfl) ⟨1383227, by rfl⟩ : syracuseStep 1844303 = 2766455) B2766455
theorem B1229903 : Blo 1228432 1229903 := bstep (se 1 (by rfl) ⟨922427, by rfl⟩ : syracuseStep 1229903 = 1844855) B1844855
theorem B1229919 : Blo 1228432 1229919 := bstep (se 1 (by rfl) ⟨922439, by rfl⟩ : syracuseStep 1229919 = 1844879) B1844879
theorem B1229947 : Blo 1228432 1229947 := bstep (se 1 (by rfl) ⟨922460, by rfl⟩ : syracuseStep 1229947 = 1844921) B1844921
theorem B1229999 : Blo 1228432 1229999 := bstep (se 1 (by rfl) ⟨922499, by rfl⟩ : syracuseStep 1229999 = 1844999) B1844999
theorem B1844423 : Blo 1228432 1844423 := bstep (se 1 (by rfl) ⟨1383317, by rfl⟩ : syracuseStep 1844423 = 2766635) B2766635
theorem B1230023 : Blo 1228432 1230023 := bstep (se 1 (by rfl) ⟨922517, by rfl⟩ : syracuseStep 1230023 = 1845035) B1845035
theorem B1230043 : Blo 1228432 1230043 := bstep (se 1 (by rfl) ⟨922532, by rfl⟩ : syracuseStep 1230043 = 1845065) B1845065
theorem B4146443 : Blo 1228432 4146443 := bstep (se 1 (by rfl) ⟨3109832, by rfl⟩ : syracuseStep 4146443 = 6219665) B6219665
theorem B1230119 : Blo 1228432 1230119 := bstep (se 1 (by rfl) ⟨922589, by rfl⟩ : syracuseStep 1230119 = 1845179) B1845179
theorem B1230159 : Blo 1228432 1230159 := bstep (se 1 (by rfl) ⟨922619, by rfl⟩ : syracuseStep 1230159 = 1845239) B1845239
theorem B1230175 : Blo 1228432 1230175 := bstep (se 1 (by rfl) ⟨922631, by rfl⟩ : syracuseStep 1230175 = 1845263) B1845263
theorem B1844585 : Blo 1228432 1844585 := bstep (se 2 (by rfl) ⟨691719, by rfl⟩ : syracuseStep 1844585 = 1383439) B1383439
theorem B1230203 : Blo 1228432 1230203 := bstep (se 1 (by rfl) ⟨922652, by rfl⟩ : syracuseStep 1230203 = 1845305) B1845305
theorem B1230255 : Blo 1228432 1230255 := bstep (se 1 (by rfl) ⟨922691, by rfl⟩ : syracuseStep 1230255 = 1845383) B1845383
theorem B1844663 : Blo 1228432 1844663 := bstep (se 1 (by rfl) ⟨1383497, by rfl⟩ : syracuseStep 1844663 = 2766995) B2766995
theorem B1230279 : Blo 1228432 1230279 := bstep (se 1 (by rfl) ⟨922709, by rfl⟩ : syracuseStep 1230279 = 1845419) B1845419
theorem B13297097 : Blo 1228432 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B1844699 : Blo 1228432 1844699 := bstep (se 1 (by rfl) ⟨1383524, by rfl⟩ : syracuseStep 1844699 = 2767049) B2767049
theorem B1230299 : Blo 1228432 1230299 := bstep (se 1 (by rfl) ⟨922724, by rfl⟩ : syracuseStep 1230299 = 1845449) B1845449
theorem B4146713 : Blo 1228432 4146713 := bstep (se 2 (by rfl) ⟨1555017, by rfl⟩ : syracuseStep 4146713 = 3110035) B3110035
theorem B3114521 : Blo 1228432 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B1230375 : Blo 1228432 1230375 := bstep (se 1 (by rfl) ⟨922781, by rfl⟩ : syracuseStep 1230375 = 1845563) B1845563
theorem B1230415 : Blo 1228432 1230415 := bstep (se 1 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 1230415 = 1845623) B1845623
theorem B1230431 : Blo 1228432 1230431 := bstep (se 1 (by rfl) ⟨922823, by rfl⟩ : syracuseStep 1230431 = 1845647) B1845647
theorem B6227603 : Blo 1228432 6227603 := bstep (se 1 (by rfl) ⟨4670702, by rfl⟩ : syracuseStep 6227603 = 9341405) B9341405
theorem B4671341 : Blo 1228432 4671341 := bstep (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) B1751753
theorem B2074511 : Blo 1228432 2074511 := bstep (se 1 (by rfl) ⟨1555883, by rfl⟩ : syracuseStep 2074511 = 3111767) B3111767
theorem B1845167 : Blo 1228432 1845167 := bstep (se 1 (by rfl) ⟨1383875, by rfl⟩ : syracuseStep 1845167 = 2767751) B2767751
theorem B1845257 : Blo 1228432 1845257 := bstep (se 2 (by rfl) ⟨691971, by rfl⟩ : syracuseStep 1845257 = 1383943) B1383943
theorem B1845287 : Blo 1228432 1845287 := bstep (se 1 (by rfl) ⟨1383965, by rfl⟩ : syracuseStep 1845287 = 2767931) B2767931
theorem B3500111 : Blo 1228432 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B3598415 : Blo 1228432 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2074747 : Blo 1228432 2074747 := bstep (se 1 (by rfl) ⟨1556060, by rfl⟩ : syracuseStep 2074747 = 3112121) B3112121
theorem B1845371 : Blo 1228432 1845371 := bstep (se 1 (by rfl) ⟨1384028, by rfl⟩ : syracuseStep 1845371 = 2768057) B2768057
theorem B2525383 : Blo 1228432 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B1845497 : Blo 1228432 1845497 := bstep (se 2 (by rfl) ⟨692061, by rfl⟩ : syracuseStep 1845497 = 1384123) B1384123
theorem B1313119 : Blo 1228432 1313119 := bstep (se 1 (by rfl) ⟨984839, by rfl⟩ : syracuseStep 1313119 = 1969679) B1969679
theorem B1845599 : Blo 1228432 1845599 := bstep (se 1 (by rfl) ⟨1384199, by rfl⟩ : syracuseStep 1845599 = 2768399) B2768399
theorem B1845611 : Blo 1228432 1845611 := bstep (se 1 (by rfl) ⟨1384208, by rfl⟩ : syracuseStep 1845611 = 2768417) B2768417
theorem B17729927 : Blo 1228432 17729927 := bstep (se 1 (by rfl) ⟨13297445, by rfl⟩ : syracuseStep 17729927 = 26594891) B26594891
theorem B14191051 : Blo 1228432 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B2492947 : Blo 1228432 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B6220313 : Blo 1228432 6220313 := bstep (se 2 (by rfl) ⟨2332617, by rfl⟩ : syracuseStep 6220313 = 4665235) B4665235
theorem B6998561 : Blo 1228432 6998561 := bstep (se 2 (by rfl) ⟨2624460, by rfl⟩ : syracuseStep 6998561 = 5248921) B5248921
theorem B14961185 : Blo 1228432 14961185 := bstep (se 2 (by rfl) ⟨5610444, by rfl⟩ : syracuseStep 14961185 = 11220889) B11220889
theorem B4147847 : Blo 1228432 4147847 := bstep (se 1 (by rfl) ⟨3110885, by rfl⟩ : syracuseStep 4147847 = 6221771) B6221771
theorem B19950259 : Blo 1228432 19950259 := bstep (se 1 (by rfl) ⟨14962694, by rfl⟩ : syracuseStep 19950259 = 29925389) B29925389
theorem B4147901 : Blo 1228432 4147901 := bstep (se 3 (by rfl) ⟨777731, by rfl⟩ : syracuseStep 4147901 = 1555463) B1555463
theorem B37849801 : Blo 1228432 37849801 := bstep (se 2 (by rfl) ⟨14193675, by rfl⟩ : syracuseStep 37849801 = 28387351) B28387351
theorem B2493175 : Blo 1228432 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B4148063 : Blo 1228432 4148063 := bstep (se 1 (by rfl) ⟨3111047, by rfl⟩ : syracuseStep 4148063 = 6222095) B6222095
theorem B8088503 : Blo 1228432 8088503 := bstep (se 1 (by rfl) ⟨6066377, by rfl⟩ : syracuseStep 8088503 = 12132755) B12132755
theorem B2075611 : Blo 1228432 2075611 := bstep (se 1 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 2075611 = 3113417) B3113417
theorem B4148225 : Blo 1228432 4148225 := bstep (se 2 (by rfl) ⟨1555584, by rfl⟩ : syracuseStep 4148225 = 3111169) B3111169
theorem B15961205 : Blo 1228432 15961205 := bstep (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) B1496363
theorem B4664567 : Blo 1228432 4664567 := bstep (se 1 (by rfl) ⟨3498425, by rfl⟩ : syracuseStep 4664567 = 6996851) B6996851
theorem B3935575 : Blo 1228432 3935575 := bstep (se 1 (by rfl) ⟨2951681, by rfl⟩ : syracuseStep 3935575 = 5903363) B5903363
theorem B8858969 : Blo 1228432 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B6647165 : Blo 1228432 6647165 := bstep (se 3 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 6647165 = 2492687) B2492687
theorem B3501593 : Blo 1228432 3501593 := bstep (se 2 (by rfl) ⟨1313097, by rfl⟩ : syracuseStep 3501593 = 2626195) B2626195
theorem B2076239 : Blo 1228432 2076239 := bstep (se 1 (by rfl) ⟨1557179, by rfl⟩ : syracuseStep 2076239 = 3114359) B3114359
theorem B2764385 : Blo 1228432 2764385 := bstep (se 2 (by rfl) ⟨1036644, by rfl⟩ : syracuseStep 2764385 = 2073289) B2073289
theorem B2952827 : Blo 1228432 2952827 := bstep (se 1 (by rfl) ⟨2214620, by rfl⟩ : syracuseStep 2952827 = 4429241) B4429241
theorem B1969787 : Blo 1228432 1969787 := bstep (se 1 (by rfl) ⟨1477340, by rfl⟩ : syracuseStep 1969787 = 2954681) B2954681
theorem B6999767 : Blo 1228432 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B15765263 : Blo 1228432 15765263 := bstep (se 1 (by rfl) ⟨11823947, by rfl⟩ : syracuseStep 15765263 = 23647895) B23647895
theorem B4149035 : Blo 1228432 4149035 := bstep (se 1 (by rfl) ⟨3111776, by rfl⟩ : syracuseStep 4149035 = 6223553) B6223553
theorem B11825027 : Blo 1228432 11825027 := bstep (se 1 (by rfl) ⟨8868770, by rfl⟩ : syracuseStep 11825027 = 17737541) B17737541
theorem B2764727 : Blo 1228432 2764727 := bstep (se 1 (by rfl) ⟨2073545, by rfl⟩ : syracuseStep 2764727 = 4147091) B4147091
theorem B4149305 : Blo 1228432 4149305 := bstep (se 2 (by rfl) ⟨1555989, by rfl⟩ : syracuseStep 4149305 = 3111979) B3111979
theorem B5255225 : Blo 1228432 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B4665539 : Blo 1228432 4665539 := bstep (se 1 (by rfl) ⟨3499154, by rfl⟩ : syracuseStep 4665539 = 6998309) B6998309
theorem B4149629 : Blo 1228432 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B3740033 : Blo 1228432 3740033 := bstep (se 2 (by rfl) ⟨1402512, by rfl⟩ : syracuseStep 3740033 = 2805025) B2805025
theorem B4207067 : Blo 1228432 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B3936755 : Blo 1228432 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B2765321 : Blo 1228432 2765321 := bstep (se 2 (by rfl) ⟨1036995, by rfl⟩ : syracuseStep 2765321 = 2073991) B2073991
theorem B17723927 : Blo 1228432 17723927 := bstep (se 1 (by rfl) ⟨13292945, by rfl⟩ : syracuseStep 17723927 = 26585891) B26585891
theorem B3109499 : Blo 1228432 3109499 := bstep (se 1 (by rfl) ⟨2332124, by rfl⟩ : syracuseStep 3109499 = 4664249) B4664249
theorem B4665995 : Blo 1228432 4665995 := bstep (se 1 (by rfl) ⟨3499496, by rfl⟩ : syracuseStep 4665995 = 6998993) B6998993
theorem B4149899 : Blo 1228432 4149899 := bstep (se 1 (by rfl) ⟨3112424, by rfl⟩ : syracuseStep 4149899 = 6224849) B6224849
theorem B1749703 : Blo 1228432 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B4666207 : Blo 1228432 4666207 := bstep (se 1 (by rfl) ⟨3499655, by rfl⟩ : syracuseStep 4666207 = 6999311) B6999311
theorem B2765663 : Blo 1228432 2765663 := bstep (se 1 (by rfl) ⟨2074247, by rfl⟩ : syracuseStep 2765663 = 4148495) B4148495
theorem B7877483 : Blo 1228432 7877483 := bstep (se 1 (by rfl) ⟨5908112, by rfl⟩ : syracuseStep 7877483 = 11816225) B11816225
theorem B2765843 : Blo 1228432 2765843 := bstep (se 1 (by rfl) ⟨2074382, by rfl⟩ : syracuseStep 2765843 = 4148765) B4148765
theorem B7877711 : Blo 1228432 7877711 := bstep (se 1 (by rfl) ⟨5908283, by rfl⟩ : syracuseStep 7877711 = 11816567) B11816567
theorem B2766185 : Blo 1228432 2766185 := bstep (se 2 (by rfl) ⟨1037319, by rfl⟩ : syracuseStep 2766185 = 2074639) B2074639
theorem B2626921 : Blo 1228432 2626921 := bstep (se 2 (by rfl) ⟨985095, by rfl⟩ : syracuseStep 2626921 = 1970191) B1970191
theorem B6223229 : Blo 1228432 6223229 := bstep (se 3 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 6223229 = 2333711) B2333711
theorem B1660343 : Blo 1228432 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B1496503 : Blo 1228432 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B4150817 : Blo 1228432 4150817 := bstep (se 2 (by rfl) ⟨1556556, by rfl⟩ : syracuseStep 4150817 = 3113113) B3113113
theorem B3741223 : Blo 1228432 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B1660495 : Blo 1228432 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B14202515 : Blo 1228432 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B4151033 : Blo 1228432 4151033 := bstep (se 2 (by rfl) ⟨1556637, by rfl⟩ : syracuseStep 4151033 = 3113275) B3113275
theorem B4667165 : Blo 1228432 4667165 := bstep (se 3 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 4667165 = 1750187) B1750187
theorem B4667179 : Blo 1228432 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B2332489 : Blo 1228432 2332489 := bstep (se 2 (by rfl) ⟨874683, by rfl⟩ : syracuseStep 2332489 = 1749367) B1749367
theorem B2766779 : Blo 1228432 2766779 := bstep (se 1 (by rfl) ⟨2075084, by rfl⟩ : syracuseStep 2766779 = 4150169) B4150169
theorem B4151303 : Blo 1228432 4151303 := bstep (se 1 (by rfl) ⟨3113477, by rfl⟩ : syracuseStep 4151303 = 6226955) B6226955
theorem B69179437 : Blo 1228432 69179437 := bstep (se 3 (by rfl) ⟨12971144, by rfl⟩ : syracuseStep 69179437 = 25942289) B25942289
theorem B2766905 : Blo 1228432 2766905 := bstep (se 2 (by rfl) ⟨1037589, by rfl⟩ : syracuseStep 2766905 = 2075179) B2075179
theorem B7002227 : Blo 1228432 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B4151411 : Blo 1228432 4151411 := bstep (se 1 (by rfl) ⟨3113558, by rfl⟩ : syracuseStep 4151411 = 6227117) B6227117
theorem B56776949 : Blo 1228432 56776949 := bstep (se 5 (by rfl) ⟨2661419, by rfl⟩ : syracuseStep 56776949 = 5322839) B5322839
theorem B31922465 : Blo 1228432 31922465 := bstep (se 2 (by rfl) ⟨11970924, by rfl⟩ : syracuseStep 31922465 = 23941849) B23941849
theorem B4151681 : Blo 1228432 4151681 := bstep (se 2 (by rfl) ⟨1556880, by rfl⟩ : syracuseStep 4151681 = 3113761) B3113761
theorem B3111311 : Blo 1228432 3111311 := bstep (se 1 (by rfl) ⟨2333483, by rfl⟩ : syracuseStep 3111311 = 4666967) B4666967
theorem B2767247 : Blo 1228432 2767247 := bstep (se 1 (by rfl) ⟨2075435, by rfl⟩ : syracuseStep 2767247 = 4150871) B4150871
theorem B1661359 : Blo 1228432 1661359 := bstep (se 1 (by rfl) ⟨1246019, by rfl⟩ : syracuseStep 1661359 = 2492039) B2492039
theorem B1554871 : Blo 1228432 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B7002683 : Blo 1228432 7002683 := bstep (se 1 (by rfl) ⟨5252012, by rfl⟩ : syracuseStep 7002683 = 10504025) B10504025
theorem B4487815 : Blo 1228432 4487815 := bstep (se 1 (by rfl) ⟨3365861, by rfl⟩ : syracuseStep 4487815 = 6731723) B6731723
theorem B9337517 : Blo 1228432 9337517 := bstep (se 3 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 9337517 = 3501569) B3501569
theorem B3111635 : Blo 1228432 3111635 := bstep (se 1 (by rfl) ⟨2333726, by rfl⟩ : syracuseStep 3111635 = 4667453) B4667453
theorem B2767571 : Blo 1228432 2767571 := bstep (se 1 (by rfl) ⟨2075678, by rfl⟩ : syracuseStep 2767571 = 4151357) B4151357
theorem B14957389 : Blo 1228432 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B4430855 : Blo 1228432 4430855 := bstep (se 1 (by rfl) ⟨3323141, by rfl⟩ : syracuseStep 4430855 = 6646283) B6646283
theorem B44858447 : Blo 1228432 44858447 := bstep (se 1 (by rfl) ⟨33643835, by rfl⟩ : syracuseStep 44858447 = 67287671) B67287671
theorem B1383547 : Blo 1228432 1383547 := bstep (se 1 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 1383547 = 2075321) B2075321
theorem B6732953 : Blo 1228432 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B4152491 : Blo 1228432 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B4988099 : Blo 1228432 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B22420759 : Blo 1228432 22420759 := bstep (se 1 (by rfl) ⟨16815569, by rfl⟩ : syracuseStep 22420759 = 33631139) B33631139
theorem B28392727 : Blo 1228432 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B8863091 : Blo 1228432 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B3325313 : Blo 1228432 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B4988425 : Blo 1228432 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B1842767 : Blo 1228432 1842767 := bstep (se 1 (by rfl) ⟨1382075, by rfl⟩ : syracuseStep 1842767 = 2764151) B2764151
theorem B1384015 : Blo 1228432 1384015 := bstep (se 1 (by rfl) ⟨1038011, by rfl⟩ : syracuseStep 1384015 = 2076023) B2076023
theorem B1228463 : Blo 1228432 1228463 := bstep (se 1 (by rfl) ⟨921347, by rfl⟩ : syracuseStep 1228463 = 1842695) B1842695
theorem B1228487 : Blo 1228432 1228487 := bstep (se 1 (by rfl) ⟨921365, by rfl⟩ : syracuseStep 1228487 = 1842731) B1842731
theorem B1842887 : Blo 1228432 1842887 := bstep (se 1 (by rfl) ⟨1382165, by rfl⟩ : syracuseStep 1842887 = 2764331) B2764331
theorem B1556167 : Blo 1228432 1556167 := bstep (se 1 (by rfl) ⟨1167125, by rfl⟩ : syracuseStep 1556167 = 2334251) B2334251
theorem B1228507 : Blo 1228432 1228507 := bstep (se 1 (by rfl) ⟨921380, by rfl⟩ : syracuseStep 1228507 = 1842761) B1842761
theorem B53133029 : Blo 1228432 53133029 := bstep (se 4 (by rfl) ⟨4981221, by rfl⟩ : syracuseStep 53133029 = 9962443) B9962443
theorem B7880429 : Blo 1228432 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B1228583 : Blo 1228432 1228583 := bstep (se 1 (by rfl) ⟨921437, by rfl⟩ : syracuseStep 1228583 = 1842875) B1842875
theorem B1228623 : Blo 1228432 1228623 := bstep (se 1 (by rfl) ⟨921467, by rfl⟩ : syracuseStep 1228623 = 1842935) B1842935
theorem B1228639 : Blo 1228432 1228639 := bstep (se 1 (by rfl) ⟨921479, by rfl⟩ : syracuseStep 1228639 = 1842959) B1842959
theorem B1843049 : Blo 1228432 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B1228667 : Blo 1228432 1228667 := bstep (se 1 (by rfl) ⟨921500, by rfl⟩ : syracuseStep 1228667 = 1843001) B1843001
theorem B1228719 : Blo 1228432 1228719 := bstep (se 1 (by rfl) ⟨921539, by rfl⟩ : syracuseStep 1228719 = 1843079) B1843079
theorem B1843127 : Blo 1228432 1843127 := bstep (se 1 (by rfl) ⟨1382345, by rfl⟩ : syracuseStep 1843127 = 2764691) B2764691
theorem B1228743 : Blo 1228432 1228743 := bstep (se 1 (by rfl) ⟨921557, by rfl⟩ : syracuseStep 1228743 = 1843115) B1843115
theorem B1228763 : Blo 1228432 1228763 := bstep (se 1 (by rfl) ⟨921572, by rfl⟩ : syracuseStep 1228763 = 1843145) B1843145
theorem B1843163 : Blo 1228432 1843163 := bstep (se 1 (by rfl) ⟨1382372, by rfl⟩ : syracuseStep 1843163 = 2764745) B2764745
theorem B2334683 : Blo 1228432 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B3367177 : Blo 1228432 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B3113225 : Blo 1228432 3113225 := bstep (se 2 (by rfl) ⟨1167459, by rfl⟩ : syracuseStep 3113225 = 2334919) B2334919
theorem B1229087 : Blo 1228432 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B1843547 : Blo 1228432 1843547 := bstep (se 1 (by rfl) ⟨1382660, by rfl⟩ : syracuseStep 1843547 = 2765321) B2765321
theorem B1229147 : Blo 1228432 1229147 := bstep (se 1 (by rfl) ⟨921860, by rfl⟩ : syracuseStep 1229147 = 1843721) B1843721
theorem B1229167 : Blo 1228432 1229167 := bstep (se 1 (by rfl) ⟨921875, by rfl⟩ : syracuseStep 1229167 = 1843751) B1843751
theorem B2072999 : Blo 1228432 2072999 := bstep (se 1 (by rfl) ⟨1554749, by rfl⟩ : syracuseStep 2072999 = 3109499) B3109499
theorem B1229223 : Blo 1228432 1229223 := bstep (se 1 (by rfl) ⟨921917, by rfl⟩ : syracuseStep 1229223 = 1843835) B1843835
theorem B1229307 : Blo 1228432 1229307 := bstep (se 1 (by rfl) ⟨921980, by rfl⟩ : syracuseStep 1229307 = 1843961) B1843961
theorem B1843775 : Blo 1228432 1843775 := bstep (se 1 (by rfl) ⟨1382831, by rfl⟩ : syracuseStep 1843775 = 2765663) B2765663
theorem B1229375 : Blo 1228432 1229375 := bstep (se 1 (by rfl) ⟨922031, by rfl⟩ : syracuseStep 1229375 = 1844063) B1844063
theorem B7094855 : Blo 1228432 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B1229383 : Blo 1228432 1229383 := bstep (se 1 (by rfl) ⟨922037, by rfl⟩ : syracuseStep 1229383 = 1844075) B1844075
theorem B2073161 : Blo 1228432 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B5251655 : Blo 1228432 5251655 := bstep (se 1 (by rfl) ⟨3938741, by rfl⟩ : syracuseStep 5251655 = 7877483) B7877483
theorem B3113579 : Blo 1228432 3113579 := bstep (se 1 (by rfl) ⟨2335184, by rfl⟩ : syracuseStep 3113579 = 4670369) B4670369
theorem B2491001 : Blo 1228432 2491001 := bstep (se 2 (by rfl) ⟨934125, by rfl⟩ : syracuseStep 2491001 = 1868251) B1868251
theorem B1843895 : Blo 1228432 1843895 := bstep (se 1 (by rfl) ⟨1382921, by rfl⟩ : syracuseStep 1843895 = 2765843) B2765843
theorem B6226631 : Blo 1228432 6226631 := bstep (se 1 (by rfl) ⟨4669973, by rfl⟩ : syracuseStep 6226631 = 9339947) B9339947
theorem B5251807 : Blo 1228432 5251807 := bstep (se 1 (by rfl) ⟨3938855, by rfl⟩ : syracuseStep 5251807 = 7877711) B7877711
theorem B1229535 : Blo 1228432 1229535 := bstep (se 1 (by rfl) ⟨922151, by rfl⟩ : syracuseStep 1229535 = 1844303) B1844303
theorem B1229615 : Blo 1228432 1229615 := bstep (se 1 (by rfl) ⟨922211, by rfl⟩ : syracuseStep 1229615 = 1844423) B1844423
theorem B26600345 : Blo 1228432 26600345 := bstep (se 2 (by rfl) ⟨9975129, by rfl⟩ : syracuseStep 26600345 = 19950259) B19950259
theorem B1844123 : Blo 1228432 1844123 := bstep (se 1 (by rfl) ⟨1383092, by rfl⟩ : syracuseStep 1844123 = 2766185) B2766185
theorem B1229723 : Blo 1228432 1229723 := bstep (se 1 (by rfl) ⟨922292, by rfl⟩ : syracuseStep 1229723 = 1844585) B1844585
theorem B1229775 : Blo 1228432 1229775 := bstep (se 1 (by rfl) ⟨922331, by rfl⟩ : syracuseStep 1229775 = 1844663) B1844663
theorem B8864731 : Blo 1228432 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1229799 : Blo 1228432 1229799 := bstep (se 1 (by rfl) ⟨922349, by rfl⟩ : syracuseStep 1229799 = 1844699) B1844699
theorem B3114227 : Blo 1228432 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B1230111 : Blo 1228432 1230111 := bstep (se 1 (by rfl) ⟨922583, by rfl⟩ : syracuseStep 1230111 = 1845167) B1845167
theorem B1844519 : Blo 1228432 1844519 := bstep (se 1 (by rfl) ⟨1383389, by rfl⟩ : syracuseStep 1844519 = 2766779) B2766779
theorem B1230171 : Blo 1228432 1230171 := bstep (se 1 (by rfl) ⟨922628, by rfl⟩ : syracuseStep 1230171 = 1845257) B1845257
theorem B1230191 : Blo 1228432 1230191 := bstep (se 1 (by rfl) ⟨922643, by rfl⟩ : syracuseStep 1230191 = 1845287) B1845287
theorem B1844603 : Blo 1228432 1844603 := bstep (se 1 (by rfl) ⟨1383452, by rfl⟩ : syracuseStep 1844603 = 2766905) B2766905
theorem B1230247 : Blo 1228432 1230247 := bstep (se 1 (by rfl) ⟨922685, by rfl⟩ : syracuseStep 1230247 = 1845371) B1845371
theorem B1844729 : Blo 1228432 1844729 := bstep (se 2 (by rfl) ⟨691773, by rfl⟩ : syracuseStep 1844729 = 1383547) B1383547
theorem B1230331 : Blo 1228432 1230331 := bstep (se 1 (by rfl) ⟨922748, by rfl⟩ : syracuseStep 1230331 = 1845497) B1845497
theorem B1230399 : Blo 1228432 1230399 := bstep (se 1 (by rfl) ⟨922799, by rfl⟩ : syracuseStep 1230399 = 1845599) B1845599
theorem B1230407 : Blo 1228432 1230407 := bstep (se 1 (by rfl) ⟨922805, by rfl⟩ : syracuseStep 1230407 = 1845611) B1845611
theorem B2074207 : Blo 1228432 2074207 := bstep (se 1 (by rfl) ⟨1555655, by rfl⟩ : syracuseStep 2074207 = 3111311) B3111311
theorem B1844831 : Blo 1228432 1844831 := bstep (se 1 (by rfl) ⟨1383623, by rfl⟩ : syracuseStep 1844831 = 2767247) B2767247
theorem B4146875 : Blo 1228432 4146875 := bstep (se 1 (by rfl) ⟨3110156, by rfl⟩ : syracuseStep 4146875 = 6220313) B6220313
theorem B29894345 : Blo 1228432 29894345 := bstep (se 2 (by rfl) ⟨11210379, by rfl⟩ : syracuseStep 29894345 = 22420759) B22420759
theorem B37856969 : Blo 1228432 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B2074423 : Blo 1228432 2074423 := bstep (se 1 (by rfl) ⟨1555817, by rfl⟩ : syracuseStep 2074423 = 3111635) B3111635
theorem B1845047 : Blo 1228432 1845047 := bstep (se 1 (by rfl) ⟨1383785, by rfl⟩ : syracuseStep 1845047 = 2767571) B2767571
theorem B2213993 : Blo 1228432 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B1845353 : Blo 1228432 1845353 := bstep (se 2 (by rfl) ⟨692007, by rfl⟩ : syracuseStep 1845353 = 1384015) B1384015
theorem B5908727 : Blo 1228432 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B2074889 : Blo 1228432 2074889 := bstep (se 2 (by rfl) ⟨778083, by rfl⟩ : syracuseStep 2074889 = 1556167) B1556167
theorem B1968551 : Blo 1228432 1968551 := bstep (se 1 (by rfl) ⟨1476413, by rfl⟩ : syracuseStep 1968551 = 2952827) B2952827
theorem B1313191 : Blo 1228432 1313191 := bstep (se 1 (by rfl) ⟨984893, by rfl⟩ : syracuseStep 1313191 = 1969787) B1969787
theorem B5253619 : Blo 1228432 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B7883351 : Blo 1228432 7883351 := bstep (se 1 (by rfl) ⟨5912513, by rfl⟩ : syracuseStep 7883351 = 11825027) B11825027
theorem B19180241 : Blo 1228432 19180241 := bstep (se 2 (by rfl) ⟨7192590, by rfl⟩ : syracuseStep 19180241 = 14385181) B14385181
theorem B9333629 : Blo 1228432 9333629 := bstep (se 3 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 9333629 = 3500111) B3500111
theorem B2493355 : Blo 1228432 2493355 := bstep (se 1 (by rfl) ⟨1870016, by rfl⟩ : syracuseStep 2493355 = 3740033) B3740033
theorem B2804711 : Blo 1228432 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B2624503 : Blo 1228432 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B11815951 : Blo 1228432 11815951 := bstep (se 1 (by rfl) ⟨8861963, by rfl⟩ : syracuseStep 11815951 = 17723927) B17723927
theorem B2215145 : Blo 1228432 2215145 := bstep (se 2 (by rfl) ⟨830679, by rfl⟩ : syracuseStep 2215145 = 1661359) B1661359
theorem B2075881 : Blo 1228432 2075881 := bstep (se 2 (by rfl) ⟨778455, by rfl⟩ : syracuseStep 2075881 = 1556911) B1556911
theorem B2764025 : Blo 1228432 2764025 := bstep (se 2 (by rfl) ⟨1036509, by rfl⟩ : syracuseStep 2764025 = 2073019) B2073019
theorem B2075935 : Blo 1228432 2075935 := bstep (se 1 (by rfl) ⟨1556951, by rfl⟩ : syracuseStep 2075935 = 3113903) B3113903
theorem B6221123 : Blo 1228432 6221123 := bstep (se 1 (by rfl) ⟨4665842, by rfl⟩ : syracuseStep 6221123 = 9331685) B9331685
theorem B4730231 : Blo 1228432 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B2764169 : Blo 1228432 2764169 := bstep (se 2 (by rfl) ⟨1036563, by rfl⟩ : syracuseStep 2764169 = 2073127) B2073127
theorem B85126573 : Blo 1228432 85126573 := bstep (se 3 (by rfl) ⟨15961232, by rfl⟩ : syracuseStep 85126573 = 31922465) B31922465
theorem B2764295 : Blo 1228432 2764295 := bstep (se 1 (by rfl) ⟨2073221, by rfl⟩ : syracuseStep 2764295 = 4146443) B4146443
theorem B5983753 : Blo 1228432 5983753 := bstep (se 2 (by rfl) ⟨2243907, by rfl⟩ : syracuseStep 5983753 = 4487815) B4487815
theorem B4148819 : Blo 1228432 4148819 := bstep (se 1 (by rfl) ⟨3111614, by rfl⟩ : syracuseStep 4148819 = 6223229) B6223229
theorem B50466401 : Blo 1228432 50466401 := bstep (se 2 (by rfl) ⟨18924900, by rfl⟩ : syracuseStep 50466401 = 37849801) B37849801
theorem B8867501 : Blo 1228432 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B2764475 : Blo 1228432 2764475 := bstep (se 1 (by rfl) ⟨2073356, by rfl⟩ : syracuseStep 2764475 = 4146713) B4146713
theorem B2076347 : Blo 1228432 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B19943185 : Blo 1228432 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B6221609 : Blo 1228432 6221609 := bstep (se 2 (by rfl) ⟨2333103, by rfl⟩ : syracuseStep 6221609 = 4666207) B4666207
theorem B2764601 : Blo 1228432 2764601 := bstep (se 2 (by rfl) ⟨1036725, by rfl⟩ : syracuseStep 2764601 = 2073451) B2073451
theorem B3321757 : Blo 1228432 3321757 := bstep (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) B1245659
theorem B37851299 : Blo 1228432 37851299 := bstep (se 1 (by rfl) ⟨28388474, by rfl⟩ : syracuseStep 37851299 = 56776949) B56776949
theorem B4665707 : Blo 1228432 4665707 := bstep (se 1 (by rfl) ⟨3499280, by rfl⟩ : syracuseStep 4665707 = 6998561) B6998561
theorem B9974123 : Blo 1228432 9974123 := bstep (se 1 (by rfl) ⟨7480592, by rfl⟩ : syracuseStep 9974123 = 14961185) B14961185
theorem B2765231 : Blo 1228432 2765231 := bstep (se 1 (by rfl) ⟨2073923, by rfl⟩ : syracuseStep 2765231 = 4147847) B4147847
theorem B5247433 : Blo 1228432 5247433 := bstep (se 2 (by rfl) ⟨1967787, by rfl⟩ : syracuseStep 5247433 = 3935575) B3935575
theorem B2765267 : Blo 1228432 2765267 := bstep (se 1 (by rfl) ⟨2073950, by rfl⟩ : syracuseStep 2765267 = 4147901) B4147901
theorem B3502561 : Blo 1228432 3502561 := bstep (se 2 (by rfl) ⟨1313460, by rfl⟩ : syracuseStep 3502561 = 2626921) B2626921
theorem B21017069 : Blo 1228432 21017069 := bstep (se 3 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 21017069 = 7881401) B7881401
theorem B2765375 : Blo 1228432 2765375 := bstep (se 1 (by rfl) ⟨2074031, by rfl⟩ : syracuseStep 2765375 = 4148063) B4148063
theorem B1995337 : Blo 1228432 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B2765483 : Blo 1228432 2765483 := bstep (se 1 (by rfl) ⟨2074112, by rfl⟩ : syracuseStep 2765483 = 4148225) B4148225
theorem B2953903 : Blo 1228432 2953903 := bstep (se 1 (by rfl) ⟨2215427, by rfl⟩ : syracuseStep 2953903 = 4430855) B4430855
theorem B29905631 : Blo 1228432 29905631 := bstep (se 1 (by rfl) ⟨22429223, by rfl⟩ : syracuseStep 29905631 = 44858447) B44858447
theorem B3109711 : Blo 1228432 3109711 := bstep (se 1 (by rfl) ⟨2332283, by rfl⟩ : syracuseStep 3109711 = 4664567) B4664567
theorem B6222905 : Blo 1228432 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B3109985 : Blo 1228432 3109985 := bstep (se 2 (by rfl) ⟨1166244, by rfl⟩ : syracuseStep 3109985 = 2332489) B2332489
theorem B4666511 : Blo 1228432 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B2766023 : Blo 1228432 2766023 := bstep (se 1 (by rfl) ⟨2074517, by rfl⟩ : syracuseStep 2766023 = 4149035) B4149035
theorem B2766203 : Blo 1228432 2766203 := bstep (se 1 (by rfl) ⟨2074652, by rfl⟩ : syracuseStep 2766203 = 4149305) B4149305
theorem B3503483 : Blo 1228432 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B92239249 : Blo 1228432 92239249 := bstep (se 2 (by rfl) ⟨34589718, by rfl⟩ : syracuseStep 92239249 = 69179437) B69179437
theorem B3110359 : Blo 1228432 3110359 := bstep (se 1 (by rfl) ⟨2332769, by rfl⟩ : syracuseStep 3110359 = 4665539) B4665539
theorem B2766329 : Blo 1228432 2766329 := bstep (se 2 (by rfl) ⟨1037373, by rfl⟩ : syracuseStep 2766329 = 2074747) B2074747
theorem B2766419 : Blo 1228432 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B23615225 : Blo 1228432 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B3110663 : Blo 1228432 3110663 := bstep (se 1 (by rfl) ⟨2332997, by rfl⟩ : syracuseStep 3110663 = 4665995) B4665995
theorem B2766599 : Blo 1228432 2766599 := bstep (se 1 (by rfl) ⟨2074949, by rfl⟩ : syracuseStep 2766599 = 4149899) B4149899
theorem B1750825 : Blo 1228432 1750825 := bstep (se 2 (by rfl) ⟨656559, by rfl⟩ : syracuseStep 1750825 = 1313119) B1313119
theorem B14014295 : Blo 1228432 14014295 := bstep (se 1 (by rfl) ⟨10510721, by rfl⟩ : syracuseStep 14014295 = 21021443) B21021443
theorem B13301597 : Blo 1228432 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B18921401 : Blo 1228432 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B3323929 : Blo 1228432 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B2332937 : Blo 1228432 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B3324233 : Blo 1228432 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B2767211 : Blo 1228432 2767211 := bstep (se 1 (by rfl) ⟨2075408, by rfl⟩ : syracuseStep 2767211 = 4150817) B4150817
theorem B9468343 : Blo 1228432 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B4151735 : Blo 1228432 4151735 := bstep (se 1 (by rfl) ⟨3113801, by rfl⟩ : syracuseStep 4151735 = 6227603) B6227603
theorem B2767355 : Blo 1228432 2767355 := bstep (se 1 (by rfl) ⟨2075516, by rfl⟩ : syracuseStep 2767355 = 4151033) B4151033
theorem B3111443 : Blo 1228432 3111443 := bstep (se 1 (by rfl) ⟨2333582, by rfl⟩ : syracuseStep 3111443 = 4667165) B4667165
theorem B1383007 : Blo 1228432 1383007 := bstep (se 1 (by rfl) ⟨1037255, by rfl⟩ : syracuseStep 1383007 = 2074511) B2074511
theorem B2767481 : Blo 1228432 2767481 := bstep (se 2 (by rfl) ⟨1037805, by rfl⟩ : syracuseStep 2767481 = 2075611) B2075611
theorem B2767535 : Blo 1228432 2767535 := bstep (se 1 (by rfl) ⟨2075651, by rfl⟩ : syracuseStep 2767535 = 4151303) B4151303
theorem B2398943 : Blo 1228432 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B4668151 : Blo 1228432 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B2767607 : Blo 1228432 2767607 := bstep (se 1 (by rfl) ⟨2075705, by rfl⟩ : syracuseStep 2767607 = 4151411) B4151411
theorem B2767787 : Blo 1228432 2767787 := bstep (se 1 (by rfl) ⟨2075840, by rfl⟩ : syracuseStep 2767787 = 4151681) B4151681
theorem B11819951 : Blo 1228432 11819951 := bstep (se 1 (by rfl) ⟨8864963, by rfl⟩ : syracuseStep 11819951 = 17729927) B17729927
theorem B4668455 : Blo 1228432 4668455 := bstep (se 1 (by rfl) ⟨3501341, by rfl⟩ : syracuseStep 4668455 = 7002683) B7002683
theorem B6225011 : Blo 1228432 6225011 := bstep (se 1 (by rfl) ⟨4668758, by rfl⟩ : syracuseStep 6225011 = 9337517) B9337517
theorem B17710325 : Blo 1228432 17710325 := bstep (se 5 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 17710325 = 1660343) B1660343
theorem B6651233 : Blo 1228432 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B4988297 : Blo 1228432 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B10640803 : Blo 1228432 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B4488635 : Blo 1228432 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B2768327 : Blo 1228432 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B5905979 : Blo 1228432 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B4431443 : Blo 1228432 4431443 := bstep (se 1 (by rfl) ⟨3323582, by rfl⟩ : syracuseStep 4431443 = 6647165) B6647165
theorem B2334395 : Blo 1228432 2334395 := bstep (se 1 (by rfl) ⟨1750796, by rfl⟩ : syracuseStep 2334395 = 3501593) B3501593
theorem B1228511 : Blo 1228432 1228511 := bstep (se 1 (by rfl) ⟨921383, by rfl⟩ : syracuseStep 1228511 = 1842767) B1842767
theorem B1384159 : Blo 1228432 1384159 := bstep (se 1 (by rfl) ⟨1038119, by rfl⟩ : syracuseStep 1384159 = 2076239) B2076239
theorem B1842923 : Blo 1228432 1842923 := bstep (se 1 (by rfl) ⟨1382192, by rfl⟩ : syracuseStep 1842923 = 2764385) B2764385
theorem B1228591 : Blo 1228432 1228591 := bstep (se 1 (by rfl) ⟨921443, by rfl⟩ : syracuseStep 1228591 = 1842887) B1842887
theorem B21569341 : Blo 1228432 21569341 := bstep (se 3 (by rfl) ⟨4044251, by rfl⟩ : syracuseStep 21569341 = 8088503) B8088503
theorem B35422019 : Blo 1228432 35422019 := bstep (se 1 (by rfl) ⟨26566514, by rfl⟩ : syracuseStep 35422019 = 53133029) B53133029
theorem B10510175 : Blo 1228432 10510175 := bstep (se 1 (by rfl) ⟨7882631, by rfl⟩ : syracuseStep 10510175 = 15765263) B15765263
theorem B1228699 : Blo 1228432 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B6225821 : Blo 1228432 6225821 := bstep (se 3 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 6225821 = 2334683) B2334683
theorem B1228751 : Blo 1228432 1228751 := bstep (se 1 (by rfl) ⟨921563, by rfl⟩ : syracuseStep 1228751 = 1843127) B1843127
theorem B1843151 : Blo 1228432 1843151 := bstep (se 1 (by rfl) ⟨1382363, by rfl⟩ : syracuseStep 1843151 = 2764727) B2764727
theorem B1228775 : Blo 1228432 1228775 := bstep (se 1 (by rfl) ⟨921581, by rfl⟩ : syracuseStep 1228775 = 1843163) B1843163
theorem B4431905 : Blo 1228432 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B1229031 : Blo 1228432 1229031 := bstep (se 1 (by rfl) ⟨921773, by rfl⟩ : syracuseStep 1229031 = 1843547) B1843547
theorem B1843487 : Blo 1228432 1843487 := bstep (se 1 (by rfl) ⟨1382615, by rfl⟩ : syracuseStep 1843487 = 2765231) B2765231
theorem B1843511 : Blo 1228432 1843511 := bstep (se 1 (by rfl) ⟨1382633, by rfl⟩ : syracuseStep 1843511 = 2765267) B2765267
theorem B1843583 : Blo 1228432 1843583 := bstep (se 1 (by rfl) ⟨1382687, by rfl⟩ : syracuseStep 1843583 = 2765375) B2765375
theorem B1229183 : Blo 1228432 1229183 := bstep (se 1 (by rfl) ⟨921887, by rfl⟩ : syracuseStep 1229183 = 1843775) B1843775
theorem B1843655 : Blo 1228432 1843655 := bstep (se 1 (by rfl) ⟨1382741, by rfl⟩ : syracuseStep 1843655 = 2765483) B2765483
theorem B1229263 : Blo 1228432 1229263 := bstep (se 1 (by rfl) ⟨921947, by rfl⟩ : syracuseStep 1229263 = 1843895) B1843895
theorem B12624457 : Blo 1228432 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B6996577 : Blo 1228432 6996577 := bstep (se 2 (by rfl) ⟨2623716, by rfl⟩ : syracuseStep 6996577 = 5247433) B5247433
theorem B1229415 : Blo 1228432 1229415 := bstep (se 1 (by rfl) ⟨922061, by rfl⟩ : syracuseStep 1229415 = 1844123) B1844123
theorem B5907053 : Blo 1228432 5907053 := bstep (se 3 (by rfl) ⟨1107572, by rfl⟩ : syracuseStep 5907053 = 2215145) B2215145
theorem B4670081 : Blo 1228432 4670081 := bstep (se 2 (by rfl) ⟨1751280, by rfl⟩ : syracuseStep 4670081 = 3502561) B3502561
theorem B7004825 : Blo 1228432 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B2073323 : Blo 1228432 2073323 := bstep (se 1 (by rfl) ⟨1554992, by rfl⟩ : syracuseStep 2073323 = 3109985) B3109985
theorem B1844009 : Blo 1228432 1844009 := bstep (se 2 (by rfl) ⟨691503, by rfl⟩ : syracuseStep 1844009 = 1383007) B1383007
theorem B1844015 : Blo 1228432 1844015 := bstep (se 1 (by rfl) ⟨1383011, by rfl⟩ : syracuseStep 1844015 = 2766023) B2766023
theorem B1229679 : Blo 1228432 1229679 := bstep (se 1 (by rfl) ⟨922259, by rfl⟩ : syracuseStep 1229679 = 1844519) B1844519
theorem B1844135 : Blo 1228432 1844135 := bstep (se 1 (by rfl) ⟨1383101, by rfl⟩ : syracuseStep 1844135 = 2766203) B2766203
theorem B1229735 : Blo 1228432 1229735 := bstep (se 1 (by rfl) ⟨922301, by rfl⟩ : syracuseStep 1229735 = 1844603) B1844603
theorem B2335655 : Blo 1228432 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B1844219 : Blo 1228432 1844219 := bstep (se 1 (by rfl) ⟨1383164, by rfl⟩ : syracuseStep 1844219 = 2766329) B2766329
theorem B1229819 : Blo 1228432 1229819 := bstep (se 1 (by rfl) ⟨922364, by rfl⟩ : syracuseStep 1229819 = 1844729) B1844729
theorem B1844279 : Blo 1228432 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B1229887 : Blo 1228432 1229887 := bstep (se 1 (by rfl) ⟨922415, by rfl⟩ : syracuseStep 1229887 = 1844831) B1844831
theorem B4146281 : Blo 1228432 4146281 := bstep (se 2 (by rfl) ⟨1554855, by rfl⟩ : syracuseStep 4146281 = 3109711) B3109711
theorem B11969693 : Blo 1228432 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B2073775 : Blo 1228432 2073775 := bstep (se 1 (by rfl) ⟨1555331, by rfl⟩ : syracuseStep 2073775 = 3110663) B3110663
theorem B1844399 : Blo 1228432 1844399 := bstep (se 1 (by rfl) ⟨1383299, by rfl⟩ : syracuseStep 1844399 = 2766599) B2766599
theorem B1230031 : Blo 1228432 1230031 := bstep (se 1 (by rfl) ⟨922523, by rfl⟩ : syracuseStep 1230031 = 1845047) B1845047
theorem B3499337 : Blo 1228432 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B15754601 : Blo 1228432 15754601 := bstep (se 2 (by rfl) ⟨5907975, by rfl⟩ : syracuseStep 15754601 = 11815951) B11815951
theorem B17958277 : Blo 1228432 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1475995 : Blo 1228432 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B1230235 : Blo 1228432 1230235 := bstep (se 1 (by rfl) ⟨922676, by rfl⟩ : syracuseStep 1230235 = 1845353) B1845353
theorem B1844807 : Blo 1228432 1844807 := bstep (se 1 (by rfl) ⟨1383605, by rfl⟩ : syracuseStep 1844807 = 2767211) B2767211
theorem B1312367 : Blo 1228432 1312367 := bstep (se 1 (by rfl) ⟨984275, by rfl⟩ : syracuseStep 1312367 = 1968551) B1968551
theorem B1844903 : Blo 1228432 1844903 := bstep (se 1 (by rfl) ⟨1383677, by rfl⟩ : syracuseStep 1844903 = 2767355) B2767355
theorem B2074295 : Blo 1228432 2074295 := bstep (se 1 (by rfl) ⟨1555721, by rfl⟩ : syracuseStep 2074295 = 3111443) B3111443
theorem B1844987 : Blo 1228432 1844987 := bstep (se 1 (by rfl) ⟨1383740, by rfl⟩ : syracuseStep 1844987 = 2767481) B2767481
theorem B1845023 : Blo 1228432 1845023 := bstep (se 1 (by rfl) ⟨1383767, by rfl⟩ : syracuseStep 1845023 = 2767535) B2767535
theorem B1599295 : Blo 1228432 1599295 := bstep (se 1 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 1599295 = 2398943) B2398943
theorem B1845071 : Blo 1228432 1845071 := bstep (se 1 (by rfl) ⟨1383803, by rfl⟩ : syracuseStep 1845071 = 2767607) B2767607
theorem B113502097 : Blo 1228432 113502097 := bstep (se 2 (by rfl) ⟨42563286, by rfl⟩ : syracuseStep 113502097 = 85126573) B85126573
theorem B1845191 : Blo 1228432 1845191 := bstep (se 1 (by rfl) ⟨1383893, by rfl⟩ : syracuseStep 1845191 = 2767787) B2767787
theorem B4147145 : Blo 1228432 4147145 := bstep (se 2 (by rfl) ⟨1555179, by rfl⟩ : syracuseStep 4147145 = 3110359) B3110359
theorem B11806883 : Blo 1228432 11806883 := bstep (se 1 (by rfl) ⟨8855162, by rfl⟩ : syracuseStep 11806883 = 17710325) B17710325
theorem B4147415 : Blo 1228432 4147415 := bstep (se 1 (by rfl) ⟨3110561, by rfl⟩ : syracuseStep 4147415 = 6221123) B6221123
theorem B4434155 : Blo 1228432 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B1845545 : Blo 1228432 1845545 := bstep (se 2 (by rfl) ⟨692079, by rfl⟩ : syracuseStep 1845545 = 1384159) B1384159
theorem B1845551 : Blo 1228432 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B47278565 : Blo 1228432 47278565 := bstep (se 4 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 47278565 = 8864731) B8864731
theorem B4147739 : Blo 1228432 4147739 := bstep (se 1 (by rfl) ⟨3110804, by rfl⟩ : syracuseStep 4147739 = 6221609) B6221609
theorem B7006783 : Blo 1228432 7006783 := bstep (se 1 (by rfl) ⟨5255087, by rfl⟩ : syracuseStep 7006783 = 10510175) B10510175
theorem B25234199 : Blo 1228432 25234199 := bstep (se 1 (by rfl) ⟨18925649, by rfl⟩ : syracuseStep 25234199 = 37851299) B37851299
theorem B2075483 : Blo 1228432 2075483 := bstep (se 1 (by rfl) ⟨1556612, by rfl⟩ : syracuseStep 2075483 = 3113225) B3113225
theorem B14011379 : Blo 1228432 14011379 := bstep (se 1 (by rfl) ⟨10508534, by rfl⟩ : syracuseStep 14011379 = 21017069) B21017069
theorem B4729903 : Blo 1228432 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B3501103 : Blo 1228432 3501103 := bstep (se 1 (by rfl) ⟨2625827, by rfl⟩ : syracuseStep 3501103 = 5251655) B5251655
theorem B2075719 : Blo 1228432 2075719 := bstep (se 1 (by rfl) ⟨1556789, by rfl⟩ : syracuseStep 2075719 = 3113579) B3113579
theorem B15756605 : Blo 1228432 15756605 := bstep (se 3 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 15756605 = 5908727) B5908727
theorem B4148603 : Blo 1228432 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B2076151 : Blo 1228432 2076151 := bstep (se 1 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 2076151 = 3114227) B3114227
theorem B2764583 : Blo 1228432 2764583 := bstep (se 1 (by rfl) ⟨2073437, by rfl⟩ : syracuseStep 2764583 = 4146875) B4146875
theorem B9342863 : Blo 1228432 9342863 := bstep (se 1 (by rfl) ⟨7007147, by rfl⟩ : syracuseStep 9342863 = 14014295) B14014295
theorem B8867731 : Blo 1228432 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B2216155 : Blo 1228432 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B11817181 : Blo 1228432 11817181 := bstep (se 3 (by rfl) ⟨2215721, by rfl⟩ : syracuseStep 11817181 = 4431443) B4431443
theorem B5255567 : Blo 1228432 5255567 := bstep (se 1 (by rfl) ⟨3941675, by rfl⟩ : syracuseStep 5255567 = 7883351) B7883351
theorem B6222419 : Blo 1228432 6222419 := bstep (se 1 (by rfl) ⟨4666814, by rfl⟩ : syracuseStep 6222419 = 9333629) B9333629
theorem B4150007 : Blo 1228432 4150007 := bstep (se 1 (by rfl) ⟨3112505, by rfl⟩ : syracuseStep 4150007 = 6225011) B6225011
theorem B2765609 : Blo 1228432 2765609 := bstep (se 2 (by rfl) ⟨1037103, by rfl⟩ : syracuseStep 2765609 = 2074207) B2074207
theorem B3937319 : Blo 1228432 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B2765879 : Blo 1228432 2765879 := bstep (se 1 (by rfl) ⟨2074409, by rfl⟩ : syracuseStep 2765879 = 4148819) B4148819
theorem B2765897 : Blo 1228432 2765897 := bstep (se 2 (by rfl) ⟨1037211, by rfl⟩ : syracuseStep 2765897 = 2074423) B2074423
theorem B28759121 : Blo 1228432 28759121 := bstep (se 2 (by rfl) ⟨10784670, by rfl⟩ : syracuseStep 28759121 = 21569341) B21569341
theorem B5911667 : Blo 1228432 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B4429009 : Blo 1228432 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B23614679 : Blo 1228432 23614679 := bstep (se 1 (by rfl) ⟨17711009, by rfl⟩ : syracuseStep 23614679 = 35422019) B35422019
theorem B4150547 : Blo 1228432 4150547 := bstep (se 1 (by rfl) ⟨3112910, by rfl⟩ : syracuseStep 4150547 = 6225821) B6225821
theorem B3110471 : Blo 1228432 3110471 := bstep (se 1 (by rfl) ⟨2332853, by rfl⟩ : syracuseStep 3110471 = 4665707) B4665707
theorem B6649415 : Blo 1228432 6649415 := bstep (se 1 (by rfl) ⟨4987061, by rfl⟩ : syracuseStep 6649415 = 9974123) B9974123
theorem B1381999 : Blo 1228432 1381999 := bstep (se 1 (by rfl) ⟨1036499, by rfl⟩ : syracuseStep 1381999 = 2072999) B2072999
theorem B1382107 : Blo 1228432 1382107 := bstep (se 1 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 1382107 = 2073161) B2073161
theorem B1660667 : Blo 1228432 1660667 := bstep (se 1 (by rfl) ⟨1245500, by rfl⟩ : syracuseStep 1660667 = 2491001) B2491001
theorem B4151087 : Blo 1228432 4151087 := bstep (se 1 (by rfl) ⟨3113315, by rfl⟩ : syracuseStep 4151087 = 6226631) B6226631
theorem B19937087 : Blo 1228432 19937087 := bstep (se 1 (by rfl) ⟨14952815, by rfl⟩ : syracuseStep 19937087 = 29905631) B29905631
theorem B17733563 : Blo 1228432 17733563 := bstep (se 1 (by rfl) ⟨13300172, by rfl⟩ : syracuseStep 17733563 = 26600345) B26600345
theorem B3111007 : Blo 1228432 3111007 := bstep (se 1 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 3111007 = 4666511) B4666511
theorem B2660449 : Blo 1228432 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B3938537 : Blo 1228432 3938537 := bstep (se 2 (by rfl) ⟨1476951, by rfl⟩ : syracuseStep 3938537 = 2953903) B2953903
theorem B7002409 : Blo 1228432 7002409 := bstep (se 2 (by rfl) ⟨2625903, by rfl⟩ : syracuseStep 7002409 = 5251807) B5251807
theorem B6224201 : Blo 1228432 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B19929563 : Blo 1228432 19929563 := bstep (se 1 (by rfl) ⟨14947172, by rfl⟩ : syracuseStep 19929563 = 29894345) B29894345
theorem B25237979 : Blo 1228432 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B15743483 : Blo 1228432 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B3324473 : Blo 1228432 3324473 := bstep (se 2 (by rfl) ⟨1246677, by rfl⟩ : syracuseStep 3324473 = 2493355) B2493355
theorem B12614267 : Blo 1228432 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B1555291 : Blo 1228432 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B1383259 : Blo 1228432 1383259 := bstep (se 1 (by rfl) ⟨1037444, by rfl⟩ : syracuseStep 1383259 = 2074889) B2074889
theorem B2767823 : Blo 1228432 2767823 := bstep (se 1 (by rfl) ⟨2075867, by rfl⟩ : syracuseStep 2767823 = 4151735) B4151735
theorem B2767841 : Blo 1228432 2767841 := bstep (se 2 (by rfl) ⟨1037940, by rfl⟩ : syracuseStep 2767841 = 2075881) B2075881
theorem B2767913 : Blo 1228432 2767913 := bstep (se 2 (by rfl) ⟨1037967, by rfl⟩ : syracuseStep 2767913 = 2075935) B2075935
theorem B12786827 : Blo 1228432 12786827 := bstep (se 1 (by rfl) ⟨9590120, by rfl⟩ : syracuseStep 12786827 = 19180241) B19180241
theorem B122985665 : Blo 1228432 122985665 := bstep (se 2 (by rfl) ⟨46119624, by rfl⟩ : syracuseStep 122985665 = 92239249) B92239249
theorem B14187737 : Blo 1228432 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B7879967 : Blo 1228432 7879967 := bstep (se 1 (by rfl) ⟨5909975, by rfl⟩ : syracuseStep 7879967 = 11819951) B11819951
theorem B7978337 : Blo 1228432 7978337 := bstep (se 2 (by rfl) ⟨2991876, by rfl⟩ : syracuseStep 7978337 = 5983753) B5983753
theorem B3112303 : Blo 1228432 3112303 := bstep (se 1 (by rfl) ⟨2334227, by rfl⟩ : syracuseStep 3112303 = 4668455) B4668455
theorem B1842683 : Blo 1228432 1842683 := bstep (se 1 (by rfl) ⟨1382012, by rfl⟩ : syracuseStep 1842683 = 2764025) B2764025
theorem B7003685 : Blo 1228432 7003685 := bstep (se 4 (by rfl) ⟨656595, by rfl⟩ : syracuseStep 7003685 = 1313191) B1313191
theorem B3153487 : Blo 1228432 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B1842779 : Blo 1228432 1842779 := bstep (se 1 (by rfl) ⟨1382084, by rfl⟩ : syracuseStep 1842779 = 2764169) B2764169
theorem B3325531 : Blo 1228432 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B1842863 : Blo 1228432 1842863 := bstep (se 1 (by rfl) ⟨1382147, by rfl⟩ : syracuseStep 1842863 = 2764295) B2764295
theorem B26590913 : Blo 1228432 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B2334433 : Blo 1228432 2334433 := bstep (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) B1750825
theorem B33644267 : Blo 1228432 33644267 := bstep (se 1 (by rfl) ⟨25233200, by rfl⟩ : syracuseStep 33644267 = 50466401) B50466401
theorem B1842983 : Blo 1228432 1842983 := bstep (se 1 (by rfl) ⟨1382237, by rfl⟩ : syracuseStep 1842983 = 2764475) B2764475
theorem B1556263 : Blo 1228432 1556263 := bstep (se 1 (by rfl) ⟨1167197, by rfl⟩ : syracuseStep 1556263 = 2334395) B2334395
theorem B1384231 : Blo 1228432 1384231 := bstep (se 1 (by rfl) ⟨1038173, by rfl⟩ : syracuseStep 1384231 = 2076347) B2076347
theorem B1228615 : Blo 1228432 1228615 := bstep (se 1 (by rfl) ⟨921461, by rfl⟩ : syracuseStep 1228615 = 1842923) B1842923
theorem B1843067 : Blo 1228432 1843067 := bstep (se 1 (by rfl) ⟨1382300, by rfl⟩ : syracuseStep 1843067 = 2764601) B2764601
theorem B7479229 : Blo 1228432 7479229 := bstep (se 3 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 7479229 = 2804711) B2804711
theorem B1228767 : Blo 1228432 1228767 := bstep (se 1 (by rfl) ⟨921575, by rfl⟩ : syracuseStep 1228767 = 1843151) B1843151
theorem B3547265 : Blo 1228432 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B1228991 : Blo 1228432 1228991 := bstep (se 1 (by rfl) ⟨921743, by rfl⟩ : syracuseStep 1228991 = 1843487) B1843487
theorem B1229007 : Blo 1228432 1229007 := bstep (se 1 (by rfl) ⟨921755, by rfl⟩ : syracuseStep 1229007 = 1843511) B1843511
theorem B1229055 : Blo 1228432 1229055 := bstep (se 1 (by rfl) ⟨921791, by rfl⟩ : syracuseStep 1229055 = 1843583) B1843583
theorem B1229103 : Blo 1228432 1229103 := bstep (se 1 (by rfl) ⟨921827, by rfl⟩ : syracuseStep 1229103 = 1843655) B1843655
theorem B3113387 : Blo 1228432 3113387 := bstep (se 1 (by rfl) ⟨2335040, by rfl⟩ : syracuseStep 3113387 = 4670081) B4670081
theorem B4669883 : Blo 1228432 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B1843739 : Blo 1228432 1843739 := bstep (se 1 (by rfl) ⟨1382804, by rfl⟩ : syracuseStep 1843739 = 2765609) B2765609
theorem B1229339 : Blo 1228432 1229339 := bstep (se 1 (by rfl) ⟨922004, by rfl⟩ : syracuseStep 1229339 = 1844009) B1844009
theorem B1229343 : Blo 1228432 1229343 := bstep (se 1 (by rfl) ⟨922007, by rfl⟩ : syracuseStep 1229343 = 1844015) B1844015
theorem B1229423 : Blo 1228432 1229423 := bstep (se 1 (by rfl) ⟨922067, by rfl⟩ : syracuseStep 1229423 = 1844135) B1844135
theorem B1229479 : Blo 1228432 1229479 := bstep (se 1 (by rfl) ⟨922109, by rfl⟩ : syracuseStep 1229479 = 1844219) B1844219
theorem B1843919 : Blo 1228432 1843919 := bstep (se 1 (by rfl) ⟨1382939, by rfl⟩ : syracuseStep 1843919 = 2765879) B2765879
theorem B1229519 : Blo 1228432 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B1843931 : Blo 1228432 1843931 := bstep (se 1 (by rfl) ⟨1382948, by rfl⟩ : syracuseStep 1843931 = 2765897) B2765897
theorem B3941111 : Blo 1228432 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B7979795 : Blo 1228432 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B1229599 : Blo 1228432 1229599 := bstep (se 1 (by rfl) ⟨922199, by rfl⟩ : syracuseStep 1229599 = 1844399) B1844399
theorem B10503067 : Blo 1228432 10503067 := bstep (se 1 (by rfl) ⟨7877300, by rfl⟩ : syracuseStep 10503067 = 15754601) B15754601
theorem B2073647 : Blo 1228432 2073647 := bstep (se 1 (by rfl) ⟨1555235, by rfl⟩ : syracuseStep 2073647 = 3110471) B3110471
theorem B1229871 : Blo 1228432 1229871 := bstep (se 1 (by rfl) ⟨922403, by rfl⟩ : syracuseStep 1229871 = 1844807) B1844807
theorem B4432943 : Blo 1228432 4432943 := bstep (se 1 (by rfl) ⟨3324707, by rfl⟩ : syracuseStep 4432943 = 6649415) B6649415
theorem B1229935 : Blo 1228432 1229935 := bstep (se 1 (by rfl) ⟨922451, by rfl⟩ : syracuseStep 1229935 = 1844903) B1844903
theorem B2073721 : Blo 1228432 2073721 := bstep (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) B1555291
theorem B1844345 : Blo 1228432 1844345 := bstep (se 2 (by rfl) ⟨691629, by rfl⟩ : syracuseStep 1844345 = 1383259) B1383259
theorem B1229991 : Blo 1228432 1229991 := bstep (se 1 (by rfl) ⟨922493, by rfl⟩ : syracuseStep 1229991 = 1844987) B1844987
theorem B1230015 : Blo 1228432 1230015 := bstep (se 1 (by rfl) ⟨922511, by rfl⟩ : syracuseStep 1230015 = 1845023) B1845023
theorem B1230047 : Blo 1228432 1230047 := bstep (se 1 (by rfl) ⟨922535, by rfl⟩ : syracuseStep 1230047 = 1845071) B1845071
theorem B11822375 : Blo 1228432 11822375 := bstep (se 1 (by rfl) ⟨8866781, by rfl⟩ : syracuseStep 11822375 = 17733563) B17733563
theorem B1230127 : Blo 1228432 1230127 := bstep (se 1 (by rfl) ⟨922595, by rfl⟩ : syracuseStep 1230127 = 1845191) B1845191
theorem B1230363 : Blo 1228432 1230363 := bstep (se 1 (by rfl) ⟨922772, by rfl⟩ : syracuseStep 1230363 = 1845545) B1845545
theorem B1230367 : Blo 1228432 1230367 := bstep (se 1 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 1230367 = 1845551) B1845551
theorem B3499645 : Blo 1228432 3499645 := bstep (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) B1312367
theorem B10495655 : Blo 1228432 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B1967993 : Blo 1228432 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B1845215 : Blo 1228432 1845215 := bstep (se 1 (by rfl) ⟨1383911, by rfl⟩ : syracuseStep 1845215 = 2767823) B2767823
theorem B1845227 : Blo 1228432 1845227 := bstep (se 1 (by rfl) ⟨1383920, by rfl⟩ : syracuseStep 1845227 = 2767841) B2767841
theorem B9340919 : Blo 1228432 9340919 := bstep (se 1 (by rfl) ⟨7005689, by rfl⟩ : syracuseStep 9340919 = 14011379) B14011379
theorem B1845275 : Blo 1228432 1845275 := bstep (se 1 (by rfl) ⟨1383956, by rfl⟩ : syracuseStep 1845275 = 2767913) B2767913
theorem B4204649 : Blo 1228432 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B4434041 : Blo 1228432 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B5253311 : Blo 1228432 5253311 := bstep (se 1 (by rfl) ⟨3939983, by rfl⟩ : syracuseStep 5253311 = 7879967) B7879967
theorem B10504403 : Blo 1228432 10504403 := bstep (se 1 (by rfl) ⟨7878302, by rfl⟩ : syracuseStep 10504403 = 15756605) B15756605
theorem B5318891 : Blo 1228432 5318891 := bstep (se 1 (by rfl) ⟨3989168, by rfl⟩ : syracuseStep 5318891 = 7978337) B7978337
theorem B2075017 : Blo 1228432 2075017 := bstep (se 2 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 2075017 = 1556263) B1556263
theorem B1845641 : Blo 1228432 1845641 := bstep (se 2 (by rfl) ⟨692115, by rfl⟩ : syracuseStep 1845641 = 1384231) B1384231
theorem B2132393 : Blo 1228432 2132393 := bstep (se 2 (by rfl) ⟨799647, by rfl⟩ : syracuseStep 2132393 = 1599295) B1599295
theorem B6228413 : Blo 1228432 6228413 := bstep (se 3 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 6228413 = 2335655) B2335655
theorem B11823641 : Blo 1228432 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B9972305 : Blo 1228432 9972305 := bstep (se 2 (by rfl) ⟨3739614, by rfl⟩ : syracuseStep 9972305 = 7479229) B7479229
theorem B6228575 : Blo 1228432 6228575 := bstep (se 1 (by rfl) ⟨4671431, by rfl⟩ : syracuseStep 6228575 = 9342863) B9342863
theorem B4148009 : Blo 1228432 4148009 := bstep (se 2 (by rfl) ⟨1555503, by rfl⟩ : syracuseStep 4148009 = 3111007) B3111007
theorem B25226149 : Blo 1228432 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B15756241 : Blo 1228432 15756241 := bstep (se 2 (by rfl) ⟨5908590, by rfl⟩ : syracuseStep 15756241 = 11817181) B11817181
theorem B34098205 : Blo 1228432 34098205 := bstep (se 3 (by rfl) ⟨6393413, by rfl⟩ : syracuseStep 34098205 = 12786827) B12786827
theorem B4148279 : Blo 1228432 4148279 := bstep (se 1 (by rfl) ⟨3111209, by rfl⟩ : syracuseStep 4148279 = 6222419) B6222419
theorem B2624879 : Blo 1228432 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B19172747 : Blo 1228432 19172747 := bstep (se 1 (by rfl) ⟨14379560, by rfl⟩ : syracuseStep 19172747 = 28759121) B28759121
theorem B2764187 : Blo 1228432 2764187 := bstep (se 1 (by rfl) ⟨2073140, by rfl⟩ : syracuseStep 2764187 = 4146281) B4146281
theorem B9342377 : Blo 1228432 9342377 := bstep (se 2 (by rfl) ⟨3503391, by rfl⟩ : syracuseStep 9342377 = 7006783) B7006783
theorem B13291391 : Blo 1228432 13291391 := bstep (se 1 (by rfl) ⟨9968543, by rfl⟩ : syracuseStep 13291391 = 19937087) B19937087
theorem B2764763 : Blo 1228432 2764763 := bstep (se 1 (by rfl) ⟨2073572, by rfl⟩ : syracuseStep 2764763 = 4147145) B4147145
theorem B2764943 : Blo 1228432 2764943 := bstep (se 1 (by rfl) ⟨2073707, by rfl⟩ : syracuseStep 2764943 = 4147415) B4147415
theorem B2625691 : Blo 1228432 2625691 := bstep (se 1 (by rfl) ⟨1969268, by rfl⟩ : syracuseStep 2625691 = 3938537) B3938537
theorem B4149467 : Blo 1228432 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B2765033 : Blo 1228432 2765033 := bstep (se 2 (by rfl) ⟨1036887, by rfl⟩ : syracuseStep 2765033 = 2073775) B2073775
theorem B31519043 : Blo 1228432 31519043 := bstep (se 1 (by rfl) ⟨23639282, by rfl⟩ : syracuseStep 31519043 = 47278565) B47278565
theorem B2765159 : Blo 1228432 2765159 := bstep (se 1 (by rfl) ⟨2073869, by rfl⟩ : syracuseStep 2765159 = 4147739) B4147739
theorem B2216315 : Blo 1228432 2216315 := bstep (se 1 (by rfl) ⟨1662236, by rfl⟩ : syracuseStep 2216315 = 3324473) B3324473
theorem B8409511 : Blo 1228432 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B4149737 : Blo 1228432 4149737 := bstep (se 2 (by rfl) ⟨1556151, by rfl⟩ : syracuseStep 4149737 = 3112303) B3112303
theorem B16822799 : Blo 1228432 16822799 := bstep (se 1 (by rfl) ⟨12617099, by rfl⟩ : syracuseStep 16822799 = 25234199) B25234199
theorem B4428445 : Blo 1228432 4428445 := bstep (se 3 (by rfl) ⟨830333, by rfl⟩ : syracuseStep 4428445 = 1660667) B1660667
theorem B95777477 : Blo 1228432 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B81990443 : Blo 1228432 81990443 := bstep (se 1 (by rfl) ⟨61492832, by rfl⟩ : syracuseStep 81990443 = 122985665) B122985665
theorem B9458491 : Blo 1228432 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B2765735 : Blo 1228432 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B151336129 : Blo 1228432 151336129 := bstep (se 2 (by rfl) ⟨56751048, by rfl⟩ : syracuseStep 151336129 = 113502097) B113502097
theorem B2954603 : Blo 1228432 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B3503711 : Blo 1228432 3503711 := bstep (se 1 (by rfl) ⟨2627783, by rfl⟩ : syracuseStep 3503711 = 5255567) B5255567
theorem B2954873 : Blo 1228432 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B9336545 : Blo 1228432 9336545 := bstep (se 2 (by rfl) ⟨3501204, by rfl⟩ : syracuseStep 9336545 = 7002409) B7002409
theorem B1382215 : Blo 1228432 1382215 := bstep (se 1 (by rfl) ⟨1036661, by rfl⟩ : syracuseStep 1382215 = 2073323) B2073323
theorem B2766671 : Blo 1228432 2766671 := bstep (se 1 (by rfl) ⟨2075003, by rfl⟩ : syracuseStep 2766671 = 4150007) B4150007
theorem B16832609 : Blo 1228432 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B9328769 : Blo 1228432 9328769 := bstep (se 2 (by rfl) ⟨3498288, by rfl⟩ : syracuseStep 9328769 = 6996577) B6996577
theorem B15743119 : Blo 1228432 15743119 := bstep (se 1 (by rfl) ⟨11807339, by rfl⟩ : syracuseStep 15743119 = 23614679) B23614679
theorem B2767031 : Blo 1228432 2767031 := bstep (se 1 (by rfl) ⟨2075273, by rfl⟩ : syracuseStep 2767031 = 4150547) B4150547
theorem B2332891 : Blo 1228432 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B1382863 : Blo 1228432 1382863 := bstep (se 1 (by rfl) ⟨1037147, by rfl⟩ : syracuseStep 1382863 = 2074295) B2074295
theorem B2767391 : Blo 1228432 2767391 := bstep (se 1 (by rfl) ⟨2075543, by rfl⟩ : syracuseStep 2767391 = 4151087) B4151087
theorem B4668137 : Blo 1228432 4668137 := bstep (se 2 (by rfl) ⟨1750551, by rfl⟩ : syracuseStep 4668137 = 3501103) B3501103
theorem B2767625 : Blo 1228432 2767625 := bstep (se 2 (by rfl) ⟨1037859, by rfl⟩ : syracuseStep 2767625 = 2075719) B2075719
theorem B7871255 : Blo 1228432 7871255 := bstep (se 1 (by rfl) ⟨5903441, by rfl⟩ : syracuseStep 7871255 = 11806883) B11806883
theorem B2956103 : Blo 1228432 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B5905345 : Blo 1228432 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B15752141 : Blo 1228432 15752141 := bstep (se 3 (by rfl) ⟨2953526, by rfl⟩ : syracuseStep 15752141 = 5907053) B5907053
theorem B13286375 : Blo 1228432 13286375 := bstep (se 1 (by rfl) ⟨9964781, by rfl⟩ : syracuseStep 13286375 = 19929563) B19929563
theorem B16825319 : Blo 1228432 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B1383655 : Blo 1228432 1383655 := bstep (se 1 (by rfl) ⟨1037741, by rfl⟩ : syracuseStep 1383655 = 2075483) B2075483
theorem B2768201 : Blo 1228432 2768201 := bstep (se 2 (by rfl) ⟨1038075, by rfl⟩ : syracuseStep 2768201 = 2076151) B2076151
theorem B1842665 : Blo 1228432 1842665 := bstep (se 2 (by rfl) ⟨690999, by rfl⟩ : syracuseStep 1842665 = 1381999) B1381999
theorem B1842809 : Blo 1228432 1842809 := bstep (se 2 (by rfl) ⟨691053, by rfl⟩ : syracuseStep 1842809 = 1382107) B1382107
theorem B3112577 : Blo 1228432 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B1228455 : Blo 1228432 1228455 := bstep (se 1 (by rfl) ⟨921341, by rfl⟩ : syracuseStep 1228455 = 1842683) B1842683
theorem B4669123 : Blo 1228432 4669123 := bstep (se 1 (by rfl) ⟨3501842, by rfl⟩ : syracuseStep 4669123 = 7003685) B7003685
theorem B1228519 : Blo 1228432 1228519 := bstep (se 1 (by rfl) ⟨921389, by rfl⟩ : syracuseStep 1228519 = 1842779) B1842779
theorem B1228575 : Blo 1228432 1228575 := bstep (se 1 (by rfl) ⟨921431, by rfl⟩ : syracuseStep 1228575 = 1842863) B1842863
theorem B17727275 : Blo 1228432 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B22429511 : Blo 1228432 22429511 := bstep (se 1 (by rfl) ⟨16822133, by rfl⟩ : syracuseStep 22429511 = 33644267) B33644267
theorem B1228655 : Blo 1228432 1228655 := bstep (se 1 (by rfl) ⟨921491, by rfl⟩ : syracuseStep 1228655 = 1842983) B1842983
theorem B1843055 : Blo 1228432 1843055 := bstep (se 1 (by rfl) ⟨1382291, by rfl⟩ : syracuseStep 1843055 = 2764583) B2764583
theorem B1228711 : Blo 1228432 1228711 := bstep (se 1 (by rfl) ⟨921533, by rfl⟩ : syracuseStep 1228711 = 1843067) B1843067
theorem B1843295 : Blo 1228432 1843295 := bstep (se 1 (by rfl) ⟨1382471, by rfl⟩ : syracuseStep 1843295 = 2764943) B2764943
theorem B1843355 : Blo 1228432 1843355 := bstep (se 1 (by rfl) ⟨1382516, by rfl⟩ : syracuseStep 1843355 = 2765033) B2765033
theorem B21012695 : Blo 1228432 21012695 := bstep (se 1 (by rfl) ⟨15759521, by rfl⟩ : syracuseStep 21012695 = 31519043) B31519043
theorem B1843439 : Blo 1228432 1843439 := bstep (se 1 (by rfl) ⟨1382579, by rfl⟩ : syracuseStep 1843439 = 2765159) B2765159
theorem B3113255 : Blo 1228432 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B11215199 : Blo 1228432 11215199 := bstep (se 1 (by rfl) ⟨8411399, by rfl⟩ : syracuseStep 11215199 = 16822799) B16822799
theorem B1229159 : Blo 1228432 1229159 := bstep (se 1 (by rfl) ⟨921869, by rfl⟩ : syracuseStep 1229159 = 1843739) B1843739
theorem B1229279 : Blo 1228432 1229279 := bstep (se 1 (by rfl) ⟨921959, by rfl⟩ : syracuseStep 1229279 = 1843919) B1843919
theorem B1229287 : Blo 1228432 1229287 := bstep (se 1 (by rfl) ⟨921965, by rfl⟩ : syracuseStep 1229287 = 1843931) B1843931
theorem B1843817 : Blo 1228432 1843817 := bstep (se 2 (by rfl) ⟨691431, by rfl⟩ : syracuseStep 1843817 = 1382863) B1382863
theorem B1843823 : Blo 1228432 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B1229563 : Blo 1228432 1229563 := bstep (se 1 (by rfl) ⟨922172, by rfl⟩ : syracuseStep 1229563 = 1844345) B1844345
theorem B7881583 : Blo 1228432 7881583 := bstep (se 1 (by rfl) ⟨5911187, by rfl⟩ : syracuseStep 7881583 = 11822375) B11822375
theorem B51127325 : Blo 1228432 51127325 := bstep (se 3 (by rfl) ⟨9586373, by rfl⟩ : syracuseStep 51127325 = 19172747) B19172747
theorem B2335807 : Blo 1228432 2335807 := bstep (se 1 (by rfl) ⟨1751855, by rfl⟩ : syracuseStep 2335807 = 3503711) B3503711
theorem B6997103 : Blo 1228432 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B5686381 : Blo 1228432 5686381 := bstep (se 3 (by rfl) ⟨1066196, by rfl⟩ : syracuseStep 5686381 = 2132393) B2132393
theorem B1844447 : Blo 1228432 1844447 := bstep (se 1 (by rfl) ⟨1383335, by rfl⟩ : syracuseStep 1844447 = 2766671) B2766671
theorem B1311995 : Blo 1228432 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B7873793 : Blo 1228432 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B1230143 : Blo 1228432 1230143 := bstep (se 1 (by rfl) ⟨922607, by rfl⟩ : syracuseStep 1230143 = 1845215) B1845215
theorem B1230151 : Blo 1228432 1230151 := bstep (se 1 (by rfl) ⟨922613, by rfl⟩ : syracuseStep 1230151 = 1845227) B1845227
theorem B6227279 : Blo 1228432 6227279 := bstep (se 1 (by rfl) ⟨4670459, by rfl⟩ : syracuseStep 6227279 = 9340919) B9340919
theorem B1230183 : Blo 1228432 1230183 := bstep (se 1 (by rfl) ⟨922637, by rfl⟩ : syracuseStep 1230183 = 1845275) B1845275
theorem B2803099 : Blo 1228432 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B6219179 : Blo 1228432 6219179 := bstep (se 1 (by rfl) ⟨4664384, by rfl⟩ : syracuseStep 6219179 = 9328769) B9328769
theorem B1844687 : Blo 1228432 1844687 := bstep (se 1 (by rfl) ⟨1383515, by rfl⟩ : syracuseStep 1844687 = 2767031) B2767031
theorem B1230427 : Blo 1228432 1230427 := bstep (se 1 (by rfl) ⟨922820, by rfl⟩ : syracuseStep 1230427 = 1845641) B1845641
theorem B1844873 : Blo 1228432 1844873 := bstep (se 2 (by rfl) ⟨691827, by rfl⟩ : syracuseStep 1844873 = 1383655) B1383655
theorem B7882427 : Blo 1228432 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B1844927 : Blo 1228432 1844927 := bstep (se 1 (by rfl) ⟨1383695, by rfl⟩ : syracuseStep 1844927 = 2767391) B2767391
theorem B1845083 : Blo 1228432 1845083 := bstep (se 1 (by rfl) ⟨1383812, by rfl⟩ : syracuseStep 1845083 = 2767625) B2767625
theorem B8857583 : Blo 1228432 8857583 := bstep (se 1 (by rfl) ⟨6643187, by rfl⟩ : syracuseStep 8857583 = 13286375) B13286375
theorem B11216879 : Blo 1228432 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B1845467 : Blo 1228432 1845467 := bstep (se 1 (by rfl) ⟨1384100, by rfl⟩ : syracuseStep 1845467 = 2768201) B2768201
theorem B6228251 : Blo 1228432 6228251 := bstep (se 1 (by rfl) ⟨4671188, by rfl⟩ : syracuseStep 6228251 = 9342377) B9342377
theorem B2075051 : Blo 1228432 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B14953007 : Blo 1228432 14953007 := bstep (se 1 (by rfl) ⟨11214755, by rfl⟩ : syracuseStep 14953007 = 22429511) B22429511
theorem B20990825 : Blo 1228432 20990825 := bstep (se 2 (by rfl) ⟨7871559, by rfl⟩ : syracuseStep 20990825 = 15743119) B15743119
theorem B3500921 : Blo 1228432 3500921 := bstep (se 2 (by rfl) ⟨1312845, by rfl⟩ : syracuseStep 3500921 = 2625691) B2625691
theorem B1477543 : Blo 1228432 1477543 := bstep (se 1 (by rfl) ⟨1108157, by rfl⟩ : syracuseStep 1477543 = 2216315) B2216315
theorem B2075591 : Blo 1228432 2075591 := bstep (se 1 (by rfl) ⟨1556693, by rfl⟩ : syracuseStep 2075591 = 3113387) B3113387
theorem B63851651 : Blo 1228432 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B5319863 : Blo 1228432 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B54660295 : Blo 1228432 54660295 := bstep (se 1 (by rfl) ⟨40995221, by rfl⟩ : syracuseStep 54660295 = 81990443) B81990443
theorem B12611321 : Blo 1228432 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B1969915 : Blo 1228432 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B14004089 : Blo 1228432 14004089 := bstep (se 2 (by rfl) ⟨5251533, by rfl⟩ : syracuseStep 14004089 = 10503067) B10503067
theorem B21008321 : Blo 1228432 21008321 := bstep (se 2 (by rfl) ⟨7878120, by rfl⟩ : syracuseStep 21008321 = 15756241) B15756241
theorem B3502207 : Blo 1228432 3502207 := bstep (se 1 (by rfl) ⟨2626655, by rfl⟩ : syracuseStep 3502207 = 5253311) B5253311
theorem B2764961 : Blo 1228432 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B201781505 : Blo 1228432 201781505 := bstep (se 2 (by rfl) ⟨75668064, by rfl⟩ : syracuseStep 201781505 = 151336129) B151336129
theorem B6648203 : Blo 1228432 6648203 := bstep (se 1 (by rfl) ⟨4986152, by rfl⟩ : syracuseStep 6648203 = 9972305) B9972305
theorem B5247503 : Blo 1228432 5247503 := bstep (se 1 (by rfl) ⟨3935627, by rfl⟩ : syracuseStep 5247503 = 7871255) B7871255
theorem B2765339 : Blo 1228432 2765339 := bstep (se 1 (by rfl) ⟨2074004, by rfl⟩ : syracuseStep 2765339 = 4148009) B4148009
theorem B1970735 : Blo 1228432 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B2765519 : Blo 1228432 2765519 := bstep (se 1 (by rfl) ⟨2074139, by rfl⟩ : syracuseStep 2765519 = 4148279) B4148279
theorem B4666193 : Blo 1228432 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B1749919 : Blo 1228432 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B11818183 : Blo 1228432 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B8860927 : Blo 1228432 8860927 := bstep (se 1 (by rfl) ⟨6645695, by rfl⟩ : syracuseStep 8860927 = 13291391) B13291391
theorem B2766311 : Blo 1228432 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B3110521 : Blo 1228432 3110521 := bstep (se 2 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 3110521 = 2332891) B2332891
theorem B2766491 : Blo 1228432 2766491 := bstep (se 1 (by rfl) ⟨2074868, by rfl⟩ : syracuseStep 2766491 = 4149737) B4149737
theorem B2627407 : Blo 1228432 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B2766689 : Blo 1228432 2766689 := bstep (se 2 (by rfl) ⟨1037508, by rfl⟩ : syracuseStep 2766689 = 2075017) B2075017
theorem B11212681 : Blo 1228432 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B1382431 : Blo 1228432 1382431 := bstep (se 1 (by rfl) ⟨1036823, by rfl⟩ : syracuseStep 1382431 = 2073647) B2073647
theorem B2955295 : Blo 1228432 2955295 := bstep (se 1 (by rfl) ⟨2216471, by rfl⟩ : syracuseStep 2955295 = 4432943) B4432943
theorem B5904593 : Blo 1228432 5904593 := bstep (se 2 (by rfl) ⟨2214222, by rfl⟩ : syracuseStep 5904593 = 4428445) B4428445
theorem B7878941 : Blo 1228432 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B6224363 : Blo 1228432 6224363 := bstep (se 1 (by rfl) ⟨4668272, by rfl⟩ : syracuseStep 6224363 = 9336545) B9336545
theorem B33634865 : Blo 1228432 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B37837493 : Blo 1228432 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B45464273 : Blo 1228432 45464273 := bstep (se 2 (by rfl) ⟨17049102, by rfl⟩ : syracuseStep 45464273 = 34098205) B34098205
theorem B11221739 : Blo 1228432 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B2956027 : Blo 1228432 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B7002935 : Blo 1228432 7002935 := bstep (se 1 (by rfl) ⟨5252201, by rfl⟩ : syracuseStep 7002935 = 10504403) B10504403
theorem B3545927 : Blo 1228432 3545927 := bstep (se 1 (by rfl) ⟨2659445, by rfl⟩ : syracuseStep 3545927 = 5318891) B5318891
theorem B4152275 : Blo 1228432 4152275 := bstep (se 1 (by rfl) ⟨3114206, by rfl⟩ : syracuseStep 4152275 = 6228413) B6228413
theorem B4152383 : Blo 1228432 4152383 := bstep (se 1 (by rfl) ⟨3114287, by rfl⟩ : syracuseStep 4152383 = 6228575) B6228575
theorem B3112091 : Blo 1228432 3112091 := bstep (se 1 (by rfl) ⟨2334068, by rfl⟩ : syracuseStep 3112091 = 4668137) B4668137
theorem B10501427 : Blo 1228432 10501427 := bstep (se 1 (by rfl) ⟨7876070, by rfl⟩ : syracuseStep 10501427 = 15752141) B15752141
theorem B6225497 : Blo 1228432 6225497 := bstep (se 2 (by rfl) ⟨2334561, by rfl⟩ : syracuseStep 6225497 = 4669123) B4669123
theorem B1842791 : Blo 1228432 1842791 := bstep (se 1 (by rfl) ⟨1382093, by rfl⟩ : syracuseStep 1842791 = 2764187) B2764187
theorem B1228443 : Blo 1228432 1228443 := bstep (se 1 (by rfl) ⟨921332, by rfl⟩ : syracuseStep 1228443 = 1842665) B1842665
theorem B1228539 : Blo 1228432 1228539 := bstep (se 1 (by rfl) ⟨921404, by rfl⟩ : syracuseStep 1228539 = 1842809) B1842809
theorem B1842953 : Blo 1228432 1842953 := bstep (se 2 (by rfl) ⟨691107, by rfl⟩ : syracuseStep 1842953 = 1382215) B1382215
theorem B1228703 : Blo 1228432 1228703 := bstep (se 1 (by rfl) ⟨921527, by rfl⟩ : syracuseStep 1228703 = 1843055) B1843055
theorem B1843175 : Blo 1228432 1843175 := bstep (se 1 (by rfl) ⟨1382381, by rfl⟩ : syracuseStep 1843175 = 2764763) B2764763
theorem B1843241 : Blo 1228432 1843241 := bstep (se 2 (by rfl) ⟨691215, by rfl⟩ : syracuseStep 1843241 = 1382431) B1382431
theorem B1228863 : Blo 1228432 1228863 := bstep (se 1 (by rfl) ⟨921647, by rfl⟩ : syracuseStep 1228863 = 1843295) B1843295
theorem B1228903 : Blo 1228432 1228903 := bstep (se 1 (by rfl) ⟨921677, by rfl⟩ : syracuseStep 1228903 = 1843355) B1843355
theorem B1843307 : Blo 1228432 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B14008463 : Blo 1228432 14008463 := bstep (se 1 (by rfl) ⟨10506347, by rfl⟩ : syracuseStep 14008463 = 21012695) B21012695
theorem B1228959 : Blo 1228432 1228959 := bstep (se 1 (by rfl) ⟨921719, by rfl⟩ : syracuseStep 1228959 = 1843439) B1843439
theorem B15761573 : Blo 1228432 15761573 := bstep (se 4 (by rfl) ⟨1477647, by rfl⟩ : syracuseStep 15761573 = 2955295) B2955295
theorem B4669609 : Blo 1228432 4669609 := bstep (se 2 (by rfl) ⟨1751103, by rfl⟩ : syracuseStep 4669609 = 3502207) B3502207
theorem B134521003 : Blo 1228432 134521003 := bstep (se 1 (by rfl) ⟨100890752, by rfl⟩ : syracuseStep 134521003 = 201781505) B201781505
theorem B3498335 : Blo 1228432 3498335 := bstep (se 1 (by rfl) ⟨2623751, by rfl⟩ : syracuseStep 3498335 = 5247503) B5247503
theorem B1843559 : Blo 1228432 1843559 := bstep (se 1 (by rfl) ⟨1382669, by rfl⟩ : syracuseStep 1843559 = 2765339) B2765339
theorem B1229211 : Blo 1228432 1229211 := bstep (se 1 (by rfl) ⟨921908, by rfl⟩ : syracuseStep 1229211 = 1843817) B1843817
theorem B1229215 : Blo 1228432 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B1843679 : Blo 1228432 1843679 := bstep (se 1 (by rfl) ⟨1382759, by rfl⟩ : syracuseStep 1843679 = 2765519) B2765519
theorem B30327365 : Blo 1228432 30327365 := bstep (se 4 (by rfl) ⟨2843190, by rfl⟩ : syracuseStep 30327365 = 5686381) B5686381
theorem B3498653 : Blo 1228432 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B1229631 : Blo 1228432 1229631 := bstep (se 1 (by rfl) ⟨922223, by rfl⟩ : syracuseStep 1229631 = 1844447) B1844447
theorem B4146119 : Blo 1228432 4146119 := bstep (se 1 (by rfl) ⟨3109589, by rfl⟩ : syracuseStep 4146119 = 6219179) B6219179
theorem B1229791 : Blo 1228432 1229791 := bstep (se 1 (by rfl) ⟨922343, by rfl⟩ : syracuseStep 1229791 = 1844687) B1844687
theorem B1844207 : Blo 1228432 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B3941369 : Blo 1228432 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B17728541 : Blo 1228432 17728541 := bstep (se 3 (by rfl) ⟨3324101, by rfl⟩ : syracuseStep 17728541 = 6648203) B6648203
theorem B1229915 : Blo 1228432 1229915 := bstep (se 1 (by rfl) ⟨922436, by rfl⟩ : syracuseStep 1229915 = 1844873) B1844873
theorem B1844327 : Blo 1228432 1844327 := bstep (se 1 (by rfl) ⟨1383245, by rfl⟩ : syracuseStep 1844327 = 2766491) B2766491
theorem B1229951 : Blo 1228432 1229951 := bstep (se 1 (by rfl) ⟨922463, by rfl⟩ : syracuseStep 1229951 = 1844927) B1844927
theorem B1230055 : Blo 1228432 1230055 := bstep (se 1 (by rfl) ⟨922541, by rfl⟩ : syracuseStep 1230055 = 1845083) B1845083
theorem B1844459 : Blo 1228432 1844459 := bstep (se 1 (by rfl) ⟨1383344, by rfl⟩ : syracuseStep 1844459 = 2766689) B2766689
theorem B1230311 : Blo 1228432 1230311 := bstep (se 1 (by rfl) ⟨922733, by rfl⟩ : syracuseStep 1230311 = 1845467) B1845467
theorem B5252627 : Blo 1228432 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B11814569 : Blo 1228432 11814569 := bstep (se 2 (by rfl) ⟨4430463, by rfl⟩ : syracuseStep 11814569 = 8860927) B8860927
theorem B22423243 : Blo 1228432 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B25224995 : Blo 1228432 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B7481159 : Blo 1228432 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B3737465 : Blo 1228432 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B13993883 : Blo 1228432 13993883 := bstep (se 1 (by rfl) ⟨10495412, by rfl⟩ : syracuseStep 13993883 = 20990825) B20990825
theorem B42567767 : Blo 1228432 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B2074727 : Blo 1228432 2074727 := bstep (se 1 (by rfl) ⟨1556045, by rfl⟩ : syracuseStep 2074727 = 3112091) B3112091
theorem B4147361 : Blo 1228432 4147361 := bstep (se 2 (by rfl) ⟨1555260, by rfl⟩ : syracuseStep 4147361 = 3110521) B3110521
theorem B8407547 : Blo 1228432 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B2075503 : Blo 1228432 2075503 := bstep (se 1 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 2075503 = 3113255) B3113255
theorem B4664735 : Blo 1228432 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B5254951 : Blo 1228432 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B1970057 : Blo 1228432 1970057 := bstep (se 2 (by rfl) ⟨738771, by rfl⟩ : syracuseStep 1970057 = 1477543) B1477543
theorem B5255293 : Blo 1228432 5255293 := bstep (se 3 (by rfl) ⟨985367, by rfl⟩ : syracuseStep 5255293 = 1970735) B1970735
theorem B3936395 : Blo 1228432 3936395 := bstep (se 1 (by rfl) ⟨2952296, by rfl⟩ : syracuseStep 3936395 = 5904593) B5904593
theorem B15757577 : Blo 1228432 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B72880393 : Blo 1228432 72880393 := bstep (se 2 (by rfl) ⟨27330147, by rfl⟩ : syracuseStep 72880393 = 54660295) B54660295
theorem B4149575 : Blo 1228432 4149575 := bstep (se 1 (by rfl) ⟨3112181, by rfl⟩ : syracuseStep 4149575 = 6224363) B6224363
theorem B14012837 : Blo 1228432 14012837 := bstep (se 4 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 14012837 = 2627407) B2627407
theorem B2363951 : Blo 1228432 2363951 := bstep (se 1 (by rfl) ⟨1772963, by rfl⟩ : syracuseStep 2363951 = 3545927) B3545927
theorem B7000951 : Blo 1228432 7000951 := bstep (se 1 (by rfl) ⟨5250713, by rfl⟩ : syracuseStep 7000951 = 10501427) B10501427
theorem B2626553 : Blo 1228432 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B4150331 : Blo 1228432 4150331 := bstep (se 1 (by rfl) ⟨3112748, by rfl⟩ : syracuseStep 4150331 = 6225497) B6225497
theorem B9336059 : Blo 1228432 9336059 := bstep (se 1 (by rfl) ⟨7002044, by rfl⟩ : syracuseStep 9336059 = 14004089) B14004089
theorem B14005547 : Blo 1228432 14005547 := bstep (se 1 (by rfl) ⟨10504160, by rfl⟩ : syracuseStep 14005547 = 21008321) B21008321
theorem B7476799 : Blo 1228432 7476799 := bstep (se 1 (by rfl) ⟨5607599, by rfl⟩ : syracuseStep 7476799 = 11215199) B11215199
theorem B3110795 : Blo 1228432 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B34084883 : Blo 1228432 34084883 := bstep (se 1 (by rfl) ⟨25563662, by rfl⟩ : syracuseStep 34084883 = 51127325) B51127325
theorem B3114409 : Blo 1228432 3114409 := bstep (se 2 (by rfl) ⟨1167903, by rfl⟩ : syracuseStep 3114409 = 2335807) B2335807
theorem B5249195 : Blo 1228432 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B4151519 : Blo 1228432 4151519 := bstep (se 1 (by rfl) ⟨3113639, by rfl⟩ : syracuseStep 4151519 = 6227279) B6227279
theorem B10508777 : Blo 1228432 10508777 := bstep (se 2 (by rfl) ⟨3940791, by rfl⟩ : syracuseStep 10508777 = 7881583) B7881583
theorem B2333225 : Blo 1228432 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B5905055 : Blo 1228432 5905055 := bstep (se 1 (by rfl) ⟨4428791, by rfl⟩ : syracuseStep 5905055 = 8857583) B8857583
theorem B7477919 : Blo 1228432 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B4152167 : Blo 1228432 4152167 := bstep (se 1 (by rfl) ⟨3114125, by rfl⟩ : syracuseStep 4152167 = 6228251) B6228251
theorem B1383367 : Blo 1228432 1383367 := bstep (se 1 (by rfl) ⟨1037525, by rfl⟩ : syracuseStep 1383367 = 2075051) B2075051
theorem B9968671 : Blo 1228432 9968671 := bstep (se 1 (by rfl) ⟨7476503, by rfl⟩ : syracuseStep 9968671 = 14953007) B14953007
theorem B30309515 : Blo 1228432 30309515 := bstep (se 1 (by rfl) ⟨22732136, by rfl⟩ : syracuseStep 30309515 = 45464273) B45464273
theorem B4668623 : Blo 1228432 4668623 := bstep (se 1 (by rfl) ⟨3501467, by rfl⟩ : syracuseStep 4668623 = 7002935) B7002935
theorem B2333947 : Blo 1228432 2333947 := bstep (se 1 (by rfl) ⟨1750460, by rfl⟩ : syracuseStep 2333947 = 3500921) B3500921
theorem B1383727 : Blo 1228432 1383727 := bstep (se 1 (by rfl) ⟨1037795, by rfl⟩ : syracuseStep 1383727 = 2075591) B2075591
theorem B2768183 : Blo 1228432 2768183 := bstep (se 1 (by rfl) ⟨2076137, by rfl⟩ : syracuseStep 2768183 = 4152275) B4152275
theorem B2768255 : Blo 1228432 2768255 := bstep (se 1 (by rfl) ⟨2076191, by rfl⟩ : syracuseStep 2768255 = 4152383) B4152383
theorem B3546575 : Blo 1228432 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B1228527 : Blo 1228432 1228527 := bstep (se 1 (by rfl) ⟨921395, by rfl⟩ : syracuseStep 1228527 = 1842791) B1842791
theorem B1228635 : Blo 1228432 1228635 := bstep (se 1 (by rfl) ⟨921476, by rfl⟩ : syracuseStep 1228635 = 1842953) B1842953
theorem B14950241 : Blo 1228432 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B1228783 : Blo 1228432 1228783 := bstep (se 1 (by rfl) ⟨921587, by rfl⟩ : syracuseStep 1228783 = 1843175) B1843175
theorem B1228827 : Blo 1228432 1228827 := bstep (se 1 (by rfl) ⟨921620, by rfl⟩ : syracuseStep 1228827 = 1843241) B1843241
theorem B1228871 : Blo 1228432 1228871 := bstep (se 1 (by rfl) ⟨921653, by rfl⟩ : syracuseStep 1228871 = 1843307) B1843307
theorem B9338975 : Blo 1228432 9338975 := bstep (se 1 (by rfl) ⟨7004231, by rfl⟩ : syracuseStep 9338975 = 14008463) B14008463
theorem B6226145 : Blo 1228432 6226145 := bstep (se 2 (by rfl) ⟨2334804, by rfl⟩ : syracuseStep 6226145 = 4669609) B4669609
theorem B1229039 : Blo 1228432 1229039 := bstep (se 1 (by rfl) ⟨921779, by rfl⟩ : syracuseStep 1229039 = 1843559) B1843559
theorem B1229119 : Blo 1228432 1229119 := bstep (se 1 (by rfl) ⟨921839, by rfl⟩ : syracuseStep 1229119 = 1843679) B1843679
theorem B97173857 : Blo 1228432 97173857 := bstep (se 2 (by rfl) ⟨36440196, by rfl⟩ : syracuseStep 97173857 = 72880393) B72880393
theorem B20218243 : Blo 1228432 20218243 := bstep (se 1 (by rfl) ⟨15163682, by rfl⟩ : syracuseStep 20218243 = 30327365) B30327365
theorem B1229471 : Blo 1228432 1229471 := bstep (se 1 (by rfl) ⟨922103, by rfl⟩ : syracuseStep 1229471 = 1844207) B1844207
theorem B1229551 : Blo 1228432 1229551 := bstep (se 1 (by rfl) ⟨922163, by rfl⟩ : syracuseStep 1229551 = 1844327) B1844327
theorem B1229639 : Blo 1228432 1229639 := bstep (se 1 (by rfl) ⟨922229, by rfl⟩ : syracuseStep 1229639 = 1844459) B1844459
theorem B2491643 : Blo 1228432 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B2073863 : Blo 1228432 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B1844489 : Blo 1228432 1844489 := bstep (se 2 (by rfl) ⟨691683, by rfl⟩ : syracuseStep 1844489 = 1383367) B1383367
theorem B28378511 : Blo 1228432 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B3499463 : Blo 1228432 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B7005851 : Blo 1228432 7005851 := bstep (se 1 (by rfl) ⟨5254388, by rfl⟩ : syracuseStep 7005851 = 10508777) B10508777
theorem B5605031 : Blo 1228432 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B1844969 : Blo 1228432 1844969 := bstep (se 2 (by rfl) ⟨691863, by rfl⟩ : syracuseStep 1844969 = 1383727) B1383727
theorem B1845455 : Blo 1228432 1845455 := bstep (se 1 (by rfl) ⟨1384091, by rfl⟩ : syracuseStep 1845455 = 2768183) B2768183
theorem B1845503 : Blo 1228432 1845503 := bstep (se 1 (by rfl) ⟨1384127, by rfl⟩ : syracuseStep 1845503 = 2768255) B2768255
theorem B7006601 : Blo 1228432 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B1313371 : Blo 1228432 1313371 := bstep (se 1 (by rfl) ⟨985028, by rfl⟩ : syracuseStep 1313371 = 1970057) B1970057
theorem B7007057 : Blo 1228432 7007057 := bstep (se 2 (by rfl) ⟨2627646, by rfl⟩ : syracuseStep 7007057 = 5255293) B5255293
theorem B10505051 : Blo 1228432 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B9341891 : Blo 1228432 9341891 := bstep (se 1 (by rfl) ⟨7006418, by rfl⟩ : syracuseStep 9341891 = 14012837) B14012837
theorem B10497053 : Blo 1228432 10497053 := bstep (se 3 (by rfl) ⟨1968197, by rfl⟩ : syracuseStep 10497053 = 3936395) B3936395
theorem B2764079 : Blo 1228432 2764079 := bstep (se 1 (by rfl) ⟨2073059, by rfl⟩ : syracuseStep 2764079 = 4146119) B4146119
theorem B7876379 : Blo 1228432 7876379 := bstep (se 1 (by rfl) ⟨5907284, by rfl⟩ : syracuseStep 7876379 = 11814569) B11814569
theorem B9334601 : Blo 1228432 9334601 := bstep (se 2 (by rfl) ⟨3500475, by rfl⟩ : syracuseStep 9334601 = 7000951) B7000951
theorem B13291561 : Blo 1228432 13291561 := bstep (se 2 (by rfl) ⟨4984335, by rfl⟩ : syracuseStep 13291561 = 9968671) B9968671
theorem B2764907 : Blo 1228432 2764907 := bstep (se 1 (by rfl) ⟨2073680, by rfl⟩ : syracuseStep 2764907 = 4147361) B4147361
theorem B6221933 : Blo 1228432 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B6303869 : Blo 1228432 6303869 := bstep (se 3 (by rfl) ⟨1181975, by rfl⟩ : syracuseStep 6303869 = 2363951) B2363951
theorem B3936703 : Blo 1228432 3936703 := bstep (se 1 (by rfl) ⟨2952527, by rfl⟩ : syracuseStep 3936703 = 5905055) B5905055
theorem B4985279 : Blo 1228432 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B20206343 : Blo 1228432 20206343 := bstep (se 1 (by rfl) ⟨15154757, by rfl⟩ : syracuseStep 20206343 = 30309515) B30309515
theorem B29897657 : Blo 1228432 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B3109823 : Blo 1228432 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B2364383 : Blo 1228432 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B9966827 : Blo 1228432 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B10507715 : Blo 1228432 10507715 := bstep (se 1 (by rfl) ⟨7880786, by rfl⟩ : syracuseStep 10507715 = 15761573) B15761573
theorem B2766383 : Blo 1228432 2766383 := bstep (se 1 (by rfl) ⟨2074787, by rfl⟩ : syracuseStep 2766383 = 4149575) B4149575
theorem B179361337 : Blo 1228432 179361337 := bstep (se 2 (by rfl) ⟨67260501, by rfl⟩ : syracuseStep 179361337 = 134521003) B134521003
theorem B2332223 : Blo 1228432 2332223 := bstep (se 1 (by rfl) ⟨1749167, by rfl⟩ : syracuseStep 2332223 = 3498335) B3498335
theorem B2627579 : Blo 1228432 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B11819027 : Blo 1228432 11819027 := bstep (se 1 (by rfl) ⟨8864270, by rfl⟩ : syracuseStep 11819027 = 17728541) B17728541
theorem B2766887 : Blo 1228432 2766887 := bstep (se 1 (by rfl) ⟨2075165, by rfl⟩ : syracuseStep 2766887 = 4150331) B4150331
theorem B6224039 : Blo 1228432 6224039 := bstep (se 1 (by rfl) ⟨4668029, by rfl⟩ : syracuseStep 6224039 = 9336059) B9336059
theorem B9337031 : Blo 1228432 9337031 := bstep (se 1 (by rfl) ⟨7002773, by rfl⟩ : syracuseStep 9337031 = 14005547) B14005547
theorem B2767337 : Blo 1228432 2767337 := bstep (se 2 (by rfl) ⟨1037751, by rfl⟩ : syracuseStep 2767337 = 2075503) B2075503
theorem B16816663 : Blo 1228432 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B4987439 : Blo 1228432 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B9329255 : Blo 1228432 9329255 := bstep (se 1 (by rfl) ⟨6996941, by rfl⟩ : syracuseStep 9329255 = 13993883) B13993883
theorem B22723255 : Blo 1228432 22723255 := bstep (se 1 (by rfl) ⟨17042441, by rfl⟩ : syracuseStep 22723255 = 34084883) B34084883
theorem B14007005 : Blo 1228432 14007005 := bstep (se 3 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 14007005 = 5252627) B5252627
theorem B1383151 : Blo 1228432 1383151 := bstep (se 1 (by rfl) ⟨1037363, by rfl⟩ : syracuseStep 1383151 = 2074727) B2074727
theorem B2767679 : Blo 1228432 2767679 := bstep (se 1 (by rfl) ⟨2075759, by rfl⟩ : syracuseStep 2767679 = 4151519) B4151519
theorem B3111929 : Blo 1228432 3111929 := bstep (se 2 (by rfl) ⟨1166973, by rfl⟩ : syracuseStep 3111929 = 2333947) B2333947
theorem B9329741 : Blo 1228432 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B4152545 : Blo 1228432 4152545 := bstep (se 2 (by rfl) ⟨1557204, by rfl⟩ : syracuseStep 4152545 = 3114409) B3114409
theorem B2768111 : Blo 1228432 2768111 := bstep (se 1 (by rfl) ⟨2076083, by rfl⟩ : syracuseStep 2768111 = 4152167) B4152167
theorem B9969065 : Blo 1228432 9969065 := bstep (se 2 (by rfl) ⟨3738399, by rfl⟩ : syracuseStep 9969065 = 7476799) B7476799
theorem B3112415 : Blo 1228432 3112415 := bstep (se 1 (by rfl) ⟨2334311, by rfl⟩ : syracuseStep 3112415 = 4668623) B4668623
theorem B7004141 : Blo 1228432 7004141 := bstep (se 3 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 7004141 = 2626553) B2626553
theorem B6225983 : Blo 1228432 6225983 := bstep (se 1 (by rfl) ⟨4669487, by rfl⟩ : syracuseStep 6225983 = 9338975) B9338975
theorem B1843271 : Blo 1228432 1843271 := bstep (se 1 (by rfl) ⟨1382453, by rfl⟩ : syracuseStep 1843271 = 2764907) B2764907
theorem B4202579 : Blo 1228432 4202579 := bstep (se 1 (by rfl) ⟨3151934, by rfl⟩ : syracuseStep 4202579 = 6303869) B6303869
theorem B19931771 : Blo 1228432 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B2073215 : Blo 1228432 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B6644551 : Blo 1228432 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B1229659 : Blo 1228432 1229659 := bstep (se 1 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 1229659 = 1844489) B1844489
theorem B259130285 : Blo 1228432 259130285 := bstep (se 3 (by rfl) ⟨48586928, by rfl⟩ : syracuseStep 259130285 = 97173857) B97173857
theorem B7005143 : Blo 1228432 7005143 := bstep (se 1 (by rfl) ⟨5253857, by rfl⟩ : syracuseStep 7005143 = 10507715) B10507715
theorem B1844201 : Blo 1228432 1844201 := bstep (se 2 (by rfl) ⟨691575, by rfl⟩ : syracuseStep 1844201 = 1383151) B1383151
theorem B1844255 : Blo 1228432 1844255 := bstep (se 1 (by rfl) ⟨1383191, by rfl⟩ : syracuseStep 1844255 = 2766383) B2766383
theorem B4670567 : Blo 1228432 4670567 := bstep (se 1 (by rfl) ⟨3502925, by rfl⟩ : syracuseStep 4670567 = 7005851) B7005851
theorem B3736687 : Blo 1228432 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B1229979 : Blo 1228432 1229979 := bstep (se 1 (by rfl) ⟨922484, by rfl⟩ : syracuseStep 1229979 = 1844969) B1844969
theorem B1844591 : Blo 1228432 1844591 := bstep (se 1 (by rfl) ⟨1383443, by rfl⟩ : syracuseStep 1844591 = 2766887) B2766887
theorem B1230303 : Blo 1228432 1230303 := bstep (se 1 (by rfl) ⟨922727, by rfl⟩ : syracuseStep 1230303 = 1845455) B1845455
theorem B1230335 : Blo 1228432 1230335 := bstep (se 1 (by rfl) ⟨922751, by rfl⟩ : syracuseStep 1230335 = 1845503) B1845503
theorem B4671067 : Blo 1228432 4671067 := bstep (se 1 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 4671067 = 7006601) B7006601
theorem B1844891 : Blo 1228432 1844891 := bstep (se 1 (by rfl) ⟨1383668, by rfl⟩ : syracuseStep 1844891 = 2767337) B2767337
theorem B6219503 : Blo 1228432 6219503 := bstep (se 1 (by rfl) ⟨4664627, by rfl⟩ : syracuseStep 6219503 = 9329255) B9329255
theorem B1845119 : Blo 1228432 1845119 := bstep (se 1 (by rfl) ⟨1383839, by rfl⟩ : syracuseStep 1845119 = 2767679) B2767679
theorem B4671371 : Blo 1228432 4671371 := bstep (se 1 (by rfl) ⟨3503528, by rfl⟩ : syracuseStep 4671371 = 7007057) B7007057
theorem B6227927 : Blo 1228432 6227927 := bstep (se 1 (by rfl) ⟨4670945, by rfl⟩ : syracuseStep 6227927 = 9341891) B9341891
theorem B2074619 : Blo 1228432 2074619 := bstep (se 1 (by rfl) ⟨1555964, by rfl⟩ : syracuseStep 2074619 = 3111929) B3111929
theorem B6998035 : Blo 1228432 6998035 := bstep (se 1 (by rfl) ⟨5248526, by rfl⟩ : syracuseStep 6998035 = 10497053) B10497053
theorem B6219827 : Blo 1228432 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B1845407 : Blo 1228432 1845407 := bstep (se 1 (by rfl) ⟨1384055, by rfl⟩ : syracuseStep 1845407 = 2768111) B2768111
theorem B6646043 : Blo 1228432 6646043 := bstep (se 1 (by rfl) ⟨4984532, by rfl⟩ : syracuseStep 6646043 = 9969065) B9969065
theorem B2074943 : Blo 1228432 2074943 := bstep (se 1 (by rfl) ⟨1556207, by rfl⟩ : syracuseStep 2074943 = 3112415) B3112415
theorem B17722081 : Blo 1228432 17722081 := bstep (se 2 (by rfl) ⟨6645780, by rfl⟩ : syracuseStep 17722081 = 13291561) B13291561
theorem B4147955 : Blo 1228432 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B89688869 : Blo 1228432 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B13470895 : Blo 1228432 13470895 := bstep (se 1 (by rfl) ⟨10103171, by rfl⟩ : syracuseStep 13470895 = 20206343) B20206343
theorem B1576255 : Blo 1228432 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B30297673 : Blo 1228432 30297673 := bstep (se 2 (by rfl) ⟨11361627, by rfl⟩ : syracuseStep 30297673 = 22723255) B22723255
theorem B18919007 : Blo 1228432 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B4149359 : Blo 1228432 4149359 := bstep (se 1 (by rfl) ⟨3112019, by rfl⟩ : syracuseStep 4149359 = 6224039) B6224039
theorem B6223067 : Blo 1228432 6223067 := bstep (se 1 (by rfl) ⟨4667300, by rfl⟩ : syracuseStep 6223067 = 9334601) B9334601
theorem B4150763 : Blo 1228432 4150763 := bstep (se 1 (by rfl) ⟨3113072, by rfl⟩ : syracuseStep 4150763 = 6226145) B6226145
theorem B3323519 : Blo 1228432 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B26957657 : Blo 1228432 26957657 := bstep (se 2 (by rfl) ⟨10109121, by rfl⟩ : syracuseStep 26957657 = 20218243) B20218243
theorem B5248937 : Blo 1228432 5248937 := bstep (se 2 (by rfl) ⟨1968351, by rfl⟩ : syracuseStep 5248937 = 3936703) B3936703
theorem B1751161 : Blo 1228432 1751161 := bstep (se 2 (by rfl) ⟨656685, by rfl⟩ : syracuseStep 1751161 = 1313371) B1313371
theorem B1661095 : Blo 1228432 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B1382575 : Blo 1228432 1382575 := bstep (se 1 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 1382575 = 2073863) B2073863
theorem B2332975 : Blo 1228432 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B1554815 : Blo 1228432 1554815 := bstep (se 1 (by rfl) ⟨1166111, by rfl⟩ : syracuseStep 1554815 = 2332223) B2332223
theorem B1751719 : Blo 1228432 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B7879351 : Blo 1228432 7879351 := bstep (se 1 (by rfl) ⟨5909513, by rfl⟩ : syracuseStep 7879351 = 11819027) B11819027
theorem B6224687 : Blo 1228432 6224687 := bstep (se 1 (by rfl) ⟨4668515, by rfl⟩ : syracuseStep 6224687 = 9337031) B9337031
theorem B3324959 : Blo 1228432 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B9338003 : Blo 1228432 9338003 := bstep (se 1 (by rfl) ⟨7003502, by rfl⟩ : syracuseStep 9338003 = 14007005) B14007005
theorem B7003367 : Blo 1228432 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B239148449 : Blo 1228432 239148449 := bstep (se 2 (by rfl) ⟨89680668, by rfl⟩ : syracuseStep 239148449 = 179361337) B179361337
theorem B2768363 : Blo 1228432 2768363 := bstep (se 1 (by rfl) ⟨2076272, by rfl⟩ : syracuseStep 2768363 = 4152545) B4152545
theorem B1842719 : Blo 1228432 1842719 := bstep (se 1 (by rfl) ⟨1382039, by rfl⟩ : syracuseStep 1842719 = 2764079) B2764079
theorem B5250919 : Blo 1228432 5250919 := bstep (se 1 (by rfl) ⟨3938189, by rfl⟩ : syracuseStep 5250919 = 7876379) B7876379
theorem B4669427 : Blo 1228432 4669427 := bstep (se 1 (by rfl) ⟨3502070, by rfl⟩ : syracuseStep 4669427 = 7004141) B7004141
theorem B9330713 : Blo 1228432 9330713 := bstep (se 2 (by rfl) ⟨3499017, by rfl⟩ : syracuseStep 9330713 = 6998035) B6998035
theorem B1228847 : Blo 1228432 1228847 := bstep (se 1 (by rfl) ⟨921635, by rfl⟩ : syracuseStep 1228847 = 1843271) B1843271
theorem B2801719 : Blo 1228432 2801719 := bstep (se 1 (by rfl) ⟨2101289, by rfl⟩ : syracuseStep 2801719 = 4202579) B4202579
theorem B2334881 : Blo 1228432 2334881 := bstep (se 2 (by rfl) ⟨875580, by rfl⟩ : syracuseStep 2334881 = 1751161) B1751161
theorem B1843433 : Blo 1228432 1843433 := bstep (se 2 (by rfl) ⟨691287, by rfl⟩ : syracuseStep 1843433 = 1382575) B1382575
theorem B13287847 : Blo 1228432 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B172753523 : Blo 1228432 172753523 := bstep (se 1 (by rfl) ⟨129565142, by rfl⟩ : syracuseStep 172753523 = 259130285) B259130285
theorem B4670095 : Blo 1228432 4670095 := bstep (se 1 (by rfl) ⟨3502571, by rfl⟩ : syracuseStep 4670095 = 7005143) B7005143
theorem B1229467 : Blo 1228432 1229467 := bstep (se 1 (by rfl) ⟨922100, by rfl⟩ : syracuseStep 1229467 = 1844201) B1844201
theorem B1229503 : Blo 1228432 1229503 := bstep (se 1 (by rfl) ⟨922127, by rfl⟩ : syracuseStep 1229503 = 1844255) B1844255
theorem B3113711 : Blo 1228432 3113711 := bstep (se 1 (by rfl) ⟨2335283, by rfl⟩ : syracuseStep 3113711 = 4670567) B4670567
theorem B2335625 : Blo 1228432 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B1229727 : Blo 1228432 1229727 := bstep (se 1 (by rfl) ⟨922295, by rfl⟩ : syracuseStep 1229727 = 1844591) B1844591
theorem B4146173 : Blo 1228432 4146173 := bstep (se 3 (by rfl) ⟨777407, by rfl⟩ : syracuseStep 4146173 = 1554815) B1554815
theorem B1229927 : Blo 1228432 1229927 := bstep (se 1 (by rfl) ⟨922445, by rfl⟩ : syracuseStep 1229927 = 1844891) B1844891
theorem B4146335 : Blo 1228432 4146335 := bstep (se 1 (by rfl) ⟨3109751, by rfl⟩ : syracuseStep 4146335 = 6219503) B6219503
theorem B1230079 : Blo 1228432 1230079 := bstep (se 1 (by rfl) ⟨922559, by rfl⟩ : syracuseStep 1230079 = 1845119) B1845119
theorem B3114247 : Blo 1228432 3114247 := bstep (se 1 (by rfl) ⟨2335685, by rfl⟩ : syracuseStep 3114247 = 4671371) B4671371
theorem B3499291 : Blo 1228432 3499291 := bstep (se 1 (by rfl) ⟨2624468, by rfl⟩ : syracuseStep 3499291 = 5248937) B5248937
theorem B4146551 : Blo 1228432 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B1230271 : Blo 1228432 1230271 := bstep (se 1 (by rfl) ⟨922703, by rfl⟩ : syracuseStep 1230271 = 1845407) B1845407
theorem B4982249 : Blo 1228432 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B40396897 : Blo 1228432 40396897 := bstep (se 2 (by rfl) ⟨15148836, by rfl⟩ : syracuseStep 40396897 = 30297673) B30297673
theorem B6228089 : Blo 1228432 6228089 := bstep (se 2 (by rfl) ⟨2335533, by rfl⟩ : syracuseStep 6228089 = 4671067) B4671067
theorem B71887085 : Blo 1228432 71887085 := bstep (se 3 (by rfl) ⟨13478828, by rfl⟩ : syracuseStep 71887085 = 26957657) B26957657
theorem B1845575 : Blo 1228432 1845575 := bstep (se 1 (by rfl) ⟨1384181, by rfl⟩ : syracuseStep 1845575 = 2768363) B2768363
theorem B2214793 : Blo 1228432 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B4148711 : Blo 1228432 4148711 := bstep (se 1 (by rfl) ⟨3111533, by rfl⟩ : syracuseStep 4148711 = 6223067) B6223067
theorem B10505801 : Blo 1228432 10505801 := bstep (se 2 (by rfl) ⟨3939675, by rfl⟩ : syracuseStep 10505801 = 7879351) B7879351
theorem B23629441 : Blo 1228432 23629441 := bstep (se 2 (by rfl) ⟨8861040, by rfl⟩ : syracuseStep 23629441 = 17722081) B17722081
theorem B2215679 : Blo 1228432 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B8859401 : Blo 1228432 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B17961193 : Blo 1228432 17961193 := bstep (se 2 (by rfl) ⟨6735447, by rfl⟩ : syracuseStep 17961193 = 13470895) B13470895
theorem B2101673 : Blo 1228432 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B2765303 : Blo 1228432 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B4149791 : Blo 1228432 4149791 := bstep (se 1 (by rfl) ⟨3112343, by rfl⟩ : syracuseStep 4149791 = 6224687) B6224687
theorem B2216639 : Blo 1228432 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B12612671 : Blo 1228432 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B7001225 : Blo 1228432 7001225 := bstep (se 2 (by rfl) ⟨2625459, by rfl⟩ : syracuseStep 7001225 = 5250919) B5250919
theorem B4150655 : Blo 1228432 4150655 := bstep (se 1 (by rfl) ⟨3112991, by rfl⟩ : syracuseStep 4150655 = 6225983) B6225983
theorem B2766239 : Blo 1228432 2766239 := bstep (se 1 (by rfl) ⟨2074679, by rfl⟩ : syracuseStep 2766239 = 4149359) B4149359
theorem B3110633 : Blo 1228432 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B1382143 : Blo 1228432 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B2767175 : Blo 1228432 2767175 := bstep (se 1 (by rfl) ⟨2075381, by rfl⟩ : syracuseStep 2767175 = 4150763) B4150763
theorem B4151951 : Blo 1228432 4151951 := bstep (se 1 (by rfl) ⟨3113963, by rfl⟩ : syracuseStep 4151951 = 6227927) B6227927
theorem B1383079 : Blo 1228432 1383079 := bstep (se 1 (by rfl) ⟨1037309, by rfl⟩ : syracuseStep 1383079 = 2074619) B2074619
theorem B4430695 : Blo 1228432 4430695 := bstep (se 1 (by rfl) ⟨3323021, by rfl⟩ : syracuseStep 4430695 = 6646043) B6646043
theorem B1383295 : Blo 1228432 1383295 := bstep (se 1 (by rfl) ⟨1037471, by rfl⟩ : syracuseStep 1383295 = 2074943) B2074943
theorem B3112951 : Blo 1228432 3112951 := bstep (se 1 (by rfl) ⟨2334713, by rfl⟩ : syracuseStep 3112951 = 4669427) B4669427
theorem B59792579 : Blo 1228432 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B6225335 : Blo 1228432 6225335 := bstep (se 1 (by rfl) ⟨4669001, by rfl⟩ : syracuseStep 6225335 = 9338003) B9338003
theorem B4668911 : Blo 1228432 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B159432299 : Blo 1228432 159432299 := bstep (se 1 (by rfl) ⟨119574224, by rfl⟩ : syracuseStep 159432299 = 239148449) B239148449
theorem B1228479 : Blo 1228432 1228479 := bstep (se 1 (by rfl) ⟨921359, by rfl⟩ : syracuseStep 1228479 = 1842719) B1842719
theorem B1556587 : Blo 1228432 1556587 := bstep (se 1 (by rfl) ⟨1167440, by rfl⟩ : syracuseStep 1556587 = 2334881) B2334881
theorem B53862529 : Blo 1228432 53862529 := bstep (se 2 (by rfl) ⟨20198448, by rfl⟩ : syracuseStep 53862529 = 40396897) B40396897
theorem B1228955 : Blo 1228432 1228955 := bstep (se 1 (by rfl) ⟨921716, by rfl⟩ : syracuseStep 1228955 = 1843433) B1843433
theorem B14942501 : Blo 1228432 14942501 := bstep (se 4 (by rfl) ⟨1400859, by rfl⟩ : syracuseStep 14942501 = 2801719) B2801719
theorem B1843535 : Blo 1228432 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1557083 : Blo 1228432 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B6226793 : Blo 1228432 6226793 := bstep (se 2 (by rfl) ⟨2335047, by rfl⟩ : syracuseStep 6226793 = 4670095) B4670095
theorem B1844105 : Blo 1228432 1844105 := bstep (se 2 (by rfl) ⟨691539, by rfl⟩ : syracuseStep 1844105 = 1383079) B1383079
theorem B1844159 : Blo 1228432 1844159 := bstep (se 1 (by rfl) ⟨1383119, by rfl⟩ : syracuseStep 1844159 = 2766239) B2766239
theorem B5604461 : Blo 1228432 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B5907593 : Blo 1228432 5907593 := bstep (se 2 (by rfl) ⟨2215347, by rfl⟩ : syracuseStep 5907593 = 4430695) B4430695
theorem B2073755 : Blo 1228432 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B1844393 : Blo 1228432 1844393 := bstep (se 2 (by rfl) ⟨691647, by rfl⟩ : syracuseStep 1844393 = 1383295) B1383295
theorem B47924723 : Blo 1228432 47924723 := bstep (se 1 (by rfl) ⟨35943542, by rfl⟩ : syracuseStep 47924723 = 71887085) B71887085
theorem B1844783 : Blo 1228432 1844783 := bstep (se 1 (by rfl) ⟨1383587, by rfl⟩ : syracuseStep 1844783 = 2767175) B2767175
theorem B1230383 : Blo 1228432 1230383 := bstep (se 1 (by rfl) ⟨922787, by rfl⟩ : syracuseStep 1230383 = 1845575) B1845575
theorem B5908477 : Blo 1228432 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B6220475 : Blo 1228432 6220475 := bstep (se 1 (by rfl) ⟨4665356, by rfl⟩ : syracuseStep 6220475 = 9330713) B9330713
theorem B1477759 : Blo 1228432 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B2075807 : Blo 1228432 2075807 := bstep (se 1 (by rfl) ⟨1556855, by rfl⟩ : syracuseStep 2075807 = 3113711) B3113711
theorem B2764115 : Blo 1228432 2764115 := bstep (se 1 (by rfl) ⟨2073086, by rfl⟩ : syracuseStep 2764115 = 4146173) B4146173
theorem B8408447 : Blo 1228432 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B2764223 : Blo 1228432 2764223 := bstep (se 1 (by rfl) ⟨2073167, by rfl⟩ : syracuseStep 2764223 = 4146335) B4146335
theorem B2764367 : Blo 1228432 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B3321499 : Blo 1228432 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B95793029 : Blo 1228432 95793029 := bstep (se 4 (by rfl) ⟨8980596, by rfl⟩ : syracuseStep 95793029 = 17961193) B17961193
theorem B4665721 : Blo 1228432 4665721 := bstep (se 2 (by rfl) ⟨1749645, by rfl⟩ : syracuseStep 4665721 = 3499291) B3499291
theorem B4150223 : Blo 1228432 4150223 := bstep (se 1 (by rfl) ⟨3112667, by rfl⟩ : syracuseStep 4150223 = 6225335) B6225335
theorem B2765807 : Blo 1228432 2765807 := bstep (se 1 (by rfl) ⟨2074355, by rfl⟩ : syracuseStep 2765807 = 4148711) B4148711
theorem B106288199 : Blo 1228432 106288199 := bstep (se 1 (by rfl) ⟨79716149, by rfl⟩ : syracuseStep 106288199 = 159432299) B159432299
theorem B4150601 : Blo 1228432 4150601 := bstep (se 2 (by rfl) ⟨1556475, by rfl⟩ : syracuseStep 4150601 = 3112951) B3112951
theorem B2766527 : Blo 1228432 2766527 := bstep (se 1 (by rfl) ⟨2074895, by rfl⟩ : syracuseStep 2766527 = 4149791) B4149791
theorem B115169015 : Blo 1228432 115169015 := bstep (se 1 (by rfl) ⟨86376761, by rfl⟩ : syracuseStep 115169015 = 172753523) B172753523
theorem B17717129 : Blo 1228432 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B4667483 : Blo 1228432 4667483 := bstep (se 1 (by rfl) ⟨3500612, by rfl⟩ : syracuseStep 4667483 = 7001225) B7001225
theorem B2767103 : Blo 1228432 2767103 := bstep (se 1 (by rfl) ⟨2075327, by rfl⟩ : syracuseStep 2767103 = 4150655) B4150655
theorem B4152059 : Blo 1228432 4152059 := bstep (se 1 (by rfl) ⟨3114044, by rfl⟩ : syracuseStep 4152059 = 6228089) B6228089
theorem B4152329 : Blo 1228432 4152329 := bstep (se 2 (by rfl) ⟨1557123, by rfl⟩ : syracuseStep 4152329 = 3114247) B3114247
theorem B2767967 : Blo 1228432 2767967 := bstep (se 1 (by rfl) ⟨2075975, by rfl⟩ : syracuseStep 2767967 = 4151951) B4151951
theorem B11812229 : Blo 1228432 11812229 := bstep (se 4 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 11812229 = 2214793) B2214793
theorem B39861719 : Blo 1228432 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B31505921 : Blo 1228432 31505921 := bstep (se 2 (by rfl) ⟨11814720, by rfl⟩ : syracuseStep 31505921 = 23629441) B23629441
theorem B3112607 : Blo 1228432 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B1842857 : Blo 1228432 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B7003867 : Blo 1228432 7003867 := bstep (se 1 (by rfl) ⟨5252900, by rfl⟩ : syracuseStep 7003867 = 10505801) B10505801
theorem B5906267 : Blo 1228432 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B9961667 : Blo 1228432 9961667 := bstep (se 1 (by rfl) ⟨7471250, by rfl⟩ : syracuseStep 9961667 = 14942501) B14942501
theorem B1229023 : Blo 1228432 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1229403 : Blo 1228432 1229403 := bstep (se 1 (by rfl) ⟨922052, by rfl⟩ : syracuseStep 1229403 = 1844105) B1844105
theorem B1229439 : Blo 1228432 1229439 := bstep (se 1 (by rfl) ⟨922079, by rfl⟩ : syracuseStep 1229439 = 1844159) B1844159
theorem B1843871 : Blo 1228432 1843871 := bstep (se 1 (by rfl) ⟨1382903, by rfl⟩ : syracuseStep 1843871 = 2765807) B2765807
theorem B3736307 : Blo 1228432 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B1229595 : Blo 1228432 1229595 := bstep (se 1 (by rfl) ⟨922196, by rfl⟩ : syracuseStep 1229595 = 1844393) B1844393
theorem B31949815 : Blo 1228432 31949815 := bstep (se 1 (by rfl) ⟨23962361, by rfl⟩ : syracuseStep 31949815 = 47924723) B47924723
theorem B1229855 : Blo 1228432 1229855 := bstep (se 1 (by rfl) ⟨922391, by rfl⟩ : syracuseStep 1229855 = 1844783) B1844783
theorem B1844351 : Blo 1228432 1844351 := bstep (se 1 (by rfl) ⟨1383263, by rfl⟩ : syracuseStep 1844351 = 2766527) B2766527
theorem B1844735 : Blo 1228432 1844735 := bstep (se 1 (by rfl) ⟨1383551, by rfl⟩ : syracuseStep 1844735 = 2767103) B2767103
theorem B4146983 : Blo 1228432 4146983 := bstep (se 1 (by rfl) ⟨3110237, by rfl⟩ : syracuseStep 4146983 = 6220475) B6220475
theorem B1845311 : Blo 1228432 1845311 := bstep (se 1 (by rfl) ⟨1383983, by rfl⟩ : syracuseStep 1845311 = 2767967) B2767967
theorem B5605631 : Blo 1228432 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B7874819 : Blo 1228432 7874819 := bstep (se 1 (by rfl) ⟨5906114, by rfl⟩ : syracuseStep 7874819 = 11812229) B11812229
theorem B2075071 : Blo 1228432 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B2075449 : Blo 1228432 2075449 := bstep (se 2 (by rfl) ⟨778293, by rfl⟩ : syracuseStep 2075449 = 1556587) B1556587
theorem B6220961 : Blo 1228432 6220961 := bstep (se 2 (by rfl) ⟨2332860, by rfl⟩ : syracuseStep 6220961 = 4665721) B4665721
theorem B76779343 : Blo 1228432 76779343 := bstep (se 1 (by rfl) ⟨57584507, by rfl⟩ : syracuseStep 76779343 = 115169015) B115169015
theorem B1970345 : Blo 1228432 1970345 := bstep (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) B1477759
theorem B4428665 : Blo 1228432 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B3937511 : Blo 1228432 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B63862019 : Blo 1228432 63862019 := bstep (se 1 (by rfl) ⟨47896514, by rfl⟩ : syracuseStep 63862019 = 95793029) B95793029
theorem B7877969 : Blo 1228432 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B71816705 : Blo 1228432 71816705 := bstep (se 2 (by rfl) ⟨26931264, by rfl⟩ : syracuseStep 71816705 = 53862529) B53862529
theorem B4151195 : Blo 1228432 4151195 := bstep (se 1 (by rfl) ⟨3113396, by rfl⟩ : syracuseStep 4151195 = 6226793) B6226793
theorem B2766815 : Blo 1228432 2766815 := bstep (se 1 (by rfl) ⟨2075111, by rfl⟩ : syracuseStep 2766815 = 4150223) B4150223
theorem B70858799 : Blo 1228432 70858799 := bstep (se 1 (by rfl) ⟨53144099, by rfl⟩ : syracuseStep 70858799 = 106288199) B106288199
theorem B3938395 : Blo 1228432 3938395 := bstep (se 1 (by rfl) ⟨2953796, by rfl⟩ : syracuseStep 3938395 = 5907593) B5907593
theorem B1382503 : Blo 1228432 1382503 := bstep (se 1 (by rfl) ⟨1036877, by rfl⟩ : syracuseStep 1382503 = 2073755) B2073755
theorem B2767067 : Blo 1228432 2767067 := bstep (se 1 (by rfl) ⟨2075300, by rfl⟩ : syracuseStep 2767067 = 4150601) B4150601
theorem B11811419 : Blo 1228432 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B3111655 : Blo 1228432 3111655 := bstep (se 1 (by rfl) ⟨2333741, by rfl⟩ : syracuseStep 3111655 = 4667483) B4667483
theorem B4152221 : Blo 1228432 4152221 := bstep (se 3 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 4152221 = 1557083) B1557083
theorem B2768039 : Blo 1228432 2768039 := bstep (se 1 (by rfl) ⟨2076029, by rfl⟩ : syracuseStep 2768039 = 4152059) B4152059
theorem B2768219 : Blo 1228432 2768219 := bstep (se 1 (by rfl) ⟨2076164, by rfl⟩ : syracuseStep 2768219 = 4152329) B4152329
theorem B1383871 : Blo 1228432 1383871 := bstep (se 1 (by rfl) ⟨1037903, by rfl⟩ : syracuseStep 1383871 = 2075807) B2075807
theorem B1842743 : Blo 1228432 1842743 := bstep (se 1 (by rfl) ⟨1382057, by rfl⟩ : syracuseStep 1842743 = 2764115) B2764115
theorem B9338489 : Blo 1228432 9338489 := bstep (se 2 (by rfl) ⟨3501933, by rfl⟩ : syracuseStep 9338489 = 7003867) B7003867
theorem B1842815 : Blo 1228432 1842815 := bstep (se 1 (by rfl) ⟨1382111, by rfl⟩ : syracuseStep 1842815 = 2764223) B2764223
theorem B26574479 : Blo 1228432 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B21003947 : Blo 1228432 21003947 := bstep (se 1 (by rfl) ⟨15752960, by rfl⟩ : syracuseStep 21003947 = 31505921) B31505921
theorem B1842911 : Blo 1228432 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B1228571 : Blo 1228432 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B5251193 : Blo 1228432 5251193 := bstep (se 2 (by rfl) ⟨1969197, by rfl⟩ : syracuseStep 5251193 = 3938395) B3938395
theorem B1843337 : Blo 1228432 1843337 := bstep (se 2 (by rfl) ⟨691251, by rfl⟩ : syracuseStep 1843337 = 1382503) B1382503
theorem B1229247 : Blo 1228432 1229247 := bstep (se 1 (by rfl) ⟨921935, by rfl⟩ : syracuseStep 1229247 = 1843871) B1843871
theorem B1229567 : Blo 1228432 1229567 := bstep (se 1 (by rfl) ⟨922175, by rfl⟩ : syracuseStep 1229567 = 1844351) B1844351
theorem B42574679 : Blo 1228432 42574679 := bstep (se 1 (by rfl) ⟨31931009, by rfl⟩ : syracuseStep 42574679 = 63862019) B63862019
theorem B5251979 : Blo 1228432 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B1229823 : Blo 1228432 1229823 := bstep (se 1 (by rfl) ⟨922367, by rfl⟩ : syracuseStep 1229823 = 1844735) B1844735
theorem B1844543 : Blo 1228432 1844543 := bstep (se 1 (by rfl) ⟨1383407, by rfl⟩ : syracuseStep 1844543 = 2766815) B2766815
theorem B42599753 : Blo 1228432 42599753 := bstep (se 2 (by rfl) ⟨15974907, by rfl⟩ : syracuseStep 42599753 = 31949815) B31949815
theorem B1230207 : Blo 1228432 1230207 := bstep (se 1 (by rfl) ⟨922655, by rfl⟩ : syracuseStep 1230207 = 1845311) B1845311
theorem B1844711 : Blo 1228432 1844711 := bstep (se 1 (by rfl) ⟨1383533, by rfl⟩ : syracuseStep 1844711 = 2767067) B2767067
theorem B3737087 : Blo 1228432 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B7874279 : Blo 1228432 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B1845161 : Blo 1228432 1845161 := bstep (se 2 (by rfl) ⟨691935, by rfl⟩ : syracuseStep 1845161 = 1383871) B1383871
theorem B9963485 : Blo 1228432 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B4147307 : Blo 1228432 4147307 := bstep (se 1 (by rfl) ⟨3110480, by rfl⟩ : syracuseStep 4147307 = 6220961) B6220961
theorem B1845359 : Blo 1228432 1845359 := bstep (se 1 (by rfl) ⟨1384019, by rfl⟩ : syracuseStep 1845359 = 2768039) B2768039
theorem B1845479 : Blo 1228432 1845479 := bstep (se 1 (by rfl) ⟨1384109, by rfl⟩ : syracuseStep 1845479 = 2768219) B2768219
theorem B14002631 : Blo 1228432 14002631 := bstep (se 1 (by rfl) ⟨10501973, by rfl⟩ : syracuseStep 14002631 = 21003947) B21003947
theorem B5254253 : Blo 1228432 5254253 := bstep (se 3 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 5254253 = 1970345) B1970345
theorem B2952443 : Blo 1228432 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B4148873 : Blo 1228432 4148873 := bstep (se 2 (by rfl) ⟨1555827, by rfl⟩ : syracuseStep 4148873 = 3111655) B3111655
theorem B47877803 : Blo 1228432 47877803 := bstep (se 1 (by rfl) ⟨35908352, by rfl⟩ : syracuseStep 47877803 = 71816705) B71816705
theorem B2764655 : Blo 1228432 2764655 := bstep (se 1 (by rfl) ⟨2073491, by rfl⟩ : syracuseStep 2764655 = 4146983) B4146983
theorem B47239199 : Blo 1228432 47239199 := bstep (se 1 (by rfl) ⟨35429399, by rfl⟩ : syracuseStep 47239199 = 70858799) B70858799
theorem B17716319 : Blo 1228432 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B102372457 : Blo 1228432 102372457 := bstep (se 2 (by rfl) ⟨38389671, by rfl⟩ : syracuseStep 102372457 = 76779343) B76779343
theorem B6641111 : Blo 1228432 6641111 := bstep (se 1 (by rfl) ⟨4980833, by rfl⟩ : syracuseStep 6641111 = 9961667) B9961667
theorem B2766761 : Blo 1228432 2766761 := bstep (se 2 (by rfl) ⟨1037535, by rfl⟩ : syracuseStep 2766761 = 2075071) B2075071
theorem B10500029 : Blo 1228432 10500029 := bstep (se 3 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 10500029 = 3937511) B3937511
theorem B2767265 : Blo 1228432 2767265 := bstep (se 2 (by rfl) ⟨1037724, by rfl⟩ : syracuseStep 2767265 = 2075449) B2075449
theorem B2767463 : Blo 1228432 2767463 := bstep (se 1 (by rfl) ⟨2075597, by rfl⟩ : syracuseStep 2767463 = 4151195) B4151195
theorem B5249879 : Blo 1228432 5249879 := bstep (se 1 (by rfl) ⟨3937409, by rfl⟩ : syracuseStep 5249879 = 7874819) B7874819
theorem B2768147 : Blo 1228432 2768147 := bstep (se 1 (by rfl) ⟨2076110, by rfl⟩ : syracuseStep 2768147 = 4152221) B4152221
theorem B1228495 : Blo 1228432 1228495 := bstep (se 1 (by rfl) ⟨921371, by rfl⟩ : syracuseStep 1228495 = 1842743) B1842743
theorem B6225659 : Blo 1228432 6225659 := bstep (se 1 (by rfl) ⟨4669244, by rfl⟩ : syracuseStep 6225659 = 9338489) B9338489
theorem B1228543 : Blo 1228432 1228543 := bstep (se 1 (by rfl) ⟨921407, by rfl⟩ : syracuseStep 1228543 = 1842815) B1842815
theorem B1228607 : Blo 1228432 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B1228891 : Blo 1228432 1228891 := bstep (se 1 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 1228891 = 1843337) B1843337
theorem B1229695 : Blo 1228432 1229695 := bstep (se 1 (by rfl) ⟨922271, by rfl⟩ : syracuseStep 1229695 = 1844543) B1844543
theorem B1229807 : Blo 1228432 1229807 := bstep (se 1 (by rfl) ⟨922355, by rfl⟩ : syracuseStep 1229807 = 1844711) B1844711
theorem B2491391 : Blo 1228432 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B1844507 : Blo 1228432 1844507 := bstep (se 1 (by rfl) ⟨1383380, by rfl⟩ : syracuseStep 1844507 = 2766761) B2766761
theorem B1230107 : Blo 1228432 1230107 := bstep (se 1 (by rfl) ⟨922580, by rfl⟩ : syracuseStep 1230107 = 1845161) B1845161
theorem B1230239 : Blo 1228432 1230239 := bstep (se 1 (by rfl) ⟨922679, by rfl⟩ : syracuseStep 1230239 = 1845359) B1845359
theorem B136496609 : Blo 1228432 136496609 := bstep (se 2 (by rfl) ⟨51186228, by rfl⟩ : syracuseStep 136496609 = 102372457) B102372457
theorem B1230319 : Blo 1228432 1230319 := bstep (se 1 (by rfl) ⟨922739, by rfl⟩ : syracuseStep 1230319 = 1845479) B1845479
theorem B1844843 : Blo 1228432 1844843 := bstep (se 1 (by rfl) ⟨1383632, by rfl⟩ : syracuseStep 1844843 = 2767265) B2767265
theorem B1844975 : Blo 1228432 1844975 := bstep (se 1 (by rfl) ⟨1383731, by rfl⟩ : syracuseStep 1844975 = 2767463) B2767463
theorem B3499919 : Blo 1228432 3499919 := bstep (se 1 (by rfl) ⟨2624939, by rfl⟩ : syracuseStep 3499919 = 5249879) B5249879
theorem B1968295 : Blo 1228432 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B1845431 : Blo 1228432 1845431 := bstep (se 1 (by rfl) ⟨1384073, by rfl⟩ : syracuseStep 1845431 = 2768147) B2768147
theorem B31918535 : Blo 1228432 31918535 := bstep (se 1 (by rfl) ⟨23938901, by rfl⟩ : syracuseStep 31918535 = 47877803) B47877803
theorem B31492799 : Blo 1228432 31492799 := bstep (se 1 (by rfl) ⟨23619599, by rfl⟩ : syracuseStep 31492799 = 47239199) B47239199
theorem B3500795 : Blo 1228432 3500795 := bstep (se 1 (by rfl) ⟨2625596, by rfl⟩ : syracuseStep 3500795 = 5251193) B5251193
theorem B3501319 : Blo 1228432 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B4427407 : Blo 1228432 4427407 := bstep (se 1 (by rfl) ⟨3320555, by rfl⟩ : syracuseStep 4427407 = 6641111) B6641111
theorem B7000019 : Blo 1228432 7000019 := bstep (se 1 (by rfl) ⟨5250014, by rfl⟩ : syracuseStep 7000019 = 10500029) B10500029
theorem B2764871 : Blo 1228432 2764871 := bstep (se 1 (by rfl) ⟨2073653, by rfl⟩ : syracuseStep 2764871 = 4147307) B4147307
theorem B9335087 : Blo 1228432 9335087 := bstep (se 1 (by rfl) ⟨7001315, by rfl⟩ : syracuseStep 9335087 = 14002631) B14002631
theorem B3502835 : Blo 1228432 3502835 := bstep (se 1 (by rfl) ⟨2627126, by rfl⟩ : syracuseStep 3502835 = 5254253) B5254253
theorem B2765915 : Blo 1228432 2765915 := bstep (se 1 (by rfl) ⟨2074436, by rfl⟩ : syracuseStep 2765915 = 4148873) B4148873
theorem B4150439 : Blo 1228432 4150439 := bstep (se 1 (by rfl) ⟨3112829, by rfl⟩ : syracuseStep 4150439 = 6225659) B6225659
theorem B28383119 : Blo 1228432 28383119 := bstep (se 1 (by rfl) ⟨21287339, by rfl⟩ : syracuseStep 28383119 = 42574679) B42574679
theorem B11810879 : Blo 1228432 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B28399835 : Blo 1228432 28399835 := bstep (se 1 (by rfl) ⟨21299876, by rfl⟩ : syracuseStep 28399835 = 42599753) B42599753
theorem B5249519 : Blo 1228432 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B6642323 : Blo 1228432 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B1843103 : Blo 1228432 1843103 := bstep (se 1 (by rfl) ⟨1382327, by rfl⟩ : syracuseStep 1843103 = 2764655) B2764655
theorem B1843247 : Blo 1228432 1843247 := bstep (se 1 (by rfl) ⟨1382435, by rfl⟩ : syracuseStep 1843247 = 2764871) B2764871
theorem B2335223 : Blo 1228432 2335223 := bstep (se 1 (by rfl) ⟨1751417, by rfl⟩ : syracuseStep 2335223 = 3502835) B3502835
theorem B1843943 : Blo 1228432 1843943 := bstep (se 1 (by rfl) ⟨1382957, by rfl⟩ : syracuseStep 1843943 = 2765915) B2765915
theorem B1229671 : Blo 1228432 1229671 := bstep (se 1 (by rfl) ⟨922253, by rfl⟩ : syracuseStep 1229671 = 1844507) B1844507
theorem B90997739 : Blo 1228432 90997739 := bstep (se 1 (by rfl) ⟨68248304, by rfl⟩ : syracuseStep 90997739 = 136496609) B136496609
theorem B1229895 : Blo 1228432 1229895 := bstep (se 1 (by rfl) ⟨922421, by rfl⟩ : syracuseStep 1229895 = 1844843) B1844843
theorem B1229983 : Blo 1228432 1229983 := bstep (se 1 (by rfl) ⟨922487, by rfl⟩ : syracuseStep 1229983 = 1844975) B1844975
theorem B7873919 : Blo 1228432 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B1230287 : Blo 1228432 1230287 := bstep (se 1 (by rfl) ⟨922715, by rfl⟩ : syracuseStep 1230287 = 1845431) B1845431
theorem B18933223 : Blo 1228432 18933223 := bstep (se 1 (by rfl) ⟨14199917, by rfl⟩ : syracuseStep 18933223 = 28399835) B28399835
theorem B3499679 : Blo 1228432 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B2624393 : Blo 1228432 2624393 := bstep (se 2 (by rfl) ⟨984147, by rfl⟩ : syracuseStep 2624393 = 1968295) B1968295
theorem B21279023 : Blo 1228432 21279023 := bstep (se 1 (by rfl) ⟨15959267, by rfl⟩ : syracuseStep 21279023 = 31918535) B31918535
theorem B4428215 : Blo 1228432 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B5903209 : Blo 1228432 5903209 := bstep (se 2 (by rfl) ⟨2213703, by rfl⟩ : syracuseStep 5903209 = 4427407) B4427407
theorem B4666679 : Blo 1228432 4666679 := bstep (se 1 (by rfl) ⟨3500009, by rfl⟩ : syracuseStep 4666679 = 7000019) B7000019
theorem B6223391 : Blo 1228432 6223391 := bstep (se 1 (by rfl) ⟨4667543, by rfl⟩ : syracuseStep 6223391 = 9335087) B9335087
theorem B1660927 : Blo 1228432 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B2766959 : Blo 1228432 2766959 := bstep (se 1 (by rfl) ⟨2075219, by rfl⟩ : syracuseStep 2766959 = 4150439) B4150439
theorem B2333279 : Blo 1228432 2333279 := bstep (se 1 (by rfl) ⟨1749959, by rfl⟩ : syracuseStep 2333279 = 3499919) B3499919
theorem B18922079 : Blo 1228432 18922079 := bstep (se 1 (by rfl) ⟨14191559, by rfl⟩ : syracuseStep 18922079 = 28383119) B28383119
theorem B4668425 : Blo 1228432 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B20995199 : Blo 1228432 20995199 := bstep (se 1 (by rfl) ⟨15746399, by rfl⟩ : syracuseStep 20995199 = 31492799) B31492799
theorem B2333863 : Blo 1228432 2333863 := bstep (se 1 (by rfl) ⟨1750397, by rfl⟩ : syracuseStep 2333863 = 3500795) B3500795
theorem B1228735 : Blo 1228432 1228735 := bstep (se 1 (by rfl) ⟨921551, by rfl⟩ : syracuseStep 1228735 = 1843103) B1843103
theorem B1228831 : Blo 1228432 1228831 := bstep (se 1 (by rfl) ⟨921623, by rfl⟩ : syracuseStep 1228831 = 1843247) B1843247
theorem B1556815 : Blo 1228432 1556815 := bstep (se 1 (by rfl) ⟨1167611, by rfl⟩ : syracuseStep 1556815 = 2335223) B2335223
theorem B1229295 : Blo 1228432 1229295 := bstep (se 1 (by rfl) ⟨921971, by rfl⟩ : syracuseStep 1229295 = 1843943) B1843943
theorem B1844639 : Blo 1228432 1844639 := bstep (se 1 (by rfl) ⟨1383479, by rfl⟩ : syracuseStep 1844639 = 2766959) B2766959
theorem B2214569 : Blo 1228432 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B2952143 : Blo 1228432 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B60665159 : Blo 1228432 60665159 := bstep (se 1 (by rfl) ⟨45498869, by rfl⟩ : syracuseStep 60665159 = 90997739) B90997739
theorem B4148927 : Blo 1228432 4148927 := bstep (se 1 (by rfl) ⟨3111695, by rfl⟩ : syracuseStep 4148927 = 6223391) B6223391
theorem B1749595 : Blo 1228432 1749595 := bstep (se 1 (by rfl) ⟨1312196, by rfl⟩ : syracuseStep 1749595 = 2624393) B2624393
theorem B25244297 : Blo 1228432 25244297 := bstep (se 2 (by rfl) ⟨9466611, by rfl⟩ : syracuseStep 25244297 = 18933223) B18933223
theorem B13996799 : Blo 1228432 13996799 := bstep (se 1 (by rfl) ⟨10497599, by rfl⟩ : syracuseStep 13996799 = 20995199) B20995199
theorem B14186015 : Blo 1228432 14186015 := bstep (se 1 (by rfl) ⟨10639511, by rfl⟩ : syracuseStep 14186015 = 21279023) B21279023
theorem B3111119 : Blo 1228432 3111119 := bstep (se 1 (by rfl) ⟨2333339, by rfl⟩ : syracuseStep 3111119 = 4666679) B4666679
theorem B5249279 : Blo 1228432 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B2333119 : Blo 1228432 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B7870945 : Blo 1228432 7870945 := bstep (se 2 (by rfl) ⟨2951604, by rfl⟩ : syracuseStep 7870945 = 5903209) B5903209
theorem B3111817 : Blo 1228432 3111817 := bstep (se 2 (by rfl) ⟨1166931, by rfl⟩ : syracuseStep 3111817 = 2333863) B2333863
theorem B1555519 : Blo 1228432 1555519 := bstep (se 1 (by rfl) ⟨1166639, by rfl⟩ : syracuseStep 1555519 = 2333279) B2333279
theorem B12614719 : Blo 1228432 12614719 := bstep (se 1 (by rfl) ⟨9461039, by rfl⟩ : syracuseStep 12614719 = 18922079) B18922079
theorem B3112283 : Blo 1228432 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B9331199 : Blo 1228432 9331199 := bstep (se 1 (by rfl) ⟨6998399, by rfl⟩ : syracuseStep 9331199 = 13996799) B13996799
theorem B10494593 : Blo 1228432 10494593 := bstep (se 2 (by rfl) ⟨3935472, by rfl⟩ : syracuseStep 10494593 = 7870945) B7870945
theorem B1229759 : Blo 1228432 1229759 := bstep (se 1 (by rfl) ⟨922319, by rfl⟩ : syracuseStep 1229759 = 1844639) B1844639
theorem B2074025 : Blo 1228432 2074025 := bstep (se 2 (by rfl) ⟨777759, by rfl⟩ : syracuseStep 2074025 = 1555519) B1555519
theorem B16819625 : Blo 1228432 16819625 := bstep (se 2 (by rfl) ⟨6307359, by rfl⟩ : syracuseStep 16819625 = 12614719) B12614719
theorem B2074079 : Blo 1228432 2074079 := bstep (se 1 (by rfl) ⟨1555559, by rfl⟩ : syracuseStep 2074079 = 3111119) B3111119
theorem B3499519 : Blo 1228432 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B1476379 : Blo 1228432 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B1968095 : Blo 1228432 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B2074855 : Blo 1228432 2074855 := bstep (se 1 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 2074855 = 3112283) B3112283
theorem B16829531 : Blo 1228432 16829531 := bstep (se 1 (by rfl) ⟨12622148, by rfl⟩ : syracuseStep 16829531 = 25244297) B25244297
theorem B2075753 : Blo 1228432 2075753 := bstep (se 2 (by rfl) ⟨778407, by rfl⟩ : syracuseStep 2075753 = 1556815) B1556815
theorem B9457343 : Blo 1228432 9457343 := bstep (se 1 (by rfl) ⟨7093007, by rfl⟩ : syracuseStep 9457343 = 14186015) B14186015
theorem B4149089 : Blo 1228432 4149089 := bstep (se 2 (by rfl) ⟨1555908, by rfl⟩ : syracuseStep 4149089 = 3111817) B3111817
theorem B2765951 : Blo 1228432 2765951 := bstep (se 1 (by rfl) ⟨2074463, by rfl⟩ : syracuseStep 2765951 = 4148927) B4148927
theorem B3110825 : Blo 1228432 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B2332793 : Blo 1228432 2332793 := bstep (se 2 (by rfl) ⟨874797, by rfl⟩ : syracuseStep 2332793 = 1749595) B1749595
theorem B161773757 : Blo 1228432 161773757 := bstep (se 3 (by rfl) ⟨30332579, by rfl⟩ : syracuseStep 161773757 = 60665159) B60665159
theorem B6996395 : Blo 1228432 6996395 := bstep (se 1 (by rfl) ⟨5247296, by rfl⟩ : syracuseStep 6996395 = 10494593) B10494593
theorem B1843967 : Blo 1228432 1843967 := bstep (se 1 (by rfl) ⟨1382975, by rfl⟩ : syracuseStep 1843967 = 2765951) B2765951
theorem B2073883 : Blo 1228432 2073883 := bstep (se 1 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 2073883 = 3110825) B3110825
theorem B107849171 : Blo 1228432 107849171 := bstep (se 1 (by rfl) ⟨80886878, by rfl⟩ : syracuseStep 107849171 = 161773757) B161773757
theorem B1968505 : Blo 1228432 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B6220799 : Blo 1228432 6220799 := bstep (se 1 (by rfl) ⟨4665599, by rfl⟩ : syracuseStep 6220799 = 9331199) B9331199
theorem B4666025 : Blo 1228432 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B11219687 : Blo 1228432 11219687 := bstep (se 1 (by rfl) ⟨8414765, by rfl⟩ : syracuseStep 11219687 = 16829531) B16829531
theorem B6304895 : Blo 1228432 6304895 := bstep (se 1 (by rfl) ⟨4728671, by rfl⟩ : syracuseStep 6304895 = 9457343) B9457343
theorem B2766059 : Blo 1228432 2766059 := bstep (se 1 (by rfl) ⟨2074544, by rfl⟩ : syracuseStep 2766059 = 4149089) B4149089
theorem B5248253 : Blo 1228432 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B2766473 : Blo 1228432 2766473 := bstep (se 2 (by rfl) ⟨1037427, by rfl⟩ : syracuseStep 2766473 = 2074855) B2074855
theorem B1382683 : Blo 1228432 1382683 := bstep (se 1 (by rfl) ⟨1037012, by rfl⟩ : syracuseStep 1382683 = 2074025) B2074025
theorem B11213083 : Blo 1228432 11213083 := bstep (se 1 (by rfl) ⟨8409812, by rfl⟩ : syracuseStep 11213083 = 16819625) B16819625
theorem B1382719 : Blo 1228432 1382719 := bstep (se 1 (by rfl) ⟨1037039, by rfl⟩ : syracuseStep 1382719 = 2074079) B2074079
theorem B1555195 : Blo 1228432 1555195 := bstep (se 1 (by rfl) ⟨1166396, by rfl⟩ : syracuseStep 1555195 = 2332793) B2332793
theorem B1383835 : Blo 1228432 1383835 := bstep (se 1 (by rfl) ⟨1037876, by rfl⟩ : syracuseStep 1383835 = 2075753) B2075753
theorem B1843577 : Blo 1228432 1843577 := bstep (se 2 (by rfl) ⟨691341, by rfl⟩ : syracuseStep 1843577 = 1382683) B1382683
theorem B14950777 : Blo 1228432 14950777 := bstep (se 2 (by rfl) ⟨5606541, by rfl⟩ : syracuseStep 14950777 = 11213083) B11213083
theorem B1843625 : Blo 1228432 1843625 := bstep (se 2 (by rfl) ⟨691359, by rfl⟩ : syracuseStep 1843625 = 1382719) B1382719
theorem B7479791 : Blo 1228432 7479791 := bstep (se 1 (by rfl) ⟨5609843, by rfl⟩ : syracuseStep 7479791 = 11219687) B11219687
theorem B1229311 : Blo 1228432 1229311 := bstep (se 1 (by rfl) ⟨921983, by rfl⟩ : syracuseStep 1229311 = 1843967) B1843967
theorem B4203263 : Blo 1228432 4203263 := bstep (se 1 (by rfl) ⟨3152447, by rfl⟩ : syracuseStep 4203263 = 6304895) B6304895
theorem B1844039 : Blo 1228432 1844039 := bstep (se 1 (by rfl) ⟨1383029, by rfl⟩ : syracuseStep 1844039 = 2766059) B2766059
theorem B2073593 : Blo 1228432 2073593 := bstep (se 2 (by rfl) ⟨777597, by rfl⟩ : syracuseStep 2073593 = 1555195) B1555195
theorem B1844315 : Blo 1228432 1844315 := bstep (se 1 (by rfl) ⟨1383236, by rfl⟩ : syracuseStep 1844315 = 2766473) B2766473
theorem B1845113 : Blo 1228432 1845113 := bstep (se 2 (by rfl) ⟨691917, by rfl⟩ : syracuseStep 1845113 = 1383835) B1383835
theorem B4147199 : Blo 1228432 4147199 := bstep (se 1 (by rfl) ⟨3110399, by rfl⟩ : syracuseStep 4147199 = 6220799) B6220799
theorem B4664263 : Blo 1228432 4664263 := bstep (se 1 (by rfl) ⟨3498197, by rfl⟩ : syracuseStep 4664263 = 6996395) B6996395
theorem B13995341 : Blo 1228432 13995341 := bstep (se 3 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 13995341 = 5248253) B5248253
theorem B2765177 : Blo 1228432 2765177 := bstep (se 2 (by rfl) ⟨1036941, by rfl⟩ : syracuseStep 2765177 = 2073883) B2073883
theorem B10498693 : Blo 1228432 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B3110683 : Blo 1228432 3110683 := bstep (se 1 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 3110683 = 4666025) B4666025
theorem B71899447 : Blo 1228432 71899447 := bstep (se 1 (by rfl) ⟨53924585, by rfl⟩ : syracuseStep 71899447 = 107849171) B107849171
theorem B1843451 : Blo 1228432 1843451 := bstep (se 1 (by rfl) ⟨1382588, by rfl⟩ : syracuseStep 1843451 = 2765177) B2765177
theorem B1229051 : Blo 1228432 1229051 := bstep (se 1 (by rfl) ⟨921788, by rfl⟩ : syracuseStep 1229051 = 1843577) B1843577
theorem B1229083 : Blo 1228432 1229083 := bstep (se 1 (by rfl) ⟨921812, by rfl⟩ : syracuseStep 1229083 = 1843625) B1843625
theorem B2802175 : Blo 1228432 2802175 := bstep (se 1 (by rfl) ⟨2101631, by rfl⟩ : syracuseStep 2802175 = 4203263) B4203263
theorem B1229359 : Blo 1228432 1229359 := bstep (se 1 (by rfl) ⟨922019, by rfl⟩ : syracuseStep 1229359 = 1844039) B1844039
theorem B1229543 : Blo 1228432 1229543 := bstep (se 1 (by rfl) ⟨922157, by rfl⟩ : syracuseStep 1229543 = 1844315) B1844315
theorem B1230075 : Blo 1228432 1230075 := bstep (se 1 (by rfl) ⟨922556, by rfl⟩ : syracuseStep 1230075 = 1845113) B1845113
theorem B6219017 : Blo 1228432 6219017 := bstep (se 2 (by rfl) ⟨2332131, by rfl⟩ : syracuseStep 6219017 = 4664263) B4664263
theorem B4147577 : Blo 1228432 4147577 := bstep (se 2 (by rfl) ⟨1555341, by rfl⟩ : syracuseStep 4147577 = 3110683) B3110683
theorem B95865929 : Blo 1228432 95865929 := bstep (se 2 (by rfl) ⟨35949723, by rfl⟩ : syracuseStep 95865929 = 71899447) B71899447
theorem B19934369 : Blo 1228432 19934369 := bstep (se 2 (by rfl) ⟨7475388, by rfl⟩ : syracuseStep 19934369 = 14950777) B14950777
theorem B2764799 : Blo 1228432 2764799 := bstep (se 1 (by rfl) ⟨2073599, by rfl⟩ : syracuseStep 2764799 = 4147199) B4147199
theorem B4986527 : Blo 1228432 4986527 := bstep (se 1 (by rfl) ⟨3739895, by rfl⟩ : syracuseStep 4986527 = 7479791) B7479791
theorem B1382395 : Blo 1228432 1382395 := bstep (se 1 (by rfl) ⟨1036796, by rfl⟩ : syracuseStep 1382395 = 2073593) B2073593
theorem B13998257 : Blo 1228432 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B9330227 : Blo 1228432 9330227 := bstep (se 1 (by rfl) ⟨6997670, by rfl⟩ : syracuseStep 9330227 = 13995341) B13995341
theorem B1228967 : Blo 1228432 1228967 := bstep (se 1 (by rfl) ⟨921725, by rfl⟩ : syracuseStep 1228967 = 1843451) B1843451
theorem B4146011 : Blo 1228432 4146011 := bstep (se 1 (by rfl) ⟨3109508, by rfl⟩ : syracuseStep 4146011 = 6219017) B6219017
theorem B9332171 : Blo 1228432 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B13297405 : Blo 1228432 13297405 := bstep (se 3 (by rfl) ⟨2493263, by rfl⟩ : syracuseStep 13297405 = 4986527) B4986527
theorem B13289579 : Blo 1228432 13289579 := bstep (se 1 (by rfl) ⟨9967184, by rfl⟩ : syracuseStep 13289579 = 19934369) B19934369
theorem B6220151 : Blo 1228432 6220151 := bstep (se 1 (by rfl) ⟨4665113, by rfl⟩ : syracuseStep 6220151 = 9330227) B9330227
theorem B14944933 : Blo 1228432 14944933 := bstep (se 4 (by rfl) ⟨1401087, by rfl⟩ : syracuseStep 14944933 = 2802175) B2802175
theorem B2765051 : Blo 1228432 2765051 := bstep (se 1 (by rfl) ⟨2073788, by rfl⟩ : syracuseStep 2765051 = 4147577) B4147577
theorem B63910619 : Blo 1228432 63910619 := bstep (se 1 (by rfl) ⟨47932964, by rfl⟩ : syracuseStep 63910619 = 95865929) B95865929
theorem B1843193 : Blo 1228432 1843193 := bstep (se 2 (by rfl) ⟨691197, by rfl⟩ : syracuseStep 1843193 = 1382395) B1382395
theorem B1843199 : Blo 1228432 1843199 := bstep (se 1 (by rfl) ⟨1382399, by rfl⟩ : syracuseStep 1843199 = 2764799) B2764799
theorem B1843367 : Blo 1228432 1843367 := bstep (se 1 (by rfl) ⟨1382525, by rfl⟩ : syracuseStep 1843367 = 2765051) B2765051
theorem B42607079 : Blo 1228432 42607079 := bstep (se 1 (by rfl) ⟨31955309, by rfl⟩ : syracuseStep 42607079 = 63910619) B63910619
theorem B4146767 : Blo 1228432 4146767 := bstep (se 1 (by rfl) ⟨3110075, by rfl⟩ : syracuseStep 4146767 = 6220151) B6220151
theorem B17729873 : Blo 1228432 17729873 := bstep (se 2 (by rfl) ⟨6648702, by rfl⟩ : syracuseStep 17729873 = 13297405) B13297405
theorem B2764007 : Blo 1228432 2764007 := bstep (se 1 (by rfl) ⟨2073005, by rfl⟩ : syracuseStep 2764007 = 4146011) B4146011
theorem B19926577 : Blo 1228432 19926577 := bstep (se 2 (by rfl) ⟨7472466, by rfl⟩ : syracuseStep 19926577 = 14944933) B14944933
theorem B6221447 : Blo 1228432 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B8859719 : Blo 1228432 8859719 := bstep (se 1 (by rfl) ⟨6644789, by rfl⟩ : syracuseStep 8859719 = 13289579) B13289579
theorem B1228799 : Blo 1228432 1228799 := bstep (se 1 (by rfl) ⟨921599, by rfl⟩ : syracuseStep 1228799 = 1843199) B1843199
theorem B1228795 : Blo 1228432 1228795 := bstep (se 1 (by rfl) ⟨921596, by rfl⟩ : syracuseStep 1228795 = 1843193) B1843193
theorem B5906479 : Blo 1228432 5906479 := bstep (se 1 (by rfl) ⟨4429859, by rfl⟩ : syracuseStep 5906479 = 8859719) B8859719
theorem B1228911 : Blo 1228432 1228911 := bstep (se 1 (by rfl) ⟨921683, by rfl⟩ : syracuseStep 1228911 = 1843367) B1843367
theorem B26568769 : Blo 1228432 26568769 := bstep (se 2 (by rfl) ⟨9963288, by rfl⟩ : syracuseStep 26568769 = 19926577) B19926577
theorem B4147631 : Blo 1228432 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B28404719 : Blo 1228432 28404719 := bstep (se 1 (by rfl) ⟨21303539, by rfl⟩ : syracuseStep 28404719 = 42607079) B42607079
theorem B2764511 : Blo 1228432 2764511 := bstep (se 1 (by rfl) ⟨2073383, by rfl⟩ : syracuseStep 2764511 = 4146767) B4146767
theorem B11819915 : Blo 1228432 11819915 := bstep (se 1 (by rfl) ⟨8864936, by rfl⟩ : syracuseStep 11819915 = 17729873) B17729873
theorem B1842671 : Blo 1228432 1842671 := bstep (se 1 (by rfl) ⟨1382003, by rfl⟩ : syracuseStep 1842671 = 2764007) B2764007
theorem B7875305 : Blo 1228432 7875305 := bstep (se 2 (by rfl) ⟨2953239, by rfl⟩ : syracuseStep 7875305 = 5906479) B5906479
theorem B35425025 : Blo 1228432 35425025 := bstep (se 2 (by rfl) ⟨13284384, by rfl⟩ : syracuseStep 35425025 = 26568769) B26568769
theorem B2765087 : Blo 1228432 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B18936479 : Blo 1228432 18936479 := bstep (se 1 (by rfl) ⟨14202359, by rfl⟩ : syracuseStep 18936479 = 28404719) B28404719
theorem B7879943 : Blo 1228432 7879943 := bstep (se 1 (by rfl) ⟨5909957, by rfl⟩ : syracuseStep 7879943 = 11819915) B11819915
theorem B1228447 : Blo 1228432 1228447 := bstep (se 1 (by rfl) ⟨921335, by rfl⟩ : syracuseStep 1228447 = 1842671) B1842671
theorem B1843007 : Blo 1228432 1843007 := bstep (se 1 (by rfl) ⟨1382255, by rfl⟩ : syracuseStep 1843007 = 2764511) B2764511
theorem B1843391 : Blo 1228432 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B12624319 : Blo 1228432 12624319 := bstep (se 1 (by rfl) ⟨9468239, by rfl⟩ : syracuseStep 12624319 = 18936479) B18936479
theorem B5253295 : Blo 1228432 5253295 := bstep (se 1 (by rfl) ⟨3939971, by rfl⟩ : syracuseStep 5253295 = 7879943) B7879943
theorem B5250203 : Blo 1228432 5250203 := bstep (se 1 (by rfl) ⟨3937652, by rfl⟩ : syracuseStep 5250203 = 7875305) B7875305
theorem B23616683 : Blo 1228432 23616683 := bstep (se 1 (by rfl) ⟨17712512, by rfl⟩ : syracuseStep 23616683 = 35425025) B35425025
theorem B1228671 : Blo 1228432 1228671 := bstep (se 1 (by rfl) ⟨921503, by rfl⟩ : syracuseStep 1228671 = 1843007) B1843007
theorem B1228927 : Blo 1228432 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B7004393 : Blo 1228432 7004393 := bstep (se 2 (by rfl) ⟨2626647, by rfl⟩ : syracuseStep 7004393 = 5253295) B5253295
theorem B3500135 : Blo 1228432 3500135 := bstep (se 1 (by rfl) ⟨2625101, by rfl⟩ : syracuseStep 3500135 = 5250203) B5250203
theorem B15744455 : Blo 1228432 15744455 := bstep (se 1 (by rfl) ⟨11808341, by rfl⟩ : syracuseStep 15744455 = 23616683) B23616683
theorem B67329701 : Blo 1228432 67329701 := bstep (se 4 (by rfl) ⟨6312159, by rfl⟩ : syracuseStep 67329701 = 12624319) B12624319
theorem B4669595 : Blo 1228432 4669595 := bstep (se 1 (by rfl) ⟨3502196, by rfl⟩ : syracuseStep 4669595 = 7004393) B7004393
theorem B10496303 : Blo 1228432 10496303 := bstep (se 1 (by rfl) ⟨7872227, by rfl⟩ : syracuseStep 10496303 = 15744455) B15744455
theorem B44886467 : Blo 1228432 44886467 := bstep (se 1 (by rfl) ⟨33664850, by rfl⟩ : syracuseStep 44886467 = 67329701) B67329701
theorem B2333423 : Blo 1228432 2333423 := bstep (se 1 (by rfl) ⟨1750067, by rfl⟩ : syracuseStep 2333423 = 3500135) B3500135
theorem B3113063 : Blo 1228432 3113063 := bstep (se 1 (by rfl) ⟨2334797, by rfl⟩ : syracuseStep 3113063 = 4669595) B4669595
theorem B6997535 : Blo 1228432 6997535 := bstep (se 1 (by rfl) ⟨5248151, by rfl⟩ : syracuseStep 6997535 = 10496303) B10496303
theorem B29924311 : Blo 1228432 29924311 := bstep (se 1 (by rfl) ⟨22443233, by rfl⟩ : syracuseStep 29924311 = 44886467) B44886467
theorem B1555615 : Blo 1228432 1555615 := bstep (se 1 (by rfl) ⟨1166711, by rfl⟩ : syracuseStep 1555615 = 2333423) B2333423
theorem B2074153 : Blo 1228432 2074153 := bstep (se 2 (by rfl) ⟨777807, by rfl⟩ : syracuseStep 2074153 = 1555615) B1555615
theorem B2075375 : Blo 1228432 2075375 := bstep (se 1 (by rfl) ⟨1556531, by rfl⟩ : syracuseStep 2075375 = 3113063) B3113063
theorem B4665023 : Blo 1228432 4665023 := bstep (se 1 (by rfl) ⟨3498767, by rfl⟩ : syracuseStep 4665023 = 6997535) B6997535
theorem B39899081 : Blo 1228432 39899081 := bstep (se 2 (by rfl) ⟨14962155, by rfl⟩ : syracuseStep 39899081 = 29924311) B29924311
theorem B2765537 : Blo 1228432 2765537 := bstep (se 2 (by rfl) ⟨1037076, by rfl⟩ : syracuseStep 2765537 = 2074153) B2074153
theorem B3110015 : Blo 1228432 3110015 := bstep (se 1 (by rfl) ⟨2332511, by rfl⟩ : syracuseStep 3110015 = 4665023) B4665023
theorem B1383583 : Blo 1228432 1383583 := bstep (se 1 (by rfl) ⟨1037687, by rfl⟩ : syracuseStep 1383583 = 2075375) B2075375
theorem B26599387 : Blo 1228432 26599387 := bstep (se 1 (by rfl) ⟨19949540, by rfl⟩ : syracuseStep 26599387 = 39899081) B39899081
theorem B1843691 : Blo 1228432 1843691 := bstep (se 1 (by rfl) ⟨1382768, by rfl⟩ : syracuseStep 1843691 = 2765537) B2765537
theorem B2073343 : Blo 1228432 2073343 := bstep (se 1 (by rfl) ⟨1555007, by rfl⟩ : syracuseStep 2073343 = 3110015) B3110015
theorem B1844777 : Blo 1228432 1844777 := bstep (se 2 (by rfl) ⟨691791, by rfl⟩ : syracuseStep 1844777 = 1383583) B1383583
theorem B35465849 : Blo 1228432 35465849 := bstep (se 2 (by rfl) ⟨13299693, by rfl⟩ : syracuseStep 35465849 = 26599387) B26599387
theorem B1229127 : Blo 1228432 1229127 := bstep (se 1 (by rfl) ⟨921845, by rfl⟩ : syracuseStep 1229127 = 1843691) B1843691
theorem B1229851 : Blo 1228432 1229851 := bstep (se 1 (by rfl) ⟨922388, by rfl⟩ : syracuseStep 1229851 = 1844777) B1844777
theorem B23643899 : Blo 1228432 23643899 := bstep (se 1 (by rfl) ⟨17732924, by rfl⟩ : syracuseStep 23643899 = 35465849) B35465849
theorem B2764457 : Blo 1228432 2764457 := bstep (se 2 (by rfl) ⟨1036671, by rfl⟩ : syracuseStep 2764457 = 2073343) B2073343
theorem B15762599 : Blo 1228432 15762599 := bstep (se 1 (by rfl) ⟨11821949, by rfl⟩ : syracuseStep 15762599 = 23643899) B23643899
theorem B1842971 : Blo 1228432 1842971 := bstep (se 1 (by rfl) ⟨1382228, by rfl⟩ : syracuseStep 1842971 = 2764457) B2764457
theorem B10508399 : Blo 1228432 10508399 := bstep (se 1 (by rfl) ⟨7881299, by rfl⟩ : syracuseStep 10508399 = 15762599) B15762599
theorem B1228647 : Blo 1228432 1228647 := bstep (se 1 (by rfl) ⟨921485, by rfl⟩ : syracuseStep 1228647 = 1842971) B1842971
theorem B7005599 : Blo 1228432 7005599 := bstep (se 1 (by rfl) ⟨5254199, by rfl⟩ : syracuseStep 7005599 = 10508399) B10508399
theorem B4670399 : Blo 1228432 4670399 := bstep (se 1 (by rfl) ⟨3502799, by rfl⟩ : syracuseStep 4670399 = 7005599) B7005599
theorem B3113599 : Blo 1228432 3113599 := bstep (se 1 (by rfl) ⟨2335199, by rfl⟩ : syracuseStep 3113599 = 4670399) B4670399
theorem B4151465 : Blo 1228432 4151465 := bstep (se 2 (by rfl) ⟨1556799, by rfl⟩ : syracuseStep 4151465 = 3113599) B3113599
theorem B2767643 : Blo 1228432 2767643 := bstep (se 1 (by rfl) ⟨2075732, by rfl⟩ : syracuseStep 2767643 = 4151465) B4151465
theorem B1845095 : Blo 1228432 1845095 := bstep (se 1 (by rfl) ⟨1383821, by rfl⟩ : syracuseStep 1845095 = 2767643) B2767643
theorem B1230063 : Blo 1228432 1230063 := bstep (se 1 (by rfl) ⟨922547, by rfl⟩ : syracuseStep 1230063 = 1845095) B1845095

theorem C0 (j : ℕ) (h1 : 307108 ≤ j) (h2 : j ≤ 307607) : Blo 1228432 (4 * j + 3) := by
  interval_cases j
  · exact B1228435
  · exact B1228439
  · exact B1228443
  · exact B1228447
  · exact B1228451
  · exact B1228455
  · exact B1228459
  · exact B1228463
  · exact B1228467
  · exact B1228471
  · exact B1228475
  · exact B1228479
  · exact B1228483
  · exact B1228487
  · exact B1228491
  · exact B1228495
  · exact B1228499
  · exact B1228503
  · exact B1228507
  · exact B1228511
  · exact B1228515
  · exact B1228519
  · exact B1228523
  · exact B1228527
  · exact B1228531
  · exact B1228535
  · exact B1228539
  · exact B1228543
  · exact B1228547
  · exact B1228551
  · exact B1228555
  · exact B1228559
  · exact B1228563
  · exact B1228567
  · exact B1228571
  · exact B1228575
  · exact B1228579
  · exact B1228583
  · exact B1228587
  · exact B1228591
  · exact B1228595
  · exact B1228599
  · exact B1228603
  · exact B1228607
  · exact B1228611
  · exact B1228615
  · exact B1228619
  · exact B1228623
  · exact B1228627
  · exact B1228631
  · exact B1228635
  · exact B1228639
  · exact B1228643
  · exact B1228647
  · exact B1228651
  · exact B1228655
  · exact B1228659
  · exact B1228663
  · exact B1228667
  · exact B1228671
  · exact B1228675
  · exact B1228679
  · exact B1228683
  · exact B1228687
  · exact B1228691
  · exact B1228695
  · exact B1228699
  · exact B1228703
  · exact B1228707
  · exact B1228711
  · exact B1228715
  · exact B1228719
  · exact B1228723
  · exact B1228727
  · exact B1228731
  · exact B1228735
  · exact B1228739
  · exact B1228743
  · exact B1228747
  · exact B1228751
  · exact B1228755
  · exact B1228759
  · exact B1228763
  · exact B1228767
  · exact B1228771
  · exact B1228775
  · exact B1228779
  · exact B1228783
  · exact B1228787
  · exact B1228791
  · exact B1228795
  · exact B1228799
  · exact B1228803
  · exact B1228807
  · exact B1228811
  · exact B1228815
  · exact B1228819
  · exact B1228823
  · exact B1228827
  · exact B1228831
  · exact B1228835
  · exact B1228839
  · exact B1228843
  · exact B1228847
  · exact B1228851
  · exact B1228855
  · exact B1228859
  · exact B1228863
  · exact B1228867
  · exact B1228871
  · exact B1228875
  · exact B1228879
  · exact B1228883
  · exact B1228887
  · exact B1228891
  · exact B1228895
  · exact B1228899
  · exact B1228903
  · exact B1228907
  · exact B1228911
  · exact B1228915
  · exact B1228919
  · exact B1228923
  · exact B1228927
  · exact B1228931
  · exact B1228935
  · exact B1228939
  · exact B1228943
  · exact B1228947
  · exact B1228951
  · exact B1228955
  · exact B1228959
  · exact B1228963
  · exact B1228967
  · exact B1228971
  · exact B1228975
  · exact B1228979
  · exact B1228983
  · exact B1228987
  · exact B1228991
  · exact B1228995
  · exact B1228999
  · exact B1229003
  · exact B1229007
  · exact B1229011
  · exact B1229015
  · exact B1229019
  · exact B1229023
  · exact B1229027
  · exact B1229031
  · exact B1229035
  · exact B1229039
  · exact B1229043
  · exact B1229047
  · exact B1229051
  · exact B1229055
  · exact B1229059
  · exact B1229063
  · exact B1229067
  · exact B1229071
  · exact B1229075
  · exact B1229079
  · exact B1229083
  · exact B1229087
  · exact B1229091
  · exact B1229095
  · exact B1229099
  · exact B1229103
  · exact B1229107
  · exact B1229111
  · exact B1229115
  · exact B1229119
  · exact B1229123
  · exact B1229127
  · exact B1229131
  · exact B1229135
  · exact B1229139
  · exact B1229143
  · exact B1229147
  · exact B1229151
  · exact B1229155
  · exact B1229159
  · exact B1229163
  · exact B1229167
  · exact B1229171
  · exact B1229175
  · exact B1229179
  · exact B1229183
  · exact B1229187
  · exact B1229191
  · exact B1229195
  · exact B1229199
  · exact B1229203
  · exact B1229207
  · exact B1229211
  · exact B1229215
  · exact B1229219
  · exact B1229223
  · exact B1229227
  · exact B1229231
  · exact B1229235
  · exact B1229239
  · exact B1229243
  · exact B1229247
  · exact B1229251
  · exact B1229255
  · exact B1229259
  · exact B1229263
  · exact B1229267
  · exact B1229271
  · exact B1229275
  · exact B1229279
  · exact B1229283
  · exact B1229287
  · exact B1229291
  · exact B1229295
  · exact B1229299
  · exact B1229303
  · exact B1229307
  · exact B1229311
  · exact B1229315
  · exact B1229319
  · exact B1229323
  · exact B1229327
  · exact B1229331
  · exact B1229335
  · exact B1229339
  · exact B1229343
  · exact B1229347
  · exact B1229351
  · exact B1229355
  · exact B1229359
  · exact B1229363
  · exact B1229367
  · exact B1229371
  · exact B1229375
  · exact B1229379
  · exact B1229383
  · exact B1229387
  · exact B1229391
  · exact B1229395
  · exact B1229399
  · exact B1229403
  · exact B1229407
  · exact B1229411
  · exact B1229415
  · exact B1229419
  · exact B1229423
  · exact B1229427
  · exact B1229431
  · exact B1229435
  · exact B1229439
  · exact B1229443
  · exact B1229447
  · exact B1229451
  · exact B1229455
  · exact B1229459
  · exact B1229463
  · exact B1229467
  · exact B1229471
  · exact B1229475
  · exact B1229479
  · exact B1229483
  · exact B1229487
  · exact B1229491
  · exact B1229495
  · exact B1229499
  · exact B1229503
  · exact B1229507
  · exact B1229511
  · exact B1229515
  · exact B1229519
  · exact B1229523
  · exact B1229527
  · exact B1229531
  · exact B1229535
  · exact B1229539
  · exact B1229543
  · exact B1229547
  · exact B1229551
  · exact B1229555
  · exact B1229559
  · exact B1229563
  · exact B1229567
  · exact B1229571
  · exact B1229575
  · exact B1229579
  · exact B1229583
  · exact B1229587
  · exact B1229591
  · exact B1229595
  · exact B1229599
  · exact B1229603
  · exact B1229607
  · exact B1229611
  · exact B1229615
  · exact B1229619
  · exact B1229623
  · exact B1229627
  · exact B1229631
  · exact B1229635
  · exact B1229639
  · exact B1229643
  · exact B1229647
  · exact B1229651
  · exact B1229655
  · exact B1229659
  · exact B1229663
  · exact B1229667
  · exact B1229671
  · exact B1229675
  · exact B1229679
  · exact B1229683
  · exact B1229687
  · exact B1229691
  · exact B1229695
  · exact B1229699
  · exact B1229703
  · exact B1229707
  · exact B1229711
  · exact B1229715
  · exact B1229719
  · exact B1229723
  · exact B1229727
  · exact B1229731
  · exact B1229735
  · exact B1229739
  · exact B1229743
  · exact B1229747
  · exact B1229751
  · exact B1229755
  · exact B1229759
  · exact B1229763
  · exact B1229767
  · exact B1229771
  · exact B1229775
  · exact B1229779
  · exact B1229783
  · exact B1229787
  · exact B1229791
  · exact B1229795
  · exact B1229799
  · exact B1229803
  · exact B1229807
  · exact B1229811
  · exact B1229815
  · exact B1229819
  · exact B1229823
  · exact B1229827
  · exact B1229831
  · exact B1229835
  · exact B1229839
  · exact B1229843
  · exact B1229847
  · exact B1229851
  · exact B1229855
  · exact B1229859
  · exact B1229863
  · exact B1229867
  · exact B1229871
  · exact B1229875
  · exact B1229879
  · exact B1229883
  · exact B1229887
  · exact B1229891
  · exact B1229895
  · exact B1229899
  · exact B1229903
  · exact B1229907
  · exact B1229911
  · exact B1229915
  · exact B1229919
  · exact B1229923
  · exact B1229927
  · exact B1229931
  · exact B1229935
  · exact B1229939
  · exact B1229943
  · exact B1229947
  · exact B1229951
  · exact B1229955
  · exact B1229959
  · exact B1229963
  · exact B1229967
  · exact B1229971
  · exact B1229975
  · exact B1229979
  · exact B1229983
  · exact B1229987
  · exact B1229991
  · exact B1229995
  · exact B1229999
  · exact B1230003
  · exact B1230007
  · exact B1230011
  · exact B1230015
  · exact B1230019
  · exact B1230023
  · exact B1230027
  · exact B1230031
  · exact B1230035
  · exact B1230039
  · exact B1230043
  · exact B1230047
  · exact B1230051
  · exact B1230055
  · exact B1230059
  · exact B1230063
  · exact B1230067
  · exact B1230071
  · exact B1230075
  · exact B1230079
  · exact B1230083
  · exact B1230087
  · exact B1230091
  · exact B1230095
  · exact B1230099
  · exact B1230103
  · exact B1230107
  · exact B1230111
  · exact B1230115
  · exact B1230119
  · exact B1230123
  · exact B1230127
  · exact B1230131
  · exact B1230135
  · exact B1230139
  · exact B1230143
  · exact B1230147
  · exact B1230151
  · exact B1230155
  · exact B1230159
  · exact B1230163
  · exact B1230167
  · exact B1230171
  · exact B1230175
  · exact B1230179
  · exact B1230183
  · exact B1230187
  · exact B1230191
  · exact B1230195
  · exact B1230199
  · exact B1230203
  · exact B1230207
  · exact B1230211
  · exact B1230215
  · exact B1230219
  · exact B1230223
  · exact B1230227
  · exact B1230231
  · exact B1230235
  · exact B1230239
  · exact B1230243
  · exact B1230247
  · exact B1230251
  · exact B1230255
  · exact B1230259
  · exact B1230263
  · exact B1230267
  · exact B1230271
  · exact B1230275
  · exact B1230279
  · exact B1230283
  · exact B1230287
  · exact B1230291
  · exact B1230295
  · exact B1230299
  · exact B1230303
  · exact B1230307
  · exact B1230311
  · exact B1230315
  · exact B1230319
  · exact B1230323
  · exact B1230327
  · exact B1230331
  · exact B1230335
  · exact B1230339
  · exact B1230343
  · exact B1230347
  · exact B1230351
  · exact B1230355
  · exact B1230359
  · exact B1230363
  · exact B1230367
  · exact B1230371
  · exact B1230375
  · exact B1230379
  · exact B1230383
  · exact B1230387
  · exact B1230391
  · exact B1230395
  · exact B1230399
  · exact B1230403
  · exact B1230407
  · exact B1230411
  · exact B1230415
  · exact B1230419
  · exact B1230423
  · exact B1230427
  · exact B1230431

theorem solution (m : ℕ) (hlo : 1228432 ≤ m) (hhi : m ≤ 1230432) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 307108 ≤ j := by omega
    have hj2 : j ≤ 307607 := by omega
    have hb : Blo 1228432 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
