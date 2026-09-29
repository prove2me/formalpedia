-- Prove2me | solution 1 for syracuse_descends_range_1589493_1590993
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:08:40.132337+00:00
-- url     : https://prove2.me/submissions/3b3da9f1-e185-418c-a8fc-e454c259072c

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


theorem B2547821 : Blo 1589493 2547821 := bbase (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) (by norm_num)
theorem B4530325 : Blo 1589493 4530325 := bbase (se 6 (by rfl) ⟨106179, by rfl⟩ : syracuseStep 4530325 = 212359) (by norm_num)
theorem B5365925 : Blo 1589493 5365925 := bbase (se 4 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 5365925 = 1006111) (by norm_num)
theorem B6037685 : Blo 1589493 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B5095669 : Blo 1589493 5095669 := bbase (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) (by norm_num)
theorem B4530485 : Blo 1589493 4530485 := bbase (se 5 (by rfl) ⟨212366, by rfl⟩ : syracuseStep 4530485 = 424733) (by norm_num)
theorem B235266389 : Blo 1589493 235266389 := bbase (se 10 (by rfl) ⟨344628, by rfl⟩ : syracuseStep 235266389 = 689257) (by norm_num)
theorem B6791525 : Blo 1589493 6791525 := bbase (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) (by norm_num)
theorem B2384261 : Blo 1589493 2384261 := bbase (se 4 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 2384261 = 447049) (by norm_num)
theorem B4358549 : Blo 1589493 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B2384285 : Blo 1589493 2384285 := bbase (se 3 (by rfl) ⟨447053, by rfl⟩ : syracuseStep 2384285 = 894107) (by norm_num)
theorem B2384309 : Blo 1589493 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B2384333 : Blo 1589493 2384333 := bbase (se 3 (by rfl) ⟨447062, by rfl⟩ : syracuseStep 2384333 = 894125) (by norm_num)
theorem B6037973 : Blo 1589493 6037973 := bbase (se 7 (by rfl) ⟨70757, by rfl⟩ : syracuseStep 6037973 = 141515) (by norm_num)
theorem B2384357 : Blo 1589493 2384357 := bbase (se 4 (by rfl) ⟨223533, by rfl⟩ : syracuseStep 2384357 = 447067) (by norm_num)
theorem B2384381 : Blo 1589493 2384381 := bbase (se 3 (by rfl) ⟨447071, by rfl⟩ : syracuseStep 2384381 = 894143) (by norm_num)
theorem B2384405 : Blo 1589493 2384405 := bbase (se 6 (by rfl) ⟨55884, by rfl⟩ : syracuseStep 2384405 = 111769) (by norm_num)
theorem B2384429 : Blo 1589493 2384429 := bbase (se 3 (by rfl) ⟨447080, by rfl⟩ : syracuseStep 2384429 = 894161) (by norm_num)
theorem B2548277 : Blo 1589493 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B2384453 : Blo 1589493 2384453 := bbase (se 4 (by rfl) ⟨223542, by rfl⟩ : syracuseStep 2384453 = 447085) (by norm_num)
theorem B5366357 : Blo 1589493 5366357 := bbase (se 8 (by rfl) ⟨31443, by rfl⟩ : syracuseStep 5366357 = 62887) (by norm_num)
theorem B2384477 : Blo 1589493 2384477 := bbase (se 3 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 2384477 = 894179) (by norm_num)
theorem B2384501 : Blo 1589493 2384501 := bbase (se 5 (by rfl) ⟨111773, by rfl⟩ : syracuseStep 2384501 = 223547) (by norm_num)
theorem B2384525 : Blo 1589493 2384525 := bbase (se 3 (by rfl) ⟨447098, by rfl⟩ : syracuseStep 2384525 = 894197) (by norm_num)
theorem B2384549 : Blo 1589493 2384549 := bbase (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) (by norm_num)
theorem B10191541 : Blo 1589493 10191541 := bbase (se 5 (by rfl) ⟨477728, by rfl⟩ : syracuseStep 10191541 = 955457) (by norm_num)
theorem B2384573 : Blo 1589493 2384573 := bbase (se 3 (by rfl) ⟨447107, by rfl⟩ : syracuseStep 2384573 = 894215) (by norm_num)
theorem B2384597 : Blo 1589493 2384597 := bbase (se 7 (by rfl) ⟨27944, by rfl⟩ : syracuseStep 2384597 = 55889) (by norm_num)
theorem B2384621 : Blo 1589493 2384621 := bbase (se 3 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 2384621 = 894233) (by norm_num)
theorem B2384645 : Blo 1589493 2384645 := bbase (se 4 (by rfl) ⟨223560, by rfl⟩ : syracuseStep 2384645 = 447121) (by norm_num)
theorem B2417413 : Blo 1589493 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B2384669 : Blo 1589493 2384669 := bbase (se 3 (by rfl) ⟨447125, by rfl⟩ : syracuseStep 2384669 = 894251) (by norm_num)
theorem B2384693 : Blo 1589493 2384693 := bbase (se 5 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 2384693 = 223565) (by norm_num)
theorem B2384717 : Blo 1589493 2384717 := bbase (se 3 (by rfl) ⟨447134, by rfl⟩ : syracuseStep 2384717 = 894269) (by norm_num)
theorem B2384741 : Blo 1589493 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B2384765 : Blo 1589493 2384765 := bbase (se 3 (by rfl) ⟨447143, by rfl⟩ : syracuseStep 2384765 = 894287) (by norm_num)
theorem B2384789 : Blo 1589493 2384789 := bbase (se 6 (by rfl) ⟨55893, by rfl⟩ : syracuseStep 2384789 = 111787) (by norm_num)
theorem B2384813 : Blo 1589493 2384813 := bbase (se 3 (by rfl) ⟨447152, by rfl⟩ : syracuseStep 2384813 = 894305) (by norm_num)
theorem B2384837 : Blo 1589493 2384837 := bbase (se 4 (by rfl) ⟨223578, by rfl⟩ : syracuseStep 2384837 = 447157) (by norm_num)
theorem B2384861 : Blo 1589493 2384861 := bbase (se 3 (by rfl) ⟨447161, by rfl⟩ : syracuseStep 2384861 = 894323) (by norm_num)
theorem B2384885 : Blo 1589493 2384885 := bbase (se 5 (by rfl) ⟨111791, by rfl⟩ : syracuseStep 2384885 = 223583) (by norm_num)
theorem B5366789 : Blo 1589493 5366789 := bbase (se 4 (by rfl) ⟨503136, by rfl⟩ : syracuseStep 5366789 = 1006273) (by norm_num)
theorem B2384909 : Blo 1589493 2384909 := bbase (se 3 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 2384909 = 894341) (by norm_num)
theorem B2384933 : Blo 1589493 2384933 := bbase (se 4 (by rfl) ⟨223587, by rfl⟩ : syracuseStep 2384933 = 447175) (by norm_num)
theorem B2384957 : Blo 1589493 2384957 := bbase (se 3 (by rfl) ⟨447179, by rfl⟩ : syracuseStep 2384957 = 894359) (by norm_num)
theorem B8053829 : Blo 1589493 8053829 := bbase (se 4 (by rfl) ⟨755046, by rfl⟩ : syracuseStep 8053829 = 1510093) (by norm_num)
theorem B2384981 : Blo 1589493 2384981 := bbase (se 8 (by rfl) ⟨13974, by rfl⟩ : syracuseStep 2384981 = 27949) (by norm_num)
theorem B2385005 : Blo 1589493 2385005 := bbase (se 3 (by rfl) ⟨447188, by rfl⟩ : syracuseStep 2385005 = 894377) (by norm_num)
theorem B2385029 : Blo 1589493 2385029 := bbase (se 4 (by rfl) ⟨223596, by rfl⟩ : syracuseStep 2385029 = 447193) (by norm_num)
theorem B2385053 : Blo 1589493 2385053 := bbase (se 3 (by rfl) ⟨447197, by rfl⟩ : syracuseStep 2385053 = 894395) (by norm_num)
theorem B2385077 : Blo 1589493 2385077 := bbase (se 5 (by rfl) ⟨111800, by rfl⟩ : syracuseStep 2385077 = 223601) (by norm_num)
theorem B2385101 : Blo 1589493 2385101 := bbase (se 3 (by rfl) ⟨447206, by rfl⟩ : syracuseStep 2385101 = 894413) (by norm_num)
theorem B2385125 : Blo 1589493 2385125 := bbase (se 4 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 2385125 = 447211) (by norm_num)
theorem B4023533 : Blo 1589493 4023533 := bbase (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) (by norm_num)
theorem B2385149 : Blo 1589493 2385149 := bbase (se 3 (by rfl) ⟨447215, by rfl⟩ : syracuseStep 2385149 = 894431) (by norm_num)
theorem B2385173 : Blo 1589493 2385173 := bbase (se 6 (by rfl) ⟨55902, by rfl⟩ : syracuseStep 2385173 = 111805) (by norm_num)
theorem B2385197 : Blo 1589493 2385197 := bbase (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) (by norm_num)
theorem B2385221 : Blo 1589493 2385221 := bbase (se 4 (by rfl) ⟨223614, by rfl⟩ : syracuseStep 2385221 = 447229) (by norm_num)
theorem B2385245 : Blo 1589493 2385245 := bbase (se 3 (by rfl) ⟨447233, by rfl⟩ : syracuseStep 2385245 = 894467) (by norm_num)
theorem B6120805 : Blo 1589493 6120805 := bbase (se 4 (by rfl) ⟨573825, by rfl⟩ : syracuseStep 6120805 = 1147651) (by norm_num)
theorem B2385269 : Blo 1589493 2385269 := bbase (se 5 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 2385269 = 223619) (by norm_num)
theorem B2385293 : Blo 1589493 2385293 := bbase (se 3 (by rfl) ⟨447242, by rfl⟩ : syracuseStep 2385293 = 894485) (by norm_num)
theorem B2385317 : Blo 1589493 2385317 := bbase (se 4 (by rfl) ⟨223623, by rfl⟩ : syracuseStep 2385317 = 447247) (by norm_num)
theorem B5367221 : Blo 1589493 5367221 := bbase (se 5 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 5367221 = 503177) (by norm_num)
theorem B2385341 : Blo 1589493 2385341 := bbase (se 3 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 2385341 = 894503) (by norm_num)
theorem B2385365 : Blo 1589493 2385365 := bbase (se 7 (by rfl) ⟨27953, by rfl⟩ : syracuseStep 2385365 = 55907) (by norm_num)
theorem B2418149 : Blo 1589493 2418149 := bbase (se 4 (by rfl) ⟨226701, by rfl⟩ : syracuseStep 2418149 = 453403) (by norm_num)
theorem B2385389 : Blo 1589493 2385389 := bbase (se 3 (by rfl) ⟨447260, by rfl⟩ : syracuseStep 2385389 = 894521) (by norm_num)
theorem B1910261 : Blo 1589493 1910261 := bbase (se 5 (by rfl) ⟨89543, by rfl⟩ : syracuseStep 1910261 = 179087) (by norm_num)
theorem B2385413 : Blo 1589493 2385413 := bbase (se 4 (by rfl) ⟨223632, by rfl⟩ : syracuseStep 2385413 = 447265) (by norm_num)
theorem B2385437 : Blo 1589493 2385437 := bbase (se 3 (by rfl) ⟨447269, by rfl⟩ : syracuseStep 2385437 = 894539) (by norm_num)
theorem B2385461 : Blo 1589493 2385461 := bbase (se 5 (by rfl) ⟨111818, by rfl⟩ : syracuseStep 2385461 = 223637) (by norm_num)
theorem B4023877 : Blo 1589493 4023877 := bbase (se 4 (by rfl) ⟨377238, by rfl⟩ : syracuseStep 4023877 = 754477) (by norm_num)
theorem B2385485 : Blo 1589493 2385485 := bbase (se 3 (by rfl) ⟨447278, by rfl⟩ : syracuseStep 2385485 = 894557) (by norm_num)
theorem B19613269 : Blo 1589493 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B2385509 : Blo 1589493 2385509 := bbase (se 4 (by rfl) ⟨223641, by rfl⟩ : syracuseStep 2385509 = 447283) (by norm_num)
theorem B4834933 : Blo 1589493 4834933 := bbase (se 5 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 4834933 = 453275) (by norm_num)
theorem B6039157 : Blo 1589493 6039157 := bbase (se 5 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 6039157 = 566171) (by norm_num)
theorem B2385533 : Blo 1589493 2385533 := bbase (se 3 (by rfl) ⟨447287, by rfl⟩ : syracuseStep 2385533 = 894575) (by norm_num)
theorem B27158165 : Blo 1589493 27158165 := bbase (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) (by norm_num)
theorem B2385557 : Blo 1589493 2385557 := bbase (se 6 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 2385557 = 111823) (by norm_num)
theorem B1697437 : Blo 1589493 1697437 := bbase (se 3 (by rfl) ⟨318269, by rfl⟩ : syracuseStep 1697437 = 636539) (by norm_num)
theorem B2385581 : Blo 1589493 2385581 := bbase (se 3 (by rfl) ⟨447296, by rfl⟩ : syracuseStep 2385581 = 894593) (by norm_num)
theorem B4023989 : Blo 1589493 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B2385605 : Blo 1589493 2385605 := bbase (se 4 (by rfl) ⟨223650, by rfl⟩ : syracuseStep 2385605 = 447301) (by norm_num)
theorem B2385629 : Blo 1589493 2385629 := bbase (se 3 (by rfl) ⟨447305, by rfl⟩ : syracuseStep 2385629 = 894611) (by norm_num)
theorem B2385653 : Blo 1589493 2385653 := bbase (se 5 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 2385653 = 223655) (by norm_num)
theorem B2385677 : Blo 1589493 2385677 := bbase (se 3 (by rfl) ⟨447314, by rfl⟩ : syracuseStep 2385677 = 894629) (by norm_num)
theorem B2385701 : Blo 1589493 2385701 := bbase (se 4 (by rfl) ⟨223659, by rfl⟩ : syracuseStep 2385701 = 447319) (by norm_num)
theorem B1910569 : Blo 1589493 1910569 := bbase (se 2 (by rfl) ⟨716463, by rfl⟩ : syracuseStep 1910569 = 1432927) (by norm_num)
theorem B2385725 : Blo 1589493 2385725 := bbase (se 3 (by rfl) ⟨447323, by rfl⟩ : syracuseStep 2385725 = 894647) (by norm_num)
theorem B2385749 : Blo 1589493 2385749 := bbase (se 9 (by rfl) ⟨6989, by rfl⟩ : syracuseStep 2385749 = 13979) (by norm_num)
theorem B5367653 : Blo 1589493 5367653 := bbase (se 4 (by rfl) ⟨503217, by rfl⟩ : syracuseStep 5367653 = 1006435) (by norm_num)
theorem B2385773 : Blo 1589493 2385773 := bbase (se 3 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 2385773 = 894665) (by norm_num)
theorem B4024181 : Blo 1589493 4024181 := bbase (se 5 (by rfl) ⟨188633, by rfl⟩ : syracuseStep 4024181 = 377267) (by norm_num)
theorem B2385797 : Blo 1589493 2385797 := bbase (se 4 (by rfl) ⟨223668, by rfl⟩ : syracuseStep 2385797 = 447337) (by norm_num)
theorem B1697689 : Blo 1589493 1697689 := bbase (se 2 (by rfl) ⟨636633, by rfl⟩ : syracuseStep 1697689 = 1273267) (by norm_num)
theorem B1697693 : Blo 1589493 1697693 := bbase (se 3 (by rfl) ⟨318317, by rfl⟩ : syracuseStep 1697693 = 636635) (by norm_num)
theorem B2385821 : Blo 1589493 2385821 := bbase (se 3 (by rfl) ⟨447341, by rfl⟩ : syracuseStep 2385821 = 894683) (by norm_num)
theorem B6039461 : Blo 1589493 6039461 := bbase (se 4 (by rfl) ⟨566199, by rfl⟩ : syracuseStep 6039461 = 1132399) (by norm_num)
theorem B2385845 : Blo 1589493 2385845 := bbase (se 5 (by rfl) ⟨111836, by rfl⟩ : syracuseStep 2385845 = 223673) (by norm_num)
theorem B2385869 : Blo 1589493 2385869 := bbase (se 3 (by rfl) ⟨447350, by rfl⟩ : syracuseStep 2385869 = 894701) (by norm_num)
theorem B2385893 : Blo 1589493 2385893 := bbase (se 4 (by rfl) ⟨223677, by rfl⟩ : syracuseStep 2385893 = 447355) (by norm_num)
theorem B2582525 : Blo 1589493 2582525 := bbase (se 3 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 2582525 = 968447) (by norm_num)
theorem B2385917 : Blo 1589493 2385917 := bbase (se 3 (by rfl) ⟨447359, by rfl⟩ : syracuseStep 2385917 = 894719) (by norm_num)
theorem B1910785 : Blo 1589493 1910785 := bbase (se 2 (by rfl) ⟨716544, by rfl⟩ : syracuseStep 1910785 = 1433089) (by norm_num)
theorem B2385941 : Blo 1589493 2385941 := bbase (se 6 (by rfl) ⟨55920, by rfl⟩ : syracuseStep 2385941 = 111841) (by norm_num)
theorem B2385965 : Blo 1589493 2385965 := bbase (se 3 (by rfl) ⟨447368, by rfl⟩ : syracuseStep 2385965 = 894737) (by norm_num)
theorem B2385989 : Blo 1589493 2385989 := bbase (se 4 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 2385989 = 447373) (by norm_num)
theorem B6793301 : Blo 1589493 6793301 := bbase (se 8 (by rfl) ⟨39804, by rfl⟩ : syracuseStep 6793301 = 79609) (by norm_num)
theorem B2386013 : Blo 1589493 2386013 := bbase (se 3 (by rfl) ⟨447377, by rfl⟩ : syracuseStep 2386013 = 894755) (by norm_num)
theorem B2386037 : Blo 1589493 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B2418805 : Blo 1589493 2418805 := bbase (se 5 (by rfl) ⟨113381, by rfl⟩ : syracuseStep 2418805 = 226763) (by norm_num)
theorem B2386061 : Blo 1589493 2386061 := bbase (se 3 (by rfl) ⟨447386, by rfl⟩ : syracuseStep 2386061 = 894773) (by norm_num)
theorem B2386085 : Blo 1589493 2386085 := bbase (se 4 (by rfl) ⟨223695, by rfl⟩ : syracuseStep 2386085 = 447391) (by norm_num)
theorem B2386109 : Blo 1589493 2386109 := bbase (se 3 (by rfl) ⟨447395, by rfl⟩ : syracuseStep 2386109 = 894791) (by norm_num)
theorem B4024525 : Blo 1589493 4024525 := bbase (se 3 (by rfl) ⟨754598, by rfl⟩ : syracuseStep 4024525 = 1509197) (by norm_num)
theorem B2386133 : Blo 1589493 2386133 := bbase (se 7 (by rfl) ⟨27962, by rfl⟩ : syracuseStep 2386133 = 55925) (by norm_num)
theorem B2386157 : Blo 1589493 2386157 := bbase (se 3 (by rfl) ⟨447404, by rfl⟩ : syracuseStep 2386157 = 894809) (by norm_num)
theorem B2386181 : Blo 1589493 2386181 := bbase (se 4 (by rfl) ⟨223704, by rfl⟩ : syracuseStep 2386181 = 447409) (by norm_num)
theorem B5368085 : Blo 1589493 5368085 := bbase (se 6 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 5368085 = 251629) (by norm_num)
theorem B2386205 : Blo 1589493 2386205 := bbase (se 3 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 2386205 = 894827) (by norm_num)
theorem B1788205 : Blo 1589493 1788205 := bbase (se 3 (by rfl) ⟨335288, by rfl⟩ : syracuseStep 1788205 = 670577) (by norm_num)
theorem B2386229 : Blo 1589493 2386229 := bbase (se 5 (by rfl) ⟨111854, by rfl⟩ : syracuseStep 2386229 = 223709) (by norm_num)
theorem B4024637 : Blo 1589493 4024637 := bbase (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) (by norm_num)
theorem B6793541 : Blo 1589493 6793541 := bbase (se 4 (by rfl) ⟨636894, by rfl⟩ : syracuseStep 6793541 = 1273789) (by norm_num)
theorem B2386253 : Blo 1589493 2386253 := bbase (se 3 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 2386253 = 894845) (by norm_num)
theorem B1788241 : Blo 1589493 1788241 := bbase (se 2 (by rfl) ⟨670590, by rfl⟩ : syracuseStep 1788241 = 1341181) (by norm_num)
theorem B2386277 : Blo 1589493 2386277 := bbase (se 4 (by rfl) ⟨223713, by rfl⟩ : syracuseStep 2386277 = 447427) (by norm_num)
theorem B1788277 : Blo 1589493 1788277 := bbase (se 5 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 1788277 = 167651) (by norm_num)
theorem B2148725 : Blo 1589493 2148725 := bbase (se 5 (by rfl) ⟨100721, by rfl⟩ : syracuseStep 2148725 = 201443) (by norm_num)
theorem B2386301 : Blo 1589493 2386301 := bbase (se 3 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 2386301 = 894863) (by norm_num)
theorem B2386325 : Blo 1589493 2386325 := bbase (se 6 (by rfl) ⟨55929, by rfl⟩ : syracuseStep 2386325 = 111859) (by norm_num)
theorem B1788313 : Blo 1589493 1788313 := bbase (se 2 (by rfl) ⟨670617, by rfl⟩ : syracuseStep 1788313 = 1341235) (by norm_num)
theorem B2386349 : Blo 1589493 2386349 := bbase (se 3 (by rfl) ⟨447440, by rfl⟩ : syracuseStep 2386349 = 894881) (by norm_num)
theorem B2263477 : Blo 1589493 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1788349 : Blo 1589493 1788349 := bbase (se 3 (by rfl) ⟨335315, by rfl⟩ : syracuseStep 1788349 = 670631) (by norm_num)
theorem B6121925 : Blo 1589493 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B2386373 : Blo 1589493 2386373 := bbase (se 4 (by rfl) ⟨223722, by rfl⟩ : syracuseStep 2386373 = 447445) (by norm_num)
theorem B1812937 : Blo 1589493 1812937 := bbase (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) (by norm_num)
theorem B1698257 : Blo 1589493 1698257 := bbase (se 2 (by rfl) ⟨636846, by rfl⟩ : syracuseStep 1698257 = 1273693) (by norm_num)
theorem B2386397 : Blo 1589493 2386397 := bbase (se 3 (by rfl) ⟨447449, by rfl⟩ : syracuseStep 2386397 = 894899) (by norm_num)
theorem B1788385 : Blo 1589493 1788385 := bbase (se 2 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 1788385 = 1341289) (by norm_num)
theorem B2386421 : Blo 1589493 2386421 := bbase (se 5 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 2386421 = 223727) (by norm_num)
theorem B4024829 : Blo 1589493 4024829 := bbase (se 3 (by rfl) ⟨754655, by rfl⟩ : syracuseStep 4024829 = 1509311) (by norm_num)
theorem B1788421 : Blo 1589493 1788421 := bbase (se 4 (by rfl) ⟨167664, by rfl⟩ : syracuseStep 1788421 = 335329) (by norm_num)
theorem B2386445 : Blo 1589493 2386445 := bbase (se 3 (by rfl) ⟨447458, by rfl⟩ : syracuseStep 2386445 = 894917) (by norm_num)
theorem B18106901 : Blo 1589493 18106901 := bbase (se 6 (by rfl) ⟨424380, by rfl⟩ : syracuseStep 18106901 = 848761) (by norm_num)
theorem B1935905 : Blo 1589493 1935905 := bbase (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) (by norm_num)
theorem B2386469 : Blo 1589493 2386469 := bbase (se 4 (by rfl) ⟨223731, by rfl⟩ : syracuseStep 2386469 = 447463) (by norm_num)
theorem B1788457 : Blo 1589493 1788457 := bbase (se 2 (by rfl) ⟨670671, by rfl⟩ : syracuseStep 1788457 = 1341343) (by norm_num)
theorem B9054773 : Blo 1589493 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B1788493 : Blo 1589493 1788493 := bbase (se 3 (by rfl) ⟨335342, by rfl⟩ : syracuseStep 1788493 = 670685) (by norm_num)
theorem B3820117 : Blo 1589493 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B2583149 : Blo 1589493 2583149 := bbase (se 3 (by rfl) ⟨484340, by rfl⟩ : syracuseStep 2583149 = 968681) (by norm_num)
theorem B1788529 : Blo 1589493 1788529 := bbase (se 2 (by rfl) ⟨670698, by rfl⟩ : syracuseStep 1788529 = 1341397) (by norm_num)
theorem B1698445 : Blo 1589493 1698445 := bbase (se 3 (by rfl) ⟨318458, by rfl⟩ : syracuseStep 1698445 = 636917) (by norm_num)
theorem B1788565 : Blo 1589493 1788565 := bbase (se 6 (by rfl) ⟨41919, by rfl⟩ : syracuseStep 1788565 = 83839) (by norm_num)
theorem B1788601 : Blo 1589493 1788601 := bbase (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) (by norm_num)
theorem B5368517 : Blo 1589493 5368517 := bbase (se 4 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 5368517 = 1006597) (by norm_num)
theorem B1788637 : Blo 1589493 1788637 := bbase (se 3 (by rfl) ⟨335369, by rfl⟩ : syracuseStep 1788637 = 670739) (by norm_num)
theorem B8047349 : Blo 1589493 8047349 := bbase (se 5 (by rfl) ⟨377219, by rfl⟩ : syracuseStep 8047349 = 754439) (by norm_num)
theorem B1788673 : Blo 1589493 1788673 := bbase (se 2 (by rfl) ⟨670752, by rfl⟩ : syracuseStep 1788673 = 1341505) (by norm_num)
theorem B1788709 : Blo 1589493 1788709 := bbase (se 4 (by rfl) ⟨167691, by rfl⟩ : syracuseStep 1788709 = 335383) (by norm_num)
theorem B1788745 : Blo 1589493 1788745 := bbase (se 2 (by rfl) ⟨670779, by rfl⟩ : syracuseStep 1788745 = 1341559) (by norm_num)
theorem B4025173 : Blo 1589493 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B2149205 : Blo 1589493 2149205 := bbase (se 9 (by rfl) ⟨6296, by rfl⟩ : syracuseStep 2149205 = 12593) (by norm_num)
theorem B1788781 : Blo 1589493 1788781 := bbase (se 3 (by rfl) ⟨335396, by rfl⟩ : syracuseStep 1788781 = 670793) (by norm_num)
theorem B1788817 : Blo 1589493 1788817 := bbase (se 2 (by rfl) ⟨670806, by rfl⟩ : syracuseStep 1788817 = 1341613) (by norm_num)
theorem B1788853 : Blo 1589493 1788853 := bbase (se 5 (by rfl) ⟨83852, by rfl⟩ : syracuseStep 1788853 = 167705) (by norm_num)
theorem B4025285 : Blo 1589493 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B1788889 : Blo 1589493 1788889 := bbase (se 2 (by rfl) ⟨670833, by rfl⟩ : syracuseStep 1788889 = 1341667) (by norm_num)
theorem B1788925 : Blo 1589493 1788925 := bbase (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) (by norm_num)
theorem B2264069 : Blo 1589493 2264069 := bbase (se 4 (by rfl) ⟨212256, by rfl⟩ : syracuseStep 2264069 = 424513) (by norm_num)
theorem B3017749 : Blo 1589493 3017749 := bbase (se 6 (by rfl) ⟨70728, by rfl⟩ : syracuseStep 3017749 = 141457) (by norm_num)
theorem B10185749 : Blo 1589493 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B1788961 : Blo 1589493 1788961 := bbase (se 2 (by rfl) ⟨670860, by rfl⟩ : syracuseStep 1788961 = 1341721) (by norm_num)
theorem B1788997 : Blo 1589493 1788997 := bbase (se 4 (by rfl) ⟨167718, by rfl⟩ : syracuseStep 1788997 = 335437) (by norm_num)
theorem B15281237 : Blo 1589493 15281237 := bbase (se 8 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 15281237 = 179077) (by norm_num)
theorem B2264149 : Blo 1589493 2264149 := bbase (se 8 (by rfl) ⟨13266, by rfl⟩ : syracuseStep 2264149 = 26533) (by norm_num)
theorem B1789033 : Blo 1589493 1789033 := bbase (se 2 (by rfl) ⟨670887, by rfl⟩ : syracuseStep 1789033 = 1341775) (by norm_num)
theorem B5368949 : Blo 1589493 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B4025477 : Blo 1589493 4025477 := bbase (se 4 (by rfl) ⟨377388, by rfl⟩ : syracuseStep 4025477 = 754777) (by norm_num)
theorem B1789069 : Blo 1589493 1789069 := bbase (se 3 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 1789069 = 670901) (by norm_num)
theorem B3017893 : Blo 1589493 3017893 := bbase (se 4 (by rfl) ⟨282927, by rfl⟩ : syracuseStep 3017893 = 565855) (by norm_num)
theorem B1789105 : Blo 1589493 1789105 := bbase (se 2 (by rfl) ⟨670914, by rfl⟩ : syracuseStep 1789105 = 1341829) (by norm_num)
theorem B3820733 : Blo 1589493 3820733 := bbase (se 3 (by rfl) ⟨716387, by rfl⟩ : syracuseStep 3820733 = 1432775) (by norm_num)
theorem B5164229 : Blo 1589493 5164229 := bbase (se 4 (by rfl) ⟨484146, by rfl⟩ : syracuseStep 5164229 = 968293) (by norm_num)
theorem B2264269 : Blo 1589493 2264269 := bbase (se 3 (by rfl) ⟨424550, by rfl⟩ : syracuseStep 2264269 = 849101) (by norm_num)
theorem B1789141 : Blo 1589493 1789141 := bbase (se 7 (by rfl) ⟨20966, by rfl⟩ : syracuseStep 1789141 = 41933) (by norm_num)
theorem B1789177 : Blo 1589493 1789177 := bbase (se 2 (by rfl) ⟨670941, by rfl⟩ : syracuseStep 1789177 = 1341883) (by norm_num)
theorem B1813757 : Blo 1589493 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B1789213 : Blo 1589493 1789213 := bbase (se 3 (by rfl) ⟨335477, by rfl⟩ : syracuseStep 1789213 = 670955) (by norm_num)
theorem B2264365 : Blo 1589493 2264365 := bbase (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) (by norm_num)
theorem B1789249 : Blo 1589493 1789249 := bbase (se 2 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 1789249 = 1341937) (by norm_num)
theorem B3018053 : Blo 1589493 3018053 := bbase (se 4 (by rfl) ⟨282942, by rfl⟩ : syracuseStep 3018053 = 565885) (by norm_num)
theorem B1789285 : Blo 1589493 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B3820925 : Blo 1589493 3820925 := bbase (se 3 (by rfl) ⟨716423, by rfl⟩ : syracuseStep 3820925 = 1432847) (by norm_num)
theorem B1789321 : Blo 1589493 1789321 := bbase (se 2 (by rfl) ⟨670995, by rfl⟩ : syracuseStep 1789321 = 1341991) (by norm_num)
theorem B1789357 : Blo 1589493 1789357 := bbase (se 3 (by rfl) ⟨335504, by rfl⟩ : syracuseStep 1789357 = 671009) (by norm_num)
theorem B2682301 : Blo 1589493 2682301 := bbase (se 3 (by rfl) ⟨502931, by rfl⟩ : syracuseStep 2682301 = 1005863) (by norm_num)
theorem B1863109 : Blo 1589493 1863109 := bbase (se 4 (by rfl) ⟨174666, by rfl⟩ : syracuseStep 1863109 = 349333) (by norm_num)
theorem B1789393 : Blo 1589493 1789393 := bbase (se 2 (by rfl) ⟨671022, by rfl⟩ : syracuseStep 1789393 = 1342045) (by norm_num)
theorem B3018197 : Blo 1589493 3018197 := bbase (se 7 (by rfl) ⟨35369, by rfl⟩ : syracuseStep 3018197 = 70739) (by norm_num)
theorem B6049237 : Blo 1589493 6049237 := bbase (se 7 (by rfl) ⟨70889, by rfl⟩ : syracuseStep 6049237 = 141779) (by norm_num)
theorem B4025821 : Blo 1589493 4025821 := bbase (se 3 (by rfl) ⟨754841, by rfl⟩ : syracuseStep 4025821 = 1509683) (by norm_num)
theorem B1789429 : Blo 1589493 1789429 := bbase (se 5 (by rfl) ⟨83879, by rfl⟩ : syracuseStep 1789429 = 167759) (by norm_num)
theorem B2682389 : Blo 1589493 2682389 := bbase (se 6 (by rfl) ⟨62868, by rfl⟩ : syracuseStep 2682389 = 125737) (by norm_num)
theorem B1789465 : Blo 1589493 1789465 := bbase (se 2 (by rfl) ⟨671049, by rfl⟩ : syracuseStep 1789465 = 1342099) (by norm_num)
theorem B3059237 : Blo 1589493 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B5369381 : Blo 1589493 5369381 := bbase (se 4 (by rfl) ⟨503379, by rfl⟩ : syracuseStep 5369381 = 1006759) (by norm_num)
theorem B2068021 : Blo 1589493 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B1789501 : Blo 1589493 1789501 := bbase (se 3 (by rfl) ⟨335531, by rfl⟩ : syracuseStep 1789501 = 671063) (by norm_num)
theorem B4025933 : Blo 1589493 4025933 := bbase (se 3 (by rfl) ⟨754862, by rfl⟩ : syracuseStep 4025933 = 1509725) (by norm_num)
theorem B1789537 : Blo 1589493 1789537 := bbase (se 2 (by rfl) ⟨671076, by rfl⟩ : syracuseStep 1789537 = 1342153) (by norm_num)
theorem B1789573 : Blo 1589493 1789573 := bbase (se 4 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 1789573 = 335545) (by norm_num)
theorem B2682517 : Blo 1589493 2682517 := bbase (se 6 (by rfl) ⟨62871, by rfl⟩ : syracuseStep 2682517 = 125743) (by norm_num)
theorem B3821213 : Blo 1589493 3821213 := bbase (se 3 (by rfl) ⟨716477, by rfl⟩ : syracuseStep 3821213 = 1432955) (by norm_num)
theorem B1789609 : Blo 1589493 1789609 := bbase (se 2 (by rfl) ⟨671103, by rfl⟩ : syracuseStep 1789609 = 1342207) (by norm_num)
theorem B1789645 : Blo 1589493 1789645 := bbase (se 3 (by rfl) ⟨335558, by rfl⟩ : syracuseStep 1789645 = 671117) (by norm_num)
theorem B6123221 : Blo 1589493 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B2682605 : Blo 1589493 2682605 := bbase (se 3 (by rfl) ⟨502988, by rfl⟩ : syracuseStep 2682605 = 1005977) (by norm_num)
theorem B1789681 : Blo 1589493 1789681 := bbase (se 2 (by rfl) ⟨671130, by rfl⟩ : syracuseStep 1789681 = 1342261) (by norm_num)
theorem B3018485 : Blo 1589493 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B4026125 : Blo 1589493 4026125 := bbase (se 3 (by rfl) ⟨754898, by rfl⟩ : syracuseStep 4026125 = 1509797) (by norm_num)
theorem B1789717 : Blo 1589493 1789717 := bbase (se 6 (by rfl) ⟨41946, by rfl⟩ : syracuseStep 1789717 = 83893) (by norm_num)
theorem B2264861 : Blo 1589493 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B1789753 : Blo 1589493 1789753 := bbase (se 2 (by rfl) ⟨671157, by rfl⟩ : syracuseStep 1789753 = 1342315) (by norm_num)
theorem B1789789 : Blo 1589493 1789789 := bbase (se 3 (by rfl) ⟨335585, by rfl⟩ : syracuseStep 1789789 = 671171) (by norm_num)
theorem B2682733 : Blo 1589493 2682733 := bbase (se 3 (by rfl) ⟨503012, by rfl⟩ : syracuseStep 2682733 = 1006025) (by norm_num)
theorem B1789825 : Blo 1589493 1789825 := bbase (se 2 (by rfl) ⟨671184, by rfl⟩ : syracuseStep 1789825 = 1342369) (by norm_num)
theorem B3018637 : Blo 1589493 3018637 := bbase (se 3 (by rfl) ⟨565994, by rfl⟩ : syracuseStep 3018637 = 1131989) (by norm_num)
theorem B1789861 : Blo 1589493 1789861 := bbase (se 4 (by rfl) ⟨167799, by rfl⟩ : syracuseStep 1789861 = 335599) (by norm_num)
theorem B2682821 : Blo 1589493 2682821 := bbase (se 4 (by rfl) ⟨251514, by rfl⟩ : syracuseStep 2682821 = 503029) (by norm_num)
theorem B3395557 : Blo 1589493 3395557 := bbase (se 4 (by rfl) ⟨318333, by rfl⟩ : syracuseStep 3395557 = 636667) (by norm_num)
theorem B8048645 : Blo 1589493 8048645 := bbase (se 4 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 8048645 = 1509121) (by norm_num)
theorem B5451781 : Blo 1589493 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B2682949 : Blo 1589493 2682949 := bbase (se 4 (by rfl) ⟨251526, by rfl⟩ : syracuseStep 2682949 = 503053) (by norm_num)
theorem B3395677 : Blo 1589493 3395677 := bbase (se 3 (by rfl) ⟨636689, by rfl⟩ : syracuseStep 3395677 = 1273379) (by norm_num)
theorem B4026469 : Blo 1589493 4026469 := bbase (se 4 (by rfl) ⟨377481, by rfl⟩ : syracuseStep 4026469 = 754963) (by norm_num)
theorem B7639157 : Blo 1589493 7639157 := bbase (se 5 (by rfl) ⟨358085, by rfl⟩ : syracuseStep 7639157 = 716171) (by norm_num)
theorem B2683037 : Blo 1589493 2683037 := bbase (se 3 (by rfl) ⟨503069, by rfl⟩ : syracuseStep 2683037 = 1006139) (by norm_num)
theorem B3018941 : Blo 1589493 3018941 := bbase (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) (by norm_num)
theorem B4026581 : Blo 1589493 4026581 := bbase (se 7 (by rfl) ⟨47186, by rfl⟩ : syracuseStep 4026581 = 94373) (by norm_num)
theorem B2683165 : Blo 1589493 2683165 := bbase (se 3 (by rfl) ⟨503093, by rfl⟩ : syracuseStep 2683165 = 1006187) (by norm_num)
theorem B13070645 : Blo 1589493 13070645 := bbase (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) (by norm_num)
theorem B3395933 : Blo 1589493 3395933 := bbase (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) (by norm_num)
theorem B3625325 : Blo 1589493 3625325 := bbase (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) (by norm_num)
theorem B2683253 : Blo 1589493 2683253 := bbase (se 5 (by rfl) ⟨125777, by rfl⟩ : syracuseStep 2683253 = 251555) (by norm_num)
theorem B4026773 : Blo 1589493 4026773 := bbase (se 6 (by rfl) ⟨94377, by rfl⟩ : syracuseStep 4026773 = 188755) (by norm_num)
theorem B4837781 : Blo 1589493 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B2683381 : Blo 1589493 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B3576365 : Blo 1589493 3576365 := bbase (se 3 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 3576365 = 1341137) (by norm_num)
theorem B6795829 : Blo 1589493 6795829 := bbase (se 5 (by rfl) ⟨318554, by rfl⟩ : syracuseStep 6795829 = 637109) (by norm_num)
theorem B2683469 : Blo 1589493 2683469 := bbase (se 3 (by rfl) ⟨503150, by rfl⟩ : syracuseStep 2683469 = 1006301) (by norm_num)
theorem B3576437 : Blo 1589493 3576437 := bbase (se 5 (by rfl) ⟨167645, by rfl⟩ : syracuseStep 3576437 = 335291) (by norm_num)
theorem B2011817 : Blo 1589493 2011817 := bbase (se 2 (by rfl) ⟨754431, by rfl⟩ : syracuseStep 2011817 = 1508863) (by norm_num)
theorem B2618029 : Blo 1589493 2618029 := bbase (se 3 (by rfl) ⟨490880, by rfl⟩ : syracuseStep 2618029 = 981761) (by norm_num)
theorem B3576509 : Blo 1589493 3576509 := bbase (se 3 (by rfl) ⟨670595, by rfl⟩ : syracuseStep 3576509 = 1341191) (by norm_num)
theorem B2683597 : Blo 1589493 2683597 := bbase (se 3 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 2683597 = 1006349) (by norm_num)
theorem B2011873 : Blo 1589493 2011873 := bbase (se 2 (by rfl) ⟨754452, by rfl⟩ : syracuseStep 2011873 = 1508905) (by norm_num)
theorem B4027117 : Blo 1589493 4027117 := bbase (se 3 (by rfl) ⟨755084, by rfl⟩ : syracuseStep 4027117 = 1510169) (by norm_num)
theorem B3576581 : Blo 1589493 3576581 := bbase (se 4 (by rfl) ⟨335304, by rfl⟩ : syracuseStep 3576581 = 670609) (by norm_num)
theorem B2683685 : Blo 1589493 2683685 := bbase (se 4 (by rfl) ⟨251595, by rfl⟩ : syracuseStep 2683685 = 503191) (by norm_num)
theorem B2011969 : Blo 1589493 2011969 := bbase (se 2 (by rfl) ⟨754488, by rfl⟩ : syracuseStep 2011969 = 1508977) (by norm_num)
theorem B3576653 : Blo 1589493 3576653 := bbase (se 3 (by rfl) ⟨670622, by rfl⟩ : syracuseStep 3576653 = 1341245) (by norm_num)
theorem B3576725 : Blo 1589493 3576725 := bbase (se 6 (by rfl) ⟨83829, by rfl⟩ : syracuseStep 3576725 = 167659) (by norm_num)
theorem B2683813 : Blo 1589493 2683813 := bbase (se 4 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 2683813 = 503215) (by norm_num)
theorem B3019693 : Blo 1589493 3019693 := bbase (se 3 (by rfl) ⟨566192, by rfl⟩ : syracuseStep 3019693 = 1132385) (by norm_num)
theorem B3576797 : Blo 1589493 3576797 := bbase (se 3 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 3576797 = 1341299) (by norm_num)
theorem B2012141 : Blo 1589493 2012141 := bbase (se 3 (by rfl) ⟨377276, by rfl⟩ : syracuseStep 2012141 = 754553) (by norm_num)
theorem B2683901 : Blo 1589493 2683901 := bbase (se 3 (by rfl) ⟨503231, by rfl⟩ : syracuseStep 2683901 = 1006463) (by norm_num)
theorem B11457557 : Blo 1589493 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B3576869 : Blo 1589493 3576869 := bbase (se 4 (by rfl) ⟨335331, by rfl⟩ : syracuseStep 3576869 = 670663) (by norm_num)
theorem B2012197 : Blo 1589493 2012197 := bbase (se 4 (by rfl) ⟨188643, by rfl⟩ : syracuseStep 2012197 = 377287) (by norm_num)
theorem B3019837 : Blo 1589493 3019837 := bbase (se 3 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 3019837 = 1132439) (by norm_num)
theorem B3576941 : Blo 1589493 3576941 := bbase (se 3 (by rfl) ⟨670676, by rfl⟩ : syracuseStep 3576941 = 1341353) (by norm_num)
theorem B2684029 : Blo 1589493 2684029 := bbase (se 3 (by rfl) ⟨503255, by rfl⟩ : syracuseStep 2684029 = 1006511) (by norm_num)
theorem B2012293 : Blo 1589493 2012293 := bbase (se 4 (by rfl) ⟨188652, by rfl⟩ : syracuseStep 2012293 = 377305) (by norm_num)
theorem B25801877 : Blo 1589493 25801877 := bbase (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) (by norm_num)
theorem B3577013 : Blo 1589493 3577013 := bbase (se 5 (by rfl) ⟨167672, by rfl⟩ : syracuseStep 3577013 = 335345) (by norm_num)
theorem B3396821 : Blo 1589493 3396821 := bbase (se 7 (by rfl) ⟨39806, by rfl⟩ : syracuseStep 3396821 = 79613) (by norm_num)
theorem B2684117 : Blo 1589493 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B3019997 : Blo 1589493 3019997 := bbase (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) (by norm_num)
theorem B3577085 : Blo 1589493 3577085 := bbase (se 3 (by rfl) ⟨670703, by rfl⟩ : syracuseStep 3577085 = 1341407) (by norm_num)
theorem B8049941 : Blo 1589493 8049941 := bbase (se 6 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 8049941 = 377341) (by norm_num)
theorem B2012465 : Blo 1589493 2012465 := bbase (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) (by norm_num)
theorem B3577157 : Blo 1589493 3577157 := bbase (se 4 (by rfl) ⟨335358, by rfl⟩ : syracuseStep 3577157 = 670717) (by norm_num)
theorem B2684245 : Blo 1589493 2684245 := bbase (se 13 (by rfl) ⟨491, by rfl⟩ : syracuseStep 2684245 = 983) (by norm_num)
theorem B2012521 : Blo 1589493 2012521 := bbase (se 2 (by rfl) ⟨754695, by rfl⟩ : syracuseStep 2012521 = 1509391) (by norm_num)
theorem B3020141 : Blo 1589493 3020141 := bbase (se 3 (by rfl) ⟨566276, by rfl⟩ : syracuseStep 3020141 = 1132553) (by norm_num)
theorem B12080501 : Blo 1589493 12080501 := bbase (se 5 (by rfl) ⟨566273, by rfl⟩ : syracuseStep 12080501 = 1132547) (by norm_num)
theorem B3577229 : Blo 1589493 3577229 := bbase (se 3 (by rfl) ⟨670730, by rfl⟩ : syracuseStep 3577229 = 1341461) (by norm_num)
theorem B2684333 : Blo 1589493 2684333 := bbase (se 3 (by rfl) ⟨503312, by rfl⟩ : syracuseStep 2684333 = 1006625) (by norm_num)
theorem B3061165 : Blo 1589493 3061165 := bbase (se 3 (by rfl) ⟨573968, by rfl⟩ : syracuseStep 3061165 = 1147937) (by norm_num)
theorem B3397061 : Blo 1589493 3397061 := bbase (se 4 (by rfl) ⟨318474, by rfl⟩ : syracuseStep 3397061 = 636949) (by norm_num)
theorem B2012617 : Blo 1589493 2012617 := bbase (se 2 (by rfl) ⟨754731, by rfl⟩ : syracuseStep 2012617 = 1509463) (by norm_num)
theorem B3577301 : Blo 1589493 3577301 := bbase (se 7 (by rfl) ⟨41921, by rfl⟩ : syracuseStep 3577301 = 83843) (by norm_num)
theorem B2864621 : Blo 1589493 2864621 := bbase (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) (by norm_num)
theorem B7640581 : Blo 1589493 7640581 := bbase (se 4 (by rfl) ⟨716304, by rfl⟩ : syracuseStep 7640581 = 1432609) (by norm_num)
theorem B3577373 : Blo 1589493 3577373 := bbase (se 3 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 3577373 = 1341515) (by norm_num)
theorem B5092901 : Blo 1589493 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B2684461 : Blo 1589493 2684461 := bbase (se 3 (by rfl) ⟨503336, by rfl⟩ : syracuseStep 2684461 = 1006673) (by norm_num)
theorem B1611353 : Blo 1589493 1611353 := bbase (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) (by norm_num)
theorem B3577445 : Blo 1589493 3577445 := bbase (se 4 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 3577445 = 670771) (by norm_num)
theorem B2012789 : Blo 1589493 2012789 := bbase (se 5 (by rfl) ⟨94349, by rfl⟩ : syracuseStep 2012789 = 188699) (by norm_num)
theorem B2684549 : Blo 1589493 2684549 := bbase (se 4 (by rfl) ⟨251676, by rfl⟩ : syracuseStep 2684549 = 503353) (by norm_num)
theorem B5232293 : Blo 1589493 5232293 := bbase (se 4 (by rfl) ⟨490527, by rfl⟩ : syracuseStep 5232293 = 981055) (by norm_num)
theorem B3577517 : Blo 1589493 3577517 := bbase (se 3 (by rfl) ⟨670784, by rfl⟩ : syracuseStep 3577517 = 1341569) (by norm_num)
theorem B2012845 : Blo 1589493 2012845 := bbase (se 3 (by rfl) ⟨377408, by rfl⟩ : syracuseStep 2012845 = 754817) (by norm_num)
theorem B5732021 : Blo 1589493 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B3577589 : Blo 1589493 3577589 := bbase (se 5 (by rfl) ⟨167699, by rfl⟩ : syracuseStep 3577589 = 335399) (by norm_num)
theorem B2684677 : Blo 1589493 2684677 := bbase (se 4 (by rfl) ⟨251688, by rfl⟩ : syracuseStep 2684677 = 503377) (by norm_num)
theorem B2012941 : Blo 1589493 2012941 := bbase (se 3 (by rfl) ⟨377426, by rfl⟩ : syracuseStep 2012941 = 754853) (by norm_num)
theorem B12072725 : Blo 1589493 12072725 := bbase (se 6 (by rfl) ⟨282954, by rfl⟩ : syracuseStep 12072725 = 565909) (by norm_num)
theorem B3577661 : Blo 1589493 3577661 := bbase (se 3 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 3577661 = 1341623) (by norm_num)
theorem B6035269 : Blo 1589493 6035269 := bbase (se 4 (by rfl) ⟨565806, by rfl⟩ : syracuseStep 6035269 = 1131613) (by norm_num)
theorem B53737301 : Blo 1589493 53737301 := bbase (se 9 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 53737301 = 314867) (by norm_num)
theorem B2684765 : Blo 1589493 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B3577733 : Blo 1589493 3577733 := bbase (se 4 (by rfl) ⟨335412, by rfl⟩ : syracuseStep 3577733 = 670825) (by norm_num)
theorem B2013113 : Blo 1589493 2013113 := bbase (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) (by norm_num)
theorem B3397565 : Blo 1589493 3397565 := bbase (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) (by norm_num)
theorem B3397573 : Blo 1589493 3397573 := bbase (se 4 (by rfl) ⟨318522, by rfl⟩ : syracuseStep 3397573 = 637045) (by norm_num)
theorem B3577805 : Blo 1589493 3577805 := bbase (se 3 (by rfl) ⟨670838, by rfl⟩ : syracuseStep 3577805 = 1341677) (by norm_num)
theorem B2013169 : Blo 1589493 2013169 := bbase (se 2 (by rfl) ⟨754938, by rfl⟩ : syracuseStep 2013169 = 1509877) (by norm_num)
theorem B3577877 : Blo 1589493 3577877 := bbase (se 6 (by rfl) ⟨83856, by rfl⟩ : syracuseStep 3577877 = 167713) (by norm_num)
theorem B2013265 : Blo 1589493 2013265 := bbase (se 2 (by rfl) ⟨754974, by rfl⟩ : syracuseStep 2013265 = 1509949) (by norm_num)
theorem B3577949 : Blo 1589493 3577949 := bbase (se 3 (by rfl) ⟨670865, by rfl⟩ : syracuseStep 3577949 = 1341731) (by norm_num)
theorem B6035573 : Blo 1589493 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B1702013 : Blo 1589493 1702013 := bbase (se 3 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 1702013 = 638255) (by norm_num)
theorem B15497365 : Blo 1589493 15497365 := bbase (se 6 (by rfl) ⟨363219, by rfl⟩ : syracuseStep 15497365 = 726439) (by norm_num)
theorem B1611937 : Blo 1589493 1611937 := bbase (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) (by norm_num)
theorem B3578021 : Blo 1589493 3578021 := bbase (se 4 (by rfl) ⟨335439, by rfl⟩ : syracuseStep 3578021 = 670879) (by norm_num)
theorem B3578093 : Blo 1589493 3578093 := bbase (se 3 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 3578093 = 1341785) (by norm_num)
theorem B2013437 : Blo 1589493 2013437 := bbase (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) (by norm_num)
theorem B3578165 : Blo 1589493 3578165 := bbase (se 5 (by rfl) ⟨167726, by rfl⟩ : syracuseStep 3578165 = 335453) (by norm_num)
theorem B2013493 : Blo 1589493 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B3578237 : Blo 1589493 3578237 := bbase (se 3 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 3578237 = 1341839) (by norm_num)
theorem B15276437 : Blo 1589493 15276437 := bbase (se 6 (by rfl) ⟨358041, by rfl⟩ : syracuseStep 15276437 = 716083) (by norm_num)
theorem B2013589 : Blo 1589493 2013589 := bbase (se 6 (by rfl) ⟨47193, by rfl⟩ : syracuseStep 2013589 = 94387) (by norm_num)
theorem B3578309 : Blo 1589493 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B4135373 : Blo 1589493 4135373 := bbase (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) (by norm_num)
theorem B3578381 : Blo 1589493 3578381 := bbase (se 3 (by rfl) ⟨670946, by rfl⟩ : syracuseStep 3578381 = 1341893) (by norm_num)
theorem B8051237 : Blo 1589493 8051237 := bbase (se 4 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 8051237 = 1509607) (by norm_num)
theorem B4192813 : Blo 1589493 4192813 := bbase (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) (by norm_num)
theorem B2546245 : Blo 1589493 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B3578453 : Blo 1589493 3578453 := bbase (se 8 (by rfl) ⟨20967, by rfl⟩ : syracuseStep 3578453 = 41935) (by norm_num)
theorem B4356709 : Blo 1589493 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B3578525 : Blo 1589493 3578525 := bbase (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) (by norm_num)
theorem B3578597 : Blo 1589493 3578597 := bbase (se 4 (by rfl) ⟨335493, by rfl⟩ : syracuseStep 3578597 = 670987) (by norm_num)
theorem B3578669 : Blo 1589493 3578669 := bbase (se 3 (by rfl) ⟨671000, by rfl⟩ : syracuseStep 3578669 = 1342001) (by norm_num)
theorem B3578741 : Blo 1589493 3578741 := bbase (se 5 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 3578741 = 335507) (by norm_num)
theorem B5364629 : Blo 1589493 5364629 := bbase (se 6 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 5364629 = 251467) (by norm_num)
theorem B3578813 : Blo 1589493 3578813 := bbase (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) (by norm_num)
theorem B2866141 : Blo 1589493 2866141 := bbase (se 3 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 2866141 = 1074803) (by norm_num)
theorem B4529141 : Blo 1589493 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B3578885 : Blo 1589493 3578885 := bbase (se 4 (by rfl) ⟨335520, by rfl⟩ : syracuseStep 3578885 = 671041) (by norm_num)
theorem B3578957 : Blo 1589493 3578957 := bbase (se 3 (by rfl) ⟨671054, by rfl⟩ : syracuseStep 3578957 = 1342109) (by norm_num)
theorem B3579029 : Blo 1589493 3579029 := bbase (se 6 (by rfl) ⟨83883, by rfl⟩ : syracuseStep 3579029 = 167767) (by norm_num)
theorem B4299925 : Blo 1589493 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B2546893 : Blo 1589493 2546893 := bbase (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) (by norm_num)
theorem B3579101 : Blo 1589493 3579101 := bbase (se 3 (by rfl) ⟨671081, by rfl⟩ : syracuseStep 3579101 = 1342163) (by norm_num)
theorem B3579173 : Blo 1589493 3579173 := bbase (se 4 (by rfl) ⟨335547, by rfl⟩ : syracuseStep 3579173 = 671095) (by norm_num)
theorem B5365061 : Blo 1589493 5365061 := bbase (se 4 (by rfl) ⟨502974, by rfl⟩ : syracuseStep 5365061 = 1005949) (by norm_num)
theorem B3579245 : Blo 1589493 3579245 := bbase (se 3 (by rfl) ⟨671108, by rfl⟩ : syracuseStep 3579245 = 1342217) (by norm_num)
theorem B3579317 : Blo 1589493 3579317 := bbase (se 5 (by rfl) ⟨167780, by rfl⟩ : syracuseStep 3579317 = 335561) (by norm_num)
theorem B3579389 : Blo 1589493 3579389 := bbase (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) (by norm_num)
theorem B3579461 : Blo 1589493 3579461 := bbase (se 4 (by rfl) ⟨335574, by rfl⟩ : syracuseStep 3579461 = 671149) (by norm_num)
theorem B3579533 : Blo 1589493 3579533 := bbase (se 3 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 3579533 = 1342325) (by norm_num)
theorem B3579605 : Blo 1589493 3579605 := bbase (se 7 (by rfl) ⟨41948, by rfl⟩ : syracuseStep 3579605 = 83897) (by norm_num)
theorem B5365493 : Blo 1589493 5365493 := bbase (se 5 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 5365493 = 503015) (by norm_num)
theorem B6446837 : Blo 1589493 6446837 := bbase (se 5 (by rfl) ⟨302195, by rfl⟩ : syracuseStep 6446837 = 604391) (by norm_num)
theorem B2866933 : Blo 1589493 2866933 := bbase (se 5 (by rfl) ⟨134387, by rfl⟩ : syracuseStep 2866933 = 268775) (by norm_num)
theorem B3579677 : Blo 1589493 3579677 := bbase (se 3 (by rfl) ⟨671189, by rfl⟩ : syracuseStep 3579677 = 1342379) (by norm_num)
theorem B8052533 : Blo 1589493 8052533 := bbase (se 5 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 8052533 = 754925) (by norm_num)
theorem B2547713 : Blo 1589493 2547713 := bstep (se 2 (by rfl) ⟨955392, by rfl⟩ : syracuseStep 2547713 = 1910785) B1910785
theorem B5365763 : Blo 1589493 5365763 := bstep (se 1 (by rfl) ⟨4024322, by rfl⟩ : syracuseStep 5365763 = 8048645) B8048645
theorem B6037517 : Blo 1589493 6037517 := bstep (se 3 (by rfl) ⟨1132034, by rfl⟩ : syracuseStep 6037517 = 2264069) B2264069
theorem B156844259 : Blo 1589493 156844259 := bstep (se 1 (by rfl) ⟨117633194, by rfl⟩ : syracuseStep 156844259 = 235266389) B235266389
theorem B2416883 : Blo 1589493 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B1589507 : Blo 1589493 1589507 := bstep (se 1 (by rfl) ⟨1192130, by rfl⟩ : syracuseStep 1589507 = 2384261) B2384261
theorem B5366033 : Blo 1589493 5366033 := bstep (se 2 (by rfl) ⟨2012262, by rfl⟩ : syracuseStep 5366033 = 4024525) B4024525
theorem B1589523 : Blo 1589493 1589523 := bstep (se 1 (by rfl) ⟨1192142, by rfl⟩ : syracuseStep 1589523 = 2384285) B2384285
theorem B1589539 : Blo 1589493 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B1589555 : Blo 1589493 1589555 := bstep (se 1 (by rfl) ⟨1192166, by rfl⟩ : syracuseStep 1589555 = 2384333) B2384333
theorem B1589571 : Blo 1589493 1589571 := bstep (se 1 (by rfl) ⟨1192178, by rfl⟩ : syracuseStep 1589571 = 2384357) B2384357
theorem B4538701 : Blo 1589493 4538701 := bstep (se 3 (by rfl) ⟨851006, by rfl⟩ : syracuseStep 4538701 = 1702013) B1702013
theorem B1589587 : Blo 1589493 1589587 := bstep (se 1 (by rfl) ⟨1192190, by rfl⟩ : syracuseStep 1589587 = 2384381) B2384381
theorem B1589603 : Blo 1589493 1589603 := bstep (se 1 (by rfl) ⟨1192202, by rfl⟩ : syracuseStep 1589603 = 2384405) B2384405
theorem B2384243 : Blo 1589493 2384243 := bstep (se 1 (by rfl) ⟨1788182, by rfl⟩ : syracuseStep 2384243 = 3576365) B3576365
theorem B1589619 : Blo 1589493 1589619 := bstep (se 1 (by rfl) ⟨1192214, by rfl⟩ : syracuseStep 1589619 = 2384429) B2384429
theorem B1589635 : Blo 1589493 1589635 := bstep (se 1 (by rfl) ⟨1192226, by rfl⟩ : syracuseStep 1589635 = 2384453) B2384453
theorem B2384273 : Blo 1589493 2384273 := bstep (se 2 (by rfl) ⟨894102, by rfl⟩ : syracuseStep 2384273 = 1788205) B1788205
theorem B1589651 : Blo 1589493 1589651 := bstep (se 1 (by rfl) ⟨1192238, by rfl⟩ : syracuseStep 1589651 = 2384477) B2384477
theorem B2384291 : Blo 1589493 2384291 := bstep (se 1 (by rfl) ⟨1788218, by rfl⟩ : syracuseStep 2384291 = 3576437) B3576437
theorem B1589667 : Blo 1589493 1589667 := bstep (se 1 (by rfl) ⟨1192250, by rfl⟩ : syracuseStep 1589667 = 2384501) B2384501
theorem B1589683 : Blo 1589493 1589683 := bstep (se 1 (by rfl) ⟨1192262, by rfl⟩ : syracuseStep 1589683 = 2384525) B2384525
theorem B2384321 : Blo 1589493 2384321 := bstep (se 2 (by rfl) ⟨894120, by rfl⟩ : syracuseStep 2384321 = 1788241) B1788241
theorem B1589699 : Blo 1589493 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B2384339 : Blo 1589493 2384339 := bstep (se 1 (by rfl) ⟨1788254, by rfl⟩ : syracuseStep 2384339 = 3576509) B3576509
theorem B1589715 : Blo 1589493 1589715 := bstep (se 1 (by rfl) ⟨1192286, by rfl⟩ : syracuseStep 1589715 = 2384573) B2384573
theorem B1589731 : Blo 1589493 1589731 := bstep (se 1 (by rfl) ⟨1192298, by rfl⟩ : syracuseStep 1589731 = 2384597) B2384597
theorem B2384369 : Blo 1589493 2384369 := bstep (se 2 (by rfl) ⟨894138, by rfl⟩ : syracuseStep 2384369 = 1788277) B1788277
theorem B1589747 : Blo 1589493 1589747 := bstep (se 1 (by rfl) ⟨1192310, by rfl⟩ : syracuseStep 1589747 = 2384621) B2384621
theorem B2384387 : Blo 1589493 2384387 := bstep (se 1 (by rfl) ⟨1788290, by rfl⟩ : syracuseStep 2384387 = 3576581) B3576581
theorem B1589763 : Blo 1589493 1589763 := bstep (se 1 (by rfl) ⟨1192322, by rfl⟩ : syracuseStep 1589763 = 2384645) B2384645
theorem B13771277 : Blo 1589493 13771277 := bstep (se 3 (by rfl) ⟨2582114, by rfl⟩ : syracuseStep 13771277 = 5164229) B5164229
theorem B1589779 : Blo 1589493 1589779 := bstep (se 1 (by rfl) ⟨1192334, by rfl⟩ : syracuseStep 1589779 = 2384669) B2384669
theorem B2384417 : Blo 1589493 2384417 := bstep (se 2 (by rfl) ⟨894156, by rfl⟩ : syracuseStep 2384417 = 1788313) B1788313
theorem B1589795 : Blo 1589493 1589795 := bstep (se 1 (by rfl) ⟨1192346, by rfl⟩ : syracuseStep 1589795 = 2384693) B2384693
theorem B2384435 : Blo 1589493 2384435 := bstep (se 1 (by rfl) ⟨1788326, by rfl⟩ : syracuseStep 2384435 = 3576653) B3576653
theorem B1589811 : Blo 1589493 1589811 := bstep (se 1 (by rfl) ⟨1192358, by rfl⟩ : syracuseStep 1589811 = 2384717) B2384717
theorem B1589827 : Blo 1589493 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B2384465 : Blo 1589493 2384465 := bstep (se 2 (by rfl) ⟨894174, by rfl⟩ : syracuseStep 2384465 = 1788349) B1788349
theorem B1589843 : Blo 1589493 1589843 := bstep (se 1 (by rfl) ⟨1192382, by rfl⟩ : syracuseStep 1589843 = 2384765) B2384765
theorem B2417249 : Blo 1589493 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B2384483 : Blo 1589493 2384483 := bstep (se 1 (by rfl) ⟨1788362, by rfl⟩ : syracuseStep 2384483 = 3576725) B3576725
theorem B1589859 : Blo 1589493 1589859 := bstep (se 1 (by rfl) ⟨1192394, by rfl⟩ : syracuseStep 1589859 = 2384789) B2384789
theorem B1589875 : Blo 1589493 1589875 := bstep (se 1 (by rfl) ⟨1192406, by rfl⟩ : syracuseStep 1589875 = 2384813) B2384813
theorem B2384513 : Blo 1589493 2384513 := bstep (se 2 (by rfl) ⟨894192, by rfl⟩ : syracuseStep 2384513 = 1788385) B1788385
theorem B1589891 : Blo 1589493 1589891 := bstep (se 1 (by rfl) ⟨1192418, by rfl⟩ : syracuseStep 1589891 = 2384837) B2384837
theorem B2384531 : Blo 1589493 2384531 := bstep (se 1 (by rfl) ⟨1788398, by rfl⟩ : syracuseStep 2384531 = 3576797) B3576797
theorem B1589907 : Blo 1589493 1589907 := bstep (se 1 (by rfl) ⟨1192430, by rfl⟩ : syracuseStep 1589907 = 2384861) B2384861
theorem B1589923 : Blo 1589493 1589923 := bstep (se 1 (by rfl) ⟨1192442, by rfl⟩ : syracuseStep 1589923 = 2384885) B2384885
theorem B2384561 : Blo 1589493 2384561 := bstep (se 2 (by rfl) ⟨894210, by rfl⟩ : syracuseStep 2384561 = 1788421) B1788421
theorem B1589939 : Blo 1589493 1589939 := bstep (se 1 (by rfl) ⟨1192454, by rfl⟩ : syracuseStep 1589939 = 2384909) B2384909
theorem B2384579 : Blo 1589493 2384579 := bstep (se 1 (by rfl) ⟨1788434, by rfl⟩ : syracuseStep 2384579 = 3576869) B3576869
theorem B1589955 : Blo 1589493 1589955 := bstep (se 1 (by rfl) ⟨1192466, by rfl⟩ : syracuseStep 1589955 = 2384933) B2384933
theorem B1589971 : Blo 1589493 1589971 := bstep (se 1 (by rfl) ⟨1192478, by rfl⟩ : syracuseStep 1589971 = 2384957) B2384957
theorem B2384609 : Blo 1589493 2384609 := bstep (se 2 (by rfl) ⟨894228, by rfl⟩ : syracuseStep 2384609 = 1788457) B1788457
theorem B1589987 : Blo 1589493 1589987 := bstep (se 1 (by rfl) ⟨1192490, by rfl⟩ : syracuseStep 1589987 = 2384981) B2384981
theorem B9061105 : Blo 1589493 9061105 := bstep (se 2 (by rfl) ⟨3397914, by rfl⟩ : syracuseStep 9061105 = 6795829) B6795829
theorem B2384627 : Blo 1589493 2384627 := bstep (se 1 (by rfl) ⟨1788470, by rfl⟩ : syracuseStep 2384627 = 3576941) B3576941
theorem B1590003 : Blo 1589493 1590003 := bstep (se 1 (by rfl) ⟨1192502, by rfl⟩ : syracuseStep 1590003 = 2385005) B2385005
theorem B1590019 : Blo 1589493 1590019 := bstep (se 1 (by rfl) ⟨1192514, by rfl⟩ : syracuseStep 1590019 = 2385029) B2385029
theorem B2384657 : Blo 1589493 2384657 := bstep (se 2 (by rfl) ⟨894246, by rfl⟩ : syracuseStep 2384657 = 1788493) B1788493
theorem B1590035 : Blo 1589493 1590035 := bstep (se 1 (by rfl) ⟨1192526, by rfl⟩ : syracuseStep 1590035 = 2385053) B2385053
theorem B2384675 : Blo 1589493 2384675 := bstep (se 1 (by rfl) ⟨1788506, by rfl⟩ : syracuseStep 2384675 = 3577013) B3577013
theorem B1590051 : Blo 1589493 1590051 := bstep (se 1 (by rfl) ⟨1192538, by rfl⟩ : syracuseStep 1590051 = 2385077) B2385077
theorem B5366573 : Blo 1589493 5366573 := bstep (se 3 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 5366573 = 2012465) B2012465
theorem B1590067 : Blo 1589493 1590067 := bstep (se 1 (by rfl) ⟨1192550, by rfl⟩ : syracuseStep 1590067 = 2385101) B2385101
theorem B2384705 : Blo 1589493 2384705 := bstep (se 2 (by rfl) ⟨894264, by rfl⟩ : syracuseStep 2384705 = 1788529) B1788529
theorem B1590083 : Blo 1589493 1590083 := bstep (se 1 (by rfl) ⟨1192562, by rfl⟩ : syracuseStep 1590083 = 2385125) B2385125
theorem B2384723 : Blo 1589493 2384723 := bstep (se 1 (by rfl) ⟨1788542, by rfl⟩ : syracuseStep 2384723 = 3577085) B3577085
theorem B1590099 : Blo 1589493 1590099 := bstep (se 1 (by rfl) ⟨1192574, by rfl⟩ : syracuseStep 1590099 = 2385149) B2385149
theorem B5366627 : Blo 1589493 5366627 := bstep (se 1 (by rfl) ⟨4024970, by rfl⟩ : syracuseStep 5366627 = 8049941) B8049941
theorem B1590115 : Blo 1589493 1590115 := bstep (se 1 (by rfl) ⟨1192586, by rfl⟩ : syracuseStep 1590115 = 2385173) B2385173
theorem B2384753 : Blo 1589493 2384753 := bstep (se 2 (by rfl) ⟨894282, by rfl⟩ : syracuseStep 2384753 = 1788565) B1788565
theorem B1590131 : Blo 1589493 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B2384771 : Blo 1589493 2384771 := bstep (se 1 (by rfl) ⟨1788578, by rfl⟩ : syracuseStep 2384771 = 3577157) B3577157
theorem B1590147 : Blo 1589493 1590147 := bstep (se 1 (by rfl) ⟨1192610, by rfl⟩ : syracuseStep 1590147 = 2385221) B2385221
theorem B3490705 : Blo 1589493 3490705 := bstep (se 2 (by rfl) ⟨1309014, by rfl⟩ : syracuseStep 3490705 = 2618029) B2618029
theorem B1590163 : Blo 1589493 1590163 := bstep (se 1 (by rfl) ⟨1192622, by rfl⟩ : syracuseStep 1590163 = 2385245) B2385245
theorem B2384801 : Blo 1589493 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B1590179 : Blo 1589493 1590179 := bstep (se 1 (by rfl) ⟨1192634, by rfl⟩ : syracuseStep 1590179 = 2385269) B2385269
theorem B8053667 : Blo 1589493 8053667 := bstep (se 1 (by rfl) ⟨6040250, by rfl⟩ : syracuseStep 8053667 = 12080501) B12080501
theorem B2384819 : Blo 1589493 2384819 := bstep (se 1 (by rfl) ⟨1788614, by rfl⟩ : syracuseStep 2384819 = 3577229) B3577229
theorem B1590195 : Blo 1589493 1590195 := bstep (se 1 (by rfl) ⟨1192646, by rfl⟩ : syracuseStep 1590195 = 2385293) B2385293
theorem B1590211 : Blo 1589493 1590211 := bstep (se 1 (by rfl) ⟨1192658, by rfl⟩ : syracuseStep 1590211 = 2385317) B2385317
theorem B2384849 : Blo 1589493 2384849 := bstep (se 2 (by rfl) ⟨894318, by rfl⟩ : syracuseStep 2384849 = 1788637) B1788637
theorem B1590227 : Blo 1589493 1590227 := bstep (se 1 (by rfl) ⟨1192670, by rfl⟩ : syracuseStep 1590227 = 2385341) B2385341
theorem B2384867 : Blo 1589493 2384867 := bstep (se 1 (by rfl) ⟨1788650, by rfl⟩ : syracuseStep 2384867 = 3577301) B3577301
theorem B1590243 : Blo 1589493 1590243 := bstep (se 1 (by rfl) ⟨1192682, by rfl⟩ : syracuseStep 1590243 = 2385365) B2385365
theorem B1909747 : Blo 1589493 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B1590259 : Blo 1589493 1590259 := bstep (se 1 (by rfl) ⟨1192694, by rfl⟩ : syracuseStep 1590259 = 2385389) B2385389
theorem B2384897 : Blo 1589493 2384897 := bstep (se 2 (by rfl) ⟨894336, by rfl⟩ : syracuseStep 2384897 = 1788673) B1788673
theorem B1590275 : Blo 1589493 1590275 := bstep (se 1 (by rfl) ⟨1192706, by rfl⟩ : syracuseStep 1590275 = 2385413) B2385413
theorem B2384915 : Blo 1589493 2384915 := bstep (se 1 (by rfl) ⟨1788686, by rfl⟩ : syracuseStep 2384915 = 3577373) B3577373
theorem B1590291 : Blo 1589493 1590291 := bstep (se 1 (by rfl) ⟨1192718, by rfl⟩ : syracuseStep 1590291 = 2385437) B2385437
theorem B1590307 : Blo 1589493 1590307 := bstep (se 1 (by rfl) ⟨1192730, by rfl⟩ : syracuseStep 1590307 = 2385461) B2385461
theorem B2384945 : Blo 1589493 2384945 := bstep (se 2 (by rfl) ⟨894354, by rfl⟩ : syracuseStep 2384945 = 1788709) B1788709
theorem B1590323 : Blo 1589493 1590323 := bstep (se 1 (by rfl) ⟨1192742, by rfl⟩ : syracuseStep 1590323 = 2385485) B2385485
theorem B2384963 : Blo 1589493 2384963 := bstep (se 1 (by rfl) ⟨1788722, by rfl⟩ : syracuseStep 2384963 = 3577445) B3577445
theorem B1590339 : Blo 1589493 1590339 := bstep (se 1 (by rfl) ⟨1192754, by rfl⟩ : syracuseStep 1590339 = 2385509) B2385509
theorem B1590355 : Blo 1589493 1590355 := bstep (se 1 (by rfl) ⟨1192766, by rfl⟩ : syracuseStep 1590355 = 2385533) B2385533
theorem B2384993 : Blo 1589493 2384993 := bstep (se 2 (by rfl) ⟨894372, by rfl⟩ : syracuseStep 2384993 = 1788745) B1788745
theorem B18105443 : Blo 1589493 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B1590371 : Blo 1589493 1590371 := bstep (se 1 (by rfl) ⟨1192778, by rfl⟩ : syracuseStep 1590371 = 2385557) B2385557
theorem B5366897 : Blo 1589493 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B2385011 : Blo 1589493 2385011 := bstep (se 1 (by rfl) ⟨1788758, by rfl⟩ : syracuseStep 2385011 = 3577517) B3577517
theorem B1590387 : Blo 1589493 1590387 := bstep (se 1 (by rfl) ⟨1192790, by rfl⟩ : syracuseStep 1590387 = 2385581) B2385581
theorem B1590403 : Blo 1589493 1590403 := bstep (se 1 (by rfl) ⟨1192802, by rfl⟩ : syracuseStep 1590403 = 2385605) B2385605
theorem B2385041 : Blo 1589493 2385041 := bstep (se 2 (by rfl) ⟨894390, by rfl⟩ : syracuseStep 2385041 = 1788781) B1788781
theorem B1590419 : Blo 1589493 1590419 := bstep (se 1 (by rfl) ⟨1192814, by rfl⟩ : syracuseStep 1590419 = 2385629) B2385629
theorem B2385059 : Blo 1589493 2385059 := bstep (se 1 (by rfl) ⟨1788794, by rfl⟩ : syracuseStep 2385059 = 3577589) B3577589
theorem B1590435 : Blo 1589493 1590435 := bstep (se 1 (by rfl) ⟨1192826, by rfl⟩ : syracuseStep 1590435 = 2385653) B2385653
theorem B1590451 : Blo 1589493 1590451 := bstep (se 1 (by rfl) ⟨1192838, by rfl⟩ : syracuseStep 1590451 = 2385677) B2385677
theorem B2385089 : Blo 1589493 2385089 := bstep (se 2 (by rfl) ⟨894408, by rfl⟩ : syracuseStep 2385089 = 1788817) B1788817
theorem B1590467 : Blo 1589493 1590467 := bstep (se 1 (by rfl) ⟨1192850, by rfl⟩ : syracuseStep 1590467 = 2385701) B2385701
theorem B2385107 : Blo 1589493 2385107 := bstep (se 1 (by rfl) ⟨1788830, by rfl⟩ : syracuseStep 2385107 = 3577661) B3577661
theorem B1590483 : Blo 1589493 1590483 := bstep (se 1 (by rfl) ⟨1192862, by rfl⟩ : syracuseStep 1590483 = 2385725) B2385725
theorem B1590499 : Blo 1589493 1590499 := bstep (se 1 (by rfl) ⟨1192874, by rfl⟩ : syracuseStep 1590499 = 2385749) B2385749
theorem B2385137 : Blo 1589493 2385137 := bstep (se 2 (by rfl) ⟨894426, by rfl⟩ : syracuseStep 2385137 = 1788853) B1788853
theorem B1590515 : Blo 1589493 1590515 := bstep (se 1 (by rfl) ⟨1192886, by rfl⟩ : syracuseStep 1590515 = 2385773) B2385773
theorem B2385155 : Blo 1589493 2385155 := bstep (se 1 (by rfl) ⟨1788866, by rfl⟩ : syracuseStep 2385155 = 3577733) B3577733
theorem B1590531 : Blo 1589493 1590531 := bstep (se 1 (by rfl) ⟨1192898, by rfl⟩ : syracuseStep 1590531 = 2385797) B2385797
theorem B1590547 : Blo 1589493 1590547 := bstep (se 1 (by rfl) ⟨1192910, by rfl⟩ : syracuseStep 1590547 = 2385821) B2385821
theorem B2385185 : Blo 1589493 2385185 := bstep (se 2 (by rfl) ⟨894444, by rfl⟩ : syracuseStep 2385185 = 1788889) B1788889
theorem B1590563 : Blo 1589493 1590563 := bstep (se 1 (by rfl) ⟨1192922, by rfl⟩ : syracuseStep 1590563 = 2385845) B2385845
theorem B2385203 : Blo 1589493 2385203 := bstep (se 1 (by rfl) ⟨1788902, by rfl⟩ : syracuseStep 2385203 = 3577805) B3577805
theorem B1590579 : Blo 1589493 1590579 := bstep (se 1 (by rfl) ⟨1192934, by rfl⟩ : syracuseStep 1590579 = 2385869) B2385869
theorem B1590595 : Blo 1589493 1590595 := bstep (se 1 (by rfl) ⟨1192946, by rfl⟩ : syracuseStep 1590595 = 2385893) B2385893
theorem B2385233 : Blo 1589493 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B1721683 : Blo 1589493 1721683 := bstep (se 1 (by rfl) ⟨1291262, by rfl⟩ : syracuseStep 1721683 = 2582525) B2582525
theorem B1590611 : Blo 1589493 1590611 := bstep (se 1 (by rfl) ⟨1192958, by rfl⟩ : syracuseStep 1590611 = 2385917) B2385917
theorem B2385251 : Blo 1589493 2385251 := bstep (se 1 (by rfl) ⟨1788938, by rfl⟩ : syracuseStep 2385251 = 3577877) B3577877
theorem B1590627 : Blo 1589493 1590627 := bstep (se 1 (by rfl) ⟨1192970, by rfl⟩ : syracuseStep 1590627 = 2385941) B2385941
theorem B4023665 : Blo 1589493 4023665 := bstep (se 2 (by rfl) ⟨1508874, by rfl⟩ : syracuseStep 4023665 = 3017749) B3017749
theorem B1590643 : Blo 1589493 1590643 := bstep (se 1 (by rfl) ⟨1192982, by rfl⟩ : syracuseStep 1590643 = 2385965) B2385965
theorem B2385281 : Blo 1589493 2385281 := bstep (se 2 (by rfl) ⟨894480, by rfl⟩ : syracuseStep 2385281 = 1788961) B1788961
theorem B1590659 : Blo 1589493 1590659 := bstep (se 1 (by rfl) ⟨1192994, by rfl⟩ : syracuseStep 1590659 = 2385989) B2385989
theorem B2385299 : Blo 1589493 2385299 := bstep (se 1 (by rfl) ⟨1788974, by rfl⟩ : syracuseStep 2385299 = 3577949) B3577949
theorem B1590675 : Blo 1589493 1590675 := bstep (se 1 (by rfl) ⟨1193006, by rfl⟩ : syracuseStep 1590675 = 2386013) B2386013
theorem B4023715 : Blo 1589493 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B1590691 : Blo 1589493 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B2385329 : Blo 1589493 2385329 := bstep (se 2 (by rfl) ⟨894498, by rfl⟩ : syracuseStep 2385329 = 1788997) B1788997
theorem B1590707 : Blo 1589493 1590707 := bstep (se 1 (by rfl) ⟨1193030, by rfl⟩ : syracuseStep 1590707 = 2386061) B2386061
theorem B2385347 : Blo 1589493 2385347 := bstep (se 1 (by rfl) ⟨1789010, by rfl⟩ : syracuseStep 2385347 = 3578021) B3578021
theorem B1590723 : Blo 1589493 1590723 := bstep (se 1 (by rfl) ⟨1193042, by rfl⟩ : syracuseStep 1590723 = 2386085) B2386085
theorem B1590739 : Blo 1589493 1590739 := bstep (se 1 (by rfl) ⟨1193054, by rfl⟩ : syracuseStep 1590739 = 2386109) B2386109
theorem B2385377 : Blo 1589493 2385377 := bstep (se 2 (by rfl) ⟨894516, by rfl⟩ : syracuseStep 2385377 = 1789033) B1789033
theorem B1590755 : Blo 1589493 1590755 := bstep (se 1 (by rfl) ⟨1193066, by rfl⟩ : syracuseStep 1590755 = 2386133) B2386133
theorem B2385395 : Blo 1589493 2385395 := bstep (se 1 (by rfl) ⟨1789046, by rfl⟩ : syracuseStep 2385395 = 3578093) B3578093
theorem B1590771 : Blo 1589493 1590771 := bstep (se 1 (by rfl) ⟨1193078, by rfl⟩ : syracuseStep 1590771 = 2386157) B2386157
theorem B1590787 : Blo 1589493 1590787 := bstep (se 1 (by rfl) ⟨1193090, by rfl⟩ : syracuseStep 1590787 = 2386181) B2386181
theorem B2385425 : Blo 1589493 2385425 := bstep (se 2 (by rfl) ⟨894534, by rfl⟩ : syracuseStep 2385425 = 1789069) B1789069
theorem B1590803 : Blo 1589493 1590803 := bstep (se 1 (by rfl) ⟨1193102, by rfl⟩ : syracuseStep 1590803 = 2386205) B2386205
theorem B2385443 : Blo 1589493 2385443 := bstep (se 1 (by rfl) ⟨1789082, by rfl⟩ : syracuseStep 2385443 = 3578165) B3578165
theorem B1590819 : Blo 1589493 1590819 := bstep (se 1 (by rfl) ⟨1193114, by rfl⟩ : syracuseStep 1590819 = 2386229) B2386229
theorem B4023857 : Blo 1589493 4023857 := bstep (se 2 (by rfl) ⟨1508946, by rfl⟩ : syracuseStep 4023857 = 3017893) B3017893
theorem B1590835 : Blo 1589493 1590835 := bstep (se 1 (by rfl) ⟨1193126, by rfl⟩ : syracuseStep 1590835 = 2386253) B2386253
theorem B2385473 : Blo 1589493 2385473 := bstep (se 2 (by rfl) ⟨894552, by rfl⟩ : syracuseStep 2385473 = 1789105) B1789105
theorem B1590851 : Blo 1589493 1590851 := bstep (se 1 (by rfl) ⟨1193138, by rfl⟩ : syracuseStep 1590851 = 2386277) B2386277
theorem B12076613 : Blo 1589493 12076613 := bstep (se 4 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 12076613 = 2264365) B2264365
theorem B2385491 : Blo 1589493 2385491 := bstep (se 1 (by rfl) ⟨1789118, by rfl⟩ : syracuseStep 2385491 = 3578237) B3578237
theorem B1590867 : Blo 1589493 1590867 := bstep (se 1 (by rfl) ⟨1193150, by rfl⟩ : syracuseStep 1590867 = 2386301) B2386301
theorem B10184291 : Blo 1589493 10184291 := bstep (se 1 (by rfl) ⟨7638218, by rfl⟩ : syracuseStep 10184291 = 15276437) B15276437
theorem B1590883 : Blo 1589493 1590883 := bstep (se 1 (by rfl) ⟨1193162, by rfl⟩ : syracuseStep 1590883 = 2386325) B2386325
theorem B2385521 : Blo 1589493 2385521 := bstep (se 2 (by rfl) ⟨894570, by rfl⟩ : syracuseStep 2385521 = 1789141) B1789141
theorem B1590899 : Blo 1589493 1590899 := bstep (se 1 (by rfl) ⟨1193174, by rfl⟩ : syracuseStep 1590899 = 2386349) B2386349
theorem B2385539 : Blo 1589493 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B4081283 : Blo 1589493 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B1590915 : Blo 1589493 1590915 := bstep (se 1 (by rfl) ⟨1193186, by rfl⟩ : syracuseStep 1590915 = 2386373) B2386373
theorem B5367437 : Blo 1589493 5367437 := bstep (se 3 (by rfl) ⟨1006394, by rfl⟩ : syracuseStep 5367437 = 2012789) B2012789
theorem B1590931 : Blo 1589493 1590931 := bstep (se 1 (by rfl) ⟨1193198, by rfl⟩ : syracuseStep 1590931 = 2386397) B2386397
theorem B2385569 : Blo 1589493 2385569 := bstep (se 2 (by rfl) ⟨894588, by rfl⟩ : syracuseStep 2385569 = 1789177) B1789177
theorem B1590947 : Blo 1589493 1590947 := bstep (se 1 (by rfl) ⟨1193210, by rfl⟩ : syracuseStep 1590947 = 2386421) B2386421
theorem B2385587 : Blo 1589493 2385587 := bstep (se 1 (by rfl) ⟨1789190, by rfl⟩ : syracuseStep 2385587 = 3578381) B3578381
theorem B1590963 : Blo 1589493 1590963 := bstep (se 1 (by rfl) ⟨1193222, by rfl⟩ : syracuseStep 1590963 = 2386445) B2386445
theorem B5367491 : Blo 1589493 5367491 := bstep (se 1 (by rfl) ⟨4025618, by rfl⟩ : syracuseStep 5367491 = 8051237) B8051237
theorem B1590979 : Blo 1589493 1590979 := bstep (se 1 (by rfl) ⟨1193234, by rfl⟩ : syracuseStep 1590979 = 2386469) B2386469
theorem B2385617 : Blo 1589493 2385617 := bstep (se 2 (by rfl) ⟨894606, by rfl⟩ : syracuseStep 2385617 = 1789213) B1789213
theorem B2385635 : Blo 1589493 2385635 := bstep (se 1 (by rfl) ⟨1789226, by rfl⟩ : syracuseStep 2385635 = 3578453) B3578453
theorem B2385665 : Blo 1589493 2385665 := bstep (se 2 (by rfl) ⟨894624, by rfl⟩ : syracuseStep 2385665 = 1789249) B1789249
theorem B2385683 : Blo 1589493 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B8161073 : Blo 1589493 8161073 := bstep (se 2 (by rfl) ⟨3060402, by rfl⟩ : syracuseStep 8161073 = 6120805) B6120805
theorem B2385713 : Blo 1589493 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B2385731 : Blo 1589493 2385731 := bstep (se 1 (by rfl) ⟨1789298, by rfl⟩ : syracuseStep 2385731 = 3578597) B3578597
theorem B2385761 : Blo 1589493 2385761 := bstep (se 2 (by rfl) ⟨894660, by rfl⟩ : syracuseStep 2385761 = 1789321) B1789321
theorem B2385779 : Blo 1589493 2385779 := bstep (se 1 (by rfl) ⟨1789334, by rfl⟩ : syracuseStep 2385779 = 3578669) B3578669
theorem B2385809 : Blo 1589493 2385809 := bstep (se 2 (by rfl) ⟨894678, by rfl⟩ : syracuseStep 2385809 = 1789357) B1789357
theorem B4081553 : Blo 1589493 4081553 := bstep (se 2 (by rfl) ⟨1530582, by rfl⟩ : syracuseStep 4081553 = 3061165) B3061165
theorem B2385827 : Blo 1589493 2385827 := bstep (se 1 (by rfl) ⟨1789370, by rfl⟩ : syracuseStep 2385827 = 3578741) B3578741
theorem B2484145 : Blo 1589493 2484145 := bstep (se 2 (by rfl) ⟨931554, by rfl⟩ : syracuseStep 2484145 = 1863109) B1863109
theorem B2385857 : Blo 1589493 2385857 := bstep (se 2 (by rfl) ⟨894696, by rfl⟩ : syracuseStep 2385857 = 1789393) B1789393
theorem B5367761 : Blo 1589493 5367761 := bstep (se 2 (by rfl) ⟨2012910, by rfl⟩ : syracuseStep 5367761 = 4025821) B4025821
theorem B2385875 : Blo 1589493 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B2385905 : Blo 1589493 2385905 := bstep (se 2 (by rfl) ⟨894714, by rfl⟩ : syracuseStep 2385905 = 1789429) B1789429
theorem B2385923 : Blo 1589493 2385923 := bstep (se 1 (by rfl) ⟨1789442, by rfl⟩ : syracuseStep 2385923 = 3578885) B3578885
theorem B2385953 : Blo 1589493 2385953 := bstep (se 2 (by rfl) ⟨894732, by rfl⟩ : syracuseStep 2385953 = 1789465) B1789465
theorem B2385971 : Blo 1589493 2385971 := bstep (se 1 (by rfl) ⟨1789478, by rfl⟩ : syracuseStep 2385971 = 3578957) B3578957
theorem B6039629 : Blo 1589493 6039629 := bstep (se 3 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 6039629 = 2264861) B2264861
theorem B2386001 : Blo 1589493 2386001 := bstep (se 2 (by rfl) ⟨894750, by rfl⟩ : syracuseStep 2386001 = 1789501) B1789501
theorem B2386019 : Blo 1589493 2386019 := bstep (se 1 (by rfl) ⟨1789514, by rfl⟩ : syracuseStep 2386019 = 3579029) B3579029
theorem B26151025 : Blo 1589493 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B2386049 : Blo 1589493 2386049 := bstep (se 2 (by rfl) ⟨894768, by rfl⟩ : syracuseStep 2386049 = 1789537) B1789537
theorem B9054341 : Blo 1589493 9054341 := bstep (se 4 (by rfl) ⟨848844, by rfl⟩ : syracuseStep 9054341 = 1697689) B1697689
theorem B2386067 : Blo 1589493 2386067 := bstep (se 1 (by rfl) ⟨1789550, by rfl⟩ : syracuseStep 2386067 = 3579101) B3579101
theorem B2386097 : Blo 1589493 2386097 := bstep (se 2 (by rfl) ⟨894786, by rfl⟩ : syracuseStep 2386097 = 1789573) B1789573
theorem B2386115 : Blo 1589493 2386115 := bstep (se 1 (by rfl) ⟨1789586, by rfl⟩ : syracuseStep 2386115 = 3579173) B3579173
theorem B2263249 : Blo 1589493 2263249 := bstep (se 2 (by rfl) ⟨848718, by rfl⟩ : syracuseStep 2263249 = 1697437) B1697437
theorem B2386145 : Blo 1589493 2386145 := bstep (se 2 (by rfl) ⟨894804, by rfl⟩ : syracuseStep 2386145 = 1789609) B1789609
theorem B2386163 : Blo 1589493 2386163 := bstep (se 1 (by rfl) ⟨1789622, by rfl⟩ : syracuseStep 2386163 = 3579245) B3579245
theorem B2386193 : Blo 1589493 2386193 := bstep (se 2 (by rfl) ⟨894822, by rfl⟩ : syracuseStep 2386193 = 1789645) B1789645
theorem B2386211 : Blo 1589493 2386211 := bstep (se 1 (by rfl) ⟨1789658, by rfl⟩ : syracuseStep 2386211 = 3579317) B3579317
theorem B2386241 : Blo 1589493 2386241 := bstep (se 2 (by rfl) ⟨894840, by rfl⟩ : syracuseStep 2386241 = 1789681) B1789681
theorem B2386259 : Blo 1589493 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B1788259 : Blo 1589493 1788259 := bstep (se 1 (by rfl) ⟨1341194, by rfl⟩ : syracuseStep 1788259 = 2682389) B2682389
theorem B2386289 : Blo 1589493 2386289 := bstep (se 2 (by rfl) ⟨894858, by rfl⟩ : syracuseStep 2386289 = 1789717) B1789717
theorem B2386307 : Blo 1589493 2386307 := bstep (se 1 (by rfl) ⟨1789730, by rfl⟩ : syracuseStep 2386307 = 3579461) B3579461
theorem B2386337 : Blo 1589493 2386337 := bstep (se 2 (by rfl) ⟨894876, by rfl⟩ : syracuseStep 2386337 = 1789753) B1789753
theorem B8047025 : Blo 1589493 8047025 := bstep (se 2 (by rfl) ⟨3017634, by rfl⟩ : syracuseStep 8047025 = 6035269) B6035269
theorem B2386355 : Blo 1589493 2386355 := bstep (se 1 (by rfl) ⟨1789766, by rfl⟩ : syracuseStep 2386355 = 3579533) B3579533
theorem B2386385 : Blo 1589493 2386385 := bstep (se 2 (by rfl) ⟨894894, by rfl⟩ : syracuseStep 2386385 = 1789789) B1789789
theorem B2386403 : Blo 1589493 2386403 := bstep (se 1 (by rfl) ⟨1789802, by rfl⟩ : syracuseStep 2386403 = 3579605) B3579605
theorem B4082147 : Blo 1589493 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B5368301 : Blo 1589493 5368301 := bstep (se 3 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 5368301 = 2013113) B2013113
theorem B1788403 : Blo 1589493 1788403 := bstep (se 1 (by rfl) ⟨1341302, by rfl⟩ : syracuseStep 1788403 = 2682605) B2682605
theorem B2386433 : Blo 1589493 2386433 := bstep (se 2 (by rfl) ⟨894912, by rfl⟩ : syracuseStep 2386433 = 1789825) B1789825
theorem B4024849 : Blo 1589493 4024849 := bstep (se 2 (by rfl) ⟨1509318, by rfl⟩ : syracuseStep 4024849 = 3018637) B3018637
theorem B2386451 : Blo 1589493 2386451 := bstep (se 1 (by rfl) ⟨1789838, by rfl⟩ : syracuseStep 2386451 = 3579677) B3579677
theorem B5368355 : Blo 1589493 5368355 := bstep (se 1 (by rfl) ⟨4026266, by rfl⟩ : syracuseStep 5368355 = 8052533) B8052533
theorem B2386481 : Blo 1589493 2386481 := bstep (se 2 (by rfl) ⟨894930, by rfl⟩ : syracuseStep 2386481 = 1789861) B1789861
theorem B1788547 : Blo 1589493 1788547 := bstep (se 1 (by rfl) ⟨1341410, by rfl⟩ : syracuseStep 1788547 = 2682821) B2682821
theorem B7269041 : Blo 1589493 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B1788691 : Blo 1589493 1788691 := bstep (se 1 (by rfl) ⟨1341518, by rfl⟩ : syracuseStep 1788691 = 2683037) B2683037
theorem B4025123 : Blo 1589493 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B5368625 : Blo 1589493 5368625 := bstep (se 2 (by rfl) ⟨2013234, by rfl⟩ : syracuseStep 5368625 = 4026469) B4026469
theorem B20663153 : Blo 1589493 20663153 := bstep (se 2 (by rfl) ⟨7748682, by rfl⟩ : syracuseStep 20663153 = 15497365) B15497365
theorem B6040433 : Blo 1589493 6040433 := bstep (se 2 (by rfl) ⟨2265162, by rfl⟩ : syracuseStep 6040433 = 4530325) B4530325
theorem B2149249 : Blo 1589493 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B2263955 : Blo 1589493 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B1788835 : Blo 1589493 1788835 := bstep (se 1 (by rfl) ⟨1341626, by rfl⟩ : syracuseStep 1788835 = 2683253) B2683253
theorem B6794189 : Blo 1589493 6794189 := bstep (se 3 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 6794189 = 2547821) B2547821
theorem B4025315 : Blo 1589493 4025315 := bstep (se 1 (by rfl) ⟨3018986, by rfl⟩ : syracuseStep 4025315 = 6037973) B6037973
theorem B6794225 : Blo 1589493 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B1698851 : Blo 1589493 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B1788979 : Blo 1589493 1788979 := bstep (se 1 (by rfl) ⟨1341734, by rfl⟩ : syracuseStep 1788979 = 2683469) B2683469
theorem B1789123 : Blo 1589493 1789123 := bstep (se 1 (by rfl) ⟨1341842, by rfl⟩ : syracuseStep 1789123 = 2683685) B2683685
theorem B3017969 : Blo 1589493 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B4836685 : Blo 1589493 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B5369165 : Blo 1589493 5369165 := bstep (se 3 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 5369165 = 2013437) B2013437
theorem B1789267 : Blo 1589493 1789267 := bstep (se 1 (by rfl) ⟨1341950, by rfl⟩ : syracuseStep 1789267 = 2683901) B2683901
theorem B7638371 : Blo 1589493 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B5369219 : Blo 1589493 5369219 := bstep (se 1 (by rfl) ⟨4026914, by rfl⟩ : syracuseStep 5369219 = 8053829) B8053829
theorem B5590417 : Blo 1589493 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B1789411 : Blo 1589493 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B2682355 : Blo 1589493 2682355 := bstep (se 1 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 2682355 = 4023533) B4023533
theorem B2264593 : Blo 1589493 2264593 := bstep (se 2 (by rfl) ⟨849222, by rfl⟩ : syracuseStep 2264593 = 1698445) B1698445
theorem B22924853 : Blo 1589493 22924853 := bstep (se 5 (by rfl) ⟨1074602, by rfl⟩ : syracuseStep 22924853 = 2149205) B2149205
theorem B1789555 : Blo 1589493 1789555 := bstep (se 1 (by rfl) ⟨1342166, by rfl⟩ : syracuseStep 1789555 = 2684333) B2684333
theorem B2682497 : Blo 1589493 2682497 := bstep (se 2 (by rfl) ⟨1005936, by rfl⟩ : syracuseStep 2682497 = 2011873) B2011873
theorem B2264707 : Blo 1589493 2264707 := bstep (se 1 (by rfl) ⟨1698530, by rfl⟩ : syracuseStep 2264707 = 3397061) B3397061
theorem B5729933 : Blo 1589493 5729933 := bstep (se 3 (by rfl) ⟨1074362, by rfl⟩ : syracuseStep 5729933 = 2148725) B2148725
theorem B5369489 : Blo 1589493 5369489 := bstep (se 2 (by rfl) ⟨2013558, by rfl⟩ : syracuseStep 5369489 = 4027117) B4027117
theorem B3223217 : Blo 1589493 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B3395267 : Blo 1589493 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B2682625 : Blo 1589493 2682625 := bstep (se 2 (by rfl) ⟨1005984, by rfl⟩ : syracuseStep 2682625 = 2011969) B2011969
theorem B1789699 : Blo 1589493 1789699 := bstep (se 1 (by rfl) ⟨1342274, by rfl⟩ : syracuseStep 1789699 = 2684549) B2684549
theorem B2682659 : Blo 1589493 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B3821347 : Blo 1589493 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B8048483 : Blo 1589493 8048483 := bstep (se 1 (by rfl) ⟨6036362, by rfl⟩ : syracuseStep 8048483 = 12072725) B12072725
theorem B4026257 : Blo 1589493 4026257 := bstep (se 2 (by rfl) ⟨1509846, by rfl⟩ : syracuseStep 4026257 = 3019693) B3019693
theorem B1789843 : Blo 1589493 1789843 := bstep (se 1 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 1789843 = 2684765) B2684765
theorem B2682787 : Blo 1589493 2682787 := bstep (se 1 (by rfl) ⟨2012090, by rfl⟩ : syracuseStep 2682787 = 4024181) B4024181
theorem B4026307 : Blo 1589493 4026307 := bstep (se 1 (by rfl) ⟨3019730, by rfl⟩ : syracuseStep 4026307 = 6039461) B6039461
theorem B15290309 : Blo 1589493 15290309 := bstep (se 4 (by rfl) ⟨1433466, by rfl⟩ : syracuseStep 15290309 = 2866933) B2866933
theorem B3821521 : Blo 1589493 3821521 := bstep (se 2 (by rfl) ⟨1433070, by rfl⟩ : syracuseStep 3821521 = 2866141) B2866141
theorem B2682929 : Blo 1589493 2682929 := bstep (se 2 (by rfl) ⟨1006098, by rfl⟩ : syracuseStep 2682929 = 2012197) B2012197
theorem B4026449 : Blo 1589493 4026449 := bstep (se 2 (by rfl) ⟨1509918, by rfl⟩ : syracuseStep 4026449 = 3019837) B3019837
theorem B3018865 : Blo 1589493 3018865 := bstep (se 2 (by rfl) ⟨1132074, by rfl⟩ : syracuseStep 3018865 = 2264149) B2264149
theorem B2683057 : Blo 1589493 2683057 := bstep (se 2 (by rfl) ⟨1006146, by rfl⟩ : syracuseStep 2683057 = 2012293) B2012293
theorem B2683091 : Blo 1589493 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B4296941 : Blo 1589493 4296941 := bstep (se 3 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 4296941 = 1611353) B1611353
theorem B3395857 : Blo 1589493 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B3019025 : Blo 1589493 3019025 := bstep (se 2 (by rfl) ⟨1132134, by rfl⟩ : syracuseStep 3019025 = 2264269) B2264269
theorem B2756915 : Blo 1589493 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B2683219 : Blo 1589493 2683219 := bstep (se 1 (by rfl) ⟨2012414, by rfl⟩ : syracuseStep 2683219 = 4024829) B4024829
theorem B12071267 : Blo 1589493 12071267 := bstep (se 1 (by rfl) ⟨9053450, by rfl⟩ : syracuseStep 12071267 = 18106901) B18106901
theorem B2683361 : Blo 1589493 2683361 := bstep (se 2 (by rfl) ⟨1006260, by rfl⟩ : syracuseStep 2683361 = 2012521) B2012521
theorem B3576401 : Blo 1589493 3576401 := bstep (se 2 (by rfl) ⟨1341150, by rfl⟩ : syracuseStep 3576401 = 2682301) B2682301
theorem B2683489 : Blo 1589493 2683489 := bstep (se 2 (by rfl) ⟨1006308, by rfl⟩ : syracuseStep 2683489 = 2012617) B2012617
theorem B3576419 : Blo 1589493 3576419 := bstep (se 1 (by rfl) ⟨2682314, by rfl⟩ : syracuseStep 3576419 = 5364629) B5364629
theorem B8065649 : Blo 1589493 8065649 := bstep (se 2 (by rfl) ⟨3024618, by rfl⟩ : syracuseStep 8065649 = 6049237) B6049237
theorem B2683523 : Blo 1589493 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B8049293 : Blo 1589493 8049293 := bstep (se 3 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 8049293 = 3018485) B3018485
theorem B3019427 : Blo 1589493 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B10187441 : Blo 1589493 10187441 := bstep (se 2 (by rfl) ⟨3820290, by rfl⟩ : syracuseStep 10187441 = 7640581) B7640581
theorem B10187491 : Blo 1589493 10187491 := bstep (se 1 (by rfl) ⟨7640618, by rfl⟩ : syracuseStep 10187491 = 15281237) B15281237
theorem B2757361 : Blo 1589493 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B2683651 : Blo 1589493 2683651 := bstep (se 1 (by rfl) ⟨2012738, by rfl⟩ : syracuseStep 2683651 = 4025477) B4025477
theorem B92943125 : Blo 1589493 92943125 := bstep (se 6 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 92943125 = 4356709) B4356709
theorem B3576689 : Blo 1589493 3576689 := bstep (se 2 (by rfl) ⟨1341258, by rfl⟩ : syracuseStep 3576689 = 2682517) B2682517
theorem B3576707 : Blo 1589493 3576707 := bstep (se 1 (by rfl) ⟨2682530, by rfl⟩ : syracuseStep 3576707 = 5365061) B5365061
theorem B2012035 : Blo 1589493 2012035 := bstep (se 1 (by rfl) ⟨1509026, by rfl⟩ : syracuseStep 2012035 = 3018053) B3018053
theorem B143299469 : Blo 1589493 143299469 := bstep (se 3 (by rfl) ⟨26868650, by rfl⟩ : syracuseStep 143299469 = 53737301) B53737301
theorem B2683793 : Blo 1589493 2683793 := bstep (se 2 (by rfl) ⟨1006422, by rfl⟩ : syracuseStep 2683793 = 2012845) B2012845
theorem B2012131 : Blo 1589493 2012131 := bstep (se 1 (by rfl) ⟨1509098, by rfl⟩ : syracuseStep 2012131 = 3018197) B3018197
theorem B2683921 : Blo 1589493 2683921 := bstep (se 2 (by rfl) ⟨1006470, by rfl⟩ : syracuseStep 2683921 = 2012941) B2012941
theorem B2683955 : Blo 1589493 2683955 := bstep (se 1 (by rfl) ⟨2012966, by rfl⟩ : syracuseStep 2683955 = 4025933) B4025933
theorem B4527181 : Blo 1589493 4527181 := bstep (se 3 (by rfl) ⟨848846, by rfl⟩ : syracuseStep 4527181 = 1697693) B1697693
theorem B3576977 : Blo 1589493 3576977 := bstep (se 2 (by rfl) ⟨1341366, by rfl⟩ : syracuseStep 3576977 = 2682733) B2682733
theorem B3576995 : Blo 1589493 3576995 := bstep (se 1 (by rfl) ⟨2682746, by rfl⟩ : syracuseStep 3576995 = 5365493) B5365493
theorem B4297891 : Blo 1589493 4297891 := bstep (se 1 (by rfl) ⟨3223418, by rfl⟩ : syracuseStep 4297891 = 6446837) B6446837
theorem B2684083 : Blo 1589493 2684083 := bstep (se 1 (by rfl) ⟨2013062, by rfl⟩ : syracuseStep 2684083 = 4026125) B4026125
theorem B4527409 : Blo 1589493 4527409 := bstep (se 2 (by rfl) ⟨1697778, by rfl⟩ : syracuseStep 4527409 = 3395557) B3395557
theorem B2684225 : Blo 1589493 2684225 := bstep (se 2 (by rfl) ⟨1006584, by rfl⟩ : syracuseStep 2684225 = 2013169) B2013169
theorem B3577265 : Blo 1589493 3577265 := bstep (se 2 (by rfl) ⟨1341474, by rfl⟩ : syracuseStep 3577265 = 2682949) B2682949
theorem B2684353 : Blo 1589493 2684353 := bstep (se 2 (by rfl) ⟨1006632, by rfl⟩ : syracuseStep 2684353 = 2013265) B2013265
theorem B3577283 : Blo 1589493 3577283 := bstep (se 1 (by rfl) ⟨2682962, by rfl⟩ : syracuseStep 3577283 = 5365925) B5365925
theorem B4527569 : Blo 1589493 4527569 := bstep (se 2 (by rfl) ⟨1697838, by rfl⟩ : syracuseStep 4527569 = 3395677) B3395677
theorem B2012627 : Blo 1589493 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B2684387 : Blo 1589493 2684387 := bstep (se 1 (by rfl) ⟨2013290, by rfl⟩ : syracuseStep 2684387 = 4026581) B4026581
theorem B8713763 : Blo 1589493 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B3020323 : Blo 1589493 3020323 := bstep (se 1 (by rfl) ⟨2265242, by rfl⟩ : syracuseStep 3020323 = 4530485) B4530485
theorem B4527683 : Blo 1589493 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B2684515 : Blo 1589493 2684515 := bstep (se 1 (by rfl) ⟨2013386, by rfl⟩ : syracuseStep 2684515 = 4026773) B4026773
theorem B3225187 : Blo 1589493 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B20371085 : Blo 1589493 20371085 := bstep (se 3 (by rfl) ⟨3819578, by rfl⟩ : syracuseStep 20371085 = 7639157) B7639157
theorem B20649653 : Blo 1589493 20649653 := bstep (se 5 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 20649653 = 1935905) B1935905
theorem B13579973 : Blo 1589493 13579973 := bstep (se 4 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 13579973 = 2546245) B2546245
theorem B3577553 : Blo 1589493 3577553 := bstep (se 2 (by rfl) ⟨1341582, by rfl⟩ : syracuseStep 3577553 = 2683165) B2683165
theorem B3577571 : Blo 1589493 3577571 := bstep (se 1 (by rfl) ⟨2683178, by rfl⟩ : syracuseStep 3577571 = 5366357) B5366357
theorem B2684657 : Blo 1589493 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B2684785 : Blo 1589493 2684785 := bstep (se 2 (by rfl) ⟨1006794, by rfl⟩ : syracuseStep 2684785 = 2013589) B2013589
theorem B9058189 : Blo 1589493 9058189 := bstep (se 3 (by rfl) ⟨1698410, by rfl⟩ : syracuseStep 9058189 = 3396821) B3396821
theorem B25786309 : Blo 1589493 25786309 := bstep (se 4 (by rfl) ⟨2417466, by rfl⟩ : syracuseStep 25786309 = 4834933) B4834933
theorem B12900293 : Blo 1589493 12900293 := bstep (se 4 (by rfl) ⟨1209402, by rfl⟩ : syracuseStep 12900293 = 2418805) B2418805
theorem B3577841 : Blo 1589493 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B3577859 : Blo 1589493 3577859 := bstep (se 1 (by rfl) ⟨2683394, by rfl⟩ : syracuseStep 3577859 = 5366789) B5366789
theorem B17201251 : Blo 1589493 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B5093489 : Blo 1589493 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B2013331 : Blo 1589493 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B13588721 : Blo 1589493 13588721 := bstep (se 2 (by rfl) ⟨5095770, by rfl⟩ : syracuseStep 13588721 = 10191541) B10191541
theorem B2013427 : Blo 1589493 2013427 := bstep (se 1 (by rfl) ⟨1510070, by rfl⟩ : syracuseStep 2013427 = 3020141) B3020141
theorem B3578129 : Blo 1589493 3578129 := bstep (se 2 (by rfl) ⟨1341798, by rfl⟩ : syracuseStep 3578129 = 2683597) B2683597
theorem B3578147 : Blo 1589493 3578147 := bstep (se 1 (by rfl) ⟨2683610, by rfl⟩ : syracuseStep 3578147 = 5367221) B5367221
theorem B1612099 : Blo 1589493 1612099 := bstep (se 1 (by rfl) ⟨1209074, by rfl⟩ : syracuseStep 1612099 = 2418149) B2418149
theorem B11622797 : Blo 1589493 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B3488195 : Blo 1589493 3488195 := bstep (se 1 (by rfl) ⟨2616146, by rfl⟩ : syracuseStep 3488195 = 5232293) B5232293
theorem B4528685 : Blo 1589493 4528685 := bstep (se 3 (by rfl) ⟨849128, by rfl⟩ : syracuseStep 4528685 = 1698257) B1698257
theorem B3578417 : Blo 1589493 3578417 := bstep (se 2 (by rfl) ⟨1341906, by rfl⟩ : syracuseStep 3578417 = 2683813) B2683813
theorem B3578435 : Blo 1589493 3578435 := bstep (se 1 (by rfl) ⟨2683826, by rfl⟩ : syracuseStep 3578435 = 5367653) B5367653
theorem B5094029 : Blo 1589493 5094029 := bstep (se 3 (by rfl) ⟨955130, by rfl⟩ : syracuseStep 5094029 = 1910261) B1910261
theorem B4528867 : Blo 1589493 4528867 := bstep (se 1 (by rfl) ⟨3396650, by rfl⟩ : syracuseStep 4528867 = 6793301) B6793301
theorem B3578705 : Blo 1589493 3578705 := bstep (se 2 (by rfl) ⟨1342014, by rfl⟩ : syracuseStep 3578705 = 2684029) B2684029
theorem B3578723 : Blo 1589493 3578723 := bstep (se 1 (by rfl) ⟨2684042, by rfl⟩ : syracuseStep 3578723 = 5368085) B5368085
theorem B5733233 : Blo 1589493 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B4529027 : Blo 1589493 4529027 := bstep (se 1 (by rfl) ⟨3396770, by rfl⟩ : syracuseStep 4529027 = 6793541) B6793541
theorem B6888397 : Blo 1589493 6888397 := bstep (se 3 (by rfl) ⟨1291574, by rfl⟩ : syracuseStep 6888397 = 2583149) B2583149
theorem B6036515 : Blo 1589493 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B10189901 : Blo 1589493 10189901 := bstep (se 3 (by rfl) ⟨1910606, by rfl⟩ : syracuseStep 10189901 = 3821213) B3821213
theorem B5364845 : Blo 1589493 5364845 := bstep (se 3 (by rfl) ⟨1005908, by rfl⟩ : syracuseStep 5364845 = 2011817) B2011817
theorem B3578993 : Blo 1589493 3578993 := bstep (se 2 (by rfl) ⟨1342122, by rfl⟩ : syracuseStep 3578993 = 2684245) B2684245
theorem B3579011 : Blo 1589493 3579011 := bstep (se 1 (by rfl) ⟨2684258, by rfl⟩ : syracuseStep 3579011 = 5368517) B5368517
theorem B5364899 : Blo 1589493 5364899 := bstep (se 1 (by rfl) ⟨4023674, by rfl⟩ : syracuseStep 5364899 = 8047349) B8047349
theorem B6790499 : Blo 1589493 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B3579281 : Blo 1589493 3579281 := bstep (se 2 (by rfl) ⟨1342230, by rfl⟩ : syracuseStep 3579281 = 2684461) B2684461
theorem B3579299 : Blo 1589493 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B5365169 : Blo 1589493 5365169 := bstep (se 2 (by rfl) ⟨2011938, by rfl⟩ : syracuseStep 5365169 = 4023877) B4023877
theorem B2547155 : Blo 1589493 2547155 := bstep (se 1 (by rfl) ⟨1910366, by rfl⟩ : syracuseStep 2547155 = 3820733) B3820733
theorem B8052209 : Blo 1589493 8052209 := bstep (se 2 (by rfl) ⟨3019578, by rfl⟩ : syracuseStep 8052209 = 6039157) B6039157
theorem B2547283 : Blo 1589493 2547283 := bstep (se 1 (by rfl) ⟨1910462, by rfl⟩ : syracuseStep 2547283 = 3820925) B3820925
theorem B3579569 : Blo 1589493 3579569 := bstep (se 2 (by rfl) ⟨1342338, by rfl⟩ : syracuseStep 3579569 = 2684677) B2684677
theorem B2039491 : Blo 1589493 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B3579587 : Blo 1589493 3579587 := bstep (se 1 (by rfl) ⟨2684690, by rfl⟩ : syracuseStep 3579587 = 5369381) B5369381
theorem B2547425 : Blo 1589493 2547425 := bstep (se 2 (by rfl) ⟨955284, by rfl⟩ : syracuseStep 2547425 = 1910569) B1910569
theorem B9060173 : Blo 1589493 9060173 := bstep (se 3 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 9060173 = 3397565) B3397565
theorem B4530097 : Blo 1589493 4530097 := bstep (se 2 (by rfl) ⟨1698786, by rfl⟩ : syracuseStep 4530097 = 3397573) B3397573
theorem B5365709 : Blo 1589493 5365709 := bstep (se 3 (by rfl) ⟨1006070, by rfl⟩ : syracuseStep 5365709 = 2012141) B2012141
theorem B4530269 : Blo 1589493 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B104562839 : Blo 1589493 104562839 := bstep (se 1 (by rfl) ⟨78422129, by rfl⟩ : syracuseStep 104562839 = 156844259) B156844259
theorem B1589495 : Blo 1589493 1589495 := bstep (se 1 (by rfl) ⟨1192121, by rfl⟩ : syracuseStep 1589495 = 2384243) B2384243
theorem B1589515 : Blo 1589493 1589515 := bstep (se 1 (by rfl) ⟨1192136, by rfl⟩ : syracuseStep 1589515 = 2384273) B2384273
theorem B1589527 : Blo 1589493 1589527 := bstep (se 1 (by rfl) ⟨1192145, by rfl⟩ : syracuseStep 1589527 = 2384291) B2384291
theorem B1589547 : Blo 1589493 1589547 := bstep (se 1 (by rfl) ⟨1192160, by rfl⟩ : syracuseStep 1589547 = 2384321) B2384321
theorem B13582637 : Blo 1589493 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B1589559 : Blo 1589493 1589559 := bstep (se 1 (by rfl) ⟨1192169, by rfl⟩ : syracuseStep 1589559 = 2384339) B2384339
theorem B1589579 : Blo 1589493 1589579 := bstep (se 1 (by rfl) ⟨1192184, by rfl⟩ : syracuseStep 1589579 = 2384369) B2384369
theorem B1589591 : Blo 1589493 1589591 := bstep (se 1 (by rfl) ⟨1192193, by rfl⟩ : syracuseStep 1589591 = 2384387) B2384387
theorem B1589611 : Blo 1589493 1589611 := bstep (se 1 (by rfl) ⟨1192208, by rfl⟩ : syracuseStep 1589611 = 2384417) B2384417
theorem B1589623 : Blo 1589493 1589623 := bstep (se 1 (by rfl) ⟨1192217, by rfl⟩ : syracuseStep 1589623 = 2384435) B2384435
theorem B2384267 : Blo 1589493 2384267 := bstep (se 1 (by rfl) ⟨1788200, by rfl⟩ : syracuseStep 2384267 = 3576401) B3576401
theorem B1589643 : Blo 1589493 1589643 := bstep (se 1 (by rfl) ⟨1192232, by rfl⟩ : syracuseStep 1589643 = 2384465) B2384465
theorem B2384279 : Blo 1589493 2384279 := bstep (se 1 (by rfl) ⟨1788209, by rfl⟩ : syracuseStep 2384279 = 3576419) B3576419
theorem B1589655 : Blo 1589493 1589655 := bstep (se 1 (by rfl) ⟨1192241, by rfl⟩ : syracuseStep 1589655 = 2384483) B2384483
theorem B1589675 : Blo 1589493 1589675 := bstep (se 1 (by rfl) ⟨1192256, by rfl⟩ : syracuseStep 1589675 = 2384513) B2384513
theorem B5366195 : Blo 1589493 5366195 := bstep (se 1 (by rfl) ⟨4024646, by rfl⟩ : syracuseStep 5366195 = 8049293) B8049293
theorem B1589687 : Blo 1589493 1589687 := bstep (se 1 (by rfl) ⟨1192265, by rfl⟩ : syracuseStep 1589687 = 2384531) B2384531
theorem B1589707 : Blo 1589493 1589707 := bstep (se 1 (by rfl) ⟨1192280, by rfl⟩ : syracuseStep 1589707 = 2384561) B2384561
theorem B6791627 : Blo 1589493 6791627 := bstep (se 1 (by rfl) ⟨5093720, by rfl⟩ : syracuseStep 6791627 = 10187441) B10187441
theorem B1589719 : Blo 1589493 1589719 := bstep (se 1 (by rfl) ⟨1192289, by rfl⟩ : syracuseStep 1589719 = 2384579) B2384579
theorem B2384345 : Blo 1589493 2384345 := bstep (se 2 (by rfl) ⟨894129, by rfl⟩ : syracuseStep 2384345 = 1788259) B1788259
theorem B1589739 : Blo 1589493 1589739 := bstep (se 1 (by rfl) ⟨1192304, by rfl⟩ : syracuseStep 1589739 = 2384609) B2384609
theorem B1589751 : Blo 1589493 1589751 := bstep (se 1 (by rfl) ⟨1192313, by rfl⟩ : syracuseStep 1589751 = 2384627) B2384627
theorem B1589771 : Blo 1589493 1589771 := bstep (se 1 (by rfl) ⟨1192328, by rfl⟩ : syracuseStep 1589771 = 2384657) B2384657
theorem B1589783 : Blo 1589493 1589783 := bstep (se 1 (by rfl) ⟨1192337, by rfl⟩ : syracuseStep 1589783 = 2384675) B2384675
theorem B1589803 : Blo 1589493 1589803 := bstep (se 1 (by rfl) ⟨1192352, by rfl⟩ : syracuseStep 1589803 = 2384705) B2384705
theorem B1589815 : Blo 1589493 1589815 := bstep (se 1 (by rfl) ⟨1192361, by rfl⟩ : syracuseStep 1589815 = 2384723) B2384723
theorem B2384459 : Blo 1589493 2384459 := bstep (se 1 (by rfl) ⟨1788344, by rfl⟩ : syracuseStep 2384459 = 3576689) B3576689
theorem B1589835 : Blo 1589493 1589835 := bstep (se 1 (by rfl) ⟨1192376, by rfl⟩ : syracuseStep 1589835 = 2384753) B2384753
theorem B2384471 : Blo 1589493 2384471 := bstep (se 1 (by rfl) ⟨1788353, by rfl⟩ : syracuseStep 2384471 = 3576707) B3576707
theorem B1589847 : Blo 1589493 1589847 := bstep (se 1 (by rfl) ⟨1192385, by rfl⟩ : syracuseStep 1589847 = 2384771) B2384771
theorem B1589867 : Blo 1589493 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B1589879 : Blo 1589493 1589879 := bstep (se 1 (by rfl) ⟨1192409, by rfl⟩ : syracuseStep 1589879 = 2384819) B2384819
theorem B1589899 : Blo 1589493 1589899 := bstep (se 1 (by rfl) ⟨1192424, by rfl⟩ : syracuseStep 1589899 = 2384849) B2384849
theorem B1589911 : Blo 1589493 1589911 := bstep (se 1 (by rfl) ⟨1192433, by rfl⟩ : syracuseStep 1589911 = 2384867) B2384867
theorem B2384537 : Blo 1589493 2384537 := bstep (se 2 (by rfl) ⟨894201, by rfl⟩ : syracuseStep 2384537 = 1788403) B1788403
theorem B1589931 : Blo 1589493 1589931 := bstep (se 1 (by rfl) ⟨1192448, by rfl⟩ : syracuseStep 1589931 = 2384897) B2384897
theorem B1589943 : Blo 1589493 1589943 := bstep (se 1 (by rfl) ⟨1192457, by rfl⟩ : syracuseStep 1589943 = 2384915) B2384915
theorem B5366465 : Blo 1589493 5366465 := bstep (se 2 (by rfl) ⟨2012424, by rfl⟩ : syracuseStep 5366465 = 4024849) B4024849
theorem B1589963 : Blo 1589493 1589963 := bstep (se 1 (by rfl) ⟨1192472, by rfl⟩ : syracuseStep 1589963 = 2384945) B2384945
theorem B1589975 : Blo 1589493 1589975 := bstep (se 1 (by rfl) ⟨1192481, by rfl⟩ : syracuseStep 1589975 = 2384963) B2384963
theorem B1589995 : Blo 1589493 1589995 := bstep (se 1 (by rfl) ⟨1192496, by rfl⟩ : syracuseStep 1589995 = 2384993) B2384993
theorem B1590007 : Blo 1589493 1590007 := bstep (se 1 (by rfl) ⟨1192505, by rfl⟩ : syracuseStep 1590007 = 2385011) B2385011
theorem B2384651 : Blo 1589493 2384651 := bstep (se 1 (by rfl) ⟨1788488, by rfl⟩ : syracuseStep 2384651 = 3576977) B3576977
theorem B1590027 : Blo 1589493 1590027 := bstep (se 1 (by rfl) ⟨1192520, by rfl⟩ : syracuseStep 1590027 = 2385041) B2385041
theorem B2384663 : Blo 1589493 2384663 := bstep (se 1 (by rfl) ⟨1788497, by rfl⟩ : syracuseStep 2384663 = 3576995) B3576995
theorem B1590039 : Blo 1589493 1590039 := bstep (se 1 (by rfl) ⟨1192529, by rfl⟩ : syracuseStep 1590039 = 2385059) B2385059
theorem B1590059 : Blo 1589493 1590059 := bstep (se 1 (by rfl) ⟨1192544, by rfl⟩ : syracuseStep 1590059 = 2385089) B2385089
theorem B1590071 : Blo 1589493 1590071 := bstep (se 1 (by rfl) ⟨1192553, by rfl⟩ : syracuseStep 1590071 = 2385107) B2385107
theorem B1590091 : Blo 1589493 1590091 := bstep (se 1 (by rfl) ⟨1192568, by rfl⟩ : syracuseStep 1590091 = 2385137) B2385137
theorem B1590103 : Blo 1589493 1590103 := bstep (se 1 (by rfl) ⟨1192577, by rfl⟩ : syracuseStep 1590103 = 2385155) B2385155
theorem B2384729 : Blo 1589493 2384729 := bstep (se 2 (by rfl) ⟨894273, by rfl⟩ : syracuseStep 2384729 = 1788547) B1788547
theorem B1590123 : Blo 1589493 1590123 := bstep (se 1 (by rfl) ⟨1192592, by rfl⟩ : syracuseStep 1590123 = 2385185) B2385185
theorem B1590135 : Blo 1589493 1590135 := bstep (se 1 (by rfl) ⟨1192601, by rfl⟩ : syracuseStep 1590135 = 2385203) B2385203
theorem B1590155 : Blo 1589493 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B1590167 : Blo 1589493 1590167 := bstep (se 1 (by rfl) ⟨1192625, by rfl⟩ : syracuseStep 1590167 = 2385251) B2385251
theorem B1590187 : Blo 1589493 1590187 := bstep (se 1 (by rfl) ⟨1192640, by rfl⟩ : syracuseStep 1590187 = 2385281) B2385281
theorem B1590199 : Blo 1589493 1590199 := bstep (se 1 (by rfl) ⟨1192649, by rfl⟩ : syracuseStep 1590199 = 2385299) B2385299
theorem B2384843 : Blo 1589493 2384843 := bstep (se 1 (by rfl) ⟨1788632, by rfl⟩ : syracuseStep 2384843 = 3577265) B3577265
theorem B1590219 : Blo 1589493 1590219 := bstep (se 1 (by rfl) ⟨1192664, by rfl⟩ : syracuseStep 1590219 = 2385329) B2385329
theorem B2384855 : Blo 1589493 2384855 := bstep (se 1 (by rfl) ⟨1788641, by rfl⟩ : syracuseStep 2384855 = 3577283) B3577283
theorem B1590231 : Blo 1589493 1590231 := bstep (se 1 (by rfl) ⟨1192673, by rfl⟩ : syracuseStep 1590231 = 2385347) B2385347
theorem B13583321 : Blo 1589493 13583321 := bstep (se 2 (by rfl) ⟨5093745, by rfl⟩ : syracuseStep 13583321 = 10187491) B10187491
theorem B6038489 : Blo 1589493 6038489 := bstep (se 2 (by rfl) ⟨2264433, by rfl⟩ : syracuseStep 6038489 = 4528867) B4528867
theorem B1590251 : Blo 1589493 1590251 := bstep (se 1 (by rfl) ⟨1192688, by rfl⟩ : syracuseStep 1590251 = 2385377) B2385377
theorem B1590263 : Blo 1589493 1590263 := bstep (se 1 (by rfl) ⟨1192697, by rfl⟩ : syracuseStep 1590263 = 2385395) B2385395
theorem B1590283 : Blo 1589493 1590283 := bstep (se 1 (by rfl) ⟨1192712, by rfl⟩ : syracuseStep 1590283 = 2385425) B2385425
theorem B5809175 : Blo 1589493 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B1590295 : Blo 1589493 1590295 := bstep (se 1 (by rfl) ⟨1192721, by rfl⟩ : syracuseStep 1590295 = 2385443) B2385443
theorem B2384921 : Blo 1589493 2384921 := bstep (se 2 (by rfl) ⟨894345, by rfl⟩ : syracuseStep 2384921 = 1788691) B1788691
theorem B1590315 : Blo 1589493 1590315 := bstep (se 1 (by rfl) ⟨1192736, by rfl⟩ : syracuseStep 1590315 = 2385473) B2385473
theorem B1590327 : Blo 1589493 1590327 := bstep (se 1 (by rfl) ⟨1192745, by rfl⟩ : syracuseStep 1590327 = 2385491) B2385491
theorem B1590347 : Blo 1589493 1590347 := bstep (se 1 (by rfl) ⟨1192760, by rfl⟩ : syracuseStep 1590347 = 2385521) B2385521
theorem B1590359 : Blo 1589493 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B2720855 : Blo 1589493 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B1590379 : Blo 1589493 1590379 := bstep (se 1 (by rfl) ⟨1192784, by rfl⟩ : syracuseStep 1590379 = 2385569) B2385569
theorem B1590391 : Blo 1589493 1590391 := bstep (se 1 (by rfl) ⟨1192793, by rfl⟩ : syracuseStep 1590391 = 2385587) B2385587
theorem B9053315 : Blo 1589493 9053315 := bstep (se 1 (by rfl) ⟨6789986, by rfl⟩ : syracuseStep 9053315 = 13579973) B13579973
theorem B2385035 : Blo 1589493 2385035 := bstep (se 1 (by rfl) ⟨1788776, by rfl⟩ : syracuseStep 2385035 = 3577553) B3577553
theorem B1590411 : Blo 1589493 1590411 := bstep (se 1 (by rfl) ⟨1192808, by rfl⟩ : syracuseStep 1590411 = 2385617) B2385617
theorem B2385047 : Blo 1589493 2385047 := bstep (se 1 (by rfl) ⟨1788785, by rfl⟩ : syracuseStep 2385047 = 3577571) B3577571
theorem B1590423 : Blo 1589493 1590423 := bstep (se 1 (by rfl) ⟨1192817, by rfl⟩ : syracuseStep 1590423 = 2385635) B2385635
theorem B1590443 : Blo 1589493 1590443 := bstep (se 1 (by rfl) ⟨1192832, by rfl⟩ : syracuseStep 1590443 = 2385665) B2385665
theorem B1590455 : Blo 1589493 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B4654273 : Blo 1589493 4654273 := bstep (se 2 (by rfl) ⟨1745352, by rfl⟩ : syracuseStep 4654273 = 3490705) B3490705
theorem B5440715 : Blo 1589493 5440715 := bstep (se 1 (by rfl) ⟨4080536, by rfl⟩ : syracuseStep 5440715 = 8161073) B8161073
theorem B1590475 : Blo 1589493 1590475 := bstep (se 1 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 1590475 = 2385713) B2385713
theorem B1590487 : Blo 1589493 1590487 := bstep (se 1 (by rfl) ⟨1192865, by rfl⟩ : syracuseStep 1590487 = 2385731) B2385731
theorem B2385113 : Blo 1589493 2385113 := bstep (se 2 (by rfl) ⟨894417, by rfl⟩ : syracuseStep 2385113 = 1788835) B1788835
theorem B5367005 : Blo 1589493 5367005 := bstep (se 3 (by rfl) ⟨1006313, by rfl⟩ : syracuseStep 5367005 = 2012627) B2012627
theorem B1590507 : Blo 1589493 1590507 := bstep (se 1 (by rfl) ⟨1192880, by rfl⟩ : syracuseStep 1590507 = 2385761) B2385761
theorem B1590519 : Blo 1589493 1590519 := bstep (se 1 (by rfl) ⟨1192889, by rfl⟩ : syracuseStep 1590519 = 2385779) B2385779
theorem B1590539 : Blo 1589493 1590539 := bstep (se 1 (by rfl) ⟨1192904, by rfl⟩ : syracuseStep 1590539 = 2385809) B2385809
theorem B2721035 : Blo 1589493 2721035 := bstep (se 1 (by rfl) ⟨2040776, by rfl⟩ : syracuseStep 2721035 = 4081553) B4081553
theorem B9184529 : Blo 1589493 9184529 := bstep (se 2 (by rfl) ⟨3444198, by rfl⟩ : syracuseStep 9184529 = 6888397) B6888397
theorem B1590551 : Blo 1589493 1590551 := bstep (se 1 (by rfl) ⟨1192913, by rfl⟩ : syracuseStep 1590551 = 2385827) B2385827
theorem B1590571 : Blo 1589493 1590571 := bstep (se 1 (by rfl) ⟨1192928, by rfl⟩ : syracuseStep 1590571 = 2385857) B2385857
theorem B1590583 : Blo 1589493 1590583 := bstep (se 1 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 1590583 = 2385875) B2385875
theorem B2385227 : Blo 1589493 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B1590603 : Blo 1589493 1590603 := bstep (se 1 (by rfl) ⟨1192952, by rfl⟩ : syracuseStep 1590603 = 2385905) B2385905
theorem B2385239 : Blo 1589493 2385239 := bstep (se 1 (by rfl) ⟨1788929, by rfl⟩ : syracuseStep 2385239 = 3577859) B3577859
theorem B1590615 : Blo 1589493 1590615 := bstep (se 1 (by rfl) ⟨1192961, by rfl⟩ : syracuseStep 1590615 = 2385923) B2385923
theorem B1590635 : Blo 1589493 1590635 := bstep (se 1 (by rfl) ⟨1192976, by rfl⟩ : syracuseStep 1590635 = 2385953) B2385953
theorem B1590647 : Blo 1589493 1590647 := bstep (se 1 (by rfl) ⟨1192985, by rfl⟩ : syracuseStep 1590647 = 2385971) B2385971
theorem B1590667 : Blo 1589493 1590667 := bstep (se 1 (by rfl) ⟨1193000, by rfl⟩ : syracuseStep 1590667 = 2386001) B2386001
theorem B1590679 : Blo 1589493 1590679 := bstep (se 1 (by rfl) ⟨1193009, by rfl⟩ : syracuseStep 1590679 = 2386019) B2386019
theorem B2385305 : Blo 1589493 2385305 := bstep (se 2 (by rfl) ⟨894489, by rfl⟩ : syracuseStep 2385305 = 1788979) B1788979
theorem B1590699 : Blo 1589493 1590699 := bstep (se 1 (by rfl) ⟨1193024, by rfl⟩ : syracuseStep 1590699 = 2386049) B2386049
theorem B1590711 : Blo 1589493 1590711 := bstep (se 1 (by rfl) ⟨1193033, by rfl⟩ : syracuseStep 1590711 = 2386067) B2386067
theorem B1590731 : Blo 1589493 1590731 := bstep (se 1 (by rfl) ⟨1193048, by rfl⟩ : syracuseStep 1590731 = 2386097) B2386097
theorem B1590743 : Blo 1589493 1590743 := bstep (se 1 (by rfl) ⟨1193057, by rfl⟩ : syracuseStep 1590743 = 2386115) B2386115
theorem B1590763 : Blo 1589493 1590763 := bstep (se 1 (by rfl) ⟨1193072, by rfl⟩ : syracuseStep 1590763 = 2386145) B2386145
theorem B1590775 : Blo 1589493 1590775 := bstep (se 1 (by rfl) ⟨1193081, by rfl⟩ : syracuseStep 1590775 = 2386163) B2386163
theorem B2385419 : Blo 1589493 2385419 := bstep (se 1 (by rfl) ⟨1789064, by rfl⟩ : syracuseStep 2385419 = 3578129) B3578129
theorem B1590795 : Blo 1589493 1590795 := bstep (se 1 (by rfl) ⟨1193096, by rfl⟩ : syracuseStep 1590795 = 2386193) B2386193
theorem B2385431 : Blo 1589493 2385431 := bstep (se 1 (by rfl) ⟨1789073, by rfl⟩ : syracuseStep 2385431 = 3578147) B3578147
theorem B1590807 : Blo 1589493 1590807 := bstep (se 1 (by rfl) ⟨1193105, by rfl⟩ : syracuseStep 1590807 = 2386211) B2386211
theorem B1590827 : Blo 1589493 1590827 := bstep (se 1 (by rfl) ⟨1193120, by rfl⟩ : syracuseStep 1590827 = 2386241) B2386241
theorem B1590839 : Blo 1589493 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1590859 : Blo 1589493 1590859 := bstep (se 1 (by rfl) ⟨1193144, by rfl⟩ : syracuseStep 1590859 = 2386289) B2386289
theorem B1590871 : Blo 1589493 1590871 := bstep (se 1 (by rfl) ⟨1193153, by rfl⟩ : syracuseStep 1590871 = 2386307) B2386307
theorem B2385497 : Blo 1589493 2385497 := bstep (se 2 (by rfl) ⟨894561, by rfl⟩ : syracuseStep 2385497 = 1789123) B1789123
theorem B1590891 : Blo 1589493 1590891 := bstep (se 1 (by rfl) ⟨1193168, by rfl⟩ : syracuseStep 1590891 = 2386337) B2386337
theorem B1590903 : Blo 1589493 1590903 := bstep (se 1 (by rfl) ⟨1193177, by rfl⟩ : syracuseStep 1590903 = 2386355) B2386355
theorem B1590923 : Blo 1589493 1590923 := bstep (se 1 (by rfl) ⟨1193192, by rfl⟩ : syracuseStep 1590923 = 2386385) B2386385
theorem B1590935 : Blo 1589493 1590935 := bstep (se 1 (by rfl) ⟨1193201, by rfl⟩ : syracuseStep 1590935 = 2386403) B2386403
theorem B2721431 : Blo 1589493 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B1590955 : Blo 1589493 1590955 := bstep (se 1 (by rfl) ⟨1193216, by rfl⟩ : syracuseStep 1590955 = 2386433) B2386433
theorem B1590967 : Blo 1589493 1590967 := bstep (se 1 (by rfl) ⟨1193225, by rfl⟩ : syracuseStep 1590967 = 2386451) B2386451
theorem B2385611 : Blo 1589493 2385611 := bstep (se 1 (by rfl) ⟨1789208, by rfl⟩ : syracuseStep 2385611 = 3578417) B3578417
theorem B1590987 : Blo 1589493 1590987 := bstep (se 1 (by rfl) ⟨1193240, by rfl⟩ : syracuseStep 1590987 = 2386481) B2386481
theorem B2385623 : Blo 1589493 2385623 := bstep (se 1 (by rfl) ⟨1789217, by rfl⟩ : syracuseStep 2385623 = 3578435) B3578435
theorem B6448913 : Blo 1589493 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B2385689 : Blo 1589493 2385689 := bstep (se 2 (by rfl) ⟨894633, by rfl⟩ : syracuseStep 2385689 = 1789267) B1789267
theorem B2295577 : Blo 1589493 2295577 := bstep (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) B1721683
theorem B19384109 : Blo 1589493 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2385803 : Blo 1589493 2385803 := bstep (se 1 (by rfl) ⟨1789352, by rfl⟩ : syracuseStep 2385803 = 3578705) B3578705
theorem B2385815 : Blo 1589493 2385815 := bstep (se 1 (by rfl) ⟨1789361, by rfl⟩ : syracuseStep 2385815 = 3578723) B3578723
theorem B2385881 : Blo 1589493 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B4024343 : Blo 1589493 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B6793267 : Blo 1589493 6793267 := bstep (se 1 (by rfl) ⟨5094950, by rfl⟩ : syracuseStep 6793267 = 10189901) B10189901
theorem B2385995 : Blo 1589493 2385995 := bstep (se 1 (by rfl) ⟨1789496, by rfl⟩ : syracuseStep 2385995 = 3578993) B3578993
theorem B2386007 : Blo 1589493 2386007 := bstep (se 1 (by rfl) ⟨1789505, by rfl⟩ : syracuseStep 2386007 = 3579011) B3579011
theorem B2386073 : Blo 1589493 2386073 := bstep (se 2 (by rfl) ⟨894777, by rfl⟩ : syracuseStep 2386073 = 1789555) B1789555
theorem B2386187 : Blo 1589493 2386187 := bstep (se 1 (by rfl) ⟨1789640, by rfl⟩ : syracuseStep 2386187 = 3579281) B3579281
theorem B2386199 : Blo 1589493 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B1698103 : Blo 1589493 1698103 := bstep (se 1 (by rfl) ⟨1273577, by rfl⟩ : syracuseStep 1698103 = 2547155) B2547155
theorem B5368139 : Blo 1589493 5368139 := bstep (se 1 (by rfl) ⟨4026104, by rfl⟩ : syracuseStep 5368139 = 8052209) B8052209
theorem B2386265 : Blo 1589493 2386265 := bstep (se 2 (by rfl) ⟨894849, by rfl⟩ : syracuseStep 2386265 = 1789699) B1789699
theorem B1788331 : Blo 1589493 1788331 := bstep (se 1 (by rfl) ⟨1341248, by rfl⟩ : syracuseStep 1788331 = 2682497) B2682497
theorem B3819955 : Blo 1589493 3819955 := bstep (se 1 (by rfl) ⟨2864966, by rfl⟩ : syracuseStep 3819955 = 5729933) B5729933
theorem B2148811 : Blo 1589493 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B2386379 : Blo 1589493 2386379 := bstep (se 1 (by rfl) ⟨1789784, by rfl⟩ : syracuseStep 2386379 = 3579569) B3579569
theorem B2263511 : Blo 1589493 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B2386391 : Blo 1589493 2386391 := bstep (se 1 (by rfl) ⟨1789793, by rfl⟩ : syracuseStep 2386391 = 3579587) B3579587
theorem B1698283 : Blo 1589493 1698283 := bstep (se 1 (by rfl) ⟨1273712, by rfl⟩ : syracuseStep 1698283 = 2547425) B2547425
theorem B12077585 : Blo 1589493 12077585 := bstep (se 2 (by rfl) ⟨4529094, by rfl⟩ : syracuseStep 12077585 = 9058189) B9058189
theorem B1788439 : Blo 1589493 1788439 := bstep (se 1 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 1788439 = 2682659) B2682659
theorem B2386457 : Blo 1589493 2386457 := bstep (se 2 (by rfl) ⟨894921, by rfl⟩ : syracuseStep 2386457 = 1789843) B1789843
theorem B6040115 : Blo 1589493 6040115 := bstep (se 1 (by rfl) ⟨4530086, by rfl⟩ : syracuseStep 6040115 = 9060173) B9060173
theorem B3312193 : Blo 1589493 3312193 := bstep (se 2 (by rfl) ⟨1242072, by rfl⟩ : syracuseStep 3312193 = 2484145) B2484145
theorem B6040129 : Blo 1589493 6040129 := bstep (se 2 (by rfl) ⟨2265048, by rfl⟩ : syracuseStep 6040129 = 4530097) B4530097
theorem B5368409 : Blo 1589493 5368409 := bstep (se 2 (by rfl) ⟨2013153, by rfl⟩ : syracuseStep 5368409 = 4026307) B4026307
theorem B10193539 : Blo 1589493 10193539 := bstep (se 1 (by rfl) ⟨7645154, by rfl⟩ : syracuseStep 10193539 = 15290309) B15290309
theorem B6793901 : Blo 1589493 6793901 := bstep (se 3 (by rfl) ⟨1273856, by rfl⟩ : syracuseStep 6793901 = 2547713) B2547713
theorem B4025011 : Blo 1589493 4025011 := bstep (se 1 (by rfl) ⟨3018758, by rfl⟩ : syracuseStep 4025011 = 6037517) B6037517
theorem B1788619 : Blo 1589493 1788619 := bstep (se 1 (by rfl) ⟨1341464, by rfl⟩ : syracuseStep 1788619 = 2682929) B2682929
theorem B1788727 : Blo 1589493 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B4025153 : Blo 1589493 4025153 := bstep (se 2 (by rfl) ⟨1509432, by rfl⟩ : syracuseStep 4025153 = 3018865) B3018865
theorem B34868033 : Blo 1589493 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B8047511 : Blo 1589493 8047511 := bstep (se 1 (by rfl) ⟨6035633, by rfl⟩ : syracuseStep 8047511 = 12071267) B12071267
theorem B3017665 : Blo 1589493 3017665 := bstep (se 2 (by rfl) ⟨1131624, by rfl⟩ : syracuseStep 3017665 = 2263249) B2263249
theorem B1788907 : Blo 1589493 1788907 := bstep (se 1 (by rfl) ⟨1341680, by rfl⟩ : syracuseStep 1788907 = 2683361) B2683361
theorem B5377099 : Blo 1589493 5377099 := bstep (se 1 (by rfl) ⟨4032824, by rfl⟩ : syracuseStep 5377099 = 8065649) B8065649
theorem B1789015 : Blo 1589493 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B2149465 : Blo 1589493 2149465 := bstep (se 2 (by rfl) ⟨806049, by rfl⟩ : syracuseStep 2149465 = 1612099) B1612099
theorem B1789195 : Blo 1589493 1789195 := bstep (se 1 (by rfl) ⟨1341896, by rfl⟩ : syracuseStep 1789195 = 2683793) B2683793
theorem B5369111 : Blo 1589493 5369111 := bstep (se 1 (by rfl) ⟨4026833, by rfl⟩ : syracuseStep 5369111 = 8053667) B8053667
theorem B1789303 : Blo 1589493 1789303 := bstep (se 1 (by rfl) ⟨1341977, by rfl⟩ : syracuseStep 1789303 = 2683955) B2683955
theorem B12070295 : Blo 1589493 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B1789483 : Blo 1589493 1789483 := bstep (se 1 (by rfl) ⟨1342112, by rfl⟩ : syracuseStep 1789483 = 2684225) B2684225
theorem B2682443 : Blo 1589493 2682443 := bstep (se 1 (by rfl) ⟨2011832, by rfl⟩ : syracuseStep 2682443 = 4023665) B4023665
theorem B3018379 : Blo 1589493 3018379 := bstep (se 1 (by rfl) ⟨2263784, by rfl⟩ : syracuseStep 3018379 = 4527569) B4527569
theorem B1789591 : Blo 1589493 1789591 := bstep (se 1 (by rfl) ⟨1342193, by rfl⟩ : syracuseStep 1789591 = 2684387) B2684387
theorem B2682571 : Blo 1589493 2682571 := bstep (se 1 (by rfl) ⟨2011928, by rfl⟩ : syracuseStep 2682571 = 4023857) B4023857
theorem B3018455 : Blo 1589493 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B13766435 : Blo 1589493 13766435 := bstep (se 1 (by rfl) ⟨10324826, by rfl⟩ : syracuseStep 13766435 = 20649653) B20649653
theorem B1789771 : Blo 1589493 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B2682713 : Blo 1589493 2682713 := bstep (se 2 (by rfl) ⟨1006017, by rfl⟩ : syracuseStep 2682713 = 2012035) B2012035
theorem B9301853 : Blo 1589493 9301853 := bstep (se 3 (by rfl) ⟨1744097, by rfl⟩ : syracuseStep 9301853 = 3488195) B3488195
theorem B2682841 : Blo 1589493 2682841 := bstep (se 2 (by rfl) ⟨1006065, by rfl⟩ : syracuseStep 2682841 = 2012131) B2012131
theorem B4026419 : Blo 1589493 4026419 := bstep (se 1 (by rfl) ⟨3019814, by rfl⟩ : syracuseStep 4026419 = 6039629) B6039629
theorem B5730521 : Blo 1589493 5730521 := bstep (se 2 (by rfl) ⟨2148945, by rfl⟩ : syracuseStep 5730521 = 4297891) B4297891
theorem B3019123 : Blo 1589493 3019123 := bstep (se 1 (by rfl) ⟨2264342, by rfl⟩ : syracuseStep 3019123 = 4528685) B4528685
theorem B3396019 : Blo 1589493 3396019 := bstep (se 1 (by rfl) ⟨2547014, by rfl⟩ : syracuseStep 3396019 = 5094029) B5094029
theorem B2683415 : Blo 1589493 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B3822155 : Blo 1589493 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B13775435 : Blo 1589493 13775435 := bstep (se 1 (by rfl) ⟨10331576, by rfl⟩ : syracuseStep 13775435 = 20663153) B20663153
theorem B4026955 : Blo 1589493 4026955 := bstep (se 1 (by rfl) ⟨3020216, by rfl⟩ : syracuseStep 4026955 = 6040433) B6040433
theorem B3019351 : Blo 1589493 3019351 := bstep (se 1 (by rfl) ⟨2264513, by rfl⟩ : syracuseStep 3019351 = 4529027) B4529027
theorem B2683543 : Blo 1589493 2683543 := bstep (se 1 (by rfl) ⟨2012657, by rfl⟩ : syracuseStep 2683543 = 4025315) B4025315
theorem B3576473 : Blo 1589493 3576473 := bstep (se 2 (by rfl) ⟨1341177, by rfl⟩ : syracuseStep 3576473 = 2682355) B2682355
theorem B3019457 : Blo 1589493 3019457 := bstep (se 2 (by rfl) ⟨1132296, by rfl⟩ : syracuseStep 3019457 = 2264593) B2264593
theorem B4027097 : Blo 1589493 4027097 := bstep (se 2 (by rfl) ⟨1510161, by rfl⟩ : syracuseStep 4027097 = 3020323) B3020323
theorem B3576563 : Blo 1589493 3576563 := bstep (se 1 (by rfl) ⟨2682422, by rfl⟩ : syracuseStep 3576563 = 5364845) B5364845
theorem B3576599 : Blo 1589493 3576599 := bstep (se 1 (by rfl) ⟨2682449, by rfl⟩ : syracuseStep 3576599 = 5364899) B5364899
theorem B3396377 : Blo 1589493 3396377 := bstep (se 2 (by rfl) ⟨1273641, by rfl⟩ : syracuseStep 3396377 = 2547283) B2547283
theorem B2011979 : Blo 1589493 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B3019609 : Blo 1589493 3019609 := bstep (se 2 (by rfl) ⟨1132353, by rfl⟩ : syracuseStep 3019609 = 2264707) B2264707
theorem B4526999 : Blo 1589493 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B5092247 : Blo 1589493 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B3576779 : Blo 1589493 3576779 := bstep (se 1 (by rfl) ⟨2682584, by rfl⟩ : syracuseStep 3576779 = 5365169) B5365169
theorem B3576833 : Blo 1589493 3576833 := bstep (se 2 (by rfl) ⟨1341312, by rfl⟩ : syracuseStep 3576833 = 2682625) B2682625
theorem B15283235 : Blo 1589493 15283235 := bstep (se 1 (by rfl) ⟨11462426, by rfl⟩ : syracuseStep 15283235 = 22924853) B22924853
theorem B3577049 : Blo 1589493 3577049 := bstep (se 2 (by rfl) ⟨1341393, by rfl⟩ : syracuseStep 3577049 = 2682787) B2682787
theorem B2684171 : Blo 1589493 2684171 := bstep (se 1 (by rfl) ⟨2013128, by rfl⟩ : syracuseStep 2684171 = 4026257) B4026257
theorem B3577139 : Blo 1589493 3577139 := bstep (se 1 (by rfl) ⟨2682854, by rfl⟩ : syracuseStep 3577139 = 5365709) B5365709
theorem B3577175 : Blo 1589493 3577175 := bstep (se 1 (by rfl) ⟨2682881, by rfl⟩ : syracuseStep 3577175 = 5365763) B5365763
theorem B2684299 : Blo 1589493 2684299 := bstep (se 1 (by rfl) ⟨2013224, by rfl⟩ : syracuseStep 2684299 = 4026449) B4026449
theorem B22935001 : Blo 1589493 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B2864627 : Blo 1589493 2864627 := bstep (se 1 (by rfl) ⟨2148470, by rfl⟩ : syracuseStep 2864627 = 4296941) B4296941
theorem B3577355 : Blo 1589493 3577355 := bstep (se 1 (by rfl) ⟨2683016, by rfl⟩ : syracuseStep 3577355 = 5366033) B5366033
theorem B2012683 : Blo 1589493 2012683 := bstep (se 1 (by rfl) ⟨1509512, by rfl⟩ : syracuseStep 2012683 = 3019025) B3019025
theorem B2684441 : Blo 1589493 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B3577409 : Blo 1589493 3577409 := bstep (se 2 (by rfl) ⟨1341528, by rfl⟩ : syracuseStep 3577409 = 2683057) B2683057
theorem B2684569 : Blo 1589493 2684569 := bstep (se 2 (by rfl) ⟨1006713, by rfl⟩ : syracuseStep 2684569 = 2013427) B2013427
theorem B9180851 : Blo 1589493 9180851 := bstep (se 1 (by rfl) ⟨6885638, by rfl⟩ : syracuseStep 9180851 = 13771277) B13771277
theorem B4527809 : Blo 1589493 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B1611499 : Blo 1589493 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B6051601 : Blo 1589493 6051601 := bstep (se 2 (by rfl) ⟨2269350, by rfl⟩ : syracuseStep 6051601 = 4538701) B4538701
theorem B2012951 : Blo 1589493 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B3577625 : Blo 1589493 3577625 := bstep (se 2 (by rfl) ⟨1341609, by rfl⟩ : syracuseStep 3577625 = 2683219) B2683219
theorem B61962083 : Blo 1589493 61962083 := bstep (se 1 (by rfl) ⟨46471562, by rfl⟩ : syracuseStep 61962083 = 92943125) B92943125
theorem B17200997 : Blo 1589493 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B3577715 : Blo 1589493 3577715 := bstep (se 1 (by rfl) ⟨2683286, by rfl⟩ : syracuseStep 3577715 = 5366573) B5366573
theorem B29407093 : Blo 1589493 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B3577751 : Blo 1589493 3577751 := bstep (se 1 (by rfl) ⟨2683313, by rfl⟩ : syracuseStep 3577751 = 5366627) B5366627
theorem B95532979 : Blo 1589493 95532979 := bstep (se 1 (by rfl) ⟨71649734, by rfl⟩ : syracuseStep 95532979 = 143299469) B143299469
theorem B6445021 : Blo 1589493 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B3577931 : Blo 1589493 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B3577985 : Blo 1589493 3577985 := bstep (se 2 (by rfl) ⟨1341744, by rfl⟩ : syracuseStep 3577985 = 2683489) B2683489
theorem B3676481 : Blo 1589493 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B12081473 : Blo 1589493 12081473 := bstep (se 2 (by rfl) ⟨4530552, by rfl⟩ : syracuseStep 12081473 = 9061105) B9061105
theorem B3578201 : Blo 1589493 3578201 := bstep (se 2 (by rfl) ⟨1341825, by rfl⟩ : syracuseStep 3578201 = 2683651) B2683651
theorem B10877285 : Blo 1589493 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B8051075 : Blo 1589493 8051075 := bstep (se 1 (by rfl) ⟨6038306, by rfl⟩ : syracuseStep 8051075 = 12076613) B12076613
theorem B6789527 : Blo 1589493 6789527 := bstep (se 1 (by rfl) ⟨5092145, by rfl⟩ : syracuseStep 6789527 = 10184291) B10184291
theorem B13580723 : Blo 1589493 13580723 := bstep (se 1 (by rfl) ⟨10185542, by rfl⟩ : syracuseStep 13580723 = 20371085) B20371085
theorem B3578291 : Blo 1589493 3578291 := bstep (se 1 (by rfl) ⟨2683718, by rfl⟩ : syracuseStep 3578291 = 5367437) B5367437
theorem B3578327 : Blo 1589493 3578327 := bstep (se 1 (by rfl) ⟨2683745, by rfl⟩ : syracuseStep 3578327 = 5367491) B5367491
theorem B2865665 : Blo 1589493 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B8600195 : Blo 1589493 8600195 := bstep (se 1 (by rfl) ⟨6450146, by rfl⟩ : syracuseStep 8600195 = 12900293) B12900293
theorem B3578507 : Blo 1589493 3578507 := bstep (se 1 (by rfl) ⟨2683880, by rfl⟩ : syracuseStep 3578507 = 5367761) B5367761
theorem B2546329 : Blo 1589493 2546329 := bstep (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) B1909747
theorem B3578561 : Blo 1589493 3578561 := bstep (se 2 (by rfl) ⟨1341960, by rfl⟩ : syracuseStep 3578561 = 2683921) B2683921
theorem B6036227 : Blo 1589493 6036227 := bstep (se 1 (by rfl) ⟨4527170, by rfl⟩ : syracuseStep 6036227 = 9054341) B9054341
theorem B6036241 : Blo 1589493 6036241 := bstep (se 2 (by rfl) ⟨2263590, by rfl⟩ : syracuseStep 6036241 = 4527181) B4527181
theorem B9059147 : Blo 1589493 9059147 := bstep (se 1 (by rfl) ⟨6794360, by rfl⟩ : syracuseStep 9059147 = 13588721) B13588721
theorem B20380517 : Blo 1589493 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B3578777 : Blo 1589493 3578777 := bstep (se 2 (by rfl) ⟨1342041, by rfl⟩ : syracuseStep 3578777 = 2684083) B2684083
theorem B7748531 : Blo 1589493 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B5364683 : Blo 1589493 5364683 := bstep (se 1 (by rfl) ⟨4023512, by rfl⟩ : syracuseStep 5364683 = 8047025) B8047025
theorem B3578867 : Blo 1589493 3578867 := bstep (se 1 (by rfl) ⟨2684150, by rfl⟩ : syracuseStep 3578867 = 5368301) B5368301
theorem B3578903 : Blo 1589493 3578903 := bstep (se 1 (by rfl) ⟨2684177, by rfl⟩ : syracuseStep 3578903 = 5368355) B5368355
theorem B6036545 : Blo 1589493 6036545 := bstep (se 2 (by rfl) ⟨2263704, by rfl⟩ : syracuseStep 6036545 = 4527409) B4527409
theorem B7453889 : Blo 1589493 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B3579083 : Blo 1589493 3579083 := bstep (se 1 (by rfl) ⟨2684312, by rfl⟩ : syracuseStep 3579083 = 5368625) B5368625
theorem B5364953 : Blo 1589493 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B3579137 : Blo 1589493 3579137 := bstep (se 2 (by rfl) ⟨1342176, by rfl⟩ : syracuseStep 3579137 = 2684353) B2684353
theorem B4529459 : Blo 1589493 4529459 := bstep (se 1 (by rfl) ⟨3397094, by rfl⟩ : syracuseStep 4529459 = 6794189) B6794189
theorem B4529483 : Blo 1589493 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B3579353 : Blo 1589493 3579353 := bstep (se 2 (by rfl) ⟨1342257, by rfl⟩ : syracuseStep 3579353 = 2684515) B2684515
theorem B3579443 : Blo 1589493 3579443 := bstep (se 1 (by rfl) ⟨2684582, by rfl⟩ : syracuseStep 3579443 = 5369165) B5369165
theorem B3579479 : Blo 1589493 3579479 := bstep (se 1 (by rfl) ⟨2684609, by rfl⟩ : syracuseStep 3579479 = 5369219) B5369219
theorem B6037213 : Blo 1589493 6037213 := bstep (se 3 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 6037213 = 2263955) B2263955
theorem B3579659 : Blo 1589493 3579659 := bstep (se 1 (by rfl) ⟨2684744, by rfl⟩ : syracuseStep 3579659 = 5369489) B5369489
theorem B3579713 : Blo 1589493 3579713 := bstep (se 2 (by rfl) ⟨1342392, by rfl⟩ : syracuseStep 3579713 = 2684785) B2684785
theorem B5365655 : Blo 1589493 5365655 := bstep (se 1 (by rfl) ⟨4024241, by rfl⟩ : syracuseStep 5365655 = 8048483) B8048483
theorem B34381745 : Blo 1589493 34381745 := bstep (se 2 (by rfl) ⟨12893154, by rfl⟩ : syracuseStep 34381745 = 25786309) B25786309
theorem B5095361 : Blo 1589493 5095361 := bstep (se 2 (by rfl) ⟨1910760, by rfl⟩ : syracuseStep 5095361 = 3821521) B3821521
theorem B1589511 : Blo 1589493 1589511 := bstep (se 1 (by rfl) ⟨1192133, by rfl⟩ : syracuseStep 1589511 = 2384267) B2384267
theorem B1589519 : Blo 1589493 1589519 := bstep (se 1 (by rfl) ⟨1192139, by rfl⟩ : syracuseStep 1589519 = 2384279) B2384279
theorem B1589563 : Blo 1589493 1589563 := bstep (se 1 (by rfl) ⟨1192172, by rfl⟩ : syracuseStep 1589563 = 2384345) B2384345
theorem B1589639 : Blo 1589493 1589639 := bstep (se 1 (by rfl) ⟨1192229, by rfl⟩ : syracuseStep 1589639 = 2384459) B2384459
theorem B2548103 : Blo 1589493 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B9183623 : Blo 1589493 9183623 := bstep (se 1 (by rfl) ⟨6887717, by rfl⟩ : syracuseStep 9183623 = 13775435) B13775435
theorem B1589647 : Blo 1589493 1589647 := bstep (se 1 (by rfl) ⟨1192235, by rfl⟩ : syracuseStep 1589647 = 2384471) B2384471
theorem B2384315 : Blo 1589493 2384315 := bstep (se 1 (by rfl) ⟨1788236, by rfl⟩ : syracuseStep 2384315 = 3576473) B3576473
theorem B1589691 : Blo 1589493 1589691 := bstep (se 1 (by rfl) ⟨1192268, by rfl⟩ : syracuseStep 1589691 = 2384537) B2384537
theorem B2384375 : Blo 1589493 2384375 := bstep (se 1 (by rfl) ⟨1788281, by rfl⟩ : syracuseStep 2384375 = 3576563) B3576563
theorem B1589767 : Blo 1589493 1589767 := bstep (se 1 (by rfl) ⟨1192325, by rfl⟩ : syracuseStep 1589767 = 2384651) B2384651
theorem B2384399 : Blo 1589493 2384399 := bstep (se 1 (by rfl) ⟨1788299, by rfl⟩ : syracuseStep 2384399 = 3576599) B3576599
theorem B1589775 : Blo 1589493 1589775 := bstep (se 1 (by rfl) ⟨1192331, by rfl⟩ : syracuseStep 1589775 = 2384663) B2384663
theorem B2384441 : Blo 1589493 2384441 := bstep (se 2 (by rfl) ⟨894165, by rfl⟩ : syracuseStep 2384441 = 1788331) B1788331
theorem B1589819 : Blo 1589493 1589819 := bstep (se 1 (by rfl) ⟨1192364, by rfl⟩ : syracuseStep 1589819 = 2384729) B2384729
theorem B2384519 : Blo 1589493 2384519 := bstep (se 1 (by rfl) ⟨1788389, by rfl⟩ : syracuseStep 2384519 = 3576779) B3576779
theorem B1589895 : Blo 1589493 1589895 := bstep (se 1 (by rfl) ⟨1192421, by rfl⟩ : syracuseStep 1589895 = 2384843) B2384843
theorem B1589903 : Blo 1589493 1589903 := bstep (se 1 (by rfl) ⟨1192427, by rfl⟩ : syracuseStep 1589903 = 2384855) B2384855
theorem B2384555 : Blo 1589493 2384555 := bstep (se 1 (by rfl) ⟨1788416, by rfl⟩ : syracuseStep 2384555 = 3576833) B3576833
theorem B1589947 : Blo 1589493 1589947 := bstep (se 1 (by rfl) ⟨1192460, by rfl⟩ : syracuseStep 1589947 = 2384921) B2384921
theorem B2384585 : Blo 1589493 2384585 := bstep (se 2 (by rfl) ⟨894219, by rfl⟩ : syracuseStep 2384585 = 1788439) B1788439
theorem B8053505 : Blo 1589493 8053505 := bstep (se 2 (by rfl) ⟨3020064, by rfl⟩ : syracuseStep 8053505 = 6040129) B6040129
theorem B1590023 : Blo 1589493 1590023 := bstep (se 1 (by rfl) ⟨1192517, by rfl⟩ : syracuseStep 1590023 = 2385035) B2385035
theorem B1590031 : Blo 1589493 1590031 := bstep (se 1 (by rfl) ⟨1192523, by rfl⟩ : syracuseStep 1590031 = 2385047) B2385047
theorem B2384699 : Blo 1589493 2384699 := bstep (se 1 (by rfl) ⟨1788524, by rfl⟩ : syracuseStep 2384699 = 3577049) B3577049
theorem B1590075 : Blo 1589493 1590075 := bstep (se 1 (by rfl) ⟨1192556, by rfl⟩ : syracuseStep 1590075 = 2385113) B2385113
theorem B13591385 : Blo 1589493 13591385 := bstep (se 2 (by rfl) ⟨5096769, by rfl⟩ : syracuseStep 13591385 = 10193539) B10193539
theorem B2384759 : Blo 1589493 2384759 := bstep (se 1 (by rfl) ⟨1788569, by rfl⟩ : syracuseStep 2384759 = 3577139) B3577139
theorem B1590151 : Blo 1589493 1590151 := bstep (se 1 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 1590151 = 2385227) B2385227
theorem B2384783 : Blo 1589493 2384783 := bstep (se 1 (by rfl) ⟨1788587, by rfl⟩ : syracuseStep 2384783 = 3577175) B3577175
theorem B1590159 : Blo 1589493 1590159 := bstep (se 1 (by rfl) ⟨1192619, by rfl⟩ : syracuseStep 1590159 = 2385239) B2385239
theorem B5366681 : Blo 1589493 5366681 := bstep (se 2 (by rfl) ⟨2012505, by rfl⟩ : syracuseStep 5366681 = 4025011) B4025011
theorem B2384825 : Blo 1589493 2384825 := bstep (se 2 (by rfl) ⟨894309, by rfl⟩ : syracuseStep 2384825 = 1788619) B1788619
theorem B1590203 : Blo 1589493 1590203 := bstep (se 1 (by rfl) ⟨1192652, by rfl⟩ : syracuseStep 1590203 = 2385305) B2385305
theorem B1909751 : Blo 1589493 1909751 := bstep (se 1 (by rfl) ⟨1432313, by rfl⟩ : syracuseStep 1909751 = 2864627) B2864627
theorem B2384903 : Blo 1589493 2384903 := bstep (se 1 (by rfl) ⟨1788677, by rfl⟩ : syracuseStep 2384903 = 3577355) B3577355
theorem B1590279 : Blo 1589493 1590279 := bstep (se 1 (by rfl) ⟨1192709, by rfl⟩ : syracuseStep 1590279 = 2385419) B2385419
theorem B1590287 : Blo 1589493 1590287 := bstep (se 1 (by rfl) ⟨1192715, by rfl⟩ : syracuseStep 1590287 = 2385431) B2385431
theorem B2384939 : Blo 1589493 2384939 := bstep (se 1 (by rfl) ⟨1788704, by rfl⟩ : syracuseStep 2384939 = 3577409) B3577409
theorem B1590331 : Blo 1589493 1590331 := bstep (se 1 (by rfl) ⟨1192748, by rfl⟩ : syracuseStep 1590331 = 2385497) B2385497
theorem B2384969 : Blo 1589493 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B1590407 : Blo 1589493 1590407 := bstep (se 1 (by rfl) ⟨1192805, by rfl⟩ : syracuseStep 1590407 = 2385611) B2385611
theorem B1590415 : Blo 1589493 1590415 := bstep (se 1 (by rfl) ⟨1192811, by rfl⟩ : syracuseStep 1590415 = 2385623) B2385623
theorem B2385083 : Blo 1589493 2385083 := bstep (se 1 (by rfl) ⟨1788812, by rfl⟩ : syracuseStep 2385083 = 3577625) B3577625
theorem B1590459 : Blo 1589493 1590459 := bstep (se 1 (by rfl) ⟨1192844, by rfl⟩ : syracuseStep 1590459 = 2385689) B2385689
theorem B2385143 : Blo 1589493 2385143 := bstep (se 1 (by rfl) ⟨1788857, by rfl⟩ : syracuseStep 2385143 = 3577715) B3577715
theorem B4023553 : Blo 1589493 4023553 := bstep (se 2 (by rfl) ⟨1508832, by rfl⟩ : syracuseStep 4023553 = 3017665) B3017665
theorem B1590535 : Blo 1589493 1590535 := bstep (se 1 (by rfl) ⟨1192901, by rfl⟩ : syracuseStep 1590535 = 2385803) B2385803
theorem B2385167 : Blo 1589493 2385167 := bstep (se 1 (by rfl) ⟨1788875, by rfl⟩ : syracuseStep 2385167 = 3577751) B3577751
theorem B1590543 : Blo 1589493 1590543 := bstep (se 1 (by rfl) ⟨1192907, by rfl⟩ : syracuseStep 1590543 = 2385815) B2385815
theorem B2385209 : Blo 1589493 2385209 := bstep (se 2 (by rfl) ⟨894453, by rfl⟩ : syracuseStep 2385209 = 1788907) B1788907
theorem B1590587 : Blo 1589493 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B2385287 : Blo 1589493 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B1590663 : Blo 1589493 1590663 := bstep (se 1 (by rfl) ⟨1192997, by rfl⟩ : syracuseStep 1590663 = 2385995) B2385995
theorem B1590671 : Blo 1589493 1590671 := bstep (se 1 (by rfl) ⟨1193003, by rfl⟩ : syracuseStep 1590671 = 2386007) B2386007
theorem B2385323 : Blo 1589493 2385323 := bstep (se 1 (by rfl) ⟨1788992, by rfl⟩ : syracuseStep 2385323 = 3577985) B3577985
theorem B7169465 : Blo 1589493 7169465 := bstep (se 2 (by rfl) ⟨2688549, by rfl⟩ : syracuseStep 7169465 = 5377099) B5377099
theorem B1590715 : Blo 1589493 1590715 := bstep (se 1 (by rfl) ⟨1193036, by rfl⟩ : syracuseStep 1590715 = 2386073) B2386073
theorem B2385353 : Blo 1589493 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B1590791 : Blo 1589493 1590791 := bstep (se 1 (by rfl) ⟨1193093, by rfl⟩ : syracuseStep 1590791 = 2386187) B2386187
theorem B1590799 : Blo 1589493 1590799 := bstep (se 1 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 1590799 = 2386199) B2386199
theorem B2450987 : Blo 1589493 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B8054315 : Blo 1589493 8054315 := bstep (se 1 (by rfl) ⟨6040736, by rfl⟩ : syracuseStep 8054315 = 12081473) B12081473
theorem B2385467 : Blo 1589493 2385467 := bstep (se 1 (by rfl) ⟨1789100, by rfl⟩ : syracuseStep 2385467 = 3578201) B3578201
theorem B1590843 : Blo 1589493 1590843 := bstep (se 1 (by rfl) ⟨1193132, by rfl⟩ : syracuseStep 1590843 = 2386265) B2386265
theorem B5367383 : Blo 1589493 5367383 := bstep (se 1 (by rfl) ⟨4025537, by rfl⟩ : syracuseStep 5367383 = 8051075) B8051075
theorem B9053815 : Blo 1589493 9053815 := bstep (se 1 (by rfl) ⟨6790361, by rfl⟩ : syracuseStep 9053815 = 13580723) B13580723
theorem B2385527 : Blo 1589493 2385527 := bstep (se 1 (by rfl) ⟨1789145, by rfl⟩ : syracuseStep 2385527 = 3578291) B3578291
theorem B1590919 : Blo 1589493 1590919 := bstep (se 1 (by rfl) ⟨1193189, by rfl⟩ : syracuseStep 1590919 = 2386379) B2386379
theorem B2385551 : Blo 1589493 2385551 := bstep (se 1 (by rfl) ⟨1789163, by rfl⟩ : syracuseStep 2385551 = 3578327) B3578327
theorem B1590927 : Blo 1589493 1590927 := bstep (se 1 (by rfl) ⟨1193195, by rfl⟩ : syracuseStep 1590927 = 2386391) B2386391
theorem B2385593 : Blo 1589493 2385593 := bstep (se 2 (by rfl) ⟨894597, by rfl⟩ : syracuseStep 2385593 = 1789195) B1789195
theorem B1590971 : Blo 1589493 1590971 := bstep (se 1 (by rfl) ⟨1193228, by rfl⟩ : syracuseStep 1590971 = 2386457) B2386457
theorem B2385671 : Blo 1589493 2385671 := bstep (se 1 (by rfl) ⟨1789253, by rfl⟩ : syracuseStep 2385671 = 3578507) B3578507
theorem B2385707 : Blo 1589493 2385707 := bstep (se 1 (by rfl) ⟨1789280, by rfl⟩ : syracuseStep 2385707 = 3578561) B3578561
theorem B2385737 : Blo 1589493 2385737 := bstep (se 2 (by rfl) ⟨894651, by rfl⟩ : syracuseStep 2385737 = 1789303) B1789303
theorem B4024151 : Blo 1589493 4024151 := bstep (se 1 (by rfl) ⟨3018113, by rfl⟩ : syracuseStep 4024151 = 6036227) B6036227
theorem B6039431 : Blo 1589493 6039431 := bstep (se 1 (by rfl) ⟨4529573, by rfl⟩ : syracuseStep 6039431 = 9059147) B9059147
theorem B2385851 : Blo 1589493 2385851 := bstep (se 1 (by rfl) ⟨1789388, by rfl⟩ : syracuseStep 2385851 = 3578777) B3578777
theorem B2385911 : Blo 1589493 2385911 := bstep (se 1 (by rfl) ⟨1789433, by rfl⟩ : syracuseStep 2385911 = 3578867) B3578867
theorem B2385935 : Blo 1589493 2385935 := bstep (se 1 (by rfl) ⟨1789451, by rfl⟩ : syracuseStep 2385935 = 3578903) B3578903
theorem B4024363 : Blo 1589493 4024363 := bstep (se 1 (by rfl) ⟨3018272, by rfl⟩ : syracuseStep 4024363 = 6036545) B6036545
theorem B2385977 : Blo 1589493 2385977 := bstep (se 2 (by rfl) ⟨894741, by rfl⟩ : syracuseStep 2385977 = 1789483) B1789483
theorem B5367869 : Blo 1589493 5367869 := bstep (se 3 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 5367869 = 2012951) B2012951
theorem B2386055 : Blo 1589493 2386055 := bstep (se 1 (by rfl) ⟨1789541, by rfl⟩ : syracuseStep 2386055 = 3579083) B3579083
theorem B2386091 : Blo 1589493 2386091 := bstep (se 1 (by rfl) ⟨1789568, by rfl⟩ : syracuseStep 2386091 = 3579137) B3579137
theorem B4024505 : Blo 1589493 4024505 := bstep (se 2 (by rfl) ⟨1509189, by rfl⟩ : syracuseStep 4024505 = 3018379) B3018379
theorem B2386121 : Blo 1589493 2386121 := bstep (se 2 (by rfl) ⟨894795, by rfl⟩ : syracuseStep 2386121 = 1789591) B1789591
theorem B8046863 : Blo 1589493 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B2148665 : Blo 1589493 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B2386235 : Blo 1589493 2386235 := bstep (se 1 (by rfl) ⟨1789676, by rfl⟩ : syracuseStep 2386235 = 3579353) B3579353
theorem B2386295 : Blo 1589493 2386295 := bstep (se 1 (by rfl) ⟨1789721, by rfl⟩ : syracuseStep 2386295 = 3579443) B3579443
theorem B1788295 : Blo 1589493 1788295 := bstep (se 1 (by rfl) ⟨1341221, by rfl⟩ : syracuseStep 1788295 = 2682443) B2682443
theorem B2386319 : Blo 1589493 2386319 := bstep (se 1 (by rfl) ⟨1789739, by rfl⟩ : syracuseStep 2386319 = 3579479) B3579479
theorem B2386361 : Blo 1589493 2386361 := bstep (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) B1789771
theorem B2386439 : Blo 1589493 2386439 := bstep (se 1 (by rfl) ⟨1789829, by rfl⟩ : syracuseStep 2386439 = 3579659) B3579659
theorem B9177623 : Blo 1589493 9177623 := bstep (se 1 (by rfl) ⟨6883217, by rfl⟩ : syracuseStep 9177623 = 13766435) B13766435
theorem B2386475 : Blo 1589493 2386475 := bstep (se 1 (by rfl) ⟨1789856, by rfl⟩ : syracuseStep 2386475 = 3579713) B3579713
theorem B1788475 : Blo 1589493 1788475 := bstep (se 1 (by rfl) ⟨1341356, by rfl⟩ : syracuseStep 1788475 = 2682713) B2682713
theorem B69708559 : Blo 1589493 69708559 := bstep (se 1 (by rfl) ⟨52281419, by rfl⟩ : syracuseStep 69708559 = 104562839) B104562839
theorem B9055091 : Blo 1589493 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B1788943 : Blo 1589493 1788943 := bstep (se 1 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 1788943 = 2683415) B2683415
theorem B4025497 : Blo 1589493 4025497 := bstep (se 2 (by rfl) ⟨1509561, by rfl⟩ : syracuseStep 4025497 = 3019123) B3019123
theorem B15281389 : Blo 1589493 15281389 := bstep (se 3 (by rfl) ⟨2865260, by rfl⟩ : syracuseStep 15281389 = 5730521) B5730521
theorem B3017999 : Blo 1589493 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B2264377 : Blo 1589493 2264377 := bstep (se 2 (by rfl) ⟨849141, by rfl⟩ : syracuseStep 2264377 = 1698283) B1698283
theorem B9055547 : Blo 1589493 9055547 := bstep (se 1 (by rfl) ⟨6791660, by rfl⟩ : syracuseStep 9055547 = 13583321) B13583321
theorem B4025659 : Blo 1589493 4025659 := bstep (se 1 (by rfl) ⟨3019244, by rfl⟩ : syracuseStep 4025659 = 6038489) B6038489
theorem B1813903 : Blo 1589493 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B5369273 : Blo 1589493 5369273 := bstep (se 2 (by rfl) ⟨2013477, by rfl⟩ : syracuseStep 5369273 = 4026955) B4026955
theorem B4025801 : Blo 1589493 4025801 := bstep (se 2 (by rfl) ⟨1509675, by rfl⟩ : syracuseStep 4025801 = 3019351) B3019351
theorem B12078557 : Blo 1589493 12078557 := bstep (se 3 (by rfl) ⟨2264729, by rfl⟩ : syracuseStep 12078557 = 4529459) B4529459
theorem B1789447 : Blo 1589493 1789447 := bstep (se 1 (by rfl) ⟨1342085, by rfl⟩ : syracuseStep 1789447 = 2684171) B2684171
theorem B1814023 : Blo 1589493 1814023 := bstep (se 1 (by rfl) ⟨1360517, by rfl⟩ : syracuseStep 1814023 = 2721035) B2721035
theorem B3395105 : Blo 1589493 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B1789627 : Blo 1589493 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B8048321 : Blo 1589493 8048321 := bstep (se 2 (by rfl) ⟨3018120, by rfl⟩ : syracuseStep 8048321 = 6036241) B6036241
theorem B1814287 : Blo 1589493 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B4026145 : Blo 1589493 4026145 := bstep (se 2 (by rfl) ⟨1509804, by rfl⟩ : syracuseStep 4026145 = 3019609) B3019609
theorem B3018539 : Blo 1589493 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B12922739 : Blo 1589493 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B41308055 : Blo 1589493 41308055 := bstep (se 1 (by rfl) ⟨30981041, by rfl⟩ : syracuseStep 41308055 = 61962083) B61962083
theorem B2682895 : Blo 1589493 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B70660117 : Blo 1589493 70660117 := bstep (se 6 (by rfl) ⟨1656096, by rfl⟩ : syracuseStep 70660117 = 3312193) B3312193
theorem B12243077 : Blo 1589493 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B6205697 : Blo 1589493 6205697 := bstep (se 2 (by rfl) ⟨2327136, by rfl⟩ : syracuseStep 6205697 = 4654273) B4654273
theorem B4526351 : Blo 1589493 4526351 := bstep (se 1 (by rfl) ⟨3394763, by rfl⟩ : syracuseStep 4526351 = 6789527) B6789527
theorem B9056549 : Blo 1589493 9056549 := bstep (se 4 (by rfl) ⟨849051, by rfl⟩ : syracuseStep 9056549 = 1698103) B1698103
theorem B22933853 : Blo 1589493 22933853 := bstep (se 3 (by rfl) ⟨4300097, by rfl⟩ : syracuseStep 22933853 = 8600195) B8600195
theorem B4026743 : Blo 1589493 4026743 := bstep (se 1 (by rfl) ⟨3020057, by rfl⟩ : syracuseStep 4026743 = 6040115) B6040115
theorem B24482269 : Blo 1589493 24482269 := bstep (se 3 (by rfl) ⟨4590425, by rfl⟩ : syracuseStep 24482269 = 9180851) B9180851
theorem B2683435 : Blo 1589493 2683435 := bstep (se 1 (by rfl) ⟨2012576, by rfl⟩ : syracuseStep 2683435 = 4025153) B4025153
theorem B23245355 : Blo 1589493 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B13587011 : Blo 1589493 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B5165687 : Blo 1589493 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B3576455 : Blo 1589493 3576455 := bstep (se 1 (by rfl) ⟨2682341, by rfl⟩ : syracuseStep 3576455 = 5364683) B5364683
theorem B2683577 : Blo 1589493 2683577 := bstep (se 2 (by rfl) ⟨1006341, by rfl⟩ : syracuseStep 2683577 = 2012683) B2012683
theorem B9057005 : Blo 1589493 9057005 := bstep (se 3 (by rfl) ⟨1698188, by rfl⟩ : syracuseStep 9057005 = 3396377) B3396377
theorem B4969259 : Blo 1589493 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B3576635 : Blo 1589493 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B3019655 : Blo 1589493 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B3576761 : Blo 1589493 3576761 := bstep (se 2 (by rfl) ⟨1341285, by rfl⟩ : syracuseStep 3576761 = 2682571) B2682571
theorem B8049617 : Blo 1589493 8049617 := bstep (se 2 (by rfl) ⟨3018606, by rfl⟩ : syracuseStep 8049617 = 6037213) B6037213
theorem B13579325 : Blo 1589493 13579325 := bstep (se 3 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 13579325 = 5092247) B5092247
theorem B2012303 : Blo 1589493 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B3577103 : Blo 1589493 3577103 := bstep (se 1 (by rfl) ⟨2682827, by rfl⟩ : syracuseStep 3577103 = 5365655) B5365655
theorem B3577121 : Blo 1589493 3577121 := bstep (se 2 (by rfl) ⟨1341420, by rfl⟩ : syracuseStep 3577121 = 2682841) B2682841
theorem B3396907 : Blo 1589493 3396907 := bstep (se 1 (by rfl) ⟨2547680, by rfl⟩ : syracuseStep 3396907 = 5095361) B5095361
theorem B2684279 : Blo 1589493 2684279 := bstep (se 1 (by rfl) ⟨2013209, by rfl⟩ : syracuseStep 2684279 = 4026419) B4026419
theorem B3020179 : Blo 1589493 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B9057689 : Blo 1589493 9057689 := bstep (se 2 (by rfl) ⟨3396633, by rfl⟩ : syracuseStep 9057689 = 6793267) B6793267
theorem B3577463 : Blo 1589493 3577463 := bstep (se 1 (by rfl) ⟨2683097, by rfl⟩ : syracuseStep 3577463 = 5366195) B5366195
theorem B4527751 : Blo 1589493 4527751 := bstep (se 1 (by rfl) ⟨3395813, by rfl⟩ : syracuseStep 4527751 = 6791627) B6791627
theorem B3577643 : Blo 1589493 3577643 := bstep (se 1 (by rfl) ⟨2683232, by rfl⟩ : syracuseStep 3577643 = 5366465) B5366465
theorem B2684731 : Blo 1589493 2684731 := bstep (se 1 (by rfl) ⟨2013548, by rfl⟩ : syracuseStep 2684731 = 4027097) B4027097
theorem B5093273 : Blo 1589493 5093273 := bstep (se 2 (by rfl) ⟨1909977, by rfl⟩ : syracuseStep 5093273 = 3819955) B3819955
theorem B4528025 : Blo 1589493 4528025 := bstep (se 2 (by rfl) ⟨1698009, by rfl⟩ : syracuseStep 4528025 = 3396019) B3396019
theorem B3872783 : Blo 1589493 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B10188823 : Blo 1589493 10188823 := bstep (se 1 (by rfl) ⟨7641617, by rfl⟩ : syracuseStep 10188823 = 15283235) B15283235
theorem B24492077 : Blo 1589493 24492077 := bstep (se 3 (by rfl) ⟨4592264, by rfl⟩ : syracuseStep 24492077 = 9184529) B9184529
theorem B6035543 : Blo 1589493 6035543 := bstep (se 1 (by rfl) ⟨4526657, by rfl⟩ : syracuseStep 6035543 = 9053315) B9053315
theorem B3627143 : Blo 1589493 3627143 := bstep (se 1 (by rfl) ⟨2720357, by rfl⟩ : syracuseStep 3627143 = 5440715) B5440715
theorem B3578003 : Blo 1589493 3578003 := bstep (se 1 (by rfl) ⟨2683502, by rfl⟩ : syracuseStep 3578003 = 5367005) B5367005
theorem B3578057 : Blo 1589493 3578057 := bstep (se 2 (by rfl) ⟨1341771, by rfl⟩ : syracuseStep 3578057 = 2683543) B2683543
theorem B29006093 : Blo 1589493 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B4299275 : Blo 1589493 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B6036029 : Blo 1589493 6036029 := bstep (se 3 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 6036029 = 2263511) B2263511
theorem B11467331 : Blo 1589493 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B7641773 : Blo 1589493 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B32275205 : Blo 1589493 32275205 := bstep (se 4 (by rfl) ⟨3025800, by rfl⟩ : syracuseStep 32275205 = 6051601) B6051601
theorem B2865953 : Blo 1589493 2865953 := bstep (se 2 (by rfl) ⟨1074732, by rfl⟩ : syracuseStep 2865953 = 2149465) B2149465
theorem B3578759 : Blo 1589493 3578759 := bstep (se 1 (by rfl) ⟨2684069, by rfl⟩ : syracuseStep 3578759 = 5368139) B5368139
theorem B8051723 : Blo 1589493 8051723 := bstep (se 1 (by rfl) ⟨6038792, by rfl⟩ : syracuseStep 8051723 = 12077585) B12077585
theorem B3578939 : Blo 1589493 3578939 := bstep (se 1 (by rfl) ⟨2684204, by rfl⟩ : syracuseStep 3578939 = 5368409) B5368409
theorem B4529267 : Blo 1589493 4529267 := bstep (se 1 (by rfl) ⟨3396950, by rfl⟩ : syracuseStep 4529267 = 6793901) B6793901
theorem B8051885 : Blo 1589493 8051885 := bstep (se 3 (by rfl) ⟨1509728, by rfl⟩ : syracuseStep 8051885 = 3019457) B3019457
theorem B3579065 : Blo 1589493 3579065 := bstep (se 2 (by rfl) ⟨1342149, by rfl⟩ : syracuseStep 3579065 = 2684299) B2684299
theorem B5365007 : Blo 1589493 5365007 := bstep (se 1 (by rfl) ⟨4023755, by rfl⟩ : syracuseStep 5365007 = 8047511) B8047511
theorem B30580001 : Blo 1589493 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B3579407 : Blo 1589493 3579407 := bstep (se 1 (by rfl) ⟨2684555, by rfl⟩ : syracuseStep 3579407 = 5369111) B5369111
theorem B5365277 : Blo 1589493 5365277 := bstep (se 3 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 5365277 = 2011979) B2011979
theorem B3579425 : Blo 1589493 3579425 := bstep (se 2 (by rfl) ⟨1342284, by rfl⟩ : syracuseStep 3579425 = 2684569) B2684569
theorem B11460325 : Blo 1589493 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B627351317 : Blo 1589493 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B6201235 : Blo 1589493 6201235 := bstep (se 1 (by rfl) ⟨4650926, by rfl⟩ : syracuseStep 6201235 = 9301853) B9301853
theorem B127377305 : Blo 1589493 127377305 := bstep (se 2 (by rfl) ⟨47766489, by rfl⟩ : syracuseStep 127377305 = 95532979) B95532979
theorem B22921163 : Blo 1589493 22921163 := bstep (se 1 (by rfl) ⟨17190872, by rfl⟩ : syracuseStep 22921163 = 34381745) B34381745
theorem B8593361 : Blo 1589493 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B5365817 : Blo 1589493 5365817 := bstep (se 2 (by rfl) ⟨2012181, by rfl⟩ : syracuseStep 5365817 = 4024363) B4024363
theorem B4137131 : Blo 1589493 4137131 := bstep (se 1 (by rfl) ⟨3102848, by rfl⟩ : syracuseStep 4137131 = 6205697) B6205697
theorem B6037699 : Blo 1589493 6037699 := bstep (se 1 (by rfl) ⟨4528274, by rfl⟩ : syracuseStep 6037699 = 9056549) B9056549
theorem B1589543 : Blo 1589493 1589543 := bstep (se 1 (by rfl) ⟨1192157, by rfl⟩ : syracuseStep 1589543 = 2384315) B2384315
theorem B1589583 : Blo 1589493 1589583 := bstep (se 1 (by rfl) ⟨1192187, by rfl⟩ : syracuseStep 1589583 = 2384375) B2384375
theorem B1589599 : Blo 1589493 1589599 := bstep (se 1 (by rfl) ⟨1192199, by rfl⟩ : syracuseStep 1589599 = 2384399) B2384399
theorem B1589627 : Blo 1589493 1589627 := bstep (se 1 (by rfl) ⟨1192220, by rfl⟩ : syracuseStep 1589627 = 2384441) B2384441
theorem B5366141 : Blo 1589493 5366141 := bstep (se 3 (by rfl) ⟨1006151, by rfl⟩ : syracuseStep 5366141 = 2012303) B2012303
theorem B2384303 : Blo 1589493 2384303 := bstep (se 1 (by rfl) ⟨1788227, by rfl⟩ : syracuseStep 2384303 = 3576455) B3576455
theorem B1589679 : Blo 1589493 1589679 := bstep (se 1 (by rfl) ⟨1192259, by rfl⟩ : syracuseStep 1589679 = 2384519) B2384519
theorem B1589703 : Blo 1589493 1589703 := bstep (se 1 (by rfl) ⟨1192277, by rfl⟩ : syracuseStep 1589703 = 2384555) B2384555
theorem B1589723 : Blo 1589493 1589723 := bstep (se 1 (by rfl) ⟨1192292, by rfl⟩ : syracuseStep 1589723 = 2384585) B2384585
theorem B6038003 : Blo 1589493 6038003 := bstep (se 1 (by rfl) ⟨4528502, by rfl⟩ : syracuseStep 6038003 = 9057005) B9057005
theorem B2384393 : Blo 1589493 2384393 := bstep (se 2 (by rfl) ⟨894147, by rfl⟩ : syracuseStep 2384393 = 1788295) B1788295
theorem B2384423 : Blo 1589493 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B1589799 : Blo 1589493 1589799 := bstep (se 1 (by rfl) ⟨1192349, by rfl⟩ : syracuseStep 1589799 = 2384699) B2384699
theorem B9060923 : Blo 1589493 9060923 := bstep (se 1 (by rfl) ⟨6795692, by rfl⟩ : syracuseStep 9060923 = 13591385) B13591385
theorem B1589839 : Blo 1589493 1589839 := bstep (se 1 (by rfl) ⟨1192379, by rfl⟩ : syracuseStep 1589839 = 2384759) B2384759
theorem B1589855 : Blo 1589493 1589855 := bstep (se 1 (by rfl) ⟨1192391, by rfl⟩ : syracuseStep 1589855 = 2384783) B2384783
theorem B2384507 : Blo 1589493 2384507 := bstep (se 1 (by rfl) ⟨1788380, by rfl⟩ : syracuseStep 2384507 = 3576761) B3576761
theorem B1589883 : Blo 1589493 1589883 := bstep (se 1 (by rfl) ⟨1192412, by rfl⟩ : syracuseStep 1589883 = 2384825) B2384825
theorem B5366411 : Blo 1589493 5366411 := bstep (se 1 (by rfl) ⟨4024808, by rfl⟩ : syracuseStep 5366411 = 8049617) B8049617
theorem B1589935 : Blo 1589493 1589935 := bstep (se 1 (by rfl) ⟨1192451, by rfl⟩ : syracuseStep 1589935 = 2384903) B2384903
theorem B1589959 : Blo 1589493 1589959 := bstep (se 1 (by rfl) ⟨1192469, by rfl⟩ : syracuseStep 1589959 = 2384939) B2384939
theorem B9052883 : Blo 1589493 9052883 := bstep (se 1 (by rfl) ⟨6789662, by rfl⟩ : syracuseStep 9052883 = 13579325) B13579325
theorem B1589979 : Blo 1589493 1589979 := bstep (se 1 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 1589979 = 2384969) B2384969
theorem B2384633 : Blo 1589493 2384633 := bstep (se 2 (by rfl) ⟨894237, by rfl⟩ : syracuseStep 2384633 = 1788475) B1788475
theorem B1590055 : Blo 1589493 1590055 := bstep (se 1 (by rfl) ⟨1192541, by rfl⟩ : syracuseStep 1590055 = 2385083) B2385083
theorem B1590095 : Blo 1589493 1590095 := bstep (se 1 (by rfl) ⟨1192571, by rfl⟩ : syracuseStep 1590095 = 2385143) B2385143
theorem B2384735 : Blo 1589493 2384735 := bstep (se 1 (by rfl) ⟨1788551, by rfl⟩ : syracuseStep 2384735 = 3577103) B3577103
theorem B1590111 : Blo 1589493 1590111 := bstep (se 1 (by rfl) ⟨1192583, by rfl⟩ : syracuseStep 1590111 = 2385167) B2385167
theorem B2384747 : Blo 1589493 2384747 := bstep (se 1 (by rfl) ⟨1788560, by rfl⟩ : syracuseStep 2384747 = 3577121) B3577121
theorem B1590139 : Blo 1589493 1590139 := bstep (se 1 (by rfl) ⟨1192604, by rfl⟩ : syracuseStep 1590139 = 2385209) B2385209
theorem B1590191 : Blo 1589493 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B6038459 : Blo 1589493 6038459 := bstep (se 1 (by rfl) ⟨4528844, by rfl⟩ : syracuseStep 6038459 = 9057689) B9057689
theorem B1590215 : Blo 1589493 1590215 := bstep (se 1 (by rfl) ⟨1192661, by rfl⟩ : syracuseStep 1590215 = 2385323) B2385323
theorem B1590235 : Blo 1589493 1590235 := bstep (se 1 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 1590235 = 2385353) B2385353
theorem B1590311 : Blo 1589493 1590311 := bstep (se 1 (by rfl) ⟨1192733, by rfl⟩ : syracuseStep 1590311 = 2385467) B2385467
theorem B2384975 : Blo 1589493 2384975 := bstep (se 1 (by rfl) ⟨1788731, by rfl⟩ : syracuseStep 2384975 = 3577463) B3577463
theorem B1590351 : Blo 1589493 1590351 := bstep (se 1 (by rfl) ⟨1192763, by rfl⟩ : syracuseStep 1590351 = 2385527) B2385527
theorem B1590367 : Blo 1589493 1590367 := bstep (se 1 (by rfl) ⟨1192775, by rfl⟩ : syracuseStep 1590367 = 2385551) B2385551
theorem B1590395 : Blo 1589493 1590395 := bstep (se 1 (by rfl) ⟨1192796, by rfl⟩ : syracuseStep 1590395 = 2385593) B2385593
theorem B1590447 : Blo 1589493 1590447 := bstep (se 1 (by rfl) ⟨1192835, by rfl⟩ : syracuseStep 1590447 = 2385671) B2385671
theorem B2385095 : Blo 1589493 2385095 := bstep (se 1 (by rfl) ⟨1788821, by rfl⟩ : syracuseStep 2385095 = 3577643) B3577643
theorem B1590471 : Blo 1589493 1590471 := bstep (se 1 (by rfl) ⟨1192853, by rfl⟩ : syracuseStep 1590471 = 2385707) B2385707
theorem B1590491 : Blo 1589493 1590491 := bstep (se 1 (by rfl) ⟨1192868, by rfl⟩ : syracuseStep 1590491 = 2385737) B2385737
theorem B1590567 : Blo 1589493 1590567 := bstep (se 1 (by rfl) ⟨1192925, by rfl⟩ : syracuseStep 1590567 = 2385851) B2385851
theorem B1590607 : Blo 1589493 1590607 := bstep (se 1 (by rfl) ⟨1192955, by rfl⟩ : syracuseStep 1590607 = 2385911) B2385911
theorem B1590623 : Blo 1589493 1590623 := bstep (se 1 (by rfl) ⟨1192967, by rfl⟩ : syracuseStep 1590623 = 2385935) B2385935
theorem B2385257 : Blo 1589493 2385257 := bstep (se 2 (by rfl) ⟨894471, by rfl⟩ : syracuseStep 2385257 = 1788943) B1788943
theorem B16328051 : Blo 1589493 16328051 := bstep (se 1 (by rfl) ⟨12246038, by rfl⟩ : syracuseStep 16328051 = 24492077) B24492077
theorem B1590651 : Blo 1589493 1590651 := bstep (se 1 (by rfl) ⟨1192988, by rfl⟩ : syracuseStep 1590651 = 2385977) B2385977
theorem B4023695 : Blo 1589493 4023695 := bstep (se 1 (by rfl) ⟨3017771, by rfl⟩ : syracuseStep 4023695 = 6035543) B6035543
theorem B2418095 : Blo 1589493 2418095 := bstep (se 1 (by rfl) ⟨1813571, by rfl⟩ : syracuseStep 2418095 = 3627143) B3627143
theorem B1590703 : Blo 1589493 1590703 := bstep (se 1 (by rfl) ⟨1193027, by rfl⟩ : syracuseStep 1590703 = 2386055) B2386055
theorem B2385335 : Blo 1589493 2385335 := bstep (se 1 (by rfl) ⟨1789001, by rfl⟩ : syracuseStep 2385335 = 3578003) B3578003
theorem B1590727 : Blo 1589493 1590727 := bstep (se 1 (by rfl) ⟨1193045, by rfl⟩ : syracuseStep 1590727 = 2386091) B2386091
theorem B2385371 : Blo 1589493 2385371 := bstep (se 1 (by rfl) ⟨1789028, by rfl⟩ : syracuseStep 2385371 = 3578057) B3578057
theorem B1590747 : Blo 1589493 1590747 := bstep (se 1 (by rfl) ⟨1193060, by rfl⟩ : syracuseStep 1590747 = 2386121) B2386121
theorem B5367329 : Blo 1589493 5367329 := bstep (se 2 (by rfl) ⟨2012748, by rfl⟩ : syracuseStep 5367329 = 4025497) B4025497
theorem B1590823 : Blo 1589493 1590823 := bstep (se 1 (by rfl) ⟨1193117, by rfl⟩ : syracuseStep 1590823 = 2386235) B2386235
theorem B1590863 : Blo 1589493 1590863 := bstep (se 1 (by rfl) ⟨1193147, by rfl⟩ : syracuseStep 1590863 = 2386295) B2386295
theorem B1590879 : Blo 1589493 1590879 := bstep (se 1 (by rfl) ⟨1193159, by rfl⟩ : syracuseStep 1590879 = 2386319) B2386319
theorem B1590907 : Blo 1589493 1590907 := bstep (se 1 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 1590907 = 2386361) B2386361
theorem B20375185 : Blo 1589493 20375185 := bstep (se 2 (by rfl) ⟨7640694, by rfl⟩ : syracuseStep 20375185 = 15281389) B15281389
theorem B1590959 : Blo 1589493 1590959 := bstep (se 1 (by rfl) ⟨1193219, by rfl⟩ : syracuseStep 1590959 = 2386439) B2386439
theorem B1590983 : Blo 1589493 1590983 := bstep (se 1 (by rfl) ⟨1193237, by rfl⟩ : syracuseStep 1590983 = 2386475) B2386475
theorem B4024019 : Blo 1589493 4024019 := bstep (se 1 (by rfl) ⟨3018014, by rfl⟩ : syracuseStep 4024019 = 6036029) B6036029
theorem B7644887 : Blo 1589493 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B5367545 : Blo 1589493 5367545 := bstep (se 2 (by rfl) ⟨2012829, by rfl⟩ : syracuseStep 5367545 = 4025659) B4025659
theorem B1910635 : Blo 1589493 1910635 := bstep (se 1 (by rfl) ⟨1432976, by rfl⟩ : syracuseStep 1910635 = 2865953) B2865953
theorem B2385839 : Blo 1589493 2385839 := bstep (se 1 (by rfl) ⟨1789379, by rfl⟩ : syracuseStep 2385839 = 3578759) B3578759
theorem B5367815 : Blo 1589493 5367815 := bstep (se 1 (by rfl) ⟨4025861, by rfl⟩ : syracuseStep 5367815 = 8051723) B8051723
theorem B2385929 : Blo 1589493 2385929 := bstep (se 2 (by rfl) ⟨894723, by rfl⟩ : syracuseStep 2385929 = 1789447) B1789447
theorem B2418697 : Blo 1589493 2418697 := bstep (se 2 (by rfl) ⟨907011, by rfl⟩ : syracuseStep 2418697 = 1814023) B1814023
theorem B2385959 : Blo 1589493 2385959 := bstep (se 1 (by rfl) ⟨1789469, by rfl⟩ : syracuseStep 2385959 = 3578939) B3578939
theorem B5367923 : Blo 1589493 5367923 := bstep (se 1 (by rfl) ⟨4025942, by rfl⟩ : syracuseStep 5367923 = 8051885) B8051885
theorem B2386043 : Blo 1589493 2386043 := bstep (se 1 (by rfl) ⟨1789532, by rfl⟩ : syracuseStep 2386043 = 3579065) B3579065
theorem B2386169 : Blo 1589493 2386169 := bstep (se 2 (by rfl) ⟨894813, by rfl⟩ : syracuseStep 2386169 = 1789627) B1789627
theorem B15280433 : Blo 1589493 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B2386271 : Blo 1589493 2386271 := bstep (se 1 (by rfl) ⟨1789703, by rfl⟩ : syracuseStep 2386271 = 3579407) B3579407
theorem B2419049 : Blo 1589493 2419049 := bstep (se 2 (by rfl) ⟨907143, by rfl⟩ : syracuseStep 2419049 = 1814287) B1814287
theorem B2263403 : Blo 1589493 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B2386283 : Blo 1589493 2386283 := bstep (se 1 (by rfl) ⟨1789712, by rfl⟩ : syracuseStep 2386283 = 3579425) B3579425
theorem B5368193 : Blo 1589493 5368193 := bstep (se 2 (by rfl) ⟨2013072, by rfl⟩ : syracuseStep 5368193 = 4026145) B4026145
theorem B8268313 : Blo 1589493 8268313 := bstep (se 2 (by rfl) ⟨3100617, by rfl⟩ : syracuseStep 8268313 = 6201235) B6201235
theorem B15280775 : Blo 1589493 15280775 := bstep (se 1 (by rfl) ⟨11460581, by rfl⟩ : syracuseStep 15280775 = 22921163) B22921163
theorem B5728907 : Blo 1589493 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B13585097 : Blo 1589493 13585097 := bstep (se 2 (by rfl) ⟨5094411, by rfl⟩ : syracuseStep 13585097 = 10188823) B10188823
theorem B8162051 : Blo 1589493 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B3017567 : Blo 1589493 3017567 := bstep (se 1 (by rfl) ⟨2263175, by rfl⟩ : syracuseStep 3017567 = 4526351) B4526351
theorem B15289235 : Blo 1589493 15289235 := bstep (se 1 (by rfl) ⟨11466926, by rfl⟩ : syracuseStep 15289235 = 22933853) B22933853
theorem B3443791 : Blo 1589493 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B1789051 : Blo 1589493 1789051 := bstep (se 1 (by rfl) ⟨1341788, by rfl⟩ : syracuseStep 1789051 = 2683577) B2683577
theorem B5369003 : Blo 1589493 5369003 := bstep (se 1 (by rfl) ⟨4026752, by rfl⟩ : syracuseStep 5369003 = 8053505) B8053505
theorem B3312839 : Blo 1589493 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B8047997 : Blo 1589493 8047997 := bstep (se 3 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 8047997 = 3017999) B3017999
theorem B5729773 : Blo 1589493 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B1789519 : Blo 1589493 1789519 := bstep (se 1 (by rfl) ⟨1342139, by rfl⟩ : syracuseStep 1789519 = 2684279) B2684279
theorem B4779643 : Blo 1589493 4779643 := bstep (se 1 (by rfl) ⟨3584732, by rfl⟩ : syracuseStep 4779643 = 7169465) B7169465
theorem B6794941 : Blo 1589493 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B24489661 : Blo 1589493 24489661 := bstep (se 3 (by rfl) ⟨4591811, by rfl⟩ : syracuseStep 24489661 = 9183623) B9183623
theorem B1633991 : Blo 1589493 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B5369543 : Blo 1589493 5369543 := bstep (se 1 (by rfl) ⟨4027157, by rfl⟩ : syracuseStep 5369543 = 8054315) B8054315
theorem B2682767 : Blo 1589493 2682767 := bstep (se 1 (by rfl) ⟨2012075, by rfl⟩ : syracuseStep 2682767 = 4024151) B4024151
theorem B4026287 : Blo 1589493 4026287 := bstep (se 1 (by rfl) ⟨3019715, by rfl⟩ : syracuseStep 4026287 = 6039431) B6039431
theorem B3395515 : Blo 1589493 3395515 := bstep (se 1 (by rfl) ⟨2546636, by rfl⟩ : syracuseStep 3395515 = 5093273) B5093273
theorem B3018683 : Blo 1589493 3018683 := bstep (se 1 (by rfl) ⟨2264012, by rfl⟩ : syracuseStep 3018683 = 4528025) B4528025
theorem B11464733 : Blo 1589493 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B2683003 : Blo 1589493 2683003 := bstep (se 1 (by rfl) ⟨2012252, by rfl⟩ : syracuseStep 2683003 = 4024505) B4024505
theorem B19337395 : Blo 1589493 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B3019169 : Blo 1589493 3019169 := bstep (se 2 (by rfl) ⟨1132188, by rfl⟩ : syracuseStep 3019169 = 2264377) B2264377
theorem B21516803 : Blo 1589493 21516803 := bstep (se 1 (by rfl) ⟨16137602, by rfl⟩ : syracuseStep 21516803 = 32275205) B32275205
theorem B4026905 : Blo 1589493 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B3019511 : Blo 1589493 3019511 := bstep (se 1 (by rfl) ⟨2264633, by rfl⟩ : syracuseStep 3019511 = 4529267) B4529267
theorem B12071753 : Blo 1589493 12071753 := bstep (se 2 (by rfl) ⟨4526907, by rfl⟩ : syracuseStep 12071753 = 9053815) B9053815
theorem B3576671 : Blo 1589493 3576671 := bstep (se 1 (by rfl) ⟨2682503, by rfl⟩ : syracuseStep 3576671 = 5365007) B5365007
theorem B20386667 : Blo 1589493 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B2683867 : Blo 1589493 2683867 := bstep (se 1 (by rfl) ⟨2012900, by rfl⟩ : syracuseStep 2683867 = 4025801) B4025801
theorem B3576851 : Blo 1589493 3576851 := bstep (se 1 (by rfl) ⟨2682638, by rfl⟩ : syracuseStep 3576851 = 5365277) B5365277
theorem B2012359 : Blo 1589493 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B8615159 : Blo 1589493 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B27538703 : Blo 1589493 27538703 := bstep (se 1 (by rfl) ⟨20654027, by rfl⟩ : syracuseStep 27538703 = 41308055) B41308055
theorem B5092669 : Blo 1589493 5092669 := bstep (se 3 (by rfl) ⟨954875, by rfl⟩ : syracuseStep 5092669 = 1909751) B1909751
theorem B3577193 : Blo 1589493 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B94213489 : Blo 1589493 94213489 := bstep (se 2 (by rfl) ⟨35330058, by rfl⟩ : syracuseStep 94213489 = 70660117) B70660117
theorem B10327421 : Blo 1589493 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B2684495 : Blo 1589493 2684495 := bstep (se 1 (by rfl) ⟨2013371, by rfl⟩ : syracuseStep 2684495 = 4026743) B4026743
theorem B15496903 : Blo 1589493 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B9058007 : Blo 1589493 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B2013103 : Blo 1589493 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B3577787 : Blo 1589493 3577787 := bstep (se 1 (by rfl) ⟨2683340, by rfl⟩ : syracuseStep 3577787 = 5366681) B5366681
theorem B3577913 : Blo 1589493 3577913 := bstep (se 2 (by rfl) ⟨1341717, by rfl⟩ : syracuseStep 3577913 = 2683435) B2683435
theorem B92944745 : Blo 1589493 92944745 := bstep (se 2 (by rfl) ⟨34854279, by rfl⟩ : syracuseStep 92944745 = 69708559) B69708559
theorem B3578255 : Blo 1589493 3578255 := bstep (se 1 (by rfl) ⟨2683691, by rfl⟩ : syracuseStep 3578255 = 5367383) B5367383
theorem B3578579 : Blo 1589493 3578579 := bstep (se 1 (by rfl) ⟨2683934, by rfl⟩ : syracuseStep 3578579 = 5367869) B5367869
theorem B5364575 : Blo 1589493 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B5364737 : Blo 1589493 5364737 := bstep (se 2 (by rfl) ⟨2011776, by rfl⟩ : syracuseStep 5364737 = 4023553) B4023553
theorem B6118415 : Blo 1589493 6118415 := bstep (se 1 (by rfl) ⟨4588811, by rfl⟩ : syracuseStep 6118415 = 9177623) B9177623
theorem B4529209 : Blo 1589493 4529209 := bstep (se 2 (by rfl) ⟨1698453, by rfl⟩ : syracuseStep 4529209 = 3396907) B3396907
theorem B5094515 : Blo 1589493 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B6036727 : Blo 1589493 6036727 := bstep (se 1 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 6036727 = 9055091) B9055091
theorem B9674149 : Blo 1589493 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B6037001 : Blo 1589493 6037001 := bstep (se 2 (by rfl) ⟨2263875, by rfl⟩ : syracuseStep 6037001 = 4527751) B4527751
theorem B6037031 : Blo 1589493 6037031 := bstep (se 1 (by rfl) ⟨4527773, by rfl⟩ : syracuseStep 6037031 = 9055547) B9055547
theorem B3579515 : Blo 1589493 3579515 := bstep (se 1 (by rfl) ⟨2684636, by rfl⟩ : syracuseStep 3579515 = 5369273) B5369273
theorem B8052371 : Blo 1589493 8052371 := bstep (se 1 (by rfl) ⟨6039278, by rfl⟩ : syracuseStep 8052371 = 12078557) B12078557
theorem B3579641 : Blo 1589493 3579641 := bstep (se 2 (by rfl) ⟨1342365, by rfl⟩ : syracuseStep 3579641 = 2684731) B2684731
theorem B5365547 : Blo 1589493 5365547 := bstep (se 1 (by rfl) ⟨4024160, by rfl⟩ : syracuseStep 5365547 = 8048321) B8048321
theorem B130572101 : Blo 1589493 130572101 := bstep (se 4 (by rfl) ⟨12241134, by rfl⟩ : syracuseStep 130572101 = 24482269) B24482269
theorem B418234211 : Blo 1589493 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B84918203 : Blo 1589493 84918203 := bstep (se 1 (by rfl) ⟨63688652, by rfl⟩ : syracuseStep 84918203 = 127377305) B127377305
theorem B7643155 : Blo 1589493 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B1589535 : Blo 1589493 1589535 := bstep (se 1 (by rfl) ⟨1192151, by rfl⟩ : syracuseStep 1589535 = 2384303) B2384303
theorem B14344535 : Blo 1589493 14344535 := bstep (se 1 (by rfl) ⟨10758401, by rfl⟩ : syracuseStep 14344535 = 21516803) B21516803
theorem B1589595 : Blo 1589493 1589595 := bstep (se 1 (by rfl) ⟨1192196, by rfl⟩ : syracuseStep 1589595 = 2384393) B2384393
theorem B1589615 : Blo 1589493 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B1589671 : Blo 1589493 1589671 := bstep (se 1 (by rfl) ⟨1192253, by rfl⟩ : syracuseStep 1589671 = 2384507) B2384507
theorem B1589755 : Blo 1589493 1589755 := bstep (se 1 (by rfl) ⟨1192316, by rfl⟩ : syracuseStep 1589755 = 2384633) B2384633
theorem B2384447 : Blo 1589493 2384447 := bstep (se 1 (by rfl) ⟨1788335, by rfl⟩ : syracuseStep 2384447 = 3576671) B3576671
theorem B1589823 : Blo 1589493 1589823 := bstep (se 1 (by rfl) ⟨1192367, by rfl⟩ : syracuseStep 1589823 = 2384735) B2384735
theorem B1589831 : Blo 1589493 1589831 := bstep (se 1 (by rfl) ⟨1192373, by rfl⟩ : syracuseStep 1589831 = 2384747) B2384747
theorem B13591111 : Blo 1589493 13591111 := bstep (se 1 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 13591111 = 20386667) B20386667
theorem B2384567 : Blo 1589493 2384567 := bstep (se 1 (by rfl) ⟨1788425, by rfl⟩ : syracuseStep 2384567 = 3576851) B3576851
theorem B1589983 : Blo 1589493 1589983 := bstep (se 1 (by rfl) ⟨1192487, by rfl⟩ : syracuseStep 1589983 = 2384975) B2384975
theorem B1590063 : Blo 1589493 1590063 := bstep (se 1 (by rfl) ⟨1192547, by rfl⟩ : syracuseStep 1590063 = 2385095) B2385095
theorem B5743439 : Blo 1589493 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B18359135 : Blo 1589493 18359135 := bstep (se 1 (by rfl) ⟨13769351, by rfl⟩ : syracuseStep 18359135 = 27538703) B27538703
theorem B2384795 : Blo 1589493 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B1590171 : Blo 1589493 1590171 := bstep (se 1 (by rfl) ⟨1192628, by rfl⟩ : syracuseStep 1590171 = 2385257) B2385257
theorem B1590223 : Blo 1589493 1590223 := bstep (se 1 (by rfl) ⟨1192667, by rfl⟩ : syracuseStep 1590223 = 2385335) B2385335
theorem B1590247 : Blo 1589493 1590247 := bstep (se 1 (by rfl) ⟨1192685, by rfl⟩ : syracuseStep 1590247 = 2385371) B2385371
theorem B6038671 : Blo 1589493 6038671 := bstep (se 1 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 6038671 = 9058007) B9058007
theorem B5096591 : Blo 1589493 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B1590559 : Blo 1589493 1590559 := bstep (se 1 (by rfl) ⟨1192919, by rfl⟩ : syracuseStep 1590559 = 2385839) B2385839
theorem B2385191 : Blo 1589493 2385191 := bstep (se 1 (by rfl) ⟨1788893, by rfl⟩ : syracuseStep 2385191 = 3577787) B3577787
theorem B1590619 : Blo 1589493 1590619 := bstep (se 1 (by rfl) ⟨1192964, by rfl⟩ : syracuseStep 1590619 = 2385929) B2385929
theorem B1590639 : Blo 1589493 1590639 := bstep (se 1 (by rfl) ⟨1192979, by rfl⟩ : syracuseStep 1590639 = 2385959) B2385959
theorem B2385275 : Blo 1589493 2385275 := bstep (se 1 (by rfl) ⟨1788956, by rfl⟩ : syracuseStep 2385275 = 3577913) B3577913
theorem B6038945 : Blo 1589493 6038945 := bstep (se 2 (by rfl) ⟨2264604, by rfl⟩ : syracuseStep 6038945 = 4529209) B4529209
theorem B1590695 : Blo 1589493 1590695 := bstep (se 1 (by rfl) ⟨1193021, by rfl⟩ : syracuseStep 1590695 = 2386043) B2386043
theorem B2385401 : Blo 1589493 2385401 := bstep (se 2 (by rfl) ⟨894525, by rfl⟩ : syracuseStep 2385401 = 1789051) B1789051
theorem B1590779 : Blo 1589493 1590779 := bstep (se 1 (by rfl) ⟨1193084, by rfl⟩ : syracuseStep 1590779 = 2386169) B2386169
theorem B1590847 : Blo 1589493 1590847 := bstep (se 1 (by rfl) ⟨1193135, by rfl⟩ : syracuseStep 1590847 = 2386271) B2386271
theorem B1590855 : Blo 1589493 1590855 := bstep (se 1 (by rfl) ⟨1193141, by rfl⟩ : syracuseStep 1590855 = 2386283) B2386283
theorem B2385503 : Blo 1589493 2385503 := bstep (se 1 (by rfl) ⟨1789127, by rfl⟩ : syracuseStep 2385503 = 3578255) B3578255
theorem B2385719 : Blo 1589493 2385719 := bstep (se 1 (by rfl) ⟨1789289, by rfl⟩ : syracuseStep 2385719 = 3578579) B3578579
theorem B125617985 : Blo 1589493 125617985 := bstep (se 2 (by rfl) ⟨47106744, by rfl⟩ : syracuseStep 125617985 = 94213489) B94213489
theorem B10192823 : Blo 1589493 10192823 := bstep (se 1 (by rfl) ⟨7644617, by rfl⟩ : syracuseStep 10192823 = 15289235) B15289235
theorem B2386025 : Blo 1589493 2386025 := bstep (se 2 (by rfl) ⟨894759, by rfl⟩ : syracuseStep 2386025 = 1789519) B1789519
theorem B27166913 : Blo 1589493 27166913 := bstep (se 2 (by rfl) ⟨10187592, by rfl⟩ : syracuseStep 27166913 = 20375185) B20375185
theorem B20662537 : Blo 1589493 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B4024667 : Blo 1589493 4024667 := bstep (se 1 (by rfl) ⟨3018500, by rfl⟩ : syracuseStep 4024667 = 6037001) B6037001
theorem B4024687 : Blo 1589493 4024687 := bstep (se 1 (by rfl) ⟨3018515, by rfl⟩ : syracuseStep 4024687 = 6037031) B6037031
theorem B2386343 : Blo 1589493 2386343 := bstep (se 1 (by rfl) ⟨1789757, by rfl⟩ : syracuseStep 2386343 = 3579515) B3579515
theorem B5368247 : Blo 1589493 5368247 := bstep (se 1 (by rfl) ⟨4026185, by rfl⟩ : syracuseStep 5368247 = 8052371) B8052371
theorem B2386427 : Blo 1589493 2386427 := bstep (se 1 (by rfl) ⟨1789820, by rfl⟩ : syracuseStep 2386427 = 3579641) B3579641
theorem B1788511 : Blo 1589493 1788511 := bstep (se 1 (by rfl) ⟨1341383, by rfl⟩ : syracuseStep 1788511 = 2682767) B2682767
theorem B25783193 : Blo 1589493 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B4025335 : Blo 1589493 4025335 := bstep (se 1 (by rfl) ⟨3019001, by rfl⟩ : syracuseStep 4025335 = 6038003) B6038003
theorem B6040615 : Blo 1589493 6040615 := bstep (se 1 (by rfl) ⟨4530461, by rfl⟩ : syracuseStep 6040615 = 9060923) B9060923
theorem B8047835 : Blo 1589493 8047835 := bstep (se 1 (by rfl) ⟨6035876, by rfl⟩ : syracuseStep 8047835 = 12071753) B12071753
theorem B4025639 : Blo 1589493 4025639 := bstep (se 1 (by rfl) ⟨3019229, by rfl⟩ : syracuseStep 4025639 = 6038459) B6038459
theorem B6884947 : Blo 1589493 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B2682463 : Blo 1589493 2682463 := bstep (se 1 (by rfl) ⟨2011847, by rfl⟩ : syracuseStep 2682463 = 4023695) B4023695
theorem B1789663 : Blo 1589493 1789663 := bstep (se 1 (by rfl) ⟨1342247, by rfl⟩ : syracuseStep 1789663 = 2684495) B2684495
theorem B2682679 : Blo 1589493 2682679 := bstep (se 1 (by rfl) ⟨2012009, by rfl⟩ : syracuseStep 2682679 = 4024019) B4024019
theorem B4591721 : Blo 1589493 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B10186955 : Blo 1589493 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B2683145 : Blo 1589493 2683145 := bstep (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) B2012359
theorem B8048969 : Blo 1589493 8048969 := bstep (se 2 (by rfl) ⟨3018363, by rfl⟩ : syracuseStep 8048969 = 6036727) B6036727
theorem B10187183 : Blo 1589493 10187183 := bstep (se 1 (by rfl) ⟨7640387, by rfl⟩ : syracuseStep 10187183 = 15280775) B15280775
theorem B9056731 : Blo 1589493 9056731 := bstep (se 1 (by rfl) ⟨6792548, by rfl⟩ : syracuseStep 9056731 = 13585097) B13585097
theorem B12898865 : Blo 1589493 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B3576383 : Blo 1589493 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B2011711 : Blo 1589493 2011711 := bstep (se 1 (by rfl) ⟨1508783, by rfl⟩ : syracuseStep 2011711 = 3017567) B3017567
theorem B7639697 : Blo 1589493 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B3576491 : Blo 1589493 3576491 := bstep (se 1 (by rfl) ⟨2682368, by rfl⟩ : syracuseStep 3576491 = 5364737) B5364737
theorem B3396343 : Blo 1589493 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B2208559 : Blo 1589493 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B3577031 : Blo 1589493 3577031 := bstep (se 1 (by rfl) ⟨2682773, by rfl⟩ : syracuseStep 3577031 = 5365547) B5365547
theorem B2684137 : Blo 1589493 2684137 := bstep (se 2 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 2684137 = 2013103) B2013103
theorem B4527353 : Blo 1589493 4527353 := bstep (se 2 (by rfl) ⟨1697757, by rfl⟩ : syracuseStep 4527353 = 3395515) B3395515
theorem B2684191 : Blo 1589493 2684191 := bstep (se 1 (by rfl) ⟨2013143, by rfl⟩ : syracuseStep 2684191 = 4026287) B4026287
theorem B2012455 : Blo 1589493 2012455 := bstep (se 1 (by rfl) ⟨1509341, by rfl⟩ : syracuseStep 2012455 = 3018683) B3018683
theorem B56612135 : Blo 1589493 56612135 := bstep (se 1 (by rfl) ⟨42459101, by rfl⟩ : syracuseStep 56612135 = 84918203) B84918203
theorem B3224929 : Blo 1589493 3224929 := bstep (se 2 (by rfl) ⟨1209348, by rfl⟩ : syracuseStep 3224929 = 2418697) B2418697
theorem B3577211 : Blo 1589493 3577211 := bstep (se 1 (by rfl) ⟨2682908, by rfl⟩ : syracuseStep 3577211 = 5365817) B5365817
theorem B2758087 : Blo 1589493 2758087 := bstep (se 1 (by rfl) ⟨2068565, by rfl⟩ : syracuseStep 2758087 = 4137131) B4137131
theorem B3577337 : Blo 1589493 3577337 := bstep (se 2 (by rfl) ⟨1341501, by rfl⟩ : syracuseStep 3577337 = 2683003) B2683003
theorem B3577427 : Blo 1589493 3577427 := bstep (se 1 (by rfl) ⟨2683070, by rfl⟩ : syracuseStep 3577427 = 5366141) B5366141
theorem B8050265 : Blo 1589493 8050265 := bstep (se 2 (by rfl) ⟨3018849, by rfl⟩ : syracuseStep 8050265 = 6037699) B6037699
theorem B2012779 : Blo 1589493 2012779 := bstep (se 1 (by rfl) ⟨1509584, by rfl⟩ : syracuseStep 2012779 = 3019169) B3019169
theorem B2684603 : Blo 1589493 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B3577607 : Blo 1589493 3577607 := bstep (se 1 (by rfl) ⟨2683205, by rfl⟩ : syracuseStep 3577607 = 5366411) B5366411
theorem B6035255 : Blo 1589493 6035255 := bstep (se 1 (by rfl) ⟨4526441, by rfl⟩ : syracuseStep 6035255 = 9052883) B9052883
theorem B2013007 : Blo 1589493 2013007 := bstep (se 1 (by rfl) ⟨1509755, by rfl⟩ : syracuseStep 2013007 = 3019511) B3019511
theorem B11024417 : Blo 1589493 11024417 := bstep (se 2 (by rfl) ⟨4134156, by rfl⟩ : syracuseStep 11024417 = 8268313) B8268313
theorem B10885367 : Blo 1589493 10885367 := bstep (se 1 (by rfl) ⟨8164025, by rfl⟩ : syracuseStep 10885367 = 16328051) B16328051
theorem B6035741 : Blo 1589493 6035741 := bstep (se 3 (by rfl) ⟨1131701, by rfl⟩ : syracuseStep 6035741 = 2263403) B2263403
theorem B1612063 : Blo 1589493 1612063 := bstep (se 1 (by rfl) ⟨1209047, by rfl⟩ : syracuseStep 1612063 = 2418095) B2418095
theorem B3578219 : Blo 1589493 3578219 := bstep (se 1 (by rfl) ⟨2683664, by rfl⟩ : syracuseStep 3578219 = 5367329) B5367329
theorem B3578363 : Blo 1589493 3578363 := bstep (se 1 (by rfl) ⟨2683772, by rfl⟩ : syracuseStep 3578363 = 5367545) B5367545
theorem B3578489 : Blo 1589493 3578489 := bstep (se 2 (by rfl) ⟨1341933, by rfl⟩ : syracuseStep 3578489 = 2683867) B2683867
theorem B3578543 : Blo 1589493 3578543 := bstep (se 1 (by rfl) ⟨2683907, by rfl⟩ : syracuseStep 3578543 = 5367815) B5367815
theorem B3578615 : Blo 1589493 3578615 := bstep (se 1 (by rfl) ⟨2683961, by rfl⟩ : syracuseStep 3578615 = 5367923) B5367923
theorem B61963163 : Blo 1589493 61963163 := bstep (se 1 (by rfl) ⟨46472372, by rfl⟩ : syracuseStep 61963163 = 92944745) B92944745
theorem B1612699 : Blo 1589493 1612699 := bstep (se 1 (by rfl) ⟨1209524, by rfl⟩ : syracuseStep 1612699 = 2419049) B2419049
theorem B3578795 : Blo 1589493 3578795 := bstep (se 1 (by rfl) ⟨2684096, by rfl⟩ : syracuseStep 3578795 = 5368193) B5368193
theorem B15277085 : Blo 1589493 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B6790225 : Blo 1589493 6790225 := bstep (se 2 (by rfl) ⟨2546334, by rfl⟩ : syracuseStep 6790225 = 5092669) B5092669
theorem B4357309 : Blo 1589493 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B10190053 : Blo 1589493 10190053 := bstep (se 4 (by rfl) ⟨955317, by rfl⟩ : syracuseStep 10190053 = 1910635) B1910635
theorem B21765469 : Blo 1589493 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B4078943 : Blo 1589493 4078943 := bstep (se 1 (by rfl) ⟨3059207, by rfl⟩ : syracuseStep 4078943 = 6118415) B6118415
theorem B3579335 : Blo 1589493 3579335 := bstep (se 1 (by rfl) ⟨2684501, by rfl⟩ : syracuseStep 3579335 = 5369003) B5369003
theorem B6372857 : Blo 1589493 6372857 := bstep (se 2 (by rfl) ⟨2389821, by rfl⟩ : syracuseStep 6372857 = 4779643) B4779643
theorem B9059921 : Blo 1589493 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B32652881 : Blo 1589493 32652881 := bstep (se 2 (by rfl) ⟨12244830, by rfl⟩ : syracuseStep 32652881 = 24489661) B24489661
theorem B5365331 : Blo 1589493 5365331 := bstep (se 1 (by rfl) ⟨4023998, by rfl⟩ : syracuseStep 5365331 = 8047997) B8047997
theorem B3579695 : Blo 1589493 3579695 := bstep (se 1 (by rfl) ⟨2684771, by rfl⟩ : syracuseStep 3579695 = 5369543) B5369543
theorem B87048067 : Blo 1589493 87048067 := bstep (se 1 (by rfl) ⟨65286050, by rfl⟩ : syracuseStep 87048067 = 130572101) B130572101
theorem B278822807 : Blo 1589493 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B10190873 : Blo 1589493 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B6791303 : Blo 1589493 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B5365979 : Blo 1589493 5365979 := bstep (se 1 (by rfl) ⟨4024484, by rfl⟩ : syracuseStep 5365979 = 8048969) B8048969
theorem B6791455 : Blo 1589493 6791455 := bstep (se 1 (by rfl) ⟨5093591, by rfl⟩ : syracuseStep 6791455 = 10187183) B10187183
theorem B27550049 : Blo 1589493 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B2384255 : Blo 1589493 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B1589631 : Blo 1589493 1589631 := bstep (se 1 (by rfl) ⟨1192223, by rfl⟩ : syracuseStep 1589631 = 2384447) B2384447
theorem B2384327 : Blo 1589493 2384327 := bstep (se 1 (by rfl) ⟨1788245, by rfl⟩ : syracuseStep 2384327 = 3576491) B3576491
theorem B1589711 : Blo 1589493 1589711 := bstep (se 1 (by rfl) ⟨1192283, by rfl⟩ : syracuseStep 1589711 = 2384567) B2384567
theorem B5366249 : Blo 1589493 5366249 := bstep (se 2 (by rfl) ⟨2012343, by rfl⟩ : syracuseStep 5366249 = 4024687) B4024687
theorem B12239423 : Blo 1589493 12239423 := bstep (se 1 (by rfl) ⟨9179567, by rfl⟩ : syracuseStep 12239423 = 18359135) B18359135
theorem B1589863 : Blo 1589493 1589863 := bstep (se 1 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 1589863 = 2384795) B2384795
theorem B12075641 : Blo 1589493 12075641 := bstep (se 2 (by rfl) ⟨4528365, by rfl⟩ : syracuseStep 12075641 = 9056731) B9056731
theorem B18121481 : Blo 1589493 18121481 := bstep (se 2 (by rfl) ⟨6795555, by rfl⟩ : syracuseStep 18121481 = 13591111) B13591111
theorem B2384681 : Blo 1589493 2384681 := bstep (se 2 (by rfl) ⟨894255, by rfl⟩ : syracuseStep 2384681 = 1788511) B1788511
theorem B2384687 : Blo 1589493 2384687 := bstep (se 1 (by rfl) ⟨1788515, by rfl⟩ : syracuseStep 2384687 = 3577031) B3577031
theorem B1590127 : Blo 1589493 1590127 := bstep (se 1 (by rfl) ⟨1192595, by rfl⟩ : syracuseStep 1590127 = 2385191) B2385191
theorem B2384807 : Blo 1589493 2384807 := bstep (se 1 (by rfl) ⟨1788605, by rfl⟩ : syracuseStep 2384807 = 3577211) B3577211
theorem B1590183 : Blo 1589493 1590183 := bstep (se 1 (by rfl) ⟨1192637, by rfl⟩ : syracuseStep 1590183 = 2385275) B2385275
theorem B2384891 : Blo 1589493 2384891 := bstep (se 1 (by rfl) ⟨1788668, by rfl⟩ : syracuseStep 2384891 = 3577337) B3577337
theorem B1590267 : Blo 1589493 1590267 := bstep (se 1 (by rfl) ⟨1192700, by rfl⟩ : syracuseStep 1590267 = 2385401) B2385401
theorem B2384951 : Blo 1589493 2384951 := bstep (se 1 (by rfl) ⟨1788713, by rfl⟩ : syracuseStep 2384951 = 3577427) B3577427
theorem B5366843 : Blo 1589493 5366843 := bstep (se 1 (by rfl) ⟨4025132, by rfl⟩ : syracuseStep 5366843 = 8050265) B8050265
theorem B1590335 : Blo 1589493 1590335 := bstep (se 1 (by rfl) ⟨1192751, by rfl⟩ : syracuseStep 1590335 = 2385503) B2385503
theorem B2385071 : Blo 1589493 2385071 := bstep (se 1 (by rfl) ⟨1788803, by rfl⟩ : syracuseStep 2385071 = 3577607) B3577607
theorem B4023503 : Blo 1589493 4023503 := bstep (se 1 (by rfl) ⟨3017627, by rfl⟩ : syracuseStep 4023503 = 6035255) B6035255
theorem B1590479 : Blo 1589493 1590479 := bstep (se 1 (by rfl) ⟨1192859, by rfl⟩ : syracuseStep 1590479 = 2385719) B2385719
theorem B5367113 : Blo 1589493 5367113 := bstep (se 2 (by rfl) ⟨2012667, by rfl⟩ : syracuseStep 5367113 = 4025335) B4025335
theorem B8054153 : Blo 1589493 8054153 := bstep (se 2 (by rfl) ⟨3020307, by rfl⟩ : syracuseStep 8054153 = 6040615) B6040615
theorem B1590683 : Blo 1589493 1590683 := bstep (se 1 (by rfl) ⟨1193012, by rfl⟩ : syracuseStep 1590683 = 2386025) B2386025
theorem B9053633 : Blo 1589493 9053633 := bstep (se 2 (by rfl) ⟨3395112, by rfl⟩ : syracuseStep 9053633 = 6790225) B6790225
theorem B4023827 : Blo 1589493 4023827 := bstep (se 1 (by rfl) ⟨3017870, by rfl⟩ : syracuseStep 4023827 = 6035741) B6035741
theorem B2385479 : Blo 1589493 2385479 := bstep (se 1 (by rfl) ⟨1789109, by rfl⟩ : syracuseStep 2385479 = 3578219) B3578219
theorem B5809745 : Blo 1589493 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B1590895 : Blo 1589493 1590895 := bstep (se 1 (by rfl) ⟨1193171, by rfl⟩ : syracuseStep 1590895 = 2386343) B2386343
theorem B2385575 : Blo 1589493 2385575 := bstep (se 1 (by rfl) ⟨1789181, by rfl⟩ : syracuseStep 2385575 = 3578363) B3578363
theorem B1590951 : Blo 1589493 1590951 := bstep (se 1 (by rfl) ⟨1193213, by rfl⟩ : syracuseStep 1590951 = 2386427) B2386427
theorem B2385659 : Blo 1589493 2385659 := bstep (se 1 (by rfl) ⟨1789244, by rfl⟩ : syracuseStep 2385659 = 3578489) B3578489
theorem B2385695 : Blo 1589493 2385695 := bstep (se 1 (by rfl) ⟨1789271, by rfl⟩ : syracuseStep 2385695 = 3578543) B3578543
theorem B2385743 : Blo 1589493 2385743 := bstep (se 1 (by rfl) ⟨1789307, by rfl⟩ : syracuseStep 2385743 = 3578615) B3578615
theorem B17188795 : Blo 1589493 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B2385863 : Blo 1589493 2385863 := bstep (se 1 (by rfl) ⟨1789397, by rfl⟩ : syracuseStep 2385863 = 3578795) B3578795
theorem B10184723 : Blo 1589493 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B2386217 : Blo 1589493 2386217 := bstep (se 2 (by rfl) ⟨894831, by rfl⟩ : syracuseStep 2386217 = 1789663) B1789663
theorem B2386223 : Blo 1589493 2386223 := bstep (se 1 (by rfl) ⟨1789667, by rfl⟩ : syracuseStep 2386223 = 3579335) B3579335
theorem B6039947 : Blo 1589493 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B21768587 : Blo 1589493 21768587 := bstep (se 1 (by rfl) ⟨16326440, by rfl⟩ : syracuseStep 21768587 = 32652881) B32652881
theorem B2386463 : Blo 1589493 2386463 := bstep (se 1 (by rfl) ⟨1789847, by rfl⟩ : syracuseStep 2386463 = 3579695) B3579695
theorem B1788763 : Blo 1589493 1788763 := bstep (se 1 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 1788763 = 2683145) B2683145
theorem B9563023 : Blo 1589493 9563023 := bstep (se 1 (by rfl) ⟨7172267, by rfl⟩ : syracuseStep 9563023 = 14344535) B14344535
theorem B2149417 : Blo 1589493 2149417 := bstep (se 2 (by rfl) ⟨806031, by rfl⟩ : syracuseStep 2149417 = 1612063) B1612063
theorem B3828959 : Blo 1589493 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B2682281 : Blo 1589493 2682281 := bstep (se 2 (by rfl) ⟨1005855, by rfl⟩ : syracuseStep 2682281 = 2011711) B2011711
theorem B150965693 : Blo 1589493 150965693 := bstep (se 3 (by rfl) ⟨28306067, by rfl⟩ : syracuseStep 150965693 = 56612135) B56612135
theorem B3018235 : Blo 1589493 3018235 := bstep (se 1 (by rfl) ⟨2263676, by rfl⟩ : syracuseStep 3018235 = 4527353) B4527353
theorem B4025963 : Blo 1589493 4025963 := bstep (se 1 (by rfl) ⟨3019472, by rfl⟩ : syracuseStep 4025963 = 6038945) B6038945
theorem B2944745 : Blo 1589493 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B1789735 : Blo 1589493 1789735 := bstep (se 1 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 1789735 = 2684603) B2684603
theorem B6795215 : Blo 1589493 6795215 := bstep (se 1 (by rfl) ⟨5096411, by rfl⟩ : syracuseStep 6795215 = 10192823) B10192823
theorem B2683111 : Blo 1589493 2683111 := bstep (se 1 (by rfl) ⟨2012333, by rfl⟩ : syracuseStep 2683111 = 4024667) B4024667
theorem B13586737 : Blo 1589493 13586737 := bstep (se 2 (by rfl) ⟨5095026, by rfl⟩ : syracuseStep 13586737 = 10190053) B10190053
theorem B2683273 : Blo 1589493 2683273 := bstep (se 2 (by rfl) ⟨1006227, by rfl⟩ : syracuseStep 2683273 = 2012455) B2012455
theorem B29020625 : Blo 1589493 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B41308775 : Blo 1589493 41308775 := bstep (se 1 (by rfl) ⟨30981581, by rfl⟩ : syracuseStep 41308775 = 61963163) B61963163
theorem B9179929 : Blo 1589493 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B3576617 : Blo 1589493 3576617 := bstep (se 2 (by rfl) ⟨1341231, by rfl⟩ : syracuseStep 3576617 = 2682463) B2682463
theorem B2683705 : Blo 1589493 2683705 := bstep (se 2 (by rfl) ⟨1006389, by rfl⟩ : syracuseStep 2683705 = 2012779) B2012779
theorem B2683759 : Blo 1589493 2683759 := bstep (se 1 (by rfl) ⟨2012819, by rfl⟩ : syracuseStep 2683759 = 4025639) B4025639
theorem B4248571 : Blo 1589493 4248571 := bstep (se 1 (by rfl) ⟨3186428, by rfl⟩ : syracuseStep 4248571 = 6372857) B6372857
theorem B3576887 : Blo 1589493 3576887 := bstep (se 1 (by rfl) ⟨2682665, by rfl⟩ : syracuseStep 3576887 = 5365331) B5365331
theorem B3576905 : Blo 1589493 3576905 := bstep (se 2 (by rfl) ⟨1341339, by rfl⟩ : syracuseStep 3576905 = 2682679) B2682679
theorem B2684009 : Blo 1589493 2684009 := bstep (se 2 (by rfl) ⟨1006503, by rfl⟩ : syracuseStep 2684009 = 2013007) B2013007
theorem B185881871 : Blo 1589493 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B3061147 : Blo 1589493 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B29398445 : Blo 1589493 29398445 := bstep (se 3 (by rfl) ⟨5512208, by rfl⟩ : syracuseStep 29398445 = 11024417) B11024417
theorem B8599243 : Blo 1589493 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B5093131 : Blo 1589493 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B3397727 : Blo 1589493 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B4528457 : Blo 1589493 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B83745323 : Blo 1589493 83745323 := bstep (se 1 (by rfl) ⟨62808992, by rfl⟩ : syracuseStep 83745323 = 125617985) B125617985
theorem B18111275 : Blo 1589493 18111275 := bstep (se 1 (by rfl) ⟨13583456, by rfl⟩ : syracuseStep 18111275 = 27166913) B27166913
theorem B7256911 : Blo 1589493 7256911 := bstep (se 1 (by rfl) ⟨5442683, by rfl⟩ : syracuseStep 7256911 = 10885367) B10885367
theorem B8051561 : Blo 1589493 8051561 := bstep (se 2 (by rfl) ⟨3019335, by rfl⟩ : syracuseStep 8051561 = 6038671) B6038671
theorem B3578831 : Blo 1589493 3578831 := bstep (se 1 (by rfl) ⟨2684123, by rfl⟩ : syracuseStep 3578831 = 5368247) B5368247
theorem B3578849 : Blo 1589493 3578849 := bstep (se 2 (by rfl) ⟨1342068, by rfl⟩ : syracuseStep 3578849 = 2684137) B2684137
theorem B3578921 : Blo 1589493 3578921 := bstep (se 2 (by rfl) ⟨1342095, by rfl⟩ : syracuseStep 3578921 = 2684191) B2684191
theorem B4299905 : Blo 1589493 4299905 := bstep (se 2 (by rfl) ⟨1612464, by rfl⟩ : syracuseStep 4299905 = 3224929) B3224929
theorem B3677449 : Blo 1589493 3677449 := bstep (se 2 (by rfl) ⟨1379043, by rfl⟩ : syracuseStep 3677449 = 2758087) B2758087
theorem B8601061 : Blo 1589493 8601061 := bstep (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) B1612699
theorem B5365223 : Blo 1589493 5365223 := bstep (se 1 (by rfl) ⟨4023917, by rfl⟩ : syracuseStep 5365223 = 8047835) B8047835
theorem B2719295 : Blo 1589493 2719295 := bstep (se 1 (by rfl) ⟨2039471, by rfl⟩ : syracuseStep 2719295 = 4078943) B4078943
theorem B116064089 : Blo 1589493 116064089 := bstep (se 2 (by rfl) ⟨43524033, by rfl⟩ : syracuseStep 116064089 = 87048067) B87048067
theorem B9060605 : Blo 1589493 9060605 := bstep (se 3 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 9060605 = 3397727) B3397727
theorem B1589503 : Blo 1589493 1589503 := bstep (se 1 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 1589503 = 2384255) B2384255
theorem B1589551 : Blo 1589493 1589551 := bstep (se 1 (by rfl) ⟨1192163, by rfl⟩ : syracuseStep 1589551 = 2384327) B2384327
theorem B8159615 : Blo 1589493 8159615 := bstep (se 1 (by rfl) ⟨6119711, by rfl⟩ : syracuseStep 8159615 = 12239423) B12239423
theorem B2384411 : Blo 1589493 2384411 := bstep (se 1 (by rfl) ⟨1788308, by rfl⟩ : syracuseStep 2384411 = 3576617) B3576617
theorem B1589787 : Blo 1589493 1589787 := bstep (se 1 (by rfl) ⟨1192340, by rfl⟩ : syracuseStep 1589787 = 2384681) B2384681
theorem B1589791 : Blo 1589493 1589791 := bstep (se 1 (by rfl) ⟨1192343, by rfl⟩ : syracuseStep 1589791 = 2384687) B2384687
theorem B1589871 : Blo 1589493 1589871 := bstep (se 1 (by rfl) ⟨1192403, by rfl⟩ : syracuseStep 1589871 = 2384807) B2384807
theorem B1589927 : Blo 1589493 1589927 := bstep (se 1 (by rfl) ⟨1192445, by rfl⟩ : syracuseStep 1589927 = 2384891) B2384891
theorem B2384591 : Blo 1589493 2384591 := bstep (se 1 (by rfl) ⟨1788443, by rfl⟩ : syracuseStep 2384591 = 3576887) B3576887
theorem B1589967 : Blo 1589493 1589967 := bstep (se 1 (by rfl) ⟨1192475, by rfl⟩ : syracuseStep 1589967 = 2384951) B2384951
theorem B2384603 : Blo 1589493 2384603 := bstep (se 1 (by rfl) ⟨1788452, by rfl⟩ : syracuseStep 2384603 = 3576905) B3576905
theorem B1590047 : Blo 1589493 1590047 := bstep (se 1 (by rfl) ⟨1192535, by rfl⟩ : syracuseStep 1590047 = 2385071) B2385071
theorem B123921247 : Blo 1589493 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B73466797 : Blo 1589493 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B12239905 : Blo 1589493 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B1590319 : Blo 1589493 1590319 := bstep (se 1 (by rfl) ⟨1192739, by rfl⟩ : syracuseStep 1590319 = 2385479) B2385479
theorem B9675881 : Blo 1589493 9675881 := bstep (se 2 (by rfl) ⟨3628455, by rfl⟩ : syracuseStep 9675881 = 7256911) B7256911
theorem B1590383 : Blo 1589493 1590383 := bstep (se 1 (by rfl) ⟨1192787, by rfl⟩ : syracuseStep 1590383 = 2385575) B2385575
theorem B2385017 : Blo 1589493 2385017 := bstep (se 2 (by rfl) ⟨894381, by rfl⟩ : syracuseStep 2385017 = 1788763) B1788763
theorem B1590439 : Blo 1589493 1590439 := bstep (se 1 (by rfl) ⟨1192829, by rfl⟩ : syracuseStep 1590439 = 2385659) B2385659
theorem B1590463 : Blo 1589493 1590463 := bstep (se 1 (by rfl) ⟨1192847, by rfl⟩ : syracuseStep 1590463 = 2385695) B2385695
theorem B1590495 : Blo 1589493 1590495 := bstep (se 1 (by rfl) ⟨1192871, by rfl⟩ : syracuseStep 1590495 = 2385743) B2385743
theorem B1590575 : Blo 1589493 1590575 := bstep (se 1 (by rfl) ⟨1192931, by rfl⟩ : syracuseStep 1590575 = 2385863) B2385863
theorem B1590811 : Blo 1589493 1590811 := bstep (se 1 (by rfl) ⟨1193108, by rfl⟩ : syracuseStep 1590811 = 2386217) B2386217
theorem B1590815 : Blo 1589493 1590815 := bstep (se 1 (by rfl) ⟨1193111, by rfl⟩ : syracuseStep 1590815 = 2386223) B2386223
theorem B15492653 : Blo 1589493 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B1590975 : Blo 1589493 1590975 := bstep (se 1 (by rfl) ⟨1193231, by rfl⟩ : syracuseStep 1590975 = 2386463) B2386463
theorem B55830215 : Blo 1589493 55830215 := bstep (se 1 (by rfl) ⟨41872661, by rfl⟩ : syracuseStep 55830215 = 83745323) B83745323
theorem B4081529 : Blo 1589493 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B5367707 : Blo 1589493 5367707 := bstep (se 1 (by rfl) ⟨4025780, by rfl⟩ : syracuseStep 5367707 = 8051561) B8051561
theorem B2385887 : Blo 1589493 2385887 := bstep (se 1 (by rfl) ⟨1789415, by rfl⟩ : syracuseStep 2385887 = 3578831) B3578831
theorem B2385899 : Blo 1589493 2385899 := bstep (se 1 (by rfl) ⟨1789424, by rfl⟩ : syracuseStep 2385899 = 3578849) B3578849
theorem B4024313 : Blo 1589493 4024313 := bstep (se 2 (by rfl) ⟨1509117, by rfl⟩ : syracuseStep 4024313 = 3018235) B3018235
theorem B2385947 : Blo 1589493 2385947 := bstep (se 1 (by rfl) ⟨1789460, by rfl⟩ : syracuseStep 2385947 = 3578921) B3578921
theorem B1788187 : Blo 1589493 1788187 := bstep (se 1 (by rfl) ⟨1341140, by rfl⟩ : syracuseStep 1788187 = 2682281) B2682281
theorem B1812863 : Blo 1589493 1812863 := bstep (se 1 (by rfl) ⟨1359647, by rfl⟩ : syracuseStep 1812863 = 2719295) B2719295
theorem B2386313 : Blo 1589493 2386313 := bstep (se 2 (by rfl) ⟨894867, by rfl⟩ : syracuseStep 2386313 = 1789735) B1789735
theorem B77376059 : Blo 1589493 77376059 := bstep (se 1 (by rfl) ⟨58032044, by rfl⟩ : syracuseStep 77376059 = 116064089) B116064089
theorem B27175661 : Blo 1589493 27175661 := bstep (se 3 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 27175661 = 10190873) B10190873
theorem B9055273 : Blo 1589493 9055273 := bstep (se 2 (by rfl) ⟨3395727, by rfl⟩ : syracuseStep 9055273 = 6791455) B6791455
theorem B18115649 : Blo 1589493 18115649 := bstep (se 2 (by rfl) ⟨6793368, by rfl⟩ : syracuseStep 18115649 = 13586737) B13586737
theorem B1789339 : Blo 1589493 1789339 := bstep (se 1 (by rfl) ⟨1342004, by rfl⟩ : syracuseStep 1789339 = 2684009) B2684009
theorem B2682335 : Blo 1589493 2682335 := bstep (se 1 (by rfl) ⟨2011751, by rfl⟩ : syracuseStep 2682335 = 4023503) B4023503
theorem B5369435 : Blo 1589493 5369435 := bstep (se 1 (by rfl) ⟨4027076, by rfl⟩ : syracuseStep 5369435 = 8054153) B8054153
theorem B19598963 : Blo 1589493 19598963 := bstep (se 1 (by rfl) ⟨14699222, by rfl⟩ : syracuseStep 19598963 = 29398445) B29398445
theorem B2682551 : Blo 1589493 2682551 := bstep (se 1 (by rfl) ⟨2011913, by rfl⟩ : syracuseStep 2682551 = 4023827) B4023827
theorem B12750697 : Blo 1589493 12750697 := bstep (se 2 (by rfl) ⟨4781511, by rfl⟩ : syracuseStep 12750697 = 9563023) B9563023
theorem B5664761 : Blo 1589493 5664761 := bstep (se 2 (by rfl) ⟨2124285, by rfl⟩ : syracuseStep 5664761 = 4248571) B4248571
theorem B3018971 : Blo 1589493 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B4026631 : Blo 1589493 4026631 := bstep (se 1 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 4026631 = 6039947) B6039947
theorem B14512391 : Blo 1589493 14512391 := bstep (se 1 (by rfl) ⟨10884293, by rfl⟩ : syracuseStep 14512391 = 21768587) B21768587
theorem B4903265 : Blo 1589493 4903265 := bstep (se 2 (by rfl) ⟨1838724, by rfl⟩ : syracuseStep 4903265 = 3677449) B3677449
theorem B2552639 : Blo 1589493 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B11465657 : Blo 1589493 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B100643795 : Blo 1589493 100643795 := bstep (se 1 (by rfl) ⟨75482846, by rfl⟩ : syracuseStep 100643795 = 150965693) B150965693
theorem B3576815 : Blo 1589493 3576815 := bstep (se 1 (by rfl) ⟨2682611, by rfl⟩ : syracuseStep 3576815 = 5365223) B5365223
theorem B2683975 : Blo 1589493 2683975 := bstep (se 1 (by rfl) ⟨2012981, by rfl⟩ : syracuseStep 2683975 = 4025963) B4025963
theorem B1963163 : Blo 1589493 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B22918393 : Blo 1589493 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B4527535 : Blo 1589493 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B3577319 : Blo 1589493 3577319 := bstep (se 1 (by rfl) ⟨2682989, by rfl⟩ : syracuseStep 3577319 = 5365979) B5365979
theorem B3577481 : Blo 1589493 3577481 := bstep (se 2 (by rfl) ⟨1341555, by rfl⟩ : syracuseStep 3577481 = 2683111) B2683111
theorem B19347083 : Blo 1589493 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B3577499 : Blo 1589493 3577499 := bstep (se 1 (by rfl) ⟨2683124, by rfl⟩ : syracuseStep 3577499 = 5366249) B5366249
theorem B27539183 : Blo 1589493 27539183 := bstep (se 1 (by rfl) ⟨20654387, by rfl⟩ : syracuseStep 27539183 = 41308775) B41308775
theorem B8050427 : Blo 1589493 8050427 := bstep (se 1 (by rfl) ⟨6037820, by rfl⟩ : syracuseStep 8050427 = 12075641) B12075641
theorem B12080987 : Blo 1589493 12080987 := bstep (se 1 (by rfl) ⟨9060740, by rfl⟩ : syracuseStep 12080987 = 18121481) B18121481
theorem B3577697 : Blo 1589493 3577697 := bstep (se 2 (by rfl) ⟨1341636, by rfl⟩ : syracuseStep 3577697 = 2683273) B2683273
theorem B3577895 : Blo 1589493 3577895 := bstep (se 1 (by rfl) ⟨2683421, by rfl⟩ : syracuseStep 3577895 = 5366843) B5366843
theorem B3578075 : Blo 1589493 3578075 := bstep (se 1 (by rfl) ⟨2683556, by rfl⟩ : syracuseStep 3578075 = 5367113) B5367113
theorem B6035755 : Blo 1589493 6035755 := bstep (se 1 (by rfl) ⟨4526816, by rfl⟩ : syracuseStep 6035755 = 9053633) B9053633
theorem B3578273 : Blo 1589493 3578273 := bstep (se 2 (by rfl) ⟨1341852, by rfl⟩ : syracuseStep 3578273 = 2683705) B2683705
theorem B3578345 : Blo 1589493 3578345 := bstep (se 2 (by rfl) ⟨1341879, by rfl⟩ : syracuseStep 3578345 = 2683759) B2683759
theorem B6789815 : Blo 1589493 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B2865889 : Blo 1589493 2865889 := bstep (se 2 (by rfl) ⟨1074708, by rfl⟩ : syracuseStep 2865889 = 2149417) B2149417
theorem B12074183 : Blo 1589493 12074183 := bstep (se 1 (by rfl) ⟨9055637, by rfl⟩ : syracuseStep 12074183 = 18111275) B18111275
theorem B11468081 : Blo 1589493 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B2866603 : Blo 1589493 2866603 := bstep (se 1 (by rfl) ⟨2149952, by rfl⟩ : syracuseStep 2866603 = 4299905) B4299905
theorem B6790841 : Blo 1589493 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B4530143 : Blo 1589493 4530143 := bstep (se 1 (by rfl) ⟨3397607, by rfl⟩ : syracuseStep 4530143 = 6795215) B6795215
theorem B9674927 : Blo 1589493 9674927 := bstep (se 1 (by rfl) ⟨7256195, by rfl⟩ : syracuseStep 9674927 = 14512391) B14512391
theorem B5439743 : Blo 1589493 5439743 := bstep (se 1 (by rfl) ⟨4079807, by rfl⟩ : syracuseStep 5439743 = 8159615) B8159615
theorem B1589607 : Blo 1589493 1589607 := bstep (se 1 (by rfl) ⟨1192205, by rfl⟩ : syracuseStep 1589607 = 2384411) B2384411
theorem B2384249 : Blo 1589493 2384249 := bstep (se 2 (by rfl) ⟨894093, by rfl⟩ : syracuseStep 2384249 = 1788187) B1788187
theorem B5235101 : Blo 1589493 5235101 := bstep (se 3 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 5235101 = 1963163) B1963163
theorem B1589727 : Blo 1589493 1589727 := bstep (se 1 (by rfl) ⟨1192295, by rfl⟩ : syracuseStep 1589727 = 2384591) B2384591
theorem B1589735 : Blo 1589493 1589735 := bstep (se 1 (by rfl) ⟨1192301, by rfl⟩ : syracuseStep 1589735 = 2384603) B2384603
theorem B7643771 : Blo 1589493 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B2384543 : Blo 1589493 2384543 := bstep (se 1 (by rfl) ⟨1788407, by rfl⟩ : syracuseStep 2384543 = 3576815) B3576815
theorem B1590011 : Blo 1589493 1590011 := bstep (se 1 (by rfl) ⟨1192508, by rfl⟩ : syracuseStep 1590011 = 2385017) B2385017
theorem B13075373 : Blo 1589493 13075373 := bstep (se 3 (by rfl) ⟨2451632, by rfl⟩ : syracuseStep 13075373 = 4903265) B4903265
theorem B2384879 : Blo 1589493 2384879 := bstep (se 1 (by rfl) ⟨1788659, by rfl⟩ : syracuseStep 2384879 = 3577319) B3577319
theorem B4834301 : Blo 1589493 4834301 := bstep (se 3 (by rfl) ⟨906431, by rfl⟩ : syracuseStep 4834301 = 1812863) B1812863
theorem B2384987 : Blo 1589493 2384987 := bstep (se 1 (by rfl) ⟨1788740, by rfl⟩ : syracuseStep 2384987 = 3577481) B3577481
theorem B2384999 : Blo 1589493 2384999 := bstep (se 1 (by rfl) ⟨1788749, by rfl⟩ : syracuseStep 2384999 = 3577499) B3577499
theorem B18359455 : Blo 1589493 18359455 := bstep (se 1 (by rfl) ⟨13769591, by rfl⟩ : syracuseStep 18359455 = 27539183) B27539183
theorem B5366951 : Blo 1589493 5366951 := bstep (se 1 (by rfl) ⟨4025213, by rfl⟩ : syracuseStep 5366951 = 8050427) B8050427
theorem B8053991 : Blo 1589493 8053991 := bstep (se 1 (by rfl) ⟨6040493, by rfl⟩ : syracuseStep 8053991 = 12080987) B12080987
theorem B2385131 : Blo 1589493 2385131 := bstep (se 1 (by rfl) ⟨1788848, by rfl⟩ : syracuseStep 2385131 = 3577697) B3577697
theorem B1590591 : Blo 1589493 1590591 := bstep (se 1 (by rfl) ⟨1192943, by rfl⟩ : syracuseStep 1590591 = 2385887) B2385887
theorem B1590599 : Blo 1589493 1590599 := bstep (se 1 (by rfl) ⟨1192949, by rfl⟩ : syracuseStep 1590599 = 2385899) B2385899
theorem B1590631 : Blo 1589493 1590631 := bstep (se 1 (by rfl) ⟨1192973, by rfl⟩ : syracuseStep 1590631 = 2385947) B2385947
theorem B2385263 : Blo 1589493 2385263 := bstep (se 1 (by rfl) ⟨1788947, by rfl⟩ : syracuseStep 2385263 = 3577895) B3577895
theorem B16319873 : Blo 1589493 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B2385383 : Blo 1589493 2385383 := bstep (se 1 (by rfl) ⟨1789037, by rfl⟩ : syracuseStep 2385383 = 3578075) B3578075
theorem B1590875 : Blo 1589493 1590875 := bstep (se 1 (by rfl) ⟨1193156, by rfl⟩ : syracuseStep 1590875 = 2386313) B2386313
theorem B2385515 : Blo 1589493 2385515 := bstep (se 1 (by rfl) ⟨1789136, by rfl⟩ : syracuseStep 2385515 = 3578273) B3578273
theorem B2385563 : Blo 1589493 2385563 := bstep (se 1 (by rfl) ⟨1789172, by rfl⟩ : syracuseStep 2385563 = 3578345) B3578345
theorem B30557857 : Blo 1589493 30557857 := bstep (se 2 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 30557857 = 22918393) B22918393
theorem B2385785 : Blo 1589493 2385785 := bstep (se 2 (by rfl) ⟨894669, by rfl⟩ : syracuseStep 2385785 = 1789339) B1789339
theorem B68003717 : Blo 1589493 68003717 := bstep (se 4 (by rfl) ⟨6375348, by rfl⟩ : syracuseStep 68003717 = 12750697) B12750697
theorem B12077099 : Blo 1589493 12077099 := bstep (se 1 (by rfl) ⟨9057824, by rfl⟩ : syracuseStep 12077099 = 18115649) B18115649
theorem B7645387 : Blo 1589493 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B1788223 : Blo 1589493 1788223 := bstep (se 1 (by rfl) ⟨1341167, by rfl⟩ : syracuseStep 1788223 = 2682335) B2682335
theorem B1788367 : Blo 1589493 1788367 := bstep (se 1 (by rfl) ⟨1341275, by rfl⟩ : syracuseStep 1788367 = 2682551) B2682551
theorem B6040403 : Blo 1589493 6040403 := bstep (se 1 (by rfl) ⟨4530302, by rfl⟩ : syracuseStep 6040403 = 9060605) B9060605
theorem B5368841 : Blo 1589493 5368841 := bstep (se 2 (by rfl) ⟨2013315, by rfl⟩ : syracuseStep 5368841 = 4026631) B4026631
theorem B8047673 : Blo 1589493 8047673 := bstep (se 2 (by rfl) ⟨3017877, by rfl⟩ : syracuseStep 8047673 = 6035755) B6035755
theorem B67095863 : Blo 1589493 67095863 := bstep (se 1 (by rfl) ⟨50321897, by rfl⟩ : syracuseStep 67095863 = 100643795) B100643795
theorem B6450587 : Blo 1589493 6450587 := bstep (se 1 (by rfl) ⟨4837940, by rfl⟩ : syracuseStep 6450587 = 9675881) B9675881
theorem B3821185 : Blo 1589493 3821185 := bstep (se 2 (by rfl) ⟨1432944, by rfl⟩ : syracuseStep 3821185 = 2865889) B2865889
theorem B12898055 : Blo 1589493 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B165228329 : Blo 1589493 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B37220143 : Blo 1589493 37220143 := bstep (se 1 (by rfl) ⟨27915107, by rfl⟩ : syracuseStep 37220143 = 55830215) B55830215
theorem B97955729 : Blo 1589493 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B2682875 : Blo 1589493 2682875 := bstep (se 1 (by rfl) ⟨2012156, by rfl⟩ : syracuseStep 2682875 = 4024313) B4024313
theorem B4526543 : Blo 1589493 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B18117107 : Blo 1589493 18117107 := bstep (se 1 (by rfl) ⟨13587830, by rfl⟩ : syracuseStep 18117107 = 27175661) B27175661
theorem B3822137 : Blo 1589493 3822137 := bstep (se 2 (by rfl) ⟨1433301, by rfl⟩ : syracuseStep 3822137 = 2866603) B2866603
theorem B8049455 : Blo 1589493 8049455 := bstep (se 1 (by rfl) ⟨6037091, by rfl⟩ : syracuseStep 8049455 = 12074183) B12074183
theorem B10884077 : Blo 1589493 10884077 := bstep (se 3 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 10884077 = 4081529) B4081529
theorem B4527227 : Blo 1589493 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B3020095 : Blo 1589493 3020095 := bstep (se 1 (by rfl) ⟨2265071, by rfl⟩ : syracuseStep 3020095 = 4530143) B4530143
theorem B8050589 : Blo 1589493 8050589 := bstep (se 3 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 8050589 = 3018971) B3018971
theorem B27228149 : Blo 1589493 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B10328435 : Blo 1589493 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B3578471 : Blo 1589493 3578471 := bstep (se 1 (by rfl) ⟨2683853, by rfl⟩ : syracuseStep 3578471 = 5367707) B5367707
theorem B12073697 : Blo 1589493 12073697 := bstep (se 2 (by rfl) ⟨4527636, by rfl⟩ : syracuseStep 12073697 = 9055273) B9055273
theorem B3578633 : Blo 1589493 3578633 := bstep (se 2 (by rfl) ⟨1341987, by rfl⟩ : syracuseStep 3578633 = 2683975) B2683975
theorem B52263901 : Blo 1589493 52263901 := bstep (se 3 (by rfl) ⟨9799481, by rfl⟩ : syracuseStep 52263901 = 19598963) B19598963
theorem B51584039 : Blo 1589493 51584039 := bstep (se 1 (by rfl) ⟨38688029, by rfl⟩ : syracuseStep 51584039 = 77376059) B77376059
theorem B6036713 : Blo 1589493 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B3579623 : Blo 1589493 3579623 := bstep (se 1 (by rfl) ⟨2684717, by rfl⟩ : syracuseStep 3579623 = 5369435) B5369435
theorem B3776507 : Blo 1589493 3776507 := bstep (se 1 (by rfl) ⟨2832380, by rfl⟩ : syracuseStep 3776507 = 5664761) B5664761
theorem B1589499 : Blo 1589493 1589499 := bstep (se 1 (by rfl) ⟨1192124, by rfl⟩ : syracuseStep 1589499 = 2384249) B2384249
theorem B3490067 : Blo 1589493 3490067 := bstep (se 1 (by rfl) ⟨2617550, by rfl⟩ : syracuseStep 3490067 = 5235101) B5235101
theorem B2548091 : Blo 1589493 2548091 := bstep (se 1 (by rfl) ⟨1911068, by rfl⟩ : syracuseStep 2548091 = 3822137) B3822137
theorem B5095847 : Blo 1589493 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B2384297 : Blo 1589493 2384297 := bstep (se 2 (by rfl) ⟨894111, by rfl⟩ : syracuseStep 2384297 = 1788223) B1788223
theorem B1589695 : Blo 1589493 1589695 := bstep (se 1 (by rfl) ⟨1192271, by rfl⟩ : syracuseStep 1589695 = 2384543) B2384543
theorem B5366303 : Blo 1589493 5366303 := bstep (se 1 (by rfl) ⟨4024727, by rfl⟩ : syracuseStep 5366303 = 8049455) B8049455
theorem B2384489 : Blo 1589493 2384489 := bstep (se 2 (by rfl) ⟨894183, by rfl⟩ : syracuseStep 2384489 = 1788367) B1788367
theorem B8716915 : Blo 1589493 8716915 := bstep (se 1 (by rfl) ⟨6537686, by rfl⟩ : syracuseStep 8716915 = 13075373) B13075373
theorem B1589919 : Blo 1589493 1589919 := bstep (se 1 (by rfl) ⟨1192439, by rfl⟩ : syracuseStep 1589919 = 2384879) B2384879
theorem B1589991 : Blo 1589493 1589991 := bstep (se 1 (by rfl) ⟨1192493, by rfl⟩ : syracuseStep 1589991 = 2384987) B2384987
theorem B1589999 : Blo 1589493 1589999 := bstep (se 1 (by rfl) ⟨1192499, by rfl⟩ : syracuseStep 1589999 = 2384999) B2384999
theorem B1590087 : Blo 1589493 1590087 := bstep (se 1 (by rfl) ⟨1192565, by rfl⟩ : syracuseStep 1590087 = 2385131) B2385131
theorem B1590175 : Blo 1589493 1590175 := bstep (se 1 (by rfl) ⟨1192631, by rfl⟩ : syracuseStep 1590175 = 2385263) B2385263
theorem B10879915 : Blo 1589493 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B1590255 : Blo 1589493 1590255 := bstep (se 1 (by rfl) ⟨1192691, by rfl⟩ : syracuseStep 1590255 = 2385383) B2385383
theorem B1590343 : Blo 1589493 1590343 := bstep (se 1 (by rfl) ⟨1192757, by rfl⟩ : syracuseStep 1590343 = 2385515) B2385515
theorem B1590375 : Blo 1589493 1590375 := bstep (se 1 (by rfl) ⟨1192781, by rfl⟩ : syracuseStep 1590375 = 2385563) B2385563
theorem B1590523 : Blo 1589493 1590523 := bstep (se 1 (by rfl) ⟨1192892, by rfl⟩ : syracuseStep 1590523 = 2385785) B2385785
theorem B5367059 : Blo 1589493 5367059 := bstep (se 1 (by rfl) ⟨4025294, by rfl⟩ : syracuseStep 5367059 = 8050589) B8050589
theorem B24479273 : Blo 1589493 24479273 := bstep (se 2 (by rfl) ⟨9179727, by rfl⟩ : syracuseStep 24479273 = 18359455) B18359455
theorem B2385647 : Blo 1589493 2385647 := bstep (se 1 (by rfl) ⟨1789235, by rfl⟩ : syracuseStep 2385647 = 3578471) B3578471
theorem B2385755 : Blo 1589493 2385755 := bstep (se 1 (by rfl) ⟨1789316, by rfl⟩ : syracuseStep 2385755 = 3578633) B3578633
theorem B4024475 : Blo 1589493 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B44730575 : Blo 1589493 44730575 := bstep (se 1 (by rfl) ⟨33547931, by rfl⟩ : syracuseStep 44730575 = 67095863) B67095863
theorem B2386415 : Blo 1589493 2386415 := bstep (se 1 (by rfl) ⟨1789811, by rfl⟩ : syracuseStep 2386415 = 3579623) B3579623
theorem B110152219 : Blo 1589493 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1788583 : Blo 1589493 1788583 := bstep (se 1 (by rfl) ⟨1341437, by rfl⟩ : syracuseStep 1788583 = 2682875) B2682875
theorem B2517671 : Blo 1589493 2517671 := bstep (se 1 (by rfl) ⟨1888253, by rfl⟩ : syracuseStep 2517671 = 3776507) B3776507
theorem B6449951 : Blo 1589493 6449951 := bstep (se 1 (by rfl) ⟨4837463, by rfl⟩ : syracuseStep 6449951 = 9674927) B9674927
theorem B10193849 : Blo 1589493 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B12078071 : Blo 1589493 12078071 := bstep (se 1 (by rfl) ⟨9058553, by rfl⟩ : syracuseStep 12078071 = 18117107) B18117107
theorem B3018151 : Blo 1589493 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B5369327 : Blo 1589493 5369327 := bstep (se 1 (by rfl) ⟨4026995, by rfl⟩ : syracuseStep 5369327 = 8053991) B8053991
theorem B12070781 : Blo 1589493 12070781 := bstep (se 3 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 12070781 = 4526543) B4526543
theorem B69685201 : Blo 1589493 69685201 := bstep (se 2 (by rfl) ⟨26131950, by rfl⟩ : syracuseStep 69685201 = 52263901) B52263901
theorem B6885623 : Blo 1589493 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B4026793 : Blo 1589493 4026793 := bstep (se 2 (by rfl) ⟨1510047, by rfl⟩ : syracuseStep 4026793 = 3020095) B3020095
theorem B8049131 : Blo 1589493 8049131 := bstep (se 1 (by rfl) ⟨6036848, by rfl⟩ : syracuseStep 8049131 = 12073697) B12073697
theorem B4026935 : Blo 1589493 4026935 := bstep (se 1 (by rfl) ⟨3020201, by rfl⟩ : syracuseStep 4026935 = 6040403) B6040403
theorem B34394813 : Blo 1589493 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B40743809 : Blo 1589493 40743809 := bstep (se 2 (by rfl) ⟨15278928, by rfl⟩ : syracuseStep 40743809 = 30557857) B30557857
theorem B181343245 : Blo 1589493 181343245 := bstep (se 3 (by rfl) ⟨34001858, by rfl⟩ : syracuseStep 181343245 = 68003717) B68003717
theorem B65303819 : Blo 1589493 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B12891469 : Blo 1589493 12891469 := bstep (se 3 (by rfl) ⟨2417150, by rfl⟩ : syracuseStep 12891469 = 4834301) B4834301
theorem B3626495 : Blo 1589493 3626495 := bstep (se 1 (by rfl) ⟨2719871, by rfl⟩ : syracuseStep 3626495 = 5439743) B5439743
theorem B7256051 : Blo 1589493 7256051 := bstep (se 1 (by rfl) ⟨5442038, by rfl⟩ : syracuseStep 7256051 = 10884077) B10884077
theorem B3577967 : Blo 1589493 3577967 := bstep (se 1 (by rfl) ⟨2683475, by rfl⟩ : syracuseStep 3577967 = 5366951) B5366951
theorem B18152099 : Blo 1589493 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B8051399 : Blo 1589493 8051399 := bstep (se 1 (by rfl) ⟨6038549, by rfl⟩ : syracuseStep 8051399 = 12077099) B12077099
theorem B3579227 : Blo 1589493 3579227 := bstep (se 1 (by rfl) ⟨2684420, by rfl⟩ : syracuseStep 3579227 = 5368841) B5368841
theorem B34389359 : Blo 1589493 34389359 := bstep (se 1 (by rfl) ⟨25792019, by rfl⟩ : syracuseStep 34389359 = 51584039) B51584039
theorem B5365115 : Blo 1589493 5365115 := bstep (se 1 (by rfl) ⟨4023836, by rfl⟩ : syracuseStep 5365115 = 8047673) B8047673
theorem B5094913 : Blo 1589493 5094913 := bstep (se 2 (by rfl) ⟨1910592, by rfl⟩ : syracuseStep 5094913 = 3821185) B3821185
theorem B4300391 : Blo 1589493 4300391 := bstep (se 1 (by rfl) ⟨3225293, by rfl⟩ : syracuseStep 4300391 = 6450587) B6450587
theorem B49626857 : Blo 1589493 49626857 := bstep (se 2 (by rfl) ⟨18610071, by rfl⟩ : syracuseStep 49626857 = 37220143) B37220143
theorem B2326711 : Blo 1589493 2326711 := bstep (se 1 (by rfl) ⟨1745033, by rfl⟩ : syracuseStep 2326711 = 3490067) B3490067
theorem B1589531 : Blo 1589493 1589531 := bstep (se 1 (by rfl) ⟨1192148, by rfl⟩ : syracuseStep 1589531 = 2384297) B2384297
theorem B5366087 : Blo 1589493 5366087 := bstep (se 1 (by rfl) ⟨4024565, by rfl⟩ : syracuseStep 5366087 = 8049131) B8049131
theorem B1589659 : Blo 1589493 1589659 := bstep (se 1 (by rfl) ⟨1192244, by rfl⟩ : syracuseStep 1589659 = 2384489) B2384489
theorem B22929875 : Blo 1589493 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B46490213 : Blo 1589493 46490213 := bstep (se 4 (by rfl) ⟨4358457, by rfl⟩ : syracuseStep 46490213 = 8716915) B8716915
theorem B2384777 : Blo 1589493 2384777 := bstep (se 2 (by rfl) ⟨894291, by rfl⟩ : syracuseStep 2384777 = 1788583) B1788583
theorem B2417663 : Blo 1589493 2417663 := bstep (se 1 (by rfl) ⟨1813247, by rfl⟩ : syracuseStep 2417663 = 3626495) B3626495
theorem B16319515 : Blo 1589493 16319515 := bstep (se 1 (by rfl) ⟨12239636, by rfl⟩ : syracuseStep 16319515 = 24479273) B24479273
theorem B1590431 : Blo 1589493 1590431 := bstep (se 1 (by rfl) ⟨1192823, by rfl⟩ : syracuseStep 1590431 = 2385647) B2385647
theorem B1590503 : Blo 1589493 1590503 := bstep (se 1 (by rfl) ⟨1192877, by rfl⟩ : syracuseStep 1590503 = 2385755) B2385755
theorem B2385311 : Blo 1589493 2385311 := bstep (se 1 (by rfl) ⟨1788983, by rfl⟩ : syracuseStep 2385311 = 3577967) B3577967
theorem B29820383 : Blo 1589493 29820383 := bstep (se 1 (by rfl) ⟨22365287, by rfl⟩ : syracuseStep 29820383 = 44730575) B44730575
theorem B1590943 : Blo 1589493 1590943 := bstep (se 1 (by rfl) ⟨1193207, by rfl⟩ : syracuseStep 1590943 = 2386415) B2386415
theorem B17188625 : Blo 1589493 17188625 := bstep (se 2 (by rfl) ⟨6445734, by rfl⟩ : syracuseStep 17188625 = 12891469) B12891469
theorem B12101399 : Blo 1589493 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B5367599 : Blo 1589493 5367599 := bstep (se 1 (by rfl) ⟨4025699, by rfl⟩ : syracuseStep 5367599 = 8051399) B8051399
theorem B4024201 : Blo 1589493 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B6793217 : Blo 1589493 6793217 := bstep (se 2 (by rfl) ⟨2547456, by rfl⟩ : syracuseStep 6793217 = 5094913) B5094913
theorem B2386151 : Blo 1589493 2386151 := bstep (se 1 (by rfl) ⟨1789613, by rfl⟩ : syracuseStep 2386151 = 3579227) B3579227
theorem B8047187 : Blo 1589493 8047187 := bstep (se 1 (by rfl) ⟨6035390, by rfl⟩ : syracuseStep 8047187 = 12070781) B12070781
theorem B4590415 : Blo 1589493 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B1698727 : Blo 1589493 1698727 := bstep (se 1 (by rfl) ⟨1274045, by rfl⟩ : syracuseStep 1698727 = 2548091) B2548091
theorem B5369057 : Blo 1589493 5369057 := bstep (se 2 (by rfl) ⟨2013396, by rfl⟩ : syracuseStep 5369057 = 4026793) B4026793
theorem B146869625 : Blo 1589493 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B43535879 : Blo 1589493 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B4837367 : Blo 1589493 4837367 := bstep (se 1 (by rfl) ⟨3628025, by rfl⟩ : syracuseStep 4837367 = 7256051) B7256051
theorem B241790993 : Blo 1589493 241790993 := bstep (se 2 (by rfl) ⟨90671622, by rfl⟩ : syracuseStep 241790993 = 181343245) B181343245
theorem B2682983 : Blo 1589493 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B6795899 : Blo 1589493 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B22926239 : Blo 1589493 22926239 := bstep (se 1 (by rfl) ⟨17194679, by rfl⟩ : syracuseStep 22926239 = 34389359) B34389359
theorem B3576743 : Blo 1589493 3576743 := bstep (se 1 (by rfl) ⟨2682557, by rfl⟩ : syracuseStep 3576743 = 5365115) B5365115
theorem B33084571 : Blo 1589493 33084571 := bstep (se 1 (by rfl) ⟨24813428, by rfl⟩ : syracuseStep 33084571 = 49626857) B49626857
theorem B3397231 : Blo 1589493 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B3577535 : Blo 1589493 3577535 := bstep (se 1 (by rfl) ⟨2683151, by rfl⟩ : syracuseStep 3577535 = 5366303) B5366303
theorem B2684623 : Blo 1589493 2684623 := bstep (se 1 (by rfl) ⟨2013467, by rfl⟩ : syracuseStep 2684623 = 4026935) B4026935
theorem B27162539 : Blo 1589493 27162539 := bstep (se 1 (by rfl) ⟨20371904, by rfl⟩ : syracuseStep 27162539 = 40743809) B40743809
theorem B3578039 : Blo 1589493 3578039 := bstep (se 1 (by rfl) ⟨2683529, by rfl⟩ : syracuseStep 3578039 = 5367059) B5367059
theorem B14506553 : Blo 1589493 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B1678447 : Blo 1589493 1678447 := bstep (se 1 (by rfl) ⟨1258835, by rfl⟩ : syracuseStep 1678447 = 2517671) B2517671
theorem B4299967 : Blo 1589493 4299967 := bstep (se 1 (by rfl) ⟨3224975, by rfl⟩ : syracuseStep 4299967 = 6449951) B6449951
theorem B8052047 : Blo 1589493 8052047 := bstep (se 1 (by rfl) ⟨6039035, by rfl⟩ : syracuseStep 8052047 = 12078071) B12078071
theorem B3579551 : Blo 1589493 3579551 := bstep (se 1 (by rfl) ⟨2684663, by rfl⟩ : syracuseStep 3579551 = 5369327) B5369327
theorem B2866927 : Blo 1589493 2866927 := bstep (se 1 (by rfl) ⟨2150195, by rfl⟩ : syracuseStep 2866927 = 4300391) B4300391
theorem B371654405 : Blo 1589493 371654405 := bstep (se 4 (by rfl) ⟨34842600, by rfl⟩ : syracuseStep 371654405 = 69685201) B69685201
theorem B161193995 : Blo 1589493 161193995 := bstep (se 1 (by rfl) ⟨120895496, by rfl⟩ : syracuseStep 161193995 = 241790993) B241790993
theorem B15286583 : Blo 1589493 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B4530599 : Blo 1589493 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B1589851 : Blo 1589493 1589851 := bstep (se 1 (by rfl) ⟨1192388, by rfl⟩ : syracuseStep 1589851 = 2384777) B2384777
theorem B2384495 : Blo 1589493 2384495 := bstep (se 1 (by rfl) ⟨1788371, by rfl⟩ : syracuseStep 2384495 = 3576743) B3576743
theorem B1590207 : Blo 1589493 1590207 := bstep (se 1 (by rfl) ⟨1192655, by rfl⟩ : syracuseStep 1590207 = 2385311) B2385311
theorem B2385023 : Blo 1589493 2385023 := bstep (se 1 (by rfl) ⟨1788767, by rfl⟩ : syracuseStep 2385023 = 3577535) B3577535
theorem B21759353 : Blo 1589493 21759353 := bstep (se 2 (by rfl) ⟨8159757, by rfl⟩ : syracuseStep 21759353 = 16319515) B16319515
theorem B2385359 : Blo 1589493 2385359 := bstep (se 1 (by rfl) ⟨1789019, by rfl⟩ : syracuseStep 2385359 = 3578039) B3578039
theorem B2237929 : Blo 1589493 2237929 := bstep (se 2 (by rfl) ⟨839223, by rfl⟩ : syracuseStep 2237929 = 1678447) B1678447
theorem B1590767 : Blo 1589493 1590767 := bstep (se 1 (by rfl) ⟨1193075, by rfl⟩ : syracuseStep 1590767 = 2386151) B2386151
theorem B5368031 : Blo 1589493 5368031 := bstep (se 1 (by rfl) ⟨4026023, by rfl⟩ : syracuseStep 5368031 = 8052047) B8052047
theorem B97913083 : Blo 1589493 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B2386367 : Blo 1589493 2386367 := bstep (se 1 (by rfl) ⟨1789775, by rfl⟩ : syracuseStep 2386367 = 3579551) B3579551
theorem B247769603 : Blo 1589493 247769603 := bstep (se 1 (by rfl) ⟨185827202, by rfl⟩ : syracuseStep 247769603 = 371654405) B371654405
theorem B1788655 : Blo 1589493 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B2264969 : Blo 1589493 2264969 := bstep (se 2 (by rfl) ⟨849363, by rfl⟩ : syracuseStep 2264969 = 1698727) B1698727
theorem B18108359 : Blo 1589493 18108359 := bstep (se 1 (by rfl) ⟨13581269, by rfl⟩ : syracuseStep 18108359 = 27162539) B27162539
theorem B123973901 : Blo 1589493 123973901 := bstep (se 3 (by rfl) ⟨23245106, by rfl⟩ : syracuseStep 123973901 = 46490213) B46490213
theorem B9671035 : Blo 1589493 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B24482213 : Blo 1589493 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B3822569 : Blo 1589493 3822569 := bstep (se 2 (by rfl) ⟨1433463, by rfl⟩ : syracuseStep 3822569 = 2866927) B2866927
theorem B12899645 : Blo 1589493 12899645 := bstep (se 3 (by rfl) ⟨2418683, by rfl⟩ : syracuseStep 12899645 = 4837367) B4837367
theorem B3577391 : Blo 1589493 3577391 := bstep (se 1 (by rfl) ⟨2683043, by rfl⟩ : syracuseStep 3577391 = 5366087) B5366087
theorem B3102281 : Blo 1589493 3102281 := bstep (se 2 (by rfl) ⟨1163355, by rfl⟩ : syracuseStep 3102281 = 2326711) B2326711
theorem B18118565 : Blo 1589493 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B15284159 : Blo 1589493 15284159 := bstep (se 1 (by rfl) ⟨11463119, by rfl⟩ : syracuseStep 15284159 = 22926239) B22926239
theorem B1611775 : Blo 1589493 1611775 := bstep (se 1 (by rfl) ⟨1208831, by rfl⟩ : syracuseStep 1611775 = 2417663) B2417663
theorem B19880255 : Blo 1589493 19880255 := bstep (se 1 (by rfl) ⟨14910191, by rfl⟩ : syracuseStep 19880255 = 29820383) B29820383
theorem B11459083 : Blo 1589493 11459083 := bstep (se 1 (by rfl) ⟨8594312, by rfl⟩ : syracuseStep 11459083 = 17188625) B17188625
theorem B8067599 : Blo 1589493 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B3578399 : Blo 1589493 3578399 := bstep (se 1 (by rfl) ⟨2683799, by rfl⟩ : syracuseStep 3578399 = 5367599) B5367599
theorem B4528811 : Blo 1589493 4528811 := bstep (se 1 (by rfl) ⟨3396608, by rfl⟩ : syracuseStep 4528811 = 6793217) B6793217
theorem B44112761 : Blo 1589493 44112761 := bstep (se 2 (by rfl) ⟨16542285, by rfl⟩ : syracuseStep 44112761 = 33084571) B33084571
theorem B5733289 : Blo 1589493 5733289 := bstep (se 2 (by rfl) ⟨2149983, by rfl⟩ : syracuseStep 5733289 = 4299967) B4299967
theorem B5364791 : Blo 1589493 5364791 := bstep (se 1 (by rfl) ⟨4023593, by rfl⟩ : syracuseStep 5364791 = 8047187) B8047187
theorem B3579371 : Blo 1589493 3579371 := bstep (se 1 (by rfl) ⟨2684528, by rfl⟩ : syracuseStep 3579371 = 5369057) B5369057
theorem B3579497 : Blo 1589493 3579497 := bstep (se 2 (by rfl) ⟨1342311, by rfl⟩ : syracuseStep 3579497 = 2684623) B2684623
theorem B29023919 : Blo 1589493 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B5365601 : Blo 1589493 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B107462663 : Blo 1589493 107462663 := bstep (se 1 (by rfl) ⟨80596997, by rfl⟩ : syracuseStep 107462663 = 161193995) B161193995
theorem B82649267 : Blo 1589493 82649267 := bstep (se 1 (by rfl) ⟨61986950, by rfl⟩ : syracuseStep 82649267 = 123973901) B123973901
theorem B10191055 : Blo 1589493 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B1589663 : Blo 1589493 1589663 := bstep (se 1 (by rfl) ⟨1192247, by rfl⟩ : syracuseStep 1589663 = 2384495) B2384495
theorem B12894713 : Blo 1589493 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B2548379 : Blo 1589493 2548379 := bstep (se 1 (by rfl) ⟨1911284, by rfl⟩ : syracuseStep 2548379 = 3822569) B3822569
theorem B15278777 : Blo 1589493 15278777 := bstep (se 2 (by rfl) ⟨5729541, by rfl⟩ : syracuseStep 15278777 = 11459083) B11459083
theorem B1590015 : Blo 1589493 1590015 := bstep (se 1 (by rfl) ⟨1192511, by rfl⟩ : syracuseStep 1590015 = 2385023) B2385023
theorem B1590239 : Blo 1589493 1590239 := bstep (se 1 (by rfl) ⟨1192679, by rfl⟩ : syracuseStep 1590239 = 2385359) B2385359
theorem B2384873 : Blo 1589493 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B2384927 : Blo 1589493 2384927 := bstep (se 1 (by rfl) ⟨1788695, by rfl⟩ : syracuseStep 2384927 = 3577391) B3577391
theorem B7644385 : Blo 1589493 7644385 := bstep (se 2 (by rfl) ⟨2866644, by rfl⟩ : syracuseStep 7644385 = 5733289) B5733289
theorem B1590911 : Blo 1589493 1590911 := bstep (se 1 (by rfl) ⟨1193183, by rfl⟩ : syracuseStep 1590911 = 2386367) B2386367
theorem B2385599 : Blo 1589493 2385599 := bstep (se 1 (by rfl) ⟨1789199, by rfl⟩ : syracuseStep 2385599 = 3578399) B3578399
theorem B2386247 : Blo 1589493 2386247 := bstep (se 1 (by rfl) ⟨1789685, by rfl⟩ : syracuseStep 2386247 = 3579371) B3579371
theorem B6039917 : Blo 1589493 6039917 := bstep (se 3 (by rfl) ⟨1132484, by rfl⟩ : syracuseStep 6039917 = 2264969) B2264969
theorem B2386331 : Blo 1589493 2386331 := bstep (se 1 (by rfl) ⟨1789748, by rfl⟩ : syracuseStep 2386331 = 3579497) B3579497
theorem B2149033 : Blo 1589493 2149033 := bstep (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) B1611775
theorem B16321475 : Blo 1589493 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B130550777 : Blo 1589493 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B2068187 : Blo 1589493 2068187 := bstep (se 1 (by rfl) ⟨1551140, by rfl⟩ : syracuseStep 2068187 = 3102281) B3102281
theorem B12079043 : Blo 1589493 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B165179735 : Blo 1589493 165179735 := bstep (se 1 (by rfl) ⟨123884801, by rfl⟩ : syracuseStep 165179735 = 247769603) B247769603
theorem B5378399 : Blo 1589493 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B3019207 : Blo 1589493 3019207 := bstep (se 1 (by rfl) ⟨2264405, by rfl⟩ : syracuseStep 3019207 = 4528811) B4528811
theorem B3576527 : Blo 1589493 3576527 := bstep (se 1 (by rfl) ⟨2682395, by rfl⟩ : syracuseStep 3576527 = 5364791) B5364791
theorem B3577067 : Blo 1589493 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B12072239 : Blo 1589493 12072239 := bstep (se 1 (by rfl) ⟨9054179, by rfl⟩ : syracuseStep 12072239 = 18108359) B18108359
theorem B3020399 : Blo 1589493 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B8599763 : Blo 1589493 8599763 := bstep (se 1 (by rfl) ⟨6449822, by rfl⟩ : syracuseStep 8599763 = 12899645) B12899645
theorem B14506235 : Blo 1589493 14506235 := bstep (se 1 (by rfl) ⟨10879676, by rfl⟩ : syracuseStep 14506235 = 21759353) B21759353
theorem B10189439 : Blo 1589493 10189439 := bstep (se 1 (by rfl) ⟨7642079, by rfl⟩ : syracuseStep 10189439 = 15284159) B15284159
theorem B3578687 : Blo 1589493 3578687 := bstep (se 1 (by rfl) ⟨2684015, by rfl⟩ : syracuseStep 3578687 = 5368031) B5368031
theorem B13253503 : Blo 1589493 13253503 := bstep (se 1 (by rfl) ⟨9940127, by rfl⟩ : syracuseStep 13253503 = 19880255) B19880255
theorem B29408507 : Blo 1589493 29408507 := bstep (se 1 (by rfl) ⟨22056380, by rfl⟩ : syracuseStep 29408507 = 44112761) B44112761
theorem B19349279 : Blo 1589493 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B11935621 : Blo 1589493 11935621 := bstep (se 4 (by rfl) ⟨1118964, by rfl⟩ : syracuseStep 11935621 = 2237929) B2237929
theorem B55099511 : Blo 1589493 55099511 := bstep (se 1 (by rfl) ⟨41324633, by rfl⟩ : syracuseStep 55099511 = 82649267) B82649267
theorem B2384351 : Blo 1589493 2384351 := bstep (se 1 (by rfl) ⟨1788263, by rfl⟩ : syracuseStep 2384351 = 3576527) B3576527
theorem B1589915 : Blo 1589493 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B1589951 : Blo 1589493 1589951 := bstep (se 1 (by rfl) ⟨1192463, by rfl⟩ : syracuseStep 1589951 = 2384927) B2384927
theorem B2384711 : Blo 1589493 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B1590399 : Blo 1589493 1590399 := bstep (se 1 (by rfl) ⟨1192799, by rfl⟩ : syracuseStep 1590399 = 2385599) B2385599
theorem B17671337 : Blo 1589493 17671337 := bstep (se 2 (by rfl) ⟨6626751, by rfl⟩ : syracuseStep 17671337 = 13253503) B13253503
theorem B1590831 : Blo 1589493 1590831 := bstep (se 1 (by rfl) ⟨1193123, by rfl⟩ : syracuseStep 1590831 = 2386247) B2386247
theorem B1590887 : Blo 1589493 1590887 := bstep (se 1 (by rfl) ⟨1193165, by rfl⟩ : syracuseStep 1590887 = 2386331) B2386331
theorem B6792959 : Blo 1589493 6792959 := bstep (se 1 (by rfl) ⟨5094719, by rfl⟩ : syracuseStep 6792959 = 10189439) B10189439
theorem B2385791 : Blo 1589493 2385791 := bstep (se 1 (by rfl) ⟨1789343, by rfl⟩ : syracuseStep 2385791 = 3578687) B3578687
theorem B5515165 : Blo 1589493 5515165 := bstep (se 3 (by rfl) ⟨1034093, by rfl⟩ : syracuseStep 5515165 = 2068187) B2068187
theorem B10880983 : Blo 1589493 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B87033851 : Blo 1589493 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B19605671 : Blo 1589493 19605671 := bstep (se 1 (by rfl) ⟨14704253, by rfl⟩ : syracuseStep 19605671 = 29408507) B29408507
theorem B71641775 : Blo 1589493 71641775 := bstep (se 1 (by rfl) ⟨53731331, by rfl⟩ : syracuseStep 71641775 = 107462663) B107462663
theorem B110119823 : Blo 1589493 110119823 := bstep (se 1 (by rfl) ⟨82589867, by rfl⟩ : syracuseStep 110119823 = 165179735) B165179735
theorem B8596475 : Blo 1589493 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B10185851 : Blo 1589493 10185851 := bstep (se 1 (by rfl) ⟨7639388, by rfl⟩ : syracuseStep 10185851 = 15278777) B15278777
theorem B4025609 : Blo 1589493 4025609 := bstep (se 2 (by rfl) ⟨1509603, by rfl⟩ : syracuseStep 4025609 = 3019207) B3019207
theorem B8048159 : Blo 1589493 8048159 := bstep (se 1 (by rfl) ⟨6036119, by rfl⟩ : syracuseStep 8048159 = 12072239) B12072239
theorem B9670823 : Blo 1589493 9670823 := bstep (se 1 (by rfl) ⟨7253117, by rfl⟩ : syracuseStep 9670823 = 14506235) B14506235
theorem B4026611 : Blo 1589493 4026611 := bstep (se 1 (by rfl) ⟨3019958, by rfl⟩ : syracuseStep 4026611 = 6039917) B6039917
theorem B6795677 : Blo 1589493 6795677 := bstep (se 3 (by rfl) ⟨1274189, by rfl⟩ : syracuseStep 6795677 = 2548379) B2548379
theorem B15914161 : Blo 1589493 15914161 := bstep (se 2 (by rfl) ⟨5967810, by rfl⟩ : syracuseStep 15914161 = 11935621) B11935621
theorem B12899519 : Blo 1589493 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B3585599 : Blo 1589493 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B13588073 : Blo 1589493 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B2865377 : Blo 1589493 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B2013599 : Blo 1589493 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B40770053 : Blo 1589493 40770053 := bstep (se 4 (by rfl) ⟨3822192, by rfl⟩ : syracuseStep 40770053 = 7644385) B7644385
theorem B5733175 : Blo 1589493 5733175 := bstep (se 1 (by rfl) ⟨4299881, by rfl⟩ : syracuseStep 5733175 = 8599763) B8599763
theorem B8052695 : Blo 1589493 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B36733007 : Blo 1589493 36733007 := bstep (se 1 (by rfl) ⟨27549755, by rfl⟩ : syracuseStep 36733007 = 55099511) B55099511
theorem B6447215 : Blo 1589493 6447215 := bstep (se 1 (by rfl) ⟨4835411, by rfl⟩ : syracuseStep 6447215 = 9670823) B9670823
theorem B4530451 : Blo 1589493 4530451 := bstep (se 1 (by rfl) ⟨3397838, by rfl⟩ : syracuseStep 4530451 = 6795677) B6795677
theorem B1589567 : Blo 1589493 1589567 := bstep (se 1 (by rfl) ⟨1192175, by rfl⟩ : syracuseStep 1589567 = 2384351) B2384351
theorem B1589807 : Blo 1589493 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B11780891 : Blo 1589493 11780891 := bstep (se 1 (by rfl) ⟨8835668, by rfl⟩ : syracuseStep 11780891 = 17671337) B17671337
theorem B7644233 : Blo 1589493 7644233 := bstep (se 2 (by rfl) ⟨2866587, by rfl⟩ : syracuseStep 7644233 = 5733175) B5733175
theorem B1590527 : Blo 1589493 1590527 := bstep (se 1 (by rfl) ⟨1192895, by rfl⟩ : syracuseStep 1590527 = 2385791) B2385791
theorem B1910251 : Blo 1589493 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B47761183 : Blo 1589493 47761183 := bstep (se 1 (by rfl) ⟨35820887, by rfl⟩ : syracuseStep 47761183 = 71641775) B71641775
theorem B5368463 : Blo 1589493 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B5369597 : Blo 1589493 5369597 := bstep (se 3 (by rfl) ⟨1006799, by rfl⟩ : syracuseStep 5369597 = 2013599) B2013599
theorem B13070447 : Blo 1589493 13070447 := bstep (se 1 (by rfl) ⟨9802835, by rfl⟩ : syracuseStep 13070447 = 19605671) B19605671
theorem B73413215 : Blo 1589493 73413215 := bstep (se 1 (by rfl) ⟨55059911, by rfl⟩ : syracuseStep 73413215 = 110119823) B110119823
theorem B5730983 : Blo 1589493 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B2683739 : Blo 1589493 2683739 := bstep (se 1 (by rfl) ⟨2012804, by rfl⟩ : syracuseStep 2683739 = 4025609) B4025609
theorem B7353553 : Blo 1589493 7353553 := bstep (se 2 (by rfl) ⟨2757582, by rfl⟩ : syracuseStep 7353553 = 5515165) B5515165
theorem B2684407 : Blo 1589493 2684407 := bstep (se 1 (by rfl) ⟨2013305, by rfl⟩ : syracuseStep 2684407 = 4026611) B4026611
theorem B8599679 : Blo 1589493 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B84875525 : Blo 1589493 84875525 := bstep (se 4 (by rfl) ⟨7957080, by rfl⟩ : syracuseStep 84875525 = 15914161) B15914161
theorem B2390399 : Blo 1589493 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B9058715 : Blo 1589493 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B4528639 : Blo 1589493 4528639 := bstep (se 1 (by rfl) ⟨3396479, by rfl⟩ : syracuseStep 4528639 = 6792959) B6792959
theorem B58022567 : Blo 1589493 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B27180035 : Blo 1589493 27180035 := bstep (se 1 (by rfl) ⟨20385026, by rfl⟩ : syracuseStep 27180035 = 40770053) B40770053
theorem B6790567 : Blo 1589493 6790567 := bstep (se 1 (by rfl) ⟨5092925, by rfl⟩ : syracuseStep 6790567 = 10185851) B10185851
theorem B5365439 : Blo 1589493 5365439 := bstep (se 1 (by rfl) ⟨4024079, by rfl⟩ : syracuseStep 5365439 = 8048159) B8048159
theorem B58031909 : Blo 1589493 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B6038185 : Blo 1589493 6038185 := bstep (se 2 (by rfl) ⟨2264319, by rfl⟩ : syracuseStep 6038185 = 4528639) B4528639
theorem B5096155 : Blo 1589493 5096155 := bstep (se 1 (by rfl) ⟨3822116, by rfl⟩ : syracuseStep 5096155 = 7644233) B7644233
theorem B56583683 : Blo 1589493 56583683 := bstep (se 1 (by rfl) ⟨42437762, by rfl⟩ : syracuseStep 56583683 = 84875525) B84875525
theorem B6039143 : Blo 1589493 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B9054089 : Blo 1589493 9054089 := bstep (se 2 (by rfl) ⟨3395283, by rfl⟩ : syracuseStep 9054089 = 6790567) B6790567
theorem B24488671 : Blo 1589493 24488671 := bstep (se 1 (by rfl) ⟨18366503, by rfl⟩ : syracuseStep 24488671 = 36733007) B36733007
theorem B6040601 : Blo 1589493 6040601 := bstep (se 2 (by rfl) ⟨2265225, by rfl⟩ : syracuseStep 6040601 = 4530451) B4530451
theorem B48942143 : Blo 1589493 48942143 := bstep (se 1 (by rfl) ⟨36706607, by rfl⟩ : syracuseStep 48942143 = 73413215) B73413215
theorem B3820655 : Blo 1589493 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B1789159 : Blo 1589493 1789159 := bstep (se 1 (by rfl) ⟨1341869, by rfl⟩ : syracuseStep 1789159 = 2683739) B2683739
theorem B254726309 : Blo 1589493 254726309 := bstep (se 4 (by rfl) ⟨23880591, by rfl⟩ : syracuseStep 254726309 = 47761183) B47761183
theorem B1593599 : Blo 1589493 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B3576959 : Blo 1589493 3576959 := bstep (se 1 (by rfl) ⟨2682719, by rfl⟩ : syracuseStep 3576959 = 5365439) B5365439
theorem B38687939 : Blo 1589493 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B4298143 : Blo 1589493 4298143 := bstep (se 1 (by rfl) ⟨3223607, by rfl⟩ : syracuseStep 4298143 = 6447215) B6447215
theorem B8713631 : Blo 1589493 8713631 := bstep (se 1 (by rfl) ⟨6535223, by rfl⟩ : syracuseStep 8713631 = 13070447) B13070447
theorem B7853927 : Blo 1589493 7853927 := bstep (se 1 (by rfl) ⟨5890445, by rfl⟩ : syracuseStep 7853927 = 11780891) B11780891
theorem B5733119 : Blo 1589493 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B9804737 : Blo 1589493 9804737 := bstep (se 2 (by rfl) ⟨3676776, by rfl⟩ : syracuseStep 9804737 = 7353553) B7353553
theorem B3578975 : Blo 1589493 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B38681711 : Blo 1589493 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B2547001 : Blo 1589493 2547001 := bstep (se 2 (by rfl) ⟨955125, by rfl⟩ : syracuseStep 2547001 = 1910251) B1910251
theorem B3579209 : Blo 1589493 3579209 := bstep (se 2 (by rfl) ⟨1342203, by rfl⟩ : syracuseStep 3579209 = 2684407) B2684407
theorem B18120023 : Blo 1589493 18120023 := bstep (se 1 (by rfl) ⟨13590017, by rfl⟩ : syracuseStep 18120023 = 27180035) B27180035
theorem B3579731 : Blo 1589493 3579731 := bstep (se 1 (by rfl) ⟨2684798, by rfl⟩ : syracuseStep 3579731 = 5369597) B5369597
theorem B2384639 : Blo 1589493 2384639 := bstep (se 1 (by rfl) ⟨1788479, by rfl⟩ : syracuseStep 2384639 = 3576959) B3576959
theorem B5809087 : Blo 1589493 5809087 := bstep (se 1 (by rfl) ⟨4356815, by rfl⟩ : syracuseStep 5809087 = 8713631) B8713631
theorem B2385545 : Blo 1589493 2385545 := bstep (se 2 (by rfl) ⟨894579, by rfl⟩ : syracuseStep 2385545 = 1789159) B1789159
theorem B2385983 : Blo 1589493 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B2386139 : Blo 1589493 2386139 := bstep (se 1 (by rfl) ⟨1789604, by rfl⟩ : syracuseStep 2386139 = 3579209) B3579209
theorem B2386487 : Blo 1589493 2386487 := bstep (se 1 (by rfl) ⟨1789865, by rfl⟩ : syracuseStep 2386487 = 3579731) B3579731
theorem B25791959 : Blo 1589493 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B6794873 : Blo 1589493 6794873 := bstep (se 2 (by rfl) ⟨2548077, by rfl⟩ : syracuseStep 6794873 = 5096155) B5096155
theorem B4026095 : Blo 1589493 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B3396001 : Blo 1589493 3396001 := bstep (se 2 (by rfl) ⟨1273500, by rfl⟩ : syracuseStep 3396001 = 2547001) B2547001
theorem B3822079 : Blo 1589493 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B5730857 : Blo 1589493 5730857 := bstep (se 2 (by rfl) ⟨2149071, by rfl⟩ : syracuseStep 5730857 = 4298143) B4298143
theorem B4027067 : Blo 1589493 4027067 := bstep (se 1 (by rfl) ⟨3020300, by rfl⟩ : syracuseStep 4027067 = 6040601) B6040601
theorem B12080015 : Blo 1589493 12080015 := bstep (se 1 (by rfl) ⟨9060011, by rfl⟩ : syracuseStep 12080015 = 18120023) B18120023
theorem B20943805 : Blo 1589493 20943805 := bstep (se 3 (by rfl) ⟨3926963, by rfl⟩ : syracuseStep 20943805 = 7853927) B7853927
theorem B26145965 : Blo 1589493 26145965 := bstep (se 3 (by rfl) ⟨4902368, by rfl⟩ : syracuseStep 26145965 = 9804737) B9804737
theorem B10188413 : Blo 1589493 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B679270157 : Blo 1589493 679270157 := bstep (se 3 (by rfl) ⟨127363154, by rfl⟩ : syracuseStep 679270157 = 254726309) B254726309
theorem B4249597 : Blo 1589493 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B8050913 : Blo 1589493 8050913 := bstep (se 2 (by rfl) ⟨3019092, by rfl⟩ : syracuseStep 8050913 = 6038185) B6038185
theorem B32651561 : Blo 1589493 32651561 := bstep (se 2 (by rfl) ⟨12244335, by rfl⟩ : syracuseStep 32651561 = 24488671) B24488671
theorem B37722455 : Blo 1589493 37722455 := bstep (se 1 (by rfl) ⟨28291841, by rfl⟩ : syracuseStep 37722455 = 56583683) B56583683
theorem B6036059 : Blo 1589493 6036059 := bstep (se 1 (by rfl) ⟨4527044, by rfl⟩ : syracuseStep 6036059 = 9054089) B9054089
theorem B32628095 : Blo 1589493 32628095 := bstep (se 1 (by rfl) ⟨24471071, by rfl⟩ : syracuseStep 32628095 = 48942143) B48942143
theorem B25787807 : Blo 1589493 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B1589759 : Blo 1589493 1589759 := bstep (se 1 (by rfl) ⟨1192319, by rfl⟩ : syracuseStep 1589759 = 2384639) B2384639
theorem B8053343 : Blo 1589493 8053343 := bstep (se 1 (by rfl) ⟨6040007, by rfl⟩ : syracuseStep 8053343 = 12080015) B12080015
theorem B5096105 : Blo 1589493 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B6792275 : Blo 1589493 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B1590363 : Blo 1589493 1590363 := bstep (se 1 (by rfl) ⟨1192772, by rfl⟩ : syracuseStep 1590363 = 2385545) B2385545
theorem B452846771 : Blo 1589493 452846771 := bstep (se 1 (by rfl) ⟨339635078, by rfl⟩ : syracuseStep 452846771 = 679270157) B679270157
theorem B1590655 : Blo 1589493 1590655 := bstep (se 1 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 1590655 = 2385983) B2385983
theorem B1590759 : Blo 1589493 1590759 := bstep (se 1 (by rfl) ⟨1193069, by rfl⟩ : syracuseStep 1590759 = 2386139) B2386139
theorem B5367275 : Blo 1589493 5367275 := bstep (se 1 (by rfl) ⟨4025456, by rfl⟩ : syracuseStep 5367275 = 8050913) B8050913
theorem B21767707 : Blo 1589493 21767707 := bstep (se 1 (by rfl) ⟨16325780, by rfl⟩ : syracuseStep 21767707 = 32651561) B32651561
theorem B1590991 : Blo 1589493 1590991 := bstep (se 1 (by rfl) ⟨1193243, by rfl⟩ : syracuseStep 1590991 = 2386487) B2386487
theorem B4024039 : Blo 1589493 4024039 := bstep (se 1 (by rfl) ⟨3018029, by rfl⟩ : syracuseStep 4024039 = 6036059) B6036059
theorem B21752063 : Blo 1589493 21752063 := bstep (se 1 (by rfl) ⟨16314047, by rfl⟩ : syracuseStep 21752063 = 32628095) B32628095
theorem B3820571 : Blo 1589493 3820571 := bstep (se 1 (by rfl) ⟨2865428, by rfl⟩ : syracuseStep 3820571 = 5730857) B5730857
theorem B7745449 : Blo 1589493 7745449 := bstep (se 2 (by rfl) ⟨2904543, by rfl⟩ : syracuseStep 7745449 = 5809087) B5809087
theorem B17191871 : Blo 1589493 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B2684063 : Blo 1589493 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B5666129 : Blo 1589493 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B2684711 : Blo 1589493 2684711 := bstep (se 1 (by rfl) ⟨2013533, by rfl⟩ : syracuseStep 2684711 = 4027067) B4027067
theorem B4528001 : Blo 1589493 4528001 := bstep (se 2 (by rfl) ⟨1698000, by rfl⟩ : syracuseStep 4528001 = 3396001) B3396001
theorem B17430643 : Blo 1589493 17430643 := bstep (se 1 (by rfl) ⟨13072982, by rfl⟩ : syracuseStep 17430643 = 26145965) B26145965
theorem B27925073 : Blo 1589493 27925073 := bstep (se 2 (by rfl) ⟨10471902, by rfl⟩ : syracuseStep 27925073 = 20943805) B20943805
theorem B25148303 : Blo 1589493 25148303 := bstep (se 1 (by rfl) ⟨18861227, by rfl⟩ : syracuseStep 25148303 = 37722455) B37722455
theorem B17194639 : Blo 1589493 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B4529915 : Blo 1589493 4529915 := bstep (se 1 (by rfl) ⟨3397436, by rfl⟩ : syracuseStep 4529915 = 6794873) B6794873
theorem B23240857 : Blo 1589493 23240857 := bstep (se 2 (by rfl) ⟨8715321, by rfl⟩ : syracuseStep 23240857 = 17430643) B17430643
theorem B18112733 : Blo 1589493 18112733 := bstep (se 3 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 18112733 = 6792275) B6792275
theorem B11461247 : Blo 1589493 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B3777419 : Blo 1589493 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B14501375 : Blo 1589493 14501375 := bstep (se 1 (by rfl) ⟨10876031, by rfl⟩ : syracuseStep 14501375 = 21752063) B21752063
theorem B5368895 : Blo 1589493 5368895 := bstep (se 1 (by rfl) ⟨4026671, by rfl⟩ : syracuseStep 5368895 = 8053343) B8053343
theorem B1789375 : Blo 1589493 1789375 := bstep (se 1 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 1789375 = 2684063) B2684063
theorem B1789807 : Blo 1589493 1789807 := bstep (se 1 (by rfl) ⟨1342355, by rfl⟩ : syracuseStep 1789807 = 2684711) B2684711
theorem B18616715 : Blo 1589493 18616715 := bstep (se 1 (by rfl) ⟨13962536, by rfl⟩ : syracuseStep 18616715 = 27925073) B27925073
theorem B16765535 : Blo 1589493 16765535 := bstep (se 1 (by rfl) ⟨12574151, by rfl⟩ : syracuseStep 16765535 = 25148303) B25148303
theorem B22926185 : Blo 1589493 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B3019943 : Blo 1589493 3019943 := bstep (se 1 (by rfl) ⟨2264957, by rfl⟩ : syracuseStep 3019943 = 4529915) B4529915
theorem B10327265 : Blo 1589493 10327265 := bstep (se 2 (by rfl) ⟨3872724, by rfl⟩ : syracuseStep 10327265 = 7745449) B7745449
theorem B3397403 : Blo 1589493 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B301897847 : Blo 1589493 301897847 := bstep (se 1 (by rfl) ⟨226423385, by rfl⟩ : syracuseStep 301897847 = 452846771) B452846771
theorem B3578183 : Blo 1589493 3578183 := bstep (se 1 (by rfl) ⟨2683637, by rfl⟩ : syracuseStep 3578183 = 5367275) B5367275
theorem B2547047 : Blo 1589493 2547047 := bstep (se 1 (by rfl) ⟨1910285, by rfl⟩ : syracuseStep 2547047 = 3820571) B3820571
theorem B29023609 : Blo 1589493 29023609 := bstep (se 2 (by rfl) ⟨10883853, by rfl⟩ : syracuseStep 29023609 = 21767707) B21767707
theorem B5365385 : Blo 1589493 5365385 := bstep (se 2 (by rfl) ⟨2012019, by rfl⟩ : syracuseStep 5365385 = 4024039) B4024039
theorem B12074669 : Blo 1589493 12074669 := bstep (se 3 (by rfl) ⟨2264000, by rfl⟩ : syracuseStep 12074669 = 4528001) B4528001
theorem B12075155 : Blo 1589493 12075155 := bstep (se 1 (by rfl) ⟨9056366, by rfl⟩ : syracuseStep 12075155 = 18112733) B18112733
theorem B12411143 : Blo 1589493 12411143 := bstep (se 1 (by rfl) ⟨9308357, by rfl⟩ : syracuseStep 12411143 = 18616715) B18616715
theorem B8053181 : Blo 1589493 8053181 := bstep (se 3 (by rfl) ⟨1509971, by rfl⟩ : syracuseStep 8053181 = 3019943) B3019943
theorem B9667583 : Blo 1589493 9667583 := bstep (se 1 (by rfl) ⟨7250687, by rfl⟩ : syracuseStep 9667583 = 14501375) B14501375
theorem B2385455 : Blo 1589493 2385455 := bstep (se 1 (by rfl) ⟨1789091, by rfl⟩ : syracuseStep 2385455 = 3578183) B3578183
theorem B2385833 : Blo 1589493 2385833 := bstep (se 2 (by rfl) ⟨894687, by rfl⟩ : syracuseStep 2385833 = 1789375) B1789375
theorem B1698031 : Blo 1589493 1698031 := bstep (se 1 (by rfl) ⟨1273523, by rfl⟩ : syracuseStep 1698031 = 2547047) B2547047
theorem B2386409 : Blo 1589493 2386409 := bstep (se 2 (by rfl) ⟨894903, by rfl⟩ : syracuseStep 2386409 = 1789807) B1789807
theorem B11177023 : Blo 1589493 11177023 := bstep (se 1 (by rfl) ⟨8382767, by rfl⟩ : syracuseStep 11177023 = 16765535) B16765535
theorem B6884843 : Blo 1589493 6884843 := bstep (se 1 (by rfl) ⟨5163632, by rfl⟩ : syracuseStep 6884843 = 10327265) B10327265
theorem B2264935 : Blo 1589493 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B201265231 : Blo 1589493 201265231 := bstep (se 1 (by rfl) ⟨150948923, by rfl⟩ : syracuseStep 201265231 = 301897847) B301897847
theorem B10073117 : Blo 1589493 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B3576923 : Blo 1589493 3576923 := bstep (se 1 (by rfl) ⟨2682692, by rfl⟩ : syracuseStep 3576923 = 5365385) B5365385
theorem B8049779 : Blo 1589493 8049779 := bstep (se 1 (by rfl) ⟨6037334, by rfl⟩ : syracuseStep 8049779 = 12074669) B12074669
theorem B30987809 : Blo 1589493 30987809 := bstep (se 2 (by rfl) ⟨11620428, by rfl⟩ : syracuseStep 30987809 = 23240857) B23240857
theorem B7640831 : Blo 1589493 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B15284123 : Blo 1589493 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B38698145 : Blo 1589493 38698145 := bstep (se 2 (by rfl) ⟨14511804, by rfl⟩ : syracuseStep 38698145 = 29023609) B29023609
theorem B3579263 : Blo 1589493 3579263 := bstep (se 1 (by rfl) ⟨2684447, by rfl⟩ : syracuseStep 3579263 = 5368895) B5368895
theorem B26861645 : Blo 1589493 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B268353641 : Blo 1589493 268353641 := bstep (se 2 (by rfl) ⟨100632615, by rfl⟩ : syracuseStep 268353641 = 201265231) B201265231
theorem B8274095 : Blo 1589493 8274095 := bstep (se 1 (by rfl) ⟨6205571, by rfl⟩ : syracuseStep 8274095 = 12411143) B12411143
theorem B2384615 : Blo 1589493 2384615 := bstep (se 1 (by rfl) ⟨1788461, by rfl⟩ : syracuseStep 2384615 = 3576923) B3576923
theorem B5366519 : Blo 1589493 5366519 := bstep (se 1 (by rfl) ⟨4024889, by rfl⟩ : syracuseStep 5366519 = 8049779) B8049779
theorem B1590303 : Blo 1589493 1590303 := bstep (se 1 (by rfl) ⟨1192727, by rfl⟩ : syracuseStep 1590303 = 2385455) B2385455
theorem B1590555 : Blo 1589493 1590555 := bstep (se 1 (by rfl) ⟨1192916, by rfl⟩ : syracuseStep 1590555 = 2385833) B2385833
theorem B18359581 : Blo 1589493 18359581 := bstep (se 3 (by rfl) ⟨3442421, by rfl⟩ : syracuseStep 18359581 = 6884843) B6884843
theorem B14902697 : Blo 1589493 14902697 := bstep (se 2 (by rfl) ⟨5588511, by rfl⟩ : syracuseStep 14902697 = 11177023) B11177023
theorem B1590939 : Blo 1589493 1590939 := bstep (se 1 (by rfl) ⟨1193204, by rfl⟩ : syracuseStep 1590939 = 2386409) B2386409
theorem B20375549 : Blo 1589493 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B25798763 : Blo 1589493 25798763 := bstep (se 1 (by rfl) ⟨19349072, by rfl⟩ : syracuseStep 25798763 = 38698145) B38698145
theorem B2386175 : Blo 1589493 2386175 := bstep (se 1 (by rfl) ⟨1789631, by rfl⟩ : syracuseStep 2386175 = 3579263) B3579263
theorem B5368787 : Blo 1589493 5368787 := bstep (se 1 (by rfl) ⟨4026590, by rfl⟩ : syracuseStep 5368787 = 8053181) B8053181
theorem B2264041 : Blo 1589493 2264041 := bstep (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) B1698031
theorem B3019913 : Blo 1589493 3019913 := bstep (se 2 (by rfl) ⟨1132467, by rfl⟩ : syracuseStep 3019913 = 2264935) B2264935
theorem B8050103 : Blo 1589493 8050103 := bstep (se 1 (by rfl) ⟨6037577, by rfl⟩ : syracuseStep 8050103 = 12075155) B12075155
theorem B6445055 : Blo 1589493 6445055 := bstep (se 1 (by rfl) ⟨4833791, by rfl⟩ : syracuseStep 6445055 = 9667583) B9667583
theorem B20658539 : Blo 1589493 20658539 := bstep (se 1 (by rfl) ⟨15493904, by rfl⟩ : syracuseStep 20658539 = 30987809) B30987809
theorem B10189415 : Blo 1589493 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B71631053 : Blo 1589493 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B68796701 : Blo 1589493 68796701 := bstep (se 3 (by rfl) ⟨12899381, by rfl⟩ : syracuseStep 68796701 = 25798763) B25798763
theorem B1589743 : Blo 1589493 1589743 := bstep (se 1 (by rfl) ⟨1192307, by rfl⟩ : syracuseStep 1589743 = 2384615) B2384615
theorem B5366735 : Blo 1589493 5366735 := bstep (se 1 (by rfl) ⟨4025051, by rfl⟩ : syracuseStep 5366735 = 8050103) B8050103
theorem B13583699 : Blo 1589493 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B1590783 : Blo 1589493 1590783 := bstep (se 1 (by rfl) ⟨1193087, by rfl⟩ : syracuseStep 1590783 = 2386175) B2386175
theorem B13772359 : Blo 1589493 13772359 := bstep (se 1 (by rfl) ⟨10329269, by rfl⟩ : syracuseStep 13772359 = 20658539) B20658539
theorem B24479441 : Blo 1589493 24479441 := bstep (se 2 (by rfl) ⟨9179790, by rfl⟩ : syracuseStep 24479441 = 18359581) B18359581
theorem B6792943 : Blo 1589493 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B5516063 : Blo 1589493 5516063 := bstep (se 1 (by rfl) ⟨4137047, by rfl⟩ : syracuseStep 5516063 = 8274095) B8274095
theorem B3018721 : Blo 1589493 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B178902427 : Blo 1589493 178902427 := bstep (se 1 (by rfl) ⟨134176820, by rfl⟩ : syracuseStep 178902427 = 268353641) B268353641
theorem B3577679 : Blo 1589493 3577679 := bstep (se 1 (by rfl) ⟨2683259, by rfl⟩ : syracuseStep 3577679 = 5366519) B5366519
theorem B2013275 : Blo 1589493 2013275 := bstep (se 1 (by rfl) ⟨1509956, by rfl⟩ : syracuseStep 2013275 = 3019913) B3019913
theorem B9935131 : Blo 1589493 9935131 := bstep (se 1 (by rfl) ⟨7451348, by rfl⟩ : syracuseStep 9935131 = 14902697) B14902697
theorem B3579191 : Blo 1589493 3579191 := bstep (se 1 (by rfl) ⟨2684393, by rfl⟩ : syracuseStep 3579191 = 5368787) B5368787
theorem B17186813 : Blo 1589493 17186813 := bstep (se 3 (by rfl) ⟨3222527, by rfl⟩ : syracuseStep 17186813 = 6445055) B6445055
theorem B13246841 : Blo 1589493 13246841 := bstep (se 2 (by rfl) ⟨4967565, by rfl⟩ : syracuseStep 13246841 = 9935131) B9935131
theorem B16319627 : Blo 1589493 16319627 := bstep (se 1 (by rfl) ⟨12239720, by rfl⟩ : syracuseStep 16319627 = 24479441) B24479441
theorem B2385119 : Blo 1589493 2385119 := bstep (se 1 (by rfl) ⟨1788839, by rfl⟩ : syracuseStep 2385119 = 3577679) B3577679
theorem B238536569 : Blo 1589493 238536569 := bstep (se 2 (by rfl) ⟨89451213, by rfl⟩ : syracuseStep 238536569 = 178902427) B178902427
theorem B2386127 : Blo 1589493 2386127 := bstep (se 1 (by rfl) ⟨1789595, by rfl⟩ : syracuseStep 2386127 = 3579191) B3579191
theorem B4024961 : Blo 1589493 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B47754035 : Blo 1589493 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B5368733 : Blo 1589493 5368733 := bstep (se 3 (by rfl) ⟨1006637, by rfl⟩ : syracuseStep 5368733 = 2013275) B2013275
theorem B73452581 : Blo 1589493 73452581 := bstep (se 4 (by rfl) ⟨6886179, by rfl⟩ : syracuseStep 73452581 = 13772359) B13772359
theorem B9055799 : Blo 1589493 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B9057257 : Blo 1589493 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B11457875 : Blo 1589493 11457875 := bstep (se 1 (by rfl) ⟨8593406, by rfl⟩ : syracuseStep 11457875 = 17186813) B17186813
theorem B45864467 : Blo 1589493 45864467 := bstep (se 1 (by rfl) ⟨34398350, by rfl⟩ : syracuseStep 45864467 = 68796701) B68796701
theorem B3577823 : Blo 1589493 3577823 := bstep (se 1 (by rfl) ⟨2683367, by rfl⟩ : syracuseStep 3577823 = 5366735) B5366735
theorem B3677375 : Blo 1589493 3677375 := bstep (se 1 (by rfl) ⟨2758031, by rfl⟩ : syracuseStep 3677375 = 5516063) B5516063
theorem B8831227 : Blo 1589493 8831227 := bstep (se 1 (by rfl) ⟨6623420, by rfl⟩ : syracuseStep 8831227 = 13246841) B13246841
theorem B9806333 : Blo 1589493 9806333 := bstep (se 3 (by rfl) ⟨1838687, by rfl⟩ : syracuseStep 9806333 = 3677375) B3677375
theorem B6038171 : Blo 1589493 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B10879751 : Blo 1589493 10879751 := bstep (se 1 (by rfl) ⟨8159813, by rfl⟩ : syracuseStep 10879751 = 16319627) B16319627
theorem B1590079 : Blo 1589493 1590079 := bstep (se 1 (by rfl) ⟨1192559, by rfl⟩ : syracuseStep 1590079 = 2385119) B2385119
theorem B159024379 : Blo 1589493 159024379 := bstep (se 1 (by rfl) ⟨119268284, by rfl⟩ : syracuseStep 159024379 = 238536569) B238536569
theorem B2385215 : Blo 1589493 2385215 := bstep (se 1 (by rfl) ⟨1788911, by rfl⟩ : syracuseStep 2385215 = 3577823) B3577823
theorem B1590751 : Blo 1589493 1590751 := bstep (se 1 (by rfl) ⟨1193063, by rfl⟩ : syracuseStep 1590751 = 2386127) B2386127
theorem B31836023 : Blo 1589493 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B7638583 : Blo 1589493 7638583 := bstep (se 1 (by rfl) ⟨5728937, by rfl⟩ : syracuseStep 7638583 = 11457875) B11457875
theorem B30576311 : Blo 1589493 30576311 := bstep (se 1 (by rfl) ⟨22932233, by rfl⟩ : syracuseStep 30576311 = 45864467) B45864467
theorem B2683307 : Blo 1589493 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B48968387 : Blo 1589493 48968387 := bstep (se 1 (by rfl) ⟨36726290, by rfl⟩ : syracuseStep 48968387 = 73452581) B73452581
theorem B3579155 : Blo 1589493 3579155 := bstep (se 1 (by rfl) ⟨2684366, by rfl⟩ : syracuseStep 3579155 = 5368733) B5368733
theorem B6037199 : Blo 1589493 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B32645591 : Blo 1589493 32645591 := bstep (se 1 (by rfl) ⟨24484193, by rfl⟩ : syracuseStep 32645591 = 48968387) B48968387
theorem B1590143 : Blo 1589493 1590143 := bstep (se 1 (by rfl) ⟨1192607, by rfl⟩ : syracuseStep 1590143 = 2385215) B2385215
theorem B26150221 : Blo 1589493 26150221 := bstep (se 3 (by rfl) ⟨4903166, by rfl⟩ : syracuseStep 26150221 = 9806333) B9806333
theorem B10184777 : Blo 1589493 10184777 := bstep (se 2 (by rfl) ⟨3819291, by rfl⟩ : syracuseStep 10184777 = 7638583) B7638583
theorem B2386103 : Blo 1589493 2386103 := bstep (se 1 (by rfl) ⟨1789577, by rfl⟩ : syracuseStep 2386103 = 3579155) B3579155
theorem B20384207 : Blo 1589493 20384207 := bstep (se 1 (by rfl) ⟨15288155, by rfl⟩ : syracuseStep 20384207 = 30576311) B30576311
theorem B4024799 : Blo 1589493 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B1788871 : Blo 1589493 1788871 := bstep (se 1 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 1788871 = 2683307) B2683307
theorem B11774969 : Blo 1589493 11774969 := bstep (se 2 (by rfl) ⟨4415613, by rfl⟩ : syracuseStep 11774969 = 8831227) B8831227
theorem B4025447 : Blo 1589493 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B7253167 : Blo 1589493 7253167 := bstep (se 1 (by rfl) ⟨5439875, by rfl⟩ : syracuseStep 7253167 = 10879751) B10879751
theorem B21224015 : Blo 1589493 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B212032505 : Blo 1589493 212032505 := bstep (se 2 (by rfl) ⟨79512189, by rfl⟩ : syracuseStep 212032505 = 159024379) B159024379
theorem B2385161 : Blo 1589493 2385161 := bstep (se 2 (by rfl) ⟨894435, by rfl⟩ : syracuseStep 2385161 = 1788871) B1788871
theorem B1590735 : Blo 1589493 1590735 := bstep (se 1 (by rfl) ⟨1193051, by rfl⟩ : syracuseStep 1590735 = 2386103) B2386103
theorem B14149343 : Blo 1589493 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B7849979 : Blo 1589493 7849979 := bstep (se 1 (by rfl) ⟨5887484, by rfl⟩ : syracuseStep 7849979 = 11774969) B11774969
theorem B141355003 : Blo 1589493 141355003 := bstep (se 1 (by rfl) ⟨106016252, by rfl⟩ : syracuseStep 141355003 = 212032505) B212032505
theorem B9670889 : Blo 1589493 9670889 := bstep (se 2 (by rfl) ⟨3626583, by rfl⟩ : syracuseStep 9670889 = 7253167) B7253167
theorem B2683199 : Blo 1589493 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B2683631 : Blo 1589493 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B21763727 : Blo 1589493 21763727 := bstep (se 1 (by rfl) ⟨16322795, by rfl⟩ : syracuseStep 21763727 = 32645591) B32645591
theorem B6789851 : Blo 1589493 6789851 := bstep (se 1 (by rfl) ⟨5092388, by rfl⟩ : syracuseStep 6789851 = 10184777) B10184777
theorem B13589471 : Blo 1589493 13589471 := bstep (se 1 (by rfl) ⟨10192103, by rfl⟩ : syracuseStep 13589471 = 20384207) B20384207
theorem B139467845 : Blo 1589493 139467845 := bstep (se 4 (by rfl) ⟨13075110, by rfl⟩ : syracuseStep 139467845 = 26150221) B26150221
theorem B6447259 : Blo 1589493 6447259 := bstep (se 1 (by rfl) ⟨4835444, by rfl⟩ : syracuseStep 6447259 = 9670889) B9670889
theorem B1590107 : Blo 1589493 1590107 := bstep (se 1 (by rfl) ⟨1192580, by rfl⟩ : syracuseStep 1590107 = 2385161) B2385161
theorem B14509151 : Blo 1589493 14509151 := bstep (se 1 (by rfl) ⟨10881863, by rfl⟩ : syracuseStep 14509151 = 21763727) B21763727
theorem B1788799 : Blo 1589493 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B1789087 : Blo 1589493 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B9432895 : Blo 1589493 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B4526567 : Blo 1589493 4526567 := bstep (se 1 (by rfl) ⟨3394925, by rfl⟩ : syracuseStep 4526567 = 6789851) B6789851
theorem B5233319 : Blo 1589493 5233319 := bstep (se 1 (by rfl) ⟨3924989, by rfl⟩ : syracuseStep 5233319 = 7849979) B7849979
theorem B9059647 : Blo 1589493 9059647 := bstep (se 1 (by rfl) ⟨6794735, by rfl⟩ : syracuseStep 9059647 = 13589471) B13589471
theorem B92978563 : Blo 1589493 92978563 := bstep (se 1 (by rfl) ⟨69733922, by rfl⟩ : syracuseStep 92978563 = 139467845) B139467845
theorem B188473337 : Blo 1589493 188473337 := bstep (se 2 (by rfl) ⟨70677501, by rfl⟩ : syracuseStep 188473337 = 141355003) B141355003
theorem B2385065 : Blo 1589493 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B2385449 : Blo 1589493 2385449 := bstep (se 2 (by rfl) ⟨894543, by rfl⟩ : syracuseStep 2385449 = 1789087) B1789087
theorem B123971417 : Blo 1589493 123971417 := bstep (se 2 (by rfl) ⟨46489281, by rfl⟩ : syracuseStep 123971417 = 92978563) B92978563
theorem B12577193 : Blo 1589493 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B125648891 : Blo 1589493 125648891 := bstep (se 1 (by rfl) ⟨94236668, by rfl⟩ : syracuseStep 125648891 = 188473337) B188473337
theorem B3017711 : Blo 1589493 3017711 := bstep (se 1 (by rfl) ⟨2263283, by rfl⟩ : syracuseStep 3017711 = 4526567) B4526567
theorem B34385381 : Blo 1589493 34385381 := bstep (se 4 (by rfl) ⟨3223629, by rfl⟩ : syracuseStep 34385381 = 6447259) B6447259
theorem B12079529 : Blo 1589493 12079529 := bstep (se 2 (by rfl) ⟨4529823, by rfl⟩ : syracuseStep 12079529 = 9059647) B9059647
theorem B9672767 : Blo 1589493 9672767 := bstep (se 1 (by rfl) ⟨7254575, by rfl⟩ : syracuseStep 9672767 = 14509151) B14509151
theorem B3488879 : Blo 1589493 3488879 := bstep (se 1 (by rfl) ⟨2616659, by rfl⟩ : syracuseStep 3488879 = 5233319) B5233319
theorem B8053019 : Blo 1589493 8053019 := bstep (se 1 (by rfl) ⟨6039764, by rfl⟩ : syracuseStep 8053019 = 12079529) B12079529
theorem B1590043 : Blo 1589493 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B1590299 : Blo 1589493 1590299 := bstep (se 1 (by rfl) ⟨1192724, by rfl⟩ : syracuseStep 1590299 = 2385449) B2385449
theorem B6448511 : Blo 1589493 6448511 := bstep (se 1 (by rfl) ⟨4836383, by rfl⟩ : syracuseStep 6448511 = 9672767) B9672767
theorem B22923587 : Blo 1589493 22923587 := bstep (se 1 (by rfl) ⟨17192690, by rfl⟩ : syracuseStep 22923587 = 34385381) B34385381
theorem B83765927 : Blo 1589493 83765927 := bstep (se 1 (by rfl) ⟨62824445, by rfl⟩ : syracuseStep 83765927 = 125648891) B125648891
theorem B8384795 : Blo 1589493 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B2011807 : Blo 1589493 2011807 := bstep (se 1 (by rfl) ⟨1508855, by rfl⟩ : syracuseStep 2011807 = 3017711) B3017711
theorem B82647611 : Blo 1589493 82647611 := bstep (se 1 (by rfl) ⟨61985708, by rfl⟩ : syracuseStep 82647611 = 123971417) B123971417
theorem B2325919 : Blo 1589493 2325919 := bstep (se 1 (by rfl) ⟨1744439, by rfl⟩ : syracuseStep 2325919 = 3488879) B3488879
theorem B5589863 : Blo 1589493 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B5368679 : Blo 1589493 5368679 := bstep (se 1 (by rfl) ⟨4026509, by rfl⟩ : syracuseStep 5368679 = 8053019) B8053019
theorem B2682409 : Blo 1589493 2682409 := bstep (se 2 (by rfl) ⟨1005903, by rfl⟩ : syracuseStep 2682409 = 2011807) B2011807
theorem B15282391 : Blo 1589493 15282391 := bstep (se 1 (by rfl) ⟨11461793, by rfl⟩ : syracuseStep 15282391 = 22923587) B22923587
theorem B223375805 : Blo 1589493 223375805 := bstep (se 3 (by rfl) ⟨41882963, by rfl⟩ : syracuseStep 223375805 = 83765927) B83765927
theorem B3101225 : Blo 1589493 3101225 := bstep (se 2 (by rfl) ⟨1162959, by rfl⟩ : syracuseStep 3101225 = 2325919) B2325919
theorem B4299007 : Blo 1589493 4299007 := bstep (se 1 (by rfl) ⟨3224255, by rfl⟩ : syracuseStep 4299007 = 6448511) B6448511
theorem B55098407 : Blo 1589493 55098407 := bstep (se 1 (by rfl) ⟨41323805, by rfl⟩ : syracuseStep 55098407 = 82647611) B82647611
theorem B20376521 : Blo 1589493 20376521 := bstep (se 2 (by rfl) ⟨7641195, by rfl⟩ : syracuseStep 20376521 = 15282391) B15282391
theorem B148917203 : Blo 1589493 148917203 := bstep (se 1 (by rfl) ⟨111687902, by rfl⟩ : syracuseStep 148917203 = 223375805) B223375805
theorem B8269933 : Blo 1589493 8269933 := bstep (se 3 (by rfl) ⟨1550612, by rfl⟩ : syracuseStep 8269933 = 3101225) B3101225
theorem B3576545 : Blo 1589493 3576545 := bstep (se 2 (by rfl) ⟨1341204, by rfl⟩ : syracuseStep 3576545 = 2682409) B2682409
theorem B146929085 : Blo 1589493 146929085 := bstep (se 3 (by rfl) ⟨27549203, by rfl⟩ : syracuseStep 146929085 = 55098407) B55098407
theorem B5732009 : Blo 1589493 5732009 := bstep (se 2 (by rfl) ⟨2149503, by rfl⟩ : syracuseStep 5732009 = 4299007) B4299007
theorem B3726575 : Blo 1589493 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B3579119 : Blo 1589493 3579119 := bstep (se 1 (by rfl) ⟨2684339, by rfl⟩ : syracuseStep 3579119 = 5368679) B5368679
theorem B11026577 : Blo 1589493 11026577 := bstep (se 2 (by rfl) ⟨4134966, by rfl⟩ : syracuseStep 11026577 = 8269933) B8269933
theorem B2384363 : Blo 1589493 2384363 := bstep (se 1 (by rfl) ⟨1788272, by rfl⟩ : syracuseStep 2384363 = 3576545) B3576545
theorem B97952723 : Blo 1589493 97952723 := bstep (se 1 (by rfl) ⟨73464542, by rfl⟩ : syracuseStep 97952723 = 146929085) B146929085
theorem B13584347 : Blo 1589493 13584347 := bstep (se 1 (by rfl) ⟨10188260, by rfl⟩ : syracuseStep 13584347 = 20376521) B20376521
theorem B2484383 : Blo 1589493 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2386079 : Blo 1589493 2386079 := bstep (se 1 (by rfl) ⟨1789559, by rfl⟩ : syracuseStep 2386079 = 3579119) B3579119
theorem B3821339 : Blo 1589493 3821339 := bstep (se 1 (by rfl) ⟨2866004, by rfl⟩ : syracuseStep 3821339 = 5732009) B5732009
theorem B99278135 : Blo 1589493 99278135 := bstep (se 1 (by rfl) ⟨74458601, by rfl⟩ : syracuseStep 99278135 = 148917203) B148917203
theorem B1589575 : Blo 1589493 1589575 := bstep (se 1 (by rfl) ⟨1192181, by rfl⟩ : syracuseStep 1589575 = 2384363) B2384363
theorem B1590719 : Blo 1589493 1590719 := bstep (se 1 (by rfl) ⟨1193039, by rfl⟩ : syracuseStep 1590719 = 2386079) B2386079
theorem B66185423 : Blo 1589493 66185423 := bstep (se 1 (by rfl) ⟨49639067, by rfl⟩ : syracuseStep 66185423 = 99278135) B99278135
theorem B29404205 : Blo 1589493 29404205 := bstep (se 3 (by rfl) ⟨5513288, by rfl⟩ : syracuseStep 29404205 = 11026577) B11026577
theorem B65301815 : Blo 1589493 65301815 := bstep (se 1 (by rfl) ⟨48976361, by rfl⟩ : syracuseStep 65301815 = 97952723) B97952723
theorem B9056231 : Blo 1589493 9056231 := bstep (se 1 (by rfl) ⟨6792173, by rfl⟩ : syracuseStep 9056231 = 13584347) B13584347
theorem B26500085 : Blo 1589493 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B2547559 : Blo 1589493 2547559 := bstep (se 1 (by rfl) ⟨1910669, by rfl⟩ : syracuseStep 2547559 = 3821339) B3821339
theorem B44123615 : Blo 1589493 44123615 := bstep (se 1 (by rfl) ⟨33092711, by rfl⟩ : syracuseStep 44123615 = 66185423) B66185423
theorem B43534543 : Blo 1589493 43534543 := bstep (se 1 (by rfl) ⟨32650907, by rfl⟩ : syracuseStep 43534543 = 65301815) B65301815
theorem B17666723 : Blo 1589493 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B3396745 : Blo 1589493 3396745 := bstep (se 2 (by rfl) ⟨1273779, by rfl⟩ : syracuseStep 3396745 = 2547559) B2547559
theorem B19602803 : Blo 1589493 19602803 := bstep (se 1 (by rfl) ⟨14702102, by rfl⟩ : syracuseStep 19602803 = 29404205) B29404205
theorem B6037487 : Blo 1589493 6037487 := bstep (se 1 (by rfl) ⟨4528115, by rfl⟩ : syracuseStep 6037487 = 9056231) B9056231
theorem B13068535 : Blo 1589493 13068535 := bstep (se 1 (by rfl) ⟨9801401, by rfl⟩ : syracuseStep 13068535 = 19602803) B19602803
theorem B4024991 : Blo 1589493 4024991 := bstep (se 1 (by rfl) ⟨3018743, by rfl⟩ : syracuseStep 4024991 = 6037487) B6037487
theorem B58046057 : Blo 1589493 58046057 := bstep (se 2 (by rfl) ⟨21767271, by rfl⟩ : syracuseStep 58046057 = 43534543) B43534543
theorem B11777815 : Blo 1589493 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B29415743 : Blo 1589493 29415743 := bstep (se 1 (by rfl) ⟨22061807, by rfl⟩ : syracuseStep 29415743 = 44123615) B44123615
theorem B4528993 : Blo 1589493 4528993 := bstep (se 2 (by rfl) ⟨1698372, by rfl⟩ : syracuseStep 4528993 = 3396745) B3396745
theorem B17424713 : Blo 1589493 17424713 := bstep (se 2 (by rfl) ⟨6534267, by rfl⟩ : syracuseStep 17424713 = 13068535) B13068535
theorem B6038657 : Blo 1589493 6038657 := bstep (se 2 (by rfl) ⟨2264496, by rfl⟩ : syracuseStep 6038657 = 4528993) B4528993
theorem B2683327 : Blo 1589493 2683327 := bstep (se 1 (by rfl) ⟨2012495, by rfl⟩ : syracuseStep 2683327 = 4024991) B4024991
theorem B38697371 : Blo 1589493 38697371 := bstep (se 1 (by rfl) ⟨29023028, by rfl⟩ : syracuseStep 38697371 = 58046057) B58046057
theorem B19610495 : Blo 1589493 19610495 := bstep (se 1 (by rfl) ⟨14707871, by rfl⟩ : syracuseStep 19610495 = 29415743) B29415743
theorem B15703753 : Blo 1589493 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B11616475 : Blo 1589493 11616475 := bstep (se 1 (by rfl) ⟨8712356, by rfl⟩ : syracuseStep 11616475 = 17424713) B17424713
theorem B25798247 : Blo 1589493 25798247 := bstep (se 1 (by rfl) ⟨19348685, by rfl⟩ : syracuseStep 25798247 = 38697371) B38697371
theorem B4025771 : Blo 1589493 4025771 := bstep (se 1 (by rfl) ⟨3019328, by rfl⟩ : syracuseStep 4025771 = 6038657) B6038657
theorem B3577769 : Blo 1589493 3577769 := bstep (se 2 (by rfl) ⟨1341663, by rfl⟩ : syracuseStep 3577769 = 2683327) B2683327
theorem B13073663 : Blo 1589493 13073663 := bstep (se 1 (by rfl) ⟨9805247, by rfl⟩ : syracuseStep 13073663 = 19610495) B19610495
theorem B20938337 : Blo 1589493 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B2385179 : Blo 1589493 2385179 := bstep (se 1 (by rfl) ⟨1788884, by rfl⟩ : syracuseStep 2385179 = 3577769) B3577769
theorem B17198831 : Blo 1589493 17198831 := bstep (se 1 (by rfl) ⟨12899123, by rfl⟩ : syracuseStep 17198831 = 25798247) B25798247
theorem B2683847 : Blo 1589493 2683847 := bstep (se 1 (by rfl) ⟨2012885, by rfl⟩ : syracuseStep 2683847 = 4025771) B4025771
theorem B15488633 : Blo 1589493 15488633 := bstep (se 2 (by rfl) ⟨5808237, by rfl⟩ : syracuseStep 15488633 = 11616475) B11616475
theorem B34863101 : Blo 1589493 34863101 := bstep (se 3 (by rfl) ⟨6536831, by rfl⟩ : syracuseStep 34863101 = 13073663) B13073663
theorem B13958891 : Blo 1589493 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B1590119 : Blo 1589493 1590119 := bstep (se 1 (by rfl) ⟨1192589, by rfl⟩ : syracuseStep 1590119 = 2385179) B2385179
theorem B23242067 : Blo 1589493 23242067 := bstep (se 1 (by rfl) ⟨17431550, by rfl⟩ : syracuseStep 23242067 = 34863101) B34863101
theorem B1789231 : Blo 1589493 1789231 := bstep (se 1 (by rfl) ⟨1341923, by rfl⟩ : syracuseStep 1789231 = 2683847) B2683847
theorem B10325755 : Blo 1589493 10325755 := bstep (se 1 (by rfl) ⟨7744316, by rfl⟩ : syracuseStep 10325755 = 15488633) B15488633
theorem B11465887 : Blo 1589493 11465887 := bstep (se 1 (by rfl) ⟨8599415, by rfl⟩ : syracuseStep 11465887 = 17198831) B17198831
theorem B9305927 : Blo 1589493 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B15287849 : Blo 1589493 15287849 := bstep (se 2 (by rfl) ⟨5732943, by rfl⟩ : syracuseStep 15287849 = 11465887) B11465887
theorem B2385641 : Blo 1589493 2385641 := bstep (se 2 (by rfl) ⟨894615, by rfl⟩ : syracuseStep 2385641 = 1789231) B1789231
theorem B6203951 : Blo 1589493 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B991661525 : Blo 1589493 991661525 := bstep (se 7 (by rfl) ⟨11621033, by rfl⟩ : syracuseStep 991661525 = 23242067) B23242067
theorem B13767673 : Blo 1589493 13767673 := bstep (se 2 (by rfl) ⟨5162877, by rfl⟩ : syracuseStep 13767673 = 10325755) B10325755
theorem B10191899 : Blo 1589493 10191899 := bstep (se 1 (by rfl) ⟨7643924, by rfl⟩ : syracuseStep 10191899 = 15287849) B15287849
theorem B1590427 : Blo 1589493 1590427 := bstep (se 1 (by rfl) ⟨1192820, by rfl⟩ : syracuseStep 1590427 = 2385641) B2385641
theorem B661107683 : Blo 1589493 661107683 := bstep (se 1 (by rfl) ⟨495830762, by rfl⟩ : syracuseStep 661107683 = 991661525) B991661525
theorem B18356897 : Blo 1589493 18356897 := bstep (se 2 (by rfl) ⟨6883836, by rfl⟩ : syracuseStep 18356897 = 13767673) B13767673
theorem B4135967 : Blo 1589493 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B440738455 : Blo 1589493 440738455 := bstep (se 1 (by rfl) ⟨330553841, by rfl⟩ : syracuseStep 440738455 = 661107683) B661107683
theorem B6794599 : Blo 1589493 6794599 := bstep (se 1 (by rfl) ⟨5095949, by rfl⟩ : syracuseStep 6794599 = 10191899) B10191899
theorem B2757311 : Blo 1589493 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B12237931 : Blo 1589493 12237931 := bstep (se 1 (by rfl) ⟨9178448, by rfl⟩ : syracuseStep 12237931 = 18356897) B18356897
theorem B1838207 : Blo 1589493 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B65268965 : Blo 1589493 65268965 := bstep (se 4 (by rfl) ⟨6118965, by rfl⟩ : syracuseStep 65268965 = 12237931) B12237931
theorem B587651273 : Blo 1589493 587651273 := bstep (se 2 (by rfl) ⟨220369227, by rfl⟩ : syracuseStep 587651273 = 440738455) B440738455
theorem B9059465 : Blo 1589493 9059465 := bstep (se 2 (by rfl) ⟨3397299, by rfl⟩ : syracuseStep 9059465 = 6794599) B6794599
theorem B391767515 : Blo 1589493 391767515 := bstep (se 1 (by rfl) ⟨293825636, by rfl⟩ : syracuseStep 391767515 = 587651273) B587651273
theorem B6039643 : Blo 1589493 6039643 := bstep (se 1 (by rfl) ⟨4529732, by rfl⟩ : syracuseStep 6039643 = 9059465) B9059465
theorem B4901885 : Blo 1589493 4901885 := bstep (se 3 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 4901885 = 1838207) B1838207
theorem B43512643 : Blo 1589493 43512643 := bstep (se 1 (by rfl) ⟨32634482, by rfl⟩ : syracuseStep 43512643 = 65268965) B65268965
theorem B8052857 : Blo 1589493 8052857 := bstep (se 2 (by rfl) ⟨3019821, by rfl⟩ : syracuseStep 8052857 = 6039643) B6039643
theorem B261178343 : Blo 1589493 261178343 := bstep (se 1 (by rfl) ⟨195883757, by rfl⟩ : syracuseStep 261178343 = 391767515) B391767515
theorem B58016857 : Blo 1589493 58016857 := bstep (se 2 (by rfl) ⟨21756321, by rfl⟩ : syracuseStep 58016857 = 43512643) B43512643
theorem B3267923 : Blo 1589493 3267923 := bstep (se 1 (by rfl) ⟨2450942, by rfl⟩ : syracuseStep 3267923 = 4901885) B4901885
theorem B5368571 : Blo 1589493 5368571 := bstep (se 1 (by rfl) ⟨4026428, by rfl⟩ : syracuseStep 5368571 = 8052857) B8052857
theorem B174118895 : Blo 1589493 174118895 := bstep (se 1 (by rfl) ⟨130589171, by rfl⟩ : syracuseStep 174118895 = 261178343) B261178343
theorem B8714461 : Blo 1589493 8714461 := bstep (se 3 (by rfl) ⟨1633961, by rfl⟩ : syracuseStep 8714461 = 3267923) B3267923
theorem B77355809 : Blo 1589493 77355809 := bstep (se 2 (by rfl) ⟨29008428, by rfl⟩ : syracuseStep 77355809 = 58016857) B58016857
theorem B51570539 : Blo 1589493 51570539 := bstep (se 1 (by rfl) ⟨38677904, by rfl⟩ : syracuseStep 51570539 = 77355809) B77355809
theorem B11619281 : Blo 1589493 11619281 := bstep (se 2 (by rfl) ⟨4357230, by rfl⟩ : syracuseStep 11619281 = 8714461) B8714461
theorem B116079263 : Blo 1589493 116079263 := bstep (se 1 (by rfl) ⟨87059447, by rfl⟩ : syracuseStep 116079263 = 174118895) B174118895
theorem B3579047 : Blo 1589493 3579047 := bstep (se 1 (by rfl) ⟨2684285, by rfl⟩ : syracuseStep 3579047 = 5368571) B5368571
theorem B2386031 : Blo 1589493 2386031 := bstep (se 1 (by rfl) ⟨1789523, by rfl⟩ : syracuseStep 2386031 = 3579047) B3579047
theorem B77386175 : Blo 1589493 77386175 := bstep (se 1 (by rfl) ⟨58039631, by rfl⟩ : syracuseStep 77386175 = 116079263) B116079263
theorem B7746187 : Blo 1589493 7746187 := bstep (se 1 (by rfl) ⟨5809640, by rfl⟩ : syracuseStep 7746187 = 11619281) B11619281
theorem B34380359 : Blo 1589493 34380359 := bstep (se 1 (by rfl) ⟨25785269, by rfl⟩ : syracuseStep 34380359 = 51570539) B51570539
theorem B1590687 : Blo 1589493 1590687 := bstep (se 1 (by rfl) ⟨1193015, by rfl⟩ : syracuseStep 1590687 = 2386031) B2386031
theorem B51590783 : Blo 1589493 51590783 := bstep (se 1 (by rfl) ⟨38693087, by rfl⟩ : syracuseStep 51590783 = 77386175) B77386175
theorem B10328249 : Blo 1589493 10328249 := bstep (se 2 (by rfl) ⟨3873093, by rfl⟩ : syracuseStep 10328249 = 7746187) B7746187
theorem B22920239 : Blo 1589493 22920239 := bstep (se 1 (by rfl) ⟨17190179, by rfl⟩ : syracuseStep 22920239 = 34380359) B34380359
theorem B27541997 : Blo 1589493 27541997 := bstep (se 3 (by rfl) ⟨5164124, by rfl⟩ : syracuseStep 27541997 = 10328249) B10328249
theorem B15280159 : Blo 1589493 15280159 := bstep (se 1 (by rfl) ⟨11460119, by rfl⟩ : syracuseStep 15280159 = 22920239) B22920239
theorem B34393855 : Blo 1589493 34393855 := bstep (se 1 (by rfl) ⟨25795391, by rfl⟩ : syracuseStep 34393855 = 51590783) B51590783
theorem B20373545 : Blo 1589493 20373545 := bstep (se 2 (by rfl) ⟨7640079, by rfl⟩ : syracuseStep 20373545 = 15280159) B15280159
theorem B18361331 : Blo 1589493 18361331 := bstep (se 1 (by rfl) ⟨13770998, by rfl⟩ : syracuseStep 18361331 = 27541997) B27541997
theorem B45858473 : Blo 1589493 45858473 := bstep (se 2 (by rfl) ⟨17196927, by rfl⟩ : syracuseStep 45858473 = 34393855) B34393855
theorem B13582363 : Blo 1589493 13582363 := bstep (se 1 (by rfl) ⟨10186772, by rfl⟩ : syracuseStep 13582363 = 20373545) B20373545
theorem B12240887 : Blo 1589493 12240887 := bstep (se 1 (by rfl) ⟨9180665, by rfl⟩ : syracuseStep 12240887 = 18361331) B18361331
theorem B30572315 : Blo 1589493 30572315 := bstep (se 1 (by rfl) ⟨22929236, by rfl⟩ : syracuseStep 30572315 = 45858473) B45858473
theorem B32642365 : Blo 1589493 32642365 := bstep (se 3 (by rfl) ⟨6120443, by rfl⟩ : syracuseStep 32642365 = 12240887) B12240887
theorem B18109817 : Blo 1589493 18109817 := bstep (se 2 (by rfl) ⟨6791181, by rfl⟩ : syracuseStep 18109817 = 13582363) B13582363
theorem B20381543 : Blo 1589493 20381543 := bstep (se 1 (by rfl) ⟨15286157, by rfl⟩ : syracuseStep 20381543 = 30572315) B30572315
theorem B13587695 : Blo 1589493 13587695 := bstep (se 1 (by rfl) ⟨10190771, by rfl⟩ : syracuseStep 13587695 = 20381543) B20381543
theorem B12073211 : Blo 1589493 12073211 := bstep (se 1 (by rfl) ⟨9054908, by rfl⟩ : syracuseStep 12073211 = 18109817) B18109817
theorem B43523153 : Blo 1589493 43523153 := bstep (se 2 (by rfl) ⟨16321182, by rfl⟩ : syracuseStep 43523153 = 32642365) B32642365
theorem B8048807 : Blo 1589493 8048807 := bstep (se 1 (by rfl) ⟨6036605, by rfl⟩ : syracuseStep 8048807 = 12073211) B12073211
theorem B9058463 : Blo 1589493 9058463 := bstep (se 1 (by rfl) ⟨6793847, by rfl⟩ : syracuseStep 9058463 = 13587695) B13587695
theorem B29015435 : Blo 1589493 29015435 := bstep (se 1 (by rfl) ⟨21761576, by rfl⟩ : syracuseStep 29015435 = 43523153) B43523153
theorem B5365871 : Blo 1589493 5365871 := bstep (se 1 (by rfl) ⟨4024403, by rfl⟩ : syracuseStep 5365871 = 8048807) B8048807
theorem B6038975 : Blo 1589493 6038975 := bstep (se 1 (by rfl) ⟨4529231, by rfl⟩ : syracuseStep 6038975 = 9058463) B9058463
theorem B19343623 : Blo 1589493 19343623 := bstep (se 1 (by rfl) ⟨14507717, by rfl⟩ : syracuseStep 19343623 = 29015435) B29015435
theorem B25791497 : Blo 1589493 25791497 := bstep (se 2 (by rfl) ⟨9671811, by rfl⟩ : syracuseStep 25791497 = 19343623) B19343623
theorem B4025983 : Blo 1589493 4025983 := bstep (se 1 (by rfl) ⟨3019487, by rfl⟩ : syracuseStep 4025983 = 6038975) B6038975
theorem B3577247 : Blo 1589493 3577247 := bstep (se 1 (by rfl) ⟨2682935, by rfl⟩ : syracuseStep 3577247 = 5365871) B5365871
theorem B2384831 : Blo 1589493 2384831 := bstep (se 1 (by rfl) ⟨1788623, by rfl⟩ : syracuseStep 2384831 = 3577247) B3577247
theorem B5367977 : Blo 1589493 5367977 := bstep (se 2 (by rfl) ⟨2012991, by rfl⟩ : syracuseStep 5367977 = 4025983) B4025983
theorem B17194331 : Blo 1589493 17194331 := bstep (se 1 (by rfl) ⟨12895748, by rfl⟩ : syracuseStep 17194331 = 25791497) B25791497
theorem B1589887 : Blo 1589493 1589887 := bstep (se 1 (by rfl) ⟨1192415, by rfl⟩ : syracuseStep 1589887 = 2384831) B2384831
theorem B11462887 : Blo 1589493 11462887 := bstep (se 1 (by rfl) ⟨8597165, by rfl⟩ : syracuseStep 11462887 = 17194331) B17194331
theorem B3578651 : Blo 1589493 3578651 := bstep (se 1 (by rfl) ⟨2683988, by rfl⟩ : syracuseStep 3578651 = 5367977) B5367977
theorem B2385767 : Blo 1589493 2385767 := bstep (se 1 (by rfl) ⟨1789325, by rfl⟩ : syracuseStep 2385767 = 3578651) B3578651
theorem B61135397 : Blo 1589493 61135397 := bstep (se 4 (by rfl) ⟨5731443, by rfl⟩ : syracuseStep 61135397 = 11462887) B11462887
theorem B1590511 : Blo 1589493 1590511 := bstep (se 1 (by rfl) ⟨1192883, by rfl⟩ : syracuseStep 1590511 = 2385767) B2385767
theorem B40756931 : Blo 1589493 40756931 := bstep (se 1 (by rfl) ⟨30567698, by rfl⟩ : syracuseStep 40756931 = 61135397) B61135397
theorem B27171287 : Blo 1589493 27171287 := bstep (se 1 (by rfl) ⟨20378465, by rfl⟩ : syracuseStep 27171287 = 40756931) B40756931
theorem B18114191 : Blo 1589493 18114191 := bstep (se 1 (by rfl) ⟨13585643, by rfl⟩ : syracuseStep 18114191 = 27171287) B27171287
theorem B12076127 : Blo 1589493 12076127 := bstep (se 1 (by rfl) ⟨9057095, by rfl⟩ : syracuseStep 12076127 = 18114191) B18114191
theorem B8050751 : Blo 1589493 8050751 := bstep (se 1 (by rfl) ⟨6038063, by rfl⟩ : syracuseStep 8050751 = 12076127) B12076127
theorem B5367167 : Blo 1589493 5367167 := bstep (se 1 (by rfl) ⟨4025375, by rfl⟩ : syracuseStep 5367167 = 8050751) B8050751
theorem B3578111 : Blo 1589493 3578111 := bstep (se 1 (by rfl) ⟨2683583, by rfl⟩ : syracuseStep 3578111 = 5367167) B5367167
theorem B2385407 : Blo 1589493 2385407 := bstep (se 1 (by rfl) ⟨1789055, by rfl⟩ : syracuseStep 2385407 = 3578111) B3578111
theorem B1590271 : Blo 1589493 1590271 := bstep (se 1 (by rfl) ⟨1192703, by rfl⟩ : syracuseStep 1590271 = 2385407) B2385407

theorem C0 (j : ℕ) (h1 : 397373 ≤ j) (h2 : j ≤ 397747) : Blo 1589493 (4 * j + 3) := by
  interval_cases j
  · exact B1589495
  · exact B1589499
  · exact B1589503
  · exact B1589507
  · exact B1589511
  · exact B1589515
  · exact B1589519
  · exact B1589523
  · exact B1589527
  · exact B1589531
  · exact B1589535
  · exact B1589539
  · exact B1589543
  · exact B1589547
  · exact B1589551
  · exact B1589555
  · exact B1589559
  · exact B1589563
  · exact B1589567
  · exact B1589571
  · exact B1589575
  · exact B1589579
  · exact B1589583
  · exact B1589587
  · exact B1589591
  · exact B1589595
  · exact B1589599
  · exact B1589603
  · exact B1589607
  · exact B1589611
  · exact B1589615
  · exact B1589619
  · exact B1589623
  · exact B1589627
  · exact B1589631
  · exact B1589635
  · exact B1589639
  · exact B1589643
  · exact B1589647
  · exact B1589651
  · exact B1589655
  · exact B1589659
  · exact B1589663
  · exact B1589667
  · exact B1589671
  · exact B1589675
  · exact B1589679
  · exact B1589683
  · exact B1589687
  · exact B1589691
  · exact B1589695
  · exact B1589699
  · exact B1589703
  · exact B1589707
  · exact B1589711
  · exact B1589715
  · exact B1589719
  · exact B1589723
  · exact B1589727
  · exact B1589731
  · exact B1589735
  · exact B1589739
  · exact B1589743
  · exact B1589747
  · exact B1589751
  · exact B1589755
  · exact B1589759
  · exact B1589763
  · exact B1589767
  · exact B1589771
  · exact B1589775
  · exact B1589779
  · exact B1589783
  · exact B1589787
  · exact B1589791
  · exact B1589795
  · exact B1589799
  · exact B1589803
  · exact B1589807
  · exact B1589811
  · exact B1589815
  · exact B1589819
  · exact B1589823
  · exact B1589827
  · exact B1589831
  · exact B1589835
  · exact B1589839
  · exact B1589843
  · exact B1589847
  · exact B1589851
  · exact B1589855
  · exact B1589859
  · exact B1589863
  · exact B1589867
  · exact B1589871
  · exact B1589875
  · exact B1589879
  · exact B1589883
  · exact B1589887
  · exact B1589891
  · exact B1589895
  · exact B1589899
  · exact B1589903
  · exact B1589907
  · exact B1589911
  · exact B1589915
  · exact B1589919
  · exact B1589923
  · exact B1589927
  · exact B1589931
  · exact B1589935
  · exact B1589939
  · exact B1589943
  · exact B1589947
  · exact B1589951
  · exact B1589955
  · exact B1589959
  · exact B1589963
  · exact B1589967
  · exact B1589971
  · exact B1589975
  · exact B1589979
  · exact B1589983
  · exact B1589987
  · exact B1589991
  · exact B1589995
  · exact B1589999
  · exact B1590003
  · exact B1590007
  · exact B1590011
  · exact B1590015
  · exact B1590019
  · exact B1590023
  · exact B1590027
  · exact B1590031
  · exact B1590035
  · exact B1590039
  · exact B1590043
  · exact B1590047
  · exact B1590051
  · exact B1590055
  · exact B1590059
  · exact B1590063
  · exact B1590067
  · exact B1590071
  · exact B1590075
  · exact B1590079
  · exact B1590083
  · exact B1590087
  · exact B1590091
  · exact B1590095
  · exact B1590099
  · exact B1590103
  · exact B1590107
  · exact B1590111
  · exact B1590115
  · exact B1590119
  · exact B1590123
  · exact B1590127
  · exact B1590131
  · exact B1590135
  · exact B1590139
  · exact B1590143
  · exact B1590147
  · exact B1590151
  · exact B1590155
  · exact B1590159
  · exact B1590163
  · exact B1590167
  · exact B1590171
  · exact B1590175
  · exact B1590179
  · exact B1590183
  · exact B1590187
  · exact B1590191
  · exact B1590195
  · exact B1590199
  · exact B1590203
  · exact B1590207
  · exact B1590211
  · exact B1590215
  · exact B1590219
  · exact B1590223
  · exact B1590227
  · exact B1590231
  · exact B1590235
  · exact B1590239
  · exact B1590243
  · exact B1590247
  · exact B1590251
  · exact B1590255
  · exact B1590259
  · exact B1590263
  · exact B1590267
  · exact B1590271
  · exact B1590275
  · exact B1590279
  · exact B1590283
  · exact B1590287
  · exact B1590291
  · exact B1590295
  · exact B1590299
  · exact B1590303
  · exact B1590307
  · exact B1590311
  · exact B1590315
  · exact B1590319
  · exact B1590323
  · exact B1590327
  · exact B1590331
  · exact B1590335
  · exact B1590339
  · exact B1590343
  · exact B1590347
  · exact B1590351
  · exact B1590355
  · exact B1590359
  · exact B1590363
  · exact B1590367
  · exact B1590371
  · exact B1590375
  · exact B1590379
  · exact B1590383
  · exact B1590387
  · exact B1590391
  · exact B1590395
  · exact B1590399
  · exact B1590403
  · exact B1590407
  · exact B1590411
  · exact B1590415
  · exact B1590419
  · exact B1590423
  · exact B1590427
  · exact B1590431
  · exact B1590435
  · exact B1590439
  · exact B1590443
  · exact B1590447
  · exact B1590451
  · exact B1590455
  · exact B1590459
  · exact B1590463
  · exact B1590467
  · exact B1590471
  · exact B1590475
  · exact B1590479
  · exact B1590483
  · exact B1590487
  · exact B1590491
  · exact B1590495
  · exact B1590499
  · exact B1590503
  · exact B1590507
  · exact B1590511
  · exact B1590515
  · exact B1590519
  · exact B1590523
  · exact B1590527
  · exact B1590531
  · exact B1590535
  · exact B1590539
  · exact B1590543
  · exact B1590547
  · exact B1590551
  · exact B1590555
  · exact B1590559
  · exact B1590563
  · exact B1590567
  · exact B1590571
  · exact B1590575
  · exact B1590579
  · exact B1590583
  · exact B1590587
  · exact B1590591
  · exact B1590595
  · exact B1590599
  · exact B1590603
  · exact B1590607
  · exact B1590611
  · exact B1590615
  · exact B1590619
  · exact B1590623
  · exact B1590627
  · exact B1590631
  · exact B1590635
  · exact B1590639
  · exact B1590643
  · exact B1590647
  · exact B1590651
  · exact B1590655
  · exact B1590659
  · exact B1590663
  · exact B1590667
  · exact B1590671
  · exact B1590675
  · exact B1590679
  · exact B1590683
  · exact B1590687
  · exact B1590691
  · exact B1590695
  · exact B1590699
  · exact B1590703
  · exact B1590707
  · exact B1590711
  · exact B1590715
  · exact B1590719
  · exact B1590723
  · exact B1590727
  · exact B1590731
  · exact B1590735
  · exact B1590739
  · exact B1590743
  · exact B1590747
  · exact B1590751
  · exact B1590755
  · exact B1590759
  · exact B1590763
  · exact B1590767
  · exact B1590771
  · exact B1590775
  · exact B1590779
  · exact B1590783
  · exact B1590787
  · exact B1590791
  · exact B1590795
  · exact B1590799
  · exact B1590803
  · exact B1590807
  · exact B1590811
  · exact B1590815
  · exact B1590819
  · exact B1590823
  · exact B1590827
  · exact B1590831
  · exact B1590835
  · exact B1590839
  · exact B1590843
  · exact B1590847
  · exact B1590851
  · exact B1590855
  · exact B1590859
  · exact B1590863
  · exact B1590867
  · exact B1590871
  · exact B1590875
  · exact B1590879
  · exact B1590883
  · exact B1590887
  · exact B1590891
  · exact B1590895
  · exact B1590899
  · exact B1590903
  · exact B1590907
  · exact B1590911
  · exact B1590915
  · exact B1590919
  · exact B1590923
  · exact B1590927
  · exact B1590931
  · exact B1590935
  · exact B1590939
  · exact B1590943
  · exact B1590947
  · exact B1590951
  · exact B1590955
  · exact B1590959
  · exact B1590963
  · exact B1590967
  · exact B1590971
  · exact B1590975
  · exact B1590979
  · exact B1590983
  · exact B1590987
  · exact B1590991

theorem solution (m : ℕ) (hlo : 1589493 ≤ m) (hhi : m ≤ 1590993) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 397373 ≤ j := by omega
    have hj2 : j ≤ 397747 := by omega
    have hb : Blo 1589493 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
