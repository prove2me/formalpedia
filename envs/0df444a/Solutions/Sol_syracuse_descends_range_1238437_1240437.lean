-- Prove2me | solution 1 for syracuse_descends_range_1238437_1240437
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:08.025017+00:00
-- url     : https://prove2.me/submissions/cb5d1ea9-e2cd-41b1-b078-6c20f6cafde6

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


theorem B1859597 : Blo 1238437 1859597 := bbase (se 3 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 1859597 = 697349) (by norm_num)
theorem B4186133 : Blo 1238437 4186133 := bbase (se 6 (by rfl) ⟨98112, by rfl⟩ : syracuseStep 4186133 = 196225) (by norm_num)
theorem B1859621 : Blo 1238437 1859621 := bbase (se 4 (by rfl) ⟨174339, by rfl⟩ : syracuseStep 1859621 = 348679) (by norm_num)
theorem B1859645 : Blo 1238437 1859645 := bbase (se 3 (by rfl) ⟨348683, by rfl⟩ : syracuseStep 1859645 = 697367) (by norm_num)
theorem B101761109 : Blo 1238437 101761109 := bbase (se 8 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 101761109 = 1192513) (by norm_num)
theorem B1859669 : Blo 1238437 1859669 := bbase (se 8 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 1859669 = 21793) (by norm_num)
theorem B1859693 : Blo 1238437 1859693 := bbase (se 3 (by rfl) ⟨348692, by rfl⟩ : syracuseStep 1859693 = 697385) (by norm_num)
theorem B1859717 : Blo 1238437 1859717 := bbase (se 4 (by rfl) ⟨174348, by rfl⟩ : syracuseStep 1859717 = 348697) (by norm_num)
theorem B2351261 : Blo 1238437 2351261 := bbase (se 3 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 2351261 = 881723) (by norm_num)
theorem B1859741 : Blo 1238437 1859741 := bbase (se 3 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 1859741 = 697403) (by norm_num)
theorem B3137717 : Blo 1238437 3137717 := bbase (se 5 (by rfl) ⟨147080, by rfl⟩ : syracuseStep 3137717 = 294161) (by norm_num)
theorem B1859765 : Blo 1238437 1859765 := bbase (se 5 (by rfl) ⟨87176, by rfl⟩ : syracuseStep 1859765 = 174353) (by norm_num)
theorem B3973301 : Blo 1238437 3973301 := bbase (se 5 (by rfl) ⟨186248, by rfl⟩ : syracuseStep 3973301 = 372497) (by norm_num)
theorem B1859789 : Blo 1238437 1859789 := bbase (se 3 (by rfl) ⟨348710, by rfl⟩ : syracuseStep 1859789 = 697421) (by norm_num)
theorem B26820821 : Blo 1238437 26820821 := bbase (se 7 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 26820821 = 628613) (by norm_num)
theorem B1859813 : Blo 1238437 1859813 := bbase (se 4 (by rfl) ⟨174357, by rfl⟩ : syracuseStep 1859813 = 348715) (by norm_num)
theorem B1859837 : Blo 1238437 1859837 := bbase (se 3 (by rfl) ⟨348719, by rfl⟩ : syracuseStep 1859837 = 697439) (by norm_num)
theorem B1859861 : Blo 1238437 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B3350821 : Blo 1238437 3350821 := bbase (se 4 (by rfl) ⟨314139, by rfl⟩ : syracuseStep 3350821 = 628279) (by norm_num)
theorem B2351405 : Blo 1238437 2351405 := bbase (se 3 (by rfl) ⟨440888, by rfl⟩ : syracuseStep 2351405 = 881777) (by norm_num)
theorem B1859885 : Blo 1238437 1859885 := bbase (se 3 (by rfl) ⟨348728, by rfl⟩ : syracuseStep 1859885 = 697457) (by norm_num)
theorem B1859909 : Blo 1238437 1859909 := bbase (se 4 (by rfl) ⟨174366, by rfl⟩ : syracuseStep 1859909 = 348733) (by norm_num)
theorem B1859933 : Blo 1238437 1859933 := bbase (se 3 (by rfl) ⟨348737, by rfl⟩ : syracuseStep 1859933 = 697475) (by norm_num)
theorem B2646373 : Blo 1238437 2646373 := bbase (se 4 (by rfl) ⟨248097, by rfl⟩ : syracuseStep 2646373 = 496195) (by norm_num)
theorem B1859957 : Blo 1238437 1859957 := bbase (se 5 (by rfl) ⟨87185, by rfl⟩ : syracuseStep 1859957 = 174371) (by norm_num)
theorem B1859981 : Blo 1238437 1859981 := bbase (se 3 (by rfl) ⟨348746, by rfl⟩ : syracuseStep 1859981 = 697493) (by norm_num)
theorem B1860005 : Blo 1238437 1860005 := bbase (se 4 (by rfl) ⟨174375, by rfl⟩ : syracuseStep 1860005 = 348751) (by norm_num)
theorem B1860029 : Blo 1238437 1860029 := bbase (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) (by norm_num)
theorem B2384333 : Blo 1238437 2384333 := bbase (se 3 (by rfl) ⟨447062, by rfl⟩ : syracuseStep 2384333 = 894125) (by norm_num)
theorem B10584533 : Blo 1238437 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B1860053 : Blo 1238437 1860053 := bbase (se 7 (by rfl) ⟨21797, by rfl⟩ : syracuseStep 1860053 = 43595) (by norm_num)
theorem B1860077 : Blo 1238437 1860077 := bbase (se 3 (by rfl) ⟨348764, by rfl⟩ : syracuseStep 1860077 = 697529) (by norm_num)
theorem B7062005 : Blo 1238437 7062005 := bbase (se 5 (by rfl) ⟨331031, by rfl⟩ : syracuseStep 7062005 = 662063) (by norm_num)
theorem B1860101 : Blo 1238437 1860101 := bbase (se 4 (by rfl) ⟨174384, by rfl⟩ : syracuseStep 1860101 = 348769) (by norm_num)
theorem B3138061 : Blo 1238437 3138061 := bbase (se 3 (by rfl) ⟨588386, by rfl⟩ : syracuseStep 3138061 = 1176773) (by norm_num)
theorem B13591061 : Blo 1238437 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B1860125 : Blo 1238437 1860125 := bbase (se 3 (by rfl) ⟨348773, by rfl⟩ : syracuseStep 1860125 = 697547) (by norm_num)
theorem B1860149 : Blo 1238437 1860149 := bbase (se 5 (by rfl) ⟨87194, by rfl⟩ : syracuseStep 1860149 = 174389) (by norm_num)
theorem B2351693 : Blo 1238437 2351693 := bbase (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) (by norm_num)
theorem B1860173 : Blo 1238437 1860173 := bbase (se 3 (by rfl) ⟨348782, by rfl⟩ : syracuseStep 1860173 = 697565) (by norm_num)
theorem B1360469 : Blo 1238437 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B1393249 : Blo 1238437 1393249 := bbase (se 2 (by rfl) ⟨522468, by rfl⟩ : syracuseStep 1393249 = 1044937) (by norm_num)
theorem B1860197 : Blo 1238437 1860197 := bbase (se 4 (by rfl) ⟨174393, by rfl⟩ : syracuseStep 1860197 = 348787) (by norm_num)
theorem B5292661 : Blo 1238437 5292661 := bbase (se 5 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 5292661 = 496187) (by norm_num)
theorem B3138173 : Blo 1238437 3138173 := bbase (se 3 (by rfl) ⟨588407, by rfl⟩ : syracuseStep 3138173 = 1176815) (by norm_num)
theorem B1860221 : Blo 1238437 1860221 := bbase (se 3 (by rfl) ⟨348791, by rfl⟩ : syracuseStep 1860221 = 697583) (by norm_num)
theorem B1393285 : Blo 1238437 1393285 := bbase (se 4 (by rfl) ⟨130620, by rfl⟩ : syracuseStep 1393285 = 261241) (by norm_num)
theorem B5292677 : Blo 1238437 5292677 := bbase (se 4 (by rfl) ⟨496188, by rfl⟩ : syracuseStep 5292677 = 992377) (by norm_num)
theorem B6275717 : Blo 1238437 6275717 := bbase (se 4 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 6275717 = 1176697) (by norm_num)
theorem B3531413 : Blo 1238437 3531413 := bbase (se 6 (by rfl) ⟨82767, by rfl⟩ : syracuseStep 3531413 = 165535) (by norm_num)
theorem B1860245 : Blo 1238437 1860245 := bbase (se 6 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 1860245 = 87199) (by norm_num)
theorem B1393321 : Blo 1238437 1393321 := bbase (se 2 (by rfl) ⟨522495, by rfl⟩ : syracuseStep 1393321 = 1044991) (by norm_num)
theorem B1860269 : Blo 1238437 1860269 := bbase (se 3 (by rfl) ⟨348800, by rfl⟩ : syracuseStep 1860269 = 697601) (by norm_num)
theorem B1860293 : Blo 1238437 1860293 := bbase (se 4 (by rfl) ⟨174402, by rfl⟩ : syracuseStep 1860293 = 348805) (by norm_num)
theorem B1393357 : Blo 1238437 1393357 := bbase (se 3 (by rfl) ⟨261254, by rfl⟩ : syracuseStep 1393357 = 522509) (by norm_num)
theorem B9413333 : Blo 1238437 9413333 := bbase (se 7 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 9413333 = 220625) (by norm_num)
theorem B2646749 : Blo 1238437 2646749 := bbase (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) (by norm_num)
theorem B1860317 : Blo 1238437 1860317 := bbase (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) (by norm_num)
theorem B2351845 : Blo 1238437 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B1393393 : Blo 1238437 1393393 := bbase (se 2 (by rfl) ⟨522522, by rfl⟩ : syracuseStep 1393393 = 1045045) (by norm_num)
theorem B1860341 : Blo 1238437 1860341 := bbase (se 5 (by rfl) ⟨87203, by rfl⟩ : syracuseStep 1860341 = 174407) (by norm_num)
theorem B1860365 : Blo 1238437 1860365 := bbase (se 3 (by rfl) ⟨348818, by rfl⟩ : syracuseStep 1860365 = 697637) (by norm_num)
theorem B1393429 : Blo 1238437 1393429 := bbase (se 6 (by rfl) ⟨32658, by rfl⟩ : syracuseStep 1393429 = 65317) (by norm_num)
theorem B1860389 : Blo 1238437 1860389 := bbase (se 4 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 1860389 = 348823) (by norm_num)
theorem B1393465 : Blo 1238437 1393465 := bbase (se 2 (by rfl) ⟨522549, by rfl⟩ : syracuseStep 1393465 = 1045099) (by norm_num)
theorem B3138365 : Blo 1238437 3138365 := bbase (se 3 (by rfl) ⟨588443, by rfl⟩ : syracuseStep 3138365 = 1176887) (by norm_num)
theorem B1860413 : Blo 1238437 1860413 := bbase (se 3 (by rfl) ⟨348827, by rfl⟩ : syracuseStep 1860413 = 697655) (by norm_num)
theorem B1590085 : Blo 1238437 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B1860437 : Blo 1238437 1860437 := bbase (se 9 (by rfl) ⟨5450, by rfl⟩ : syracuseStep 1860437 = 10901) (by norm_num)
theorem B1393501 : Blo 1238437 1393501 := bbase (se 3 (by rfl) ⟨261281, by rfl⟩ : syracuseStep 1393501 = 522563) (by norm_num)
theorem B1860461 : Blo 1238437 1860461 := bbase (se 3 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 1860461 = 697673) (by norm_num)
theorem B1393537 : Blo 1238437 1393537 := bbase (se 2 (by rfl) ⟨522576, by rfl⟩ : syracuseStep 1393537 = 1045153) (by norm_num)
theorem B1860485 : Blo 1238437 1860485 := bbase (se 4 (by rfl) ⟨174420, by rfl⟩ : syracuseStep 1860485 = 348841) (by norm_num)
theorem B1860509 : Blo 1238437 1860509 := bbase (se 3 (by rfl) ⟨348845, by rfl⟩ : syracuseStep 1860509 = 697691) (by norm_num)
theorem B1393573 : Blo 1238437 1393573 := bbase (se 4 (by rfl) ⟨130647, by rfl⟩ : syracuseStep 1393573 = 261295) (by norm_num)
theorem B2089901 : Blo 1238437 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B1860533 : Blo 1238437 1860533 := bbase (se 5 (by rfl) ⟨87212, by rfl⟩ : syracuseStep 1860533 = 174425) (by norm_num)
theorem B1393609 : Blo 1238437 1393609 := bbase (se 2 (by rfl) ⟨522603, by rfl⟩ : syracuseStep 1393609 = 1045207) (by norm_num)
theorem B1860557 : Blo 1238437 1860557 := bbase (se 3 (by rfl) ⟨348854, by rfl⟩ : syracuseStep 1860557 = 697709) (by norm_num)
theorem B1860581 : Blo 1238437 1860581 := bbase (se 4 (by rfl) ⟨174429, by rfl⟩ : syracuseStep 1860581 = 348859) (by norm_num)
theorem B1393645 : Blo 1238437 1393645 := bbase (se 3 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 1393645 = 522617) (by norm_num)
theorem B1860605 : Blo 1238437 1860605 := bbase (se 3 (by rfl) ⟨348863, by rfl⟩ : syracuseStep 1860605 = 697727) (by norm_num)
theorem B1393681 : Blo 1238437 1393681 := bbase (se 2 (by rfl) ⟨522630, by rfl⟩ : syracuseStep 1393681 = 1045261) (by norm_num)
theorem B2352149 : Blo 1238437 2352149 := bbase (se 6 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 2352149 = 110257) (by norm_num)
theorem B1860629 : Blo 1238437 1860629 := bbase (se 6 (by rfl) ⟨43608, by rfl⟩ : syracuseStep 1860629 = 87217) (by norm_num)
theorem B2090029 : Blo 1238437 2090029 := bbase (se 3 (by rfl) ⟨391880, by rfl⟩ : syracuseStep 2090029 = 783761) (by norm_num)
theorem B1860653 : Blo 1238437 1860653 := bbase (se 3 (by rfl) ⟨348872, by rfl⟩ : syracuseStep 1860653 = 697745) (by norm_num)
theorem B1393717 : Blo 1238437 1393717 := bbase (se 5 (by rfl) ⟨65330, by rfl⟩ : syracuseStep 1393717 = 130661) (by norm_num)
theorem B1393753 : Blo 1238437 1393753 := bbase (se 2 (by rfl) ⟨522657, by rfl⟩ : syracuseStep 1393753 = 1045315) (by norm_num)
theorem B9405557 : Blo 1238437 9405557 := bbase (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) (by norm_num)
theorem B1393789 : Blo 1238437 1393789 := bbase (se 3 (by rfl) ⟨261335, by rfl⟩ : syracuseStep 1393789 = 522671) (by norm_num)
theorem B2090117 : Blo 1238437 2090117 := bbase (se 4 (by rfl) ⟨195948, by rfl⟩ : syracuseStep 2090117 = 391897) (by norm_num)
theorem B4465813 : Blo 1238437 4465813 := bbase (se 6 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 4465813 = 209335) (by norm_num)
theorem B3138709 : Blo 1238437 3138709 := bbase (se 6 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 3138709 = 147127) (by norm_num)
theorem B1393825 : Blo 1238437 1393825 := bbase (se 2 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 1393825 = 1045369) (by norm_num)
theorem B1393861 : Blo 1238437 1393861 := bbase (se 4 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 1393861 = 261349) (by norm_num)
theorem B2786525 : Blo 1238437 2786525 := bbase (se 3 (by rfl) ⟨522473, by rfl⟩ : syracuseStep 2786525 = 1044947) (by norm_num)
theorem B3351781 : Blo 1238437 3351781 := bbase (se 4 (by rfl) ⟨314229, by rfl⟩ : syracuseStep 3351781 = 628459) (by norm_num)
theorem B1393897 : Blo 1238437 1393897 := bbase (se 2 (by rfl) ⟨522711, by rfl⟩ : syracuseStep 1393897 = 1045423) (by norm_num)
theorem B2090245 : Blo 1238437 2090245 := bbase (se 4 (by rfl) ⟨195960, by rfl⟩ : syracuseStep 2090245 = 391921) (by norm_num)
theorem B3138821 : Blo 1238437 3138821 := bbase (se 4 (by rfl) ⟨294264, by rfl⟩ : syracuseStep 3138821 = 588529) (by norm_num)
theorem B1393933 : Blo 1238437 1393933 := bbase (se 3 (by rfl) ⟨261362, by rfl⟩ : syracuseStep 1393933 = 522725) (by norm_num)
theorem B2786597 : Blo 1238437 2786597 := bbase (se 4 (by rfl) ⟨261243, by rfl⟩ : syracuseStep 2786597 = 522487) (by norm_num)
theorem B4465957 : Blo 1238437 4465957 := bbase (se 4 (by rfl) ⟨418683, by rfl⟩ : syracuseStep 4465957 = 837367) (by norm_num)
theorem B1393969 : Blo 1238437 1393969 := bbase (se 2 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 1393969 = 1045477) (by norm_num)
theorem B2385229 : Blo 1238437 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B1394005 : Blo 1238437 1394005 := bbase (se 12 (by rfl) ⟨510, by rfl⟩ : syracuseStep 1394005 = 1021) (by norm_num)
theorem B2090333 : Blo 1238437 2090333 := bbase (se 3 (by rfl) ⟨391937, by rfl⟩ : syracuseStep 2090333 = 783875) (by norm_num)
theorem B1983845 : Blo 1238437 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B2786669 : Blo 1238437 2786669 := bbase (se 3 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 2786669 = 1045001) (by norm_num)
theorem B1394041 : Blo 1238437 1394041 := bbase (se 2 (by rfl) ⟨522765, by rfl⟩ : syracuseStep 1394041 = 1045531) (by norm_num)
theorem B1394077 : Blo 1238437 1394077 := bbase (se 3 (by rfl) ⟨261389, by rfl⟩ : syracuseStep 1394077 = 522779) (by norm_num)
theorem B2786741 : Blo 1238437 2786741 := bbase (se 5 (by rfl) ⟨130628, by rfl⟩ : syracuseStep 2786741 = 261257) (by norm_num)
theorem B1394113 : Blo 1238437 1394113 := bbase (se 2 (by rfl) ⟨522792, by rfl⟩ : syracuseStep 1394113 = 1045585) (by norm_num)
theorem B3139013 : Blo 1238437 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B2090461 : Blo 1238437 2090461 := bbase (se 3 (by rfl) ⟨391961, by rfl⟩ : syracuseStep 2090461 = 783923) (by norm_num)
theorem B1394149 : Blo 1238437 1394149 := bbase (se 4 (by rfl) ⟨130701, by rfl⟩ : syracuseStep 1394149 = 261403) (by norm_num)
theorem B2786813 : Blo 1238437 2786813 := bbase (se 3 (by rfl) ⟨522527, by rfl⟩ : syracuseStep 2786813 = 1045055) (by norm_num)
theorem B1394185 : Blo 1238437 1394185 := bbase (se 2 (by rfl) ⟨522819, by rfl⟩ : syracuseStep 1394185 = 1045639) (by norm_num)
theorem B1394221 : Blo 1238437 1394221 := bbase (se 3 (by rfl) ⟨261416, by rfl⟩ : syracuseStep 1394221 = 522833) (by norm_num)
theorem B2090549 : Blo 1238437 2090549 := bbase (se 5 (by rfl) ⟨97994, by rfl⟩ : syracuseStep 2090549 = 195989) (by norm_num)
theorem B2786885 : Blo 1238437 2786885 := bbase (se 4 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 2786885 = 522541) (by norm_num)
theorem B1394257 : Blo 1238437 1394257 := bbase (se 2 (by rfl) ⟨522846, by rfl⟩ : syracuseStep 1394257 = 1045693) (by norm_num)
theorem B40175189 : Blo 1238437 40175189 := bbase (se 8 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 40175189 = 470803) (by norm_num)
theorem B6702677 : Blo 1238437 6702677 := bbase (se 8 (by rfl) ⟨39273, by rfl⟩ : syracuseStep 6702677 = 78547) (by norm_num)
theorem B1394293 : Blo 1238437 1394293 := bbase (se 5 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 1394293 = 130715) (by norm_num)
theorem B1984133 : Blo 1238437 1984133 := bbase (se 4 (by rfl) ⟨186012, by rfl⟩ : syracuseStep 1984133 = 372025) (by norm_num)
theorem B2786957 : Blo 1238437 2786957 := bbase (se 3 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 2786957 = 1045109) (by norm_num)
theorem B1394329 : Blo 1238437 1394329 := bbase (se 2 (by rfl) ⟨522873, by rfl⟩ : syracuseStep 1394329 = 1045747) (by norm_num)
theorem B2090677 : Blo 1238437 2090677 := bbase (se 5 (by rfl) ⟨98000, by rfl⟩ : syracuseStep 2090677 = 196001) (by norm_num)
theorem B1394365 : Blo 1238437 1394365 := bbase (se 3 (by rfl) ⟨261443, by rfl⟩ : syracuseStep 1394365 = 522887) (by norm_num)
theorem B2787029 : Blo 1238437 2787029 := bbase (se 7 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 2787029 = 65321) (by norm_num)
theorem B1394401 : Blo 1238437 1394401 := bbase (se 2 (by rfl) ⟨522900, by rfl⟩ : syracuseStep 1394401 = 1045801) (by norm_num)
theorem B2352901 : Blo 1238437 2352901 := bbase (se 4 (by rfl) ⟨220584, by rfl⟩ : syracuseStep 2352901 = 441169) (by norm_num)
theorem B1394437 : Blo 1238437 1394437 := bbase (se 4 (by rfl) ⟨130728, by rfl⟩ : syracuseStep 1394437 = 261457) (by norm_num)
theorem B2090765 : Blo 1238437 2090765 := bbase (se 3 (by rfl) ⟨392018, by rfl⟩ : syracuseStep 2090765 = 784037) (by norm_num)
theorem B2066197 : Blo 1238437 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B2787101 : Blo 1238437 2787101 := bbase (se 3 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 2787101 = 1045163) (by norm_num)
theorem B3139357 : Blo 1238437 3139357 := bbase (se 3 (by rfl) ⟨588629, by rfl⟩ : syracuseStep 3139357 = 1177259) (by norm_num)
theorem B1394473 : Blo 1238437 1394473 := bbase (se 2 (by rfl) ⟨522927, by rfl⟩ : syracuseStep 1394473 = 1045855) (by norm_num)
theorem B1394509 : Blo 1238437 1394509 := bbase (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) (by norm_num)
theorem B2787173 : Blo 1238437 2787173 := bbase (se 4 (by rfl) ⟨261297, by rfl⟩ : syracuseStep 2787173 = 522595) (by norm_num)
theorem B4704101 : Blo 1238437 4704101 := bbase (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) (by norm_num)
theorem B1394545 : Blo 1238437 1394545 := bbase (se 2 (by rfl) ⟨522954, by rfl⟩ : syracuseStep 1394545 = 1045909) (by norm_num)
theorem B2090893 : Blo 1238437 2090893 := bbase (se 3 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 2090893 = 784085) (by norm_num)
theorem B3139469 : Blo 1238437 3139469 := bbase (se 3 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 3139469 = 1177301) (by norm_num)
theorem B2353045 : Blo 1238437 2353045 := bbase (se 6 (by rfl) ⟨55149, by rfl⟩ : syracuseStep 2353045 = 110299) (by norm_num)
theorem B1394581 : Blo 1238437 1394581 := bbase (se 6 (by rfl) ⟨32685, by rfl⟩ : syracuseStep 1394581 = 65371) (by norm_num)
theorem B6277013 : Blo 1238437 6277013 := bbase (se 6 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 6277013 = 294235) (by norm_num)
theorem B2787245 : Blo 1238437 2787245 := bbase (se 3 (by rfl) ⟨522608, by rfl⟩ : syracuseStep 2787245 = 1045217) (by norm_num)
theorem B8480693 : Blo 1238437 8480693 := bbase (se 5 (by rfl) ⟨397532, by rfl⟩ : syracuseStep 8480693 = 795065) (by norm_num)
theorem B1394617 : Blo 1238437 1394617 := bbase (se 2 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 1394617 = 1045963) (by norm_num)
theorem B2295749 : Blo 1238437 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B1394653 : Blo 1238437 1394653 := bbase (se 3 (by rfl) ⟨261497, by rfl⟩ : syracuseStep 1394653 = 522995) (by norm_num)
theorem B2090981 : Blo 1238437 2090981 := bbase (se 4 (by rfl) ⟨196029, by rfl⟩ : syracuseStep 2090981 = 392059) (by norm_num)
theorem B2787317 : Blo 1238437 2787317 := bbase (se 5 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 2787317 = 261311) (by norm_num)
theorem B2828285 : Blo 1238437 2828285 := bbase (se 3 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 2828285 = 1060607) (by norm_num)
theorem B1394689 : Blo 1238437 1394689 := bbase (se 2 (by rfl) ⟨523008, by rfl⟩ : syracuseStep 1394689 = 1046017) (by norm_num)
theorem B1984549 : Blo 1238437 1984549 := bbase (se 4 (by rfl) ⟨186051, by rfl⟩ : syracuseStep 1984549 = 372103) (by norm_num)
theorem B1394725 : Blo 1238437 1394725 := bbase (se 4 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 1394725 = 261511) (by norm_num)
theorem B2353205 : Blo 1238437 2353205 := bbase (se 5 (by rfl) ⟨110306, by rfl⟩ : syracuseStep 2353205 = 220613) (by norm_num)
theorem B2787389 : Blo 1238437 2787389 := bbase (se 3 (by rfl) ⟨522635, by rfl⟩ : syracuseStep 2787389 = 1045271) (by norm_num)
theorem B4237381 : Blo 1238437 4237381 := bbase (se 4 (by rfl) ⟨397254, by rfl⟩ : syracuseStep 4237381 = 794509) (by norm_num)
theorem B1394761 : Blo 1238437 1394761 := bbase (se 2 (by rfl) ⟨523035, by rfl⟩ : syracuseStep 1394761 = 1046071) (by norm_num)
theorem B3139661 : Blo 1238437 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B2091109 : Blo 1238437 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B1394797 : Blo 1238437 1394797 := bbase (se 3 (by rfl) ⟨261524, by rfl⟩ : syracuseStep 1394797 = 523049) (by norm_num)
theorem B4180085 : Blo 1238437 4180085 := bbase (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) (by norm_num)
theorem B2787461 : Blo 1238437 2787461 := bbase (se 4 (by rfl) ⟨261324, by rfl⟩ : syracuseStep 2787461 = 522649) (by norm_num)
theorem B4704389 : Blo 1238437 4704389 := bbase (se 4 (by rfl) ⟨441036, by rfl⟩ : syracuseStep 4704389 = 882073) (by norm_num)
theorem B2721925 : Blo 1238437 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B1394833 : Blo 1238437 1394833 := bbase (se 2 (by rfl) ⟨523062, by rfl⟩ : syracuseStep 1394833 = 1046125) (by norm_num)
theorem B1394869 : Blo 1238437 1394869 := bbase (se 5 (by rfl) ⟨65384, by rfl⟩ : syracuseStep 1394869 = 130769) (by norm_num)
theorem B2091197 : Blo 1238437 2091197 := bbase (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) (by norm_num)
theorem B2353349 : Blo 1238437 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B2787533 : Blo 1238437 2787533 := bbase (se 3 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 2787533 = 1045325) (by norm_num)
theorem B1394905 : Blo 1238437 1394905 := bbase (se 2 (by rfl) ⟨523089, by rfl⟩ : syracuseStep 1394905 = 1046179) (by norm_num)
theorem B1394941 : Blo 1238437 1394941 := bbase (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) (by norm_num)
theorem B2787605 : Blo 1238437 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B1394977 : Blo 1238437 1394977 := bbase (se 2 (by rfl) ⟨523116, by rfl⟩ : syracuseStep 1394977 = 1046233) (by norm_num)
theorem B2091325 : Blo 1238437 2091325 := bbase (se 3 (by rfl) ⟨392123, by rfl⟩ : syracuseStep 2091325 = 784247) (by norm_num)
theorem B1395013 : Blo 1238437 1395013 := bbase (se 4 (by rfl) ⟨130782, by rfl⟩ : syracuseStep 1395013 = 261565) (by norm_num)
theorem B2648389 : Blo 1238437 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B2787677 : Blo 1238437 2787677 := bbase (se 3 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 2787677 = 1045379) (by norm_num)
theorem B1395049 : Blo 1238437 1395049 := bbase (se 2 (by rfl) ⟨523143, by rfl⟩ : syracuseStep 1395049 = 1046287) (by norm_num)
theorem B1395085 : Blo 1238437 1395085 := bbase (se 3 (by rfl) ⟨261578, by rfl⟩ : syracuseStep 1395085 = 523157) (by norm_num)
theorem B2091413 : Blo 1238437 2091413 := bbase (se 6 (by rfl) ⟨49017, by rfl⟩ : syracuseStep 2091413 = 98035) (by norm_num)
theorem B2787749 : Blo 1238437 2787749 := bbase (se 4 (by rfl) ⟨261351, by rfl⟩ : syracuseStep 2787749 = 522703) (by norm_num)
theorem B1395121 : Blo 1238437 1395121 := bbase (se 2 (by rfl) ⟨523170, by rfl⟩ : syracuseStep 1395121 = 1046341) (by norm_num)
theorem B1395157 : Blo 1238437 1395157 := bbase (se 7 (by rfl) ⟨16349, by rfl⟩ : syracuseStep 1395157 = 32699) (by norm_num)
theorem B2353637 : Blo 1238437 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B2787821 : Blo 1238437 2787821 := bbase (se 3 (by rfl) ⟨522716, by rfl⟩ : syracuseStep 2787821 = 1045433) (by norm_num)
theorem B8931829 : Blo 1238437 8931829 := bbase (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) (by norm_num)
theorem B2828789 : Blo 1238437 2828789 := bbase (se 5 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 2828789 = 265199) (by norm_num)
theorem B1395193 : Blo 1238437 1395193 := bbase (se 2 (by rfl) ⟨523197, by rfl⟩ : syracuseStep 1395193 = 1046395) (by norm_num)
theorem B1763861 : Blo 1238437 1763861 := bbase (se 6 (by rfl) ⟨41340, by rfl⟩ : syracuseStep 1763861 = 82681) (by norm_num)
theorem B2091541 : Blo 1238437 2091541 := bbase (se 6 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 2091541 = 98041) (by norm_num)
theorem B1395229 : Blo 1238437 1395229 := bbase (se 3 (by rfl) ⟨261605, by rfl⟩ : syracuseStep 1395229 = 523211) (by norm_num)
theorem B4180517 : Blo 1238437 4180517 := bbase (se 4 (by rfl) ⟨391923, by rfl⟩ : syracuseStep 4180517 = 783847) (by norm_num)
theorem B2787893 : Blo 1238437 2787893 := bbase (se 5 (by rfl) ⟨130682, by rfl⟩ : syracuseStep 2787893 = 261365) (by norm_num)
theorem B9054773 : Blo 1238437 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B2828861 : Blo 1238437 2828861 := bbase (se 3 (by rfl) ⟨530411, by rfl⟩ : syracuseStep 2828861 = 1060823) (by norm_num)
theorem B1395265 : Blo 1238437 1395265 := bbase (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) (by norm_num)
theorem B1395301 : Blo 1238437 1395301 := bbase (se 4 (by rfl) ⟨130809, by rfl⟩ : syracuseStep 1395301 = 261619) (by norm_num)
theorem B2091629 : Blo 1238437 2091629 := bbase (se 3 (by rfl) ⟨392180, by rfl⟩ : syracuseStep 2091629 = 784361) (by norm_num)
theorem B2787965 : Blo 1238437 2787965 := bbase (se 3 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 2787965 = 1045487) (by norm_num)
theorem B2353789 : Blo 1238437 2353789 := bbase (se 3 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 2353789 = 882671) (by norm_num)
theorem B1395337 : Blo 1238437 1395337 := bbase (se 2 (by rfl) ⟨523251, by rfl⟩ : syracuseStep 1395337 = 1046503) (by norm_num)
theorem B1395373 : Blo 1238437 1395373 := bbase (se 3 (by rfl) ⟨261632, by rfl⟩ : syracuseStep 1395373 = 523265) (by norm_num)
theorem B2788037 : Blo 1238437 2788037 := bbase (se 4 (by rfl) ⟨261378, by rfl⟩ : syracuseStep 2788037 = 522757) (by norm_num)
theorem B1567441 : Blo 1238437 1567441 := bbase (se 2 (by rfl) ⟨587790, by rfl⟩ : syracuseStep 1567441 = 1175581) (by norm_num)
theorem B1395409 : Blo 1238437 1395409 := bbase (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) (by norm_num)
theorem B2091757 : Blo 1238437 2091757 := bbase (se 3 (by rfl) ⟨392204, by rfl⟩ : syracuseStep 2091757 = 784409) (by norm_num)
theorem B8932085 : Blo 1238437 8932085 := bbase (se 5 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 8932085 = 837383) (by norm_num)
theorem B1395445 : Blo 1238437 1395445 := bbase (se 5 (by rfl) ⟨65411, by rfl⟩ : syracuseStep 1395445 = 130823) (by norm_num)
theorem B2788109 : Blo 1238437 2788109 := bbase (se 3 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 2788109 = 1045541) (by norm_num)
theorem B1395481 : Blo 1238437 1395481 := bbase (se 2 (by rfl) ⟨523305, by rfl⟩ : syracuseStep 1395481 = 1046611) (by norm_num)
theorem B2091845 : Blo 1238437 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B2788181 : Blo 1238437 2788181 := bbase (se 9 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 2788181 = 16337) (by norm_num)
theorem B5294933 : Blo 1238437 5294933 := bbase (se 9 (by rfl) ⟨15512, by rfl⟩ : syracuseStep 5294933 = 31025) (by norm_num)
theorem B13405013 : Blo 1238437 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B1567613 : Blo 1238437 1567613 := bbase (se 3 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 1567613 = 587855) (by norm_num)
theorem B2788253 : Blo 1238437 2788253 := bbase (se 3 (by rfl) ⟨522797, by rfl⟩ : syracuseStep 2788253 = 1045595) (by norm_num)
theorem B2354093 : Blo 1238437 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B1567669 : Blo 1238437 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B2976709 : Blo 1238437 2976709 := bbase (se 4 (by rfl) ⟨279066, by rfl⟩ : syracuseStep 2976709 = 558133) (by norm_num)
theorem B2091973 : Blo 1238437 2091973 := bbase (se 4 (by rfl) ⟨196122, by rfl⟩ : syracuseStep 2091973 = 392245) (by norm_num)
theorem B1985485 : Blo 1238437 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B4180949 : Blo 1238437 4180949 := bbase (se 7 (by rfl) ⟨48995, by rfl⟩ : syracuseStep 4180949 = 97991) (by norm_num)
theorem B2788325 : Blo 1238437 2788325 := bbase (se 4 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 2788325 = 522811) (by norm_num)
theorem B1567765 : Blo 1238437 1567765 := bbase (se 6 (by rfl) ⟨36744, by rfl⟩ : syracuseStep 1567765 = 73489) (by norm_num)
theorem B2092061 : Blo 1238437 2092061 := bbase (se 3 (by rfl) ⟨392261, by rfl⟩ : syracuseStep 2092061 = 784523) (by norm_num)
theorem B2788397 : Blo 1238437 2788397 := bbase (se 3 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 2788397 = 1045649) (by norm_num)
theorem B3771461 : Blo 1238437 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2788469 : Blo 1238437 2788469 := bbase (se 5 (by rfl) ⟨130709, by rfl⟩ : syracuseStep 2788469 = 261419) (by norm_num)
theorem B1674373 : Blo 1238437 1674373 := bbase (se 4 (by rfl) ⟨156972, by rfl⟩ : syracuseStep 1674373 = 313945) (by norm_num)
theorem B2092189 : Blo 1238437 2092189 := bbase (se 3 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 2092189 = 784571) (by norm_num)
theorem B6278309 : Blo 1238437 6278309 := bbase (se 4 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 6278309 = 1177183) (by norm_num)
theorem B2788541 : Blo 1238437 2788541 := bbase (se 3 (by rfl) ⟨522851, by rfl⟩ : syracuseStep 2788541 = 1045703) (by norm_num)
theorem B1567937 : Blo 1238437 1567937 := bbase (se 2 (by rfl) ⟨587976, by rfl⟩ : syracuseStep 1567937 = 1175953) (by norm_num)
theorem B7056629 : Blo 1238437 7056629 := bbase (se 5 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 7056629 = 661559) (by norm_num)
theorem B2092277 : Blo 1238437 2092277 := bbase (se 5 (by rfl) ⟨98075, by rfl⟩ : syracuseStep 2092277 = 196151) (by norm_num)
theorem B1567993 : Blo 1238437 1567993 := bbase (se 2 (by rfl) ⟨587997, by rfl⟩ : syracuseStep 1567993 = 1175995) (by norm_num)
theorem B1764613 : Blo 1238437 1764613 := bbase (se 4 (by rfl) ⟨165432, by rfl⟩ : syracuseStep 1764613 = 330865) (by norm_num)
theorem B2788613 : Blo 1238437 2788613 := bbase (se 4 (by rfl) ⟨261432, by rfl⟩ : syracuseStep 2788613 = 522865) (by norm_num)
theorem B4705573 : Blo 1238437 4705573 := bbase (se 4 (by rfl) ⟨441147, by rfl⟩ : syracuseStep 4705573 = 882295) (by norm_num)
theorem B2788685 : Blo 1238437 2788685 := bbase (se 3 (by rfl) ⟨522878, by rfl⟩ : syracuseStep 2788685 = 1045757) (by norm_num)
theorem B1568089 : Blo 1238437 1568089 := bbase (se 2 (by rfl) ⟨588033, by rfl⟩ : syracuseStep 1568089 = 1176067) (by norm_num)
theorem B1674589 : Blo 1238437 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B10587509 : Blo 1238437 10587509 := bbase (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) (by norm_num)
theorem B2092405 : Blo 1238437 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B4181381 : Blo 1238437 4181381 := bbase (se 4 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 4181381 = 784009) (by norm_num)
theorem B2788757 : Blo 1238437 2788757 := bbase (se 6 (by rfl) ⟨65361, by rfl⟩ : syracuseStep 2788757 = 130723) (by norm_num)
theorem B2977229 : Blo 1238437 2977229 := bbase (se 3 (by rfl) ⟨558230, by rfl⟩ : syracuseStep 2977229 = 1116461) (by norm_num)
theorem B2092493 : Blo 1238437 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B2788829 : Blo 1238437 2788829 := bbase (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) (by norm_num)
theorem B2264573 : Blo 1238437 2264573 := bbase (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) (by norm_num)
theorem B1568261 : Blo 1238437 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B6696469 : Blo 1238437 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B2788901 : Blo 1238437 2788901 := bbase (se 4 (by rfl) ⟨261459, by rfl⟩ : syracuseStep 2788901 = 522919) (by norm_num)
theorem B1568317 : Blo 1238437 1568317 := bbase (se 3 (by rfl) ⟨294059, by rfl⟩ : syracuseStep 1568317 = 588119) (by norm_num)
theorem B6270533 : Blo 1238437 6270533 := bbase (se 4 (by rfl) ⟨587862, by rfl⟩ : syracuseStep 6270533 = 1175725) (by norm_num)
theorem B2092621 : Blo 1238437 2092621 := bbase (se 3 (by rfl) ⟨392366, by rfl⟩ : syracuseStep 2092621 = 784733) (by norm_num)
theorem B4705877 : Blo 1238437 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B2788973 : Blo 1238437 2788973 := bbase (se 3 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 2788973 = 1045865) (by norm_num)
theorem B1257077 : Blo 1238437 1257077 := bbase (se 5 (by rfl) ⟨58925, by rfl⟩ : syracuseStep 1257077 = 117851) (by norm_num)
theorem B1568413 : Blo 1238437 1568413 := bbase (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) (by norm_num)
theorem B2354845 : Blo 1238437 2354845 := bbase (se 3 (by rfl) ⟨441533, by rfl⟩ : syracuseStep 2354845 = 883067) (by norm_num)
theorem B2092709 : Blo 1238437 2092709 := bbase (se 4 (by rfl) ⟨196191, by rfl⟩ : syracuseStep 2092709 = 392383) (by norm_num)
theorem B2789045 : Blo 1238437 2789045 := bbase (se 5 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 2789045 = 261473) (by norm_num)
theorem B2789117 : Blo 1238437 2789117 := bbase (se 3 (by rfl) ⟨522959, by rfl⟩ : syracuseStep 2789117 = 1045919) (by norm_num)
theorem B1675037 : Blo 1238437 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B2092837 : Blo 1238437 2092837 := bbase (se 4 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 2092837 = 392407) (by norm_num)
theorem B4181813 : Blo 1238437 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B2789189 : Blo 1238437 2789189 := bbase (se 4 (by rfl) ⟨261486, by rfl⟩ : syracuseStep 2789189 = 522973) (by norm_num)
theorem B1568585 : Blo 1238437 1568585 := bbase (se 2 (by rfl) ⟨588219, by rfl⟩ : syracuseStep 1568585 = 1176439) (by norm_num)
theorem B2977613 : Blo 1238437 2977613 := bbase (se 3 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 2977613 = 1116605) (by norm_num)
theorem B2977661 : Blo 1238437 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B2092925 : Blo 1238437 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B1568641 : Blo 1238437 1568641 := bbase (se 2 (by rfl) ⟨588240, by rfl⟩ : syracuseStep 1568641 = 1176481) (by norm_num)
theorem B2977669 : Blo 1238437 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B2789261 : Blo 1238437 2789261 := bbase (se 3 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 2789261 = 1045973) (by norm_num)
theorem B2789333 : Blo 1238437 2789333 := bbase (se 7 (by rfl) ⟨32687, by rfl⟩ : syracuseStep 2789333 = 65375) (by norm_num)
theorem B1568737 : Blo 1238437 1568737 := bbase (se 2 (by rfl) ⟨588276, by rfl⟩ : syracuseStep 1568737 = 1176553) (by norm_num)
theorem B2232301 : Blo 1238437 2232301 := bbase (se 3 (by rfl) ⟨418556, by rfl⟩ : syracuseStep 2232301 = 837113) (by norm_num)
theorem B2093053 : Blo 1238437 2093053 := bbase (se 3 (by rfl) ⟨392447, by rfl⟩ : syracuseStep 2093053 = 784895) (by norm_num)
theorem B2789405 : Blo 1238437 2789405 := bbase (se 3 (by rfl) ⟨523013, by rfl⟩ : syracuseStep 2789405 = 1046027) (by norm_num)
theorem B1765405 : Blo 1238437 1765405 := bbase (se 3 (by rfl) ⟨331013, by rfl⟩ : syracuseStep 1765405 = 662027) (by norm_num)
theorem B2093141 : Blo 1238437 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1323101 : Blo 1238437 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B3969125 : Blo 1238437 3969125 := bbase (se 4 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 3969125 = 744211) (by norm_num)
theorem B2789477 : Blo 1238437 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B5959781 : Blo 1238437 5959781 := bbase (se 4 (by rfl) ⟨558729, by rfl⟩ : syracuseStep 5959781 = 1117459) (by norm_num)
theorem B1986677 : Blo 1238437 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B2232461 : Blo 1238437 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B1568909 : Blo 1238437 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B2789549 : Blo 1238437 2789549 := bbase (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) (by norm_num)
theorem B1568965 : Blo 1238437 1568965 := bbase (se 4 (by rfl) ⟨147090, by rfl⟩ : syracuseStep 1568965 = 294181) (by norm_num)
theorem B9539797 : Blo 1238437 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B4182245 : Blo 1238437 4182245 := bbase (se 4 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 4182245 = 784171) (by norm_num)
theorem B2265317 : Blo 1238437 2265317 := bbase (se 4 (by rfl) ⟨212373, by rfl⟩ : syracuseStep 2265317 = 424747) (by norm_num)
theorem B2789621 : Blo 1238437 2789621 := bbase (se 5 (by rfl) ⟨130763, by rfl⟩ : syracuseStep 2789621 = 261527) (by norm_num)
theorem B1569061 : Blo 1238437 1569061 := bbase (se 4 (by rfl) ⟨147099, by rfl⟩ : syracuseStep 1569061 = 294199) (by norm_num)
theorem B1986869 : Blo 1238437 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B2789693 : Blo 1238437 2789693 := bbase (se 3 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 2789693 = 1046135) (by norm_num)
theorem B1765741 : Blo 1238437 1765741 := bbase (se 3 (by rfl) ⟨331076, by rfl⟩ : syracuseStep 1765741 = 662153) (by norm_num)
theorem B2789765 : Blo 1238437 2789765 := bbase (se 4 (by rfl) ⟨261540, by rfl⟩ : syracuseStep 2789765 = 523081) (by norm_num)
theorem B7057813 : Blo 1238437 7057813 := bbase (se 6 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 7057813 = 330835) (by norm_num)
theorem B1937837 : Blo 1238437 1937837 := bbase (se 3 (by rfl) ⟨363344, by rfl⟩ : syracuseStep 1937837 = 726689) (by norm_num)
theorem B6279605 : Blo 1238437 6279605 := bbase (se 5 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 6279605 = 588713) (by norm_num)
theorem B2789837 : Blo 1238437 2789837 := bbase (se 3 (by rfl) ⟨523094, by rfl⟩ : syracuseStep 2789837 = 1046189) (by norm_num)
theorem B1569233 : Blo 1238437 1569233 := bbase (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) (by norm_num)
theorem B1569289 : Blo 1238437 1569289 := bbase (se 2 (by rfl) ⟨588483, by rfl⟩ : syracuseStep 1569289 = 1176967) (by norm_num)
theorem B2789909 : Blo 1238437 2789909 := bbase (se 6 (by rfl) ⟨65388, by rfl⟩ : syracuseStep 2789909 = 130777) (by norm_num)
theorem B1323545 : Blo 1238437 1323545 := bbase (se 2 (by rfl) ⟨496329, by rfl⟩ : syracuseStep 1323545 = 992659) (by norm_num)
theorem B3527221 : Blo 1238437 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1765957 : Blo 1238437 1765957 := bbase (se 4 (by rfl) ⟨165558, by rfl⟩ : syracuseStep 1765957 = 331117) (by norm_num)
theorem B2789981 : Blo 1238437 2789981 := bbase (se 3 (by rfl) ⟨523121, by rfl⟩ : syracuseStep 2789981 = 1046243) (by norm_num)
theorem B1569385 : Blo 1238437 1569385 := bbase (se 2 (by rfl) ⟨588519, by rfl⟩ : syracuseStep 1569385 = 1177039) (by norm_num)
theorem B5952149 : Blo 1238437 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B4182677 : Blo 1238437 4182677 := bbase (se 6 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 4182677 = 196063) (by norm_num)
theorem B2790053 : Blo 1238437 2790053 := bbase (se 4 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 2790053 = 523135) (by norm_num)
theorem B3527381 : Blo 1238437 3527381 := bbase (se 7 (by rfl) ⟨41336, by rfl⟩ : syracuseStep 3527381 = 82673) (by norm_num)
theorem B2790125 : Blo 1238437 2790125 := bbase (se 3 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 2790125 = 1046297) (by norm_num)
theorem B1323793 : Blo 1238437 1323793 := bbase (se 2 (by rfl) ⟨496422, by rfl⟩ : syracuseStep 1323793 = 992845) (by norm_num)
theorem B1569557 : Blo 1238437 1569557 := bbase (se 6 (by rfl) ⟨36786, by rfl⟩ : syracuseStep 1569557 = 73573) (by norm_num)
theorem B2790197 : Blo 1238437 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B1569613 : Blo 1238437 1569613 := bbase (se 3 (by rfl) ⟨294302, by rfl⟩ : syracuseStep 1569613 = 588605) (by norm_num)
theorem B6271829 : Blo 1238437 6271829 := bbase (se 9 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 6271829 = 36749) (by norm_num)
theorem B1291117 : Blo 1238437 1291117 := bbase (se 3 (by rfl) ⟨242084, by rfl⟩ : syracuseStep 1291117 = 484169) (by norm_num)
theorem B2978669 : Blo 1238437 2978669 := bbase (se 3 (by rfl) ⟨558500, by rfl⟩ : syracuseStep 2978669 = 1117001) (by norm_num)
theorem B2790269 : Blo 1238437 2790269 := bbase (se 3 (by rfl) ⟨523175, by rfl⟩ : syracuseStep 2790269 = 1046351) (by norm_num)
theorem B1569709 : Blo 1238437 1569709 := bbase (se 3 (by rfl) ⟨294320, by rfl⟩ : syracuseStep 1569709 = 588641) (by norm_num)
theorem B7943093 : Blo 1238437 7943093 := bbase (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) (by norm_num)
theorem B3527621 : Blo 1238437 3527621 := bbase (se 4 (by rfl) ⟨330714, by rfl⟩ : syracuseStep 3527621 = 661429) (by norm_num)
theorem B2790341 : Blo 1238437 2790341 := bbase (se 4 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 2790341 = 523189) (by norm_num)
theorem B3224573 : Blo 1238437 3224573 := bbase (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) (by norm_num)
theorem B2790413 : Blo 1238437 2790413 := bbase (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) (by norm_num)
theorem B1487893 : Blo 1238437 1487893 := bbase (se 6 (by rfl) ⟨34872, by rfl⟩ : syracuseStep 1487893 = 69745) (by norm_num)
theorem B2978861 : Blo 1238437 2978861 := bbase (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) (by norm_num)
theorem B6362165 : Blo 1238437 6362165 := bbase (se 5 (by rfl) ⟨298226, by rfl⟩ : syracuseStep 6362165 = 596453) (by norm_num)
theorem B4183109 : Blo 1238437 4183109 := bbase (se 4 (by rfl) ⟨392166, by rfl⟩ : syracuseStep 4183109 = 784333) (by norm_num)
theorem B2790485 : Blo 1238437 2790485 := bbase (se 8 (by rfl) ⟨16350, by rfl⟩ : syracuseStep 2790485 = 32701) (by norm_num)
theorem B1569881 : Blo 1238437 1569881 := bbase (se 2 (by rfl) ⟨588705, by rfl⟩ : syracuseStep 1569881 = 1177411) (by norm_num)
theorem B1676389 : Blo 1238437 1676389 := bbase (se 4 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 1676389 = 314323) (by norm_num)
theorem B3527813 : Blo 1238437 3527813 := bbase (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) (by norm_num)
theorem B2790557 : Blo 1238437 2790557 := bbase (se 3 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 2790557 = 1046459) (by norm_num)
theorem B4240565 : Blo 1238437 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B1324225 : Blo 1238437 1324225 := bbase (se 2 (by rfl) ⟨496584, by rfl⟩ : syracuseStep 1324225 = 993169) (by norm_num)
theorem B2233541 : Blo 1238437 2233541 := bbase (se 4 (by rfl) ⟨209394, by rfl⟩ : syracuseStep 2233541 = 418789) (by norm_num)
theorem B11310293 : Blo 1238437 11310293 := bbase (se 7 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 11310293 = 265085) (by norm_num)
theorem B2790629 : Blo 1238437 2790629 := bbase (se 4 (by rfl) ⟨261621, by rfl⟩ : syracuseStep 2790629 = 523243) (by norm_num)
theorem B2512117 : Blo 1238437 2512117 := bbase (se 5 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 2512117 = 235511) (by norm_num)
theorem B1324297 : Blo 1238437 1324297 := bbase (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) (by norm_num)
theorem B14316821 : Blo 1238437 14316821 := bbase (se 6 (by rfl) ⟨335550, by rfl⟩ : syracuseStep 14316821 = 671101) (by norm_num)
theorem B2790701 : Blo 1238437 2790701 := bbase (se 3 (by rfl) ⟨523256, by rfl⟩ : syracuseStep 2790701 = 1046513) (by norm_num)
theorem B2233685 : Blo 1238437 2233685 := bbase (se 14 (by rfl) ⟨204, by rfl⟩ : syracuseStep 2233685 = 409) (by norm_num)
theorem B3134821 : Blo 1238437 3134821 := bbase (se 4 (by rfl) ⟨293889, by rfl⟩ : syracuseStep 3134821 = 587779) (by norm_num)
theorem B2790773 : Blo 1238437 2790773 := bbase (se 5 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 2790773 = 261635) (by norm_num)
theorem B2790845 : Blo 1238437 2790845 := bbase (se 3 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 2790845 = 1046567) (by norm_num)
theorem B3134933 : Blo 1238437 3134933 := bbase (se 7 (by rfl) ⟨36737, by rfl⟩ : syracuseStep 3134933 = 73475) (by norm_num)
theorem B4183541 : Blo 1238437 4183541 := bbase (se 5 (by rfl) ⟨196103, by rfl⟩ : syracuseStep 4183541 = 392207) (by norm_num)
theorem B2790917 : Blo 1238437 2790917 := bbase (se 4 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 2790917 = 523297) (by norm_num)
theorem B3061373 : Blo 1238437 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B3135125 : Blo 1238437 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B4707989 : Blo 1238437 4707989 := bbase (se 6 (by rfl) ⟨110343, by rfl⟩ : syracuseStep 4707989 = 220687) (by norm_num)
theorem B3766181 : Blo 1238437 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B4183973 : Blo 1238437 4183973 := bbase (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) (by norm_num)
theorem B1341361 : Blo 1238437 1341361 := bbase (se 2 (by rfl) ⟨503010, by rfl⟩ : syracuseStep 1341361 = 1006021) (by norm_num)
theorem B4708277 : Blo 1238437 4708277 := bbase (se 5 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 4708277 = 441401) (by norm_num)
theorem B5953493 : Blo 1238437 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B3135469 : Blo 1238437 3135469 := bbase (se 3 (by rfl) ⟨587900, by rfl⟩ : syracuseStep 3135469 = 1175801) (by norm_num)
theorem B5363765 : Blo 1238437 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B2119765 : Blo 1238437 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B3135581 : Blo 1238437 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B6273125 : Blo 1238437 6273125 := bbase (se 4 (by rfl) ⟨588105, by rfl⟩ : syracuseStep 6273125 = 1176211) (by norm_num)
theorem B3528805 : Blo 1238437 3528805 := bbase (se 4 (by rfl) ⟨330825, by rfl⟩ : syracuseStep 3528805 = 661651) (by norm_num)
theorem B4528261 : Blo 1238437 4528261 := bbase (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) (by norm_num)
theorem B1857677 : Blo 1238437 1857677 := bbase (se 3 (by rfl) ⟨348314, by rfl⟩ : syracuseStep 1857677 = 696629) (by norm_num)
theorem B1857701 : Blo 1238437 1857701 := bbase (se 4 (by rfl) ⟨174159, by rfl⟩ : syracuseStep 1857701 = 348319) (by norm_num)
theorem B1857725 : Blo 1238437 1857725 := bbase (se 3 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 1857725 = 696647) (by norm_num)
theorem B1857749 : Blo 1238437 1857749 := bbase (se 7 (by rfl) ⟨21770, by rfl⟩ : syracuseStep 1857749 = 43541) (by norm_num)
theorem B1857773 : Blo 1238437 1857773 := bbase (se 3 (by rfl) ⟨348332, by rfl⟩ : syracuseStep 1857773 = 696665) (by norm_num)
theorem B1857797 : Blo 1238437 1857797 := bbase (se 4 (by rfl) ⟨174168, by rfl⟩ : syracuseStep 1857797 = 348337) (by norm_num)
theorem B1857821 : Blo 1238437 1857821 := bbase (se 3 (by rfl) ⟨348341, by rfl⟩ : syracuseStep 1857821 = 696683) (by norm_num)
theorem B3135773 : Blo 1238437 3135773 := bbase (se 3 (by rfl) ⟨587957, by rfl⟩ : syracuseStep 3135773 = 1175915) (by norm_num)
theorem B1857845 : Blo 1238437 1857845 := bbase (se 5 (by rfl) ⟨87086, by rfl⟩ : syracuseStep 1857845 = 174173) (by norm_num)
theorem B1431865 : Blo 1238437 1431865 := bbase (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) (by norm_num)
theorem B1857869 : Blo 1238437 1857869 := bbase (se 3 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 1857869 = 696701) (by norm_num)
theorem B7059797 : Blo 1238437 7059797 := bbase (se 10 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 7059797 = 20683) (by norm_num)
theorem B4184405 : Blo 1238437 4184405 := bbase (se 10 (by rfl) ⟨6129, by rfl⟩ : syracuseStep 4184405 = 12259) (by norm_num)
theorem B1857893 : Blo 1238437 1857893 := bbase (se 4 (by rfl) ⟨174177, by rfl⟩ : syracuseStep 1857893 = 348355) (by norm_num)
theorem B1857917 : Blo 1238437 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B1489277 : Blo 1238437 1489277 := bbase (se 3 (by rfl) ⟨279239, by rfl⟩ : syracuseStep 1489277 = 558479) (by norm_num)
theorem B1857941 : Blo 1238437 1857941 := bbase (se 6 (by rfl) ⟨43545, by rfl⟩ : syracuseStep 1857941 = 87091) (by norm_num)
theorem B2513317 : Blo 1238437 2513317 := bbase (se 4 (by rfl) ⟨235623, by rfl⟩ : syracuseStep 2513317 = 471247) (by norm_num)
theorem B1857965 : Blo 1238437 1857965 := bbase (se 3 (by rfl) ⟨348368, by rfl⟩ : syracuseStep 1857965 = 696737) (by norm_num)
theorem B1857989 : Blo 1238437 1857989 := bbase (se 4 (by rfl) ⟨174186, by rfl⟩ : syracuseStep 1857989 = 348373) (by norm_num)
theorem B1858013 : Blo 1238437 1858013 := bbase (se 3 (by rfl) ⟨348377, by rfl⟩ : syracuseStep 1858013 = 696755) (by norm_num)
theorem B1858037 : Blo 1238437 1858037 := bbase (se 5 (by rfl) ⟨87095, by rfl⟩ : syracuseStep 1858037 = 174191) (by norm_num)
theorem B1858061 : Blo 1238437 1858061 := bbase (se 3 (by rfl) ⟨348386, by rfl⟩ : syracuseStep 1858061 = 696773) (by norm_num)
theorem B1858085 : Blo 1238437 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1858109 : Blo 1238437 1858109 := bbase (se 3 (by rfl) ⟨348395, by rfl⟩ : syracuseStep 1858109 = 696791) (by norm_num)
theorem B1858133 : Blo 1238437 1858133 := bbase (se 8 (by rfl) ⟨10887, by rfl⟩ : syracuseStep 1858133 = 21775) (by norm_num)
theorem B1858157 : Blo 1238437 1858157 := bbase (se 3 (by rfl) ⟨348404, by rfl⟩ : syracuseStep 1858157 = 696809) (by norm_num)
theorem B3136117 : Blo 1238437 3136117 := bbase (se 5 (by rfl) ⟨147005, by rfl⟩ : syracuseStep 3136117 = 294011) (by norm_num)
theorem B1489537 : Blo 1238437 1489537 := bbase (se 2 (by rfl) ⟨558576, by rfl⟩ : syracuseStep 1489537 = 1117153) (by norm_num)
theorem B1858181 : Blo 1238437 1858181 := bbase (se 4 (by rfl) ⟨174204, by rfl⟩ : syracuseStep 1858181 = 348409) (by norm_num)
theorem B1858205 : Blo 1238437 1858205 := bbase (se 3 (by rfl) ⟨348413, by rfl⟩ : syracuseStep 1858205 = 696827) (by norm_num)
theorem B1489585 : Blo 1238437 1489585 := bbase (se 2 (by rfl) ⟨558594, by rfl⟩ : syracuseStep 1489585 = 1117189) (by norm_num)
theorem B1858229 : Blo 1238437 1858229 := bbase (se 5 (by rfl) ⟨87104, by rfl⟩ : syracuseStep 1858229 = 174209) (by norm_num)
theorem B1858253 : Blo 1238437 1858253 := bbase (se 3 (by rfl) ⟨348422, by rfl⟩ : syracuseStep 1858253 = 696845) (by norm_num)
theorem B3627733 : Blo 1238437 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B1858277 : Blo 1238437 1858277 := bbase (se 4 (by rfl) ⟨174213, by rfl⟩ : syracuseStep 1858277 = 348427) (by norm_num)
theorem B3136229 : Blo 1238437 3136229 := bbase (se 4 (by rfl) ⟨294021, by rfl⟩ : syracuseStep 3136229 = 588043) (by norm_num)
theorem B1858301 : Blo 1238437 1858301 := bbase (se 3 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 1858301 = 696863) (by norm_num)
theorem B4184837 : Blo 1238437 4184837 := bbase (se 4 (by rfl) ⟨392328, by rfl⟩ : syracuseStep 4184837 = 784657) (by norm_num)
theorem B1858325 : Blo 1238437 1858325 := bbase (se 6 (by rfl) ⟨43554, by rfl⟩ : syracuseStep 1858325 = 87109) (by norm_num)
theorem B1858349 : Blo 1238437 1858349 := bbase (se 3 (by rfl) ⟨348440, by rfl⟩ : syracuseStep 1858349 = 696881) (by norm_num)
theorem B1858373 : Blo 1238437 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B1858397 : Blo 1238437 1858397 := bbase (se 3 (by rfl) ⟨348449, by rfl⟩ : syracuseStep 1858397 = 696899) (by norm_num)
theorem B8592245 : Blo 1238437 8592245 := bbase (se 5 (by rfl) ⟨402761, by rfl⟩ : syracuseStep 8592245 = 805523) (by norm_num)
theorem B1858421 : Blo 1238437 1858421 := bbase (se 5 (by rfl) ⟨87113, by rfl⟩ : syracuseStep 1858421 = 174227) (by norm_num)
theorem B2120573 : Blo 1238437 2120573 := bbase (se 3 (by rfl) ⟨397607, by rfl⟩ : syracuseStep 2120573 = 795215) (by norm_num)
theorem B1858445 : Blo 1238437 1858445 := bbase (se 3 (by rfl) ⟨348458, by rfl⟩ : syracuseStep 1858445 = 696917) (by norm_num)
theorem B1858469 : Blo 1238437 1858469 := bbase (se 4 (by rfl) ⟨174231, by rfl⟩ : syracuseStep 1858469 = 348463) (by norm_num)
theorem B3136421 : Blo 1238437 3136421 := bbase (se 4 (by rfl) ⟨294039, by rfl⟩ : syracuseStep 3136421 = 588079) (by norm_num)
theorem B1858493 : Blo 1238437 1858493 := bbase (se 3 (by rfl) ⟨348467, by rfl⟩ : syracuseStep 1858493 = 696935) (by norm_num)
theorem B1858517 : Blo 1238437 1858517 := bbase (se 7 (by rfl) ⟨21779, by rfl⟩ : syracuseStep 1858517 = 43559) (by norm_num)
theorem B6364133 : Blo 1238437 6364133 := bbase (se 4 (by rfl) ⟨596637, by rfl⟩ : syracuseStep 6364133 = 1193275) (by norm_num)
theorem B1858541 : Blo 1238437 1858541 := bbase (se 3 (by rfl) ⟨348476, by rfl⟩ : syracuseStep 1858541 = 696953) (by norm_num)
theorem B1858565 : Blo 1238437 1858565 := bbase (se 4 (by rfl) ⟨174240, by rfl⟩ : syracuseStep 1858565 = 348481) (by norm_num)
theorem B1342469 : Blo 1238437 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B1858589 : Blo 1238437 1858589 := bbase (se 3 (by rfl) ⟨348485, by rfl⟩ : syracuseStep 1858589 = 696971) (by norm_num)
theorem B1858613 : Blo 1238437 1858613 := bbase (se 5 (by rfl) ⟨87122, by rfl⟩ : syracuseStep 1858613 = 174245) (by norm_num)
theorem B2825293 : Blo 1238437 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B1858637 : Blo 1238437 1858637 := bbase (se 3 (by rfl) ⟨348494, by rfl⟩ : syracuseStep 1858637 = 696989) (by norm_num)
theorem B4709461 : Blo 1238437 4709461 := bbase (se 8 (by rfl) ⟨27594, by rfl⟩ : syracuseStep 4709461 = 55189) (by norm_num)
theorem B1858661 : Blo 1238437 1858661 := bbase (se 4 (by rfl) ⟨174249, by rfl⟩ : syracuseStep 1858661 = 348499) (by norm_num)
theorem B1858685 : Blo 1238437 1858685 := bbase (se 3 (by rfl) ⟨348503, by rfl⟩ : syracuseStep 1858685 = 697007) (by norm_num)
theorem B1858709 : Blo 1238437 1858709 := bbase (se 6 (by rfl) ⟨43563, by rfl⟩ : syracuseStep 1858709 = 87127) (by norm_num)
theorem B5291173 : Blo 1238437 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B1858733 : Blo 1238437 1858733 := bbase (se 3 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 1858733 = 697025) (by norm_num)
theorem B3529909 : Blo 1238437 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B4185269 : Blo 1238437 4185269 := bbase (se 5 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 4185269 = 392369) (by norm_num)
theorem B1858757 : Blo 1238437 1858757 := bbase (se 4 (by rfl) ⟨174258, by rfl⟩ : syracuseStep 1858757 = 348517) (by norm_num)
theorem B3177677 : Blo 1238437 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B1858781 : Blo 1238437 1858781 := bbase (se 3 (by rfl) ⟨348521, by rfl⟩ : syracuseStep 1858781 = 697043) (by norm_num)
theorem B2645237 : Blo 1238437 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B1858805 : Blo 1238437 1858805 := bbase (se 5 (by rfl) ⟨87131, by rfl⟩ : syracuseStep 1858805 = 174263) (by norm_num)
theorem B2645245 : Blo 1238437 2645245 := bbase (se 3 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 2645245 = 991967) (by norm_num)
theorem B3136765 : Blo 1238437 3136765 := bbase (se 3 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 3136765 = 1176287) (by norm_num)
theorem B5160197 : Blo 1238437 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B1858829 : Blo 1238437 1858829 := bbase (se 3 (by rfl) ⟨348530, by rfl⟩ : syracuseStep 1858829 = 697061) (by norm_num)
theorem B1858853 : Blo 1238437 1858853 := bbase (se 4 (by rfl) ⟨174267, by rfl⟩ : syracuseStep 1858853 = 348535) (by norm_num)
theorem B1858877 : Blo 1238437 1858877 := bbase (se 3 (by rfl) ⟨348539, by rfl⟩ : syracuseStep 1858877 = 697079) (by norm_num)
theorem B1858901 : Blo 1238437 1858901 := bbase (se 11 (by rfl) ⟨1361, by rfl⟩ : syracuseStep 1858901 = 2723) (by norm_num)
theorem B5954917 : Blo 1238437 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B3136877 : Blo 1238437 3136877 := bbase (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) (by norm_num)
theorem B1858925 : Blo 1238437 1858925 := bbase (se 3 (by rfl) ⟨348548, by rfl⟩ : syracuseStep 1858925 = 697097) (by norm_num)
theorem B6274421 : Blo 1238437 6274421 := bbase (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) (by norm_num)
theorem B1858949 : Blo 1238437 1858949 := bbase (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) (by norm_num)
theorem B4709765 : Blo 1238437 4709765 := bbase (se 4 (by rfl) ⟨441540, by rfl⟩ : syracuseStep 4709765 = 883081) (by norm_num)
theorem B1858973 : Blo 1238437 1858973 := bbase (se 3 (by rfl) ⟨348557, by rfl⟩ : syracuseStep 1858973 = 697115) (by norm_num)
theorem B1858997 : Blo 1238437 1858997 := bbase (se 5 (by rfl) ⟨87140, by rfl⟩ : syracuseStep 1858997 = 174281) (by norm_num)
theorem B1859021 : Blo 1238437 1859021 := bbase (se 3 (by rfl) ⟨348566, by rfl⟩ : syracuseStep 1859021 = 697133) (by norm_num)
theorem B1859045 : Blo 1238437 1859045 := bbase (se 4 (by rfl) ⟨174285, by rfl⟩ : syracuseStep 1859045 = 348571) (by norm_num)
theorem B1859069 : Blo 1238437 1859069 := bbase (se 3 (by rfl) ⟨348575, by rfl⟩ : syracuseStep 1859069 = 697151) (by norm_num)
theorem B1859093 : Blo 1238437 1859093 := bbase (se 6 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 1859093 = 87145) (by norm_num)
theorem B5307925 : Blo 1238437 5307925 := bbase (se 6 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 5307925 = 248809) (by norm_num)
theorem B3137069 : Blo 1238437 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B1859117 : Blo 1238437 1859117 := bbase (se 3 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 1859117 = 697169) (by norm_num)
theorem B2514485 : Blo 1238437 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B1859141 : Blo 1238437 1859141 := bbase (se 4 (by rfl) ⟨174294, by rfl⟩ : syracuseStep 1859141 = 348589) (by norm_num)
theorem B1859165 : Blo 1238437 1859165 := bbase (se 3 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 1859165 = 697187) (by norm_num)
theorem B4185701 : Blo 1238437 4185701 := bbase (se 4 (by rfl) ⟨392409, by rfl⟩ : syracuseStep 4185701 = 784819) (by norm_num)
theorem B1859189 : Blo 1238437 1859189 := bbase (se 5 (by rfl) ⟨87149, by rfl⟩ : syracuseStep 1859189 = 174299) (by norm_num)
theorem B1859213 : Blo 1238437 1859213 := bbase (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) (by norm_num)
theorem B1859237 : Blo 1238437 1859237 := bbase (se 4 (by rfl) ⟨174303, by rfl⟩ : syracuseStep 1859237 = 348607) (by norm_num)
theorem B1859261 : Blo 1238437 1859261 := bbase (se 3 (by rfl) ⟨348611, by rfl⟩ : syracuseStep 1859261 = 697223) (by norm_num)
theorem B1859285 : Blo 1238437 1859285 := bbase (se 7 (by rfl) ⟨21788, by rfl⟩ : syracuseStep 1859285 = 43577) (by norm_num)
theorem B1859309 : Blo 1238437 1859309 := bbase (se 3 (by rfl) ⟨348620, by rfl⟩ : syracuseStep 1859309 = 697241) (by norm_num)
theorem B2351101 : Blo 1238437 2351101 := bbase (se 3 (by rfl) ⟨440831, by rfl⟩ : syracuseStep 2351101 = 881663) (by norm_num)
theorem B1859333 : Blo 1238437 1859333 := bbase (se 4 (by rfl) ⟨174312, by rfl⟩ : syracuseStep 1859333 = 348625) (by norm_num)
theorem B1859357 : Blo 1238437 1859357 := bbase (se 3 (by rfl) ⟨348629, by rfl⟩ : syracuseStep 1859357 = 697259) (by norm_num)
theorem B6356789 : Blo 1238437 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B1859381 : Blo 1238437 1859381 := bbase (se 5 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 1859381 = 174317) (by norm_num)
theorem B1859405 : Blo 1238437 1859405 := bbase (se 3 (by rfl) ⟨348638, by rfl⟩ : syracuseStep 1859405 = 697277) (by norm_num)
theorem B2121557 : Blo 1238437 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B1859429 : Blo 1238437 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B1859453 : Blo 1238437 1859453 := bbase (se 3 (by rfl) ⟨348647, by rfl⟩ : syracuseStep 1859453 = 697295) (by norm_num)
theorem B3137413 : Blo 1238437 3137413 := bbase (se 4 (by rfl) ⟨294132, by rfl⟩ : syracuseStep 3137413 = 588265) (by norm_num)
theorem B1859477 : Blo 1238437 1859477 := bbase (se 6 (by rfl) ⟨43581, by rfl⟩ : syracuseStep 1859477 = 87163) (by norm_num)
theorem B1859501 : Blo 1238437 1859501 := bbase (se 3 (by rfl) ⟨348656, by rfl⟩ : syracuseStep 1859501 = 697313) (by norm_num)
theorem B3973045 : Blo 1238437 3973045 := bbase (se 5 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 3973045 = 372473) (by norm_num)
theorem B1859525 : Blo 1238437 1859525 := bbase (se 4 (by rfl) ⟨174330, by rfl⟩ : syracuseStep 1859525 = 348661) (by norm_num)
theorem B1859549 : Blo 1238437 1859549 := bbase (se 3 (by rfl) ⟨348665, by rfl⟩ : syracuseStep 1859549 = 697331) (by norm_num)
theorem B3137525 : Blo 1238437 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B1859573 : Blo 1238437 1859573 := bbase (se 5 (by rfl) ⟨87167, by rfl⟩ : syracuseStep 1859573 = 174335) (by norm_num)
theorem B1908733 : Blo 1238437 1908733 := bbase (se 3 (by rfl) ⟨357887, by rfl⟩ : syracuseStep 1908733 = 715775) (by norm_num)
theorem B1859585 : Blo 1238437 1859585 := bstep (se 2 (by rfl) ⟨697344, by rfl⟩ : syracuseStep 1859585 = 1394689) B1394689
theorem B3579917 : Blo 1238437 3579917 := bstep (se 3 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 3579917 = 1342469) B1342469
theorem B1859603 : Blo 1238437 1859603 := bstep (se 1 (by rfl) ⟨1394702, by rfl⟩ : syracuseStep 1859603 = 2789405) B2789405
theorem B2646065 : Blo 1238437 2646065 := bstep (se 2 (by rfl) ⟨992274, by rfl⟩ : syracuseStep 2646065 = 1984549) B1984549
theorem B1859633 : Blo 1238437 1859633 := bstep (se 2 (by rfl) ⟨697362, by rfl⟩ : syracuseStep 1859633 = 1394725) B1394725
theorem B2646083 : Blo 1238437 2646083 := bstep (se 1 (by rfl) ⟨1984562, by rfl⟩ : syracuseStep 2646083 = 3969125) B3969125
theorem B1859651 : Blo 1238437 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B3973187 : Blo 1238437 3973187 := bstep (se 1 (by rfl) ⟨2979890, by rfl⟩ : syracuseStep 3973187 = 5959781) B5959781
theorem B1859681 : Blo 1238437 1859681 := bstep (se 2 (by rfl) ⟨697380, by rfl⟩ : syracuseStep 1859681 = 1394761) B1394761
theorem B2826353 : Blo 1238437 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B1859699 : Blo 1238437 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B1859729 : Blo 1238437 1859729 := bstep (se 2 (by rfl) ⟨697398, by rfl⟩ : syracuseStep 1859729 = 1394797) B1394797
theorem B1859747 : Blo 1238437 1859747 := bstep (se 1 (by rfl) ⟨1394810, by rfl⟩ : syracuseStep 1859747 = 2789621) B2789621
theorem B6037681 : Blo 1238437 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B3629233 : Blo 1238437 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B1859777 : Blo 1238437 1859777 := bstep (se 2 (by rfl) ⟨697416, by rfl⟩ : syracuseStep 1859777 = 1394833) B1394833
theorem B1859795 : Blo 1238437 1859795 := bstep (se 1 (by rfl) ⟨1394846, by rfl⟩ : syracuseStep 1859795 = 2789693) B2789693
theorem B4186349 : Blo 1238437 4186349 := bstep (se 3 (by rfl) ⟨784940, by rfl⟩ : syracuseStep 4186349 = 1569881) B1569881
theorem B1859825 : Blo 1238437 1859825 := bstep (se 2 (by rfl) ⟨697434, by rfl⟩ : syracuseStep 1859825 = 1394869) B1394869
theorem B1859843 : Blo 1238437 1859843 := bstep (se 1 (by rfl) ⟨1394882, by rfl⟩ : syracuseStep 1859843 = 2789765) B2789765
theorem B1859873 : Blo 1238437 1859873 := bstep (se 2 (by rfl) ⟨697452, by rfl⟩ : syracuseStep 1859873 = 1394905) B1394905
theorem B4186403 : Blo 1238437 4186403 := bstep (se 1 (by rfl) ⟨3139802, by rfl⟩ : syracuseStep 4186403 = 6279605) B6279605
theorem B1589555 : Blo 1238437 1589555 := bstep (se 1 (by rfl) ⟨1192166, by rfl⟩ : syracuseStep 1589555 = 2384333) B2384333
theorem B1859891 : Blo 1238437 1859891 := bstep (se 1 (by rfl) ⟨1394918, by rfl⟩ : syracuseStep 1859891 = 2789837) B2789837
theorem B1859921 : Blo 1238437 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B1859939 : Blo 1238437 1859939 := bstep (se 1 (by rfl) ⟨1394954, by rfl⟩ : syracuseStep 1859939 = 2789909) B2789909
theorem B9060707 : Blo 1238437 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B1859969 : Blo 1238437 1859969 := bstep (se 2 (by rfl) ⟨697488, by rfl⟩ : syracuseStep 1859969 = 1394977) B1394977
theorem B1859987 : Blo 1238437 1859987 := bstep (se 1 (by rfl) ⟨1394990, by rfl⟩ : syracuseStep 1859987 = 2789981) B2789981
theorem B1909153 : Blo 1238437 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B1860017 : Blo 1238437 1860017 := bstep (se 2 (by rfl) ⟨697506, by rfl⟩ : syracuseStep 1860017 = 1395013) B1395013
theorem B3531185 : Blo 1238437 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B1860035 : Blo 1238437 1860035 := bstep (se 1 (by rfl) ⟨1395026, by rfl⟩ : syracuseStep 1860035 = 2790053) B2790053
theorem B1860065 : Blo 1238437 1860065 := bstep (se 2 (by rfl) ⟨697524, by rfl⟩ : syracuseStep 1860065 = 1395049) B1395049
theorem B2351587 : Blo 1238437 2351587 := bstep (se 1 (by rfl) ⟨1763690, by rfl⟩ : syracuseStep 2351587 = 3527381) B3527381
theorem B6275555 : Blo 1238437 6275555 := bstep (se 1 (by rfl) ⟨4706666, by rfl⟩ : syracuseStep 6275555 = 9413333) B9413333
theorem B1860083 : Blo 1238437 1860083 := bstep (se 1 (by rfl) ⟨1395062, by rfl⟩ : syracuseStep 1860083 = 2790125) B2790125
theorem B1860113 : Blo 1238437 1860113 := bstep (se 2 (by rfl) ⟨697542, by rfl⟩ : syracuseStep 1860113 = 1395085) B1395085
theorem B1860131 : Blo 1238437 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B3351089 : Blo 1238437 3351089 := bstep (se 2 (by rfl) ⟨1256658, by rfl⟩ : syracuseStep 3351089 = 2513317) B2513317
theorem B1860161 : Blo 1238437 1860161 := bstep (se 2 (by rfl) ⟨697560, by rfl⟩ : syracuseStep 1860161 = 1395121) B1395121
theorem B1860179 : Blo 1238437 1860179 := bstep (se 1 (by rfl) ⟨1395134, by rfl⟩ : syracuseStep 1860179 = 2790269) B2790269
theorem B1860209 : Blo 1238437 1860209 := bstep (se 2 (by rfl) ⟨697578, by rfl⟩ : syracuseStep 1860209 = 1395157) B1395157
theorem B1393267 : Blo 1238437 1393267 := bstep (se 1 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 1393267 = 2089901) B2089901
theorem B2351747 : Blo 1238437 2351747 := bstep (se 1 (by rfl) ⟨1763810, by rfl⟩ : syracuseStep 2351747 = 3527621) B3527621
theorem B1860227 : Blo 1238437 1860227 := bstep (se 1 (by rfl) ⟨1395170, by rfl⟩ : syracuseStep 1860227 = 2790341) B2790341
theorem B7053965 : Blo 1238437 7053965 := bstep (se 3 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 7053965 = 2645237) B2645237
theorem B1860257 : Blo 1238437 1860257 := bstep (se 2 (by rfl) ⟨697596, by rfl⟩ : syracuseStep 1860257 = 1395193) B1395193
theorem B1860275 : Blo 1238437 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B1860305 : Blo 1238437 1860305 := bstep (se 2 (by rfl) ⟨697614, by rfl⟩ : syracuseStep 1860305 = 1395229) B1395229
theorem B1860323 : Blo 1238437 1860323 := bstep (se 1 (by rfl) ⟨1395242, by rfl⟩ : syracuseStep 1860323 = 2790485) B2790485
theorem B4702961 : Blo 1238437 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B1393411 : Blo 1238437 1393411 := bstep (se 1 (by rfl) ⟨1045058, by rfl⟩ : syracuseStep 1393411 = 2090117) B2090117
theorem B1860353 : Blo 1238437 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B1860371 : Blo 1238437 1860371 := bstep (se 1 (by rfl) ⟨1395278, by rfl⟩ : syracuseStep 1860371 = 2790557) B2790557
theorem B2827043 : Blo 1238437 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B1860401 : Blo 1238437 1860401 := bstep (se 2 (by rfl) ⟨697650, by rfl⟩ : syracuseStep 1860401 = 1395301) B1395301
theorem B1860419 : Blo 1238437 1860419 := bstep (se 1 (by rfl) ⟨1395314, by rfl⟩ : syracuseStep 1860419 = 2790629) B2790629
theorem B3138385 : Blo 1238437 3138385 := bstep (se 2 (by rfl) ⟨1176894, by rfl⟩ : syracuseStep 3138385 = 2353789) B2353789
theorem B1860449 : Blo 1238437 1860449 := bstep (se 2 (by rfl) ⟨697668, by rfl⟩ : syracuseStep 1860449 = 1395337) B1395337
theorem B9544547 : Blo 1238437 9544547 := bstep (se 1 (by rfl) ⟨7158410, by rfl⟩ : syracuseStep 9544547 = 14316821) B14316821
theorem B1860467 : Blo 1238437 1860467 := bstep (se 1 (by rfl) ⟨1395350, by rfl⟩ : syracuseStep 1860467 = 2790701) B2790701
theorem B1860497 : Blo 1238437 1860497 := bstep (se 2 (by rfl) ⟨697686, by rfl⟩ : syracuseStep 1860497 = 1395373) B1395373
theorem B1393555 : Blo 1238437 1393555 := bstep (se 1 (by rfl) ⟨1045166, by rfl⟩ : syracuseStep 1393555 = 2090333) B2090333
theorem B1860515 : Blo 1238437 1860515 := bstep (se 1 (by rfl) ⟨1395386, by rfl⟩ : syracuseStep 1860515 = 2790773) B2790773
theorem B2089921 : Blo 1238437 2089921 := bstep (se 2 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 2089921 = 1567441) B1567441
theorem B1860545 : Blo 1238437 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B1860563 : Blo 1238437 1860563 := bstep (se 1 (by rfl) ⟨1395422, by rfl⟩ : syracuseStep 1860563 = 2790845) B2790845
theorem B2089955 : Blo 1238437 2089955 := bstep (se 1 (by rfl) ⟨1567466, by rfl⟩ : syracuseStep 2089955 = 3134933) B3134933
theorem B1860593 : Blo 1238437 1860593 := bstep (se 2 (by rfl) ⟨697722, by rfl⟩ : syracuseStep 1860593 = 1395445) B1395445
theorem B1860611 : Blo 1238437 1860611 := bstep (se 1 (by rfl) ⟨1395458, by rfl⟩ : syracuseStep 1860611 = 2790917) B2790917
theorem B1860641 : Blo 1238437 1860641 := bstep (se 2 (by rfl) ⟨697740, by rfl⟩ : syracuseStep 1860641 = 1395481) B1395481
theorem B1393699 : Blo 1238437 1393699 := bstep (se 1 (by rfl) ⟨1045274, by rfl⟩ : syracuseStep 1393699 = 2090549) B2090549
theorem B2090083 : Blo 1238437 2090083 := bstep (se 1 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 2090083 = 3135125) B3135125
theorem B3138659 : Blo 1238437 3138659 := bstep (se 1 (by rfl) ⟨2353994, by rfl⟩ : syracuseStep 3138659 = 4707989) B4707989
theorem B1721489 : Blo 1238437 1721489 := bstep (se 2 (by rfl) ⟨645558, by rfl⟩ : syracuseStep 1721489 = 1291117) B1291117
theorem B1393843 : Blo 1238437 1393843 := bstep (se 1 (by rfl) ⟨1045382, by rfl⟩ : syracuseStep 1393843 = 2090765) B2090765
theorem B2090225 : Blo 1238437 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B6276365 : Blo 1238437 6276365 := bstep (se 3 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 6276365 = 2353637) B2353637
theorem B2647313 : Blo 1238437 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B5653795 : Blo 1238437 5653795 := bstep (se 1 (by rfl) ⟨4240346, by rfl⟩ : syracuseStep 5653795 = 8480693) B8480693
theorem B3138851 : Blo 1238437 3138851 := bstep (se 1 (by rfl) ⟨2354138, by rfl⟩ : syracuseStep 3138851 = 4708277) B4708277
theorem B1393987 : Blo 1238437 1393987 := bstep (se 1 (by rfl) ⟨1045490, by rfl⟩ : syracuseStep 1393987 = 2090981) B2090981
theorem B1885523 : Blo 1238437 1885523 := bstep (se 1 (by rfl) ⟨1414142, by rfl⟩ : syracuseStep 1885523 = 2828285) B2828285
theorem B1983857 : Blo 1238437 1983857 := bstep (se 2 (by rfl) ⟨743946, by rfl⟩ : syracuseStep 1983857 = 1487893) B1487893
theorem B2090353 : Blo 1238437 2090353 := bstep (se 2 (by rfl) ⟨783882, by rfl⟩ : syracuseStep 2090353 = 1567765) B1567765
theorem B4703629 : Blo 1238437 4703629 := bstep (se 3 (by rfl) ⟨881930, by rfl⟩ : syracuseStep 4703629 = 1763861) B1763861
theorem B2786705 : Blo 1238437 2786705 := bstep (se 2 (by rfl) ⟨1045014, by rfl⟩ : syracuseStep 2786705 = 2090029) B2090029
theorem B2090387 : Blo 1238437 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B2786723 : Blo 1238437 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B1238451 : Blo 1238437 1238451 := bstep (se 1 (by rfl) ⟨928838, by rfl⟩ : syracuseStep 1238451 = 1857677) B1857677
theorem B1238467 : Blo 1238437 1238467 := bstep (se 1 (by rfl) ⟨928850, by rfl⟩ : syracuseStep 1238467 = 1857701) B1857701
theorem B1238483 : Blo 1238437 1238483 := bstep (se 1 (by rfl) ⟨928862, by rfl⟩ : syracuseStep 1238483 = 1857725) B1857725
theorem B1394131 : Blo 1238437 1394131 := bstep (se 1 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 1394131 = 2091197) B2091197
theorem B1238499 : Blo 1238437 1238499 := bstep (se 1 (by rfl) ⟨928874, by rfl⟩ : syracuseStep 1238499 = 1857749) B1857749
theorem B1238515 : Blo 1238437 1238515 := bstep (se 1 (by rfl) ⟨928886, by rfl⟩ : syracuseStep 1238515 = 1857773) B1857773
theorem B1238531 : Blo 1238437 1238531 := bstep (se 1 (by rfl) ⟨928898, by rfl⟩ : syracuseStep 1238531 = 1857797) B1857797
theorem B1238547 : Blo 1238437 1238547 := bstep (se 1 (by rfl) ⟨928910, by rfl⟩ : syracuseStep 1238547 = 1857821) B1857821
theorem B2090515 : Blo 1238437 2090515 := bstep (se 1 (by rfl) ⟨1567886, by rfl⟩ : syracuseStep 2090515 = 3135773) B3135773
theorem B1238563 : Blo 1238437 1238563 := bstep (se 1 (by rfl) ⟨928922, by rfl⟩ : syracuseStep 1238563 = 1857845) B1857845
theorem B7054897 : Blo 1238437 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B1238579 : Blo 1238437 1238579 := bstep (se 1 (by rfl) ⟨928934, by rfl⟩ : syracuseStep 1238579 = 1857869) B1857869
theorem B1238595 : Blo 1238437 1238595 := bstep (se 1 (by rfl) ⟨928946, by rfl⟩ : syracuseStep 1238595 = 1857893) B1857893
theorem B1238611 : Blo 1238437 1238611 := bstep (se 1 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 1238611 = 1857917) B1857917
theorem B1238627 : Blo 1238437 1238627 := bstep (se 1 (by rfl) ⟨928970, by rfl⟩ : syracuseStep 1238627 = 1857941) B1857941
theorem B1394275 : Blo 1238437 1394275 := bstep (se 1 (by rfl) ⟨1045706, by rfl⟩ : syracuseStep 1394275 = 2091413) B2091413
theorem B1238643 : Blo 1238437 1238643 := bstep (se 1 (by rfl) ⟨928982, by rfl⟩ : syracuseStep 1238643 = 1857965) B1857965
theorem B1238659 : Blo 1238437 1238659 := bstep (se 1 (by rfl) ⟨928994, by rfl⟩ : syracuseStep 1238659 = 1857989) B1857989
theorem B3352205 : Blo 1238437 3352205 := bstep (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) B1257077
theorem B1238675 : Blo 1238437 1238675 := bstep (se 1 (by rfl) ⟨929006, by rfl⟩ : syracuseStep 1238675 = 1858013) B1858013
theorem B2090657 : Blo 1238437 2090657 := bstep (se 2 (by rfl) ⟨783996, by rfl⟩ : syracuseStep 2090657 = 1567993) B1567993
theorem B1238691 : Blo 1238437 1238691 := bstep (se 1 (by rfl) ⟨929018, by rfl⟩ : syracuseStep 1238691 = 1858037) B1858037
theorem B1885859 : Blo 1238437 1885859 := bstep (se 1 (by rfl) ⟨1414394, by rfl⟩ : syracuseStep 1885859 = 2828789) B2828789
theorem B2786993 : Blo 1238437 2786993 := bstep (se 2 (by rfl) ⟨1045122, by rfl⟩ : syracuseStep 2786993 = 2090245) B2090245
theorem B2352817 : Blo 1238437 2352817 := bstep (se 2 (by rfl) ⟨882306, by rfl⟩ : syracuseStep 2352817 = 1764613) B1764613
theorem B1238707 : Blo 1238437 1238707 := bstep (se 1 (by rfl) ⟨929030, by rfl⟩ : syracuseStep 1238707 = 1858061) B1858061
theorem B2787011 : Blo 1238437 2787011 := bstep (se 1 (by rfl) ⟨2090258, by rfl⟩ : syracuseStep 2787011 = 4180517) B4180517
theorem B1238723 : Blo 1238437 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1238739 : Blo 1238437 1238739 := bstep (se 1 (by rfl) ⟨929054, by rfl⟩ : syracuseStep 1238739 = 1858109) B1858109
theorem B1885907 : Blo 1238437 1885907 := bstep (se 1 (by rfl) ⟨1414430, by rfl⟩ : syracuseStep 1885907 = 2828861) B2828861
theorem B1238755 : Blo 1238437 1238755 := bstep (se 1 (by rfl) ⟨929066, by rfl⟩ : syracuseStep 1238755 = 1858133) B1858133
theorem B1238771 : Blo 1238437 1238771 := bstep (se 1 (by rfl) ⟨929078, by rfl⟩ : syracuseStep 1238771 = 1858157) B1858157
theorem B1394419 : Blo 1238437 1394419 := bstep (se 1 (by rfl) ⟨1045814, by rfl⟩ : syracuseStep 1394419 = 2091629) B2091629
theorem B1238787 : Blo 1238437 1238787 := bstep (se 1 (by rfl) ⟨929090, by rfl⟩ : syracuseStep 1238787 = 1858181) B1858181
theorem B3180305 : Blo 1238437 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B1238803 : Blo 1238437 1238803 := bstep (se 1 (by rfl) ⟨929102, by rfl⟩ : syracuseStep 1238803 = 1858205) B1858205
theorem B2090785 : Blo 1238437 2090785 := bstep (se 2 (by rfl) ⟨784044, by rfl⟩ : syracuseStep 2090785 = 1568089) B1568089
theorem B1238819 : Blo 1238437 1238819 := bstep (se 1 (by rfl) ⟨929114, by rfl⟩ : syracuseStep 1238819 = 1858229) B1858229
theorem B4179761 : Blo 1238437 4179761 := bstep (se 2 (by rfl) ⟨1567410, by rfl⟩ : syracuseStep 4179761 = 3134821) B3134821
theorem B7939889 : Blo 1238437 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B1238835 : Blo 1238437 1238835 := bstep (se 1 (by rfl) ⟨929126, by rfl⟩ : syracuseStep 1238835 = 1858253) B1858253
theorem B1238851 : Blo 1238437 1238851 := bstep (se 1 (by rfl) ⟨929138, by rfl⟩ : syracuseStep 1238851 = 1858277) B1858277
theorem B2090819 : Blo 1238437 2090819 := bstep (se 1 (by rfl) ⟨1568114, by rfl⟩ : syracuseStep 2090819 = 3136229) B3136229
theorem B1238867 : Blo 1238437 1238867 := bstep (se 1 (by rfl) ⟨929150, by rfl⟩ : syracuseStep 1238867 = 1858301) B1858301
theorem B1238883 : Blo 1238437 1238883 := bstep (se 1 (by rfl) ⟨929162, by rfl⟩ : syracuseStep 1238883 = 1858325) B1858325
theorem B1238899 : Blo 1238437 1238899 := bstep (se 1 (by rfl) ⟨929174, by rfl⟩ : syracuseStep 1238899 = 1858349) B1858349
theorem B1238915 : Blo 1238437 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B1394563 : Blo 1238437 1394563 := bstep (se 1 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 1394563 = 2091845) B2091845
theorem B1238931 : Blo 1238437 1238931 := bstep (se 1 (by rfl) ⟨929198, by rfl⟩ : syracuseStep 1238931 = 1858397) B1858397
theorem B5728163 : Blo 1238437 5728163 := bstep (se 1 (by rfl) ⟨4296122, by rfl⟩ : syracuseStep 5728163 = 8592245) B8592245
theorem B1238947 : Blo 1238437 1238947 := bstep (se 1 (by rfl) ⟨929210, by rfl⟩ : syracuseStep 1238947 = 1858421) B1858421
theorem B1238963 : Blo 1238437 1238963 := bstep (se 1 (by rfl) ⟨929222, by rfl⟩ : syracuseStep 1238963 = 1858445) B1858445
theorem B1238979 : Blo 1238437 1238979 := bstep (se 1 (by rfl) ⟨929234, by rfl⟩ : syracuseStep 1238979 = 1858469) B1858469
theorem B2090947 : Blo 1238437 2090947 := bstep (se 1 (by rfl) ⟨1568210, by rfl⟩ : syracuseStep 2090947 = 3136421) B3136421
theorem B2787281 : Blo 1238437 2787281 := bstep (se 2 (by rfl) ⟨1045230, by rfl⟩ : syracuseStep 2787281 = 2090461) B2090461
theorem B1238995 : Blo 1238437 1238995 := bstep (se 1 (by rfl) ⟨929246, by rfl⟩ : syracuseStep 1238995 = 1858493) B1858493
theorem B2787299 : Blo 1238437 2787299 := bstep (se 1 (by rfl) ⟨2090474, by rfl⟩ : syracuseStep 2787299 = 4180949) B4180949
theorem B1239011 : Blo 1238437 1239011 := bstep (se 1 (by rfl) ⟨929258, by rfl⟩ : syracuseStep 1239011 = 1858517) B1858517
theorem B1239027 : Blo 1238437 1239027 := bstep (se 1 (by rfl) ⟨929270, by rfl⟩ : syracuseStep 1239027 = 1858541) B1858541
theorem B1239043 : Blo 1238437 1239043 := bstep (se 1 (by rfl) ⟨929282, by rfl⟩ : syracuseStep 1239043 = 1858565) B1858565
theorem B1239059 : Blo 1238437 1239059 := bstep (se 1 (by rfl) ⟨929294, by rfl⟩ : syracuseStep 1239059 = 1858589) B1858589
theorem B1394707 : Blo 1238437 1394707 := bstep (se 1 (by rfl) ⟨1046030, by rfl⟩ : syracuseStep 1394707 = 2092061) B2092061
theorem B1239075 : Blo 1238437 1239075 := bstep (se 1 (by rfl) ⟨929306, by rfl⟩ : syracuseStep 1239075 = 1858613) B1858613
theorem B1239091 : Blo 1238437 1239091 := bstep (se 1 (by rfl) ⟨929318, by rfl⟩ : syracuseStep 1239091 = 1858637) B1858637
theorem B1239107 : Blo 1238437 1239107 := bstep (se 1 (by rfl) ⟨929330, by rfl⟩ : syracuseStep 1239107 = 1858661) B1858661
theorem B4466765 : Blo 1238437 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B2091089 : Blo 1238437 2091089 := bstep (se 2 (by rfl) ⟨784158, by rfl⟩ : syracuseStep 2091089 = 1568317) B1568317
theorem B1239123 : Blo 1238437 1239123 := bstep (se 1 (by rfl) ⟨929342, by rfl⟩ : syracuseStep 1239123 = 1858685) B1858685
theorem B1239139 : Blo 1238437 1239139 := bstep (se 1 (by rfl) ⟨929354, by rfl⟩ : syracuseStep 1239139 = 1858709) B1858709
theorem B1239155 : Blo 1238437 1239155 := bstep (se 1 (by rfl) ⟨929366, by rfl⟩ : syracuseStep 1239155 = 1858733) B1858733
theorem B1239171 : Blo 1238437 1239171 := bstep (se 1 (by rfl) ⟨929378, by rfl⟩ : syracuseStep 1239171 = 1858757) B1858757
theorem B1239187 : Blo 1238437 1239187 := bstep (se 1 (by rfl) ⟨929390, by rfl⟩ : syracuseStep 1239187 = 1858781) B1858781
theorem B4704419 : Blo 1238437 4704419 := bstep (se 1 (by rfl) ⟨3528314, by rfl⟩ : syracuseStep 4704419 = 7056629) B7056629
theorem B1239203 : Blo 1238437 1239203 := bstep (se 1 (by rfl) ⟨929402, by rfl⟩ : syracuseStep 1239203 = 1858805) B1858805
theorem B1394851 : Blo 1238437 1394851 := bstep (se 1 (by rfl) ⟨1046138, by rfl⟩ : syracuseStep 1394851 = 2092277) B2092277
theorem B1239219 : Blo 1238437 1239219 := bstep (se 1 (by rfl) ⟨929414, by rfl⟩ : syracuseStep 1239219 = 1858829) B1858829
theorem B1239235 : Blo 1238437 1239235 := bstep (se 1 (by rfl) ⟨929426, by rfl⟩ : syracuseStep 1239235 = 1858853) B1858853
theorem B2091217 : Blo 1238437 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B3139793 : Blo 1238437 3139793 := bstep (se 2 (by rfl) ⟨1177422, by rfl⟩ : syracuseStep 3139793 = 2354845) B2354845
theorem B1239251 : Blo 1238437 1239251 := bstep (se 1 (by rfl) ⟨929438, by rfl⟩ : syracuseStep 1239251 = 1858877) B1858877
theorem B1239267 : Blo 1238437 1239267 := bstep (se 1 (by rfl) ⟨929450, by rfl⟩ : syracuseStep 1239267 = 1858901) B1858901
theorem B2787569 : Blo 1238437 2787569 := bstep (se 2 (by rfl) ⟨1045338, by rfl⟩ : syracuseStep 2787569 = 2090677) B2090677
theorem B2091251 : Blo 1238437 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B1239283 : Blo 1238437 1239283 := bstep (se 1 (by rfl) ⟨929462, by rfl⟩ : syracuseStep 1239283 = 1858925) B1858925
theorem B2787587 : Blo 1238437 2787587 := bstep (se 1 (by rfl) ⟨2090690, by rfl⟩ : syracuseStep 2787587 = 4181381) B4181381
theorem B1239299 : Blo 1238437 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B3139843 : Blo 1238437 3139843 := bstep (se 1 (by rfl) ⟨2354882, by rfl⟩ : syracuseStep 3139843 = 4709765) B4709765
theorem B1239315 : Blo 1238437 1239315 := bstep (se 1 (by rfl) ⟨929486, by rfl⟩ : syracuseStep 1239315 = 1858973) B1858973
theorem B1239331 : Blo 1238437 1239331 := bstep (se 1 (by rfl) ⟨929498, by rfl⟩ : syracuseStep 1239331 = 1858997) B1858997
theorem B1984819 : Blo 1238437 1984819 := bstep (se 1 (by rfl) ⟨1488614, by rfl⟩ : syracuseStep 1984819 = 2977229) B2977229
theorem B1239347 : Blo 1238437 1239347 := bstep (se 1 (by rfl) ⟨929510, by rfl⟩ : syracuseStep 1239347 = 1859021) B1859021
theorem B1394995 : Blo 1238437 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B1239363 : Blo 1238437 1239363 := bstep (se 1 (by rfl) ⟨929522, by rfl⟩ : syracuseStep 1239363 = 1859045) B1859045
theorem B4180301 : Blo 1238437 4180301 := bstep (se 3 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 4180301 = 1567613) B1567613
theorem B7940429 : Blo 1238437 7940429 := bstep (se 3 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 7940429 = 2977661) B2977661
theorem B1239379 : Blo 1238437 1239379 := bstep (se 1 (by rfl) ⟨929534, by rfl⟩ : syracuseStep 1239379 = 1859069) B1859069
theorem B1509715 : Blo 1238437 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1239395 : Blo 1238437 1239395 := bstep (se 1 (by rfl) ⟨929546, by rfl⟩ : syracuseStep 1239395 = 1859093) B1859093
theorem B2754929 : Blo 1238437 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B2091379 : Blo 1238437 2091379 := bstep (se 1 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 2091379 = 3137069) B3137069
theorem B1239411 : Blo 1238437 1239411 := bstep (se 1 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 1239411 = 1859117) B1859117
theorem B4180355 : Blo 1238437 4180355 := bstep (se 1 (by rfl) ⟨3135266, by rfl⟩ : syracuseStep 4180355 = 6270533) B6270533
theorem B1239427 : Blo 1238437 1239427 := bstep (se 1 (by rfl) ⟨929570, by rfl⟩ : syracuseStep 1239427 = 1859141) B1859141
theorem B1239443 : Blo 1238437 1239443 := bstep (se 1 (by rfl) ⟨929582, by rfl⟩ : syracuseStep 1239443 = 1859165) B1859165
theorem B1239459 : Blo 1238437 1239459 := bstep (se 1 (by rfl) ⟨929594, by rfl⟩ : syracuseStep 1239459 = 1859189) B1859189
theorem B1239475 : Blo 1238437 1239475 := bstep (se 1 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 1239475 = 1859213) B1859213
theorem B1239491 : Blo 1238437 1239491 := bstep (se 1 (by rfl) ⟨929618, by rfl⟩ : syracuseStep 1239491 = 1859237) B1859237
theorem B1395139 : Blo 1238437 1395139 := bstep (se 1 (by rfl) ⟨1046354, by rfl⟩ : syracuseStep 1395139 = 2092709) B2092709
theorem B1239507 : Blo 1238437 1239507 := bstep (se 1 (by rfl) ⟨929630, by rfl⟩ : syracuseStep 1239507 = 1859261) B1859261
theorem B1239523 : Blo 1238437 1239523 := bstep (se 1 (by rfl) ⟨929642, by rfl⟩ : syracuseStep 1239523 = 1859285) B1859285
theorem B1239539 : Blo 1238437 1239539 := bstep (se 1 (by rfl) ⟨929654, by rfl⟩ : syracuseStep 1239539 = 1859309) B1859309
theorem B2091521 : Blo 1238437 2091521 := bstep (se 2 (by rfl) ⟨784320, by rfl⟩ : syracuseStep 2091521 = 1568641) B1568641
theorem B1239555 : Blo 1238437 1239555 := bstep (se 1 (by rfl) ⟨929666, by rfl⟩ : syracuseStep 1239555 = 1859333) B1859333
theorem B2787857 : Blo 1238437 2787857 := bstep (se 2 (by rfl) ⟨1045446, by rfl⟩ : syracuseStep 2787857 = 2090893) B2090893
theorem B1239571 : Blo 1238437 1239571 := bstep (se 1 (by rfl) ⟨929678, by rfl⟩ : syracuseStep 1239571 = 1859357) B1859357
theorem B4237859 : Blo 1238437 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B2787875 : Blo 1238437 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B1239587 : Blo 1238437 1239587 := bstep (se 1 (by rfl) ⟨929690, by rfl⟩ : syracuseStep 1239587 = 1859381) B1859381
theorem B1985075 : Blo 1238437 1985075 := bstep (se 1 (by rfl) ⟨1488806, by rfl⟩ : syracuseStep 1985075 = 2977613) B2977613
theorem B1239603 : Blo 1238437 1239603 := bstep (se 1 (by rfl) ⟨929702, by rfl⟩ : syracuseStep 1239603 = 1859405) B1859405
theorem B1788481 : Blo 1238437 1788481 := bstep (se 2 (by rfl) ⟨670680, by rfl⟩ : syracuseStep 1788481 = 1341361) B1341361
theorem B1239619 : Blo 1238437 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1239635 : Blo 1238437 1239635 := bstep (se 1 (by rfl) ⟨929726, by rfl⟩ : syracuseStep 1239635 = 1859453) B1859453
theorem B1395283 : Blo 1238437 1395283 := bstep (se 1 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 1395283 = 2092925) B2092925
theorem B1239651 : Blo 1238437 1239651 := bstep (se 1 (by rfl) ⟨929738, by rfl⟩ : syracuseStep 1239651 = 1859477) B1859477
theorem B1239667 : Blo 1238437 1239667 := bstep (se 1 (by rfl) ⟨929750, by rfl⟩ : syracuseStep 1239667 = 1859501) B1859501
theorem B2091649 : Blo 1238437 2091649 := bstep (se 2 (by rfl) ⟨784368, by rfl⟩ : syracuseStep 2091649 = 1568737) B1568737
theorem B1239683 : Blo 1238437 1239683 := bstep (se 1 (by rfl) ⟨929762, by rfl⟩ : syracuseStep 1239683 = 1859525) B1859525
theorem B4180625 : Blo 1238437 4180625 := bstep (se 2 (by rfl) ⟨1567734, by rfl⟩ : syracuseStep 4180625 = 3135469) B3135469
theorem B2976401 : Blo 1238437 2976401 := bstep (se 2 (by rfl) ⟨1116150, by rfl⟩ : syracuseStep 2976401 = 2232301) B2232301
theorem B1239699 : Blo 1238437 1239699 := bstep (se 1 (by rfl) ⟨929774, by rfl⟩ : syracuseStep 1239699 = 1859549) B1859549
theorem B2091683 : Blo 1238437 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B1239715 : Blo 1238437 1239715 := bstep (se 1 (by rfl) ⟨929786, by rfl⟩ : syracuseStep 1239715 = 1859573) B1859573
theorem B1239731 : Blo 1238437 1239731 := bstep (se 1 (by rfl) ⟨929798, by rfl⟩ : syracuseStep 1239731 = 1859597) B1859597
theorem B1239747 : Blo 1238437 1239747 := bstep (se 1 (by rfl) ⟨929810, by rfl⟩ : syracuseStep 1239747 = 1859621) B1859621
theorem B2353873 : Blo 1238437 2353873 := bstep (se 2 (by rfl) ⟨882702, by rfl⟩ : syracuseStep 2353873 = 1765405) B1765405
theorem B1239763 : Blo 1238437 1239763 := bstep (se 1 (by rfl) ⟨929822, by rfl⟩ : syracuseStep 1239763 = 1859645) B1859645
theorem B67840739 : Blo 1238437 67840739 := bstep (se 1 (by rfl) ⟨50880554, by rfl⟩ : syracuseStep 67840739 = 101761109) B101761109
theorem B1239779 : Blo 1238437 1239779 := bstep (se 1 (by rfl) ⟨929834, by rfl⟩ : syracuseStep 1239779 = 1859669) B1859669
theorem B1395427 : Blo 1238437 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B1239795 : Blo 1238437 1239795 := bstep (se 1 (by rfl) ⟨929846, by rfl⟩ : syracuseStep 1239795 = 1859693) B1859693
theorem B1239811 : Blo 1238437 1239811 := bstep (se 1 (by rfl) ⟨929858, by rfl⟩ : syracuseStep 1239811 = 1859717) B1859717
theorem B1567507 : Blo 1238437 1567507 := bstep (se 1 (by rfl) ⟨1175630, by rfl⟩ : syracuseStep 1567507 = 2351261) B2351261
theorem B1239827 : Blo 1238437 1239827 := bstep (se 1 (by rfl) ⟨929870, by rfl⟩ : syracuseStep 1239827 = 1859741) B1859741
theorem B2091811 : Blo 1238437 2091811 := bstep (se 1 (by rfl) ⟨1568858, by rfl⟩ : syracuseStep 2091811 = 3137717) B3137717
theorem B1239843 : Blo 1238437 1239843 := bstep (se 1 (by rfl) ⟨929882, by rfl⟩ : syracuseStep 1239843 = 1859765) B1859765
theorem B2648867 : Blo 1238437 2648867 := bstep (se 1 (by rfl) ⟨1986650, by rfl⟩ : syracuseStep 2648867 = 3973301) B3973301
theorem B2788145 : Blo 1238437 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B4705073 : Blo 1238437 4705073 := bstep (se 2 (by rfl) ⟨1764402, by rfl⟩ : syracuseStep 4705073 = 3528805) B3528805
theorem B1239859 : Blo 1238437 1239859 := bstep (se 1 (by rfl) ⟨929894, by rfl⟩ : syracuseStep 1239859 = 1859789) B1859789
theorem B2788163 : Blo 1238437 2788163 := bstep (se 1 (by rfl) ⟨2091122, by rfl⟩ : syracuseStep 2788163 = 4182245) B4182245
theorem B1239875 : Blo 1238437 1239875 := bstep (se 1 (by rfl) ⟨929906, by rfl⟩ : syracuseStep 1239875 = 1859813) B1859813
theorem B1510211 : Blo 1238437 1510211 := bstep (se 1 (by rfl) ⟨1132658, by rfl⟩ : syracuseStep 1510211 = 2265317) B2265317
theorem B1239891 : Blo 1238437 1239891 := bstep (se 1 (by rfl) ⟨929918, by rfl⟩ : syracuseStep 1239891 = 1859837) B1859837
theorem B1239907 : Blo 1238437 1239907 := bstep (se 1 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 1239907 = 1859861) B1859861
theorem B1567603 : Blo 1238437 1567603 := bstep (se 1 (by rfl) ⟨1175702, by rfl⟩ : syracuseStep 1567603 = 2351405) B2351405
theorem B1239923 : Blo 1238437 1239923 := bstep (se 1 (by rfl) ⟨929942, by rfl⟩ : syracuseStep 1239923 = 1859885) B1859885
theorem B1239939 : Blo 1238437 1239939 := bstep (se 1 (by rfl) ⟨929954, by rfl⟩ : syracuseStep 1239939 = 1859909) B1859909
theorem B1239955 : Blo 1238437 1239955 := bstep (se 1 (by rfl) ⟨929966, by rfl⟩ : syracuseStep 1239955 = 1859933) B1859933
theorem B1239971 : Blo 1238437 1239971 := bstep (se 1 (by rfl) ⟨929978, by rfl⟩ : syracuseStep 1239971 = 1859957) B1859957
theorem B2091953 : Blo 1238437 2091953 := bstep (se 2 (by rfl) ⟨784482, by rfl⟩ : syracuseStep 2091953 = 1568965) B1568965
theorem B1239987 : Blo 1238437 1239987 := bstep (se 1 (by rfl) ⟨929990, by rfl⟩ : syracuseStep 1239987 = 1859981) B1859981
theorem B14117813 : Blo 1238437 14117813 := bstep (se 5 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 14117813 = 1323545) B1323545
theorem B1240003 : Blo 1238437 1240003 := bstep (se 1 (by rfl) ⟨930002, by rfl⟩ : syracuseStep 1240003 = 1860005) B1860005
theorem B1240019 : Blo 1238437 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B7056355 : Blo 1238437 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B1240035 : Blo 1238437 1240035 := bstep (se 1 (by rfl) ⟨930026, by rfl⟩ : syracuseStep 1240035 = 1860053) B1860053
theorem B1240051 : Blo 1238437 1240051 := bstep (se 1 (by rfl) ⟨930038, by rfl⟩ : syracuseStep 1240051 = 1860077) B1860077
theorem B1240067 : Blo 1238437 1240067 := bstep (se 1 (by rfl) ⟨930050, by rfl⟩ : syracuseStep 1240067 = 1860101) B1860101
theorem B9407501 : Blo 1238437 9407501 := bstep (se 3 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 9407501 = 3527813) B3527813
theorem B1240083 : Blo 1238437 1240083 := bstep (se 1 (by rfl) ⟨930062, by rfl⟩ : syracuseStep 1240083 = 1860125) B1860125
theorem B1240099 : Blo 1238437 1240099 := bstep (se 1 (by rfl) ⟨930074, by rfl⟩ : syracuseStep 1240099 = 1860149) B1860149
theorem B4467761 : Blo 1238437 4467761 := bstep (se 2 (by rfl) ⟨1675410, by rfl⟩ : syracuseStep 4467761 = 3350821) B3350821
theorem B2092081 : Blo 1238437 2092081 := bstep (se 2 (by rfl) ⟨784530, by rfl⟩ : syracuseStep 2092081 = 1569061) B1569061
theorem B1240115 : Blo 1238437 1240115 := bstep (se 1 (by rfl) ⟨930086, by rfl⟩ : syracuseStep 1240115 = 1860173) B1860173
theorem B1240131 : Blo 1238437 1240131 := bstep (se 1 (by rfl) ⟨930098, by rfl⟩ : syracuseStep 1240131 = 1860197) B1860197
theorem B2788433 : Blo 1238437 2788433 := bstep (se 2 (by rfl) ⟨1045662, by rfl⟩ : syracuseStep 2788433 = 2091325) B2091325
theorem B2092115 : Blo 1238437 2092115 := bstep (se 1 (by rfl) ⟨1569086, by rfl⟩ : syracuseStep 2092115 = 3138173) B3138173
theorem B1240147 : Blo 1238437 1240147 := bstep (se 1 (by rfl) ⟨930110, by rfl⟩ : syracuseStep 1240147 = 1860221) B1860221
theorem B3968099 : Blo 1238437 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2788451 : Blo 1238437 2788451 := bstep (se 1 (by rfl) ⟨2091338, by rfl⟩ : syracuseStep 2788451 = 4182677) B4182677
theorem B2354275 : Blo 1238437 2354275 := bstep (se 1 (by rfl) ⟨1765706, by rfl⟩ : syracuseStep 2354275 = 3531413) B3531413
theorem B1240163 : Blo 1238437 1240163 := bstep (se 1 (by rfl) ⟨930122, by rfl⟩ : syracuseStep 1240163 = 1860245) B1860245
theorem B1240179 : Blo 1238437 1240179 := bstep (se 1 (by rfl) ⟨930134, by rfl⟩ : syracuseStep 1240179 = 1860269) B1860269
theorem B1240195 : Blo 1238437 1240195 := bstep (se 1 (by rfl) ⟨930146, by rfl⟩ : syracuseStep 1240195 = 1860293) B1860293
theorem B2354321 : Blo 1238437 2354321 := bstep (se 2 (by rfl) ⟨882870, by rfl⟩ : syracuseStep 2354321 = 1765741) B1765741
theorem B1764499 : Blo 1238437 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1240211 : Blo 1238437 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B1240227 : Blo 1238437 1240227 := bstep (se 1 (by rfl) ⟨930170, by rfl⟩ : syracuseStep 1240227 = 1860341) B1860341
theorem B4181165 : Blo 1238437 4181165 := bstep (se 3 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 4181165 = 1567937) B1567937
theorem B1240243 : Blo 1238437 1240243 := bstep (se 1 (by rfl) ⟨930182, by rfl⟩ : syracuseStep 1240243 = 1860365) B1860365
theorem B1240259 : Blo 1238437 1240259 := bstep (se 1 (by rfl) ⟨930194, by rfl⟩ : syracuseStep 1240259 = 1860389) B1860389
theorem B8473805 : Blo 1238437 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B2092243 : Blo 1238437 2092243 := bstep (se 1 (by rfl) ⟨1569182, by rfl⟩ : syracuseStep 2092243 = 3138365) B3138365
theorem B1240275 : Blo 1238437 1240275 := bstep (se 1 (by rfl) ⟨930206, by rfl⟩ : syracuseStep 1240275 = 1860413) B1860413
theorem B4181219 : Blo 1238437 4181219 := bstep (se 1 (by rfl) ⟨3135914, by rfl⟩ : syracuseStep 4181219 = 6271829) B6271829
theorem B1240291 : Blo 1238437 1240291 := bstep (se 1 (by rfl) ⟨930218, by rfl⟩ : syracuseStep 1240291 = 1860437) B1860437
theorem B1985779 : Blo 1238437 1985779 := bstep (se 1 (by rfl) ⟨1489334, by rfl⟩ : syracuseStep 1985779 = 2978669) B2978669
theorem B1240307 : Blo 1238437 1240307 := bstep (se 1 (by rfl) ⟨930230, by rfl⟩ : syracuseStep 1240307 = 1860461) B1860461
theorem B1240323 : Blo 1238437 1240323 := bstep (se 1 (by rfl) ⟨930242, by rfl⟩ : syracuseStep 1240323 = 1860485) B1860485
theorem B1240339 : Blo 1238437 1240339 := bstep (se 1 (by rfl) ⟨930254, by rfl⟩ : syracuseStep 1240339 = 1860509) B1860509
theorem B5295395 : Blo 1238437 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B1240355 : Blo 1238437 1240355 := bstep (se 1 (by rfl) ⟨930266, by rfl⟩ : syracuseStep 1240355 = 1860533) B1860533
theorem B1240371 : Blo 1238437 1240371 := bstep (se 1 (by rfl) ⟨930278, by rfl⟩ : syracuseStep 1240371 = 1860557) B1860557
theorem B1240387 : Blo 1238437 1240387 := bstep (se 1 (by rfl) ⟨930290, by rfl⟩ : syracuseStep 1240387 = 1860581) B1860581
theorem B2149715 : Blo 1238437 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B1240403 : Blo 1238437 1240403 := bstep (se 1 (by rfl) ⟨930302, by rfl⟩ : syracuseStep 1240403 = 1860605) B1860605
theorem B2092385 : Blo 1238437 2092385 := bstep (se 2 (by rfl) ⟨784644, by rfl⟩ : syracuseStep 2092385 = 1569289) B1569289
theorem B1568099 : Blo 1238437 1568099 := bstep (se 1 (by rfl) ⟨1176074, by rfl⟩ : syracuseStep 1568099 = 2352149) B2352149
theorem B1240419 : Blo 1238437 1240419 := bstep (se 1 (by rfl) ⟨930314, by rfl⟩ : syracuseStep 1240419 = 1860629) B1860629
theorem B2788721 : Blo 1238437 2788721 := bstep (se 2 (by rfl) ⟨1045770, by rfl⟩ : syracuseStep 2788721 = 2091541) B2091541
theorem B1240435 : Blo 1238437 1240435 := bstep (se 1 (by rfl) ⟨930326, by rfl⟩ : syracuseStep 1240435 = 1860653) B1860653
theorem B2788739 : Blo 1238437 2788739 := bstep (se 1 (by rfl) ⟨2091554, by rfl⟩ : syracuseStep 2788739 = 4183109) B4183109
theorem B6270371 : Blo 1238437 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B2354609 : Blo 1238437 2354609 := bstep (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) B1765957
theorem B2092513 : Blo 1238437 2092513 := bstep (se 2 (by rfl) ⟨784692, by rfl⟩ : syracuseStep 2092513 = 1569385) B1569385
theorem B4181489 : Blo 1238437 4181489 := bstep (se 2 (by rfl) ⟨1568058, by rfl⟩ : syracuseStep 4181489 = 3136117) B3136117
theorem B7056881 : Blo 1238437 7056881 := bstep (se 2 (by rfl) ⟨2646330, by rfl⟩ : syracuseStep 7056881 = 5292661) B5292661
theorem B1986049 : Blo 1238437 1986049 := bstep (se 2 (by rfl) ⟨744768, by rfl⟩ : syracuseStep 1986049 = 1489537) B1489537
theorem B2092547 : Blo 1238437 2092547 := bstep (se 1 (by rfl) ⟨1569410, by rfl⟩ : syracuseStep 2092547 = 3138821) B3138821
theorem B1986113 : Blo 1238437 1986113 := bstep (se 2 (by rfl) ⟨744792, by rfl⟩ : syracuseStep 1986113 = 1489585) B1489585
theorem B1322563 : Blo 1238437 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B4836977 : Blo 1238437 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B2092675 : Blo 1238437 2092675 := bstep (se 1 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 2092675 = 3139013) B3139013
theorem B2789009 : Blo 1238437 2789009 := bstep (se 2 (by rfl) ⟨1045878, by rfl⟩ : syracuseStep 2789009 = 2091757) B2091757
theorem B2789027 : Blo 1238437 2789027 := bstep (se 1 (by rfl) ⟨2091770, by rfl⟩ : syracuseStep 2789027 = 4183541) B4183541
theorem B26783459 : Blo 1238437 26783459 := bstep (se 1 (by rfl) ⟨20087594, by rfl⟩ : syracuseStep 26783459 = 40175189) B40175189
theorem B4468451 : Blo 1238437 4468451 := bstep (se 1 (by rfl) ⟨3351338, by rfl⟩ : syracuseStep 4468451 = 6702677) B6702677
theorem B2092817 : Blo 1238437 2092817 := bstep (se 2 (by rfl) ⟨784806, by rfl⟩ : syracuseStep 2092817 = 1569613) B1569613
theorem B2092945 : Blo 1238437 2092945 := bstep (se 2 (by rfl) ⟨784854, by rfl⟩ : syracuseStep 2092945 = 1569709) B1569709
theorem B3968945 : Blo 1238437 3968945 := bstep (se 2 (by rfl) ⟨1488354, by rfl⟩ : syracuseStep 3968945 = 2976709) B2976709
theorem B2789297 : Blo 1238437 2789297 := bstep (se 2 (by rfl) ⟨1045986, by rfl⟩ : syracuseStep 2789297 = 2091973) B2091973
theorem B2092979 : Blo 1238437 2092979 := bstep (se 1 (by rfl) ⟨1569734, by rfl⟩ : syracuseStep 2092979 = 3139469) B3139469
theorem B2789315 : Blo 1238437 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B13397957 : Blo 1238437 13397957 := bstep (se 4 (by rfl) ⟨1256058, by rfl⟩ : syracuseStep 13397957 = 2512117) B2512117
theorem B3968995 : Blo 1238437 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B4182029 : Blo 1238437 4182029 := bstep (se 3 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 4182029 = 1568261) B1568261
theorem B3575843 : Blo 1238437 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B1568803 : Blo 1238437 1568803 := bstep (se 1 (by rfl) ⟨1176602, by rfl⟩ : syracuseStep 1568803 = 2353205) B2353205
theorem B2093107 : Blo 1238437 2093107 := bstep (se 1 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 2093107 = 3139661) B3139661
theorem B4182083 : Blo 1238437 4182083 := bstep (se 1 (by rfl) ⟨3136562, by rfl⟩ : syracuseStep 4182083 = 6273125) B6273125
theorem B6279281 : Blo 1238437 6279281 := bstep (se 2 (by rfl) ⟨2354730, by rfl⟩ : syracuseStep 6279281 = 4709461) B4709461
theorem B1568899 : Blo 1238437 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B2232497 : Blo 1238437 2232497 := bstep (se 2 (by rfl) ⟨837186, by rfl⟩ : syracuseStep 2232497 = 1674373) B1674373
theorem B6271181 : Blo 1238437 6271181 := bstep (se 3 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 6271181 = 2351693) B2351693
theorem B2789585 : Blo 1238437 2789585 := bstep (se 2 (by rfl) ⟨1046094, by rfl⟩ : syracuseStep 2789585 = 2092189) B2092189
theorem B4706531 : Blo 1238437 4706531 := bstep (se 1 (by rfl) ⟨3529898, by rfl⟩ : syracuseStep 4706531 = 7059797) B7059797
theorem B2789603 : Blo 1238437 2789603 := bstep (se 1 (by rfl) ⟨2092202, by rfl⟩ : syracuseStep 2789603 = 4184405) B4184405
theorem B4706545 : Blo 1238437 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B1765633 : Blo 1238437 1765633 := bstep (se 2 (by rfl) ⟨662112, by rfl⟩ : syracuseStep 1765633 = 1324225) B1324225
theorem B4469041 : Blo 1238437 4469041 := bstep (se 2 (by rfl) ⟨1675890, by rfl⟩ : syracuseStep 4469041 = 3351781) B3351781
theorem B8163661 : Blo 1238437 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B3526993 : Blo 1238437 3526993 := bstep (se 2 (by rfl) ⟨1322622, by rfl⟩ : syracuseStep 3526993 = 2645245) B2645245
theorem B4182353 : Blo 1238437 4182353 := bstep (se 2 (by rfl) ⟨1568382, by rfl⟩ : syracuseStep 4182353 = 3136765) B3136765
theorem B1765729 : Blo 1238437 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B2232785 : Blo 1238437 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B2789873 : Blo 1238437 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B2789891 : Blo 1238437 2789891 := bstep (se 1 (by rfl) ⟨2092418, by rfl⟩ : syracuseStep 2789891 = 4184837) B4184837
theorem B1413715 : Blo 1238437 1413715 := bstep (se 1 (by rfl) ⟨1060286, by rfl⟩ : syracuseStep 1413715 = 2120573) B2120573
theorem B1569395 : Blo 1238437 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B2790161 : Blo 1238437 2790161 := bstep (se 2 (by rfl) ⟨1046310, by rfl⟩ : syracuseStep 2790161 = 2092621) B2092621
theorem B2790179 : Blo 1238437 2790179 := bstep (se 1 (by rfl) ⟨2092634, by rfl⟩ : syracuseStep 2790179 = 4185269) B4185269
theorem B4182893 : Blo 1238437 4182893 := bstep (se 3 (by rfl) ⟨784292, by rfl⟩ : syracuseStep 4182893 = 1568585) B1568585
theorem B5657485 : Blo 1238437 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B7058339 : Blo 1238437 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B4182947 : Blo 1238437 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B1676323 : Blo 1238437 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B2790449 : Blo 1238437 2790449 := bstep (se 2 (by rfl) ⟨1046418, by rfl⟩ : syracuseStep 2790449 = 2092837) B2092837
theorem B2790467 : Blo 1238437 2790467 := bstep (se 1 (by rfl) ⟨2092850, by rfl⟩ : syracuseStep 2790467 = 4185701) B4185701
theorem B3970225 : Blo 1238437 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B4183217 : Blo 1238437 4183217 := bstep (se 2 (by rfl) ⟨1568706, by rfl⟩ : syracuseStep 4183217 = 3137413) B3137413
theorem B5297393 : Blo 1238437 5297393 := bstep (se 2 (by rfl) ⟨1986522, by rfl⟩ : syracuseStep 5297393 = 3973045) B3973045
theorem B3134801 : Blo 1238437 3134801 := bstep (se 2 (by rfl) ⟨1175550, by rfl⟩ : syracuseStep 3134801 = 2351101) B2351101
theorem B2544977 : Blo 1238437 2544977 := bstep (se 2 (by rfl) ⟨954366, by rfl⟩ : syracuseStep 2544977 = 1908733) B1908733
theorem B2790737 : Blo 1238437 2790737 := bstep (se 2 (by rfl) ⟨1046526, by rfl⟩ : syracuseStep 2790737 = 2093053) B2093053
theorem B2790755 : Blo 1238437 2790755 := bstep (se 1 (by rfl) ⟨2093066, by rfl⟩ : syracuseStep 2790755 = 4186133) B4186133
theorem B1324451 : Blo 1238437 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B5649841 : Blo 1238437 5649841 := bstep (se 2 (by rfl) ⟨2118690, by rfl⟩ : syracuseStep 5649841 = 4237381) B4237381
theorem B1488307 : Blo 1238437 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B7943629 : Blo 1238437 7943629 := bstep (se 3 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 7943629 = 2978861) B2978861
theorem B17880547 : Blo 1238437 17880547 := bstep (se 1 (by rfl) ⟨13410410, by rfl⟩ : syracuseStep 17880547 = 26820821) B26820821
theorem B10057229 : Blo 1238437 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B3528269 : Blo 1238437 3528269 := bstep (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) B1323101
theorem B12719729 : Blo 1238437 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B1291891 : Blo 1238437 1291891 := bstep (se 1 (by rfl) ⟨968918, by rfl⟩ : syracuseStep 1291891 = 1937837) B1937837
theorem B4708003 : Blo 1238437 4708003 := bstep (se 1 (by rfl) ⟨3531002, by rfl⟩ : syracuseStep 4708003 = 7062005) B7062005
theorem B4183757 : Blo 1238437 4183757 := bstep (se 3 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 4183757 = 1568909) B1568909
theorem B3528451 : Blo 1238437 3528451 := bstep (se 1 (by rfl) ⟨2646338, by rfl⟩ : syracuseStep 3528451 = 5292677) B5292677
theorem B4183811 : Blo 1238437 4183811 := bstep (se 1 (by rfl) ⟨3137858, by rfl⟩ : syracuseStep 4183811 = 6275717) B6275717
theorem B3528497 : Blo 1238437 3528497 := bstep (se 2 (by rfl) ⟨1323186, by rfl⟩ : syracuseStep 3528497 = 2646373) B2646373
theorem B9410417 : Blo 1238437 9410417 := bstep (se 2 (by rfl) ⟨3528906, by rfl⟩ : syracuseStep 9410417 = 7057813) B7057813
theorem B30160781 : Blo 1238437 30160781 := bstep (se 3 (by rfl) ⟨5655146, by rfl⟩ : syracuseStep 30160781 = 11310293) B11310293
theorem B11909105 : Blo 1238437 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B13760525 : Blo 1238437 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B4184081 : Blo 1238437 4184081 := bstep (se 2 (by rfl) ⟨1569030, by rfl⟩ : syracuseStep 4184081 = 3138061) B3138061
theorem B4241443 : Blo 1238437 4241443 := bstep (se 1 (by rfl) ⟨3181082, by rfl⟩ : syracuseStep 4241443 = 6362165) B6362165
theorem B1857665 : Blo 1238437 1857665 := bstep (se 2 (by rfl) ⟨696624, by rfl⟩ : syracuseStep 1857665 = 1393249) B1393249
theorem B1489027 : Blo 1238437 1489027 := bstep (se 1 (by rfl) ⟨1116770, by rfl⟩ : syracuseStep 1489027 = 2233541) B2233541
theorem B5298317 : Blo 1238437 5298317 := bstep (se 3 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 5298317 = 1986869) B1986869
theorem B1857683 : Blo 1238437 1857683 := bstep (se 1 (by rfl) ⟨1393262, by rfl⟩ : syracuseStep 1857683 = 2786525) B2786525
theorem B1857713 : Blo 1238437 1857713 := bstep (se 2 (by rfl) ⟨696642, by rfl⟩ : syracuseStep 1857713 = 1393285) B1393285
theorem B1857731 : Blo 1238437 1857731 := bstep (se 1 (by rfl) ⟨1393298, by rfl⟩ : syracuseStep 1857731 = 2786597) B2786597
theorem B1857761 : Blo 1238437 1857761 := bstep (se 2 (by rfl) ⟨696660, by rfl⟩ : syracuseStep 1857761 = 1393321) B1393321
theorem B1489123 : Blo 1238437 1489123 := bstep (se 1 (by rfl) ⟨1116842, by rfl⟩ : syracuseStep 1489123 = 2233685) B2233685
theorem B1857779 : Blo 1238437 1857779 := bstep (se 1 (by rfl) ⟨1393334, by rfl⟩ : syracuseStep 1857779 = 2786669) B2786669
theorem B1857809 : Blo 1238437 1857809 := bstep (se 2 (by rfl) ⟨696678, by rfl⟩ : syracuseStep 1857809 = 1393357) B1393357
theorem B1857827 : Blo 1238437 1857827 := bstep (se 1 (by rfl) ⟨1393370, by rfl⟩ : syracuseStep 1857827 = 2786741) B2786741
theorem B3135793 : Blo 1238437 3135793 := bstep (se 2 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 3135793 = 2351845) B2351845
theorem B1857857 : Blo 1238437 1857857 := bstep (se 2 (by rfl) ⟨696696, by rfl⟩ : syracuseStep 1857857 = 1393393) B1393393
theorem B3971405 : Blo 1238437 3971405 := bstep (se 3 (by rfl) ⟨744638, by rfl⟩ : syracuseStep 3971405 = 1489277) B1489277
theorem B1857875 : Blo 1238437 1857875 := bstep (se 1 (by rfl) ⟨1393406, by rfl⟩ : syracuseStep 1857875 = 2786813) B2786813
theorem B1857905 : Blo 1238437 1857905 := bstep (se 2 (by rfl) ⟨696714, by rfl⟩ : syracuseStep 1857905 = 1393429) B1393429
theorem B1857923 : Blo 1238437 1857923 := bstep (se 1 (by rfl) ⟨1393442, by rfl⟩ : syracuseStep 1857923 = 2786885) B2786885
theorem B1857953 : Blo 1238437 1857953 := bstep (se 2 (by rfl) ⟨696732, by rfl⟩ : syracuseStep 1857953 = 1393465) B1393465
theorem B2120113 : Blo 1238437 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B1857971 : Blo 1238437 1857971 := bstep (se 1 (by rfl) ⟨1393478, by rfl⟩ : syracuseStep 1857971 = 2786957) B2786957
theorem B1858001 : Blo 1238437 1858001 := bstep (se 2 (by rfl) ⟨696750, by rfl⟩ : syracuseStep 1858001 = 1393501) B1393501
theorem B1858019 : Blo 1238437 1858019 := bstep (se 1 (by rfl) ⟨1393514, by rfl⟩ : syracuseStep 1858019 = 2787029) B2787029
theorem B1858049 : Blo 1238437 1858049 := bstep (se 2 (by rfl) ⟨696768, by rfl⟩ : syracuseStep 1858049 = 1393537) B1393537
theorem B1858067 : Blo 1238437 1858067 := bstep (se 1 (by rfl) ⟨1393550, by rfl⟩ : syracuseStep 1858067 = 2787101) B2787101
theorem B4184621 : Blo 1238437 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B1858097 : Blo 1238437 1858097 := bstep (se 2 (by rfl) ⟨696786, by rfl⟩ : syracuseStep 1858097 = 1393573) B1393573
theorem B1858115 : Blo 1238437 1858115 := bstep (se 1 (by rfl) ⟨1393586, by rfl⟩ : syracuseStep 1858115 = 2787173) B2787173
theorem B3136067 : Blo 1238437 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B1858145 : Blo 1238437 1858145 := bstep (se 2 (by rfl) ⟨696804, by rfl⟩ : syracuseStep 1858145 = 1393609) B1393609
theorem B4184675 : Blo 1238437 4184675 := bstep (se 1 (by rfl) ⟨3138506, by rfl⟩ : syracuseStep 4184675 = 6277013) B6277013
theorem B1858163 : Blo 1238437 1858163 := bstep (se 1 (by rfl) ⟨1393622, by rfl⟩ : syracuseStep 1858163 = 2787245) B2787245
theorem B1530499 : Blo 1238437 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B1858193 : Blo 1238437 1858193 := bstep (se 2 (by rfl) ⟨696822, by rfl⟩ : syracuseStep 1858193 = 1393645) B1393645
theorem B1858211 : Blo 1238437 1858211 := bstep (se 1 (by rfl) ⟨1393658, by rfl⟩ : syracuseStep 1858211 = 2787317) B2787317
theorem B1858241 : Blo 1238437 1858241 := bstep (se 2 (by rfl) ⟨696840, by rfl⟩ : syracuseStep 1858241 = 1393681) B1393681
theorem B1858259 : Blo 1238437 1858259 := bstep (se 1 (by rfl) ⟨1393694, by rfl⟩ : syracuseStep 1858259 = 2787389) B2787389
theorem B1858289 : Blo 1238437 1858289 := bstep (se 2 (by rfl) ⟨696858, by rfl⟩ : syracuseStep 1858289 = 1393717) B1393717
theorem B1858307 : Blo 1238437 1858307 := bstep (se 1 (by rfl) ⟨1393730, by rfl⟩ : syracuseStep 1858307 = 2787461) B2787461
theorem B3136259 : Blo 1238437 3136259 := bstep (se 1 (by rfl) ⟨2352194, by rfl⟩ : syracuseStep 3136259 = 4704389) B4704389
theorem B7060229 : Blo 1238437 7060229 := bstep (se 4 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 7060229 = 1323793) B1323793
theorem B3767057 : Blo 1238437 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1858337 : Blo 1238437 1858337 := bstep (se 2 (by rfl) ⟨696876, by rfl⟩ : syracuseStep 1858337 = 1393753) B1393753
theorem B2235185 : Blo 1238437 2235185 := bstep (se 2 (by rfl) ⟨838194, by rfl⟩ : syracuseStep 2235185 = 1676389) B1676389
theorem B1858355 : Blo 1238437 1858355 := bstep (se 1 (by rfl) ⟨1393766, by rfl⟩ : syracuseStep 1858355 = 2787533) B2787533
theorem B1858385 : Blo 1238437 1858385 := bstep (se 2 (by rfl) ⟨696894, by rfl⟩ : syracuseStep 1858385 = 1393789) B1393789
theorem B1858403 : Blo 1238437 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B5954417 : Blo 1238437 5954417 := bstep (se 2 (by rfl) ⟨2232906, by rfl⟩ : syracuseStep 5954417 = 4465813) B4465813
theorem B4184945 : Blo 1238437 4184945 := bstep (se 2 (by rfl) ⟨1569354, by rfl⟩ : syracuseStep 4184945 = 3138709) B3138709
theorem B1858433 : Blo 1238437 1858433 := bstep (se 2 (by rfl) ⟨696912, by rfl⟩ : syracuseStep 1858433 = 1393825) B1393825
theorem B3627917 : Blo 1238437 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B1858451 : Blo 1238437 1858451 := bstep (se 1 (by rfl) ⟨1393838, by rfl⟩ : syracuseStep 1858451 = 2787677) B2787677
theorem B1858481 : Blo 1238437 1858481 := bstep (se 2 (by rfl) ⟨696930, by rfl⟩ : syracuseStep 1858481 = 1393861) B1393861
theorem B1858499 : Blo 1238437 1858499 := bstep (se 1 (by rfl) ⟨1393874, by rfl⟩ : syracuseStep 1858499 = 2787749) B2787749
theorem B1858529 : Blo 1238437 1858529 := bstep (se 2 (by rfl) ⟨696948, by rfl⟩ : syracuseStep 1858529 = 1393897) B1393897
theorem B1858547 : Blo 1238437 1858547 := bstep (se 1 (by rfl) ⟨1393910, by rfl⟩ : syracuseStep 1858547 = 2787821) B2787821
theorem B5291021 : Blo 1238437 5291021 := bstep (se 3 (by rfl) ⟨992066, by rfl⟩ : syracuseStep 5291021 = 1984133) B1984133
theorem B1858577 : Blo 1238437 1858577 := bstep (se 2 (by rfl) ⟨696966, by rfl⟩ : syracuseStep 1858577 = 1393933) B1393933
theorem B1858595 : Blo 1238437 1858595 := bstep (se 1 (by rfl) ⟨1393946, by rfl⟩ : syracuseStep 1858595 = 2787893) B2787893
theorem B6036515 : Blo 1238437 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B5954609 : Blo 1238437 5954609 := bstep (se 2 (by rfl) ⟨2232978, by rfl⟩ : syracuseStep 5954609 = 4465957) B4465957
theorem B6274097 : Blo 1238437 6274097 := bstep (se 2 (by rfl) ⟨2352786, by rfl⟩ : syracuseStep 6274097 = 4705573) B4705573
theorem B1858625 : Blo 1238437 1858625 := bstep (se 2 (by rfl) ⟨696984, by rfl⟩ : syracuseStep 1858625 = 1393969) B1393969
theorem B1858643 : Blo 1238437 1858643 := bstep (se 1 (by rfl) ⟨1393982, by rfl⟩ : syracuseStep 1858643 = 2787965) B2787965
theorem B1858673 : Blo 1238437 1858673 := bstep (se 2 (by rfl) ⟨697002, by rfl⟩ : syracuseStep 1858673 = 1394005) B1394005
theorem B1858691 : Blo 1238437 1858691 := bstep (se 1 (by rfl) ⟨1394018, by rfl⟩ : syracuseStep 1858691 = 2788037) B2788037
theorem B1858721 : Blo 1238437 1858721 := bstep (se 2 (by rfl) ⟨697020, by rfl⟩ : syracuseStep 1858721 = 1394041) B1394041
theorem B5954723 : Blo 1238437 5954723 := bstep (se 1 (by rfl) ⟨4466042, by rfl⟩ : syracuseStep 5954723 = 8932085) B8932085
theorem B1858739 : Blo 1238437 1858739 := bstep (se 1 (by rfl) ⟨1394054, by rfl⟩ : syracuseStep 1858739 = 2788109) B2788109
theorem B1858769 : Blo 1238437 1858769 := bstep (se 2 (by rfl) ⟨697038, by rfl⟩ : syracuseStep 1858769 = 1394077) B1394077
theorem B1858787 : Blo 1238437 1858787 := bstep (se 1 (by rfl) ⟨1394090, by rfl⟩ : syracuseStep 1858787 = 2788181) B2788181
theorem B3529955 : Blo 1238437 3529955 := bstep (se 1 (by rfl) ⟨2647466, by rfl⟩ : syracuseStep 3529955 = 5294933) B5294933
theorem B8936675 : Blo 1238437 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B1858817 : Blo 1238437 1858817 := bstep (se 2 (by rfl) ⟨697056, by rfl⟩ : syracuseStep 1858817 = 1394113) B1394113
theorem B1858835 : Blo 1238437 1858835 := bstep (se 1 (by rfl) ⟨1394126, by rfl⟩ : syracuseStep 1858835 = 2788253) B2788253
theorem B1858865 : Blo 1238437 1858865 := bstep (se 2 (by rfl) ⟨697074, by rfl⟩ : syracuseStep 1858865 = 1394149) B1394149
theorem B1858883 : Blo 1238437 1858883 := bstep (se 1 (by rfl) ⟨1394162, by rfl⟩ : syracuseStep 1858883 = 2788325) B2788325
theorem B4242755 : Blo 1238437 4242755 := bstep (se 1 (by rfl) ⟨3182066, by rfl⟩ : syracuseStep 4242755 = 6364133) B6364133
theorem B1858913 : Blo 1238437 1858913 := bstep (se 2 (by rfl) ⟨697092, by rfl⟩ : syracuseStep 1858913 = 1394185) B1394185
theorem B8928625 : Blo 1238437 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B7077233 : Blo 1238437 7077233 := bstep (se 2 (by rfl) ⟨2653962, by rfl⟩ : syracuseStep 7077233 = 5307925) B5307925
theorem B1858931 : Blo 1238437 1858931 := bstep (se 1 (by rfl) ⟨1394198, by rfl⟩ : syracuseStep 1858931 = 2788397) B2788397
theorem B4185485 : Blo 1238437 4185485 := bstep (se 3 (by rfl) ⟨784778, by rfl⟩ : syracuseStep 4185485 = 1569557) B1569557
theorem B1858961 : Blo 1238437 1858961 := bstep (se 2 (by rfl) ⟨697110, by rfl⟩ : syracuseStep 1858961 = 1394221) B1394221
theorem B1858979 : Blo 1238437 1858979 := bstep (se 1 (by rfl) ⟨1394234, by rfl⟩ : syracuseStep 1858979 = 2788469) B2788469
theorem B1859009 : Blo 1238437 1859009 := bstep (se 2 (by rfl) ⟨697128, by rfl⟩ : syracuseStep 1859009 = 1394257) B1394257
theorem B4185539 : Blo 1238437 4185539 := bstep (se 1 (by rfl) ⟨3139154, by rfl⟩ : syracuseStep 4185539 = 6278309) B6278309
theorem B1859027 : Blo 1238437 1859027 := bstep (se 1 (by rfl) ⟨1394270, by rfl⟩ : syracuseStep 1859027 = 2788541) B2788541
theorem B1859057 : Blo 1238437 1859057 := bstep (se 2 (by rfl) ⟨697146, by rfl⟩ : syracuseStep 1859057 = 1394293) B1394293
theorem B1859075 : Blo 1238437 1859075 := bstep (se 1 (by rfl) ⟨1394306, by rfl⟩ : syracuseStep 1859075 = 2788613) B2788613
theorem B1859105 : Blo 1238437 1859105 := bstep (se 2 (by rfl) ⟨697164, by rfl⟩ : syracuseStep 1859105 = 1394329) B1394329
theorem B1859123 : Blo 1238437 1859123 := bstep (se 1 (by rfl) ⟨1394342, by rfl⟩ : syracuseStep 1859123 = 2788685) B2788685
theorem B1859153 : Blo 1238437 1859153 := bstep (se 2 (by rfl) ⟨697182, by rfl⟩ : syracuseStep 1859153 = 1394365) B1394365
theorem B1859171 : Blo 1238437 1859171 := bstep (se 1 (by rfl) ⟨1394378, by rfl⟩ : syracuseStep 1859171 = 2788757) B2788757
theorem B1859201 : Blo 1238437 1859201 := bstep (se 2 (by rfl) ⟨697200, by rfl⟩ : syracuseStep 1859201 = 1394401) B1394401
theorem B1859219 : Blo 1238437 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B3137201 : Blo 1238437 3137201 := bstep (se 2 (by rfl) ⟨1176450, by rfl⟩ : syracuseStep 3137201 = 2352901) B2352901
theorem B1859249 : Blo 1238437 1859249 := bstep (se 2 (by rfl) ⟨697218, by rfl⟩ : syracuseStep 1859249 = 1394437) B1394437
theorem B1859267 : Blo 1238437 1859267 := bstep (se 1 (by rfl) ⟨1394450, by rfl⟩ : syracuseStep 1859267 = 2788901) B2788901
theorem B4185809 : Blo 1238437 4185809 := bstep (se 2 (by rfl) ⟨1569678, by rfl⟩ : syracuseStep 4185809 = 3139357) B3139357
theorem B1859297 : Blo 1238437 1859297 := bstep (se 2 (by rfl) ⟨697236, by rfl⟩ : syracuseStep 1859297 = 1394473) B1394473
theorem B3137251 : Blo 1238437 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1859315 : Blo 1238437 1859315 := bstep (se 1 (by rfl) ⟨1394486, by rfl⟩ : syracuseStep 1859315 = 2788973) B2788973
theorem B10043149 : Blo 1238437 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B1859345 : Blo 1238437 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B1859363 : Blo 1238437 1859363 := bstep (se 1 (by rfl) ⟨1394522, by rfl⟩ : syracuseStep 1859363 = 2789045) B2789045
theorem B1859393 : Blo 1238437 1859393 := bstep (se 2 (by rfl) ⟨697272, by rfl⟩ : syracuseStep 1859393 = 1394545) B1394545
theorem B1859411 : Blo 1238437 1859411 := bstep (se 1 (by rfl) ⟨1394558, by rfl⟩ : syracuseStep 1859411 = 2789117) B2789117
theorem B3137393 : Blo 1238437 3137393 := bstep (se 2 (by rfl) ⟨1176522, by rfl⟩ : syracuseStep 3137393 = 2353045) B2353045
theorem B1859441 : Blo 1238437 1859441 := bstep (se 2 (by rfl) ⟨697290, by rfl⟩ : syracuseStep 1859441 = 1394581) B1394581
theorem B1859459 : Blo 1238437 1859459 := bstep (se 1 (by rfl) ⟨1394594, by rfl⟩ : syracuseStep 1859459 = 2789189) B2789189
theorem B1859489 : Blo 1238437 1859489 := bstep (se 2 (by rfl) ⟨697308, by rfl⟩ : syracuseStep 1859489 = 1394617) B1394617
theorem B1859507 : Blo 1238437 1859507 := bstep (se 1 (by rfl) ⟨1394630, by rfl⟩ : syracuseStep 1859507 = 2789261) B2789261
theorem B1859537 : Blo 1238437 1859537 := bstep (se 2 (by rfl) ⟨697326, by rfl⟩ : syracuseStep 1859537 = 1394653) B1394653
theorem B1859555 : Blo 1238437 1859555 := bstep (se 1 (by rfl) ⟨1394666, by rfl⟩ : syracuseStep 1859555 = 2789333) B2789333
theorem B2383895 : Blo 1238437 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B1859609 : Blo 1238437 1859609 := bstep (se 2 (by rfl) ⟨697353, by rfl⟩ : syracuseStep 1859609 = 1394707) B1394707
theorem B1884235 : Blo 1238437 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B4186187 : Blo 1238437 4186187 := bstep (se 1 (by rfl) ⟨3139640, by rfl⟩ : syracuseStep 4186187 = 6279281) B6279281
theorem B1859723 : Blo 1238437 1859723 := bstep (se 1 (by rfl) ⟨1394792, by rfl⟩ : syracuseStep 1859723 = 2789585) B2789585
theorem B3137687 : Blo 1238437 3137687 := bstep (se 1 (by rfl) ⟨2353265, by rfl⟩ : syracuseStep 3137687 = 4706531) B4706531
theorem B1859735 : Blo 1238437 1859735 := bstep (se 1 (by rfl) ⟨1394801, by rfl⟩ : syracuseStep 1859735 = 2789603) B2789603
theorem B11911373 : Blo 1238437 11911373 := bstep (se 3 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 11911373 = 4466765) B4466765
theorem B1859801 : Blo 1238437 1859801 := bstep (se 2 (by rfl) ⟨697425, by rfl⟩ : syracuseStep 1859801 = 1394851) B1394851
theorem B6275393 : Blo 1238437 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B1859915 : Blo 1238437 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B1859927 : Blo 1238437 1859927 := bstep (se 1 (by rfl) ⟨1394945, by rfl⟩ : syracuseStep 1859927 = 2789891) B2789891
theorem B4186457 : Blo 1238437 4186457 := bstep (se 2 (by rfl) ⟨1569921, by rfl⟩ : syracuseStep 4186457 = 3139843) B3139843
theorem B2646425 : Blo 1238437 2646425 := bstep (se 2 (by rfl) ⟨992409, by rfl⟩ : syracuseStep 2646425 = 1984819) B1984819
theorem B1859993 : Blo 1238437 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B4702643 : Blo 1238437 4702643 := bstep (se 1 (by rfl) ⟨3526982, by rfl⟩ : syracuseStep 4702643 = 7053965) B7053965
theorem B4702657 : Blo 1238437 4702657 := bstep (se 2 (by rfl) ⟨1763496, by rfl⟩ : syracuseStep 4702657 = 3526993) B3526993
theorem B1860107 : Blo 1238437 1860107 := bstep (se 1 (by rfl) ⟨1395080, by rfl⟩ : syracuseStep 1860107 = 2790161) B2790161
theorem B1860119 : Blo 1238437 1860119 := bstep (se 1 (by rfl) ⟨1395089, by rfl⟩ : syracuseStep 1860119 = 2790179) B2790179
theorem B1860185 : Blo 1238437 1860185 := bstep (se 2 (by rfl) ⟨697569, by rfl⟩ : syracuseStep 1860185 = 1395139) B1395139
theorem B1393303 : Blo 1238437 1393303 := bstep (se 1 (by rfl) ⟨1044977, by rfl⟩ : syracuseStep 1393303 = 2089955) B2089955
theorem B1860299 : Blo 1238437 1860299 := bstep (se 1 (by rfl) ⟨1395224, by rfl⟩ : syracuseStep 1860299 = 2790449) B2790449
theorem B1860311 : Blo 1238437 1860311 := bstep (se 1 (by rfl) ⟨1395233, by rfl⟩ : syracuseStep 1860311 = 2790467) B2790467
theorem B2384641 : Blo 1238437 2384641 := bstep (se 2 (by rfl) ⟨894240, by rfl⟩ : syracuseStep 2384641 = 1788481) B1788481
theorem B1884953 : Blo 1238437 1884953 := bstep (se 2 (by rfl) ⟨706857, by rfl⟩ : syracuseStep 1884953 = 1413715) B1413715
theorem B1860377 : Blo 1238437 1860377 := bstep (se 2 (by rfl) ⟨697641, by rfl⟩ : syracuseStep 1860377 = 1395283) B1395283
theorem B1393483 : Blo 1238437 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B3531595 : Blo 1238437 3531595 := bstep (se 1 (by rfl) ⟨2648696, by rfl⟩ : syracuseStep 3531595 = 5297393) B5297393
theorem B2040665 : Blo 1238437 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B20112245 : Blo 1238437 20112245 := bstep (se 5 (by rfl) ⟨942761, by rfl⟩ : syracuseStep 20112245 = 1885523) B1885523
theorem B2089867 : Blo 1238437 2089867 := bstep (se 1 (by rfl) ⟨1567400, by rfl⟩ : syracuseStep 2089867 = 3134801) B3134801
theorem B1860491 : Blo 1238437 1860491 := bstep (se 1 (by rfl) ⟨1395368, by rfl⟩ : syracuseStep 1860491 = 2790737) B2790737
theorem B1860503 : Blo 1238437 1860503 := bstep (se 1 (by rfl) ⟨1395377, by rfl⟩ : syracuseStep 1860503 = 2790755) B2790755
theorem B1393591 : Blo 1238437 1393591 := bstep (se 1 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 1393591 = 2090387) B2090387
theorem B3138497 : Blo 1238437 3138497 := bstep (se 2 (by rfl) ⟨1176936, by rfl⟩ : syracuseStep 3138497 = 2353873) B2353873
theorem B1860569 : Blo 1238437 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B128803861 : Blo 1238437 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B2090009 : Blo 1238437 2090009 := bstep (se 2 (by rfl) ⟨783753, by rfl⟩ : syracuseStep 2090009 = 1567507) B1567507
theorem B2352179 : Blo 1238437 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B8479819 : Blo 1238437 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B3531869 : Blo 1238437 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B1393771 : Blo 1238437 1393771 := bstep (se 1 (by rfl) ⟨1045328, by rfl⟩ : syracuseStep 1393771 = 2090657) B2090657
theorem B2090137 : Blo 1238437 2090137 := bstep (se 2 (by rfl) ⟨783801, by rfl⟩ : syracuseStep 2090137 = 1567603) B1567603
theorem B2786507 : Blo 1238437 2786507 := bstep (se 1 (by rfl) ⟨2089880, by rfl⟩ : syracuseStep 2786507 = 4179761) B4179761
theorem B2352331 : Blo 1238437 2352331 := bstep (se 1 (by rfl) ⟨1764248, by rfl⟩ : syracuseStep 2352331 = 3528497) B3528497
theorem B5293259 : Blo 1238437 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B1393879 : Blo 1238437 1393879 := bstep (se 1 (by rfl) ⟨1045409, by rfl⟩ : syracuseStep 1393879 = 2090819) B2090819
theorem B2786561 : Blo 1238437 2786561 := bstep (se 2 (by rfl) ⟨1044960, by rfl⟩ : syracuseStep 2786561 = 2089921) B2089921
theorem B7939403 : Blo 1238437 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B1394059 : Blo 1238437 1394059 := bstep (se 1 (by rfl) ⟨1045544, by rfl⟩ : syracuseStep 1394059 = 2091089) B2091089
theorem B1238443 : Blo 1238437 1238443 := bstep (se 1 (by rfl) ⟨928832, by rfl⟩ : syracuseStep 1238443 = 1857665) B1857665
theorem B3532211 : Blo 1238437 3532211 := bstep (se 1 (by rfl) ⟨2649158, by rfl⟩ : syracuseStep 3532211 = 5298317) B5298317
theorem B1238455 : Blo 1238437 1238455 := bstep (se 1 (by rfl) ⟨928841, by rfl⟩ : syracuseStep 1238455 = 1857683) B1857683
theorem B1238475 : Blo 1238437 1238475 := bstep (se 1 (by rfl) ⟨928856, by rfl⟩ : syracuseStep 1238475 = 1857713) B1857713
theorem B120620501 : Blo 1238437 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B1238487 : Blo 1238437 1238487 := bstep (se 1 (by rfl) ⟨928865, by rfl⟩ : syracuseStep 1238487 = 1857731) B1857731
theorem B2786777 : Blo 1238437 2786777 := bstep (se 2 (by rfl) ⟨1045041, by rfl⟩ : syracuseStep 2786777 = 2090083) B2090083
theorem B3139033 : Blo 1238437 3139033 := bstep (se 2 (by rfl) ⟨1177137, by rfl⟩ : syracuseStep 3139033 = 2354275) B2354275
theorem B1238507 : Blo 1238437 1238507 := bstep (se 1 (by rfl) ⟨928880, by rfl⟩ : syracuseStep 1238507 = 1857761) B1857761
theorem B1238519 : Blo 1238437 1238519 := bstep (se 1 (by rfl) ⟨928889, by rfl⟩ : syracuseStep 1238519 = 1857779) B1857779
theorem B1394167 : Blo 1238437 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B1238539 : Blo 1238437 1238539 := bstep (se 1 (by rfl) ⟨928904, by rfl⟩ : syracuseStep 1238539 = 1857809) B1857809
theorem B1238551 : Blo 1238437 1238551 := bstep (se 1 (by rfl) ⟨928913, by rfl⟩ : syracuseStep 1238551 = 1857827) B1857827
theorem B2352665 : Blo 1238437 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B1238571 : Blo 1238437 1238571 := bstep (se 1 (by rfl) ⟨928928, by rfl⟩ : syracuseStep 1238571 = 1857857) B1857857
theorem B2786867 : Blo 1238437 2786867 := bstep (se 1 (by rfl) ⟨2090150, by rfl⟩ : syracuseStep 2786867 = 4180301) B4180301
theorem B5293619 : Blo 1238437 5293619 := bstep (se 1 (by rfl) ⟨3970214, by rfl⟩ : syracuseStep 5293619 = 7940429) B7940429
theorem B1238583 : Blo 1238437 1238583 := bstep (se 1 (by rfl) ⟨928937, by rfl⟩ : syracuseStep 1238583 = 1857875) B1857875
theorem B2647603 : Blo 1238437 2647603 := bstep (se 1 (by rfl) ⟨1985702, by rfl⟩ : syracuseStep 2647603 = 3971405) B3971405
theorem B1238603 : Blo 1238437 1238603 := bstep (se 1 (by rfl) ⟨928952, by rfl⟩ : syracuseStep 1238603 = 1857905) B1857905
theorem B1238615 : Blo 1238437 1238615 := bstep (se 1 (by rfl) ⟨928961, by rfl⟩ : syracuseStep 1238615 = 1857923) B1857923
theorem B2786903 : Blo 1238437 2786903 := bstep (se 1 (by rfl) ⟨2090177, by rfl⟩ : syracuseStep 2786903 = 4180355) B4180355
theorem B1238635 : Blo 1238437 1238635 := bstep (se 1 (by rfl) ⟨928976, by rfl⟩ : syracuseStep 1238635 = 1857953) B1857953
theorem B1238647 : Blo 1238437 1238647 := bstep (se 1 (by rfl) ⟨928985, by rfl⟩ : syracuseStep 1238647 = 1857971) B1857971
theorem B1238667 : Blo 1238437 1238667 := bstep (se 1 (by rfl) ⟨929000, by rfl⟩ : syracuseStep 1238667 = 1858001) B1858001
theorem B1238679 : Blo 1238437 1238679 := bstep (se 1 (by rfl) ⟨929009, by rfl⟩ : syracuseStep 1238679 = 1858019) B1858019
theorem B1238699 : Blo 1238437 1238699 := bstep (se 1 (by rfl) ⟨929024, by rfl⟩ : syracuseStep 1238699 = 1858049) B1858049
theorem B1394347 : Blo 1238437 1394347 := bstep (se 1 (by rfl) ⟨1045760, by rfl⟩ : syracuseStep 1394347 = 2091521) B2091521
theorem B1238711 : Blo 1238437 1238711 := bstep (se 1 (by rfl) ⟨929033, by rfl⟩ : syracuseStep 1238711 = 1858067) B1858067
theorem B1238731 : Blo 1238437 1238731 := bstep (se 1 (by rfl) ⟨929048, by rfl⟩ : syracuseStep 1238731 = 1858097) B1858097
theorem B1238743 : Blo 1238437 1238743 := bstep (se 1 (by rfl) ⟨929057, by rfl⟩ : syracuseStep 1238743 = 1858115) B1858115
theorem B2090711 : Blo 1238437 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B7538393 : Blo 1238437 7538393 := bstep (se 2 (by rfl) ⟨2826897, by rfl⟩ : syracuseStep 7538393 = 5653795) B5653795
theorem B1238763 : Blo 1238437 1238763 := bstep (se 1 (by rfl) ⟨929072, by rfl⟩ : syracuseStep 1238763 = 1858145) B1858145
theorem B1238775 : Blo 1238437 1238775 := bstep (se 1 (by rfl) ⟨929081, by rfl⟩ : syracuseStep 1238775 = 1858163) B1858163
theorem B2787083 : Blo 1238437 2787083 := bstep (se 1 (by rfl) ⟨2090312, by rfl⟩ : syracuseStep 2787083 = 4180625) B4180625
theorem B1984267 : Blo 1238437 1984267 := bstep (se 1 (by rfl) ⟨1488200, by rfl⟩ : syracuseStep 1984267 = 2976401) B2976401
theorem B1238795 : Blo 1238437 1238795 := bstep (se 1 (by rfl) ⟨929096, by rfl⟩ : syracuseStep 1238795 = 1858193) B1858193
theorem B1238807 : Blo 1238437 1238807 := bstep (se 1 (by rfl) ⟨929105, by rfl⟩ : syracuseStep 1238807 = 1858211) B1858211
theorem B1394455 : Blo 1238437 1394455 := bstep (se 1 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 1394455 = 2091683) B2091683
theorem B1238827 : Blo 1238437 1238827 := bstep (se 1 (by rfl) ⟨929120, by rfl⟩ : syracuseStep 1238827 = 1858241) B1858241
theorem B1238839 : Blo 1238437 1238839 := bstep (se 1 (by rfl) ⟨929129, by rfl⟩ : syracuseStep 1238839 = 1858259) B1858259
theorem B11904833 : Blo 1238437 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B2787137 : Blo 1238437 2787137 := bstep (se 2 (by rfl) ⟨1045176, by rfl⟩ : syracuseStep 2787137 = 2090353) B2090353
theorem B1238859 : Blo 1238437 1238859 := bstep (se 1 (by rfl) ⟨929144, by rfl⟩ : syracuseStep 1238859 = 1858289) B1858289
theorem B1238871 : Blo 1238437 1238871 := bstep (se 1 (by rfl) ⟨929153, by rfl⟩ : syracuseStep 1238871 = 1858307) B1858307
theorem B2090839 : Blo 1238437 2090839 := bstep (se 1 (by rfl) ⟨1568129, by rfl⟩ : syracuseStep 2090839 = 3136259) B3136259
theorem B1238891 : Blo 1238437 1238891 := bstep (se 1 (by rfl) ⟨929168, by rfl⟩ : syracuseStep 1238891 = 1858337) B1858337
theorem B1238903 : Blo 1238437 1238903 := bstep (se 1 (by rfl) ⟨929177, by rfl⟩ : syracuseStep 1238903 = 1858355) B1858355
theorem B1238923 : Blo 1238437 1238923 := bstep (se 1 (by rfl) ⟨929192, by rfl⟩ : syracuseStep 1238923 = 1858385) B1858385
theorem B1238935 : Blo 1238437 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B1984409 : Blo 1238437 1984409 := bstep (se 2 (by rfl) ⟨744153, by rfl⟩ : syracuseStep 1984409 = 1488307) B1488307
theorem B1238955 : Blo 1238437 1238955 := bstep (se 1 (by rfl) ⟨929216, by rfl⟩ : syracuseStep 1238955 = 1858433) B1858433
theorem B2418611 : Blo 1238437 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B1238967 : Blo 1238437 1238967 := bstep (se 1 (by rfl) ⟨929225, by rfl⟩ : syracuseStep 1238967 = 1858451) B1858451
theorem B1238987 : Blo 1238437 1238987 := bstep (se 1 (by rfl) ⟨929240, by rfl⟩ : syracuseStep 1238987 = 1858481) B1858481
theorem B1394635 : Blo 1238437 1394635 := bstep (se 1 (by rfl) ⟨1045976, by rfl⟩ : syracuseStep 1394635 = 2091953) B2091953
theorem B1238999 : Blo 1238437 1238999 := bstep (se 1 (by rfl) ⟨929249, by rfl⟩ : syracuseStep 1238999 = 1858499) B1858499
theorem B23840729 : Blo 1238437 23840729 := bstep (se 2 (by rfl) ⟨8940273, by rfl⟩ : syracuseStep 23840729 = 17880547) B17880547
theorem B1239019 : Blo 1238437 1239019 := bstep (se 1 (by rfl) ⟨929264, by rfl⟩ : syracuseStep 1239019 = 1858529) B1858529
theorem B1239031 : Blo 1238437 1239031 := bstep (se 1 (by rfl) ⟨929273, by rfl⟩ : syracuseStep 1239031 = 1858547) B1858547
theorem B2648065 : Blo 1238437 2648065 := bstep (se 2 (by rfl) ⟨993024, by rfl⟩ : syracuseStep 2648065 = 1986049) B1986049
theorem B1239051 : Blo 1238437 1239051 := bstep (se 1 (by rfl) ⟨929288, by rfl⟩ : syracuseStep 1239051 = 1858577) B1858577
theorem B1239063 : Blo 1238437 1239063 := bstep (se 1 (by rfl) ⟨929297, by rfl⟩ : syracuseStep 1239063 = 1858595) B1858595
theorem B4024343 : Blo 1238437 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2787353 : Blo 1238437 2787353 := bstep (se 2 (by rfl) ⟨1045257, by rfl⟩ : syracuseStep 2787353 = 2090515) B2090515
theorem B1239083 : Blo 1238437 1239083 := bstep (se 1 (by rfl) ⟨929312, by rfl⟩ : syracuseStep 1239083 = 1858625) B1858625
theorem B1239095 : Blo 1238437 1239095 := bstep (se 1 (by rfl) ⟨929321, by rfl⟩ : syracuseStep 1239095 = 1858643) B1858643
theorem B1394743 : Blo 1238437 1394743 := bstep (se 1 (by rfl) ⟨1046057, by rfl⟩ : syracuseStep 1394743 = 2092115) B2092115
theorem B9406529 : Blo 1238437 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B1239115 : Blo 1238437 1239115 := bstep (se 1 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 1239115 = 1858673) B1858673
theorem B1239127 : Blo 1238437 1239127 := bstep (se 1 (by rfl) ⟨929345, by rfl⟩ : syracuseStep 1239127 = 1858691) B1858691
theorem B1763417 : Blo 1238437 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B7063645 : Blo 1238437 7063645 := bstep (se 3 (by rfl) ⟨1324433, by rfl⟩ : syracuseStep 7063645 = 2648867) B2648867
theorem B1239147 : Blo 1238437 1239147 := bstep (se 1 (by rfl) ⟨929360, by rfl⟩ : syracuseStep 1239147 = 1858721) B1858721
theorem B2787443 : Blo 1238437 2787443 := bstep (se 1 (by rfl) ⟨2090582, by rfl⟩ : syracuseStep 2787443 = 4181165) B4181165
theorem B1239159 : Blo 1238437 1239159 := bstep (se 1 (by rfl) ⟨929369, by rfl⟩ : syracuseStep 1239159 = 1858739) B1858739
theorem B1239179 : Blo 1238437 1239179 := bstep (se 1 (by rfl) ⟨929384, by rfl⟩ : syracuseStep 1239179 = 1858769) B1858769
theorem B2787479 : Blo 1238437 2787479 := bstep (se 1 (by rfl) ⟨2090609, by rfl⟩ : syracuseStep 2787479 = 4181219) B4181219
theorem B1239191 : Blo 1238437 1239191 := bstep (se 1 (by rfl) ⟨929393, by rfl⟩ : syracuseStep 1239191 = 1858787) B1858787
theorem B2353303 : Blo 1238437 2353303 := bstep (se 1 (by rfl) ⟨1764977, by rfl⟩ : syracuseStep 2353303 = 3529955) B3529955
theorem B5957783 : Blo 1238437 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B1722521 : Blo 1238437 1722521 := bstep (se 2 (by rfl) ⟨645945, by rfl⟩ : syracuseStep 1722521 = 1291891) B1291891
theorem B1239211 : Blo 1238437 1239211 := bstep (se 1 (by rfl) ⟨929408, by rfl⟩ : syracuseStep 1239211 = 1858817) B1858817
theorem B1239223 : Blo 1238437 1239223 := bstep (se 1 (by rfl) ⟨929417, by rfl⟩ : syracuseStep 1239223 = 1858835) B1858835
theorem B1239243 : Blo 1238437 1239243 := bstep (se 1 (by rfl) ⟨929432, by rfl⟩ : syracuseStep 1239243 = 1858865) B1858865
theorem B1239255 : Blo 1238437 1239255 := bstep (se 1 (by rfl) ⟨929441, by rfl⟩ : syracuseStep 1239255 = 1858883) B1858883
theorem B2828503 : Blo 1238437 2828503 := bstep (se 1 (by rfl) ⟨2121377, by rfl⟩ : syracuseStep 2828503 = 4242755) B4242755
theorem B6277337 : Blo 1238437 6277337 := bstep (se 2 (by rfl) ⟨2354001, by rfl⟩ : syracuseStep 6277337 = 4708003) B4708003
theorem B1239275 : Blo 1238437 1239275 := bstep (se 1 (by rfl) ⟨929456, by rfl⟩ : syracuseStep 1239275 = 1858913) B1858913
theorem B1394923 : Blo 1238437 1394923 := bstep (se 1 (by rfl) ⟨1046192, by rfl⟩ : syracuseStep 1394923 = 2092385) B2092385
theorem B1239287 : Blo 1238437 1239287 := bstep (se 1 (by rfl) ⟨929465, by rfl⟩ : syracuseStep 1239287 = 1858931) B1858931
theorem B11307269 : Blo 1238437 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B1239307 : Blo 1238437 1239307 := bstep (se 1 (by rfl) ⟨929480, by rfl⟩ : syracuseStep 1239307 = 1858961) B1858961
theorem B4180247 : Blo 1238437 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B1239319 : Blo 1238437 1239319 := bstep (se 1 (by rfl) ⟨929489, by rfl⟩ : syracuseStep 1239319 = 1858979) B1858979
theorem B1239339 : Blo 1238437 1239339 := bstep (se 1 (by rfl) ⟨929504, by rfl⟩ : syracuseStep 1239339 = 1859009) B1859009
theorem B1239351 : Blo 1238437 1239351 := bstep (se 1 (by rfl) ⟨929513, by rfl⟩ : syracuseStep 1239351 = 1859027) B1859027
theorem B2787659 : Blo 1238437 2787659 := bstep (se 1 (by rfl) ⟨2090744, by rfl⟩ : syracuseStep 2787659 = 4181489) B4181489
theorem B4704587 : Blo 1238437 4704587 := bstep (se 1 (by rfl) ⟨3528440, by rfl⟩ : syracuseStep 4704587 = 7056881) B7056881
theorem B1239371 : Blo 1238437 1239371 := bstep (se 1 (by rfl) ⟨929528, by rfl⟩ : syracuseStep 1239371 = 1859057) B1859057
theorem B1239383 : Blo 1238437 1239383 := bstep (se 1 (by rfl) ⟨929537, by rfl⟩ : syracuseStep 1239383 = 1859075) B1859075
theorem B1395031 : Blo 1238437 1395031 := bstep (se 1 (by rfl) ⟨1046273, by rfl⟩ : syracuseStep 1395031 = 2092547) B2092547
theorem B4704601 : Blo 1238437 4704601 := bstep (se 2 (by rfl) ⟨1764225, by rfl⟩ : syracuseStep 4704601 = 3528451) B3528451
theorem B1239403 : Blo 1238437 1239403 := bstep (se 1 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 1239403 = 1859105) B1859105
theorem B1239415 : Blo 1238437 1239415 := bstep (se 1 (by rfl) ⟨929561, by rfl⟩ : syracuseStep 1239415 = 1859123) B1859123
theorem B2787713 : Blo 1238437 2787713 := bstep (se 2 (by rfl) ⟨1045392, by rfl⟩ : syracuseStep 2787713 = 2090785) B2090785
theorem B1239435 : Blo 1238437 1239435 := bstep (se 1 (by rfl) ⟨929576, by rfl⟩ : syracuseStep 1239435 = 1859153) B1859153
theorem B1239447 : Blo 1238437 1239447 := bstep (se 1 (by rfl) ⟨929585, by rfl⟩ : syracuseStep 1239447 = 1859171) B1859171
theorem B1239467 : Blo 1238437 1239467 := bstep (se 1 (by rfl) ⟨929600, by rfl⟩ : syracuseStep 1239467 = 1859201) B1859201
theorem B1239479 : Blo 1238437 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B2091467 : Blo 1238437 2091467 := bstep (se 1 (by rfl) ⟨1568600, by rfl⟩ : syracuseStep 2091467 = 3137201) B3137201
theorem B1239499 : Blo 1238437 1239499 := bstep (se 1 (by rfl) ⟨929624, by rfl⟩ : syracuseStep 1239499 = 1859249) B1859249
theorem B1239511 : Blo 1238437 1239511 := bstep (se 1 (by rfl) ⟨929633, by rfl⟩ : syracuseStep 1239511 = 1859267) B1859267
theorem B1239531 : Blo 1238437 1239531 := bstep (se 1 (by rfl) ⟨929648, by rfl⟩ : syracuseStep 1239531 = 1859297) B1859297
theorem B1239543 : Blo 1238437 1239543 := bstep (se 1 (by rfl) ⟨929657, by rfl⟩ : syracuseStep 1239543 = 1859315) B1859315
theorem B1239563 : Blo 1238437 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B1395211 : Blo 1238437 1395211 := bstep (se 1 (by rfl) ⟨1046408, by rfl⟩ : syracuseStep 1395211 = 2092817) B2092817
theorem B1239575 : Blo 1238437 1239575 := bstep (se 1 (by rfl) ⟨929681, by rfl⟩ : syracuseStep 1239575 = 1859363) B1859363
theorem B1239595 : Blo 1238437 1239595 := bstep (se 1 (by rfl) ⟨929696, by rfl⟩ : syracuseStep 1239595 = 1859393) B1859393
theorem B1239607 : Blo 1238437 1239607 := bstep (se 1 (by rfl) ⟨929705, by rfl⟩ : syracuseStep 1239607 = 1859411) B1859411
theorem B2091595 : Blo 1238437 2091595 := bstep (se 1 (by rfl) ⟨1568696, by rfl⟩ : syracuseStep 2091595 = 3137393) B3137393
theorem B1239627 : Blo 1238437 1239627 := bstep (se 1 (by rfl) ⟨929720, by rfl⟩ : syracuseStep 1239627 = 1859441) B1859441
theorem B1239639 : Blo 1238437 1239639 := bstep (se 1 (by rfl) ⟨929729, by rfl⟩ : syracuseStep 1239639 = 1859459) B1859459
theorem B2787929 : Blo 1238437 2787929 := bstep (se 2 (by rfl) ⟨1045473, by rfl⟩ : syracuseStep 2787929 = 2090947) B2090947
theorem B1239659 : Blo 1238437 1239659 := bstep (se 1 (by rfl) ⟨929744, by rfl⟩ : syracuseStep 1239659 = 1859489) B1859489
theorem B1239671 : Blo 1238437 1239671 := bstep (se 1 (by rfl) ⟨929753, by rfl⟩ : syracuseStep 1239671 = 1859507) B1859507
theorem B1395319 : Blo 1238437 1395319 := bstep (se 1 (by rfl) ⟨1046489, by rfl⟩ : syracuseStep 1395319 = 2092979) B2092979
theorem B8931971 : Blo 1238437 8931971 := bstep (se 1 (by rfl) ⟨6698978, by rfl⟩ : syracuseStep 8931971 = 13397957) B13397957
theorem B1239691 : Blo 1238437 1239691 := bstep (se 1 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 1239691 = 1859537) B1859537
theorem B1239703 : Blo 1238437 1239703 := bstep (se 1 (by rfl) ⟨929777, by rfl⟩ : syracuseStep 1239703 = 1859555) B1859555
theorem B1239723 : Blo 1238437 1239723 := bstep (se 1 (by rfl) ⟨929792, by rfl⟩ : syracuseStep 1239723 = 1859585) B1859585
theorem B2788019 : Blo 1238437 2788019 := bstep (se 1 (by rfl) ⟨2091014, by rfl⟩ : syracuseStep 2788019 = 4182029) B4182029
theorem B1239735 : Blo 1238437 1239735 := bstep (se 1 (by rfl) ⟨929801, by rfl⟩ : syracuseStep 1239735 = 1859603) B1859603
theorem B1239755 : Blo 1238437 1239755 := bstep (se 1 (by rfl) ⟨929816, by rfl⟩ : syracuseStep 1239755 = 1859633) B1859633
theorem B9546445 : Blo 1238437 9546445 := bstep (se 3 (by rfl) ⟨1789958, by rfl⟩ : syracuseStep 9546445 = 3579917) B3579917
theorem B1764055 : Blo 1238437 1764055 := bstep (se 1 (by rfl) ⟨1323041, by rfl⟩ : syracuseStep 1764055 = 2646083) B2646083
theorem B2788055 : Blo 1238437 2788055 := bstep (se 1 (by rfl) ⟨2091041, by rfl⟩ : syracuseStep 2788055 = 4182083) B4182083
theorem B2091737 : Blo 1238437 2091737 := bstep (se 2 (by rfl) ⟨784401, by rfl⟩ : syracuseStep 2091737 = 1568803) B1568803
theorem B1239767 : Blo 1238437 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B5655257 : Blo 1238437 5655257 := bstep (se 2 (by rfl) ⟨2120721, by rfl⟩ : syracuseStep 5655257 = 4241443) B4241443
theorem B2648791 : Blo 1238437 2648791 := bstep (se 1 (by rfl) ⟨1986593, by rfl⟩ : syracuseStep 2648791 = 3973187) B3973187
theorem B1239787 : Blo 1238437 1239787 := bstep (se 1 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 1239787 = 1859681) B1859681
theorem B1239799 : Blo 1238437 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B1239819 : Blo 1238437 1239819 := bstep (se 1 (by rfl) ⟨929864, by rfl⟩ : syracuseStep 1239819 = 1859729) B1859729
theorem B1239831 : Blo 1238437 1239831 := bstep (se 1 (by rfl) ⟨929873, by rfl⟩ : syracuseStep 1239831 = 1859747) B1859747
theorem B1239851 : Blo 1238437 1239851 := bstep (se 1 (by rfl) ⟨929888, by rfl⟩ : syracuseStep 1239851 = 1859777) B1859777
theorem B7056173 : Blo 1238437 7056173 := bstep (se 3 (by rfl) ⟨1323032, by rfl⟩ : syracuseStep 7056173 = 2646065) B2646065
theorem B4180787 : Blo 1238437 4180787 := bstep (se 1 (by rfl) ⟨3135590, by rfl⟩ : syracuseStep 4180787 = 6271181) B6271181
theorem B1239863 : Blo 1238437 1239863 := bstep (se 1 (by rfl) ⟨929897, by rfl⟩ : syracuseStep 1239863 = 1859795) B1859795
theorem B1239883 : Blo 1238437 1239883 := bstep (se 1 (by rfl) ⟨929912, by rfl⟩ : syracuseStep 1239883 = 1859825) B1859825
theorem B1239895 : Blo 1238437 1239895 := bstep (se 1 (by rfl) ⟨929921, by rfl⟩ : syracuseStep 1239895 = 1859843) B1859843
theorem B1985369 : Blo 1238437 1985369 := bstep (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) B1489027
theorem B2091865 : Blo 1238437 2091865 := bstep (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) B1568899
theorem B1239915 : Blo 1238437 1239915 := bstep (se 1 (by rfl) ⟨929936, by rfl⟩ : syracuseStep 1239915 = 1859873) B1859873
theorem B1239927 : Blo 1238437 1239927 := bstep (se 1 (by rfl) ⟨929945, by rfl⟩ : syracuseStep 1239927 = 1859891) B1859891
theorem B2788235 : Blo 1238437 2788235 := bstep (se 1 (by rfl) ⟨2091176, by rfl⟩ : syracuseStep 2788235 = 4182353) B4182353
theorem B1239947 : Blo 1238437 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B1239959 : Blo 1238437 1239959 := bstep (se 1 (by rfl) ⟨929969, by rfl⟩ : syracuseStep 1239959 = 1859939) B1859939
theorem B1239979 : Blo 1238437 1239979 := bstep (se 1 (by rfl) ⟨929984, by rfl⟩ : syracuseStep 1239979 = 1859969) B1859969
theorem B1239991 : Blo 1238437 1239991 := bstep (se 1 (by rfl) ⟨929993, by rfl⟩ : syracuseStep 1239991 = 1859987) B1859987
theorem B2788289 : Blo 1238437 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B1240011 : Blo 1238437 1240011 := bstep (se 1 (by rfl) ⟨930008, by rfl⟩ : syracuseStep 1240011 = 1860017) B1860017
theorem B2354123 : Blo 1238437 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B1240023 : Blo 1238437 1240023 := bstep (se 1 (by rfl) ⟨930017, by rfl⟩ : syracuseStep 1240023 = 1860035) B1860035
theorem B1240043 : Blo 1238437 1240043 := bstep (se 1 (by rfl) ⟨930032, by rfl⟩ : syracuseStep 1240043 = 1860065) B1860065
theorem B1240055 : Blo 1238437 1240055 := bstep (se 1 (by rfl) ⟨930041, by rfl⟩ : syracuseStep 1240055 = 1860083) B1860083
theorem B2354177 : Blo 1238437 2354177 := bstep (se 2 (by rfl) ⟨882816, by rfl⟩ : syracuseStep 2354177 = 1765633) B1765633
theorem B1240075 : Blo 1238437 1240075 := bstep (se 1 (by rfl) ⟨930056, by rfl⟩ : syracuseStep 1240075 = 1860113) B1860113
theorem B1240087 : Blo 1238437 1240087 := bstep (se 1 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 1240087 = 1860131) B1860131
theorem B1240107 : Blo 1238437 1240107 := bstep (se 1 (by rfl) ⟨930080, by rfl⟩ : syracuseStep 1240107 = 1860161) B1860161
theorem B4590637 : Blo 1238437 4590637 := bstep (se 3 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 4590637 = 1721489) B1721489
theorem B1240119 : Blo 1238437 1240119 := bstep (se 1 (by rfl) ⟨930089, by rfl⟩ : syracuseStep 1240119 = 1860179) B1860179
theorem B4181057 : Blo 1238437 4181057 := bstep (se 2 (by rfl) ⟨1567896, by rfl⟩ : syracuseStep 4181057 = 3135793) B3135793
theorem B5958721 : Blo 1238437 5958721 := bstep (se 2 (by rfl) ⟨2234520, by rfl⟩ : syracuseStep 5958721 = 4469041) B4469041
theorem B1240139 : Blo 1238437 1240139 := bstep (se 1 (by rfl) ⟨930104, by rfl⟩ : syracuseStep 1240139 = 1860209) B1860209
theorem B1567831 : Blo 1238437 1567831 := bstep (se 1 (by rfl) ⟨1175873, by rfl⟩ : syracuseStep 1567831 = 2351747) B2351747
theorem B1240151 : Blo 1238437 1240151 := bstep (se 1 (by rfl) ⟨930113, by rfl⟩ : syracuseStep 1240151 = 1860227) B1860227
theorem B1240171 : Blo 1238437 1240171 := bstep (se 1 (by rfl) ⟨930128, by rfl⟩ : syracuseStep 1240171 = 1860257) B1860257
theorem B1240183 : Blo 1238437 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B1240203 : Blo 1238437 1240203 := bstep (se 1 (by rfl) ⟨930152, by rfl⟩ : syracuseStep 1240203 = 1860305) B1860305
theorem B1240215 : Blo 1238437 1240215 := bstep (se 1 (by rfl) ⟨930161, by rfl⟩ : syracuseStep 1240215 = 1860323) B1860323
theorem B2788505 : Blo 1238437 2788505 := bstep (se 2 (by rfl) ⟨1045689, by rfl⟩ : syracuseStep 2788505 = 2091379) B2091379
theorem B1240235 : Blo 1238437 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B1240247 : Blo 1238437 1240247 := bstep (se 1 (by rfl) ⟨930185, by rfl⟩ : syracuseStep 1240247 = 1860371) B1860371
theorem B1240267 : Blo 1238437 1240267 := bstep (se 1 (by rfl) ⟨930200, by rfl⟩ : syracuseStep 1240267 = 1860401) B1860401
theorem B1240279 : Blo 1238437 1240279 := bstep (se 1 (by rfl) ⟨930209, by rfl⟩ : syracuseStep 1240279 = 1860419) B1860419
theorem B1240299 : Blo 1238437 1240299 := bstep (se 1 (by rfl) ⟨930224, by rfl⟩ : syracuseStep 1240299 = 1860449) B1860449
theorem B2788595 : Blo 1238437 2788595 := bstep (se 1 (by rfl) ⟨2091446, by rfl⟩ : syracuseStep 2788595 = 4182893) B4182893
theorem B1240311 : Blo 1238437 1240311 := bstep (se 1 (by rfl) ⟨930233, by rfl⟩ : syracuseStep 1240311 = 1860467) B1860467
theorem B1240331 : Blo 1238437 1240331 := bstep (se 1 (by rfl) ⟨930248, by rfl⟩ : syracuseStep 1240331 = 1860497) B1860497
theorem B4705559 : Blo 1238437 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B2788631 : Blo 1238437 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B1240343 : Blo 1238437 1240343 := bstep (se 1 (by rfl) ⟨930257, by rfl⟩ : syracuseStep 1240343 = 1860515) B1860515
theorem B1240363 : Blo 1238437 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B1240375 : Blo 1238437 1240375 := bstep (se 1 (by rfl) ⟨930281, by rfl⟩ : syracuseStep 1240375 = 1860563) B1860563
theorem B1240395 : Blo 1238437 1240395 := bstep (se 1 (by rfl) ⟨930296, by rfl⟩ : syracuseStep 1240395 = 1860593) B1860593
theorem B1240407 : Blo 1238437 1240407 := bstep (se 1 (by rfl) ⟨930305, by rfl⟩ : syracuseStep 1240407 = 1860611) B1860611
theorem B1240427 : Blo 1238437 1240427 := bstep (se 1 (by rfl) ⟨930320, by rfl⟩ : syracuseStep 1240427 = 1860641) B1860641
theorem B2092439 : Blo 1238437 2092439 := bstep (se 1 (by rfl) ⟨1569329, by rfl⟩ : syracuseStep 2092439 = 3138659) B3138659
theorem B2788811 : Blo 1238437 2788811 := bstep (se 1 (by rfl) ⟨2091608, by rfl⟩ : syracuseStep 2788811 = 4183217) B4183217
theorem B4238813 : Blo 1238437 4238813 := bstep (se 3 (by rfl) ⟨794777, by rfl⟩ : syracuseStep 4238813 = 1589555) B1589555
theorem B2788865 : Blo 1238437 2788865 := bstep (se 2 (by rfl) ⟨1045824, by rfl⟩ : syracuseStep 2788865 = 2091649) B2091649
theorem B1764875 : Blo 1238437 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B2092567 : Blo 1238437 2092567 := bstep (se 1 (by rfl) ⟨1569425, by rfl⟩ : syracuseStep 2092567 = 3138851) B3138851
theorem B6786605 : Blo 1238437 6786605 := bstep (se 3 (by rfl) ⟨1272488, by rfl⟩ : syracuseStep 6786605 = 2544977) B2544977
theorem B4181597 : Blo 1238437 4181597 := bstep (se 3 (by rfl) ⟨784049, by rfl⟩ : syracuseStep 4181597 = 1568099) B1568099
theorem B24161885 : Blo 1238437 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B6704819 : Blo 1238437 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B2789081 : Blo 1238437 2789081 := bstep (se 2 (by rfl) ⟨1045905, by rfl⟩ : syracuseStep 2789081 = 2091811) B2091811
theorem B1257239 : Blo 1238437 1257239 := bstep (se 1 (by rfl) ⟨942929, by rfl⟩ : syracuseStep 1257239 = 1885859) B1885859
theorem B6278957 : Blo 1238437 6278957 := bstep (se 3 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 6278957 = 2354609) B2354609
theorem B2789171 : Blo 1238437 2789171 := bstep (se 1 (by rfl) ⟨2091878, by rfl⟩ : syracuseStep 2789171 = 4183757) B4183757
theorem B1257271 : Blo 1238437 1257271 := bstep (se 1 (by rfl) ⟨942953, by rfl⟩ : syracuseStep 1257271 = 1885907) B1885907
theorem B2789207 : Blo 1238437 2789207 := bstep (se 1 (by rfl) ⟨2091905, by rfl⟩ : syracuseStep 2789207 = 4183811) B4183811
theorem B7941989 : Blo 1238437 7941989 := bstep (se 4 (by rfl) ⟨744561, by rfl⟩ : syracuseStep 7941989 = 1489123) B1489123
theorem B20107187 : Blo 1238437 20107187 := bstep (se 1 (by rfl) ⟨15080390, by rfl⟩ : syracuseStep 20107187 = 30160781) B30160781
theorem B9408473 : Blo 1238437 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B2789387 : Blo 1238437 2789387 := bstep (se 1 (by rfl) ⟨2092040, by rfl⟩ : syracuseStep 2789387 = 4184081) B4184081
theorem B2789441 : Blo 1238437 2789441 := bstep (se 2 (by rfl) ⟨1046040, by rfl⟩ : syracuseStep 2789441 = 2092081) B2092081
theorem B11300957 : Blo 1238437 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B2093195 : Blo 1238437 2093195 := bstep (se 1 (by rfl) ⟨1569896, by rfl⟩ : syracuseStep 2093195 = 3139793) B3139793
theorem B2789657 : Blo 1238437 2789657 := bstep (se 2 (by rfl) ⟨1046121, by rfl⟩ : syracuseStep 2789657 = 2092243) B2092243
theorem B2789747 : Blo 1238437 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B1323383 : Blo 1238437 1323383 := bstep (se 1 (by rfl) ⟨992537, by rfl⟩ : syracuseStep 1323383 = 1985075) B1985075
theorem B2789783 : Blo 1238437 2789783 := bstep (se 1 (by rfl) ⟨2092337, by rfl⟩ : syracuseStep 2789783 = 4184675) B4184675
theorem B4706819 : Blo 1238437 4706819 := bstep (se 1 (by rfl) ⟨3530114, by rfl⟩ : syracuseStep 4706819 = 7060229) B7060229
theorem B9417221 : Blo 1238437 9417221 := bstep (se 4 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 9417221 = 1765729) B1765729
theorem B2511371 : Blo 1238437 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B6271505 : Blo 1238437 6271505 := bstep (se 2 (by rfl) ⟨2351814, by rfl⟩ : syracuseStep 6271505 = 4703629) B4703629
theorem B7533121 : Blo 1238437 7533121 := bstep (se 2 (by rfl) ⟨2824920, by rfl⟩ : syracuseStep 7533121 = 5649841) B5649841
theorem B3969611 : Blo 1238437 3969611 := bstep (se 1 (by rfl) ⟨2977208, by rfl⟩ : syracuseStep 3969611 = 5954417) B5954417
theorem B2789963 : Blo 1238437 2789963 := bstep (se 1 (by rfl) ⟨2092472, by rfl⟩ : syracuseStep 2789963 = 4184945) B4184945
theorem B11915869 : Blo 1238437 11915869 := bstep (se 3 (by rfl) ⟨2234225, by rfl⟩ : syracuseStep 11915869 = 4468451) B4468451
theorem B2790017 : Blo 1238437 2790017 := bstep (se 2 (by rfl) ⟨1046256, by rfl⟩ : syracuseStep 2790017 = 2092513) B2092513
theorem B3527347 : Blo 1238437 3527347 := bstep (se 1 (by rfl) ⟨2645510, by rfl⟩ : syracuseStep 3527347 = 5291021) B5291021
theorem B6271667 : Blo 1238437 6271667 := bstep (se 1 (by rfl) ⟨4703750, by rfl⟩ : syracuseStep 6271667 = 9407501) B9407501
theorem B3969739 : Blo 1238437 3969739 := bstep (se 1 (by rfl) ⟨2977304, by rfl⟩ : syracuseStep 3969739 = 5954609) B5954609
theorem B4182731 : Blo 1238437 4182731 := bstep (se 1 (by rfl) ⟨3137048, by rfl⟩ : syracuseStep 4182731 = 6274097) B6274097
theorem B2978507 : Blo 1238437 2978507 := bstep (se 1 (by rfl) ⟨2233880, by rfl⟩ : syracuseStep 2978507 = 4467761) B4467761
theorem B1569547 : Blo 1238437 1569547 := bstep (se 1 (by rfl) ⟨1177160, by rfl⟩ : syracuseStep 1569547 = 2354321) B2354321
theorem B3969815 : Blo 1238437 3969815 := bstep (se 1 (by rfl) ⟨2977361, by rfl⟩ : syracuseStep 3969815 = 5954723) B5954723
theorem B5649203 : Blo 1238437 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B2790233 : Blo 1238437 2790233 := bstep (se 2 (by rfl) ⟨1046337, by rfl⟩ : syracuseStep 2790233 = 2092675) B2092675
theorem B4027229 : Blo 1238437 4027229 := bstep (se 3 (by rfl) ⟨755105, by rfl⟩ : syracuseStep 4027229 = 1510211) B1510211
theorem B2790323 : Blo 1238437 2790323 := bstep (se 1 (by rfl) ⟨2092742, by rfl⟩ : syracuseStep 2790323 = 4185485) B4185485
theorem B2790359 : Blo 1238437 2790359 := bstep (se 1 (by rfl) ⟨2092769, by rfl⟩ : syracuseStep 2790359 = 4185539) B4185539
theorem B4183001 : Blo 1238437 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B13390865 : Blo 1238437 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B1324075 : Blo 1238437 1324075 := bstep (se 1 (by rfl) ⟨993056, by rfl⟩ : syracuseStep 1324075 = 1986113) B1986113
theorem B3224651 : Blo 1238437 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B15275101 : Blo 1238437 15275101 := bstep (se 3 (by rfl) ⟨2864081, by rfl⟩ : syracuseStep 15275101 = 5728163) B5728163
theorem B2790539 : Blo 1238437 2790539 := bstep (se 1 (by rfl) ⟨2092904, by rfl⟩ : syracuseStep 2790539 = 4185809) B4185809
theorem B17855639 : Blo 1238437 17855639 := bstep (se 1 (by rfl) ⟨13391729, by rfl⟩ : syracuseStep 17855639 = 26783459) B26783459
theorem B2790593 : Blo 1238437 2790593 := bstep (se 2 (by rfl) ⟨1046472, by rfl⟩ : syracuseStep 2790593 = 2092945) B2092945
theorem B2790809 : Blo 1238437 2790809 := bstep (se 2 (by rfl) ⟨1046553, by rfl⟩ : syracuseStep 2790809 = 2093107) B2093107
theorem B1488331 : Blo 1238437 1488331 := bstep (se 1 (by rfl) ⟨1116248, by rfl⟩ : syracuseStep 1488331 = 2232497) B2232497
theorem B2790899 : Blo 1238437 2790899 := bstep (se 1 (by rfl) ⟨2093174, by rfl⟩ : syracuseStep 2790899 = 4186349) B4186349
theorem B2790935 : Blo 1238437 2790935 := bstep (se 1 (by rfl) ⟨2093201, by rfl⟩ : syracuseStep 2790935 = 4186403) B4186403
theorem B4838977 : Blo 1238437 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B4183703 : Blo 1238437 4183703 := bstep (se 1 (by rfl) ⟨3137777, by rfl⟩ : syracuseStep 4183703 = 6275555) B6275555
theorem B10884881 : Blo 1238437 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2012953 : Blo 1238437 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B3135307 : Blo 1238437 3135307 := bstep (se 1 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 3135307 = 4702961) B4702961
theorem B2545537 : Blo 1238437 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B6363031 : Blo 1238437 6363031 := bstep (se 1 (by rfl) ⟨4772273, by rfl⟩ : syracuseStep 6363031 = 9544547) B9544547
theorem B3135449 : Blo 1238437 3135449 := bstep (se 2 (by rfl) ⟨1175793, by rfl⟩ : syracuseStep 3135449 = 2351587) B2351587
theorem B1857689 : Blo 1238437 1857689 := bstep (se 2 (by rfl) ⟨696633, by rfl⟩ : syracuseStep 1857689 = 1393267) B1393267
theorem B4184243 : Blo 1238437 4184243 := bstep (se 1 (by rfl) ⟨3138182, by rfl⟩ : syracuseStep 4184243 = 6276365) B6276365
theorem B21174533 : Blo 1238437 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B1857803 : Blo 1238437 1857803 := bstep (se 1 (by rfl) ⟨1393352, by rfl⟩ : syracuseStep 1857803 = 2786705) B2786705
theorem B1857815 : Blo 1238437 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B5290285 : Blo 1238437 5290285 := bstep (se 3 (by rfl) ⟨991928, by rfl⟩ : syracuseStep 5290285 = 1983857) B1983857
theorem B7346477 : Blo 1238437 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B18872621 : Blo 1238437 18872621 := bstep (se 3 (by rfl) ⟨3538616, by rfl⟩ : syracuseStep 18872621 = 7077233) B7077233
theorem B1857881 : Blo 1238437 1857881 := bstep (se 2 (by rfl) ⟨696705, by rfl⟩ : syracuseStep 1857881 = 1393411) B1393411
theorem B2234803 : Blo 1238437 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B4184513 : Blo 1238437 4184513 := bstep (se 2 (by rfl) ⟨1569192, by rfl⟩ : syracuseStep 4184513 = 3138385) B3138385
theorem B1857995 : Blo 1238437 1857995 := bstep (se 1 (by rfl) ⟨1393496, by rfl⟩ : syracuseStep 1857995 = 2786993) B2786993
theorem B1858007 : Blo 1238437 1858007 := bstep (se 1 (by rfl) ⟨1393505, by rfl⟩ : syracuseStep 1858007 = 2787011) B2787011
theorem B2120203 : Blo 1238437 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B7543313 : Blo 1238437 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B1858073 : Blo 1238437 1858073 := bstep (se 2 (by rfl) ⟨696777, by rfl⟩ : syracuseStep 1858073 = 1393555) B1393555
theorem B5954093 : Blo 1238437 5954093 := bstep (se 3 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 5954093 = 2232785) B2232785
theorem B6273611 : Blo 1238437 6273611 := bstep (se 1 (by rfl) ⟨4705208, by rfl⟩ : syracuseStep 6273611 = 9410417) B9410417
theorem B10590821 : Blo 1238437 10590821 := bstep (se 4 (by rfl) ⟨992889, by rfl⟩ : syracuseStep 10590821 = 1985779) B1985779
theorem B1858187 : Blo 1238437 1858187 := bstep (se 1 (by rfl) ⟨1393640, by rfl⟩ : syracuseStep 1858187 = 2787281) B2787281
theorem B1858199 : Blo 1238437 1858199 := bstep (se 1 (by rfl) ⟨1393649, by rfl⟩ : syracuseStep 1858199 = 2787299) B2787299
theorem B9173683 : Blo 1238437 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B1858265 : Blo 1238437 1858265 := bstep (se 2 (by rfl) ⟨696849, by rfl⟩ : syracuseStep 1858265 = 1393699) B1393699
theorem B2235097 : Blo 1238437 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B3136279 : Blo 1238437 3136279 := bstep (se 1 (by rfl) ⟨2352209, by rfl⟩ : syracuseStep 3136279 = 4704419) B4704419
theorem B8936237 : Blo 1238437 8936237 := bstep (se 3 (by rfl) ⟨1675544, by rfl⟩ : syracuseStep 8936237 = 3351089) B3351089
theorem B1858379 : Blo 1238437 1858379 := bstep (se 1 (by rfl) ⟨1393784, by rfl⟩ : syracuseStep 1858379 = 2787569) B2787569
theorem B1858391 : Blo 1238437 1858391 := bstep (se 1 (by rfl) ⟨1393793, by rfl⟩ : syracuseStep 1858391 = 2787587) B2787587
theorem B1858457 : Blo 1238437 1858457 := bstep (se 2 (by rfl) ⟨696921, by rfl⟩ : syracuseStep 1858457 = 1393843) B1393843
theorem B4185053 : Blo 1238437 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B1858571 : Blo 1238437 1858571 := bstep (se 1 (by rfl) ⟨1393928, by rfl⟩ : syracuseStep 1858571 = 2787857) B2787857
theorem B1858583 : Blo 1238437 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B1858649 : Blo 1238437 1858649 := bstep (se 2 (by rfl) ⟨696993, by rfl⟩ : syracuseStep 1858649 = 1393987) B1393987
theorem B45227159 : Blo 1238437 45227159 := bstep (se 1 (by rfl) ⟨33920369, by rfl⟩ : syracuseStep 45227159 = 67840739) B67840739
theorem B1858763 : Blo 1238437 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B3136715 : Blo 1238437 3136715 := bstep (se 1 (by rfl) ⟨2352536, by rfl⟩ : syracuseStep 3136715 = 4705073) B4705073
theorem B1490123 : Blo 1238437 1490123 := bstep (se 1 (by rfl) ⟨1117592, by rfl⟩ : syracuseStep 1490123 = 2235185) B2235185
theorem B1858775 : Blo 1238437 1858775 := bstep (se 1 (by rfl) ⟨1394081, by rfl⟩ : syracuseStep 1858775 = 2788163) B2788163
theorem B10591505 : Blo 1238437 10591505 := bstep (se 2 (by rfl) ⟨3971814, by rfl⟩ : syracuseStep 10591505 = 7943629) B7943629
theorem B1858841 : Blo 1238437 1858841 := bstep (se 2 (by rfl) ⟨697065, by rfl⟩ : syracuseStep 1858841 = 1394131) B1394131
theorem B9411875 : Blo 1238437 9411875 := bstep (se 1 (by rfl) ⟨7058906, by rfl⟩ : syracuseStep 9411875 = 14117813) B14117813
theorem B1858955 : Blo 1238437 1858955 := bstep (se 1 (by rfl) ⟨1394216, by rfl⟩ : syracuseStep 1858955 = 2788433) B2788433
theorem B2645399 : Blo 1238437 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B1858967 : Blo 1238437 1858967 := bstep (se 1 (by rfl) ⟨1394225, by rfl⟩ : syracuseStep 1858967 = 2788451) B2788451
theorem B1859033 : Blo 1238437 1859033 := bstep (se 2 (by rfl) ⟨697137, by rfl⟩ : syracuseStep 1859033 = 1394275) B1394275
theorem B3530263 : Blo 1238437 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B1433143 : Blo 1238437 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B3137089 : Blo 1238437 3137089 := bstep (se 2 (by rfl) ⟨1176408, by rfl⟩ : syracuseStep 3137089 = 2352817) B2352817
theorem B1859147 : Blo 1238437 1859147 := bstep (se 1 (by rfl) ⟨1394360, by rfl⟩ : syracuseStep 1859147 = 2788721) B2788721
theorem B1859159 : Blo 1238437 1859159 := bstep (se 1 (by rfl) ⟨1394369, by rfl⟩ : syracuseStep 1859159 = 2788739) B2788739
theorem B1859225 : Blo 1238437 1859225 := bstep (se 2 (by rfl) ⟨697209, by rfl⟩ : syracuseStep 1859225 = 1394419) B1394419
theorem B1859339 : Blo 1238437 1859339 := bstep (se 1 (by rfl) ⟨1394504, by rfl⟩ : syracuseStep 1859339 = 2789009) B2789009
theorem B1859351 : Blo 1238437 1859351 := bstep (se 1 (by rfl) ⟨1394513, by rfl⟩ : syracuseStep 1859351 = 2789027) B2789027
theorem B1859417 : Blo 1238437 1859417 := bstep (se 2 (by rfl) ⟨697281, by rfl⟩ : syracuseStep 1859417 = 1394563) B1394563
theorem B2645963 : Blo 1238437 2645963 := bstep (se 1 (by rfl) ⟨1984472, by rfl⟩ : syracuseStep 2645963 = 3968945) B3968945
theorem B1859531 : Blo 1238437 1859531 := bstep (se 1 (by rfl) ⟨1394648, by rfl⟩ : syracuseStep 1859531 = 2789297) B2789297
theorem B1859543 : Blo 1238437 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B5291993 : Blo 1238437 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B3530753 : Blo 1238437 3530753 := bstep (se 2 (by rfl) ⟨1324032, by rfl⟩ : syracuseStep 3530753 = 2648065) B2648065
theorem B1859591 : Blo 1238437 1859591 := bstep (se 1 (by rfl) ⟨1394693, by rfl⟩ : syracuseStep 1859591 = 2789387) B2789387
theorem B1589263 : Blo 1238437 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B1859627 : Blo 1238437 1859627 := bstep (se 1 (by rfl) ⟨1394720, by rfl⟩ : syracuseStep 1859627 = 2789441) B2789441
theorem B1859657 : Blo 1238437 1859657 := bstep (se 2 (by rfl) ⟨697371, by rfl⟩ : syracuseStep 1859657 = 1394743) B1394743
theorem B1859771 : Blo 1238437 1859771 := bstep (se 1 (by rfl) ⟨1394828, by rfl⟩ : syracuseStep 1859771 = 2789657) B2789657
theorem B3137737 : Blo 1238437 3137737 := bstep (se 2 (by rfl) ⟨1176651, by rfl⟩ : syracuseStep 3137737 = 2353303) B2353303
theorem B4702445 : Blo 1238437 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B1859831 : Blo 1238437 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B1859855 : Blo 1238437 1859855 := bstep (se 1 (by rfl) ⟨1394891, by rfl⟩ : syracuseStep 1859855 = 2789783) B2789783
theorem B7643429 : Blo 1238437 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B1859897 : Blo 1238437 1859897 := bstep (se 2 (by rfl) ⟨697461, by rfl⟩ : syracuseStep 1859897 = 1394923) B1394923
theorem B3137879 : Blo 1238437 3137879 := bstep (se 1 (by rfl) ⟨2353409, by rfl⟩ : syracuseStep 3137879 = 4706819) B4706819
theorem B2646407 : Blo 1238437 2646407 := bstep (se 1 (by rfl) ⟨1984805, by rfl⟩ : syracuseStep 2646407 = 3969611) B3969611
theorem B1859975 : Blo 1238437 1859975 := bstep (se 1 (by rfl) ⟨1394981, by rfl⟩ : syracuseStep 1859975 = 2789963) B2789963
theorem B7053713 : Blo 1238437 7053713 := bstep (se 2 (by rfl) ⟨2645142, by rfl⟩ : syracuseStep 7053713 = 5290285) B5290285
theorem B1860011 : Blo 1238437 1860011 := bstep (se 1 (by rfl) ⟨1395008, by rfl⟩ : syracuseStep 1860011 = 2790017) B2790017
theorem B1860041 : Blo 1238437 1860041 := bstep (se 2 (by rfl) ⟨697515, by rfl⟩ : syracuseStep 1860041 = 1395031) B1395031
theorem B3973661 : Blo 1238437 3973661 := bstep (se 3 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 3973661 = 1490123) B1490123
theorem B1860155 : Blo 1238437 1860155 := bstep (se 1 (by rfl) ⟨1395116, by rfl⟩ : syracuseStep 1860155 = 2790233) B2790233
theorem B1860215 : Blo 1238437 1860215 := bstep (se 1 (by rfl) ⟨1395161, by rfl⟩ : syracuseStep 1860215 = 2790323) B2790323
theorem B1860239 : Blo 1238437 1860239 := bstep (se 1 (by rfl) ⟨1395179, by rfl⟩ : syracuseStep 1860239 = 2790359) B2790359
theorem B2826937 : Blo 1238437 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B1393339 : Blo 1238437 1393339 := bstep (se 1 (by rfl) ⟨1045004, by rfl⟩ : syracuseStep 1393339 = 2090009) B2090009
theorem B1860281 : Blo 1238437 1860281 := bstep (se 2 (by rfl) ⟨697605, by rfl⟩ : syracuseStep 1860281 = 1395211) B1395211
theorem B10044161 : Blo 1238437 10044161 := bstep (se 2 (by rfl) ⟨3766560, by rfl⟩ : syracuseStep 10044161 = 7533121) B7533121
theorem B1860359 : Blo 1238437 1860359 := bstep (se 1 (by rfl) ⟨1395269, by rfl⟩ : syracuseStep 1860359 = 2790539) B2790539
theorem B11903759 : Blo 1238437 11903759 := bstep (se 1 (by rfl) ⟨8927819, by rfl⟩ : syracuseStep 11903759 = 17855639) B17855639
theorem B1860395 : Blo 1238437 1860395 := bstep (se 1 (by rfl) ⟨1395296, by rfl⟩ : syracuseStep 1860395 = 2790593) B2790593
theorem B1860425 : Blo 1238437 1860425 := bstep (se 2 (by rfl) ⟨697659, by rfl⟩ : syracuseStep 1860425 = 1395319) B1395319
theorem B5292935 : Blo 1238437 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B12231577 : Blo 1238437 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B4703129 : Blo 1238437 4703129 := bstep (se 2 (by rfl) ⟨1763673, by rfl⟩ : syracuseStep 4703129 = 3527347) B3527347
theorem B21767093 : Blo 1238437 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B5292985 : Blo 1238437 5292985 := bstep (se 2 (by rfl) ⟨1984869, by rfl⟩ : syracuseStep 5292985 = 3969739) B3969739
theorem B1860539 : Blo 1238437 1860539 := bstep (se 1 (by rfl) ⟨1395404, by rfl⟩ : syracuseStep 1860539 = 2790809) B2790809
theorem B2352073 : Blo 1238437 2352073 := bstep (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) B1764055
theorem B3531721 : Blo 1238437 3531721 := bstep (se 2 (by rfl) ⟨1324395, by rfl⟩ : syracuseStep 3531721 = 2648791) B2648791
theorem B80413667 : Blo 1238437 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B1860599 : Blo 1238437 1860599 := bstep (se 1 (by rfl) ⟨1395449, by rfl⟩ : syracuseStep 1860599 = 2790899) B2790899
theorem B3179521 : Blo 1238437 3179521 := bstep (se 2 (by rfl) ⟨1192320, by rfl⟩ : syracuseStep 3179521 = 2384641) B2384641
theorem B1860623 : Blo 1238437 1860623 := bstep (se 1 (by rfl) ⟨1395467, by rfl⟩ : syracuseStep 1860623 = 2790935) B2790935
theorem B7054397 : Blo 1238437 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B11920517 : Blo 1238437 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B1393807 : Blo 1238437 1393807 := bstep (se 1 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 1393807 = 2090711) B2090711
theorem B2786489 : Blo 1238437 2786489 := bstep (se 2 (by rfl) ⟨1044933, by rfl⟩ : syracuseStep 2786489 = 2089867) B2089867
theorem B2090299 : Blo 1238437 2090299 := bstep (se 1 (by rfl) ⟨1567724, by rfl⟩ : syracuseStep 2090299 = 3135449) B3135449
theorem B15893819 : Blo 1238437 15893819 := bstep (se 1 (by rfl) ⟨11920364, by rfl⟩ : syracuseStep 15893819 = 23840729) B23840729
theorem B171738481 : Blo 1238437 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B11306425 : Blo 1238437 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B1238459 : Blo 1238437 1238459 := bstep (se 1 (by rfl) ⟨928844, by rfl⟩ : syracuseStep 1238459 = 1857689) B1857689
theorem B2090441 : Blo 1238437 2090441 := bstep (se 2 (by rfl) ⟨783915, by rfl⟩ : syracuseStep 2090441 = 1567831) B1567831
theorem B20366801 : Blo 1238437 20366801 := bstep (se 2 (by rfl) ⟨7637550, by rfl⟩ : syracuseStep 20366801 = 15275101) B15275101
theorem B14116355 : Blo 1238437 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B7538179 : Blo 1238437 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B1238535 : Blo 1238437 1238535 := bstep (se 1 (by rfl) ⟨928901, by rfl⟩ : syracuseStep 1238535 = 1857803) B1857803
theorem B1238543 : Blo 1238437 1238543 := bstep (se 1 (by rfl) ⟨928907, by rfl⟩ : syracuseStep 1238543 = 1857815) B1857815
theorem B2786831 : Blo 1238437 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B2786849 : Blo 1238437 2786849 := bstep (se 2 (by rfl) ⟨1045068, by rfl⟩ : syracuseStep 2786849 = 2090137) B2090137
theorem B1238587 : Blo 1238437 1238587 := bstep (se 1 (by rfl) ⟨928940, by rfl⟩ : syracuseStep 1238587 = 1857881) B1857881
theorem B1238663 : Blo 1238437 1238663 := bstep (se 1 (by rfl) ⟨928997, by rfl⟩ : syracuseStep 1238663 = 1857995) B1857995
theorem B1394311 : Blo 1238437 1394311 := bstep (se 1 (by rfl) ⟨1045733, by rfl⟩ : syracuseStep 1394311 = 2091467) B2091467
theorem B1238671 : Blo 1238437 1238671 := bstep (se 1 (by rfl) ⟨929003, by rfl⟩ : syracuseStep 1238671 = 1858007) B1858007
theorem B1238715 : Blo 1238437 1238715 := bstep (se 1 (by rfl) ⟨929036, by rfl⟩ : syracuseStep 1238715 = 1858073) B1858073
theorem B1238791 : Blo 1238437 1238791 := bstep (se 1 (by rfl) ⟨929093, by rfl⟩ : syracuseStep 1238791 = 1858187) B1858187
theorem B1238799 : Blo 1238437 1238799 := bstep (se 1 (by rfl) ⟨929099, by rfl⟩ : syracuseStep 1238799 = 1858199) B1858199
theorem B1238843 : Blo 1238437 1238843 := bstep (se 1 (by rfl) ⟨929132, by rfl⟩ : syracuseStep 1238843 = 1858265) B1858265
theorem B1394491 : Blo 1238437 1394491 := bstep (se 1 (by rfl) ⟨1045868, by rfl⟩ : syracuseStep 1394491 = 2091737) B2091737
theorem B3770171 : Blo 1238437 3770171 := bstep (se 1 (by rfl) ⟨2827628, by rfl⟩ : syracuseStep 3770171 = 5655257) B5655257
theorem B4704115 : Blo 1238437 4704115 := bstep (se 1 (by rfl) ⟨3528086, by rfl⟩ : syracuseStep 4704115 = 7056173) B7056173
theorem B5957491 : Blo 1238437 5957491 := bstep (se 1 (by rfl) ⟨4468118, by rfl⟩ : syracuseStep 5957491 = 8936237) B8936237
theorem B2787191 : Blo 1238437 2787191 := bstep (se 1 (by rfl) ⟨2090393, by rfl⟩ : syracuseStep 2787191 = 4180787) B4180787
theorem B1238919 : Blo 1238437 1238919 := bstep (se 1 (by rfl) ⟨929189, by rfl⟩ : syracuseStep 1238919 = 1858379) B1858379
theorem B1238927 : Blo 1238437 1238927 := bstep (se 1 (by rfl) ⟨929195, by rfl⟩ : syracuseStep 1238927 = 1858391) B1858391
theorem B1984441 : Blo 1238437 1984441 := bstep (se 2 (by rfl) ⟨744165, by rfl⟩ : syracuseStep 1984441 = 1488331) B1488331
theorem B1238971 : Blo 1238437 1238971 := bstep (se 1 (by rfl) ⟨929228, by rfl⟩ : syracuseStep 1238971 = 1858457) B1858457
theorem B1239047 : Blo 1238437 1239047 := bstep (se 1 (by rfl) ⟨929285, by rfl⟩ : syracuseStep 1239047 = 1858571) B1858571
theorem B1239055 : Blo 1238437 1239055 := bstep (se 1 (by rfl) ⟨929291, by rfl⟩ : syracuseStep 1239055 = 1858583) B1858583
theorem B2787371 : Blo 1238437 2787371 := bstep (se 1 (by rfl) ⟨2090528, by rfl⟩ : syracuseStep 2787371 = 4181057) B4181057
theorem B1239099 : Blo 1238437 1239099 := bstep (se 1 (by rfl) ⟨929324, by rfl⟩ : syracuseStep 1239099 = 1858649) B1858649
theorem B10586173 : Blo 1238437 10586173 := bstep (se 3 (by rfl) ⟨1984907, by rfl⟩ : syracuseStep 10586173 = 3969815) B3969815
theorem B3352637 : Blo 1238437 3352637 := bstep (se 3 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 3352637 = 1257239) B1257239
theorem B1239175 : Blo 1238437 1239175 := bstep (se 1 (by rfl) ⟨929381, by rfl⟩ : syracuseStep 1239175 = 1858763) B1858763
theorem B2091143 : Blo 1238437 2091143 := bstep (se 1 (by rfl) ⟨1568357, by rfl⟩ : syracuseStep 2091143 = 3136715) B3136715
theorem B1239183 : Blo 1238437 1239183 := bstep (se 1 (by rfl) ⟨929387, by rfl⟩ : syracuseStep 1239183 = 1858775) B1858775
theorem B1239227 : Blo 1238437 1239227 := bstep (se 1 (by rfl) ⟨929420, by rfl⟩ : syracuseStep 1239227 = 1858841) B1858841
theorem B5294317 : Blo 1238437 5294317 := bstep (se 3 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 5294317 = 1985369) B1985369
theorem B1239303 : Blo 1238437 1239303 := bstep (se 1 (by rfl) ⟨929477, by rfl⟩ : syracuseStep 1239303 = 1858955) B1858955
theorem B1239311 : Blo 1238437 1239311 := bstep (se 1 (by rfl) ⟨929483, by rfl⟩ : syracuseStep 1239311 = 1858967) B1858967
theorem B1394959 : Blo 1238437 1394959 := bstep (se 1 (by rfl) ⟨1046219, by rfl⟩ : syracuseStep 1394959 = 2092439) B2092439
theorem B1239355 : Blo 1238437 1239355 := bstep (se 1 (by rfl) ⟨929516, by rfl⟩ : syracuseStep 1239355 = 1859033) B1859033
theorem B4524403 : Blo 1238437 4524403 := bstep (se 1 (by rfl) ⟨3393302, by rfl⟩ : syracuseStep 4524403 = 6786605) B6786605
theorem B1239431 : Blo 1238437 1239431 := bstep (se 1 (by rfl) ⟨929573, by rfl⟩ : syracuseStep 1239431 = 1859147) B1859147
theorem B1239439 : Blo 1238437 1239439 := bstep (se 1 (by rfl) ⟨929579, by rfl⟩ : syracuseStep 1239439 = 1859159) B1859159
theorem B2787731 : Blo 1238437 2787731 := bstep (se 1 (by rfl) ⟨2090798, by rfl⟩ : syracuseStep 2787731 = 4181597) B4181597
theorem B16107923 : Blo 1238437 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B4180409 : Blo 1238437 4180409 := bstep (se 2 (by rfl) ⟨1567653, by rfl⟩ : syracuseStep 4180409 = 3135307) B3135307
theorem B1239483 : Blo 1238437 1239483 := bstep (se 1 (by rfl) ⟨929612, by rfl⟩ : syracuseStep 1239483 = 1859225) B1859225
theorem B2787785 : Blo 1238437 2787785 := bstep (se 2 (by rfl) ⟨1045419, by rfl⟩ : syracuseStep 2787785 = 2090839) B2090839
theorem B6449629 : Blo 1238437 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B3394049 : Blo 1238437 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B1239559 : Blo 1238437 1239559 := bstep (se 1 (by rfl) ⟨929669, by rfl⟩ : syracuseStep 1239559 = 1859339) B1859339
theorem B1239567 : Blo 1238437 1239567 := bstep (se 1 (by rfl) ⟨929675, by rfl⟩ : syracuseStep 1239567 = 1859351) B1859351
theorem B6277661 : Blo 1238437 6277661 := bstep (se 3 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 6277661 = 2354123) B2354123
theorem B1239611 : Blo 1238437 1239611 := bstep (se 1 (by rfl) ⟨929708, by rfl⟩ : syracuseStep 1239611 = 1859417) B1859417
theorem B5294659 : Blo 1238437 5294659 := bstep (se 1 (by rfl) ⟨3970994, by rfl⟩ : syracuseStep 5294659 = 7941989) B7941989
theorem B13404791 : Blo 1238437 13404791 := bstep (se 1 (by rfl) ⟨10053593, by rfl⟩ : syracuseStep 13404791 = 20107187) B20107187
theorem B1763975 : Blo 1238437 1763975 := bstep (se 1 (by rfl) ⟨1322981, by rfl⟩ : syracuseStep 1763975 = 2645963) B2645963
theorem B1239687 : Blo 1238437 1239687 := bstep (se 1 (by rfl) ⟨929765, by rfl⟩ : syracuseStep 1239687 = 1859531) B1859531
theorem B1239695 : Blo 1238437 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B1239739 : Blo 1238437 1239739 := bstep (se 1 (by rfl) ⟨929804, by rfl⟩ : syracuseStep 1239739 = 1859609) B1859609
theorem B1239815 : Blo 1238437 1239815 := bstep (se 1 (by rfl) ⟨929861, by rfl⟩ : syracuseStep 1239815 = 1859723) B1859723
theorem B1395463 : Blo 1238437 1395463 := bstep (se 1 (by rfl) ⟨1046597, by rfl⟩ : syracuseStep 1395463 = 2093195) B2093195
theorem B2091791 : Blo 1238437 2091791 := bstep (se 1 (by rfl) ⟨1568843, by rfl⟩ : syracuseStep 2091791 = 3137687) B3137687
theorem B1239823 : Blo 1238437 1239823 := bstep (se 1 (by rfl) ⟨929867, by rfl⟩ : syracuseStep 1239823 = 1859735) B1859735
theorem B7940915 : Blo 1238437 7940915 := bstep (se 1 (by rfl) ⟨5955686, by rfl⟩ : syracuseStep 7940915 = 11911373) B11911373
theorem B1239867 : Blo 1238437 1239867 := bstep (se 1 (by rfl) ⟨929900, by rfl⟩ : syracuseStep 1239867 = 1859801) B1859801
theorem B1239943 : Blo 1238437 1239943 := bstep (se 1 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 1239943 = 1859915) B1859915
theorem B1239951 : Blo 1238437 1239951 := bstep (se 1 (by rfl) ⟨929963, by rfl⟩ : syracuseStep 1239951 = 1859927) B1859927
theorem B1764283 : Blo 1238437 1764283 := bstep (se 1 (by rfl) ⟨1323212, by rfl⟩ : syracuseStep 1764283 = 2646425) B2646425
theorem B1239995 : Blo 1238437 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B6278147 : Blo 1238437 6278147 := bstep (se 1 (by rfl) ⟨4708610, by rfl⟩ : syracuseStep 6278147 = 9417221) B9417221
theorem B1674247 : Blo 1238437 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B1240071 : Blo 1238437 1240071 := bstep (se 1 (by rfl) ⟨930053, by rfl⟩ : syracuseStep 1240071 = 1860107) B1860107
theorem B4181003 : Blo 1238437 4181003 := bstep (se 1 (by rfl) ⟨3135752, by rfl⟩ : syracuseStep 4181003 = 6271505) B6271505
theorem B1240079 : Blo 1238437 1240079 := bstep (se 1 (by rfl) ⟨930059, by rfl⟩ : syracuseStep 1240079 = 1860119) B1860119
theorem B1240123 : Blo 1238437 1240123 := bstep (se 1 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 1240123 = 1860185) B1860185
theorem B4181111 : Blo 1238437 4181111 := bstep (se 1 (by rfl) ⟨3135833, by rfl⟩ : syracuseStep 4181111 = 6271667) B6271667
theorem B2788487 : Blo 1238437 2788487 := bstep (se 1 (by rfl) ⟨2091365, by rfl⟩ : syracuseStep 2788487 = 4182731) B4182731
theorem B1985671 : Blo 1238437 1985671 := bstep (se 1 (by rfl) ⟨1489253, by rfl⟩ : syracuseStep 1985671 = 2978507) B2978507
theorem B1240199 : Blo 1238437 1240199 := bstep (se 1 (by rfl) ⟨930149, by rfl⟩ : syracuseStep 1240199 = 1860299) B1860299
theorem B1240207 : Blo 1238437 1240207 := bstep (se 1 (by rfl) ⟨930155, by rfl⟩ : syracuseStep 1240207 = 1860311) B1860311
theorem B1256635 : Blo 1238437 1256635 := bstep (se 1 (by rfl) ⟨942476, by rfl⟩ : syracuseStep 1256635 = 1884953) B1884953
theorem B1240251 : Blo 1238437 1240251 := bstep (se 1 (by rfl) ⟨930188, by rfl⟩ : syracuseStep 1240251 = 1860377) B1860377
theorem B6270209 : Blo 1238437 6270209 := bstep (se 2 (by rfl) ⟨2351328, by rfl⟩ : syracuseStep 6270209 = 4702657) B4702657
theorem B1240327 : Blo 1238437 1240327 := bstep (se 1 (by rfl) ⟨930245, by rfl⟩ : syracuseStep 1240327 = 1860491) B1860491
theorem B1240335 : Blo 1238437 1240335 := bstep (se 1 (by rfl) ⟨930251, by rfl⟩ : syracuseStep 1240335 = 1860503) B1860503
theorem B2092331 : Blo 1238437 2092331 := bstep (se 1 (by rfl) ⟨1569248, by rfl⟩ : syracuseStep 2092331 = 3138497) B3138497
theorem B2788667 : Blo 1238437 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B1240379 : Blo 1238437 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B2354579 : Blo 1238437 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B2788793 : Blo 1238437 2788793 := bstep (se 2 (by rfl) ⟨1045797, by rfl⟩ : syracuseStep 2788793 = 2091595) B2091595
theorem B19590605 : Blo 1238437 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B15887825 : Blo 1238437 15887825 := bstep (se 2 (by rfl) ⟨5957934, by rfl⟩ : syracuseStep 15887825 = 11915869) B11915869
theorem B2354807 : Blo 1238437 2354807 := bstep (se 1 (by rfl) ⟨1766105, by rfl⟩ : syracuseStep 2354807 = 3532211) B3532211
theorem B2092729 : Blo 1238437 2092729 := bstep (se 2 (by rfl) ⟨784773, by rfl⟩ : syracuseStep 2092729 = 1569547) B1569547
theorem B4181705 : Blo 1238437 4181705 := bstep (se 2 (by rfl) ⟨1568139, by rfl⟩ : syracuseStep 4181705 = 3136279) B3136279
theorem B2789135 : Blo 1238437 2789135 := bstep (se 1 (by rfl) ⟨2091851, by rfl⟩ : syracuseStep 2789135 = 4183703) B4183703
theorem B2789153 : Blo 1238437 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B15085349 : Blo 1238437 15085349 := bstep (se 4 (by rfl) ⟨1414251, by rfl⟩ : syracuseStep 15085349 = 2828503) B2828503
theorem B1322939 : Blo 1238437 1322939 := bstep (se 1 (by rfl) ⟨992204, by rfl⟩ : syracuseStep 1322939 = 1984409) B1984409
theorem B2682895 : Blo 1238437 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B4706333 : Blo 1238437 4706333 := bstep (se 3 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 4706333 = 1764875) B1764875
theorem B6271019 : Blo 1238437 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B1765433 : Blo 1238437 1765433 := bstep (se 2 (by rfl) ⟨662037, by rfl⟩ : syracuseStep 1765433 = 1324075) B1324075
theorem B2789495 : Blo 1238437 2789495 := bstep (se 1 (by rfl) ⟨2092121, by rfl⟩ : syracuseStep 2789495 = 4184243) B4184243
theorem B6705445 : Blo 1238437 6705445 := bstep (se 4 (by rfl) ⟨628635, by rfl⟩ : syracuseStep 6705445 = 1257271) B1257271
theorem B2789675 : Blo 1238437 2789675 := bstep (se 1 (by rfl) ⟨2092256, by rfl⟩ : syracuseStep 2789675 = 4184513) B4184513
theorem B3969395 : Blo 1238437 3969395 := bstep (se 1 (by rfl) ⟨2977046, by rfl⟩ : syracuseStep 3969395 = 5954093) B5954093
theorem B4182407 : Blo 1238437 4182407 := bstep (se 1 (by rfl) ⟨3136805, by rfl⟩ : syracuseStep 4182407 = 6273611) B6273611
theorem B2790035 : Blo 1238437 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B1569451 : Blo 1238437 1569451 := bstep (se 1 (by rfl) ⟨1177088, by rfl⟩ : syracuseStep 1569451 = 2354177) B2354177
theorem B4707017 : Blo 1238437 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B2790089 : Blo 1238437 2790089 := bstep (se 2 (by rfl) ⟨1046283, by rfl⟩ : syracuseStep 2790089 = 2092567) B2092567
theorem B4182785 : Blo 1238437 4182785 := bstep (se 2 (by rfl) ⟨1568544, by rfl⟩ : syracuseStep 4182785 = 3137089) B3137089
theorem B6451969 : Blo 1238437 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B30151439 : Blo 1238437 30151439 := bstep (se 1 (by rfl) ⟨22613579, by rfl⟩ : syracuseStep 30151439 = 45227159) B45227159
theorem B2683937 : Blo 1238437 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B4469879 : Blo 1238437 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B8484041 : Blo 1238437 8484041 := bstep (se 2 (by rfl) ⟨3181515, by rfl⟩ : syracuseStep 8484041 = 6363031) B6363031
theorem B14111981 : Blo 1238437 14111981 := bstep (se 3 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 14111981 = 5291993) B5291993
theorem B6272315 : Blo 1238437 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B2790791 : Blo 1238437 2790791 := bstep (se 1 (by rfl) ⟨2093093, by rfl⟩ : syracuseStep 2790791 = 4186187) B4186187
theorem B7533971 : Blo 1238437 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B2512313 : Blo 1238437 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B9418193 : Blo 1238437 9418193 := bstep (se 2 (by rfl) ⟨3531822, by rfl⟩ : syracuseStep 9418193 = 7063645) B7063645
theorem B6272477 : Blo 1238437 6272477 := bstep (se 3 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 6272477 = 2352179) B2352179
theorem B8599069 : Blo 1238437 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B4183595 : Blo 1238437 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B2790971 : Blo 1238437 2790971 := bstep (se 1 (by rfl) ⟨2093228, by rfl⟩ : syracuseStep 2790971 = 4186457) B4186457
theorem B24483397 : Blo 1238437 24483397 := bstep (se 4 (by rfl) ⟨2295318, by rfl⟩ : syracuseStep 24483397 = 4590637) B4590637
theorem B3135095 : Blo 1238437 3135095 := bstep (se 1 (by rfl) ⟨2351321, by rfl⟩ : syracuseStep 3135095 = 4702643) B4702643
theorem B4593389 : Blo 1238437 4593389 := bstep (se 3 (by rfl) ⟨861260, by rfl⟩ : syracuseStep 4593389 = 1722521) B1722521
theorem B6272801 : Blo 1238437 6272801 := bstep (se 2 (by rfl) ⟨2352300, by rfl⟩ : syracuseStep 6272801 = 4704601) B4704601
theorem B3766135 : Blo 1238437 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B2684819 : Blo 1238437 2684819 := bstep (se 1 (by rfl) ⟨2013614, by rfl⟩ : syracuseStep 2684819 = 4027229) B4027229
theorem B2979737 : Blo 1238437 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B13408163 : Blo 1238437 13408163 := bstep (se 1 (by rfl) ⟨10056122, by rfl⟩ : syracuseStep 13408163 = 20112245) B20112245
theorem B8927243 : Blo 1238437 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B1857671 : Blo 1238437 1857671 := bstep (se 1 (by rfl) ⟨1393253, by rfl⟩ : syracuseStep 1857671 = 2786507) B2786507
theorem B3528839 : Blo 1238437 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B1857707 : Blo 1238437 1857707 := bstep (se 1 (by rfl) ⟨1393280, by rfl⟩ : syracuseStep 1857707 = 2786561) B2786561
theorem B1857737 : Blo 1238437 1857737 := bstep (se 2 (by rfl) ⟨696651, by rfl⟩ : syracuseStep 1857737 = 1393303) B1393303
theorem B12728593 : Blo 1238437 12728593 := bstep (se 2 (by rfl) ⟨4773222, by rfl⟩ : syracuseStep 12728593 = 9546445) B9546445
theorem B1857851 : Blo 1238437 1857851 := bstep (se 1 (by rfl) ⟨1393388, by rfl⟩ : syracuseStep 1857851 = 2786777) B2786777
theorem B3529021 : Blo 1238437 3529021 := bstep (se 3 (by rfl) ⟨661691, by rfl⟩ : syracuseStep 3529021 = 1323383) B1323383
theorem B1857911 : Blo 1238437 1857911 := bstep (se 1 (by rfl) ⟨1393433, by rfl⟩ : syracuseStep 1857911 = 2786867) B2786867
theorem B3529079 : Blo 1238437 3529079 := bstep (se 1 (by rfl) ⟨2646809, by rfl⟩ : syracuseStep 3529079 = 5293619) B5293619
theorem B1857935 : Blo 1238437 1857935 := bstep (se 1 (by rfl) ⟨1393451, by rfl⟩ : syracuseStep 1857935 = 2786903) B2786903
theorem B1857977 : Blo 1238437 1857977 := bstep (se 2 (by rfl) ⟨696741, by rfl⟩ : syracuseStep 1857977 = 1393483) B1393483
theorem B4708793 : Blo 1238437 4708793 := bstep (se 2 (by rfl) ⟨1765797, by rfl⟩ : syracuseStep 4708793 = 3531595) B3531595
theorem B1858055 : Blo 1238437 1858055 := bstep (se 1 (by rfl) ⟨1393541, by rfl⟩ : syracuseStep 1858055 = 2787083) B2787083
theorem B7256587 : Blo 1238437 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B7936555 : Blo 1238437 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B1858091 : Blo 1238437 1858091 := bstep (se 1 (by rfl) ⟨1393568, by rfl⟩ : syracuseStep 1858091 = 2787137) B2787137
theorem B1858121 : Blo 1238437 1858121 := bstep (se 2 (by rfl) ⟨696795, by rfl⟩ : syracuseStep 1858121 = 1393591) B1393591
theorem B11303501 : Blo 1238437 11303501 := bstep (se 3 (by rfl) ⟨2119406, by rfl⟩ : syracuseStep 11303501 = 4238813) B4238813
theorem B1858235 : Blo 1238437 1858235 := bstep (se 1 (by rfl) ⟨1393676, by rfl⟩ : syracuseStep 1858235 = 2787353) B2787353
theorem B10582757 : Blo 1238437 10582757 := bstep (se 4 (by rfl) ⟨992133, by rfl⟩ : syracuseStep 10582757 = 1984267) B1984267
theorem B6273773 : Blo 1238437 6273773 := bstep (se 3 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 6273773 = 2352665) B2352665
theorem B1858295 : Blo 1238437 1858295 := bstep (se 1 (by rfl) ⟨1393721, by rfl⟩ : syracuseStep 1858295 = 2787443) B2787443
theorem B7944961 : Blo 1238437 7944961 := bstep (se 2 (by rfl) ⟨2979360, by rfl⟩ : syracuseStep 7944961 = 5958721) B5958721
theorem B1858319 : Blo 1238437 1858319 := bstep (se 1 (by rfl) ⟨1393739, by rfl⟩ : syracuseStep 1858319 = 2787479) B2787479
theorem B3971855 : Blo 1238437 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B1858361 : Blo 1238437 1858361 := bstep (se 2 (by rfl) ⟨696885, by rfl⟩ : syracuseStep 1858361 = 1393771) B1393771
theorem B4184891 : Blo 1238437 4184891 := bstep (se 1 (by rfl) ⟨3138668, by rfl⟩ : syracuseStep 4184891 = 6277337) B6277337
theorem B12581747 : Blo 1238437 12581747 := bstep (se 1 (by rfl) ⟨9436310, by rfl⟩ : syracuseStep 12581747 = 18872621) B18872621
theorem B1858439 : Blo 1238437 1858439 := bstep (se 1 (by rfl) ⟨1393829, by rfl⟩ : syracuseStep 1858439 = 2787659) B2787659
theorem B3136391 : Blo 1238437 3136391 := bstep (se 1 (by rfl) ⟨2352293, by rfl⟩ : syracuseStep 3136391 = 4704587) B4704587
theorem B1858475 : Blo 1238437 1858475 := bstep (se 1 (by rfl) ⟨1393856, by rfl⟩ : syracuseStep 1858475 = 2787713) B2787713
theorem B3136441 : Blo 1238437 3136441 := bstep (se 2 (by rfl) ⟨1176165, by rfl⟩ : syracuseStep 3136441 = 2352331) B2352331
theorem B1858505 : Blo 1238437 1858505 := bstep (se 2 (by rfl) ⟨696939, by rfl⟩ : syracuseStep 1858505 = 1393879) B1393879
theorem B5028875 : Blo 1238437 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B1858619 : Blo 1238437 1858619 := bstep (se 1 (by rfl) ⟨1393964, by rfl⟩ : syracuseStep 1858619 = 2787929) B2787929
theorem B7060547 : Blo 1238437 7060547 := bstep (se 1 (by rfl) ⟨5295410, by rfl⟩ : syracuseStep 7060547 = 10590821) B10590821
theorem B5954647 : Blo 1238437 5954647 := bstep (se 1 (by rfl) ⟨4465985, by rfl⟩ : syracuseStep 5954647 = 8931971) B8931971
theorem B1858679 : Blo 1238437 1858679 := bstep (se 1 (by rfl) ⟨1394009, by rfl⟩ : syracuseStep 1858679 = 2788019) B2788019
theorem B1858703 : Blo 1238437 1858703 := bstep (se 1 (by rfl) ⟨1394027, by rfl⟩ : syracuseStep 1858703 = 2788055) B2788055
theorem B1858745 : Blo 1238437 1858745 := bstep (se 2 (by rfl) ⟨697029, by rfl⟩ : syracuseStep 1858745 = 1394059) B1394059
theorem B20102381 : Blo 1238437 20102381 := bstep (se 3 (by rfl) ⟨3769196, by rfl⟩ : syracuseStep 20102381 = 7538393) B7538393
theorem B1858823 : Blo 1238437 1858823 := bstep (se 1 (by rfl) ⟨1394117, by rfl⟩ : syracuseStep 1858823 = 2788235) B2788235
theorem B4185377 : Blo 1238437 4185377 := bstep (se 2 (by rfl) ⟨1569516, by rfl⟩ : syracuseStep 4185377 = 3139033) B3139033
theorem B1858859 : Blo 1238437 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B1858889 : Blo 1238437 1858889 := bstep (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) B1394167
theorem B3530137 : Blo 1238437 3530137 := bstep (se 2 (by rfl) ⟨1323801, by rfl⟩ : syracuseStep 3530137 = 2647603) B2647603
theorem B1859003 : Blo 1238437 1859003 := bstep (se 1 (by rfl) ⟨1394252, by rfl⟩ : syracuseStep 1859003 = 2788505) B2788505
theorem B1859063 : Blo 1238437 1859063 := bstep (se 1 (by rfl) ⟨1394297, by rfl⟩ : syracuseStep 1859063 = 2788595) B2788595
theorem B7061003 : Blo 1238437 7061003 := bstep (se 1 (by rfl) ⟨5295752, by rfl⟩ : syracuseStep 7061003 = 10591505) B10591505
theorem B3137039 : Blo 1238437 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B1859087 : Blo 1238437 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B6274583 : Blo 1238437 6274583 := bstep (se 1 (by rfl) ⟨4705937, by rfl⟩ : syracuseStep 6274583 = 9411875) B9411875
theorem B1859129 : Blo 1238437 1859129 := bstep (se 2 (by rfl) ⟨697173, by rfl⟩ : syracuseStep 1859129 = 1394347) B1394347
theorem B1859207 : Blo 1238437 1859207 := bstep (se 1 (by rfl) ⟨1394405, by rfl⟩ : syracuseStep 1859207 = 2788811) B2788811
theorem B1859243 : Blo 1238437 1859243 := bstep (se 1 (by rfl) ⟨1394432, by rfl⟩ : syracuseStep 1859243 = 2788865) B2788865
theorem B1859273 : Blo 1238437 1859273 := bstep (se 2 (by rfl) ⟨697227, by rfl⟩ : syracuseStep 1859273 = 1394455) B1394455
theorem B1859387 : Blo 1238437 1859387 := bstep (se 1 (by rfl) ⟨1394540, by rfl⟩ : syracuseStep 1859387 = 2789081) B2789081
theorem B4185971 : Blo 1238437 4185971 := bstep (se 1 (by rfl) ⟨3139478, by rfl⟩ : syracuseStep 4185971 = 6278957) B6278957
theorem B1859447 : Blo 1238437 1859447 := bstep (se 1 (by rfl) ⟨1394585, by rfl⟩ : syracuseStep 1859447 = 2789171) B2789171
theorem B1859471 : Blo 1238437 1859471 := bstep (se 1 (by rfl) ⟨1394603, by rfl⟩ : syracuseStep 1859471 = 2789207) B2789207
theorem B1859513 : Blo 1238437 1859513 := bstep (se 2 (by rfl) ⟨697317, by rfl⟩ : syracuseStep 1859513 = 1394635) B1394635
theorem B3137555 : Blo 1238437 3137555 := bstep (se 1 (by rfl) ⟨2353166, by rfl⟩ : syracuseStep 3137555 = 4706333) B4706333
theorem B1859663 : Blo 1238437 1859663 := bstep (se 1 (by rfl) ⟨1394747, by rfl⟩ : syracuseStep 1859663 = 2789495) B2789495
theorem B14114897 : Blo 1238437 14114897 := bstep (se 2 (by rfl) ⟨5293086, by rfl⟩ : syracuseStep 14114897 = 10586173) B10586173
theorem B5095619 : Blo 1238437 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B1859783 : Blo 1238437 1859783 := bstep (se 1 (by rfl) ⟨1394837, by rfl⟩ : syracuseStep 1859783 = 2789675) B2789675
theorem B2646263 : Blo 1238437 2646263 := bstep (se 1 (by rfl) ⟨1984697, by rfl⟩ : syracuseStep 2646263 = 3969395) B3969395
theorem B4702475 : Blo 1238437 4702475 := bstep (se 1 (by rfl) ⟨3526856, by rfl⟩ : syracuseStep 4702475 = 7053713) B7053713
theorem B1859945 : Blo 1238437 1859945 := bstep (se 2 (by rfl) ⟨697479, by rfl⟩ : syracuseStep 1859945 = 1394959) B1394959
theorem B1860023 : Blo 1238437 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B3138011 : Blo 1238437 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B1860059 : Blo 1238437 1860059 := bstep (se 1 (by rfl) ⟨1395044, by rfl⟩ : syracuseStep 1860059 = 2790089) B2790089
theorem B53609111 : Blo 1238437 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B9675449 : Blo 1238437 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B4702931 : Blo 1238437 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B7947011 : Blo 1238437 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B120570677 : Blo 1238437 120570677 := bstep (se 5 (by rfl) ⟨5651750, by rfl⟩ : syracuseStep 120570677 = 11303501) B11303501
theorem B3769249 : Blo 1238437 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B1860527 : Blo 1238437 1860527 := bstep (se 1 (by rfl) ⟨1395395, by rfl⟩ : syracuseStep 1860527 = 2790791) B2790791
theorem B5022647 : Blo 1238437 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B1393627 : Blo 1238437 1393627 := bstep (se 1 (by rfl) ⟨1045220, by rfl⟩ : syracuseStep 1393627 = 2090441) B2090441
theorem B10593281 : Blo 1238437 10593281 := bstep (se 2 (by rfl) ⟨3972480, by rfl⟩ : syracuseStep 10593281 = 7944961) B7944961
theorem B8602625 : Blo 1238437 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B1860617 : Blo 1238437 1860617 := bstep (se 2 (by rfl) ⟨697731, by rfl⟩ : syracuseStep 1860617 = 1395463) B1395463
theorem B1860647 : Blo 1238437 1860647 := bstep (se 1 (by rfl) ⟨1395485, by rfl⟩ : syracuseStep 1860647 = 2790971) B2790971
theorem B2090063 : Blo 1238437 2090063 := bstep (se 1 (by rfl) ⟨1567547, by rfl⟩ : syracuseStep 2090063 = 3135095) B3135095
theorem B2352377 : Blo 1238437 2352377 := bstep (se 2 (by rfl) ⟨882141, by rfl⟩ : syracuseStep 2352377 = 1764283) B1764283
theorem B8938775 : Blo 1238437 8938775 := bstep (se 1 (by rfl) ⟨6704081, by rfl⟩ : syracuseStep 8938775 = 13408163) B13408163
theorem B1238447 : Blo 1238437 1238447 := bstep (se 1 (by rfl) ⟨928835, by rfl⟩ : syracuseStep 1238447 = 1857671) B1857671
theorem B1394095 : Blo 1238437 1394095 := bstep (se 1 (by rfl) ⟨1045571, by rfl⟩ : syracuseStep 1394095 = 2091143) B2091143
theorem B2352559 : Blo 1238437 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B1238471 : Blo 1238437 1238471 := bstep (se 1 (by rfl) ⟨928853, by rfl⟩ : syracuseStep 1238471 = 1857707) B1857707
theorem B7939529 : Blo 1238437 7939529 := bstep (se 2 (by rfl) ⟨2977323, by rfl⟩ : syracuseStep 7939529 = 5954647) B5954647
theorem B1238491 : Blo 1238437 1238491 := bstep (se 1 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 1238491 = 1857737) B1857737
theorem B2647561 : Blo 1238437 2647561 := bstep (se 2 (by rfl) ⟨992835, by rfl⟩ : syracuseStep 2647561 = 1985671) B1985671
theorem B1238567 : Blo 1238437 1238567 := bstep (se 1 (by rfl) ⟨928925, by rfl⟩ : syracuseStep 1238567 = 1857851) B1857851
theorem B1238607 : Blo 1238437 1238607 := bstep (se 1 (by rfl) ⟨928955, by rfl⟩ : syracuseStep 1238607 = 1857911) B1857911
theorem B2352719 : Blo 1238437 2352719 := bstep (se 1 (by rfl) ⟨1764539, by rfl⟩ : syracuseStep 2352719 = 3529079) B3529079
theorem B1238623 : Blo 1238437 1238623 := bstep (se 1 (by rfl) ⟨928967, by rfl⟩ : syracuseStep 1238623 = 1857935) B1857935
theorem B2786939 : Blo 1238437 2786939 := bstep (se 1 (by rfl) ⟨2090204, by rfl⟩ : syracuseStep 2786939 = 4180409) B4180409
theorem B1238651 : Blo 1238437 1238651 := bstep (se 1 (by rfl) ⟨928988, by rfl⟩ : syracuseStep 1238651 = 1857977) B1857977
theorem B3139195 : Blo 1238437 3139195 := bstep (se 1 (by rfl) ⟨2354396, by rfl⟩ : syracuseStep 3139195 = 4708793) B4708793
theorem B1238703 : Blo 1238437 1238703 := bstep (se 1 (by rfl) ⟨929027, by rfl⟩ : syracuseStep 1238703 = 1858055) B1858055
theorem B4703933 : Blo 1238437 4703933 := bstep (se 3 (by rfl) ⟨881987, by rfl⟩ : syracuseStep 4703933 = 1763975) B1763975
theorem B1238727 : Blo 1238437 1238727 := bstep (se 1 (by rfl) ⟨929045, by rfl⟩ : syracuseStep 1238727 = 1858091) B1858091
theorem B1238747 : Blo 1238437 1238747 := bstep (se 1 (by rfl) ⟨929060, by rfl⟩ : syracuseStep 1238747 = 1858121) B1858121
theorem B2787065 : Blo 1238437 2787065 := bstep (se 2 (by rfl) ⟨1045149, by rfl⟩ : syracuseStep 2787065 = 2090299) B2090299
theorem B1238823 : Blo 1238437 1238823 := bstep (se 1 (by rfl) ⟨929117, by rfl⟩ : syracuseStep 1238823 = 1858235) B1858235
theorem B7055171 : Blo 1238437 7055171 := bstep (se 1 (by rfl) ⟨5291378, by rfl⟩ : syracuseStep 7055171 = 10582757) B10582757
theorem B228984641 : Blo 1238437 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B1238863 : Blo 1238437 1238863 := bstep (se 1 (by rfl) ⟨929147, by rfl⟩ : syracuseStep 1238863 = 1858295) B1858295
theorem B1238879 : Blo 1238437 1238879 := bstep (se 1 (by rfl) ⟨929159, by rfl⟩ : syracuseStep 1238879 = 1858319) B1858319
theorem B1394527 : Blo 1238437 1394527 := bstep (se 1 (by rfl) ⟨1045895, by rfl⟩ : syracuseStep 1394527 = 2091791) B2091791
theorem B2647903 : Blo 1238437 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B5293943 : Blo 1238437 5293943 := bstep (se 1 (by rfl) ⟨3970457, by rfl⟩ : syracuseStep 5293943 = 7940915) B7940915
theorem B1238907 : Blo 1238437 1238907 := bstep (se 1 (by rfl) ⟨929180, by rfl⟩ : syracuseStep 1238907 = 1858361) B1858361
theorem B15075233 : Blo 1238437 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B1238959 : Blo 1238437 1238959 := bstep (se 1 (by rfl) ⟨929219, by rfl⟩ : syracuseStep 1238959 = 1858439) B1858439
theorem B2090927 : Blo 1238437 2090927 := bstep (se 1 (by rfl) ⟨1568195, by rfl⟩ : syracuseStep 2090927 = 3136391) B3136391
theorem B1238983 : Blo 1238437 1238983 := bstep (se 1 (by rfl) ⟨929237, by rfl⟩ : syracuseStep 1238983 = 1858475) B1858475
theorem B12249037 : Blo 1238437 12249037 := bstep (se 3 (by rfl) ⟨2296694, by rfl⟩ : syracuseStep 12249037 = 4593389) B4593389
theorem B1239003 : Blo 1238437 1239003 := bstep (se 1 (by rfl) ⟨929252, by rfl⟩ : syracuseStep 1239003 = 1858505) B1858505
theorem B2787335 : Blo 1238437 2787335 := bstep (se 1 (by rfl) ⟨2090501, by rfl⟩ : syracuseStep 2787335 = 4181003) B4181003
theorem B3352583 : Blo 1238437 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B1239079 : Blo 1238437 1239079 := bstep (se 1 (by rfl) ⟨929309, by rfl⟩ : syracuseStep 1239079 = 1858619) B1858619
theorem B2787407 : Blo 1238437 2787407 := bstep (se 1 (by rfl) ⟨2090555, by rfl⟩ : syracuseStep 2787407 = 4181111) B4181111
theorem B1239119 : Blo 1238437 1239119 := bstep (se 1 (by rfl) ⟨929339, by rfl⟩ : syracuseStep 1239119 = 1858679) B1858679
theorem B1239135 : Blo 1238437 1239135 := bstep (se 1 (by rfl) ⟨929351, by rfl⟩ : syracuseStep 1239135 = 1858703) B1858703
theorem B1239163 : Blo 1238437 1239163 := bstep (se 1 (by rfl) ⟨929372, by rfl⟩ : syracuseStep 1239163 = 1858745) B1858745
theorem B4180139 : Blo 1238437 4180139 := bstep (se 1 (by rfl) ⟨3135104, by rfl⟩ : syracuseStep 4180139 = 6270209) B6270209
theorem B1239215 : Blo 1238437 1239215 := bstep (se 1 (by rfl) ⟨929411, by rfl⟩ : syracuseStep 1239215 = 1858823) B1858823
theorem B1239239 : Blo 1238437 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B1394887 : Blo 1238437 1394887 := bstep (se 1 (by rfl) ⟨1046165, by rfl⟩ : syracuseStep 1394887 = 2092331) B2092331
theorem B1239259 : Blo 1238437 1239259 := bstep (se 1 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 1239259 = 1858889) B1858889
theorem B1239335 : Blo 1238437 1239335 := bstep (se 1 (by rfl) ⟨929501, by rfl⟩ : syracuseStep 1239335 = 1859003) B1859003
theorem B13060403 : Blo 1238437 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B1239375 : Blo 1238437 1239375 := bstep (se 1 (by rfl) ⟨929531, by rfl⟩ : syracuseStep 1239375 = 1859063) B1859063
theorem B2091359 : Blo 1238437 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B1239391 : Blo 1238437 1239391 := bstep (se 1 (by rfl) ⟨929543, by rfl⟩ : syracuseStep 1239391 = 1859087) B1859087
theorem B1239419 : Blo 1238437 1239419 := bstep (se 1 (by rfl) ⟨929564, by rfl⟩ : syracuseStep 1239419 = 1859129) B1859129
theorem B1239471 : Blo 1238437 1239471 := bstep (se 1 (by rfl) ⟨929603, by rfl⟩ : syracuseStep 1239471 = 1859207) B1859207
theorem B1239495 : Blo 1238437 1239495 := bstep (se 1 (by rfl) ⟨929621, by rfl⟩ : syracuseStep 1239495 = 1859243) B1859243
theorem B2787803 : Blo 1238437 2787803 := bstep (se 1 (by rfl) ⟨2090852, by rfl⟩ : syracuseStep 2787803 = 4181705) B4181705
theorem B1239515 : Blo 1238437 1239515 := bstep (se 1 (by rfl) ⟨929636, by rfl⟩ : syracuseStep 1239515 = 1859273) B1859273
theorem B1239591 : Blo 1238437 1239591 := bstep (se 1 (by rfl) ⟨929693, by rfl⟩ : syracuseStep 1239591 = 1859387) B1859387
theorem B1239631 : Blo 1238437 1239631 := bstep (se 1 (by rfl) ⟨929723, by rfl⟩ : syracuseStep 1239631 = 1859447) B1859447
theorem B1239647 : Blo 1238437 1239647 := bstep (se 1 (by rfl) ⟨929735, by rfl⟩ : syracuseStep 1239647 = 1859471) B1859471
theorem B1239675 : Blo 1238437 1239675 := bstep (se 1 (by rfl) ⟨929756, by rfl⟩ : syracuseStep 1239675 = 1859513) B1859513
theorem B2353835 : Blo 1238437 2353835 := bstep (se 1 (by rfl) ⟨1765376, by rfl⟩ : syracuseStep 2353835 = 3530753) B3530753
theorem B1239727 : Blo 1238437 1239727 := bstep (se 1 (by rfl) ⟨929795, by rfl⟩ : syracuseStep 1239727 = 1859591) B1859591
theorem B4180679 : Blo 1238437 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B1239751 : Blo 1238437 1239751 := bstep (se 1 (by rfl) ⟨929813, by rfl⟩ : syracuseStep 1239751 = 1859627) B1859627
theorem B1239771 : Blo 1238437 1239771 := bstep (se 1 (by rfl) ⟨929828, by rfl⟩ : syracuseStep 1239771 = 1859657) B1859657
theorem B1239847 : Blo 1238437 1239847 := bstep (se 1 (by rfl) ⟨929885, by rfl⟩ : syracuseStep 1239847 = 1859771) B1859771
theorem B8940365 : Blo 1238437 8940365 := bstep (se 3 (by rfl) ⟨1676318, by rfl⟩ : syracuseStep 8940365 = 3352637) B3352637
theorem B1239887 : Blo 1238437 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B1239903 : Blo 1238437 1239903 := bstep (se 1 (by rfl) ⟨929927, by rfl⟩ : syracuseStep 1239903 = 1859855) B1859855
theorem B1239931 : Blo 1238437 1239931 := bstep (se 1 (by rfl) ⟨929948, by rfl⟩ : syracuseStep 1239931 = 1859897) B1859897
theorem B2091919 : Blo 1238437 2091919 := bstep (se 1 (by rfl) ⟨1568939, by rfl⟩ : syracuseStep 2091919 = 3137879) B3137879
theorem B1764271 : Blo 1238437 1764271 := bstep (se 1 (by rfl) ⟨1323203, by rfl⟩ : syracuseStep 1764271 = 2646407) B2646407
theorem B2788271 : Blo 1238437 2788271 := bstep (se 1 (by rfl) ⟨2091203, by rfl⟩ : syracuseStep 2788271 = 4182407) B4182407
theorem B1239983 : Blo 1238437 1239983 := bstep (se 1 (by rfl) ⟨929987, by rfl⟩ : syracuseStep 1239983 = 1859975) B1859975
theorem B1240007 : Blo 1238437 1240007 := bstep (se 1 (by rfl) ⟨930005, by rfl⟩ : syracuseStep 1240007 = 1860011) B1860011
theorem B1240027 : Blo 1238437 1240027 := bstep (se 1 (by rfl) ⟨930020, by rfl⟩ : syracuseStep 1240027 = 1860041) B1860041
theorem B2649107 : Blo 1238437 2649107 := bstep (se 1 (by rfl) ⟨1986830, by rfl⟩ : syracuseStep 2649107 = 3973661) B3973661
theorem B1240103 : Blo 1238437 1240103 := bstep (se 1 (by rfl) ⟨930077, by rfl⟩ : syracuseStep 1240103 = 1860155) B1860155
theorem B8940593 : Blo 1238437 8940593 := bstep (se 2 (by rfl) ⟨3352722, by rfl⟩ : syracuseStep 8940593 = 6705445) B6705445
theorem B1240143 : Blo 1238437 1240143 := bstep (se 1 (by rfl) ⟨930107, by rfl⟩ : syracuseStep 1240143 = 1860215) B1860215
theorem B4705361 : Blo 1238437 4705361 := bstep (se 2 (by rfl) ⟨1764510, by rfl⟩ : syracuseStep 4705361 = 3529021) B3529021
theorem B1240159 : Blo 1238437 1240159 := bstep (se 1 (by rfl) ⟨930119, by rfl⟩ : syracuseStep 1240159 = 1860239) B1860239
theorem B1240187 : Blo 1238437 1240187 := bstep (se 1 (by rfl) ⟨930140, by rfl⟩ : syracuseStep 1240187 = 1860281) B1860281
theorem B6032537 : Blo 1238437 6032537 := bstep (se 2 (by rfl) ⟨2262201, by rfl⟩ : syracuseStep 6032537 = 4524403) B4524403
theorem B6696107 : Blo 1238437 6696107 := bstep (se 1 (by rfl) ⟨5022080, by rfl⟩ : syracuseStep 6696107 = 10044161) B10044161
theorem B2788523 : Blo 1238437 2788523 := bstep (se 1 (by rfl) ⟨2091392, by rfl⟩ : syracuseStep 2788523 = 4182785) B4182785
theorem B1240239 : Blo 1238437 1240239 := bstep (se 1 (by rfl) ⟨930179, by rfl⟩ : syracuseStep 1240239 = 1860359) B1860359
theorem B1240263 : Blo 1238437 1240263 := bstep (se 1 (by rfl) ⟨930197, by rfl⟩ : syracuseStep 1240263 = 1860395) B1860395
theorem B1240283 : Blo 1238437 1240283 := bstep (se 1 (by rfl) ⟨930212, by rfl⟩ : syracuseStep 1240283 = 1860425) B1860425
theorem B14511395 : Blo 1238437 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B1240359 : Blo 1238437 1240359 := bstep (se 1 (by rfl) ⟨930269, by rfl⟩ : syracuseStep 1240359 = 1860539) B1860539
theorem B1240399 : Blo 1238437 1240399 := bstep (se 1 (by rfl) ⟨930299, by rfl⟩ : syracuseStep 1240399 = 1860599) B1860599
theorem B1240415 : Blo 1238437 1240415 := bstep (se 1 (by rfl) ⟨930311, by rfl⟩ : syracuseStep 1240415 = 1860623) B1860623
theorem B1789291 : Blo 1238437 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B5656027 : Blo 1238437 5656027 := bstep (se 1 (by rfl) ⟨4242020, by rfl⟩ : syracuseStep 5656027 = 8484041) B8484041
theorem B9407987 : Blo 1238437 9407987 := bstep (se 1 (by rfl) ⟨7055990, by rfl⟩ : syracuseStep 9407987 = 14111981) B14111981
theorem B4181543 : Blo 1238437 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B10595879 : Blo 1238437 10595879 := bstep (se 1 (by rfl) ⟨7946909, by rfl⟩ : syracuseStep 10595879 = 15893819) B15893819
theorem B2092601 : Blo 1238437 2092601 := bstep (se 2 (by rfl) ⟨784725, by rfl⟩ : syracuseStep 2092601 = 1569451) B1569451
theorem B1674875 : Blo 1238437 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B13577867 : Blo 1238437 13577867 := bstep (se 1 (by rfl) ⟨10183400, by rfl⟩ : syracuseStep 13577867 = 20366801) B20366801
theorem B6278795 : Blo 1238437 6278795 := bstep (se 1 (by rfl) ⟨4709096, by rfl⟩ : syracuseStep 6278795 = 9418193) B9418193
theorem B4181651 : Blo 1238437 4181651 := bstep (se 1 (by rfl) ⟨3136238, by rfl⟩ : syracuseStep 4181651 = 6272477) B6272477
theorem B2789063 : Blo 1238437 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B4181867 : Blo 1238437 4181867 := bstep (se 1 (by rfl) ⟨3136400, by rfl⟩ : syracuseStep 4181867 = 6272801) B6272801
theorem B4181921 : Blo 1238437 4181921 := bstep (se 2 (by rfl) ⟨1568220, by rfl⟩ : syracuseStep 4181921 = 3136441) B3136441
theorem B7057313 : Blo 1238437 7057313 := bstep (se 2 (by rfl) ⟨2646492, by rfl⟩ : syracuseStep 7057313 = 5292985) B5292985
theorem B1789879 : Blo 1238437 1789879 := bstep (se 1 (by rfl) ⟨1342409, by rfl⟩ : syracuseStep 1789879 = 2684819) B2684819
theorem B1986491 : Blo 1238437 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B4239361 : Blo 1238437 4239361 := bstep (se 2 (by rfl) ⟨1589760, by rfl⟩ : syracuseStep 4239361 = 3179521) B3179521
theorem B5951495 : Blo 1238437 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B2232329 : Blo 1238437 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B1675513 : Blo 1238437 1675513 := bstep (se 2 (by rfl) ⟨628317, by rfl⟩ : syracuseStep 1675513 = 1256635) B1256635
theorem B4182515 : Blo 1238437 4182515 := bstep (se 1 (by rfl) ⟨3136886, by rfl⟩ : syracuseStep 4182515 = 6273773) B6273773
theorem B4706849 : Blo 1238437 4706849 := bstep (se 2 (by rfl) ⟨1765068, by rfl⟩ : syracuseStep 4706849 = 3530137) B3530137
theorem B2789927 : Blo 1238437 2789927 := bstep (se 1 (by rfl) ⟨2092445, by rfl⟩ : syracuseStep 2789927 = 4184891) B4184891
theorem B11465425 : Blo 1238437 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B4707031 : Blo 1238437 4707031 := bstep (se 1 (by rfl) ⟨3530273, by rfl⟩ : syracuseStep 4707031 = 7060547) B7060547
theorem B2790251 : Blo 1238437 2790251 := bstep (se 1 (by rfl) ⟨2092688, by rfl⟩ : syracuseStep 2790251 = 4185377) B4185377
theorem B2790305 : Blo 1238437 2790305 := bstep (se 2 (by rfl) ⟨1046364, by rfl⟩ : syracuseStep 2790305 = 2092729) B2092729
theorem B1569719 : Blo 1238437 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B4707335 : Blo 1238437 4707335 := bstep (se 1 (by rfl) ⟨3530501, by rfl⟩ : syracuseStep 4707335 = 7061003) B7061003
theorem B4183055 : Blo 1238437 4183055 := bstep (se 1 (by rfl) ⟨3137291, by rfl⟩ : syracuseStep 4183055 = 6274583) B6274583
theorem B1569871 : Blo 1238437 1569871 := bstep (se 1 (by rfl) ⟨1177403, by rfl⟩ : syracuseStep 1569871 = 2354807) B2354807
theorem B6272153 : Blo 1238437 6272153 := bstep (se 2 (by rfl) ⟨2352057, by rfl⟩ : syracuseStep 6272153 = 4704115) B4704115
theorem B7943321 : Blo 1238437 7943321 := bstep (se 2 (by rfl) ⟨2978745, by rfl⟩ : syracuseStep 7943321 = 5957491) B5957491
theorem B3527837 : Blo 1238437 3527837 := bstep (se 3 (by rfl) ⟨661469, by rfl⟩ : syracuseStep 3527837 = 1322939) B1322939
theorem B10056899 : Blo 1238437 10056899 := bstep (se 1 (by rfl) ⟨7542674, by rfl⟩ : syracuseStep 10056899 = 15085349) B15085349
theorem B2790647 : Blo 1238437 2790647 := bstep (se 1 (by rfl) ⟨2092985, by rfl⟩ : syracuseStep 2790647 = 4185971) B4185971
theorem B3577193 : Blo 1238437 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B4707821 : Blo 1238437 4707821 := bstep (se 3 (by rfl) ⟨882716, by rfl⟩ : syracuseStep 4707821 = 1765433) B1765433
theorem B3134963 : Blo 1238437 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B4183649 : Blo 1238437 4183649 := bstep (se 2 (by rfl) ⟨1568868, by rfl⟩ : syracuseStep 4183649 = 3137737) B3137737
theorem B7059089 : Blo 1238437 7059089 := bstep (se 2 (by rfl) ⟨2647158, by rfl⟩ : syracuseStep 7059089 = 5294317) B5294317
theorem B33904277 : Blo 1238437 33904277 := bstep (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) B1589263
theorem B16971457 : Blo 1238437 16971457 := bstep (se 2 (by rfl) ⟨6364296, by rfl⟩ : syracuseStep 16971457 = 12728593) B12728593
theorem B7935839 : Blo 1238437 7935839 := bstep (se 1 (by rfl) ⟨5951879, by rfl⟩ : syracuseStep 7935839 = 11903759) B11903759
theorem B20100959 : Blo 1238437 20100959 := bstep (se 1 (by rfl) ⟨15075719, by rfl⟩ : syracuseStep 20100959 = 30151439) B30151439
theorem B3528623 : Blo 1238437 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B3135419 : Blo 1238437 3135419 := bstep (se 1 (by rfl) ⟨2351564, by rfl⟩ : syracuseStep 3135419 = 4703129) B4703129
theorem B8599505 : Blo 1238437 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B10582073 : Blo 1238437 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B2979919 : Blo 1238437 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B7059545 : Blo 1238437 7059545 := bstep (se 2 (by rfl) ⟨2647329, by rfl⟩ : syracuseStep 7059545 = 5294659) B5294659
theorem B1857659 : Blo 1238437 1857659 := bstep (se 1 (by rfl) ⟨1393244, by rfl⟩ : syracuseStep 1857659 = 2786489) B2786489
theorem B1857785 : Blo 1238437 1857785 := bstep (se 2 (by rfl) ⟨696669, by rfl⟩ : syracuseStep 1857785 = 1393339) B1393339
theorem B9410903 : Blo 1238437 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B1857887 : Blo 1238437 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B1857899 : Blo 1238437 1857899 := bstep (se 1 (by rfl) ⟨1393424, by rfl⟩ : syracuseStep 1857899 = 2786849) B2786849
theorem B16308769 : Blo 1238437 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B2513447 : Blo 1238437 2513447 := bstep (se 1 (by rfl) ⟨1885085, by rfl⟩ : syracuseStep 2513447 = 3770171) B3770171
theorem B1858127 : Blo 1238437 1858127 := bstep (se 1 (by rfl) ⟨1393595, by rfl⟩ : syracuseStep 1858127 = 2787191) B2787191
theorem B3136097 : Blo 1238437 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B4708961 : Blo 1238437 4708961 := bstep (se 2 (by rfl) ⟨1765860, by rfl⟩ : syracuseStep 4708961 = 3531721) B3531721
theorem B9050797 : Blo 1238437 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B1858247 : Blo 1238437 1858247 := bstep (se 1 (by rfl) ⟨1393685, by rfl⟩ : syracuseStep 1858247 = 2787371) B2787371
theorem B1858409 : Blo 1238437 1858409 := bstep (se 2 (by rfl) ⟨696903, by rfl⟩ : syracuseStep 1858409 = 1393807) B1393807
theorem B1858487 : Blo 1238437 1858487 := bstep (se 1 (by rfl) ⟨1393865, by rfl⟩ : syracuseStep 1858487 = 2787731) B2787731
theorem B10738615 : Blo 1238437 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B1858523 : Blo 1238437 1858523 := bstep (se 1 (by rfl) ⟨1393892, by rfl⟩ : syracuseStep 1858523 = 2787785) B2787785
theorem B4185107 : Blo 1238437 4185107 := bstep (se 1 (by rfl) ⟨3138830, by rfl⟩ : syracuseStep 4185107 = 6277661) B6277661
theorem B8936527 : Blo 1238437 8936527 := bstep (se 1 (by rfl) ⟨6702395, by rfl⟩ : syracuseStep 8936527 = 13404791) B13404791
theorem B8387831 : Blo 1238437 8387831 := bstep (se 1 (by rfl) ⟨6290873, by rfl⟩ : syracuseStep 8387831 = 12581747) B12581747
theorem B4185431 : Blo 1238437 4185431 := bstep (se 1 (by rfl) ⟨3139073, by rfl⟩ : syracuseStep 4185431 = 6278147) B6278147
theorem B10050905 : Blo 1238437 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B1858991 : Blo 1238437 1858991 := bstep (se 1 (by rfl) ⟨1394243, by rfl⟩ : syracuseStep 1858991 = 2788487) B2788487
theorem B32644529 : Blo 1238437 32644529 := bstep (se 2 (by rfl) ⟨12241698, by rfl⟩ : syracuseStep 32644529 = 24483397) B24483397
theorem B13401587 : Blo 1238437 13401587 := bstep (se 1 (by rfl) ⟨10051190, by rfl⟩ : syracuseStep 13401587 = 20102381) B20102381
theorem B1859081 : Blo 1238437 1859081 := bstep (se 2 (by rfl) ⟨697155, by rfl⟩ : syracuseStep 1859081 = 1394311) B1394311
theorem B1859111 : Blo 1238437 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B1859195 : Blo 1238437 1859195 := bstep (se 1 (by rfl) ⟨1394396, by rfl⟩ : syracuseStep 1859195 = 2788793) B2788793
theorem B10591883 : Blo 1238437 10591883 := bstep (se 1 (by rfl) ⟨7943912, by rfl⟩ : syracuseStep 10591883 = 15887825) B15887825
theorem B1859321 : Blo 1238437 1859321 := bstep (se 2 (by rfl) ⟨697245, by rfl⟩ : syracuseStep 1859321 = 1394491) B1394491
theorem B5021513 : Blo 1238437 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B1859423 : Blo 1238437 1859423 := bstep (se 1 (by rfl) ⟨1394567, by rfl⟩ : syracuseStep 1859423 = 2789135) B2789135
theorem B1859435 : Blo 1238437 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B2645921 : Blo 1238437 2645921 := bstep (se 2 (by rfl) ⟨992220, by rfl⟩ : syracuseStep 2645921 = 1984441) B1984441
theorem B22609925 : Blo 1238437 22609925 := bstep (se 4 (by rfl) ⟨2119680, by rfl⟩ : syracuseStep 22609925 = 4239361) B4239361
theorem B3973225 : Blo 1238437 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B1859849 : Blo 1238437 1859849 := bstep (se 2 (by rfl) ⟨697443, by rfl⟩ : syracuseStep 1859849 = 1394887) B1394887
theorem B3137899 : Blo 1238437 3137899 := bstep (se 1 (by rfl) ⟨2353424, by rfl⟩ : syracuseStep 3137899 = 4706849) B4706849
theorem B1859951 : Blo 1238437 1859951 := bstep (se 1 (by rfl) ⟨1394963, by rfl⟩ : syracuseStep 1859951 = 2789927) B2789927
theorem B80380451 : Blo 1238437 80380451 := bstep (se 1 (by rfl) ⟨60285338, by rfl⟩ : syracuseStep 80380451 = 120570677) B120570677
theorem B1860167 : Blo 1238437 1860167 := bstep (se 1 (by rfl) ⟨1395125, by rfl⟩ : syracuseStep 1860167 = 2790251) B2790251
theorem B1860203 : Blo 1238437 1860203 := bstep (se 1 (by rfl) ⟨1395152, by rfl⟩ : syracuseStep 1860203 = 2790305) B2790305
theorem B7062187 : Blo 1238437 7062187 := bstep (se 1 (by rfl) ⟨5296640, by rfl⟩ : syracuseStep 7062187 = 10593281) B10593281
theorem B3138223 : Blo 1238437 3138223 := bstep (se 1 (by rfl) ⟨2353667, by rfl⟩ : syracuseStep 3138223 = 4707335) B4707335
theorem B1393375 : Blo 1238437 1393375 := bstep (se 1 (by rfl) ⟨1045031, by rfl⟩ : syracuseStep 1393375 = 2090063) B2090063
theorem B2351891 : Blo 1238437 2351891 := bstep (se 1 (by rfl) ⟨1763918, by rfl⟩ : syracuseStep 2351891 = 3527837) B3527837
theorem B1860431 : Blo 1238437 1860431 := bstep (se 1 (by rfl) ⟨1395323, by rfl⟩ : syracuseStep 1860431 = 2790647) B2790647
theorem B2384795 : Blo 1238437 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B15287233 : Blo 1238437 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B6276041 : Blo 1238437 6276041 := bstep (se 2 (by rfl) ⟨2353515, by rfl⟩ : syracuseStep 6276041 = 4707031) B4707031
theorem B5293019 : Blo 1238437 5293019 := bstep (se 1 (by rfl) ⟨3969764, by rfl⟩ : syracuseStep 5293019 = 7939529) B7939529
theorem B3138547 : Blo 1238437 3138547 := bstep (se 1 (by rfl) ⟨2353910, by rfl⟩ : syracuseStep 3138547 = 4707821) B4707821
theorem B2089975 : Blo 1238437 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B22602851 : Blo 1238437 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B4703447 : Blo 1238437 4703447 := bstep (se 1 (by rfl) ⟨3527585, by rfl⟩ : syracuseStep 4703447 = 7055171) B7055171
theorem B1393951 : Blo 1238437 1393951 := bstep (se 1 (by rfl) ⟨1045463, by rfl⟩ : syracuseStep 1393951 = 2090927) B2090927
theorem B2352415 : Blo 1238437 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B2090279 : Blo 1238437 2090279 := bstep (se 1 (by rfl) ⟨1567709, by rfl⟩ : syracuseStep 2090279 = 3135419) B3135419
theorem B7054715 : Blo 1238437 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B1238439 : Blo 1238437 1238439 := bstep (se 1 (by rfl) ⟨928829, by rfl⟩ : syracuseStep 1238439 = 1857659) B1857659
theorem B2786759 : Blo 1238437 2786759 := bstep (se 1 (by rfl) ⟨2090069, by rfl⟩ : syracuseStep 2786759 = 4180139) B4180139
theorem B1238523 : Blo 1238437 1238523 := bstep (se 1 (by rfl) ⟨928892, by rfl⟩ : syracuseStep 1238523 = 1857785) B1857785
theorem B1238591 : Blo 1238437 1238591 := bstep (se 1 (by rfl) ⟨928943, by rfl⟩ : syracuseStep 1238591 = 1857887) B1857887
theorem B1394239 : Blo 1238437 1394239 := bstep (se 1 (by rfl) ⟨1045679, by rfl⟩ : syracuseStep 1394239 = 2091359) B2091359
theorem B1238599 : Blo 1238437 1238599 := bstep (se 1 (by rfl) ⟨928949, by rfl⟩ : syracuseStep 1238599 = 1857899) B1857899
theorem B4466333 : Blo 1238437 4466333 := bstep (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) B1674875
theorem B1238751 : Blo 1238437 1238751 := bstep (se 1 (by rfl) ⟨929063, by rfl⟩ : syracuseStep 1238751 = 1858127) B1858127
theorem B2090731 : Blo 1238437 2090731 := bstep (se 1 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 2090731 = 3136097) B3136097
theorem B3139307 : Blo 1238437 3139307 := bstep (se 1 (by rfl) ⟨2354480, by rfl⟩ : syracuseStep 3139307 = 4708961) B4708961
theorem B2787119 : Blo 1238437 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B1238831 : Blo 1238437 1238831 := bstep (se 1 (by rfl) ⟨929123, by rfl⟩ : syracuseStep 1238831 = 1858247) B1858247
theorem B2385721 : Blo 1238437 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B1238939 : Blo 1238437 1238939 := bstep (se 1 (by rfl) ⟨929204, by rfl⟩ : syracuseStep 1238939 = 1858409) B1858409
theorem B1238991 : Blo 1238437 1238991 := bstep (se 1 (by rfl) ⟨929243, by rfl⟩ : syracuseStep 1238991 = 1858487) B1858487
theorem B1239015 : Blo 1238437 1239015 := bstep (se 1 (by rfl) ⟨929261, by rfl⟩ : syracuseStep 1239015 = 1858523) B1858523
theorem B22628609 : Blo 1238437 22628609 := bstep (se 2 (by rfl) ⟨8485728, by rfl⟩ : syracuseStep 22628609 = 16971457) B16971457
theorem B1239327 : Blo 1238437 1239327 := bstep (se 1 (by rfl) ⟨929495, by rfl⟩ : syracuseStep 1239327 = 1858991) B1858991
theorem B1239387 : Blo 1238437 1239387 := bstep (se 1 (by rfl) ⟨929540, by rfl⟩ : syracuseStep 1239387 = 1859081) B1859081
theorem B2787695 : Blo 1238437 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B1239407 : Blo 1238437 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B7063919 : Blo 1238437 7063919 := bstep (se 1 (by rfl) ⟨5297939, by rfl⟩ : syracuseStep 7063919 = 10595879) B10595879
theorem B1395067 : Blo 1238437 1395067 := bstep (se 1 (by rfl) ⟨1046300, by rfl⟩ : syracuseStep 1395067 = 2092601) B2092601
theorem B1239463 : Blo 1238437 1239463 := bstep (se 1 (by rfl) ⟨929597, by rfl⟩ : syracuseStep 1239463 = 1859195) B1859195
theorem B2787767 : Blo 1238437 2787767 := bstep (se 1 (by rfl) ⟨2090825, by rfl⟩ : syracuseStep 2787767 = 4181651) B4181651
theorem B1239547 : Blo 1238437 1239547 := bstep (se 1 (by rfl) ⟨929660, by rfl⟩ : syracuseStep 1239547 = 1859321) B1859321
theorem B22932013 : Blo 1238437 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B1239615 : Blo 1238437 1239615 := bstep (se 1 (by rfl) ⟨929711, by rfl⟩ : syracuseStep 1239615 = 1859423) B1859423
theorem B2787911 : Blo 1238437 2787911 := bstep (se 1 (by rfl) ⟨2090933, by rfl⟩ : syracuseStep 2787911 = 4181867) B4181867
theorem B1239623 : Blo 1238437 1239623 := bstep (se 1 (by rfl) ⟨929717, by rfl⟩ : syracuseStep 1239623 = 1859435) B1859435
theorem B2386505 : Blo 1238437 2386505 := bstep (se 2 (by rfl) ⟨894939, by rfl⟩ : syracuseStep 2386505 = 1789879) B1789879
theorem B1763947 : Blo 1238437 1763947 := bstep (se 1 (by rfl) ⟨1322960, by rfl⟩ : syracuseStep 1763947 = 2645921) B2645921
theorem B2787947 : Blo 1238437 2787947 := bstep (se 1 (by rfl) ⟨2090960, by rfl⟩ : syracuseStep 2787947 = 4181921) B4181921
theorem B4704875 : Blo 1238437 4704875 := bstep (se 1 (by rfl) ⟨3528656, by rfl⟩ : syracuseStep 4704875 = 7057313) B7057313
theorem B22940333 : Blo 1238437 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B3967663 : Blo 1238437 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B2091703 : Blo 1238437 2091703 := bstep (se 1 (by rfl) ⟨1568777, by rfl⟩ : syracuseStep 2091703 = 3137555) B3137555
theorem B1239775 : Blo 1238437 1239775 := bstep (se 1 (by rfl) ⟨929831, by rfl⟩ : syracuseStep 1239775 = 1859663) B1859663
theorem B1239855 : Blo 1238437 1239855 := bstep (se 1 (by rfl) ⟨929891, by rfl⟩ : syracuseStep 1239855 = 1859783) B1859783
theorem B1764175 : Blo 1238437 1764175 := bstep (se 1 (by rfl) ⟨1323131, by rfl⟩ : syracuseStep 1764175 = 2646263) B2646263
theorem B1239963 : Blo 1238437 1239963 := bstep (se 1 (by rfl) ⟨929972, by rfl⟩ : syracuseStep 1239963 = 1859945) B1859945
theorem B1240015 : Blo 1238437 1240015 := bstep (se 1 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 1240015 = 1860023) B1860023
theorem B2092007 : Blo 1238437 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B1240039 : Blo 1238437 1240039 := bstep (se 1 (by rfl) ⟨930029, by rfl⟩ : syracuseStep 1240039 = 1860059) B1860059
theorem B2788343 : Blo 1238437 2788343 := bstep (se 1 (by rfl) ⟨2091257, by rfl⟩ : syracuseStep 2788343 = 4182515) B4182515
theorem B6450299 : Blo 1238437 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B1240351 : Blo 1238437 1240351 := bstep (se 1 (by rfl) ⟨930263, by rfl⟩ : syracuseStep 1240351 = 1860527) B1860527
theorem B22367549 : Blo 1238437 22367549 := bstep (se 3 (by rfl) ⟨4193915, by rfl⟩ : syracuseStep 22367549 = 8387831) B8387831
theorem B1240411 : Blo 1238437 1240411 := bstep (se 1 (by rfl) ⟨930308, by rfl⟩ : syracuseStep 1240411 = 1860617) B1860617
theorem B2788703 : Blo 1238437 2788703 := bstep (se 1 (by rfl) ⟨2091527, by rfl⟩ : syracuseStep 2788703 = 4183055) B4183055
theorem B1240431 : Blo 1238437 1240431 := bstep (se 1 (by rfl) ⟨930323, by rfl⟩ : syracuseStep 1240431 = 1860647) B1860647
theorem B21745025 : Blo 1238437 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B4181435 : Blo 1238437 4181435 := bstep (se 1 (by rfl) ⟨3136076, by rfl⟩ : syracuseStep 4181435 = 6272153) B6272153
theorem B5295547 : Blo 1238437 5295547 := bstep (se 1 (by rfl) ⟨3971660, by rfl⟩ : syracuseStep 5295547 = 7943321) B7943321
theorem B1568251 : Blo 1238437 1568251 := bstep (se 1 (by rfl) ⟨1176188, by rfl⟩ : syracuseStep 1568251 = 2352377) B2352377
theorem B5959183 : Blo 1238437 5959183 := bstep (se 1 (by rfl) ⟨4469387, by rfl⟩ : syracuseStep 5959183 = 8938775) B8938775
theorem B48270917 : Blo 1238437 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B1568479 : Blo 1238437 1568479 := bstep (se 1 (by rfl) ⟨1176359, by rfl⟩ : syracuseStep 1568479 = 2352719) B2352719
theorem B2789099 : Blo 1238437 2789099 := bstep (se 1 (by rfl) ⟨2091824, by rfl⟩ : syracuseStep 2789099 = 4183649) B4183649
theorem B4706059 : Blo 1238437 4706059 := bstep (se 1 (by rfl) ⟨3529544, by rfl⟩ : syracuseStep 4706059 = 7059089) B7059089
theorem B2789225 : Blo 1238437 2789225 := bstep (se 2 (by rfl) ⟨1045959, by rfl⟩ : syracuseStep 2789225 = 2091919) B2091919
theorem B5025665 : Blo 1238437 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B4706363 : Blo 1238437 4706363 := bstep (se 1 (by rfl) ⟨3529772, by rfl⟩ : syracuseStep 4706363 = 7059545) B7059545
theorem B11915369 : Blo 1238437 11915369 := bstep (se 2 (by rfl) ⟨4468263, by rfl⟩ : syracuseStep 11915369 = 8936527) B8936527
theorem B2093161 : Blo 1238437 2093161 := bstep (se 2 (by rfl) ⟨784935, by rfl⟩ : syracuseStep 2093161 = 1569871) B1569871
theorem B1675631 : Blo 1238437 1675631 := bstep (se 1 (by rfl) ⟨1256723, by rfl⟩ : syracuseStep 1675631 = 2513447) B2513447
theorem B1569223 : Blo 1238437 1569223 := bstep (se 1 (by rfl) ⟨1176917, by rfl⟩ : syracuseStep 1569223 = 2353835) B2353835
theorem B5960243 : Blo 1238437 5960243 := bstep (se 1 (by rfl) ⟨4470182, by rfl⟩ : syracuseStep 5960243 = 8940365) B8940365
theorem B7541369 : Blo 1238437 7541369 := bstep (se 2 (by rfl) ⟨2828013, by rfl⟩ : syracuseStep 7541369 = 5656027) B5656027
theorem B2790071 : Blo 1238437 2790071 := bstep (se 1 (by rfl) ⟨2092553, by rfl⟩ : syracuseStep 2790071 = 4185107) B4185107
theorem B1766071 : Blo 1238437 1766071 := bstep (se 1 (by rfl) ⟨1324553, by rfl⟩ : syracuseStep 1766071 = 2649107) B2649107
theorem B5960395 : Blo 1238437 5960395 := bstep (se 1 (by rfl) ⟨4470296, by rfl⟩ : syracuseStep 5960395 = 8940593) B8940593
theorem B2790287 : Blo 1238437 2790287 := bstep (se 1 (by rfl) ⟨2092715, by rfl⟩ : syracuseStep 2790287 = 4185431) B4185431
theorem B9409445 : Blo 1238437 9409445 := bstep (se 4 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 9409445 = 1764271) B1764271
theorem B21763019 : Blo 1238437 21763019 := bstep (se 1 (by rfl) ⟨16322264, by rfl⟩ : syracuseStep 21763019 = 32644529) B32644529
theorem B6271991 : Blo 1238437 6271991 := bstep (se 1 (by rfl) ⟨4703993, by rfl⟩ : syracuseStep 6271991 = 9407987) B9407987
theorem B8934391 : Blo 1238437 8934391 := bstep (se 1 (by rfl) ⟨6700793, by rfl⟩ : syracuseStep 8934391 = 13401587) B13401587
theorem B5297309 : Blo 1238437 5297309 := bstep (se 3 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 5297309 = 1986491) B1986491
theorem B3347675 : Blo 1238437 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B16332049 : Blo 1238437 16332049 := bstep (se 2 (by rfl) ⟨6124518, by rfl⟩ : syracuseStep 16332049 = 12249037) B12249037
theorem B9409931 : Blo 1238437 9409931 := bstep (se 1 (by rfl) ⟨7057448, by rfl⟩ : syracuseStep 9409931 = 14114897) B14114897
theorem B23811509 : Blo 1238437 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B3397079 : Blo 1238437 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B3134983 : Blo 1238437 3134983 := bstep (se 1 (by rfl) ⟨2351237, by rfl⟩ : syracuseStep 3134983 = 4702475) B4702475
theorem B2234017 : Blo 1238437 2234017 := bstep (se 2 (by rfl) ⟨837756, by rfl⟩ : syracuseStep 2234017 = 1675513) B1675513
theorem B35739407 : Blo 1238437 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B3135287 : Blo 1238437 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B26818397 : Blo 1238437 26818397 := bstep (se 3 (by rfl) ⟨5028449, by rfl⟩ : syracuseStep 26818397 = 10056899) B10056899
theorem B3348431 : Blo 1238437 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B1857959 : Blo 1238437 1857959 := bstep (se 1 (by rfl) ⟨1393469, by rfl⟩ : syracuseStep 1857959 = 2786939) B2786939
theorem B3135955 : Blo 1238437 3135955 := bstep (se 1 (by rfl) ⟨2351966, by rfl⟩ : syracuseStep 3135955 = 4703933) B4703933
theorem B1858043 : Blo 1238437 1858043 := bstep (se 1 (by rfl) ⟨1393532, by rfl⟩ : syracuseStep 1858043 = 2787065) B2787065
theorem B152656427 : Blo 1238437 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B5290559 : Blo 1238437 5290559 := bstep (se 1 (by rfl) ⟨3967919, by rfl⟩ : syracuseStep 5290559 = 7935839) B7935839
theorem B13400639 : Blo 1238437 13400639 := bstep (se 1 (by rfl) ⟨10050479, by rfl⟩ : syracuseStep 13400639 = 20100959) B20100959
theorem B14318153 : Blo 1238437 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B3529295 : Blo 1238437 3529295 := bstep (se 1 (by rfl) ⟨2646971, by rfl⟩ : syracuseStep 3529295 = 5293943) B5293943
theorem B10050155 : Blo 1238437 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B1858169 : Blo 1238437 1858169 := bstep (se 2 (by rfl) ⟨696813, by rfl⟩ : syracuseStep 1858169 = 1393627) B1393627
theorem B1858223 : Blo 1238437 1858223 := bstep (se 1 (by rfl) ⟨1393667, by rfl⟩ : syracuseStep 1858223 = 2787335) B2787335
theorem B2235055 : Blo 1238437 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B1858271 : Blo 1238437 1858271 := bstep (se 1 (by rfl) ⟨1393703, by rfl⟩ : syracuseStep 1858271 = 2787407) B2787407
theorem B8706935 : Blo 1238437 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B6273935 : Blo 1238437 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1858535 : Blo 1238437 1858535 := bstep (se 1 (by rfl) ⟨1393901, by rfl⟩ : syracuseStep 1858535 = 2787803) B2787803
theorem B1858793 : Blo 1238437 1858793 := bstep (se 2 (by rfl) ⟨697047, by rfl⟩ : syracuseStep 1858793 = 1394095) B1394095
theorem B3136745 : Blo 1238437 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B1858847 : Blo 1238437 1858847 := bstep (se 1 (by rfl) ⟨1394135, by rfl⟩ : syracuseStep 1858847 = 2788271) B2788271
theorem B21192029 : Blo 1238437 21192029 := bstep (se 3 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 21192029 = 7947011) B7947011
theorem B3530081 : Blo 1238437 3530081 := bstep (se 2 (by rfl) ⟨1323780, by rfl⟩ : syracuseStep 3530081 = 2647561) B2647561
theorem B3136907 : Blo 1238437 3136907 := bstep (se 1 (by rfl) ⟨2352680, by rfl⟩ : syracuseStep 3136907 = 4705361) B4705361
theorem B4021691 : Blo 1238437 4021691 := bstep (se 1 (by rfl) ⟨3016268, by rfl⟩ : syracuseStep 4021691 = 6032537) B6032537
theorem B4464071 : Blo 1238437 4464071 := bstep (se 1 (by rfl) ⟨3348053, by rfl⟩ : syracuseStep 4464071 = 6696107) B6696107
theorem B1859015 : Blo 1238437 1859015 := bstep (se 1 (by rfl) ⟨1394261, by rfl⟩ : syracuseStep 1859015 = 2788523) B2788523
theorem B4185593 : Blo 1238437 4185593 := bstep (se 2 (by rfl) ⟨1569597, by rfl⟩ : syracuseStep 4185593 = 3139195) B3139195
theorem B9674263 : Blo 1238437 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B6700603 : Blo 1238437 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B9051911 : Blo 1238437 9051911 := bstep (se 1 (by rfl) ⟨6788933, by rfl⟩ : syracuseStep 9051911 = 13577867) B13577867
theorem B7061255 : Blo 1238437 7061255 := bstep (se 1 (by rfl) ⟨5295941, by rfl⟩ : syracuseStep 7061255 = 10591883) B10591883
theorem B4185863 : Blo 1238437 4185863 := bstep (se 1 (by rfl) ⟨3139397, by rfl⟩ : syracuseStep 4185863 = 6278795) B6278795
theorem B1859369 : Blo 1238437 1859369 := bstep (se 2 (by rfl) ⟨697263, by rfl⟩ : syracuseStep 1859369 = 1394527) B1394527
theorem B3530537 : Blo 1238437 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B1859375 : Blo 1238437 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B4185917 : Blo 1238437 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B15073283 : Blo 1238437 15073283 := bstep (se 1 (by rfl) ⟨11304962, by rfl⟩ : syracuseStep 15073283 = 22609925) B22609925
theorem B3137575 : Blo 1238437 3137575 := bstep (se 1 (by rfl) ⟨2353181, by rfl⟩ : syracuseStep 3137575 = 4706363) B4706363
theorem B3973495 : Blo 1238437 3973495 := bstep (se 1 (by rfl) ⟨2980121, by rfl⟩ : syracuseStep 3973495 = 5960243) B5960243
theorem B1860047 : Blo 1238437 1860047 := bstep (se 1 (by rfl) ⟨1395035, by rfl⟩ : syracuseStep 1860047 = 2790071) B2790071
theorem B1860089 : Blo 1238437 1860089 := bstep (se 2 (by rfl) ⟨697533, by rfl⟩ : syracuseStep 1860089 = 1395067) B1395067
theorem B1860191 : Blo 1238437 1860191 := bstep (se 1 (by rfl) ⟨1395143, by rfl⟩ : syracuseStep 1860191 = 2790287) B2790287
theorem B14508679 : Blo 1238437 14508679 := bstep (se 1 (by rfl) ⟨10881509, by rfl⟩ : syracuseStep 14508679 = 21763019) B21763019
theorem B3531539 : Blo 1238437 3531539 := bstep (se 1 (by rfl) ⟨2648654, by rfl⟩ : syracuseStep 3531539 = 5297309) B5297309
theorem B2351929 : Blo 1238437 2351929 := bstep (se 2 (by rfl) ⟨881973, by rfl⟩ : syracuseStep 2351929 = 1763947) B1763947
theorem B1393519 : Blo 1238437 1393519 := bstep (se 1 (by rfl) ⟨1045139, by rfl⟩ : syracuseStep 1393519 = 2090279) B2090279
theorem B4703143 : Blo 1238437 4703143 := bstep (se 1 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 4703143 = 7054715) B7054715
theorem B7947193 : Blo 1238437 7947193 := bstep (se 2 (by rfl) ⟨2980197, by rfl⟩ : syracuseStep 7947193 = 5960395) B5960395
theorem B2352233 : Blo 1238437 2352233 := bstep (se 2 (by rfl) ⟨882087, by rfl⟩ : syracuseStep 2352233 = 1764175) B1764175
theorem B10724509 : Blo 1238437 10724509 := bstep (se 3 (by rfl) ⟨2010845, by rfl⟩ : syracuseStep 10724509 = 4021691) B4021691
theorem B2090191 : Blo 1238437 2090191 := bstep (se 1 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 2090191 = 3135287) B3135287
theorem B20382977 : Blo 1238437 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B2786633 : Blo 1238437 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B11912521 : Blo 1238437 11912521 := bstep (se 2 (by rfl) ⟨4467195, by rfl⟩ : syracuseStep 11912521 = 8934391) B8934391
theorem B128722445 : Blo 1238437 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B1238639 : Blo 1238437 1238639 := bstep (se 1 (by rfl) ⟨928979, by rfl⟩ : syracuseStep 1238639 = 1857959) B1857959
theorem B1238695 : Blo 1238437 1238695 := bstep (se 1 (by rfl) ⟨929021, by rfl⟩ : syracuseStep 1238695 = 1858043) B1858043
theorem B101770951 : Blo 1238437 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B9545435 : Blo 1238437 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B1591003 : Blo 1238437 1591003 := bstep (se 1 (by rfl) ⟨1193252, by rfl⟩ : syracuseStep 1591003 = 2386505) B2386505
theorem B2352863 : Blo 1238437 2352863 := bstep (se 1 (by rfl) ⟨1764647, by rfl⟩ : syracuseStep 2352863 = 3529295) B3529295
theorem B1238779 : Blo 1238437 1238779 := bstep (se 1 (by rfl) ⟨929084, by rfl⟩ : syracuseStep 1238779 = 1858169) B1858169
theorem B1238815 : Blo 1238437 1238815 := bstep (se 1 (by rfl) ⟨929111, by rfl⟩ : syracuseStep 1238815 = 1858223) B1858223
theorem B1238847 : Blo 1238437 1238847 := bstep (se 1 (by rfl) ⟨929135, by rfl⟩ : syracuseStep 1238847 = 1858271) B1858271
theorem B1239023 : Blo 1238437 1239023 := bstep (se 1 (by rfl) ⟨929267, by rfl⟩ : syracuseStep 1239023 = 1858535) B1858535
theorem B1394671 : Blo 1238437 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B2091001 : Blo 1238437 2091001 := bstep (se 2 (by rfl) ⟨784125, by rfl⟩ : syracuseStep 2091001 = 1568251) B1568251
theorem B4179977 : Blo 1238437 4179977 := bstep (se 2 (by rfl) ⟨1567491, by rfl⟩ : syracuseStep 4179977 = 3134983) B3134983
theorem B1239195 : Blo 1238437 1239195 := bstep (se 1 (by rfl) ⟨929396, by rfl⟩ : syracuseStep 1239195 = 1858793) B1858793
theorem B2091163 : Blo 1238437 2091163 := bstep (se 1 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 2091163 = 3136745) B3136745
theorem B1239231 : Blo 1238437 1239231 := bstep (se 1 (by rfl) ⟨929423, by rfl⟩ : syracuseStep 1239231 = 1858847) B1858847
theorem B14911699 : Blo 1238437 14911699 := bstep (se 1 (by rfl) ⟨11183774, by rfl⟩ : syracuseStep 14911699 = 22367549) B22367549
theorem B2353387 : Blo 1238437 2353387 := bstep (se 1 (by rfl) ⟨1765040, by rfl⟩ : syracuseStep 2353387 = 3530081) B3530081
theorem B2091271 : Blo 1238437 2091271 := bstep (se 1 (by rfl) ⟨1568453, by rfl⟩ : syracuseStep 2091271 = 3136907) B3136907
theorem B2787623 : Blo 1238437 2787623 := bstep (se 1 (by rfl) ⟨2090717, by rfl⟩ : syracuseStep 2787623 = 4181435) B4181435
theorem B2091305 : Blo 1238437 2091305 := bstep (se 2 (by rfl) ⟨784239, by rfl⟩ : syracuseStep 2091305 = 1568479) B1568479
theorem B2976047 : Blo 1238437 2976047 := bstep (se 1 (by rfl) ⟨2232035, by rfl⟩ : syracuseStep 2976047 = 4464071) B4464071
theorem B1239343 : Blo 1238437 1239343 := bstep (se 1 (by rfl) ⟨929507, by rfl⟩ : syracuseStep 1239343 = 1859015) B1859015
theorem B2787641 : Blo 1238437 2787641 := bstep (se 2 (by rfl) ⟨1045365, by rfl⟩ : syracuseStep 2787641 = 2090731) B2090731
theorem B6359453 : Blo 1238437 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B3180961 : Blo 1238437 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B1239579 : Blo 1238437 1239579 := bstep (se 1 (by rfl) ⟨929684, by rfl⟩ : syracuseStep 1239579 = 1859369) B1859369
theorem B2353691 : Blo 1238437 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B1239583 : Blo 1238437 1239583 := bstep (se 1 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 1239583 = 1859375) B1859375
theorem B1239899 : Blo 1238437 1239899 := bstep (se 1 (by rfl) ⟨929924, by rfl⟩ : syracuseStep 1239899 = 1859849) B1859849
theorem B1239967 : Blo 1238437 1239967 := bstep (se 1 (by rfl) ⟨929975, by rfl⟩ : syracuseStep 1239967 = 1859951) B1859951
theorem B53586967 : Blo 1238437 53586967 := bstep (se 1 (by rfl) ⟨40190225, by rfl⟩ : syracuseStep 53586967 = 80380451) B80380451
theorem B1240111 : Blo 1238437 1240111 := bstep (se 1 (by rfl) ⟨930083, by rfl⟩ : syracuseStep 1240111 = 1860167) B1860167
theorem B1240135 : Blo 1238437 1240135 := bstep (se 1 (by rfl) ⟨930101, by rfl⟩ : syracuseStep 1240135 = 1860203) B1860203
theorem B1567927 : Blo 1238437 1567927 := bstep (se 1 (by rfl) ⟨1175945, by rfl⟩ : syracuseStep 1567927 = 2351891) B2351891
theorem B1240287 : Blo 1238437 1240287 := bstep (se 1 (by rfl) ⟨930215, by rfl⟩ : syracuseStep 1240287 = 1860431) B1860431
theorem B2092297 : Blo 1238437 2092297 := bstep (se 2 (by rfl) ⟨784611, by rfl⟩ : syracuseStep 2092297 = 1569223) B1569223
theorem B4181273 : Blo 1238437 4181273 := bstep (se 2 (by rfl) ⟨1567977, by rfl⟩ : syracuseStep 4181273 = 3135955) B3135955
theorem B4181327 : Blo 1238437 4181327 := bstep (se 1 (by rfl) ⟨3135995, by rfl⟩ : syracuseStep 4181327 = 6271991) B6271991
theorem B30576017 : Blo 1238437 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B15068567 : Blo 1238437 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B2231783 : Blo 1238437 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B9416249 : Blo 1238437 9416249 := bstep (se 2 (by rfl) ⟨3531093, by rfl⟩ : syracuseStep 9416249 = 7062187) B7062187
theorem B2788937 : Blo 1238437 2788937 := bstep (se 2 (by rfl) ⟨1045851, by rfl⟩ : syracuseStep 2788937 = 2091703) B2091703
theorem B2354761 : Blo 1238437 2354761 := bstep (se 2 (by rfl) ⟨883035, by rfl⟩ : syracuseStep 2354761 = 1766071) B1766071
theorem B4468349 : Blo 1238437 4468349 := bstep (se 3 (by rfl) ⟨837815, by rfl⟩ : syracuseStep 4468349 = 1675631) B1675631
theorem B2264719 : Blo 1238437 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B2977555 : Blo 1238437 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B2092871 : Blo 1238437 2092871 := bstep (se 1 (by rfl) ⟨1569653, by rfl⟩ : syracuseStep 2092871 = 3139307) B3139307
theorem B23826271 : Blo 1238437 23826271 := bstep (se 1 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 23826271 = 35739407) B35739407
theorem B17878931 : Blo 1238437 17878931 := bstep (se 1 (by rfl) ⟨13409198, by rfl⟩ : syracuseStep 17878931 = 26818397) B26818397
theorem B2232287 : Blo 1238437 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B15085739 : Blo 1238437 15085739 := bstep (se 1 (by rfl) ⟨11314304, by rfl⟩ : syracuseStep 15085739 = 22628609) B22628609
theorem B3527039 : Blo 1238437 3527039 := bstep (se 1 (by rfl) ⟨2645279, by rfl⟩ : syracuseStep 3527039 = 5290559) B5290559
theorem B8933759 : Blo 1238437 8933759 := bstep (se 1 (by rfl) ⟨6700319, by rfl⟩ : syracuseStep 8933759 = 13400639) B13400639
theorem B5804623 : Blo 1238437 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B4182623 : Blo 1238437 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B12899017 : Blo 1238437 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B8934137 : Blo 1238437 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B2978689 : Blo 1238437 2978689 := bstep (se 2 (by rfl) ⟨1117008, by rfl⟩ : syracuseStep 2978689 = 2234017) B2234017
theorem B14128019 : Blo 1238437 14128019 := bstep (se 1 (by rfl) ⟨10596014, by rfl⟩ : syracuseStep 14128019 = 21192029) B21192029
theorem B14496683 : Blo 1238437 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B2790395 : Blo 1238437 2790395 := bstep (se 1 (by rfl) ⟨2092796, by rfl⟩ : syracuseStep 2790395 = 4185593) B4185593
theorem B6034607 : Blo 1238437 6034607 := bstep (se 1 (by rfl) ⟨4525955, by rfl⟩ : syracuseStep 6034607 = 9051911) B9051911
theorem B4707503 : Blo 1238437 4707503 := bstep (se 1 (by rfl) ⟨3530627, by rfl⟩ : syracuseStep 4707503 = 7061255) B7061255
theorem B2790575 : Blo 1238437 2790575 := bstep (se 1 (by rfl) ⟨2092931, by rfl⟩ : syracuseStep 2790575 = 4185863) B4185863
theorem B2790611 : Blo 1238437 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B7943579 : Blo 1238437 7943579 := bstep (se 1 (by rfl) ⟨5957684, by rfl⟩ : syracuseStep 7943579 = 11915369) B11915369
theorem B5297633 : Blo 1238437 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B2790881 : Blo 1238437 2790881 := bstep (se 2 (by rfl) ⟨1046580, by rfl⟩ : syracuseStep 2790881 = 2093161) B2093161
theorem B5027579 : Blo 1238437 5027579 := bstep (se 1 (by rfl) ⟨3770684, by rfl⟩ : syracuseStep 5027579 = 7541369) B7541369
theorem B4183865 : Blo 1238437 4183865 := bstep (se 2 (by rfl) ⟨1568949, by rfl⟩ : syracuseStep 4183865 = 3137899) B3137899
theorem B6272963 : Blo 1238437 6272963 := bstep (se 1 (by rfl) ⟨4704722, by rfl⟩ : syracuseStep 6272963 = 9409445) B9409445
theorem B4184027 : Blo 1238437 4184027 := bstep (se 1 (by rfl) ⟨3138020, by rfl⟩ : syracuseStep 4184027 = 6276041) B6276041
theorem B3528679 : Blo 1238437 3528679 := bstep (se 1 (by rfl) ⟨2646509, by rfl⟩ : syracuseStep 3528679 = 5293019) B5293019
theorem B3135631 : Blo 1238437 3135631 := bstep (se 1 (by rfl) ⟨2351723, by rfl⟩ : syracuseStep 3135631 = 4703447) B4703447
theorem B5290217 : Blo 1238437 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B4184297 : Blo 1238437 4184297 := bstep (se 2 (by rfl) ⟨1569111, by rfl⟩ : syracuseStep 4184297 = 3138223) B3138223
theorem B2980073 : Blo 1238437 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B6273287 : Blo 1238437 6273287 := bstep (se 1 (by rfl) ⟨4704965, by rfl⟩ : syracuseStep 6273287 = 9409931) B9409931
theorem B15874339 : Blo 1238437 15874339 := bstep (se 1 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 15874339 = 23811509) B23811509
theorem B1857833 : Blo 1238437 1857833 := bstep (se 2 (by rfl) ⟨696687, by rfl⟩ : syracuseStep 1857833 = 1393375) B1393375
theorem B1857839 : Blo 1238437 1857839 := bstep (se 1 (by rfl) ⟨1393379, by rfl⟩ : syracuseStep 1857839 = 2786759) B2786759
theorem B1858079 : Blo 1238437 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B4184729 : Blo 1238437 4184729 := bstep (se 2 (by rfl) ⟨1569273, by rfl⟩ : syracuseStep 4184729 = 3138547) B3138547
theorem B87104261 : Blo 1238437 87104261 := bstep (se 4 (by rfl) ⟨8166024, by rfl⟩ : syracuseStep 87104261 = 16332049) B16332049
theorem B1858463 : Blo 1238437 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B4709279 : Blo 1238437 4709279 := bstep (se 1 (by rfl) ⟨3531959, by rfl⟩ : syracuseStep 4709279 = 7063919) B7063919
theorem B1858511 : Blo 1238437 1858511 := bstep (se 1 (by rfl) ⟨1393883, by rfl⟩ : syracuseStep 1858511 = 2787767) B2787767
theorem B1858601 : Blo 1238437 1858601 := bstep (se 2 (by rfl) ⟨696975, by rfl⟩ : syracuseStep 1858601 = 1393951) B1393951
theorem B3136553 : Blo 1238437 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B1858607 : Blo 1238437 1858607 := bstep (se 1 (by rfl) ⟨1393955, by rfl⟩ : syracuseStep 1858607 = 2787911) B2787911
theorem B1858631 : Blo 1238437 1858631 := bstep (se 1 (by rfl) ⟨1393973, by rfl⟩ : syracuseStep 1858631 = 2787947) B2787947
theorem B3136583 : Blo 1238437 3136583 := bstep (se 1 (by rfl) ⟨2352437, by rfl⟩ : syracuseStep 3136583 = 4704875) B4704875
theorem B6700103 : Blo 1238437 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B15293555 : Blo 1238437 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B7060729 : Blo 1238437 7060729 := bstep (se 2 (by rfl) ⟨2647773, by rfl⟩ : syracuseStep 7060729 = 5295547) B5295547
theorem B1858895 : Blo 1238437 1858895 := bstep (se 1 (by rfl) ⟨1394171, by rfl⟩ : syracuseStep 1858895 = 2788343) B2788343
theorem B7945577 : Blo 1238437 7945577 := bstep (se 2 (by rfl) ⟨2979591, by rfl⟩ : syracuseStep 7945577 = 5959183) B5959183
theorem B4300199 : Blo 1238437 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B1858985 : Blo 1238437 1858985 := bstep (se 2 (by rfl) ⟨697119, by rfl⟩ : syracuseStep 1858985 = 1394239) B1394239
theorem B1859135 : Blo 1238437 1859135 := bstep (se 1 (by rfl) ⟨1394351, by rfl⟩ : syracuseStep 1859135 = 2788703) B2788703
theorem B6274745 : Blo 1238437 6274745 := bstep (se 2 (by rfl) ⟨2353029, by rfl⟩ : syracuseStep 6274745 = 4706059) B4706059
theorem B1859399 : Blo 1238437 1859399 := bstep (se 1 (by rfl) ⟨1394549, by rfl⟩ : syracuseStep 1859399 = 2789099) B2789099
theorem B1859483 : Blo 1238437 1859483 := bstep (se 1 (by rfl) ⟨1394612, by rfl⟩ : syracuseStep 1859483 = 2789225) B2789225
theorem B3350443 : Blo 1238437 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B2351359 : Blo 1238437 2351359 := bstep (se 1 (by rfl) ⟨1763519, by rfl⟩ : syracuseStep 2351359 = 3527039) B3527039
theorem B5955839 : Blo 1238437 5955839 := bstep (se 1 (by rfl) ⟨4466879, by rfl⟩ : syracuseStep 5955839 = 8933759) B8933759
theorem B19882265 : Blo 1238437 19882265 := bstep (se 2 (by rfl) ⟨7455849, by rfl⟩ : syracuseStep 19882265 = 14911699) B14911699
theorem B3137849 : Blo 1238437 3137849 := bstep (se 2 (by rfl) ⟨1176693, by rfl⟩ : syracuseStep 3137849 = 2353387) B2353387
theorem B5956091 : Blo 1238437 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B1860263 : Blo 1238437 1860263 := bstep (se 1 (by rfl) ⟨1395197, by rfl⟩ : syracuseStep 1860263 = 2790395) B2790395
theorem B4023071 : Blo 1238437 4023071 := bstep (se 1 (by rfl) ⟨3017303, by rfl⟩ : syracuseStep 4023071 = 6034607) B6034607
theorem B3138335 : Blo 1238437 3138335 := bstep (se 1 (by rfl) ⟨2353751, by rfl⟩ : syracuseStep 3138335 = 4707503) B4707503
theorem B1860383 : Blo 1238437 1860383 := bstep (se 1 (by rfl) ⟨1395287, by rfl⟩ : syracuseStep 1860383 = 2790575) B2790575
theorem B1860407 : Blo 1238437 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B3531755 : Blo 1238437 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B1860587 : Blo 1238437 1860587 := bstep (se 1 (by rfl) ⟨1395440, by rfl⟩ : syracuseStep 1860587 = 2790881) B2790881
theorem B3351719 : Blo 1238437 3351719 := bstep (se 1 (by rfl) ⟨2513789, by rfl⟩ : syracuseStep 3351719 = 5027579) B5027579
theorem B2786651 : Blo 1238437 2786651 := bstep (se 1 (by rfl) ⟨2089988, by rfl⟩ : syracuseStep 2786651 = 4179977) B4179977
theorem B1238555 : Blo 1238437 1238555 := bstep (se 1 (by rfl) ⟨928916, by rfl⟩ : syracuseStep 1238555 = 1857833) B1857833
theorem B1394203 : Blo 1238437 1394203 := bstep (se 1 (by rfl) ⟨1045652, by rfl⟩ : syracuseStep 1394203 = 2091305) B2091305
theorem B1238559 : Blo 1238437 1238559 := bstep (se 1 (by rfl) ⟨928919, by rfl⟩ : syracuseStep 1238559 = 1857839) B1857839
theorem B1984031 : Blo 1238437 1984031 := bstep (se 1 (by rfl) ⟨1488023, by rfl⟩ : syracuseStep 1984031 = 2976047) B2976047
theorem B2090569 : Blo 1238437 2090569 := bstep (se 2 (by rfl) ⟨783963, by rfl⟩ : syracuseStep 2090569 = 1567927) B1567927
theorem B2786921 : Blo 1238437 2786921 := bstep (se 2 (by rfl) ⟨1045095, by rfl⟩ : syracuseStep 2786921 = 2090191) B2090191
theorem B9414305 : Blo 1238437 9414305 := bstep (se 2 (by rfl) ⟨3530364, by rfl⟩ : syracuseStep 9414305 = 7060729) B7060729
theorem B1238719 : Blo 1238437 1238719 := bstep (se 1 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 1238719 = 1858079) B1858079
theorem B1238975 : Blo 1238437 1238975 := bstep (se 1 (by rfl) ⟨929231, by rfl⟩ : syracuseStep 1238975 = 1858463) B1858463
theorem B3139519 : Blo 1238437 3139519 := bstep (se 1 (by rfl) ⟨2354639, by rfl⟩ : syracuseStep 3139519 = 4709279) B4709279
theorem B1239007 : Blo 1238437 1239007 := bstep (se 1 (by rfl) ⟨929255, by rfl⟩ : syracuseStep 1239007 = 1858511) B1858511
theorem B232278029 : Blo 1238437 232278029 := bstep (se 3 (by rfl) ⟨43552130, by rfl⟩ : syracuseStep 232278029 = 87104261) B87104261
theorem B1239067 : Blo 1238437 1239067 := bstep (se 1 (by rfl) ⟨929300, by rfl⟩ : syracuseStep 1239067 = 1858601) B1858601
theorem B2091035 : Blo 1238437 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B1239071 : Blo 1238437 1239071 := bstep (se 1 (by rfl) ⟨929303, by rfl⟩ : syracuseStep 1239071 = 1858607) B1858607
theorem B1239087 : Blo 1238437 1239087 := bstep (se 1 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 1239087 = 1858631) B1858631
theorem B2091055 : Blo 1238437 2091055 := bstep (se 1 (by rfl) ⟨1568291, by rfl⟩ : syracuseStep 2091055 = 3136583) B3136583
theorem B4466735 : Blo 1238437 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B3139681 : Blo 1238437 3139681 := bstep (se 2 (by rfl) ⟨1177380, by rfl⟩ : syracuseStep 3139681 = 2354761) B2354761
theorem B2787515 : Blo 1238437 2787515 := bstep (se 1 (by rfl) ⟨2090636, by rfl⟩ : syracuseStep 2787515 = 4181273) B4181273
theorem B2787551 : Blo 1238437 2787551 := bstep (se 1 (by rfl) ⟨2090663, by rfl⟩ : syracuseStep 2787551 = 4181327) B4181327
theorem B1239263 : Blo 1238437 1239263 := bstep (se 1 (by rfl) ⟨929447, by rfl⟩ : syracuseStep 1239263 = 1858895) B1858895
theorem B135694601 : Blo 1238437 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B20384011 : Blo 1238437 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B10045711 : Blo 1238437 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B1239323 : Blo 1238437 1239323 := bstep (se 1 (by rfl) ⟨929492, by rfl⟩ : syracuseStep 1239323 = 1858985) B1858985
theorem B6277499 : Blo 1238437 6277499 := bstep (se 1 (by rfl) ⟨4708124, by rfl⟩ : syracuseStep 6277499 = 9416249) B9416249
theorem B1239423 : Blo 1238437 1239423 := bstep (se 1 (by rfl) ⟨929567, by rfl⟩ : syracuseStep 1239423 = 1859135) B1859135
theorem B1239599 : Blo 1238437 1239599 := bstep (se 1 (by rfl) ⟨929699, by rfl⟩ : syracuseStep 1239599 = 1859399) B1859399
theorem B1395247 : Blo 1238437 1395247 := bstep (se 1 (by rfl) ⟨1046435, by rfl⟩ : syracuseStep 1395247 = 2092871) B2092871
theorem B4467257 : Blo 1238437 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B1239655 : Blo 1238437 1239655 := bstep (se 1 (by rfl) ⟨929741, by rfl⟩ : syracuseStep 1239655 = 1859483) B1859483
theorem B4704905 : Blo 1238437 4704905 := bstep (se 2 (by rfl) ⟨1764339, by rfl⟩ : syracuseStep 4704905 = 3528679) B3528679
theorem B2788001 : Blo 1238437 2788001 := bstep (se 2 (by rfl) ⟨1045500, by rfl⟩ : syracuseStep 2788001 = 2091001) B2091001
theorem B4180841 : Blo 1238437 4180841 := bstep (se 2 (by rfl) ⟨1567815, by rfl⟩ : syracuseStep 4180841 = 3135631) B3135631
theorem B2788217 : Blo 1238437 2788217 := bstep (se 2 (by rfl) ⟨1045581, by rfl⟩ : syracuseStep 2788217 = 2091163) B2091163
theorem B1240031 : Blo 1238437 1240031 := bstep (se 1 (by rfl) ⟨930023, by rfl⟩ : syracuseStep 1240031 = 1860047) B1860047
theorem B1240059 : Blo 1238437 1240059 := bstep (se 1 (by rfl) ⟨930044, by rfl⟩ : syracuseStep 1240059 = 1860089) B1860089
theorem B2788361 : Blo 1238437 2788361 := bstep (se 2 (by rfl) ⟨1045635, by rfl⟩ : syracuseStep 2788361 = 2091271) B2091271
theorem B2788415 : Blo 1238437 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B1240127 : Blo 1238437 1240127 := bstep (se 1 (by rfl) ⟨930095, by rfl⟩ : syracuseStep 1240127 = 1860191) B1860191
theorem B2354359 : Blo 1238437 2354359 := bstep (se 1 (by rfl) ⟨1765769, by rfl⟩ : syracuseStep 2354359 = 3531539) B3531539
theorem B1568155 : Blo 1238437 1568155 := bstep (se 1 (by rfl) ⟨1176116, by rfl⟩ : syracuseStep 1568155 = 2352233) B2352233
theorem B19344905 : Blo 1238437 19344905 := bstep (se 2 (by rfl) ⟨7254339, by rfl⟩ : syracuseStep 19344905 = 14508679) B14508679
theorem B17198689 : Blo 1238437 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B5295719 : Blo 1238437 5295719 := bstep (se 1 (by rfl) ⟨3971789, by rfl⟩ : syracuseStep 5295719 = 7943579) B7943579
theorem B85814963 : Blo 1238437 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B1568575 : Blo 1238437 1568575 := bstep (se 1 (by rfl) ⟨1176431, by rfl⟩ : syracuseStep 1568575 = 2352863) B2352863
theorem B2789243 : Blo 1238437 2789243 := bstep (se 1 (by rfl) ⟨2091932, by rfl⟩ : syracuseStep 2789243 = 4183865) B4183865
theorem B6270857 : Blo 1238437 6270857 := bstep (se 2 (by rfl) ⟨2351571, by rfl⟩ : syracuseStep 6270857 = 4703143) B4703143
theorem B10596257 : Blo 1238437 10596257 := bstep (se 2 (by rfl) ⟨3973596, by rfl⟩ : syracuseStep 10596257 = 7947193) B7947193
theorem B4181975 : Blo 1238437 4181975 := bstep (se 1 (by rfl) ⟨3136481, by rfl⟩ : syracuseStep 4181975 = 6272963) B6272963
theorem B2789351 : Blo 1238437 2789351 := bstep (se 1 (by rfl) ⟨2092013, by rfl⟩ : syracuseStep 2789351 = 4184027) B4184027
theorem B3526811 : Blo 1238437 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B2789531 : Blo 1238437 2789531 := bstep (se 1 (by rfl) ⟨2092148, by rfl⟩ : syracuseStep 2789531 = 4184297) B4184297
theorem B1986715 : Blo 1238437 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B4182191 : Blo 1238437 4182191 := bstep (se 1 (by rfl) ⟨3136643, by rfl⟩ : syracuseStep 4182191 = 6273287) B6273287
theorem B14299345 : Blo 1238437 14299345 := bstep (se 2 (by rfl) ⟨5362254, by rfl⟩ : syracuseStep 14299345 = 10724509) B10724509
theorem B4239635 : Blo 1238437 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B2789729 : Blo 1238437 2789729 := bstep (se 2 (by rfl) ⟨1046148, by rfl⟩ : syracuseStep 2789729 = 2092297) B2092297
theorem B1569127 : Blo 1238437 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B2789819 : Blo 1238437 2789819 := bstep (se 1 (by rfl) ⟨2092364, by rfl⟩ : syracuseStep 2789819 = 4184729) B4184729
theorem B10195703 : Blo 1238437 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B3019625 : Blo 1238437 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B5297051 : Blo 1238437 5297051 := bstep (se 1 (by rfl) ⟨3972788, by rfl⟩ : syracuseStep 5297051 = 7945577) B7945577
theorem B1487855 : Blo 1238437 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B3970073 : Blo 1238437 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B2978899 : Blo 1238437 2978899 := bstep (se 1 (by rfl) ⟨2234174, by rfl⟩ : syracuseStep 2978899 = 4468349) B4468349
theorem B4183163 : Blo 1238437 4183163 := bstep (se 1 (by rfl) ⟨3137372, by rfl⟩ : syracuseStep 4183163 = 6274745) B6274745
theorem B1488191 : Blo 1238437 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B10048855 : Blo 1238437 10048855 := bstep (se 1 (by rfl) ⟨7536641, by rfl⟩ : syracuseStep 10048855 = 15073283) B15073283
theorem B4183433 : Blo 1238437 4183433 := bstep (se 2 (by rfl) ⟨1568787, by rfl⟩ : syracuseStep 4183433 = 3137575) B3137575
theorem B10057159 : Blo 1238437 10057159 := bstep (se 1 (by rfl) ⟨7542869, by rfl⟩ : syracuseStep 10057159 = 15085739) B15085739
theorem B21165785 : Blo 1238437 21165785 := bstep (se 2 (by rfl) ⟨7937169, by rfl⟩ : syracuseStep 21165785 = 15874339) B15874339
theorem B5297993 : Blo 1238437 5297993 := bstep (se 2 (by rfl) ⟨1986747, by rfl⟩ : syracuseStep 5297993 = 3973495) B3973495
theorem B4241281 : Blo 1238437 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B9418679 : Blo 1238437 9418679 := bstep (se 1 (by rfl) ⟨7064009, by rfl⟩ : syracuseStep 9418679 = 14128019) B14128019
theorem B7739497 : Blo 1238437 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B13588651 : Blo 1238437 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B1857755 : Blo 1238437 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B3135905 : Blo 1238437 3135905 := bstep (se 2 (by rfl) ⟨1175964, by rfl⟩ : syracuseStep 3135905 = 2351929) B2351929
theorem B6363623 : Blo 1238437 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B1858025 : Blo 1238437 1858025 := bstep (se 2 (by rfl) ⟨696759, by rfl⟩ : syracuseStep 1858025 = 1393519) B1393519
theorem B3971585 : Blo 1238437 3971585 := bstep (se 2 (by rfl) ⟨1489344, by rfl⟩ : syracuseStep 3971585 = 2978689) B2978689
theorem B71449289 : Blo 1238437 71449289 := bstep (se 2 (by rfl) ⟨26793483, by rfl⟩ : syracuseStep 71449289 = 53586967) B53586967
theorem B1858415 : Blo 1238437 1858415 := bstep (se 1 (by rfl) ⟨1393811, by rfl⟩ : syracuseStep 1858415 = 2787623) B2787623
theorem B1858427 : Blo 1238437 1858427 := bstep (se 1 (by rfl) ⟨1393820, by rfl⟩ : syracuseStep 1858427 = 2787641) B2787641
theorem B15883361 : Blo 1238437 15883361 := bstep (se 2 (by rfl) ⟨5956260, by rfl⟩ : syracuseStep 15883361 = 11912521) B11912521
theorem B2866799 : Blo 1238437 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B2121337 : Blo 1238437 2121337 := bstep (se 2 (by rfl) ⟨795501, by rfl⟩ : syracuseStep 2121337 = 1591003) B1591003
theorem B1859291 : Blo 1238437 1859291 := bstep (se 1 (by rfl) ⟨1394468, by rfl⟩ : syracuseStep 1859291 = 2788937) B2788937
theorem B38657821 : Blo 1238437 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B31768361 : Blo 1238437 31768361 := bstep (se 2 (by rfl) ⟨11913135, by rfl⟩ : syracuseStep 31768361 = 23826271) B23826271
theorem B11919287 : Blo 1238437 11919287 := bstep (se 1 (by rfl) ⟨8939465, by rfl⟩ : syracuseStep 11919287 = 17878931) B17878931
theorem B1859561 : Blo 1238437 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B2351207 : Blo 1238437 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B1859687 : Blo 1238437 1859687 := bstep (se 1 (by rfl) ⟨1394765, by rfl⟩ : syracuseStep 1859687 = 2789531) B2789531
theorem B4186241 : Blo 1238437 4186241 := bstep (se 2 (by rfl) ⟨1569840, by rfl⟩ : syracuseStep 4186241 = 3139681) B3139681
theorem B1859819 : Blo 1238437 1859819 := bstep (se 1 (by rfl) ⟨1394864, by rfl⟩ : syracuseStep 1859819 = 2789729) B2789729
theorem B1859879 : Blo 1238437 1859879 := bstep (se 1 (by rfl) ⟨1394909, by rfl⟩ : syracuseStep 1859879 = 2789819) B2789819
theorem B3531367 : Blo 1238437 3531367 := bstep (se 1 (by rfl) ⟨2648525, by rfl⟩ : syracuseStep 3531367 = 5297051) B5297051
theorem B2646715 : Blo 1238437 2646715 := bstep (se 1 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 2646715 = 3970073) B3970073
theorem B11305693 : Blo 1238437 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B1860329 : Blo 1238437 1860329 := bstep (se 2 (by rfl) ⟨697623, by rfl⟩ : syracuseStep 1860329 = 1395247) B1395247
theorem B53019373 : Blo 1238437 53019373 := bstep (se 3 (by rfl) ⟨9941132, by rfl⟩ : syracuseStep 53019373 = 19882265) B19882265
theorem B6276203 : Blo 1238437 6276203 := bstep (se 1 (by rfl) ⟨4707152, by rfl⟩ : syracuseStep 6276203 = 9414305) B9414305
theorem B3531995 : Blo 1238437 3531995 := bstep (se 1 (by rfl) ⟨2648996, by rfl⟩ : syracuseStep 3531995 = 5297993) B5297993
theorem B1394023 : Blo 1238437 1394023 := bstep (se 1 (by rfl) ⟨1045517, by rfl⟩ : syracuseStep 1394023 = 2091035) B2091035
theorem B53577125 : Blo 1238437 53577125 := bstep (se 4 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 53577125 = 10045711) B10045711
theorem B1238503 : Blo 1238437 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B3139145 : Blo 1238437 3139145 := bstep (se 2 (by rfl) ⟨1177179, by rfl⟩ : syracuseStep 3139145 = 2354359) B2354359
theorem B2090603 : Blo 1238437 2090603 := bstep (se 1 (by rfl) ⟨1567952, by rfl⟩ : syracuseStep 2090603 = 3135905) B3135905
theorem B1238683 : Blo 1238437 1238683 := bstep (se 1 (by rfl) ⟨929012, by rfl⟩ : syracuseStep 1238683 = 1858025) B1858025
theorem B2647723 : Blo 1238437 2647723 := bstep (se 1 (by rfl) ⟨1985792, by rfl⟩ : syracuseStep 2647723 = 3971585) B3971585
theorem B2090873 : Blo 1238437 2090873 := bstep (se 2 (by rfl) ⟨784077, by rfl⟩ : syracuseStep 2090873 = 1568155) B1568155
theorem B2787227 : Blo 1238437 2787227 := bstep (se 1 (by rfl) ⟨2090420, by rfl⟩ : syracuseStep 2787227 = 4180841) B4180841
theorem B1238943 : Blo 1238437 1238943 := bstep (se 1 (by rfl) ⟨929207, by rfl⟩ : syracuseStep 1238943 = 1858415) B1858415
theorem B1238951 : Blo 1238437 1238951 := bstep (se 1 (by rfl) ⟨929213, by rfl⟩ : syracuseStep 1238951 = 1858427) B1858427
theorem B2787425 : Blo 1238437 2787425 := bstep (se 2 (by rfl) ⟨1045284, by rfl⟩ : syracuseStep 2787425 = 2090569) B2090569
theorem B22931585 : Blo 1238437 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B2828449 : Blo 1238437 2828449 := bstep (se 2 (by rfl) ⟨1060668, by rfl⟩ : syracuseStep 2828449 = 2121337) B2121337
theorem B12896603 : Blo 1238437 12896603 := bstep (se 1 (by rfl) ⟨9672452, by rfl⟩ : syracuseStep 12896603 = 19344905) B19344905
theorem B1911199 : Blo 1238437 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B2091433 : Blo 1238437 2091433 := bstep (se 2 (by rfl) ⟨784287, by rfl⟩ : syracuseStep 2091433 = 1568575) B1568575
theorem B1239527 : Blo 1238437 1239527 := bstep (se 1 (by rfl) ⟨929645, by rfl⟩ : syracuseStep 1239527 = 1859291) B1859291
theorem B5655041 : Blo 1238437 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B21178907 : Blo 1238437 21178907 := bstep (se 1 (by rfl) ⟨15884180, by rfl⟩ : syracuseStep 21178907 = 31768361) B31768361
theorem B4180571 : Blo 1238437 4180571 := bstep (se 1 (by rfl) ⟨3135428, by rfl⟩ : syracuseStep 4180571 = 6270857) B6270857
theorem B7064171 : Blo 1238437 7064171 := bstep (se 1 (by rfl) ⟨5298128, by rfl⟩ : syracuseStep 7064171 = 10596257) B10596257
theorem B3967613 : Blo 1238437 3967613 := bstep (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) B1487855
theorem B2787983 : Blo 1238437 2787983 := bstep (se 1 (by rfl) ⟨2090987, by rfl⟩ : syracuseStep 2787983 = 4181975) B4181975
theorem B1239707 : Blo 1238437 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B2788073 : Blo 1238437 2788073 := bstep (se 2 (by rfl) ⟨1045527, by rfl⟩ : syracuseStep 2788073 = 2091055) B2091055
theorem B2788127 : Blo 1238437 2788127 := bstep (se 1 (by rfl) ⟨2091095, by rfl⟩ : syracuseStep 2788127 = 4182191) B4182191
theorem B2091899 : Blo 1238437 2091899 := bstep (se 1 (by rfl) ⟨1568924, by rfl⟩ : syracuseStep 2091899 = 3137849) B3137849
theorem B2648953 : Blo 1238437 2648953 := bstep (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) B1986715
theorem B19065793 : Blo 1238437 19065793 := bstep (se 2 (by rfl) ⟨7149672, by rfl⟩ : syracuseStep 19065793 = 14299345) B14299345
theorem B15887461 : Blo 1238437 15887461 := bstep (se 4 (by rfl) ⟨1489449, by rfl⟩ : syracuseStep 15887461 = 2978899) B2978899
theorem B1240175 : Blo 1238437 1240175 := bstep (se 1 (by rfl) ⟨930131, by rfl⟩ : syracuseStep 1240175 = 1860263) B1860263
theorem B2092169 : Blo 1238437 2092169 := bstep (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) B1569127
theorem B2682047 : Blo 1238437 2682047 := bstep (se 1 (by rfl) ⟨2011535, by rfl⟩ : syracuseStep 2682047 = 4023071) B4023071
theorem B2092223 : Blo 1238437 2092223 := bstep (se 1 (by rfl) ⟨1569167, by rfl⟩ : syracuseStep 2092223 = 3138335) B3138335
theorem B1240255 : Blo 1238437 1240255 := bstep (se 1 (by rfl) ⟨930191, by rfl⟩ : syracuseStep 1240255 = 1860383) B1860383
theorem B1240271 : Blo 1238437 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B2354503 : Blo 1238437 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B1240391 : Blo 1238437 1240391 := bstep (se 1 (by rfl) ⟨930293, by rfl⟩ : syracuseStep 1240391 = 1860587) B1860587
theorem B2788775 : Blo 1238437 2788775 := bstep (se 1 (by rfl) ⟨2091581, by rfl⟩ : syracuseStep 2788775 = 4183163) B4183163
theorem B3968509 : Blo 1238437 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B2788955 : Blo 1238437 2788955 := bstep (se 1 (by rfl) ⟨2091716, by rfl⟩ : syracuseStep 2788955 = 4183433) B4183433
theorem B1322687 : Blo 1238437 1322687 := bstep (se 1 (by rfl) ⟨992015, by rfl⟩ : syracuseStep 1322687 = 1984031) B1984031
theorem B14110523 : Blo 1238437 14110523 := bstep (se 1 (by rfl) ⟨10582892, by rfl⟩ : syracuseStep 14110523 = 21165785) B21165785
theorem B16969661 : Blo 1238437 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B6279119 : Blo 1238437 6279119 := bstep (se 1 (by rfl) ⟨4709339, by rfl⟩ : syracuseStep 6279119 = 9418679) B9418679
theorem B2977823 : Blo 1238437 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B2978171 : Blo 1238437 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B13398473 : Blo 1238437 13398473 := bstep (se 2 (by rfl) ⟨5024427, by rfl⟩ : syracuseStep 13398473 = 10048855) B10048855
theorem B47632859 : Blo 1238437 47632859 := bstep (se 1 (by rfl) ⟨35724644, by rfl⟩ : syracuseStep 47632859 = 71449289) B71449289
theorem B10588907 : Blo 1238437 10588907 := bstep (se 1 (by rfl) ⟨7941680, by rfl⟩ : syracuseStep 10588907 = 15883361) B15883361
theorem B57209975 : Blo 1238437 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B10319329 : Blo 1238437 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B3970559 : Blo 1238437 3970559 := bstep (se 1 (by rfl) ⟨2977919, by rfl⟩ : syracuseStep 3970559 = 5955839) B5955839
theorem B18118201 : Blo 1238437 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B3970727 : Blo 1238437 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B3135145 : Blo 1238437 3135145 := bstep (se 2 (by rfl) ⟨1175679, by rfl⟩ : syracuseStep 3135145 = 2351359) B2351359
theorem B27178681 : Blo 1238437 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B6797135 : Blo 1238437 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B2013083 : Blo 1238437 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B2234479 : Blo 1238437 2234479 := bstep (se 1 (by rfl) ⟨1675859, by rfl⟩ : syracuseStep 2234479 = 3351719) B3351719
theorem B1857767 : Blo 1238437 1857767 := bstep (se 1 (by rfl) ⟨1393325, by rfl⟩ : syracuseStep 1857767 = 2786651) B2786651
theorem B1857947 : Blo 1238437 1857947 := bstep (se 1 (by rfl) ⟨1393460, by rfl⟩ : syracuseStep 1857947 = 2786921) B2786921
theorem B154852019 : Blo 1238437 154852019 := bstep (se 1 (by rfl) ⟨116139014, by rfl⟩ : syracuseStep 154852019 = 232278029) B232278029
theorem B1858343 : Blo 1238437 1858343 := bstep (se 1 (by rfl) ⟨1393757, by rfl⟩ : syracuseStep 1858343 = 2787515) B2787515
theorem B1858367 : Blo 1238437 1858367 := bstep (se 1 (by rfl) ⟨1393775, by rfl⟩ : syracuseStep 1858367 = 2787551) B2787551
theorem B90463067 : Blo 1238437 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B4184999 : Blo 1238437 4184999 := bstep (se 1 (by rfl) ⟨3138749, by rfl⟩ : syracuseStep 4184999 = 6277499) B6277499
theorem B3136603 : Blo 1238437 3136603 := bstep (se 1 (by rfl) ⟨2352452, by rfl⟩ : syracuseStep 3136603 = 4704905) B4704905
theorem B1858667 : Blo 1238437 1858667 := bstep (se 1 (by rfl) ⟨1394000, by rfl⟩ : syracuseStep 1858667 = 2788001) B2788001
theorem B1858811 : Blo 1238437 1858811 := bstep (se 1 (by rfl) ⟨1394108, by rfl⟩ : syracuseStep 1858811 = 2788217) B2788217
theorem B13409545 : Blo 1238437 13409545 := bstep (se 2 (by rfl) ⟨5028579, by rfl⟩ : syracuseStep 13409545 = 10057159) B10057159
theorem B1858907 : Blo 1238437 1858907 := bstep (se 1 (by rfl) ⟨1394180, by rfl⟩ : syracuseStep 1858907 = 2788361) B2788361
theorem B1858937 : Blo 1238437 1858937 := bstep (se 2 (by rfl) ⟨697101, by rfl⟩ : syracuseStep 1858937 = 1394203) B1394203
theorem B1858943 : Blo 1238437 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B51543761 : Blo 1238437 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B3530479 : Blo 1238437 3530479 := bstep (se 1 (by rfl) ⟨2647859, by rfl⟩ : syracuseStep 3530479 = 5295719) B5295719
theorem B1859495 : Blo 1238437 1859495 := bstep (se 1 (by rfl) ⟨1394621, by rfl⟩ : syracuseStep 1859495 = 2789243) B2789243
theorem B4186025 : Blo 1238437 4186025 := bstep (se 2 (by rfl) ⟨1569759, by rfl⟩ : syracuseStep 4186025 = 3139519) B3139519
theorem B7946191 : Blo 1238437 7946191 := bstep (se 1 (by rfl) ⟨5959643, by rfl⟩ : syracuseStep 7946191 = 11919287) B11919287
theorem B1859567 : Blo 1238437 1859567 := bstep (se 1 (by rfl) ⟨1394675, by rfl⟩ : syracuseStep 1859567 = 2789351) B2789351
theorem B2548265 : Blo 1238437 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B35718083 : Blo 1238437 35718083 := bstep (se 1 (by rfl) ⟨26788562, by rfl⟩ : syracuseStep 35718083 = 53577125) B53577125
theorem B15074257 : Blo 1238437 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B1393735 : Blo 1238437 1393735 := bstep (se 1 (by rfl) ⟨1045301, by rfl⟩ : syracuseStep 1393735 = 2090603) B2090603
theorem B2647151 : Blo 1238437 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B3531937 : Blo 1238437 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B4531423 : Blo 1238437 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B1393915 : Blo 1238437 1393915 := bstep (se 1 (by rfl) ⟨1045436, by rfl⟩ : syracuseStep 1393915 = 2090873) B2090873
theorem B25421057 : Blo 1238437 25421057 := bstep (se 2 (by rfl) ⟨9532896, by rfl⟩ : syracuseStep 25421057 = 19065793) B19065793
theorem B15287723 : Blo 1238437 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B1238511 : Blo 1238437 1238511 := bstep (se 1 (by rfl) ⟨928883, by rfl⟩ : syracuseStep 1238511 = 1857767) B1857767
theorem B1238631 : Blo 1238437 1238631 := bstep (se 1 (by rfl) ⟨928973, by rfl⟩ : syracuseStep 1238631 = 1857947) B1857947
theorem B3770027 : Blo 1238437 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B2787047 : Blo 1238437 2787047 := bstep (se 1 (by rfl) ⟨2090285, by rfl⟩ : syracuseStep 2787047 = 4180571) B4180571
theorem B3139337 : Blo 1238437 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B1238895 : Blo 1238437 1238895 := bstep (se 1 (by rfl) ⟨929171, by rfl⟩ : syracuseStep 1238895 = 1858343) B1858343
theorem B1238911 : Blo 1238437 1238911 := bstep (se 1 (by rfl) ⟨929183, by rfl⟩ : syracuseStep 1238911 = 1858367) B1858367
theorem B1394599 : Blo 1238437 1394599 := bstep (se 1 (by rfl) ⟨1045949, by rfl⟩ : syracuseStep 1394599 = 2091899) B2091899
theorem B1239111 : Blo 1238437 1239111 := bstep (se 1 (by rfl) ⟨929333, by rfl⟩ : syracuseStep 1239111 = 1858667) B1858667
theorem B1394779 : Blo 1238437 1394779 := bstep (se 1 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 1394779 = 2092169) B2092169
theorem B1788031 : Blo 1238437 1788031 := bstep (se 1 (by rfl) ⟨1341023, by rfl⟩ : syracuseStep 1788031 = 2682047) B2682047
theorem B1394815 : Blo 1238437 1394815 := bstep (se 1 (by rfl) ⟨1046111, by rfl⟩ : syracuseStep 1394815 = 2092223) B2092223
theorem B1239207 : Blo 1238437 1239207 := bstep (se 1 (by rfl) ⟨929405, by rfl⟩ : syracuseStep 1239207 = 1858811) B1858811
theorem B4180193 : Blo 1238437 4180193 := bstep (se 2 (by rfl) ⟨1567572, by rfl⟩ : syracuseStep 4180193 = 3135145) B3135145
theorem B1239271 : Blo 1238437 1239271 := bstep (se 1 (by rfl) ⟨929453, by rfl⟩ : syracuseStep 1239271 = 1858907) B1858907
theorem B1239291 : Blo 1238437 1239291 := bstep (se 1 (by rfl) ⟨929468, by rfl⟩ : syracuseStep 1239291 = 1858937) B1858937
theorem B1239295 : Blo 1238437 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B9407015 : Blo 1238437 9407015 := bstep (se 1 (by rfl) ⟨7055261, by rfl⟩ : syracuseStep 9407015 = 14110523) B14110523
theorem B10594921 : Blo 1238437 10594921 := bstep (se 2 (by rfl) ⟨3973095, by rfl⟩ : syracuseStep 10594921 = 7946191) B7946191
theorem B1239663 : Blo 1238437 1239663 := bstep (se 1 (by rfl) ⟨929747, by rfl⟩ : syracuseStep 1239663 = 1859495) B1859495
theorem B1239711 : Blo 1238437 1239711 := bstep (se 1 (by rfl) ⟨929783, by rfl⟩ : syracuseStep 1239711 = 1859567) B1859567
theorem B1239791 : Blo 1238437 1239791 := bstep (se 1 (by rfl) ⟨929843, by rfl⟩ : syracuseStep 1239791 = 1859687) B1859687
theorem B7940861 : Blo 1238437 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B1239879 : Blo 1238437 1239879 := bstep (se 1 (by rfl) ⟨929909, by rfl⟩ : syracuseStep 1239879 = 1859819) B1859819
theorem B1239919 : Blo 1238437 1239919 := bstep (se 1 (by rfl) ⟨929939, by rfl⟩ : syracuseStep 1239919 = 1859879) B1859879
theorem B1985447 : Blo 1238437 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B6269885 : Blo 1238437 6269885 := bstep (se 3 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 6269885 = 2351207) B2351207
theorem B31755239 : Blo 1238437 31755239 := bstep (se 1 (by rfl) ⟨23816429, by rfl⟩ : syracuseStep 31755239 = 47632859) B47632859
theorem B1240219 : Blo 1238437 1240219 := bstep (se 1 (by rfl) ⟨930164, by rfl⟩ : syracuseStep 1240219 = 1860329) B1860329
theorem B2788577 : Blo 1238437 2788577 := bstep (se 2 (by rfl) ⟨1045716, by rfl⟩ : syracuseStep 2788577 = 2091433) B2091433
theorem B2354663 : Blo 1238437 2354663 := bstep (se 1 (by rfl) ⟨1765997, by rfl⟩ : syracuseStep 2354663 = 3531995) B3531995
theorem B15085061 : Blo 1238437 15085061 := bstep (se 4 (by rfl) ⟨1414224, by rfl⟩ : syracuseStep 15085061 = 2828449) B2828449
theorem B70692497 : Blo 1238437 70692497 := bstep (se 2 (by rfl) ⟨26509686, by rfl⟩ : syracuseStep 70692497 = 53019373) B53019373
theorem B2092763 : Blo 1238437 2092763 := bstep (se 1 (by rfl) ⟨1569572, by rfl⟩ : syracuseStep 2092763 = 3139145) B3139145
theorem B35729261 : Blo 1238437 35729261 := bstep (se 3 (by rfl) ⟨6699236, by rfl⟩ : syracuseStep 35729261 = 13398473) B13398473
theorem B10588157 : Blo 1238437 10588157 := bstep (se 3 (by rfl) ⟨1985279, by rfl⟩ : syracuseStep 10588157 = 3970559) B3970559
theorem B4182137 : Blo 1238437 4182137 := bstep (se 2 (by rfl) ⟨1568301, by rfl⟩ : syracuseStep 4182137 = 3136603) B3136603
theorem B8597735 : Blo 1238437 8597735 := bstep (se 1 (by rfl) ⟨6448301, by rfl⟩ : syracuseStep 8597735 = 12896603) B12896603
theorem B17879393 : Blo 1238437 17879393 := bstep (se 2 (by rfl) ⟨6704772, by rfl⟩ : syracuseStep 17879393 = 13409545) B13409545
theorem B14119271 : Blo 1238437 14119271 := bstep (se 1 (by rfl) ⟨10589453, by rfl⟩ : syracuseStep 14119271 = 21178907) B21178907
theorem B3527165 : Blo 1238437 3527165 := bstep (se 3 (by rfl) ⟨661343, by rfl⟩ : syracuseStep 3527165 = 1322687) B1322687
theorem B137450029 : Blo 1238437 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B2789999 : Blo 1238437 2789999 := bstep (se 1 (by rfl) ⟨2092499, by rfl⟩ : syracuseStep 2789999 = 4184999) B4184999
theorem B13759105 : Blo 1238437 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B36238241 : Blo 1238437 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B4707305 : Blo 1238437 4707305 := bstep (se 2 (by rfl) ⟨1765239, by rfl⟩ : syracuseStep 4707305 = 3530479) B3530479
theorem B2790683 : Blo 1238437 2790683 := bstep (se 1 (by rfl) ⟨2093012, by rfl⟩ : syracuseStep 2790683 = 4186025) B4186025
theorem B2790827 : Blo 1238437 2790827 := bstep (se 1 (by rfl) ⟨2093120, by rfl⟩ : syracuseStep 2790827 = 4186241) B4186241
theorem B2979305 : Blo 1238437 2979305 := bstep (se 2 (by rfl) ⟨1117239, by rfl⟩ : syracuseStep 2979305 = 2234479) B2234479
theorem B7059271 : Blo 1238437 7059271 := bstep (se 1 (by rfl) ⟨5294453, by rfl⟩ : syracuseStep 7059271 = 10588907) B10588907
theorem B4184135 : Blo 1238437 4184135 := bstep (se 1 (by rfl) ⟨3138101, by rfl⟩ : syracuseStep 4184135 = 6276203) B6276203
theorem B38139983 : Blo 1238437 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B4708489 : Blo 1238437 4708489 := bstep (se 2 (by rfl) ⟨1765683, by rfl⟩ : syracuseStep 4708489 = 3531367) B3531367
theorem B3528953 : Blo 1238437 3528953 := bstep (se 2 (by rfl) ⟨1323357, by rfl⟩ : syracuseStep 3528953 = 2646715) B2646715
theorem B1858151 : Blo 1238437 1858151 := bstep (se 1 (by rfl) ⟨1393613, by rfl⟩ : syracuseStep 1858151 = 2787227) B2787227
theorem B1342055 : Blo 1238437 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B1858283 : Blo 1238437 1858283 := bstep (se 1 (by rfl) ⟨1393712, by rfl⟩ : syracuseStep 1858283 = 2787425) B2787425
theorem B21183281 : Blo 1238437 21183281 := bstep (se 2 (by rfl) ⟨7943730, by rfl⟩ : syracuseStep 21183281 = 15887461) B15887461
theorem B4709447 : Blo 1238437 4709447 := bstep (se 1 (by rfl) ⟨3532085, by rfl⟩ : syracuseStep 4709447 = 7064171) B7064171
theorem B2645075 : Blo 1238437 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B1858655 : Blo 1238437 1858655 := bstep (se 1 (by rfl) ⟨1393991, by rfl⟩ : syracuseStep 1858655 = 2787983) B2787983
theorem B103234679 : Blo 1238437 103234679 := bstep (se 1 (by rfl) ⟨77426009, by rfl⟩ : syracuseStep 103234679 = 154852019) B154852019
theorem B1858697 : Blo 1238437 1858697 := bstep (se 2 (by rfl) ⟨697011, by rfl⟩ : syracuseStep 1858697 = 1394023) B1394023
theorem B1858715 : Blo 1238437 1858715 := bstep (se 1 (by rfl) ⟨1394036, by rfl⟩ : syracuseStep 1858715 = 2788073) B2788073
theorem B1858751 : Blo 1238437 1858751 := bstep (se 1 (by rfl) ⟨1394063, by rfl⟩ : syracuseStep 1858751 = 2788127) B2788127
theorem B60308711 : Blo 1238437 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B5291345 : Blo 1238437 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B24157601 : Blo 1238437 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B3530297 : Blo 1238437 3530297 := bstep (se 2 (by rfl) ⟨1323861, by rfl⟩ : syracuseStep 3530297 = 2647723) B2647723
theorem B1859183 : Blo 1238437 1859183 := bstep (se 1 (by rfl) ⟨1394387, by rfl⟩ : syracuseStep 1859183 = 2788775) B2788775
theorem B1859303 : Blo 1238437 1859303 := bstep (se 1 (by rfl) ⟨1394477, by rfl⟩ : syracuseStep 1859303 = 2788955) B2788955
theorem B11313107 : Blo 1238437 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B4186079 : Blo 1238437 4186079 := bstep (se 1 (by rfl) ⟨3139559, by rfl⟩ : syracuseStep 4186079 = 6279119) B6279119
theorem B1859705 : Blo 1238437 1859705 := bstep (se 2 (by rfl) ⟨697389, by rfl⟩ : syracuseStep 1859705 = 1394779) B1394779
theorem B2384041 : Blo 1238437 2384041 := bstep (se 2 (by rfl) ⟨894015, by rfl⟩ : syracuseStep 2384041 = 1788031) B1788031
theorem B1859753 : Blo 1238437 1859753 := bstep (se 2 (by rfl) ⟨697407, by rfl⟩ : syracuseStep 1859753 = 1394815) B1394815
theorem B11919595 : Blo 1238437 11919595 := bstep (se 1 (by rfl) ⟨8939696, by rfl⟩ : syracuseStep 11919595 = 17879393) B17879393
theorem B9412847 : Blo 1238437 9412847 := bstep (se 1 (by rfl) ⟨7059635, by rfl⟩ : syracuseStep 9412847 = 14119271) B14119271
theorem B2351443 : Blo 1238437 2351443 := bstep (se 1 (by rfl) ⟨1763582, by rfl⟩ : syracuseStep 2351443 = 3527165) B3527165
theorem B1859999 : Blo 1238437 1859999 := bstep (se 1 (by rfl) ⟨1394999, by rfl⟩ : syracuseStep 1859999 = 2789999) B2789999
theorem B27181493 : Blo 1238437 27181493 := bstep (se 5 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 27181493 = 2548265) B2548265
theorem B24158827 : Blo 1238437 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B3138203 : Blo 1238437 3138203 := bstep (se 1 (by rfl) ⟨2353652, by rfl⟩ : syracuseStep 3138203 = 4707305) B4707305
theorem B1860455 : Blo 1238437 1860455 := bstep (se 1 (by rfl) ⟨1395341, by rfl⟩ : syracuseStep 1860455 = 2790683) B2790683
theorem B10191815 : Blo 1238437 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B1860551 : Blo 1238437 1860551 := bstep (se 1 (by rfl) ⟨1395413, by rfl⟩ : syracuseStep 1860551 = 2790827) B2790827
theorem B2786795 : Blo 1238437 2786795 := bstep (se 1 (by rfl) ⟨2090096, by rfl⟩ : syracuseStep 2786795 = 4180193) B4180193
theorem B2352635 : Blo 1238437 2352635 := bstep (se 1 (by rfl) ⟨1764476, by rfl⟩ : syracuseStep 2352635 = 3528953) B3528953
theorem B1238767 : Blo 1238437 1238767 := bstep (se 1 (by rfl) ⟨929075, by rfl⟩ : syracuseStep 1238767 = 1858151) B1858151
theorem B1238855 : Blo 1238437 1238855 := bstep (se 1 (by rfl) ⟨929141, by rfl⟩ : syracuseStep 1238855 = 1858283) B1858283
theorem B5293907 : Blo 1238437 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B4179923 : Blo 1238437 4179923 := bstep (se 1 (by rfl) ⟨3134942, by rfl⟩ : syracuseStep 4179923 = 6269885) B6269885
theorem B21170159 : Blo 1238437 21170159 := bstep (se 1 (by rfl) ⟨15877619, by rfl⟩ : syracuseStep 21170159 = 31755239) B31755239
theorem B3139631 : Blo 1238437 3139631 := bstep (se 1 (by rfl) ⟨2354723, by rfl⟩ : syracuseStep 3139631 = 4709447) B4709447
theorem B1763383 : Blo 1238437 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B1239103 : Blo 1238437 1239103 := bstep (se 1 (by rfl) ⟨929327, by rfl⟩ : syracuseStep 1239103 = 1858655) B1858655
theorem B68823119 : Blo 1238437 68823119 := bstep (se 1 (by rfl) ⟨51617339, by rfl⟩ : syracuseStep 68823119 = 103234679) B103234679
theorem B1239131 : Blo 1238437 1239131 := bstep (se 1 (by rfl) ⟨929348, by rfl⟩ : syracuseStep 1239131 = 1858697) B1858697
theorem B1239143 : Blo 1238437 1239143 := bstep (se 1 (by rfl) ⟨929357, by rfl⟩ : syracuseStep 1239143 = 1858715) B1858715
theorem B1239167 : Blo 1238437 1239167 := bstep (se 1 (by rfl) ⟨929375, by rfl⟩ : syracuseStep 1239167 = 1858751) B1858751
theorem B2353531 : Blo 1238437 2353531 := bstep (se 1 (by rfl) ⟨1765148, by rfl⟩ : syracuseStep 2353531 = 3530297) B3530297
theorem B1239455 : Blo 1238437 1239455 := bstep (se 1 (by rfl) ⟨929591, by rfl⟩ : syracuseStep 1239455 = 1859183) B1859183
theorem B1395175 : Blo 1238437 1395175 := bstep (se 1 (by rfl) ⟨1046381, by rfl⟩ : syracuseStep 1395175 = 2092763) B2092763
theorem B1239535 : Blo 1238437 1239535 := bstep (se 1 (by rfl) ⟨929651, by rfl⟩ : syracuseStep 1239535 = 1859303) B1859303
theorem B2788091 : Blo 1238437 2788091 := bstep (se 1 (by rfl) ⟨2091068, by rfl⟩ : syracuseStep 2788091 = 4182137) B4182137
theorem B6277985 : Blo 1238437 6277985 := bstep (se 2 (by rfl) ⟨2354244, by rfl⟩ : syracuseStep 6277985 = 4708489) B4708489
theorem B183266705 : Blo 1238437 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B1764767 : Blo 1238437 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B14126561 : Blo 1238437 14126561 := bstep (se 2 (by rfl) ⟨5297460, by rfl⟩ : syracuseStep 14126561 = 10594921) B10594921
theorem B18345473 : Blo 1238437 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B1986203 : Blo 1238437 1986203 := bstep (se 1 (by rfl) ⟨1489652, by rfl⟩ : syracuseStep 1986203 = 2979305) B2979305
theorem B2092891 : Blo 1238437 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B20099009 : Blo 1238437 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B2789423 : Blo 1238437 2789423 := bstep (se 1 (by rfl) ⟨2092067, by rfl⟩ : syracuseStep 2789423 = 4184135) B4184135
theorem B6041897 : Blo 1238437 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B6271343 : Blo 1238437 6271343 := bstep (se 1 (by rfl) ⟨4703507, by rfl⟩ : syracuseStep 6271343 = 9407015) B9407015
theorem B1323631 : Blo 1238437 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B3527563 : Blo 1238437 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B1569775 : Blo 1238437 1569775 := bstep (se 1 (by rfl) ⟨1177331, by rfl⟩ : syracuseStep 1569775 = 2354663) B2354663
theorem B10056707 : Blo 1238437 10056707 := bstep (se 1 (by rfl) ⟨7542530, by rfl⟩ : syracuseStep 10056707 = 15085061) B15085061
theorem B23819507 : Blo 1238437 23819507 := bstep (se 1 (by rfl) ⟨17864630, by rfl⟩ : syracuseStep 23819507 = 35729261) B35729261
theorem B7542071 : Blo 1238437 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B2790719 : Blo 1238437 2790719 := bstep (se 1 (by rfl) ⟨2093039, by rfl⟩ : syracuseStep 2790719 = 4186079) B4186079
theorem B7058771 : Blo 1238437 7058771 := bstep (se 1 (by rfl) ⟨5294078, by rfl⟩ : syracuseStep 7058771 = 10588157) B10588157
theorem B5731823 : Blo 1238437 5731823 := bstep (se 1 (by rfl) ⟨4298867, by rfl⟩ : syracuseStep 5731823 = 8597735) B8597735
theorem B23812055 : Blo 1238437 23812055 := bstep (se 1 (by rfl) ⟨17859041, by rfl⟩ : syracuseStep 23812055 = 35718083) B35718083
theorem B16947371 : Blo 1238437 16947371 := bstep (se 1 (by rfl) ⟨12710528, by rfl⟩ : syracuseStep 16947371 = 25421057) B25421057
theorem B2513351 : Blo 1238437 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B1858031 : Blo 1238437 1858031 := bstep (se 1 (by rfl) ⟨1393523, by rfl⟩ : syracuseStep 1858031 = 2787047) B2787047
theorem B25426655 : Blo 1238437 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B1858313 : Blo 1238437 1858313 := bstep (se 2 (by rfl) ⟨696867, by rfl⟩ : syracuseStep 1858313 = 1393735) B1393735
theorem B4709249 : Blo 1238437 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B3578813 : Blo 1238437 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B1858553 : Blo 1238437 1858553 := bstep (se 2 (by rfl) ⟨696957, by rfl⟩ : syracuseStep 1858553 = 1393915) B1393915
theorem B14122187 : Blo 1238437 14122187 := bstep (se 1 (by rfl) ⟨10591640, by rfl⟩ : syracuseStep 14122187 = 21183281) B21183281
theorem B1859051 : Blo 1238437 1859051 := bstep (se 1 (by rfl) ⟨1394288, by rfl⟩ : syracuseStep 1859051 = 2788577) B2788577
theorem B40205807 : Blo 1238437 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B16105067 : Blo 1238437 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B9412361 : Blo 1238437 9412361 := bstep (se 2 (by rfl) ⟨3529635, by rfl⟩ : syracuseStep 9412361 = 7059271) B7059271
theorem B47128331 : Blo 1238437 47128331 := bstep (se 1 (by rfl) ⟨35346248, by rfl⟩ : syracuseStep 47128331 = 70692497) B70692497
theorem B1859465 : Blo 1238437 1859465 := bstep (se 2 (by rfl) ⟨697299, by rfl⟩ : syracuseStep 1859465 = 1394599) B1394599
theorem B1859615 : Blo 1238437 1859615 := bstep (se 1 (by rfl) ⟨1394711, by rfl⟩ : syracuseStep 1859615 = 2789423) B2789423
theorem B2351177 : Blo 1238437 2351177 := bstep (se 2 (by rfl) ⟨881691, by rfl⟩ : syracuseStep 2351177 = 1763383) B1763383
theorem B6275231 : Blo 1238437 6275231 := bstep (se 1 (by rfl) ⟨4706423, by rfl⟩ : syracuseStep 6275231 = 9412847) B9412847
theorem B3178721 : Blo 1238437 3178721 := bstep (se 2 (by rfl) ⟨1192020, by rfl⟩ : syracuseStep 3178721 = 2384041) B2384041
theorem B18120995 : Blo 1238437 18120995 := bstep (se 1 (by rfl) ⟨13590746, by rfl⟩ : syracuseStep 18120995 = 27181493) B27181493
theorem B15892793 : Blo 1238437 15892793 := bstep (se 2 (by rfl) ⟨5959797, by rfl⟩ : syracuseStep 15892793 = 11919595) B11919595
theorem B3138041 : Blo 1238437 3138041 := bstep (se 2 (by rfl) ⟨1176765, by rfl⟩ : syracuseStep 3138041 = 2353531) B2353531
theorem B1860233 : Blo 1238437 1860233 := bstep (se 2 (by rfl) ⟨697587, by rfl⟩ : syracuseStep 1860233 = 1395175) B1395175
theorem B32211769 : Blo 1238437 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B1860479 : Blo 1238437 1860479 := bstep (se 1 (by rfl) ⟨1395359, by rfl⟩ : syracuseStep 1860479 = 2790719) B2790719
theorem B4703417 : Blo 1238437 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B2786615 : Blo 1238437 2786615 := bstep (se 1 (by rfl) ⟨2089961, by rfl⟩ : syracuseStep 2786615 = 4179923) B4179923
theorem B11298247 : Blo 1238437 11298247 := bstep (se 1 (by rfl) ⟨8473685, by rfl⟩ : syracuseStep 11298247 = 16947371) B16947371
theorem B1238687 : Blo 1238437 1238687 := bstep (se 1 (by rfl) ⟨929015, by rfl⟩ : syracuseStep 1238687 = 1858031) B1858031
theorem B16951103 : Blo 1238437 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B1238875 : Blo 1238437 1238875 := bstep (se 1 (by rfl) ⟨929156, by rfl⟩ : syracuseStep 1238875 = 1858313) B1858313
theorem B3139499 : Blo 1238437 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B2385875 : Blo 1238437 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B1239035 : Blo 1238437 1239035 := bstep (se 1 (by rfl) ⟨929276, by rfl⟩ : syracuseStep 1239035 = 1858553) B1858553
theorem B9414791 : Blo 1238437 9414791 := bstep (se 1 (by rfl) ⟨7061093, by rfl⟩ : syracuseStep 9414791 = 14122187) B14122187
theorem B122177803 : Blo 1238437 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B1239367 : Blo 1238437 1239367 := bstep (se 1 (by rfl) ⟨929525, by rfl⟩ : syracuseStep 1239367 = 1859051) B1859051
theorem B31418887 : Blo 1238437 31418887 := bstep (se 1 (by rfl) ⟨23564165, by rfl⟩ : syracuseStep 31418887 = 47128331) B47128331
theorem B1239643 : Blo 1238437 1239643 := bstep (se 1 (by rfl) ⟨929732, by rfl⟩ : syracuseStep 1239643 = 1859465) B1859465
theorem B1239803 : Blo 1238437 1239803 := bstep (se 1 (by rfl) ⟨929852, by rfl⟩ : syracuseStep 1239803 = 1859705) B1859705
theorem B1239835 : Blo 1238437 1239835 := bstep (se 1 (by rfl) ⟨929876, by rfl⟩ : syracuseStep 1239835 = 1859753) B1859753
theorem B183528317 : Blo 1238437 183528317 := bstep (se 3 (by rfl) ⟨34411559, by rfl⟩ : syracuseStep 183528317 = 68823119) B68823119
theorem B4180895 : Blo 1238437 4180895 := bstep (se 1 (by rfl) ⟨3135671, by rfl⟩ : syracuseStep 4180895 = 6271343) B6271343
theorem B1239999 : Blo 1238437 1239999 := bstep (se 1 (by rfl) ⟨929999, by rfl⟩ : syracuseStep 1239999 = 1859999) B1859999
theorem B2092135 : Blo 1238437 2092135 := bstep (se 1 (by rfl) ⟨1569101, by rfl⟩ : syracuseStep 2092135 = 3138203) B3138203
theorem B1240303 : Blo 1238437 1240303 := bstep (se 1 (by rfl) ⟨930227, by rfl⟩ : syracuseStep 1240303 = 1860455) B1860455
theorem B6794543 : Blo 1238437 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B1240367 : Blo 1238437 1240367 := bstep (se 1 (by rfl) ⟨930275, by rfl⟩ : syracuseStep 1240367 = 1860551) B1860551
theorem B6704471 : Blo 1238437 6704471 := bstep (se 1 (by rfl) ⟨5028353, by rfl⟩ : syracuseStep 6704471 = 10056707) B10056707
theorem B1764841 : Blo 1238437 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B15879671 : Blo 1238437 15879671 := bstep (se 1 (by rfl) ⟨11909753, by rfl⟩ : syracuseStep 15879671 = 23819507) B23819507
theorem B4705847 : Blo 1238437 4705847 := bstep (se 1 (by rfl) ⟨3529385, by rfl⟩ : syracuseStep 4705847 = 7058771) B7058771
theorem B1568423 : Blo 1238437 1568423 := bstep (se 1 (by rfl) ⟨1176317, by rfl⟩ : syracuseStep 1568423 = 2352635) B2352635
theorem B4706045 : Blo 1238437 4706045 := bstep (se 3 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 4706045 = 1764767) B1764767
theorem B2093033 : Blo 1238437 2093033 := bstep (se 2 (by rfl) ⟨784887, by rfl⟩ : syracuseStep 2093033 = 1569775) B1569775
theorem B2093087 : Blo 1238437 2093087 := bstep (se 1 (by rfl) ⟨1569815, by rfl⟩ : syracuseStep 2093087 = 3139631) B3139631
theorem B1675567 : Blo 1238437 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B9417707 : Blo 1238437 9417707 := bstep (se 1 (by rfl) ⟨7063280, by rfl⟩ : syracuseStep 9417707 = 14126561) B14126561
theorem B10736711 : Blo 1238437 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B1324135 : Blo 1238437 1324135 := bstep (se 1 (by rfl) ⟨993101, by rfl⟩ : syracuseStep 1324135 = 1986203) B1986203
theorem B2790521 : Blo 1238437 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B13399339 : Blo 1238437 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B4027931 : Blo 1238437 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B3135257 : Blo 1238437 3135257 := bstep (se 2 (by rfl) ⟨1175721, by rfl⟩ : syracuseStep 3135257 = 2351443) B2351443
theorem B5028047 : Blo 1238437 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B1857863 : Blo 1238437 1857863 := bstep (se 1 (by rfl) ⟨1393397, by rfl⟩ : syracuseStep 1857863 = 2786795) B2786795
theorem B3529271 : Blo 1238437 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B15284861 : Blo 1238437 15284861 := bstep (se 3 (by rfl) ⟨2865911, by rfl⟩ : syracuseStep 15284861 = 5731823) B5731823
theorem B15874703 : Blo 1238437 15874703 := bstep (se 1 (by rfl) ⟨11906027, by rfl⟩ : syracuseStep 15874703 = 23812055) B23812055
theorem B14113439 : Blo 1238437 14113439 := bstep (se 1 (by rfl) ⟨10585079, by rfl⟩ : syracuseStep 14113439 = 21170159) B21170159
theorem B1858727 : Blo 1238437 1858727 := bstep (se 1 (by rfl) ⟨1394045, by rfl⟩ : syracuseStep 1858727 = 2788091) B2788091
theorem B4185323 : Blo 1238437 4185323 := bstep (se 1 (by rfl) ⟨3138992, by rfl⟩ : syracuseStep 4185323 = 6277985) B6277985
theorem B26803871 : Blo 1238437 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B12230315 : Blo 1238437 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B6274907 : Blo 1238437 6274907 := bstep (se 1 (by rfl) ⟨4706180, by rfl⟩ : syracuseStep 6274907 = 9412361) B9412361
theorem B1860347 : Blo 1238437 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B2090171 : Blo 1238437 2090171 := bstep (se 1 (by rfl) ⟨1567628, by rfl⟩ : syracuseStep 2090171 = 3135257) B3135257
theorem B6276527 : Blo 1238437 6276527 := bstep (se 1 (by rfl) ⟨4707395, by rfl⟩ : syracuseStep 6276527 = 9414791) B9414791
theorem B3352031 : Blo 1238437 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B1238575 : Blo 1238437 1238575 := bstep (se 1 (by rfl) ⟨928931, by rfl⟩ : syracuseStep 1238575 = 1857863) B1857863
theorem B2787263 : Blo 1238437 2787263 := bstep (se 1 (by rfl) ⟨2090447, by rfl⟩ : syracuseStep 2787263 = 4180895) B4180895
theorem B2353121 : Blo 1238437 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B1239151 : Blo 1238437 1239151 := bstep (se 1 (by rfl) ⟨929363, by rfl⟩ : syracuseStep 1239151 = 1858727) B1858727
theorem B10586447 : Blo 1238437 10586447 := bstep (se 1 (by rfl) ⟨7939835, by rfl⟩ : syracuseStep 10586447 = 15879671) B15879671
theorem B17869247 : Blo 1238437 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B8153543 : Blo 1238437 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B1395355 : Blo 1238437 1395355 := bstep (se 1 (by rfl) ⟨1046516, by rfl⟩ : syracuseStep 1395355 = 2093033) B2093033
theorem B1239743 : Blo 1238437 1239743 := bstep (se 1 (by rfl) ⟨929807, by rfl⟩ : syracuseStep 1239743 = 1859615) B1859615
theorem B1395391 : Blo 1238437 1395391 := bstep (se 1 (by rfl) ⟨1046543, by rfl⟩ : syracuseStep 1395391 = 2093087) B2093087
theorem B1567451 : Blo 1238437 1567451 := bstep (se 1 (by rfl) ⟨1175588, by rfl⟩ : syracuseStep 1567451 = 2351177) B2351177
theorem B10595195 : Blo 1238437 10595195 := bstep (se 1 (by rfl) ⟨7946396, by rfl⟩ : syracuseStep 10595195 = 15892793) B15892793
theorem B2092027 : Blo 1238437 2092027 := bstep (se 1 (by rfl) ⟨1569020, by rfl⟩ : syracuseStep 2092027 = 3138041) B3138041
theorem B1240155 : Blo 1238437 1240155 := bstep (se 1 (by rfl) ⟨930116, by rfl⟩ : syracuseStep 1240155 = 1860233) B1860233
theorem B1240319 : Blo 1238437 1240319 := bstep (se 1 (by rfl) ⟨930239, by rfl⟩ : syracuseStep 1240319 = 1860479) B1860479
theorem B6278471 : Blo 1238437 6278471 := bstep (se 1 (by rfl) ⟨4708853, by rfl⟩ : syracuseStep 6278471 = 9417707) B9417707
theorem B17878589 : Blo 1238437 17878589 := bstep (se 3 (by rfl) ⟨3352235, by rfl⟩ : syracuseStep 17878589 = 6704471) B6704471
theorem B11300735 : Blo 1238437 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B2092999 : Blo 1238437 2092999 := bstep (se 1 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 2092999 = 3139499) B3139499
theorem B2789513 : Blo 1238437 2789513 := bstep (se 2 (by rfl) ⟨1046067, by rfl⟩ : syracuseStep 2789513 = 2092135) B2092135
theorem B1765513 : Blo 1238437 1765513 := bstep (se 2 (by rfl) ⟨662067, by rfl⟩ : syracuseStep 1765513 = 1324135) B1324135
theorem B4182461 : Blo 1238437 4182461 := bstep (se 3 (by rfl) ⟨784211, by rfl⟩ : syracuseStep 4182461 = 1568423) B1568423
theorem B9408959 : Blo 1238437 9408959 := bstep (se 1 (by rfl) ⟨7056719, by rfl⟩ : syracuseStep 9408959 = 14113439) B14113439
theorem B122352211 : Blo 1238437 122352211 := bstep (se 1 (by rfl) ⟨91764158, by rfl⟩ : syracuseStep 122352211 = 183528317) B183528317
theorem B2790215 : Blo 1238437 2790215 := bstep (se 1 (by rfl) ⟨2092661, by rfl⟩ : syracuseStep 2790215 = 4185323) B4185323
theorem B60257317 : Blo 1238437 60257317 := bstep (se 4 (by rfl) ⟨5649123, by rfl⟩ : syracuseStep 60257317 = 11298247) B11298247
theorem B6362333 : Blo 1238437 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B4183271 : Blo 1238437 4183271 := bstep (se 1 (by rfl) ⟨3137453, by rfl⟩ : syracuseStep 4183271 = 6274907) B6274907
theorem B4183487 : Blo 1238437 4183487 := bstep (se 1 (by rfl) ⟨3137615, by rfl⟩ : syracuseStep 4183487 = 6275231) B6275231
theorem B2119147 : Blo 1238437 2119147 := bstep (se 1 (by rfl) ⟨1589360, by rfl⟩ : syracuseStep 2119147 = 3178721) B3178721
theorem B12080663 : Blo 1238437 12080663 := bstep (se 1 (by rfl) ⟨9060497, by rfl⟩ : syracuseStep 12080663 = 18120995) B18120995
theorem B162903737 : Blo 1238437 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B2234089 : Blo 1238437 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B41891849 : Blo 1238437 41891849 := bstep (se 2 (by rfl) ⟨15709443, by rfl⟩ : syracuseStep 41891849 = 31418887) B31418887
theorem B7157807 : Blo 1238437 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B3135611 : Blo 1238437 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B1857743 : Blo 1238437 1857743 := bstep (se 1 (by rfl) ⟨1393307, by rfl⟩ : syracuseStep 1857743 = 2786615) B2786615
theorem B2685287 : Blo 1238437 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B42949025 : Blo 1238437 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B9411389 : Blo 1238437 9411389 := bstep (se 3 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 9411389 = 3529271) B3529271
theorem B17865785 : Blo 1238437 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B10189907 : Blo 1238437 10189907 := bstep (se 1 (by rfl) ⟨7642430, by rfl⟩ : syracuseStep 10189907 = 15284861) B15284861
theorem B10583135 : Blo 1238437 10583135 := bstep (se 1 (by rfl) ⟨7937351, by rfl⟩ : syracuseStep 10583135 = 15874703) B15874703
theorem B4529695 : Blo 1238437 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B3137231 : Blo 1238437 3137231 := bstep (se 1 (by rfl) ⟨2352923, by rfl⟩ : syracuseStep 3137231 = 4705847) B4705847
theorem B3137363 : Blo 1238437 3137363 := bstep (se 1 (by rfl) ⟨2353022, by rfl⟩ : syracuseStep 3137363 = 4706045) B4706045
theorem B1859675 : Blo 1238437 1859675 := bstep (se 1 (by rfl) ⟨1394756, by rfl⟩ : syracuseStep 1859675 = 2789513) B2789513
theorem B1860143 : Blo 1238437 1860143 := bstep (se 1 (by rfl) ⟨1395107, by rfl⟩ : syracuseStep 1860143 = 2790215) B2790215
theorem B163136281 : Blo 1238437 163136281 := bstep (se 2 (by rfl) ⟨61176105, by rfl⟩ : syracuseStep 163136281 = 122352211) B122352211
theorem B1393447 : Blo 1238437 1393447 := bstep (se 1 (by rfl) ⟨1045085, by rfl⟩ : syracuseStep 1393447 = 2090171) B2090171
theorem B1860473 : Blo 1238437 1860473 := bstep (se 2 (by rfl) ⟨697677, by rfl⟩ : syracuseStep 1860473 = 1395355) B1395355
theorem B1860521 : Blo 1238437 1860521 := bstep (se 2 (by rfl) ⟨697695, by rfl⟩ : syracuseStep 1860521 = 1395391) B1395391
theorem B8053775 : Blo 1238437 8053775 := bstep (se 1 (by rfl) ⟨6040331, by rfl⟩ : syracuseStep 8053775 = 12080663) B12080663
theorem B108602491 : Blo 1238437 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B27927899 : Blo 1238437 27927899 := bstep (se 1 (by rfl) ⟨20945924, by rfl⟩ : syracuseStep 27927899 = 41891849) B41891849
theorem B2090407 : Blo 1238437 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B1238495 : Blo 1238437 1238495 := bstep (se 1 (by rfl) ⟨928871, by rfl⟩ : syracuseStep 1238495 = 1857743) B1857743
theorem B28632683 : Blo 1238437 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B11912831 : Blo 1238437 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B4179869 : Blo 1238437 4179869 := bstep (se 3 (by rfl) ⟨783725, by rfl⟩ : syracuseStep 4179869 = 1567451) B1567451
theorem B7063463 : Blo 1238437 7063463 := bstep (se 1 (by rfl) ⟨5297597, by rfl⟩ : syracuseStep 7063463 = 10595195) B10595195
theorem B6039593 : Blo 1238437 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B6793271 : Blo 1238437 6793271 := bstep (se 1 (by rfl) ⟨5094953, by rfl⟩ : syracuseStep 6793271 = 10189907) B10189907
theorem B7055423 : Blo 1238437 7055423 := bstep (se 1 (by rfl) ⟨5291567, by rfl⟩ : syracuseStep 7055423 = 10583135) B10583135
theorem B2091487 : Blo 1238437 2091487 := bstep (se 1 (by rfl) ⟨1568615, by rfl⟩ : syracuseStep 2091487 = 3137231) B3137231
theorem B2091575 : Blo 1238437 2091575 := bstep (se 1 (by rfl) ⟨1568681, by rfl⟩ : syracuseStep 2091575 = 3137363) B3137363
theorem B2354017 : Blo 1238437 2354017 := bstep (se 2 (by rfl) ⟨882756, by rfl⟩ : syracuseStep 2354017 = 1765513) B1765513
theorem B2788307 : Blo 1238437 2788307 := bstep (se 1 (by rfl) ⟨2091230, by rfl⟩ : syracuseStep 2788307 = 4182461) B4182461
theorem B1240231 : Blo 1238437 1240231 := bstep (se 1 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 1240231 = 1860347) B1860347
theorem B2788847 : Blo 1238437 2788847 := bstep (se 1 (by rfl) ⟨2091635, by rfl⟩ : syracuseStep 2788847 = 4183271) B4183271
theorem B2788991 : Blo 1238437 2788991 := bstep (se 1 (by rfl) ⟨2091743, by rfl⟩ : syracuseStep 2788991 = 4183487) B4183487
theorem B1568747 : Blo 1238437 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B2789369 : Blo 1238437 2789369 := bstep (se 2 (by rfl) ⟨1046013, by rfl⟩ : syracuseStep 2789369 = 2092027) B2092027
theorem B4771871 : Blo 1238437 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B80343089 : Blo 1238437 80343089 := bstep (se 2 (by rfl) ⟨30128658, by rfl⟩ : syracuseStep 80343089 = 60257317) B60257317
theorem B7057631 : Blo 1238437 7057631 := bstep (se 1 (by rfl) ⟨5293223, by rfl⟩ : syracuseStep 7057631 = 10586447) B10586447
theorem B1790191 : Blo 1238437 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B5435695 : Blo 1238437 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B45208469 : Blo 1238437 45208469 := bstep (se 6 (by rfl) ⟨1059573, by rfl⟩ : syracuseStep 45208469 = 2119147) B2119147
theorem B2978785 : Blo 1238437 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B7533823 : Blo 1238437 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B2790665 : Blo 1238437 2790665 := bstep (se 2 (by rfl) ⟨1046499, by rfl⟩ : syracuseStep 2790665 = 2092999) B2092999
theorem B6272639 : Blo 1238437 6272639 := bstep (se 1 (by rfl) ⟨4704479, by rfl⟩ : syracuseStep 6272639 = 9408959) B9408959
theorem B4241555 : Blo 1238437 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B4184351 : Blo 1238437 4184351 := bstep (se 1 (by rfl) ⟨3138263, by rfl⟩ : syracuseStep 4184351 = 6276527) B6276527
theorem B2234687 : Blo 1238437 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B1858175 : Blo 1238437 1858175 := bstep (se 1 (by rfl) ⟨1393631, by rfl⟩ : syracuseStep 1858175 = 2787263) B2787263
theorem B6274259 : Blo 1238437 6274259 := bstep (se 1 (by rfl) ⟨4705694, by rfl⟩ : syracuseStep 6274259 = 9411389) B9411389
theorem B11910523 : Blo 1238437 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B4185647 : Blo 1238437 4185647 := bstep (se 1 (by rfl) ⟨3139235, by rfl⟩ : syracuseStep 4185647 = 6278471) B6278471
theorem B11919059 : Blo 1238437 11919059 := bstep (se 1 (by rfl) ⟨8939294, by rfl⟩ : syracuseStep 11919059 = 17878589) B17878589
theorem B30138979 : Blo 1238437 30138979 := bstep (se 1 (by rfl) ⟨22604234, by rfl⟩ : syracuseStep 30138979 = 45208469) B45208469
theorem B1860443 : Blo 1238437 1860443 := bstep (se 1 (by rfl) ⟨1395332, by rfl⟩ : syracuseStep 1860443 = 2790665) B2790665
theorem B217515041 : Blo 1238437 217515041 := bstep (se 2 (by rfl) ⟨81568140, by rfl⟩ : syracuseStep 217515041 = 163136281) B163136281
theorem B19088455 : Blo 1238437 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B3138689 : Blo 1238437 3138689 := bstep (se 2 (by rfl) ⟨1177008, by rfl⟩ : syracuseStep 3138689 = 2354017) B2354017
theorem B2786579 : Blo 1238437 2786579 := bstep (se 1 (by rfl) ⟨2089934, by rfl⟩ : syracuseStep 2786579 = 4179869) B4179869
theorem B4703615 : Blo 1238437 4703615 := bstep (se 1 (by rfl) ⟨3527711, by rfl⟩ : syracuseStep 4703615 = 7055423) B7055423
theorem B2827703 : Blo 1238437 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B144803321 : Blo 1238437 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B10045097 : Blo 1238437 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B1394383 : Blo 1238437 1394383 := bstep (se 1 (by rfl) ⟨1045787, by rfl⟩ : syracuseStep 1394383 = 2091575) B2091575
theorem B1238783 : Blo 1238437 1238783 := bstep (se 1 (by rfl) ⟨929087, by rfl⟩ : syracuseStep 1238783 = 1858175) B1858175
theorem B2787209 : Blo 1238437 2787209 := bstep (se 2 (by rfl) ⟨1045203, by rfl⟩ : syracuseStep 2787209 = 2090407) B2090407
theorem B3181247 : Blo 1238437 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B53562059 : Blo 1238437 53562059 := bstep (se 1 (by rfl) ⟨40171544, by rfl⟩ : syracuseStep 53562059 = 80343089) B80343089
theorem B1239783 : Blo 1238437 1239783 := bstep (se 1 (by rfl) ⟨929837, by rfl⟩ : syracuseStep 1239783 = 1859675) B1859675
theorem B4705087 : Blo 1238437 4705087 := bstep (se 1 (by rfl) ⟨3528815, by rfl⟩ : syracuseStep 4705087 = 7057631) B7057631
theorem B2386921 : Blo 1238437 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B1240095 : Blo 1238437 1240095 := bstep (se 1 (by rfl) ⟨930071, by rfl⟩ : syracuseStep 1240095 = 1860143) B1860143
theorem B1240315 : Blo 1238437 1240315 := bstep (se 1 (by rfl) ⟨930236, by rfl⟩ : syracuseStep 1240315 = 1860473) B1860473
theorem B1240347 : Blo 1238437 1240347 := bstep (se 1 (by rfl) ⟨930260, by rfl⟩ : syracuseStep 1240347 = 1860521) B1860521
theorem B2788649 : Blo 1238437 2788649 := bstep (se 2 (by rfl) ⟨1045743, by rfl⟩ : syracuseStep 2788649 = 2091487) B2091487
theorem B5369183 : Blo 1238437 5369183 := bstep (se 1 (by rfl) ⟨4026887, by rfl⟩ : syracuseStep 5369183 = 8053775) B8053775
theorem B5959165 : Blo 1238437 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B4181759 : Blo 1238437 4181759 := bstep (se 1 (by rfl) ⟨3136319, by rfl⟩ : syracuseStep 4181759 = 6272639) B6272639
theorem B7941887 : Blo 1238437 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B4026395 : Blo 1238437 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B2789567 : Blo 1238437 2789567 := bstep (se 1 (by rfl) ⟨2092175, by rfl⟩ : syracuseStep 2789567 = 4184351) B4184351
theorem B15880697 : Blo 1238437 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B4182839 : Blo 1238437 4182839 := bstep (se 1 (by rfl) ⟨3137129, by rfl⟩ : syracuseStep 4182839 = 6274259) B6274259
theorem B2790431 : Blo 1238437 2790431 := bstep (se 1 (by rfl) ⟨2092823, by rfl⟩ : syracuseStep 2790431 = 4185647) B4185647
theorem B4183325 : Blo 1238437 4183325 := bstep (se 3 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 4183325 = 1568747) B1568747
theorem B7247593 : Blo 1238437 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B18618599 : Blo 1238437 18618599 := bstep (se 1 (by rfl) ⟨13963949, by rfl⟩ : syracuseStep 18618599 = 27927899) B27927899
theorem B1857929 : Blo 1238437 1857929 := bstep (se 2 (by rfl) ⟨696723, by rfl⟩ : syracuseStep 1857929 = 1393447) B1393447
theorem B4708975 : Blo 1238437 4708975 := bstep (se 1 (by rfl) ⟨3531731, by rfl⟩ : syracuseStep 4708975 = 7063463) B7063463
theorem B3971713 : Blo 1238437 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B4528847 : Blo 1238437 4528847 := bstep (se 1 (by rfl) ⟨3396635, by rfl⟩ : syracuseStep 4528847 = 6793271) B6793271
theorem B1858871 : Blo 1238437 1858871 := bstep (se 1 (by rfl) ⟨1394153, by rfl⟩ : syracuseStep 1858871 = 2788307) B2788307
theorem B1859231 : Blo 1238437 1859231 := bstep (se 1 (by rfl) ⟨1394423, by rfl⟩ : syracuseStep 1859231 = 2788847) B2788847
theorem B1859327 : Blo 1238437 1859327 := bstep (se 1 (by rfl) ⟨1394495, by rfl⟩ : syracuseStep 1859327 = 2788991) B2788991
theorem B7946039 : Blo 1238437 7946039 := bstep (se 1 (by rfl) ⟨5959529, by rfl⟩ : syracuseStep 7946039 = 11919059) B11919059
theorem B1859579 : Blo 1238437 1859579 := bstep (se 1 (by rfl) ⟨1394684, by rfl⟩ : syracuseStep 1859579 = 2789369) B2789369
theorem B1859711 : Blo 1238437 1859711 := bstep (se 1 (by rfl) ⟨1394783, by rfl⟩ : syracuseStep 1859711 = 2789567) B2789567
theorem B1860287 : Blo 1238437 1860287 := bstep (se 1 (by rfl) ⟨1395215, by rfl⟩ : syracuseStep 1860287 = 2790431) B2790431
theorem B1885135 : Blo 1238437 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B96535547 : Blo 1238437 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B12412399 : Blo 1238437 12412399 := bstep (se 1 (by rfl) ⟨9309299, by rfl⟩ : syracuseStep 12412399 = 18618599) B18618599
theorem B1238619 : Blo 1238437 1238619 := bstep (se 1 (by rfl) ⟨928964, by rfl⟩ : syracuseStep 1238619 = 1857929) B1857929
theorem B1239247 : Blo 1238437 1239247 := bstep (se 1 (by rfl) ⟨929435, by rfl⟩ : syracuseStep 1239247 = 1858871) B1858871
theorem B1239487 : Blo 1238437 1239487 := bstep (se 1 (by rfl) ⟨929615, by rfl⟩ : syracuseStep 1239487 = 1859231) B1859231
theorem B2787839 : Blo 1238437 2787839 := bstep (se 1 (by rfl) ⟨2090879, by rfl⟩ : syracuseStep 2787839 = 4181759) B4181759
theorem B5294591 : Blo 1238437 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B1239551 : Blo 1238437 1239551 := bstep (se 1 (by rfl) ⟨929663, by rfl⟩ : syracuseStep 1239551 = 1859327) B1859327
theorem B1239719 : Blo 1238437 1239719 := bstep (se 1 (by rfl) ⟨929789, by rfl⟩ : syracuseStep 1239719 = 1859579) B1859579
theorem B10587131 : Blo 1238437 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B2788559 : Blo 1238437 2788559 := bstep (se 1 (by rfl) ⟨2091419, by rfl⟩ : syracuseStep 2788559 = 4182839) B4182839
theorem B1240295 : Blo 1238437 1240295 := bstep (se 1 (by rfl) ⟨930221, by rfl⟩ : syracuseStep 1240295 = 1860443) B1860443
theorem B145010027 : Blo 1238437 145010027 := bstep (se 1 (by rfl) ⟨108757520, by rfl⟩ : syracuseStep 145010027 = 217515041) B217515041
theorem B2092459 : Blo 1238437 2092459 := bstep (se 1 (by rfl) ⟨1569344, by rfl⟩ : syracuseStep 2092459 = 3138689) B3138689
theorem B40185305 : Blo 1238437 40185305 := bstep (se 2 (by rfl) ⟨15069489, by rfl⟩ : syracuseStep 40185305 = 30138979) B30138979
theorem B6278633 : Blo 1238437 6278633 := bstep (se 2 (by rfl) ⟨2354487, by rfl⟩ : syracuseStep 6278633 = 4708975) B4708975
theorem B5295617 : Blo 1238437 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B2788883 : Blo 1238437 2788883 := bstep (se 1 (by rfl) ⟨2091662, by rfl⟩ : syracuseStep 2788883 = 4183325) B4183325
theorem B6696731 : Blo 1238437 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B3182561 : Blo 1238437 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B3019231 : Blo 1238437 3019231 := bstep (se 1 (by rfl) ⟨2264423, by rfl⟩ : syracuseStep 3019231 = 4528847) B4528847
theorem B9663457 : Blo 1238437 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B5297359 : Blo 1238437 5297359 := bstep (se 1 (by rfl) ⟨3973019, by rfl⟩ : syracuseStep 5297359 = 7946039) B7946039
theorem B2684263 : Blo 1238437 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B1857719 : Blo 1238437 1857719 := bstep (se 1 (by rfl) ⟨1393289, by rfl⟩ : syracuseStep 1857719 = 2786579) B2786579
theorem B3135743 : Blo 1238437 3135743 := bstep (se 1 (by rfl) ⟨2351807, by rfl⟩ : syracuseStep 3135743 = 4703615) B4703615
theorem B6273449 : Blo 1238437 6273449 := bstep (se 2 (by rfl) ⟨2352543, by rfl⟩ : syracuseStep 6273449 = 4705087) B4705087
theorem B1858139 : Blo 1238437 1858139 := bstep (se 1 (by rfl) ⟨1393604, by rfl⟩ : syracuseStep 1858139 = 2787209) B2787209
theorem B25451273 : Blo 1238437 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B2120831 : Blo 1238437 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B35708039 : Blo 1238437 35708039 := bstep (se 1 (by rfl) ⟨26781029, by rfl⟩ : syracuseStep 35708039 = 53562059) B53562059
theorem B7945553 : Blo 1238437 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B1859099 : Blo 1238437 1859099 := bstep (se 1 (by rfl) ⟨1394324, by rfl⟩ : syracuseStep 1859099 = 2788649) B2788649
theorem B3579455 : Blo 1238437 3579455 := bstep (se 1 (by rfl) ⟨2684591, by rfl⟩ : syracuseStep 3579455 = 5369183) B5369183
theorem B1859177 : Blo 1238437 1859177 := bstep (se 2 (by rfl) ⟨697191, by rfl⟩ : syracuseStep 1859177 = 1394383) B1394383
theorem B64357031 : Blo 1238437 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B1238479 : Blo 1238437 1238479 := bstep (se 1 (by rfl) ⟨928859, by rfl⟩ : syracuseStep 1238479 = 1857719) B1857719
theorem B2090495 : Blo 1238437 2090495 := bstep (se 1 (by rfl) ⟨1567871, by rfl⟩ : syracuseStep 2090495 = 3135743) B3135743
theorem B7063145 : Blo 1238437 7063145 := bstep (se 2 (by rfl) ⟨2648679, by rfl⟩ : syracuseStep 7063145 = 5297359) B5297359
theorem B1238759 : Blo 1238437 1238759 := bstep (se 1 (by rfl) ⟨929069, by rfl⟩ : syracuseStep 1238759 = 1858139) B1858139
theorem B16549865 : Blo 1238437 16549865 := bstep (se 2 (by rfl) ⟨6206199, by rfl⟩ : syracuseStep 16549865 = 12412399) B12412399
theorem B26790203 : Blo 1238437 26790203 := bstep (se 1 (by rfl) ⟨20092652, by rfl⟩ : syracuseStep 26790203 = 40185305) B40185305
theorem B1239399 : Blo 1238437 1239399 := bstep (se 1 (by rfl) ⟨929549, by rfl⟩ : syracuseStep 1239399 = 1859099) B1859099
theorem B2386303 : Blo 1238437 2386303 := bstep (se 1 (by rfl) ⟨1789727, by rfl⟩ : syracuseStep 2386303 = 3579455) B3579455
theorem B1239451 : Blo 1238437 1239451 := bstep (se 1 (by rfl) ⟨929588, by rfl⟩ : syracuseStep 1239451 = 1859177) B1859177
theorem B1239807 : Blo 1238437 1239807 := bstep (se 1 (by rfl) ⟨929855, by rfl⟩ : syracuseStep 1239807 = 1859711) B1859711
theorem B1240191 : Blo 1238437 1240191 := bstep (se 1 (by rfl) ⟨930143, by rfl⟩ : syracuseStep 1240191 = 1860287) B1860287
theorem B4025641 : Blo 1238437 4025641 := bstep (se 2 (by rfl) ⟨1509615, by rfl⟩ : syracuseStep 4025641 = 3019231) B3019231
theorem B4182299 : Blo 1238437 4182299 := bstep (se 1 (by rfl) ⟨3136724, by rfl⟩ : syracuseStep 4182299 = 6273449) B6273449
theorem B2789945 : Blo 1238437 2789945 := bstep (se 2 (by rfl) ⟨1046229, by rfl⟩ : syracuseStep 2789945 = 2092459) B2092459
theorem B7058087 : Blo 1238437 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B1413887 : Blo 1238437 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B5297035 : Blo 1238437 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B2513513 : Blo 1238437 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B12884609 : Blo 1238437 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B1858559 : Blo 1238437 1858559 := bstep (se 1 (by rfl) ⟨1393919, by rfl⟩ : syracuseStep 1858559 = 2787839) B2787839
theorem B3529727 : Blo 1238437 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B3579017 : Blo 1238437 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B67870061 : Blo 1238437 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B23805359 : Blo 1238437 23805359 := bstep (se 1 (by rfl) ⟨17854019, by rfl⟩ : syracuseStep 23805359 = 35708039) B35708039
theorem B1859039 : Blo 1238437 1859039 := bstep (se 1 (by rfl) ⟨1394279, by rfl⟩ : syracuseStep 1859039 = 2788559) B2788559
theorem B96673351 : Blo 1238437 96673351 := bstep (se 1 (by rfl) ⟨72505013, by rfl⟩ : syracuseStep 96673351 = 145010027) B145010027
theorem B4185755 : Blo 1238437 4185755 := bstep (se 1 (by rfl) ⟨3139316, by rfl⟩ : syracuseStep 4185755 = 6278633) B6278633
theorem B3530411 : Blo 1238437 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B1859255 : Blo 1238437 1859255 := bstep (se 1 (by rfl) ⟨1394441, by rfl⟩ : syracuseStep 1859255 = 2788883) B2788883
theorem B4464487 : Blo 1238437 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B2121707 : Blo 1238437 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B1859963 : Blo 1238437 1859963 := bstep (se 1 (by rfl) ⟨1394972, by rfl⟩ : syracuseStep 1859963 = 2789945) B2789945
theorem B1393663 : Blo 1238437 1393663 := bstep (se 1 (by rfl) ⟨1045247, by rfl⟩ : syracuseStep 1393663 = 2090495) B2090495
theorem B7062713 : Blo 1238437 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B38176181 : Blo 1238437 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B17860135 : Blo 1238437 17860135 := bstep (se 1 (by rfl) ⟨13395101, by rfl⟩ : syracuseStep 17860135 = 26790203) B26790203
theorem B34358957 : Blo 1238437 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B5367521 : Blo 1238437 5367521 := bstep (se 2 (by rfl) ⟨2012820, by rfl⟩ : syracuseStep 5367521 = 4025641) B4025641
theorem B1239039 : Blo 1238437 1239039 := bstep (se 1 (by rfl) ⟨929279, by rfl⟩ : syracuseStep 1239039 = 1858559) B1858559
theorem B2353151 : Blo 1238437 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B45246707 : Blo 1238437 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B15870239 : Blo 1238437 15870239 := bstep (se 1 (by rfl) ⟨11902679, by rfl⟩ : syracuseStep 15870239 = 23805359) B23805359
theorem B1239359 : Blo 1238437 1239359 := bstep (se 1 (by rfl) ⟨929519, by rfl⟩ : syracuseStep 1239359 = 1859039) B1859039
theorem B2353607 : Blo 1238437 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B1239503 : Blo 1238437 1239503 := bstep (se 1 (by rfl) ⟨929627, by rfl⟩ : syracuseStep 1239503 = 1859255) B1859255
theorem B2788199 : Blo 1238437 2788199 := bstep (se 1 (by rfl) ⟨2091149, by rfl⟩ : syracuseStep 2788199 = 4182299) B4182299
theorem B42904687 : Blo 1238437 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B4705391 : Blo 1238437 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B1675675 : Blo 1238437 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B12726949 : Blo 1238437 12726949 := bstep (se 4 (by rfl) ⟨1193151, by rfl⟩ : syracuseStep 12726949 = 2386303) B2386303
theorem B128897801 : Blo 1238437 128897801 := bstep (se 2 (by rfl) ⟨48336675, by rfl⟩ : syracuseStep 128897801 = 96673351) B96673351
theorem B2790503 : Blo 1238437 2790503 := bstep (se 1 (by rfl) ⟨2092877, by rfl⟩ : syracuseStep 2790503 = 4185755) B4185755
theorem B5952649 : Blo 1238437 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B1414471 : Blo 1238437 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B4708763 : Blo 1238437 4708763 := bstep (se 1 (by rfl) ⟨3531572, by rfl⟩ : syracuseStep 4708763 = 7063145) B7063145
theorem B11033243 : Blo 1238437 11033243 := bstep (se 1 (by rfl) ⟨8274932, by rfl⟩ : syracuseStep 11033243 = 16549865) B16549865
theorem B15081461 : Blo 1238437 15081461 := bstep (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) B1413887
theorem B1860335 : Blo 1238437 1860335 := bstep (se 1 (by rfl) ⟨1395251, by rfl⟩ : syracuseStep 1860335 = 2790503) B2790503
theorem B22905971 : Blo 1238437 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B57206249 : Blo 1238437 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B30164471 : Blo 1238437 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B3139175 : Blo 1238437 3139175 := bstep (se 1 (by rfl) ⟨2354381, by rfl⟩ : syracuseStep 3139175 = 4708763) B4708763
theorem B1885961 : Blo 1238437 1885961 := bstep (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) B1414471
theorem B10054307 : Blo 1238437 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B1239975 : Blo 1238437 1239975 := bstep (se 1 (by rfl) ⟨929981, by rfl⟩ : syracuseStep 1239975 = 1859963) B1859963
theorem B16969265 : Blo 1238437 16969265 := bstep (se 2 (by rfl) ⟨6363474, by rfl⟩ : syracuseStep 16969265 = 12726949) B12726949
theorem B10580159 : Blo 1238437 10580159 := bstep (se 1 (by rfl) ⟨7935119, by rfl⟩ : syracuseStep 10580159 = 15870239) B15870239
theorem B1569071 : Blo 1238437 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B85931867 : Blo 1238437 85931867 := bstep (se 1 (by rfl) ⟨64448900, by rfl⟩ : syracuseStep 85931867 = 128897801) B128897801
theorem B2234233 : Blo 1238437 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B4708475 : Blo 1238437 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B25450787 : Blo 1238437 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B3578347 : Blo 1238437 3578347 := bstep (se 1 (by rfl) ⟨2683760, by rfl⟩ : syracuseStep 3578347 = 5367521) B5367521
theorem B1858217 : Blo 1238437 1858217 := bstep (se 2 (by rfl) ⟨696831, by rfl⟩ : syracuseStep 1858217 = 1393663) B1393663
theorem B7936865 : Blo 1238437 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B7355495 : Blo 1238437 7355495 := bstep (se 1 (by rfl) ⟨5516621, by rfl⟩ : syracuseStep 7355495 = 11033243) B11033243
theorem B1858799 : Blo 1238437 1858799 := bstep (se 1 (by rfl) ⟨1394099, by rfl⟩ : syracuseStep 1858799 = 2788199) B2788199
theorem B23813513 : Blo 1238437 23813513 := bstep (se 2 (by rfl) ⟨8930067, by rfl⟩ : syracuseStep 23813513 = 17860135) B17860135
theorem B3136927 : Blo 1238437 3136927 := bstep (se 1 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 3136927 = 4705391) B4705391
theorem B6275069 : Blo 1238437 6275069 := bstep (se 3 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 6275069 = 2353151) B2353151
theorem B7053439 : Blo 1238437 7053439 := bstep (se 1 (by rfl) ⟨5290079, by rfl⟩ : syracuseStep 7053439 = 10580159) B10580159
theorem B15270647 : Blo 1238437 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B57287911 : Blo 1238437 57287911 := bstep (se 1 (by rfl) ⟨42965933, by rfl⟩ : syracuseStep 57287911 = 85931867) B85931867
theorem B3138983 : Blo 1238437 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B16967191 : Blo 1238437 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B6702871 : Blo 1238437 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B1238811 : Blo 1238437 1238811 := bstep (se 1 (by rfl) ⟨929108, by rfl⟩ : syracuseStep 1238811 = 1858217) B1858217
theorem B1239199 : Blo 1238437 1239199 := bstep (se 1 (by rfl) ⟨929399, by rfl⟩ : syracuseStep 1239199 = 1858799) B1858799
theorem B19614653 : Blo 1238437 19614653 := bstep (se 3 (by rfl) ⟨3677747, by rfl⟩ : syracuseStep 19614653 = 7355495) B7355495
theorem B1240223 : Blo 1238437 1240223 := bstep (se 1 (by rfl) ⟨930167, by rfl⟩ : syracuseStep 1240223 = 1860335) B1860335
theorem B4771129 : Blo 1238437 4771129 := bstep (se 2 (by rfl) ⟨1789173, by rfl⟩ : syracuseStep 4771129 = 3578347) B3578347
theorem B38137499 : Blo 1238437 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B2092783 : Blo 1238437 2092783 := bstep (se 1 (by rfl) ⟨1569587, by rfl⟩ : syracuseStep 2092783 = 3139175) B3139175
theorem B4182569 : Blo 1238437 4182569 := bstep (se 2 (by rfl) ⟨1568463, by rfl⟩ : syracuseStep 4182569 = 3136927) B3136927
theorem B2978977 : Blo 1238437 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B4183379 : Blo 1238437 4183379 := bstep (se 1 (by rfl) ⟨3137534, by rfl⟩ : syracuseStep 4183379 = 6275069) B6275069
theorem B4184189 : Blo 1238437 4184189 := bstep (se 3 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 4184189 = 1569071) B1569071
theorem B20109647 : Blo 1238437 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B5291243 : Blo 1238437 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B5029229 : Blo 1238437 5029229 := bstep (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) B1885961
theorem B15875675 : Blo 1238437 15875675 := bstep (se 1 (by rfl) ⟨11906756, by rfl⟩ : syracuseStep 15875675 = 23813513) B23813513
theorem B11312843 : Blo 1238437 11312843 := bstep (se 1 (by rfl) ⟨8484632, by rfl⟩ : syracuseStep 11312843 = 16969265) B16969265
theorem B9404585 : Blo 1238437 9404585 := bstep (se 2 (by rfl) ⟨3526719, by rfl⟩ : syracuseStep 9404585 = 7053439) B7053439
theorem B13411277 : Blo 1238437 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B76383881 : Blo 1238437 76383881 := bstep (se 2 (by rfl) ⟨28643955, by rfl⟩ : syracuseStep 76383881 = 57287911) B57287911
theorem B13076435 : Blo 1238437 13076435 := bstep (se 1 (by rfl) ⟨9807326, by rfl⟩ : syracuseStep 13076435 = 19614653) B19614653
theorem B2788379 : Blo 1238437 2788379 := bstep (se 1 (by rfl) ⟨2091284, by rfl⟩ : syracuseStep 2788379 = 4182569) B4182569
theorem B2788919 : Blo 1238437 2788919 := bstep (se 1 (by rfl) ⟨2091689, by rfl⟩ : syracuseStep 2788919 = 4183379) B4183379
theorem B2092655 : Blo 1238437 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B2789459 : Blo 1238437 2789459 := bstep (se 1 (by rfl) ⟨2092094, by rfl⟩ : syracuseStep 2789459 = 4184189) B4184189
theorem B13406431 : Blo 1238437 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B6361505 : Blo 1238437 6361505 := bstep (se 2 (by rfl) ⟨2385564, by rfl⟩ : syracuseStep 6361505 = 4771129) B4771129
theorem B30167581 : Blo 1238437 30167581 := bstep (se 3 (by rfl) ⟨5656421, by rfl⟩ : syracuseStep 30167581 = 11312843) B11312843
theorem B22622921 : Blo 1238437 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B3527495 : Blo 1238437 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B2790377 : Blo 1238437 2790377 := bstep (se 2 (by rfl) ⟨1046391, by rfl⟩ : syracuseStep 2790377 = 2092783) B2092783
theorem B25424999 : Blo 1238437 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B3971969 : Blo 1238437 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B40721725 : Blo 1238437 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B8937161 : Blo 1238437 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B10583783 : Blo 1238437 10583783 := bstep (se 1 (by rfl) ⟨7937837, by rfl⟩ : syracuseStep 10583783 = 15875675) B15875675
theorem B1859639 : Blo 1238437 1859639 := bstep (se 1 (by rfl) ⟨1394729, by rfl⟩ : syracuseStep 1859639 = 2789459) B2789459
theorem B17875241 : Blo 1238437 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B15081947 : Blo 1238437 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B2351663 : Blo 1238437 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B1860251 : Blo 1238437 1860251 := bstep (se 1 (by rfl) ⟨1395188, by rfl⟩ : syracuseStep 1860251 = 2790377) B2790377
theorem B40223441 : Blo 1238437 40223441 := bstep (se 2 (by rfl) ⟨15083790, by rfl⟩ : syracuseStep 40223441 = 30167581) B30167581
theorem B16949999 : Blo 1238437 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B50922587 : Blo 1238437 50922587 := bstep (se 1 (by rfl) ⟨38191940, by rfl⟩ : syracuseStep 50922587 = 76383881) B76383881
theorem B2647979 : Blo 1238437 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B1395103 : Blo 1238437 1395103 := bstep (se 1 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 1395103 = 2092655) B2092655
theorem B5958107 : Blo 1238437 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B7055855 : Blo 1238437 7055855 := bstep (se 1 (by rfl) ⟨5291891, by rfl⟩ : syracuseStep 7055855 = 10583783) B10583783
theorem B6269723 : Blo 1238437 6269723 := bstep (se 1 (by rfl) ⟨4702292, by rfl⟩ : syracuseStep 6269723 = 9404585) B9404585
theorem B8940851 : Blo 1238437 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B34870493 : Blo 1238437 34870493 := bstep (se 3 (by rfl) ⟨6538217, by rfl⟩ : syracuseStep 34870493 = 13076435) B13076435
theorem B4241003 : Blo 1238437 4241003 := bstep (se 1 (by rfl) ⟨3180752, by rfl⟩ : syracuseStep 4241003 = 6361505) B6361505
theorem B54295633 : Blo 1238437 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B1858919 : Blo 1238437 1858919 := bstep (se 1 (by rfl) ⟨1394189, by rfl⟩ : syracuseStep 1858919 = 2788379) B2788379
theorem B1859279 : Blo 1238437 1859279 := bstep (se 1 (by rfl) ⟨1394459, by rfl⟩ : syracuseStep 1859279 = 2788919) B2788919
theorem B1860137 : Blo 1238437 1860137 := bstep (se 2 (by rfl) ⟨697551, by rfl⟩ : syracuseStep 1860137 = 1395103) B1395103
theorem B33948391 : Blo 1238437 33948391 := bstep (se 1 (by rfl) ⟨25461293, by rfl⟩ : syracuseStep 33948391 = 50922587) B50922587
theorem B45237365 : Blo 1238437 45237365 := bstep (se 5 (by rfl) ⟨2120501, by rfl⟩ : syracuseStep 45237365 = 4241003) B4241003
theorem B72394177 : Blo 1238437 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B4703903 : Blo 1238437 4703903 := bstep (se 1 (by rfl) ⟨3527927, by rfl⟩ : syracuseStep 4703903 = 7055855) B7055855
theorem B4179815 : Blo 1238437 4179815 := bstep (se 1 (by rfl) ⟨3134861, by rfl⟩ : syracuseStep 4179815 = 6269723) B6269723
theorem B1239279 : Blo 1238437 1239279 := bstep (se 1 (by rfl) ⟨929459, by rfl⟩ : syracuseStep 1239279 = 1858919) B1858919
theorem B1239519 : Blo 1238437 1239519 := bstep (se 1 (by rfl) ⟨929639, by rfl⟩ : syracuseStep 1239519 = 1859279) B1859279
theorem B1239759 : Blo 1238437 1239759 := bstep (se 1 (by rfl) ⟨929819, by rfl⟩ : syracuseStep 1239759 = 1859639) B1859639
theorem B10054631 : Blo 1238437 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B1567775 : Blo 1238437 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B1240167 : Blo 1238437 1240167 := bstep (se 1 (by rfl) ⟨930125, by rfl⟩ : syracuseStep 1240167 = 1860251) B1860251
theorem B26815627 : Blo 1238437 26815627 := bstep (se 1 (by rfl) ⟨20111720, by rfl⟩ : syracuseStep 26815627 = 40223441) B40223441
theorem B11299999 : Blo 1238437 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B1765319 : Blo 1238437 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B5960567 : Blo 1238437 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B11916827 : Blo 1238437 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B23246995 : Blo 1238437 23246995 := bstep (se 1 (by rfl) ⟨17435246, by rfl⟩ : syracuseStep 23246995 = 34870493) B34870493
theorem B3972071 : Blo 1238437 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B3973711 : Blo 1238437 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B2786543 : Blo 1238437 2786543 := bstep (se 1 (by rfl) ⟨2089907, by rfl⟩ : syracuseStep 2786543 = 4179815) B4179815
theorem B15066665 : Blo 1238437 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B2648047 : Blo 1238437 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B6703087 : Blo 1238437 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B4180733 : Blo 1238437 4180733 := bstep (se 3 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 4180733 = 1567775) B1567775
theorem B1240091 : Blo 1238437 1240091 := bstep (se 1 (by rfl) ⟨930068, by rfl⟩ : syracuseStep 1240091 = 1860137) B1860137
theorem B30158243 : Blo 1238437 30158243 := bstep (se 1 (by rfl) ⟨22618682, by rfl⟩ : syracuseStep 30158243 = 45237365) B45237365
theorem B45264521 : Blo 1238437 45264521 := bstep (se 2 (by rfl) ⟨16974195, by rfl⟩ : syracuseStep 45264521 = 33948391) B33948391
theorem B35754169 : Blo 1238437 35754169 := bstep (se 2 (by rfl) ⟨13407813, by rfl⟩ : syracuseStep 35754169 = 26815627) B26815627
theorem B4707517 : Blo 1238437 4707517 := bstep (se 3 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 4707517 = 1765319) B1765319
theorem B30995993 : Blo 1238437 30995993 := bstep (se 2 (by rfl) ⟨11623497, by rfl⟩ : syracuseStep 30995993 = 23246995) B23246995
theorem B7944551 : Blo 1238437 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B3135935 : Blo 1238437 3135935 := bstep (se 1 (by rfl) ⟨2351951, by rfl⟩ : syracuseStep 3135935 = 4703903) B4703903
theorem B96525569 : Blo 1238437 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B10044443 : Blo 1238437 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B6276689 : Blo 1238437 6276689 := bstep (se 2 (by rfl) ⟨2353758, by rfl⟩ : syracuseStep 6276689 = 4707517) B4707517
theorem B2090623 : Blo 1238437 2090623 := bstep (se 1 (by rfl) ⟨1567967, by rfl⟩ : syracuseStep 2090623 = 3135935) B3135935
theorem B2787155 : Blo 1238437 2787155 := bstep (se 1 (by rfl) ⟨2090366, by rfl⟩ : syracuseStep 2787155 = 4180733) B4180733
theorem B64350379 : Blo 1238437 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B20105495 : Blo 1238437 20105495 := bstep (se 1 (by rfl) ⟨15079121, by rfl⟩ : syracuseStep 20105495 = 30158243) B30158243
theorem B47672225 : Blo 1238437 47672225 := bstep (se 2 (by rfl) ⟨17877084, by rfl⟩ : syracuseStep 47672225 = 35754169) B35754169
theorem B20663995 : Blo 1238437 20663995 := bstep (se 1 (by rfl) ⟨15497996, by rfl⟩ : syracuseStep 20663995 = 30995993) B30995993
theorem B5296367 : Blo 1238437 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B30176347 : Blo 1238437 30176347 := bstep (se 1 (by rfl) ⟨22632260, by rfl⟩ : syracuseStep 30176347 = 45264521) B45264521
theorem B5298281 : Blo 1238437 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B1857695 : Blo 1238437 1857695 := bstep (se 1 (by rfl) ⟨1393271, by rfl⟩ : syracuseStep 1857695 = 2786543) B2786543
theorem B3530729 : Blo 1238437 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B8937449 : Blo 1238437 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B14123645 : Blo 1238437 14123645 := bstep (se 3 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 14123645 = 5296367) B5296367
theorem B3532187 : Blo 1238437 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B1238463 : Blo 1238437 1238463 := bstep (se 1 (by rfl) ⟨928847, by rfl⟩ : syracuseStep 1238463 = 1857695) B1857695
theorem B13403663 : Blo 1238437 13403663 := bstep (se 1 (by rfl) ⟨10052747, by rfl⟩ : syracuseStep 13403663 = 20105495) B20105495
theorem B2787497 : Blo 1238437 2787497 := bstep (se 2 (by rfl) ⟨1045311, by rfl⟩ : syracuseStep 2787497 = 2090623) B2090623
theorem B27551993 : Blo 1238437 27551993 := bstep (se 2 (by rfl) ⟨10331997, by rfl⟩ : syracuseStep 27551993 = 20663995) B20663995
theorem B9415277 : Blo 1238437 9415277 := bstep (se 3 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 9415277 = 3530729) B3530729
theorem B5958299 : Blo 1238437 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B40235129 : Blo 1238437 40235129 := bstep (se 2 (by rfl) ⟨15088173, by rfl⟩ : syracuseStep 40235129 = 30176347) B30176347
theorem B31781483 : Blo 1238437 31781483 := bstep (se 1 (by rfl) ⟨23836112, by rfl⟩ : syracuseStep 31781483 = 47672225) B47672225
theorem B26785181 : Blo 1238437 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B85800505 : Blo 1238437 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B4184459 : Blo 1238437 4184459 := bstep (se 1 (by rfl) ⟨3138344, by rfl⟩ : syracuseStep 4184459 = 6276689) B6276689
theorem B1858103 : Blo 1238437 1858103 := bstep (se 1 (by rfl) ⟨1393577, by rfl⟩ : syracuseStep 1858103 = 2787155) B2787155
theorem B1238735 : Blo 1238437 1238735 := bstep (se 1 (by rfl) ⟨929051, by rfl⟩ : syracuseStep 1238735 = 1858103) B1858103
theorem B6276851 : Blo 1238437 6276851 := bstep (se 1 (by rfl) ⟨4707638, by rfl⟩ : syracuseStep 6276851 = 9415277) B9415277
theorem B26823419 : Blo 1238437 26823419 := bstep (se 1 (by rfl) ⟨20117564, by rfl⟩ : syracuseStep 26823419 = 40235129) B40235129
theorem B21187655 : Blo 1238437 21187655 := bstep (se 1 (by rfl) ⟨15890741, by rfl⟩ : syracuseStep 21187655 = 31781483) B31781483
theorem B9415763 : Blo 1238437 9415763 := bstep (se 1 (by rfl) ⟨7061822, by rfl⟩ : syracuseStep 9415763 = 14123645) B14123645
theorem B2789639 : Blo 1238437 2789639 := bstep (se 1 (by rfl) ⟨2092229, by rfl⟩ : syracuseStep 2789639 = 4184459) B4184459
theorem B15888797 : Blo 1238437 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B73471981 : Blo 1238437 73471981 := bstep (se 3 (by rfl) ⟨13775996, by rfl⟩ : syracuseStep 73471981 = 27551993) B27551993
theorem B17856787 : Blo 1238437 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B8935775 : Blo 1238437 8935775 := bstep (se 1 (by rfl) ⟨6701831, by rfl⟩ : syracuseStep 8935775 = 13403663) B13403663
theorem B9419165 : Blo 1238437 9419165 := bstep (se 3 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 9419165 = 3532187) B3532187
theorem B1858331 : Blo 1238437 1858331 := bstep (se 1 (by rfl) ⟨1393748, by rfl⟩ : syracuseStep 1858331 = 2787497) B2787497
theorem B114400673 : Blo 1238437 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B1859759 : Blo 1238437 1859759 := bstep (se 1 (by rfl) ⟨1394819, by rfl⟩ : syracuseStep 1859759 = 2789639) B2789639
theorem B10592531 : Blo 1238437 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B5957183 : Blo 1238437 5957183 := bstep (se 1 (by rfl) ⟨4467887, by rfl⟩ : syracuseStep 5957183 = 8935775) B8935775
theorem B1238887 : Blo 1238437 1238887 := bstep (se 1 (by rfl) ⟨929165, by rfl⟩ : syracuseStep 1238887 = 1858331) B1858331
theorem B14125103 : Blo 1238437 14125103 := bstep (se 1 (by rfl) ⟨10593827, by rfl⟩ : syracuseStep 14125103 = 21187655) B21187655
theorem B6277175 : Blo 1238437 6277175 := bstep (se 1 (by rfl) ⟨4707881, by rfl⟩ : syracuseStep 6277175 = 9415763) B9415763
theorem B97962641 : Blo 1238437 97962641 := bstep (se 2 (by rfl) ⟨36735990, by rfl⟩ : syracuseStep 97962641 = 73471981) B73471981
theorem B23809049 : Blo 1238437 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B6279443 : Blo 1238437 6279443 := bstep (se 1 (by rfl) ⟨4709582, by rfl⟩ : syracuseStep 6279443 = 9419165) B9419165
theorem B4184567 : Blo 1238437 4184567 := bstep (se 1 (by rfl) ⟨3138425, by rfl⟩ : syracuseStep 4184567 = 6276851) B6276851
theorem B17882279 : Blo 1238437 17882279 := bstep (se 1 (by rfl) ⟨13411709, by rfl⟩ : syracuseStep 17882279 = 26823419) B26823419
theorem B76267115 : Blo 1238437 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B7061687 : Blo 1238437 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B4186295 : Blo 1238437 4186295 := bstep (se 1 (by rfl) ⟨3139721, by rfl⟩ : syracuseStep 4186295 = 6279443) B6279443
theorem B15885821 : Blo 1238437 15885821 := bstep (se 3 (by rfl) ⟨2978591, by rfl⟩ : syracuseStep 15885821 = 5957183) B5957183
theorem B65308427 : Blo 1238437 65308427 := bstep (se 1 (by rfl) ⟨48981320, by rfl⟩ : syracuseStep 65308427 = 97962641) B97962641
theorem B11921519 : Blo 1238437 11921519 := bstep (se 1 (by rfl) ⟨8941139, by rfl⟩ : syracuseStep 11921519 = 17882279) B17882279
theorem B1239839 : Blo 1238437 1239839 := bstep (se 1 (by rfl) ⟨929879, by rfl⟩ : syracuseStep 1239839 = 1859759) B1859759
theorem B9416735 : Blo 1238437 9416735 := bstep (se 1 (by rfl) ⟨7062551, by rfl⟩ : syracuseStep 9416735 = 14125103) B14125103
theorem B2789711 : Blo 1238437 2789711 := bstep (se 1 (by rfl) ⟨2092283, by rfl⟩ : syracuseStep 2789711 = 4184567) B4184567
theorem B15872699 : Blo 1238437 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B50844743 : Blo 1238437 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B4184783 : Blo 1238437 4184783 := bstep (se 1 (by rfl) ⟨3138587, by rfl⟩ : syracuseStep 4184783 = 6277175) B6277175
theorem B1859807 : Blo 1238437 1859807 := bstep (se 1 (by rfl) ⟨1394855, by rfl⟩ : syracuseStep 1859807 = 2789711) B2789711
theorem B7947679 : Blo 1238437 7947679 := bstep (se 1 (by rfl) ⟨5960759, by rfl⟩ : syracuseStep 7947679 = 11921519) B11921519
theorem B6277823 : Blo 1238437 6277823 := bstep (se 1 (by rfl) ⟨4708367, by rfl⟩ : syracuseStep 6277823 = 9416735) B9416735
theorem B2789855 : Blo 1238437 2789855 := bstep (se 1 (by rfl) ⟨2092391, by rfl⟩ : syracuseStep 2789855 = 4184783) B4184783
theorem B4707791 : Blo 1238437 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B2790863 : Blo 1238437 2790863 := bstep (se 1 (by rfl) ⟨2093147, by rfl⟩ : syracuseStep 2790863 = 4186295) B4186295
theorem B10581799 : Blo 1238437 10581799 := bstep (se 1 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 10581799 = 15872699) B15872699
theorem B33896495 : Blo 1238437 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B10590547 : Blo 1238437 10590547 := bstep (se 1 (by rfl) ⟨7942910, by rfl⟩ : syracuseStep 10590547 = 15885821) B15885821
theorem B43538951 : Blo 1238437 43538951 := bstep (se 1 (by rfl) ⟨32654213, by rfl⟩ : syracuseStep 43538951 = 65308427) B65308427
theorem B1859903 : Blo 1238437 1859903 := bstep (se 1 (by rfl) ⟨1394927, by rfl⟩ : syracuseStep 1859903 = 2789855) B2789855
theorem B3138527 : Blo 1238437 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B1860575 : Blo 1238437 1860575 := bstep (se 1 (by rfl) ⟨1395431, by rfl⟩ : syracuseStep 1860575 = 2790863) B2790863
theorem B29025967 : Blo 1238437 29025967 := bstep (se 1 (by rfl) ⟨21769475, by rfl⟩ : syracuseStep 29025967 = 43538951) B43538951
theorem B14109065 : Blo 1238437 14109065 := bstep (se 2 (by rfl) ⟨5290899, by rfl⟩ : syracuseStep 14109065 = 10581799) B10581799
theorem B1239871 : Blo 1238437 1239871 := bstep (se 1 (by rfl) ⟨929903, by rfl⟩ : syracuseStep 1239871 = 1859807) B1859807
theorem B22597663 : Blo 1238437 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B10596905 : Blo 1238437 10596905 := bstep (se 2 (by rfl) ⟨3973839, by rfl⟩ : syracuseStep 10596905 = 7947679) B7947679
theorem B14120729 : Blo 1238437 14120729 := bstep (se 2 (by rfl) ⟨5295273, by rfl⟩ : syracuseStep 14120729 = 10590547) B10590547
theorem B4185215 : Blo 1238437 4185215 := bstep (se 1 (by rfl) ⟨3138911, by rfl⟩ : syracuseStep 4185215 = 6277823) B6277823
theorem B30130217 : Blo 1238437 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B9413819 : Blo 1238437 9413819 := bstep (se 1 (by rfl) ⟨7060364, by rfl⟩ : syracuseStep 9413819 = 14120729) B14120729
theorem B9406043 : Blo 1238437 9406043 := bstep (se 1 (by rfl) ⟨7054532, by rfl⟩ : syracuseStep 9406043 = 14109065) B14109065
theorem B38701289 : Blo 1238437 38701289 := bstep (se 2 (by rfl) ⟨14512983, by rfl⟩ : syracuseStep 38701289 = 29025967) B29025967
theorem B1239935 : Blo 1238437 1239935 := bstep (se 1 (by rfl) ⟨929951, by rfl⟩ : syracuseStep 1239935 = 1859903) B1859903
theorem B7064603 : Blo 1238437 7064603 := bstep (se 1 (by rfl) ⟨5298452, by rfl⟩ : syracuseStep 7064603 = 10596905) B10596905
theorem B2092351 : Blo 1238437 2092351 := bstep (se 1 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 2092351 = 3138527) B3138527
theorem B1240383 : Blo 1238437 1240383 := bstep (se 1 (by rfl) ⟨930287, by rfl⟩ : syracuseStep 1240383 = 1860575) B1860575
theorem B2790143 : Blo 1238437 2790143 := bstep (se 1 (by rfl) ⟨2092607, by rfl⟩ : syracuseStep 2790143 = 4185215) B4185215
theorem B20086811 : Blo 1238437 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B1860095 : Blo 1238437 1860095 := bstep (se 1 (by rfl) ⟨1395071, by rfl⟩ : syracuseStep 1860095 = 2790143) B2790143
theorem B6275879 : Blo 1238437 6275879 := bstep (se 1 (by rfl) ⟨4706909, by rfl⟩ : syracuseStep 6275879 = 9413819) B9413819
theorem B6270695 : Blo 1238437 6270695 := bstep (se 1 (by rfl) ⟨4703021, by rfl⟩ : syracuseStep 6270695 = 9406043) B9406043
theorem B25800859 : Blo 1238437 25800859 := bstep (se 1 (by rfl) ⟨19350644, by rfl⟩ : syracuseStep 25800859 = 38701289) B38701289
theorem B2789801 : Blo 1238437 2789801 := bstep (se 2 (by rfl) ⟨1046175, by rfl⟩ : syracuseStep 2789801 = 2092351) B2092351
theorem B4709735 : Blo 1238437 4709735 := bstep (se 1 (by rfl) ⟨3532301, by rfl⟩ : syracuseStep 4709735 = 7064603) B7064603
theorem B1859867 : Blo 1238437 1859867 := bstep (se 1 (by rfl) ⟨1394900, by rfl⟩ : syracuseStep 1859867 = 2789801) B2789801
theorem B3139823 : Blo 1238437 3139823 := bstep (se 1 (by rfl) ⟨2354867, by rfl⟩ : syracuseStep 3139823 = 4709735) B4709735
theorem B4180463 : Blo 1238437 4180463 := bstep (se 1 (by rfl) ⟨3135347, by rfl⟩ : syracuseStep 4180463 = 6270695) B6270695
theorem B34401145 : Blo 1238437 34401145 := bstep (se 2 (by rfl) ⟨12900429, by rfl⟩ : syracuseStep 34401145 = 25800859) B25800859
theorem B1240063 : Blo 1238437 1240063 := bstep (se 1 (by rfl) ⟨930047, by rfl⟩ : syracuseStep 1240063 = 1860095) B1860095
theorem B13391207 : Blo 1238437 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B4183919 : Blo 1238437 4183919 := bstep (se 1 (by rfl) ⟨3137939, by rfl⟩ : syracuseStep 4183919 = 6275879) B6275879
theorem B45868193 : Blo 1238437 45868193 := bstep (se 2 (by rfl) ⟨17200572, by rfl⟩ : syracuseStep 45868193 = 34401145) B34401145
theorem B2786975 : Blo 1238437 2786975 := bstep (se 1 (by rfl) ⟨2090231, by rfl⟩ : syracuseStep 2786975 = 4180463) B4180463
theorem B1239911 : Blo 1238437 1239911 := bstep (se 1 (by rfl) ⟨929933, by rfl⟩ : syracuseStep 1239911 = 1859867) B1859867
theorem B2789279 : Blo 1238437 2789279 := bstep (se 1 (by rfl) ⟨2091959, by rfl⟩ : syracuseStep 2789279 = 4183919) B4183919
theorem B2093215 : Blo 1238437 2093215 := bstep (se 1 (by rfl) ⟨1569911, by rfl⟩ : syracuseStep 2093215 = 3139823) B3139823
theorem B8927471 : Blo 1238437 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B5951647 : Blo 1238437 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B2790953 : Blo 1238437 2790953 := bstep (se 2 (by rfl) ⟨1046607, by rfl⟩ : syracuseStep 2790953 = 2093215) B2093215
theorem B30578795 : Blo 1238437 30578795 := bstep (se 1 (by rfl) ⟨22934096, by rfl⟩ : syracuseStep 30578795 = 45868193) B45868193
theorem B1857983 : Blo 1238437 1857983 := bstep (se 1 (by rfl) ⟨1393487, by rfl⟩ : syracuseStep 1857983 = 2786975) B2786975
theorem B1859519 : Blo 1238437 1859519 := bstep (se 1 (by rfl) ⟨1394639, by rfl⟩ : syracuseStep 1859519 = 2789279) B2789279
theorem B1860635 : Blo 1238437 1860635 := bstep (se 1 (by rfl) ⟨1395476, by rfl⟩ : syracuseStep 1860635 = 2790953) B2790953
theorem B1238655 : Blo 1238437 1238655 := bstep (se 1 (by rfl) ⟨928991, by rfl⟩ : syracuseStep 1238655 = 1857983) B1857983
theorem B1239679 : Blo 1238437 1239679 := bstep (se 1 (by rfl) ⟨929759, by rfl⟩ : syracuseStep 1239679 = 1859519) B1859519
theorem B20385863 : Blo 1238437 20385863 := bstep (se 1 (by rfl) ⟨15289397, by rfl⟩ : syracuseStep 20385863 = 30578795) B30578795
theorem B31742117 : Blo 1238437 31742117 := bstep (se 4 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 31742117 = 5951647) B5951647
theorem B13590575 : Blo 1238437 13590575 := bstep (se 1 (by rfl) ⟨10192931, by rfl⟩ : syracuseStep 13590575 = 20385863) B20385863
theorem B21161411 : Blo 1238437 21161411 := bstep (se 1 (by rfl) ⟨15871058, by rfl⟩ : syracuseStep 21161411 = 31742117) B31742117
theorem B1240423 : Blo 1238437 1240423 := bstep (se 1 (by rfl) ⟨930317, by rfl⟩ : syracuseStep 1240423 = 1860635) B1860635
theorem B9060383 : Blo 1238437 9060383 := bstep (se 1 (by rfl) ⟨6795287, by rfl⟩ : syracuseStep 9060383 = 13590575) B13590575
theorem B14107607 : Blo 1238437 14107607 := bstep (se 1 (by rfl) ⟨10580705, by rfl⟩ : syracuseStep 14107607 = 21161411) B21161411
theorem B9405071 : Blo 1238437 9405071 := bstep (se 1 (by rfl) ⟨7053803, by rfl⟩ : syracuseStep 9405071 = 14107607) B14107607
theorem B6040255 : Blo 1238437 6040255 := bstep (se 1 (by rfl) ⟨4530191, by rfl⟩ : syracuseStep 6040255 = 9060383) B9060383
theorem B8053673 : Blo 1238437 8053673 := bstep (se 2 (by rfl) ⟨3020127, by rfl⟩ : syracuseStep 8053673 = 6040255) B6040255
theorem B6270047 : Blo 1238437 6270047 := bstep (se 1 (by rfl) ⟨4702535, by rfl⟩ : syracuseStep 6270047 = 9405071) B9405071
theorem B4180031 : Blo 1238437 4180031 := bstep (se 1 (by rfl) ⟨3135023, by rfl⟩ : syracuseStep 4180031 = 6270047) B6270047
theorem B21476461 : Blo 1238437 21476461 := bstep (se 3 (by rfl) ⟨4026836, by rfl⟩ : syracuseStep 21476461 = 8053673) B8053673
theorem B2786687 : Blo 1238437 2786687 := bstep (se 1 (by rfl) ⟨2090015, by rfl⟩ : syracuseStep 2786687 = 4180031) B4180031
theorem B28635281 : Blo 1238437 28635281 := bstep (se 2 (by rfl) ⟨10738230, by rfl⟩ : syracuseStep 28635281 = 21476461) B21476461
theorem B19090187 : Blo 1238437 19090187 := bstep (se 1 (by rfl) ⟨14317640, by rfl⟩ : syracuseStep 19090187 = 28635281) B28635281
theorem B1857791 : Blo 1238437 1857791 := bstep (se 1 (by rfl) ⟨1393343, by rfl⟩ : syracuseStep 1857791 = 2786687) B2786687
theorem B1238527 : Blo 1238437 1238527 := bstep (se 1 (by rfl) ⟨928895, by rfl⟩ : syracuseStep 1238527 = 1857791) B1857791
theorem B12726791 : Blo 1238437 12726791 := bstep (se 1 (by rfl) ⟨9545093, by rfl⟩ : syracuseStep 12726791 = 19090187) B19090187
theorem B8484527 : Blo 1238437 8484527 := bstep (se 1 (by rfl) ⟨6363395, by rfl⟩ : syracuseStep 8484527 = 12726791) B12726791
theorem B22625405 : Blo 1238437 22625405 := bstep (se 3 (by rfl) ⟨4242263, by rfl⟩ : syracuseStep 22625405 = 8484527) B8484527
theorem B15083603 : Blo 1238437 15083603 := bstep (se 1 (by rfl) ⟨11312702, by rfl⟩ : syracuseStep 15083603 = 22625405) B22625405
theorem B10055735 : Blo 1238437 10055735 := bstep (se 1 (by rfl) ⟨7541801, by rfl⟩ : syracuseStep 10055735 = 15083603) B15083603
theorem B6703823 : Blo 1238437 6703823 := bstep (se 1 (by rfl) ⟨5027867, by rfl⟩ : syracuseStep 6703823 = 10055735) B10055735
theorem B4469215 : Blo 1238437 4469215 := bstep (se 1 (by rfl) ⟨3351911, by rfl⟩ : syracuseStep 4469215 = 6703823) B6703823
theorem B5958953 : Blo 1238437 5958953 := bstep (se 2 (by rfl) ⟨2234607, by rfl⟩ : syracuseStep 5958953 = 4469215) B4469215
theorem B3972635 : Blo 1238437 3972635 := bstep (se 1 (by rfl) ⟨2979476, by rfl⟩ : syracuseStep 3972635 = 5958953) B5958953
theorem B2648423 : Blo 1238437 2648423 := bstep (se 1 (by rfl) ⟨1986317, by rfl⟩ : syracuseStep 2648423 = 3972635) B3972635
theorem B7062461 : Blo 1238437 7062461 := bstep (se 3 (by rfl) ⟨1324211, by rfl⟩ : syracuseStep 7062461 = 2648423) B2648423
theorem B4708307 : Blo 1238437 4708307 := bstep (se 1 (by rfl) ⟨3531230, by rfl⟩ : syracuseStep 4708307 = 7062461) B7062461
theorem B3138871 : Blo 1238437 3138871 := bstep (se 1 (by rfl) ⟨2354153, by rfl⟩ : syracuseStep 3138871 = 4708307) B4708307
theorem B4185161 : Blo 1238437 4185161 := bstep (se 2 (by rfl) ⟨1569435, by rfl⟩ : syracuseStep 4185161 = 3138871) B3138871
theorem B2790107 : Blo 1238437 2790107 := bstep (se 1 (by rfl) ⟨2092580, by rfl⟩ : syracuseStep 2790107 = 4185161) B4185161
theorem B1860071 : Blo 1238437 1860071 := bstep (se 1 (by rfl) ⟨1395053, by rfl⟩ : syracuseStep 1860071 = 2790107) B2790107
theorem B1240047 : Blo 1238437 1240047 := bstep (se 1 (by rfl) ⟨930035, by rfl⟩ : syracuseStep 1240047 = 1860071) B1860071

theorem C0 (j : ℕ) (h1 : 309609 ≤ j) (h2 : j ≤ 310108) : Blo 1238437 (4 * j + 3) := by
  interval_cases j
  · exact B1238439
  · exact B1238443
  · exact B1238447
  · exact B1238451
  · exact B1238455
  · exact B1238459
  · exact B1238463
  · exact B1238467
  · exact B1238471
  · exact B1238475
  · exact B1238479
  · exact B1238483
  · exact B1238487
  · exact B1238491
  · exact B1238495
  · exact B1238499
  · exact B1238503
  · exact B1238507
  · exact B1238511
  · exact B1238515
  · exact B1238519
  · exact B1238523
  · exact B1238527
  · exact B1238531
  · exact B1238535
  · exact B1238539
  · exact B1238543
  · exact B1238547
  · exact B1238551
  · exact B1238555
  · exact B1238559
  · exact B1238563
  · exact B1238567
  · exact B1238571
  · exact B1238575
  · exact B1238579
  · exact B1238583
  · exact B1238587
  · exact B1238591
  · exact B1238595
  · exact B1238599
  · exact B1238603
  · exact B1238607
  · exact B1238611
  · exact B1238615
  · exact B1238619
  · exact B1238623
  · exact B1238627
  · exact B1238631
  · exact B1238635
  · exact B1238639
  · exact B1238643
  · exact B1238647
  · exact B1238651
  · exact B1238655
  · exact B1238659
  · exact B1238663
  · exact B1238667
  · exact B1238671
  · exact B1238675
  · exact B1238679
  · exact B1238683
  · exact B1238687
  · exact B1238691
  · exact B1238695
  · exact B1238699
  · exact B1238703
  · exact B1238707
  · exact B1238711
  · exact B1238715
  · exact B1238719
  · exact B1238723
  · exact B1238727
  · exact B1238731
  · exact B1238735
  · exact B1238739
  · exact B1238743
  · exact B1238747
  · exact B1238751
  · exact B1238755
  · exact B1238759
  · exact B1238763
  · exact B1238767
  · exact B1238771
  · exact B1238775
  · exact B1238779
  · exact B1238783
  · exact B1238787
  · exact B1238791
  · exact B1238795
  · exact B1238799
  · exact B1238803
  · exact B1238807
  · exact B1238811
  · exact B1238815
  · exact B1238819
  · exact B1238823
  · exact B1238827
  · exact B1238831
  · exact B1238835
  · exact B1238839
  · exact B1238843
  · exact B1238847
  · exact B1238851
  · exact B1238855
  · exact B1238859
  · exact B1238863
  · exact B1238867
  · exact B1238871
  · exact B1238875
  · exact B1238879
  · exact B1238883
  · exact B1238887
  · exact B1238891
  · exact B1238895
  · exact B1238899
  · exact B1238903
  · exact B1238907
  · exact B1238911
  · exact B1238915
  · exact B1238919
  · exact B1238923
  · exact B1238927
  · exact B1238931
  · exact B1238935
  · exact B1238939
  · exact B1238943
  · exact B1238947
  · exact B1238951
  · exact B1238955
  · exact B1238959
  · exact B1238963
  · exact B1238967
  · exact B1238971
  · exact B1238975
  · exact B1238979
  · exact B1238983
  · exact B1238987
  · exact B1238991
  · exact B1238995
  · exact B1238999
  · exact B1239003
  · exact B1239007
  · exact B1239011
  · exact B1239015
  · exact B1239019
  · exact B1239023
  · exact B1239027
  · exact B1239031
  · exact B1239035
  · exact B1239039
  · exact B1239043
  · exact B1239047
  · exact B1239051
  · exact B1239055
  · exact B1239059
  · exact B1239063
  · exact B1239067
  · exact B1239071
  · exact B1239075
  · exact B1239079
  · exact B1239083
  · exact B1239087
  · exact B1239091
  · exact B1239095
  · exact B1239099
  · exact B1239103
  · exact B1239107
  · exact B1239111
  · exact B1239115
  · exact B1239119
  · exact B1239123
  · exact B1239127
  · exact B1239131
  · exact B1239135
  · exact B1239139
  · exact B1239143
  · exact B1239147
  · exact B1239151
  · exact B1239155
  · exact B1239159
  · exact B1239163
  · exact B1239167
  · exact B1239171
  · exact B1239175
  · exact B1239179
  · exact B1239183
  · exact B1239187
  · exact B1239191
  · exact B1239195
  · exact B1239199
  · exact B1239203
  · exact B1239207
  · exact B1239211
  · exact B1239215
  · exact B1239219
  · exact B1239223
  · exact B1239227
  · exact B1239231
  · exact B1239235
  · exact B1239239
  · exact B1239243
  · exact B1239247
  · exact B1239251
  · exact B1239255
  · exact B1239259
  · exact B1239263
  · exact B1239267
  · exact B1239271
  · exact B1239275
  · exact B1239279
  · exact B1239283
  · exact B1239287
  · exact B1239291
  · exact B1239295
  · exact B1239299
  · exact B1239303
  · exact B1239307
  · exact B1239311
  · exact B1239315
  · exact B1239319
  · exact B1239323
  · exact B1239327
  · exact B1239331
  · exact B1239335
  · exact B1239339
  · exact B1239343
  · exact B1239347
  · exact B1239351
  · exact B1239355
  · exact B1239359
  · exact B1239363
  · exact B1239367
  · exact B1239371
  · exact B1239375
  · exact B1239379
  · exact B1239383
  · exact B1239387
  · exact B1239391
  · exact B1239395
  · exact B1239399
  · exact B1239403
  · exact B1239407
  · exact B1239411
  · exact B1239415
  · exact B1239419
  · exact B1239423
  · exact B1239427
  · exact B1239431
  · exact B1239435
  · exact B1239439
  · exact B1239443
  · exact B1239447
  · exact B1239451
  · exact B1239455
  · exact B1239459
  · exact B1239463
  · exact B1239467
  · exact B1239471
  · exact B1239475
  · exact B1239479
  · exact B1239483
  · exact B1239487
  · exact B1239491
  · exact B1239495
  · exact B1239499
  · exact B1239503
  · exact B1239507
  · exact B1239511
  · exact B1239515
  · exact B1239519
  · exact B1239523
  · exact B1239527
  · exact B1239531
  · exact B1239535
  · exact B1239539
  · exact B1239543
  · exact B1239547
  · exact B1239551
  · exact B1239555
  · exact B1239559
  · exact B1239563
  · exact B1239567
  · exact B1239571
  · exact B1239575
  · exact B1239579
  · exact B1239583
  · exact B1239587
  · exact B1239591
  · exact B1239595
  · exact B1239599
  · exact B1239603
  · exact B1239607
  · exact B1239611
  · exact B1239615
  · exact B1239619
  · exact B1239623
  · exact B1239627
  · exact B1239631
  · exact B1239635
  · exact B1239639
  · exact B1239643
  · exact B1239647
  · exact B1239651
  · exact B1239655
  · exact B1239659
  · exact B1239663
  · exact B1239667
  · exact B1239671
  · exact B1239675
  · exact B1239679
  · exact B1239683
  · exact B1239687
  · exact B1239691
  · exact B1239695
  · exact B1239699
  · exact B1239703
  · exact B1239707
  · exact B1239711
  · exact B1239715
  · exact B1239719
  · exact B1239723
  · exact B1239727
  · exact B1239731
  · exact B1239735
  · exact B1239739
  · exact B1239743
  · exact B1239747
  · exact B1239751
  · exact B1239755
  · exact B1239759
  · exact B1239763
  · exact B1239767
  · exact B1239771
  · exact B1239775
  · exact B1239779
  · exact B1239783
  · exact B1239787
  · exact B1239791
  · exact B1239795
  · exact B1239799
  · exact B1239803
  · exact B1239807
  · exact B1239811
  · exact B1239815
  · exact B1239819
  · exact B1239823
  · exact B1239827
  · exact B1239831
  · exact B1239835
  · exact B1239839
  · exact B1239843
  · exact B1239847
  · exact B1239851
  · exact B1239855
  · exact B1239859
  · exact B1239863
  · exact B1239867
  · exact B1239871
  · exact B1239875
  · exact B1239879
  · exact B1239883
  · exact B1239887
  · exact B1239891
  · exact B1239895
  · exact B1239899
  · exact B1239903
  · exact B1239907
  · exact B1239911
  · exact B1239915
  · exact B1239919
  · exact B1239923
  · exact B1239927
  · exact B1239931
  · exact B1239935
  · exact B1239939
  · exact B1239943
  · exact B1239947
  · exact B1239951
  · exact B1239955
  · exact B1239959
  · exact B1239963
  · exact B1239967
  · exact B1239971
  · exact B1239975
  · exact B1239979
  · exact B1239983
  · exact B1239987
  · exact B1239991
  · exact B1239995
  · exact B1239999
  · exact B1240003
  · exact B1240007
  · exact B1240011
  · exact B1240015
  · exact B1240019
  · exact B1240023
  · exact B1240027
  · exact B1240031
  · exact B1240035
  · exact B1240039
  · exact B1240043
  · exact B1240047
  · exact B1240051
  · exact B1240055
  · exact B1240059
  · exact B1240063
  · exact B1240067
  · exact B1240071
  · exact B1240075
  · exact B1240079
  · exact B1240083
  · exact B1240087
  · exact B1240091
  · exact B1240095
  · exact B1240099
  · exact B1240103
  · exact B1240107
  · exact B1240111
  · exact B1240115
  · exact B1240119
  · exact B1240123
  · exact B1240127
  · exact B1240131
  · exact B1240135
  · exact B1240139
  · exact B1240143
  · exact B1240147
  · exact B1240151
  · exact B1240155
  · exact B1240159
  · exact B1240163
  · exact B1240167
  · exact B1240171
  · exact B1240175
  · exact B1240179
  · exact B1240183
  · exact B1240187
  · exact B1240191
  · exact B1240195
  · exact B1240199
  · exact B1240203
  · exact B1240207
  · exact B1240211
  · exact B1240215
  · exact B1240219
  · exact B1240223
  · exact B1240227
  · exact B1240231
  · exact B1240235
  · exact B1240239
  · exact B1240243
  · exact B1240247
  · exact B1240251
  · exact B1240255
  · exact B1240259
  · exact B1240263
  · exact B1240267
  · exact B1240271
  · exact B1240275
  · exact B1240279
  · exact B1240283
  · exact B1240287
  · exact B1240291
  · exact B1240295
  · exact B1240299
  · exact B1240303
  · exact B1240307
  · exact B1240311
  · exact B1240315
  · exact B1240319
  · exact B1240323
  · exact B1240327
  · exact B1240331
  · exact B1240335
  · exact B1240339
  · exact B1240343
  · exact B1240347
  · exact B1240351
  · exact B1240355
  · exact B1240359
  · exact B1240363
  · exact B1240367
  · exact B1240371
  · exact B1240375
  · exact B1240379
  · exact B1240383
  · exact B1240387
  · exact B1240391
  · exact B1240395
  · exact B1240399
  · exact B1240403
  · exact B1240407
  · exact B1240411
  · exact B1240415
  · exact B1240419
  · exact B1240423
  · exact B1240427
  · exact B1240431
  · exact B1240435

theorem solution (m : ℕ) (hlo : 1238437 ≤ m) (hhi : m ≤ 1240437) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 309609 ≤ j := by omega
    have hj2 : j ≤ 310108 := by omega
    have hb : Blo 1238437 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
