-- Prove2me | solution 1 for syracuse_descends_range_511796_515796
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:22.719438+00:00
-- url     : https://prove2.me/submissions/25ea29fe-589b-4957-a22d-81cb700e7256

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


theorem B3964949 : Blo 511796 3964949 := bbase (se 6 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 3964949 = 185857) (by norm_num)
theorem B1737125 : Blo 511796 1737125 := bbase (se 4 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 1737125 = 325711) (by norm_num)
theorem B3900149 : Blo 511796 3900149 := bbase (se 5 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 3900149 = 365639) (by norm_num)
theorem B1737557 : Blo 511796 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B558073 : Blo 511796 558073 := bbase (se 2 (by rfl) ⟨209277, by rfl⟩ : syracuseStep 558073 = 418555) (by norm_num)
theorem B4949045 : Blo 511796 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B5276821 : Blo 511796 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B1737989 : Blo 511796 1737989 := bbase (se 4 (by rfl) ⟨162936, by rfl⟩ : syracuseStep 1737989 = 325873) (by norm_num)
theorem B623993 : Blo 511796 623993 := bbase (se 2 (by rfl) ⟨233997, by rfl⟩ : syracuseStep 623993 = 467995) (by norm_num)
theorem B820613 : Blo 511796 820613 := bbase (se 4 (by rfl) ⟨76932, by rfl⟩ : syracuseStep 820613 = 153865) (by norm_num)
theorem B2000533 : Blo 511796 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B1738421 : Blo 511796 1738421 := bbase (se 5 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 1738421 = 162977) (by norm_num)
theorem B820997 : Blo 511796 820997 := bbase (se 4 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 820997 = 153937) (by norm_num)
theorem B3508085 : Blo 511796 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B821125 : Blo 511796 821125 := bbase (se 4 (by rfl) ⟨76980, by rfl⟩ : syracuseStep 821125 = 153961) (by norm_num)
theorem B1640341 : Blo 511796 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1640405 : Blo 511796 1640405 := bbase (se 7 (by rfl) ⟨19223, by rfl⟩ : syracuseStep 1640405 = 38447) (by norm_num)
theorem B2197525 : Blo 511796 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B1738853 : Blo 511796 1738853 := bbase (se 4 (by rfl) ⟨163017, by rfl⟩ : syracuseStep 1738853 = 326035) (by norm_num)
theorem B4163957 : Blo 511796 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B2591189 : Blo 511796 2591189 := bbase (se 7 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 2591189 = 60731) (by norm_num)
theorem B1739285 : Blo 511796 1739285 := bbase (se 6 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 1739285 = 81529) (by norm_num)
theorem B822125 : Blo 511796 822125 := bbase (se 3 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 822125 = 308297) (by norm_num)
theorem B1739717 : Blo 511796 1739717 := bbase (se 4 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 1739717 = 326197) (by norm_num)
theorem B592861 : Blo 511796 592861 := bbase (se 3 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 592861 = 222323) (by norm_num)
theorem B822253 : Blo 511796 822253 := bbase (se 3 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 822253 = 308345) (by norm_num)
theorem B2460725 : Blo 511796 2460725 := bbase (se 5 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 2460725 = 230693) (by norm_num)
theorem B2919509 : Blo 511796 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B658577 : Blo 511796 658577 := bbase (se 2 (by rfl) ⟨246966, by rfl⟩ : syracuseStep 658577 = 493933) (by norm_num)
theorem B1871045 : Blo 511796 1871045 := bbase (se 4 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 1871045 = 350821) (by norm_num)
theorem B822637 : Blo 511796 822637 := bbase (se 3 (by rfl) ⟨154244, by rfl⟩ : syracuseStep 822637 = 308489) (by norm_num)
theorem B1740149 : Blo 511796 1740149 := bbase (se 5 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 1740149 = 163139) (by norm_num)
theorem B986573 : Blo 511796 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B1183301 : Blo 511796 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B659017 : Blo 511796 659017 := bbase (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) (by norm_num)
theorem B5836373 : Blo 511796 5836373 := bbase (se 8 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 5836373 = 68395) (by norm_num)
theorem B822893 : Blo 511796 822893 := bbase (se 3 (by rfl) ⟨154292, by rfl⟩ : syracuseStep 822893 = 308585) (by norm_num)
theorem B2592485 : Blo 511796 2592485 := bbase (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) (by norm_num)
theorem B1740581 : Blo 511796 1740581 := bbase (se 4 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 1740581 = 326359) (by norm_num)
theorem B986941 : Blo 511796 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B823765 : Blo 511796 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B823861 : Blo 511796 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B1151549 : Blo 511796 1151549 := bbase (se 3 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 1151549 = 431831) (by norm_num)
theorem B1151621 : Blo 511796 1151621 := bbase (se 4 (by rfl) ⟨107964, by rfl⟩ : syracuseStep 1151621 = 215929) (by norm_num)
theorem B1151693 : Blo 511796 1151693 := bbase (se 3 (by rfl) ⟨215942, by rfl⟩ : syracuseStep 1151693 = 431885) (by norm_num)
theorem B824021 : Blo 511796 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B1151765 : Blo 511796 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B627521 : Blo 511796 627521 := bbase (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) (by norm_num)
theorem B1151837 : Blo 511796 1151837 := bbase (se 3 (by rfl) ⟨215969, by rfl⟩ : syracuseStep 1151837 = 431939) (by norm_num)
theorem B1151909 : Blo 511796 1151909 := bbase (se 4 (by rfl) ⟨107991, by rfl⟩ : syracuseStep 1151909 = 215983) (by norm_num)
theorem B1643429 : Blo 511796 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B2200517 : Blo 511796 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B1151981 : Blo 511796 1151981 := bbase (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) (by norm_num)
theorem B2593781 : Blo 511796 2593781 := bbase (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) (by norm_num)
theorem B4166645 : Blo 511796 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B1152053 : Blo 511796 1152053 := bbase (se 5 (by rfl) ⟨54002, by rfl⟩ : syracuseStep 1152053 = 108005) (by norm_num)
theorem B1152125 : Blo 511796 1152125 := bbase (se 3 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 1152125 = 432047) (by norm_num)
theorem B1152197 : Blo 511796 1152197 := bbase (se 4 (by rfl) ⟨108018, by rfl⟩ : syracuseStep 1152197 = 216037) (by norm_num)
theorem B1152269 : Blo 511796 1152269 := bbase (se 3 (by rfl) ⟨216050, by rfl⟩ : syracuseStep 1152269 = 432101) (by norm_num)
theorem B693517 : Blo 511796 693517 := bbase (se 3 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 693517 = 260069) (by norm_num)
theorem B693581 : Blo 511796 693581 := bbase (se 3 (by rfl) ⟨130046, by rfl⟩ : syracuseStep 693581 = 260093) (by norm_num)
theorem B1152341 : Blo 511796 1152341 := bbase (se 14 (by rfl) ⟨105, by rfl⟩ : syracuseStep 1152341 = 211) (by norm_num)
theorem B628105 : Blo 511796 628105 := bbase (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) (by norm_num)
theorem B1152413 : Blo 511796 1152413 := bbase (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) (by norm_num)
theorem B1152485 : Blo 511796 1152485 := bbase (se 4 (by rfl) ⟨108045, by rfl⟩ : syracuseStep 1152485 = 216091) (by norm_num)
theorem B693749 : Blo 511796 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B1152557 : Blo 511796 1152557 := bbase (se 3 (by rfl) ⟨216104, by rfl⟩ : syracuseStep 1152557 = 432209) (by norm_num)
theorem B1152629 : Blo 511796 1152629 := bbase (se 5 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 1152629 = 108059) (by norm_num)
theorem B1152701 : Blo 511796 1152701 := bbase (se 3 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 1152701 = 432263) (by norm_num)
theorem B1152773 : Blo 511796 1152773 := bbase (se 4 (by rfl) ⟨108072, by rfl⟩ : syracuseStep 1152773 = 216145) (by norm_num)
theorem B825149 : Blo 511796 825149 := bbase (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) (by norm_num)
theorem B1152845 : Blo 511796 1152845 := bbase (se 3 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 1152845 = 432317) (by norm_num)
theorem B2463605 : Blo 511796 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1152917 : Blo 511796 1152917 := bbase (se 6 (by rfl) ⟨27021, by rfl⟩ : syracuseStep 1152917 = 54043) (by norm_num)
theorem B1054637 : Blo 511796 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B2201525 : Blo 511796 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B1152989 : Blo 511796 1152989 := bbase (se 3 (by rfl) ⟨216185, by rfl⟩ : syracuseStep 1152989 = 432371) (by norm_num)
theorem B1153061 : Blo 511796 1153061 := bbase (se 4 (by rfl) ⟨108099, by rfl⟩ : syracuseStep 1153061 = 216199) (by norm_num)
theorem B1153133 : Blo 511796 1153133 := bbase (se 3 (by rfl) ⟨216212, by rfl⟩ : syracuseStep 1153133 = 432425) (by norm_num)
theorem B1153205 : Blo 511796 1153205 := bbase (se 5 (by rfl) ⟨54056, by rfl⟩ : syracuseStep 1153205 = 108113) (by norm_num)
theorem B4397237 : Blo 511796 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B1480933 : Blo 511796 1480933 := bbase (se 4 (by rfl) ⟨138837, by rfl⟩ : syracuseStep 1480933 = 277675) (by norm_num)
theorem B1153277 : Blo 511796 1153277 := bbase (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) (by norm_num)
theorem B2595077 : Blo 511796 2595077 := bbase (se 4 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 2595077 = 486577) (by norm_num)
theorem B825661 : Blo 511796 825661 := bbase (se 3 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 825661 = 309623) (by norm_num)
theorem B1153349 : Blo 511796 1153349 := bbase (se 4 (by rfl) ⟨108126, by rfl⟩ : syracuseStep 1153349 = 216253) (by norm_num)
theorem B1153421 : Blo 511796 1153421 := bbase (se 3 (by rfl) ⟨216266, by rfl⟩ : syracuseStep 1153421 = 432533) (by norm_num)
theorem B1153493 : Blo 511796 1153493 := bbase (se 7 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 1153493 = 27035) (by norm_num)
theorem B1153565 : Blo 511796 1153565 := bbase (se 3 (by rfl) ⟨216293, by rfl⟩ : syracuseStep 1153565 = 432587) (by norm_num)
theorem B1153637 : Blo 511796 1153637 := bbase (se 4 (by rfl) ⟨108153, by rfl⟩ : syracuseStep 1153637 = 216307) (by norm_num)
theorem B1153709 : Blo 511796 1153709 := bbase (se 3 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 1153709 = 432641) (by norm_num)
theorem B1153781 : Blo 511796 1153781 := bbase (se 5 (by rfl) ⟨54083, by rfl⟩ : syracuseStep 1153781 = 108167) (by norm_num)
theorem B1153853 : Blo 511796 1153853 := bbase (se 3 (by rfl) ⟨216347, by rfl⟩ : syracuseStep 1153853 = 432695) (by norm_num)
theorem B1153925 : Blo 511796 1153925 := bbase (se 4 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 1153925 = 216361) (by norm_num)
theorem B1153997 : Blo 511796 1153997 := bbase (se 3 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 1153997 = 432749) (by norm_num)
theorem B924653 : Blo 511796 924653 := bbase (se 3 (by rfl) ⟨173372, by rfl⟩ : syracuseStep 924653 = 346745) (by norm_num)
theorem B1154069 : Blo 511796 1154069 := bbase (se 6 (by rfl) ⟨27048, by rfl⟩ : syracuseStep 1154069 = 54097) (by norm_num)
theorem B1154141 : Blo 511796 1154141 := bbase (se 3 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 1154141 = 432803) (by norm_num)
theorem B1875077 : Blo 511796 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B1154213 : Blo 511796 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B1154285 : Blo 511796 1154285 := bbase (se 3 (by rfl) ⟨216428, by rfl⟩ : syracuseStep 1154285 = 432857) (by norm_num)
theorem B1154357 : Blo 511796 1154357 := bbase (se 5 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 1154357 = 108221) (by norm_num)
theorem B38083925 : Blo 511796 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B1154429 : Blo 511796 1154429 := bbase (se 3 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 1154429 = 432911) (by norm_num)
theorem B1154501 : Blo 511796 1154501 := bbase (se 4 (by rfl) ⟨108234, by rfl⟩ : syracuseStep 1154501 = 216469) (by norm_num)
theorem B1154573 : Blo 511796 1154573 := bbase (se 3 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 1154573 = 432965) (by norm_num)
theorem B2596373 : Blo 511796 2596373 := bbase (se 6 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 2596373 = 121705) (by norm_num)
theorem B1154645 : Blo 511796 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B1154717 : Blo 511796 1154717 := bbase (se 3 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 1154717 = 433019) (by norm_num)
theorem B1154789 : Blo 511796 1154789 := bbase (se 4 (by rfl) ⟨108261, by rfl⟩ : syracuseStep 1154789 = 216523) (by norm_num)
theorem B1154861 : Blo 511796 1154861 := bbase (se 3 (by rfl) ⟨216536, by rfl⟩ : syracuseStep 1154861 = 433073) (by norm_num)
theorem B1154933 : Blo 511796 1154933 := bbase (se 5 (by rfl) ⟨54137, by rfl⟩ : syracuseStep 1154933 = 108275) (by norm_num)
theorem B925597 : Blo 511796 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B1155005 : Blo 511796 1155005 := bbase (se 3 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 1155005 = 433127) (by norm_num)
theorem B2957269 : Blo 511796 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B2465797 : Blo 511796 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B1155077 : Blo 511796 1155077 := bbase (se 4 (by rfl) ⟨108288, by rfl⟩ : syracuseStep 1155077 = 216577) (by norm_num)
theorem B696349 : Blo 511796 696349 := bbase (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) (by norm_num)
theorem B1351757 : Blo 511796 1351757 := bbase (se 3 (by rfl) ⟨253454, by rfl⟩ : syracuseStep 1351757 = 506909) (by norm_num)
theorem B1155149 : Blo 511796 1155149 := bbase (se 3 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 1155149 = 433181) (by norm_num)
theorem B7610453 : Blo 511796 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1155221 : Blo 511796 1155221 := bbase (se 6 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 1155221 = 54151) (by norm_num)
theorem B1155293 : Blo 511796 1155293 := bbase (se 3 (by rfl) ⟨216617, by rfl⟩ : syracuseStep 1155293 = 433235) (by norm_num)
theorem B3285269 : Blo 511796 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B1155365 : Blo 511796 1155365 := bbase (se 4 (by rfl) ⟨108315, by rfl⟩ : syracuseStep 1155365 = 216631) (by norm_num)
theorem B3907925 : Blo 511796 3907925 := bbase (se 10 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 3907925 = 11449) (by norm_num)
theorem B1155437 : Blo 511796 1155437 := bbase (se 3 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 1155437 = 433289) (by norm_num)
theorem B926101 : Blo 511796 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B893357 : Blo 511796 893357 := bbase (se 3 (by rfl) ⟨167504, by rfl⟩ : syracuseStep 893357 = 335009) (by norm_num)
theorem B1155509 : Blo 511796 1155509 := bbase (se 5 (by rfl) ⟨54164, by rfl⟩ : syracuseStep 1155509 = 108329) (by norm_num)
theorem B1155581 : Blo 511796 1155581 := bbase (se 3 (by rfl) ⟨216671, by rfl⟩ : syracuseStep 1155581 = 433343) (by norm_num)
theorem B729661 : Blo 511796 729661 := bbase (se 3 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 729661 = 273623) (by norm_num)
theorem B1155653 : Blo 511796 1155653 := bbase (se 4 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 1155653 = 216685) (by norm_num)
theorem B1647221 : Blo 511796 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B1155725 : Blo 511796 1155725 := bbase (se 3 (by rfl) ⟨216698, by rfl⟩ : syracuseStep 1155725 = 433397) (by norm_num)
theorem B5415605 : Blo 511796 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B1155797 : Blo 511796 1155797 := bbase (se 7 (by rfl) ⟨13544, by rfl⟩ : syracuseStep 1155797 = 27089) (by norm_num)
theorem B1155869 : Blo 511796 1155869 := bbase (se 3 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 1155869 = 433451) (by norm_num)
theorem B2597669 : Blo 511796 2597669 := bbase (se 4 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 2597669 = 487063) (by norm_num)
theorem B1155941 : Blo 511796 1155941 := bbase (se 4 (by rfl) ⟨108369, by rfl⟩ : syracuseStep 1155941 = 216739) (by norm_num)
theorem B1156013 : Blo 511796 1156013 := bbase (se 3 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 1156013 = 433505) (by norm_num)
theorem B1156085 : Blo 511796 1156085 := bbase (se 5 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 1156085 = 108383) (by norm_num)
theorem B1385477 : Blo 511796 1385477 := bbase (se 4 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 1385477 = 259777) (by norm_num)
theorem B1156157 : Blo 511796 1156157 := bbase (se 3 (by rfl) ⟨216779, by rfl⟩ : syracuseStep 1156157 = 433559) (by norm_num)
theorem B5022805 : Blo 511796 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B1156229 : Blo 511796 1156229 := bbase (se 4 (by rfl) ⟨108396, by rfl⟩ : syracuseStep 1156229 = 216793) (by norm_num)
theorem B730253 : Blo 511796 730253 := bbase (se 3 (by rfl) ⟨136922, by rfl⟩ : syracuseStep 730253 = 273845) (by norm_num)
theorem B992405 : Blo 511796 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B1156301 : Blo 511796 1156301 := bbase (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) (by norm_num)
theorem B730333 : Blo 511796 730333 := bbase (se 3 (by rfl) ⟨136937, by rfl⟩ : syracuseStep 730333 = 273875) (by norm_num)
theorem B926981 : Blo 511796 926981 := bbase (se 4 (by rfl) ⟨86904, by rfl⟩ : syracuseStep 926981 = 173809) (by norm_num)
theorem B1156373 : Blo 511796 1156373 := bbase (se 6 (by rfl) ⟨27102, by rfl⟩ : syracuseStep 1156373 = 54205) (by norm_num)
theorem B730453 : Blo 511796 730453 := bbase (se 12 (by rfl) ⟨267, by rfl⟩ : syracuseStep 730453 = 535) (by norm_num)
theorem B1156445 : Blo 511796 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B1156517 : Blo 511796 1156517 := bbase (se 4 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 1156517 = 216847) (by norm_num)
theorem B730549 : Blo 511796 730549 := bbase (se 5 (by rfl) ⟨34244, by rfl⟩ : syracuseStep 730549 = 68489) (by norm_num)
theorem B1156589 : Blo 511796 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B1648133 : Blo 511796 1648133 := bbase (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) (by norm_num)
theorem B1386037 : Blo 511796 1386037 := bbase (se 5 (by rfl) ⟨64970, by rfl⟩ : syracuseStep 1386037 = 129941) (by norm_num)
theorem B1156661 : Blo 511796 1156661 := bbase (se 5 (by rfl) ⟨54218, by rfl⟩ : syracuseStep 1156661 = 108437) (by norm_num)
theorem B1156733 : Blo 511796 1156733 := bbase (se 3 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 1156733 = 433775) (by norm_num)
theorem B1156805 : Blo 511796 1156805 := bbase (se 4 (by rfl) ⟨108450, by rfl⟩ : syracuseStep 1156805 = 216901) (by norm_num)
theorem B927485 : Blo 511796 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B1156877 : Blo 511796 1156877 := bbase (se 3 (by rfl) ⟨216914, by rfl⟩ : syracuseStep 1156877 = 433829) (by norm_num)
theorem B1156949 : Blo 511796 1156949 := bbase (se 9 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 1156949 = 6779) (by norm_num)
theorem B1157021 : Blo 511796 1157021 := bbase (se 3 (by rfl) ⟨216941, by rfl⟩ : syracuseStep 1157021 = 433883) (by norm_num)
theorem B731045 : Blo 511796 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B1157093 : Blo 511796 1157093 := bbase (se 4 (by rfl) ⟨108477, by rfl⟩ : syracuseStep 1157093 = 216955) (by norm_num)
theorem B1157165 : Blo 511796 1157165 := bbase (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) (by norm_num)
theorem B2598965 : Blo 511796 2598965 := bbase (se 5 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 2598965 = 243653) (by norm_num)
theorem B1943621 : Blo 511796 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B1157237 : Blo 511796 1157237 := bbase (se 5 (by rfl) ⟨54245, by rfl⟩ : syracuseStep 1157237 = 108491) (by norm_num)
theorem B1157309 : Blo 511796 1157309 := bbase (se 3 (by rfl) ⟨216995, by rfl⟩ : syracuseStep 1157309 = 433991) (by norm_num)
theorem B1157381 : Blo 511796 1157381 := bbase (se 4 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 1157381 = 217009) (by norm_num)
theorem B1157453 : Blo 511796 1157453 := bbase (se 3 (by rfl) ⟨217022, by rfl⟩ : syracuseStep 1157453 = 434045) (by norm_num)
theorem B1943909 : Blo 511796 1943909 := bbase (se 4 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 1943909 = 364483) (by norm_num)
theorem B1157525 : Blo 511796 1157525 := bbase (se 6 (by rfl) ⟨27129, by rfl⟩ : syracuseStep 1157525 = 54259) (by norm_num)
theorem B731597 : Blo 511796 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B1157597 : Blo 511796 1157597 := bbase (se 3 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 1157597 = 434099) (by norm_num)
theorem B1157669 : Blo 511796 1157669 := bbase (se 4 (by rfl) ⟨108531, by rfl⟩ : syracuseStep 1157669 = 217063) (by norm_num)
theorem B1321525 : Blo 511796 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1157741 : Blo 511796 1157741 := bbase (se 3 (by rfl) ⟨217076, by rfl⟩ : syracuseStep 1157741 = 434153) (by norm_num)
theorem B1256093 : Blo 511796 1256093 := bbase (se 3 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 1256093 = 471035) (by norm_num)
theorem B1157813 : Blo 511796 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B1157885 : Blo 511796 1157885 := bbase (se 3 (by rfl) ⟨217103, by rfl⟩ : syracuseStep 1157885 = 434207) (by norm_num)
theorem B1157957 : Blo 511796 1157957 := bbase (se 4 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 1157957 = 217117) (by norm_num)
theorem B1649477 : Blo 511796 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B1158029 : Blo 511796 1158029 := bbase (se 3 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 1158029 = 434261) (by norm_num)
theorem B2927573 : Blo 511796 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B1158101 : Blo 511796 1158101 := bbase (se 7 (by rfl) ⟨13571, by rfl⟩ : syracuseStep 1158101 = 27143) (by norm_num)
theorem B1158173 : Blo 511796 1158173 := bbase (se 3 (by rfl) ⟨217157, by rfl⟩ : syracuseStep 1158173 = 434315) (by norm_num)
theorem B1158245 : Blo 511796 1158245 := bbase (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) (by norm_num)
theorem B1158317 : Blo 511796 1158317 := bbase (se 3 (by rfl) ⟨217184, by rfl⟩ : syracuseStep 1158317 = 434369) (by norm_num)
theorem B732349 : Blo 511796 732349 := bbase (se 3 (by rfl) ⟨137315, by rfl⟩ : syracuseStep 732349 = 274631) (by norm_num)
theorem B1158389 : Blo 511796 1158389 := bbase (se 5 (by rfl) ⟨54299, by rfl⟩ : syracuseStep 1158389 = 108599) (by norm_num)
theorem B7417109 : Blo 511796 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B1158461 : Blo 511796 1158461 := bbase (se 3 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 1158461 = 434423) (by norm_num)
theorem B2600261 : Blo 511796 2600261 := bbase (se 4 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 2600261 = 487549) (by norm_num)
theorem B1158533 : Blo 511796 1158533 := bbase (se 4 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 1158533 = 217225) (by norm_num)
theorem B863669 : Blo 511796 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B4926901 : Blo 511796 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B1158605 : Blo 511796 1158605 := bbase (se 3 (by rfl) ⟨217238, by rfl⟩ : syracuseStep 1158605 = 434477) (by norm_num)
theorem B1945093 : Blo 511796 1945093 := bbase (se 4 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 1945093 = 364705) (by norm_num)
theorem B1158677 : Blo 511796 1158677 := bbase (se 6 (by rfl) ⟨27156, by rfl⟩ : syracuseStep 1158677 = 54313) (by norm_num)
theorem B863797 : Blo 511796 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B1158749 : Blo 511796 1158749 := bbase (se 3 (by rfl) ⟨217265, by rfl⟩ : syracuseStep 1158749 = 434531) (by norm_num)
theorem B863885 : Blo 511796 863885 := bbase (se 3 (by rfl) ⟨161978, by rfl⟩ : syracuseStep 863885 = 323957) (by norm_num)
theorem B1158821 : Blo 511796 1158821 := bbase (se 4 (by rfl) ⟨108639, by rfl⟩ : syracuseStep 1158821 = 217279) (by norm_num)
theorem B634601 : Blo 511796 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B1158893 : Blo 511796 1158893 := bbase (se 3 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 1158893 = 434585) (by norm_num)
theorem B864013 : Blo 511796 864013 := bbase (se 3 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 864013 = 324005) (by norm_num)
theorem B6598421 : Blo 511796 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B1945397 : Blo 511796 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B1158965 : Blo 511796 1158965 := bbase (se 5 (by rfl) ⟨54326, by rfl⟩ : syracuseStep 1158965 = 108653) (by norm_num)
theorem B864101 : Blo 511796 864101 := bbase (se 4 (by rfl) ⟨81009, by rfl⟩ : syracuseStep 864101 = 162019) (by norm_num)
theorem B1093493 : Blo 511796 1093493 := bbase (se 5 (by rfl) ⟨51257, by rfl⟩ : syracuseStep 1093493 = 102515) (by norm_num)
theorem B1159037 : Blo 511796 1159037 := bbase (se 3 (by rfl) ⟨217319, by rfl⟩ : syracuseStep 1159037 = 434639) (by norm_num)
theorem B2469797 : Blo 511796 2469797 := bbase (se 4 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 2469797 = 463087) (by norm_num)
theorem B1159109 : Blo 511796 1159109 := bbase (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) (by norm_num)
theorem B733141 : Blo 511796 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B864229 : Blo 511796 864229 := bbase (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) (by norm_num)
theorem B1093637 : Blo 511796 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B1159181 : Blo 511796 1159181 := bbase (se 3 (by rfl) ⟨217346, by rfl⟩ : syracuseStep 1159181 = 434693) (by norm_num)
theorem B864317 : Blo 511796 864317 := bbase (se 3 (by rfl) ⟨162059, by rfl⟩ : syracuseStep 864317 = 324119) (by norm_num)
theorem B1159253 : Blo 511796 1159253 := bbase (se 8 (by rfl) ⟨6792, by rfl⟩ : syracuseStep 1159253 = 13585) (by norm_num)
theorem B2928757 : Blo 511796 2928757 := bbase (se 5 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 2928757 = 274571) (by norm_num)
theorem B1388677 : Blo 511796 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1159325 : Blo 511796 1159325 := bbase (se 3 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 1159325 = 434747) (by norm_num)
theorem B1847461 : Blo 511796 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B2076853 : Blo 511796 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B864445 : Blo 511796 864445 := bbase (se 3 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 864445 = 324167) (by norm_num)
theorem B1650901 : Blo 511796 1650901 := bbase (se 7 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 1650901 = 38693) (by norm_num)
theorem B1159397 : Blo 511796 1159397 := bbase (se 4 (by rfl) ⟨108693, by rfl⟩ : syracuseStep 1159397 = 217387) (by norm_num)
theorem B864533 : Blo 511796 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B733477 : Blo 511796 733477 := bbase (se 4 (by rfl) ⟨68763, by rfl⟩ : syracuseStep 733477 = 137527) (by norm_num)
theorem B1159469 : Blo 511796 1159469 := bbase (se 3 (by rfl) ⟨217400, by rfl⟩ : syracuseStep 1159469 = 434801) (by norm_num)
theorem B1159541 : Blo 511796 1159541 := bbase (se 5 (by rfl) ⟨54353, by rfl⟩ : syracuseStep 1159541 = 108707) (by norm_num)
theorem B864661 : Blo 511796 864661 := bbase (se 6 (by rfl) ⟨20265, by rfl⟩ : syracuseStep 864661 = 40531) (by norm_num)
theorem B1159613 : Blo 511796 1159613 := bbase (se 3 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 1159613 = 434855) (by norm_num)
theorem B864749 : Blo 511796 864749 := bbase (se 3 (by rfl) ⟨162140, by rfl⟩ : syracuseStep 864749 = 324281) (by norm_num)
theorem B733693 : Blo 511796 733693 := bbase (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) (by norm_num)
theorem B1159685 : Blo 511796 1159685 := bbase (se 4 (by rfl) ⟨108720, by rfl⟩ : syracuseStep 1159685 = 217441) (by norm_num)
theorem B1159757 : Blo 511796 1159757 := bbase (se 3 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 1159757 = 434909) (by norm_num)
theorem B2601557 : Blo 511796 2601557 := bbase (se 8 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 2601557 = 30487) (by norm_num)
theorem B864877 : Blo 511796 864877 := bbase (se 3 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 864877 = 324329) (by norm_num)
theorem B1159829 : Blo 511796 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B864965 : Blo 511796 864965 := bbase (se 4 (by rfl) ⟨81090, by rfl⟩ : syracuseStep 864965 = 162181) (by norm_num)
theorem B1159901 : Blo 511796 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B1094381 : Blo 511796 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B1159973 : Blo 511796 1159973 := bbase (se 4 (by rfl) ⟨108747, by rfl⟩ : syracuseStep 1159973 = 217495) (by norm_num)
theorem B865093 : Blo 511796 865093 := bbase (se 4 (by rfl) ⟨81102, by rfl⟩ : syracuseStep 865093 = 162205) (by norm_num)
theorem B6566741 : Blo 511796 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B1389413 : Blo 511796 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1160045 : Blo 511796 1160045 := bbase (se 3 (by rfl) ⟨217508, by rfl⟩ : syracuseStep 1160045 = 435017) (by norm_num)
theorem B734069 : Blo 511796 734069 := bbase (se 5 (by rfl) ⟨34409, by rfl⟩ : syracuseStep 734069 = 68819) (by norm_num)
theorem B865181 : Blo 511796 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B1160117 : Blo 511796 1160117 := bbase (se 5 (by rfl) ⟨54380, by rfl⟩ : syracuseStep 1160117 = 108761) (by norm_num)
theorem B1160189 : Blo 511796 1160189 := bbase (se 3 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 1160189 = 435071) (by norm_num)
theorem B865309 : Blo 511796 865309 := bbase (se 3 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 865309 = 324491) (by norm_num)
theorem B1160261 : Blo 511796 1160261 := bbase (se 4 (by rfl) ⟨108774, by rfl⟩ : syracuseStep 1160261 = 217549) (by norm_num)
theorem B865397 : Blo 511796 865397 := bbase (se 5 (by rfl) ⟨40565, by rfl⟩ : syracuseStep 865397 = 81131) (by norm_num)
theorem B1160333 : Blo 511796 1160333 := bbase (se 3 (by rfl) ⟨217562, by rfl⟩ : syracuseStep 1160333 = 435125) (by norm_num)
theorem B1160405 : Blo 511796 1160405 := bbase (se 7 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 1160405 = 27197) (by norm_num)
theorem B865525 : Blo 511796 865525 := bbase (se 5 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 865525 = 81143) (by norm_num)
theorem B1160477 : Blo 511796 1160477 := bbase (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) (by norm_num)
theorem B865613 : Blo 511796 865613 := bbase (se 3 (by rfl) ⟨162302, by rfl⟩ : syracuseStep 865613 = 324605) (by norm_num)
theorem B865741 : Blo 511796 865741 := bbase (se 3 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 865741 = 324653) (by norm_num)
theorem B1095133 : Blo 511796 1095133 := bbase (se 3 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 1095133 = 410675) (by norm_num)
theorem B2635253 : Blo 511796 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B865829 : Blo 511796 865829 := bbase (se 4 (by rfl) ⟨81171, by rfl⟩ : syracuseStep 865829 = 162343) (by norm_num)
theorem B8336981 : Blo 511796 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1095277 : Blo 511796 1095277 := bbase (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) (by norm_num)
theorem B865957 : Blo 511796 865957 := bbase (se 4 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 865957 = 162367) (by norm_num)
theorem B767717 : Blo 511796 767717 := bbase (se 4 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 767717 = 143947) (by norm_num)
theorem B767741 : Blo 511796 767741 := bbase (se 3 (by rfl) ⟨143951, by rfl⟩ : syracuseStep 767741 = 287903) (by norm_num)
theorem B866045 : Blo 511796 866045 := bbase (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) (by norm_num)
theorem B767765 : Blo 511796 767765 := bbase (se 6 (by rfl) ⟨17994, by rfl⟩ : syracuseStep 767765 = 35989) (by norm_num)
theorem B767789 : Blo 511796 767789 := bbase (se 3 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 767789 = 287921) (by norm_num)
theorem B767813 : Blo 511796 767813 := bbase (se 4 (by rfl) ⟨71982, by rfl⟩ : syracuseStep 767813 = 143965) (by norm_num)
theorem B767837 : Blo 511796 767837 := bbase (se 3 (by rfl) ⟨143969, by rfl⟩ : syracuseStep 767837 = 287939) (by norm_num)
theorem B2602853 : Blo 511796 2602853 := bbase (se 4 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 2602853 = 488035) (by norm_num)
theorem B767861 : Blo 511796 767861 := bbase (se 5 (by rfl) ⟨35993, by rfl⟩ : syracuseStep 767861 = 71987) (by norm_num)
theorem B1947509 : Blo 511796 1947509 := bbase (se 5 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 1947509 = 182579) (by norm_num)
theorem B866173 : Blo 511796 866173 := bbase (se 3 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 866173 = 324815) (by norm_num)
theorem B767885 : Blo 511796 767885 := bbase (se 3 (by rfl) ⟨143978, by rfl⟩ : syracuseStep 767885 = 287957) (by norm_num)
theorem B767909 : Blo 511796 767909 := bbase (se 4 (by rfl) ⟨71991, by rfl⟩ : syracuseStep 767909 = 143983) (by norm_num)
theorem B767933 : Blo 511796 767933 := bbase (se 3 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 767933 = 287975) (by norm_num)
theorem B767957 : Blo 511796 767957 := bbase (se 7 (by rfl) ⟨8999, by rfl⟩ : syracuseStep 767957 = 17999) (by norm_num)
theorem B866261 : Blo 511796 866261 := bbase (se 7 (by rfl) ⟨10151, by rfl⟩ : syracuseStep 866261 = 20303) (by norm_num)
theorem B1095653 : Blo 511796 1095653 := bbase (se 4 (by rfl) ⟨102717, by rfl⟩ : syracuseStep 1095653 = 205435) (by norm_num)
theorem B767981 : Blo 511796 767981 := bbase (se 3 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 767981 = 287993) (by norm_num)
theorem B768005 : Blo 511796 768005 := bbase (se 4 (by rfl) ⟨72000, by rfl⟩ : syracuseStep 768005 = 144001) (by norm_num)
theorem B768029 : Blo 511796 768029 := bbase (se 3 (by rfl) ⟨144005, by rfl⟩ : syracuseStep 768029 = 288011) (by norm_num)
theorem B768053 : Blo 511796 768053 := bbase (se 5 (by rfl) ⟨36002, by rfl⟩ : syracuseStep 768053 = 72005) (by norm_num)
theorem B2930741 : Blo 511796 2930741 := bbase (se 5 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 2930741 = 274757) (by norm_num)
theorem B768077 : Blo 511796 768077 := bbase (se 3 (by rfl) ⟨144014, by rfl⟩ : syracuseStep 768077 = 288029) (by norm_num)
theorem B866389 : Blo 511796 866389 := bbase (se 8 (by rfl) ⟨5076, by rfl⟩ : syracuseStep 866389 = 10153) (by norm_num)
theorem B768101 : Blo 511796 768101 := bbase (se 4 (by rfl) ⟨72009, by rfl⟩ : syracuseStep 768101 = 144019) (by norm_num)
theorem B768125 : Blo 511796 768125 := bbase (se 3 (by rfl) ⟨144023, by rfl⟩ : syracuseStep 768125 = 288047) (by norm_num)
theorem B768149 : Blo 511796 768149 := bbase (se 6 (by rfl) ⟨18003, by rfl⟩ : syracuseStep 768149 = 36007) (by norm_num)
theorem B1947797 : Blo 511796 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B768173 : Blo 511796 768173 := bbase (se 3 (by rfl) ⟨144032, by rfl⟩ : syracuseStep 768173 = 288065) (by norm_num)
theorem B866477 : Blo 511796 866477 := bbase (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) (by norm_num)
theorem B768197 : Blo 511796 768197 := bbase (se 4 (by rfl) ⟨72018, by rfl⟩ : syracuseStep 768197 = 144037) (by norm_num)
theorem B768221 : Blo 511796 768221 := bbase (se 3 (by rfl) ⟨144041, by rfl⟩ : syracuseStep 768221 = 288083) (by norm_num)
theorem B768245 : Blo 511796 768245 := bbase (se 5 (by rfl) ⟨36011, by rfl⟩ : syracuseStep 768245 = 72023) (by norm_num)
theorem B768269 : Blo 511796 768269 := bbase (se 3 (by rfl) ⟨144050, by rfl⟩ : syracuseStep 768269 = 288101) (by norm_num)
theorem B768293 : Blo 511796 768293 := bbase (se 4 (by rfl) ⟨72027, by rfl⟩ : syracuseStep 768293 = 144055) (by norm_num)
theorem B866605 : Blo 511796 866605 := bbase (se 3 (by rfl) ⟨162488, by rfl⟩ : syracuseStep 866605 = 324977) (by norm_num)
theorem B768317 : Blo 511796 768317 := bbase (se 3 (by rfl) ⟨144059, by rfl⟩ : syracuseStep 768317 = 288119) (by norm_num)
theorem B768341 : Blo 511796 768341 := bbase (se 10 (by rfl) ⟨1125, by rfl⟩ : syracuseStep 768341 = 2251) (by norm_num)
theorem B1096021 : Blo 511796 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B768365 : Blo 511796 768365 := bbase (se 3 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 768365 = 288137) (by norm_num)
theorem B768389 : Blo 511796 768389 := bbase (se 4 (by rfl) ⟨72036, by rfl⟩ : syracuseStep 768389 = 144073) (by norm_num)
theorem B866693 : Blo 511796 866693 := bbase (se 4 (by rfl) ⟨81252, by rfl⟩ : syracuseStep 866693 = 162505) (by norm_num)
theorem B768413 : Blo 511796 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B768437 : Blo 511796 768437 := bbase (se 5 (by rfl) ⟨36020, by rfl⟩ : syracuseStep 768437 = 72041) (by norm_num)
theorem B768461 : Blo 511796 768461 := bbase (se 3 (by rfl) ⟨144086, by rfl⟩ : syracuseStep 768461 = 288173) (by norm_num)
theorem B768485 : Blo 511796 768485 := bbase (se 4 (by rfl) ⟨72045, by rfl⟩ : syracuseStep 768485 = 144091) (by norm_num)
theorem B768509 : Blo 511796 768509 := bbase (se 3 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 768509 = 288191) (by norm_num)
theorem B866821 : Blo 511796 866821 := bbase (se 4 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 866821 = 162529) (by norm_num)
theorem B768533 : Blo 511796 768533 := bbase (se 6 (by rfl) ⟨18012, by rfl⟩ : syracuseStep 768533 = 36025) (by norm_num)
theorem B768557 : Blo 511796 768557 := bbase (se 3 (by rfl) ⟨144104, by rfl⟩ : syracuseStep 768557 = 288209) (by norm_num)
theorem B768581 : Blo 511796 768581 := bbase (se 4 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 768581 = 144109) (by norm_num)
theorem B768605 : Blo 511796 768605 := bbase (se 3 (by rfl) ⟨144113, by rfl⟩ : syracuseStep 768605 = 288227) (by norm_num)
theorem B866909 : Blo 511796 866909 := bbase (se 3 (by rfl) ⟨162545, by rfl⟩ : syracuseStep 866909 = 325091) (by norm_num)
theorem B768629 : Blo 511796 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B768653 : Blo 511796 768653 := bbase (se 3 (by rfl) ⟨144122, by rfl⟩ : syracuseStep 768653 = 288245) (by norm_num)
theorem B768677 : Blo 511796 768677 := bbase (se 4 (by rfl) ⟨72063, by rfl⟩ : syracuseStep 768677 = 144127) (by norm_num)
theorem B768701 : Blo 511796 768701 := bbase (se 3 (by rfl) ⟨144131, by rfl⟩ : syracuseStep 768701 = 288263) (by norm_num)
theorem B768725 : Blo 511796 768725 := bbase (se 7 (by rfl) ⟨9008, by rfl⟩ : syracuseStep 768725 = 18017) (by norm_num)
theorem B867037 : Blo 511796 867037 := bbase (se 3 (by rfl) ⟨162569, by rfl⟩ : syracuseStep 867037 = 325139) (by norm_num)
theorem B768749 : Blo 511796 768749 := bbase (se 3 (by rfl) ⟨144140, by rfl⟩ : syracuseStep 768749 = 288281) (by norm_num)
theorem B768773 : Blo 511796 768773 := bbase (se 4 (by rfl) ⟨72072, by rfl⟩ : syracuseStep 768773 = 144145) (by norm_num)
theorem B768797 : Blo 511796 768797 := bbase (se 3 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 768797 = 288299) (by norm_num)
theorem B768821 : Blo 511796 768821 := bbase (se 5 (by rfl) ⟨36038, by rfl⟩ : syracuseStep 768821 = 72077) (by norm_num)
theorem B867125 : Blo 511796 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B768845 : Blo 511796 768845 := bbase (se 3 (by rfl) ⟨144158, by rfl⟩ : syracuseStep 768845 = 288317) (by norm_num)
theorem B768869 : Blo 511796 768869 := bbase (se 4 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 768869 = 144163) (by norm_num)
theorem B768893 : Blo 511796 768893 := bbase (se 3 (by rfl) ⟨144167, by rfl⟩ : syracuseStep 768893 = 288335) (by norm_num)
theorem B768917 : Blo 511796 768917 := bbase (se 6 (by rfl) ⟨18021, by rfl⟩ : syracuseStep 768917 = 36043) (by norm_num)
theorem B1391509 : Blo 511796 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B768941 : Blo 511796 768941 := bbase (se 3 (by rfl) ⟨144176, by rfl⟩ : syracuseStep 768941 = 288353) (by norm_num)
theorem B2702261 : Blo 511796 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B867253 : Blo 511796 867253 := bbase (se 5 (by rfl) ⟨40652, by rfl⟩ : syracuseStep 867253 = 81305) (by norm_num)
theorem B768965 : Blo 511796 768965 := bbase (se 4 (by rfl) ⟨72090, by rfl⟩ : syracuseStep 768965 = 144181) (by norm_num)
theorem B1391573 : Blo 511796 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B768989 : Blo 511796 768989 := bbase (se 3 (by rfl) ⟨144185, by rfl⟩ : syracuseStep 768989 = 288371) (by norm_num)
theorem B769013 : Blo 511796 769013 := bbase (se 5 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 769013 = 72095) (by norm_num)
theorem B1850357 : Blo 511796 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B769037 : Blo 511796 769037 := bbase (se 3 (by rfl) ⟨144194, by rfl⟩ : syracuseStep 769037 = 288389) (by norm_num)
theorem B867341 : Blo 511796 867341 := bbase (se 3 (by rfl) ⟨162626, by rfl⟩ : syracuseStep 867341 = 325253) (by norm_num)
theorem B769061 : Blo 511796 769061 := bbase (se 4 (by rfl) ⟨72099, by rfl⟩ : syracuseStep 769061 = 144199) (by norm_num)
theorem B769085 : Blo 511796 769085 := bbase (se 3 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 769085 = 288407) (by norm_num)
theorem B769109 : Blo 511796 769109 := bbase (se 8 (by rfl) ⟨4506, by rfl⟩ : syracuseStep 769109 = 9013) (by norm_num)
theorem B769133 : Blo 511796 769133 := bbase (se 3 (by rfl) ⟨144212, by rfl⟩ : syracuseStep 769133 = 288425) (by norm_num)
theorem B2604149 : Blo 511796 2604149 := bbase (se 5 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 2604149 = 244139) (by norm_num)
theorem B769157 : Blo 511796 769157 := bbase (se 4 (by rfl) ⟨72108, by rfl⟩ : syracuseStep 769157 = 144217) (by norm_num)
theorem B867469 : Blo 511796 867469 := bbase (se 3 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 867469 = 325301) (by norm_num)
theorem B769181 : Blo 511796 769181 := bbase (se 3 (by rfl) ⟨144221, by rfl⟩ : syracuseStep 769181 = 288443) (by norm_num)
theorem B769205 : Blo 511796 769205 := bbase (se 5 (by rfl) ⟨36056, by rfl⟩ : syracuseStep 769205 = 72113) (by norm_num)
theorem B769229 : Blo 511796 769229 := bbase (se 3 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 769229 = 288461) (by norm_num)
theorem B1752293 : Blo 511796 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B769253 : Blo 511796 769253 := bbase (se 4 (by rfl) ⟨72117, by rfl⟩ : syracuseStep 769253 = 144235) (by norm_num)
theorem B867557 : Blo 511796 867557 := bbase (se 4 (by rfl) ⟨81333, by rfl⟩ : syracuseStep 867557 = 162667) (by norm_num)
theorem B1785077 : Blo 511796 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B769277 : Blo 511796 769277 := bbase (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) (by norm_num)
theorem B769301 : Blo 511796 769301 := bbase (se 6 (by rfl) ⟨18030, by rfl⟩ : syracuseStep 769301 = 36061) (by norm_num)
theorem B769325 : Blo 511796 769325 := bbase (se 3 (by rfl) ⟨144248, by rfl⟩ : syracuseStep 769325 = 288497) (by norm_num)
theorem B1948981 : Blo 511796 1948981 := bbase (se 5 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 1948981 = 182717) (by norm_num)
theorem B1457477 : Blo 511796 1457477 := bbase (se 4 (by rfl) ⟨136638, by rfl⟩ : syracuseStep 1457477 = 273277) (by norm_num)
theorem B769349 : Blo 511796 769349 := bbase (se 4 (by rfl) ⟨72126, by rfl⟩ : syracuseStep 769349 = 144253) (by norm_num)
theorem B4930901 : Blo 511796 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B769373 : Blo 511796 769373 := bbase (se 3 (by rfl) ⟨144257, by rfl⟩ : syracuseStep 769373 = 288515) (by norm_num)
theorem B867685 : Blo 511796 867685 := bbase (se 4 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 867685 = 162691) (by norm_num)
theorem B769397 : Blo 511796 769397 := bbase (se 5 (by rfl) ⟨36065, by rfl⟩ : syracuseStep 769397 = 72131) (by norm_num)
theorem B769421 : Blo 511796 769421 := bbase (se 3 (by rfl) ⟨144266, by rfl⟩ : syracuseStep 769421 = 288533) (by norm_num)
theorem B769445 : Blo 511796 769445 := bbase (se 4 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 769445 = 144271) (by norm_num)
theorem B769469 : Blo 511796 769469 := bbase (se 3 (by rfl) ⟨144275, by rfl⟩ : syracuseStep 769469 = 288551) (by norm_num)
theorem B867773 : Blo 511796 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B769493 : Blo 511796 769493 := bbase (se 7 (by rfl) ⟨9017, by rfl⟩ : syracuseStep 769493 = 18035) (by norm_num)
theorem B2473429 : Blo 511796 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B769517 : Blo 511796 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B769541 : Blo 511796 769541 := bbase (se 4 (by rfl) ⟨72144, by rfl⟩ : syracuseStep 769541 = 144289) (by norm_num)
theorem B769565 : Blo 511796 769565 := bbase (se 3 (by rfl) ⟨144293, by rfl⟩ : syracuseStep 769565 = 288587) (by norm_num)
theorem B769589 : Blo 511796 769589 := bbase (se 5 (by rfl) ⟨36074, by rfl⟩ : syracuseStep 769589 = 72149) (by norm_num)
theorem B867901 : Blo 511796 867901 := bbase (se 3 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 867901 = 325463) (by norm_num)
theorem B769613 : Blo 511796 769613 := bbase (se 3 (by rfl) ⟨144302, by rfl⟩ : syracuseStep 769613 = 288605) (by norm_num)
theorem B769637 : Blo 511796 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B1949285 : Blo 511796 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B769661 : Blo 511796 769661 := bbase (se 3 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 769661 = 288623) (by norm_num)
theorem B769685 : Blo 511796 769685 := bbase (se 6 (by rfl) ⟨18039, by rfl⟩ : syracuseStep 769685 = 36079) (by norm_num)
theorem B867989 : Blo 511796 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B769709 : Blo 511796 769709 := bbase (se 3 (by rfl) ⟨144320, by rfl⟩ : syracuseStep 769709 = 288641) (by norm_num)
theorem B769733 : Blo 511796 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B769757 : Blo 511796 769757 := bbase (se 3 (by rfl) ⟨144329, by rfl⟩ : syracuseStep 769757 = 288659) (by norm_num)
theorem B1457909 : Blo 511796 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B769781 : Blo 511796 769781 := bbase (se 5 (by rfl) ⟨36083, by rfl⟩ : syracuseStep 769781 = 72167) (by norm_num)
theorem B769805 : Blo 511796 769805 := bbase (se 3 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 769805 = 288677) (by norm_num)
theorem B868117 : Blo 511796 868117 := bbase (se 6 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 868117 = 40693) (by norm_num)
theorem B769829 : Blo 511796 769829 := bbase (se 4 (by rfl) ⟨72171, by rfl⟩ : syracuseStep 769829 = 144343) (by norm_num)
theorem B1097525 : Blo 511796 1097525 := bbase (se 5 (by rfl) ⟨51446, by rfl⟩ : syracuseStep 1097525 = 102893) (by norm_num)
theorem B769853 : Blo 511796 769853 := bbase (se 3 (by rfl) ⟨144347, by rfl⟩ : syracuseStep 769853 = 288695) (by norm_num)
theorem B769877 : Blo 511796 769877 := bbase (se 9 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 769877 = 4511) (by norm_num)
theorem B2080613 : Blo 511796 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B769901 : Blo 511796 769901 := bbase (se 3 (by rfl) ⟨144356, by rfl⟩ : syracuseStep 769901 = 288713) (by norm_num)
theorem B868205 : Blo 511796 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B769925 : Blo 511796 769925 := bbase (se 4 (by rfl) ⟨72180, by rfl⟩ : syracuseStep 769925 = 144361) (by norm_num)
theorem B769949 : Blo 511796 769949 := bbase (se 3 (by rfl) ⟨144365, by rfl⟩ : syracuseStep 769949 = 288731) (by norm_num)
theorem B769973 : Blo 511796 769973 := bbase (se 5 (by rfl) ⟨36092, by rfl⟩ : syracuseStep 769973 = 72185) (by norm_num)
theorem B3915701 : Blo 511796 3915701 := bbase (se 5 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 3915701 = 367097) (by norm_num)
theorem B1097669 : Blo 511796 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B769997 : Blo 511796 769997 := bbase (se 3 (by rfl) ⟨144374, by rfl⟩ : syracuseStep 769997 = 288749) (by norm_num)
theorem B770021 : Blo 511796 770021 := bbase (se 4 (by rfl) ⟨72189, by rfl⟩ : syracuseStep 770021 = 144379) (by norm_num)
theorem B868333 : Blo 511796 868333 := bbase (se 3 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 868333 = 325625) (by norm_num)
theorem B770045 : Blo 511796 770045 := bbase (se 3 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 770045 = 288767) (by norm_num)
theorem B770069 : Blo 511796 770069 := bbase (se 6 (by rfl) ⟨18048, by rfl⟩ : syracuseStep 770069 = 36097) (by norm_num)
theorem B770093 : Blo 511796 770093 := bbase (se 3 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 770093 = 288785) (by norm_num)
theorem B770117 : Blo 511796 770117 := bbase (se 4 (by rfl) ⟨72198, by rfl⟩ : syracuseStep 770117 = 144397) (by norm_num)
theorem B868421 : Blo 511796 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B770141 : Blo 511796 770141 := bbase (se 3 (by rfl) ⟨144401, by rfl⟩ : syracuseStep 770141 = 288803) (by norm_num)
theorem B770165 : Blo 511796 770165 := bbase (se 5 (by rfl) ⟨36101, by rfl⟩ : syracuseStep 770165 = 72203) (by norm_num)
theorem B770189 : Blo 511796 770189 := bbase (se 3 (by rfl) ⟨144410, by rfl⟩ : syracuseStep 770189 = 288821) (by norm_num)
theorem B770213 : Blo 511796 770213 := bbase (se 4 (by rfl) ⟨72207, by rfl⟩ : syracuseStep 770213 = 144415) (by norm_num)
theorem B770237 : Blo 511796 770237 := bbase (se 3 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 770237 = 288839) (by norm_num)
theorem B868549 : Blo 511796 868549 := bbase (se 4 (by rfl) ⟨81426, by rfl⟩ : syracuseStep 868549 = 162853) (by norm_num)
theorem B770261 : Blo 511796 770261 := bbase (se 7 (by rfl) ⟨9026, by rfl⟩ : syracuseStep 770261 = 18053) (by norm_num)
theorem B2932949 : Blo 511796 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B770285 : Blo 511796 770285 := bbase (se 3 (by rfl) ⟨144428, by rfl⟩ : syracuseStep 770285 = 288857) (by norm_num)
theorem B770309 : Blo 511796 770309 := bbase (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) (by norm_num)
theorem B770333 : Blo 511796 770333 := bbase (se 3 (by rfl) ⟨144437, by rfl⟩ : syracuseStep 770333 = 288875) (by norm_num)
theorem B868637 : Blo 511796 868637 := bbase (se 3 (by rfl) ⟨162869, by rfl⟩ : syracuseStep 868637 = 325739) (by norm_num)
theorem B1098029 : Blo 511796 1098029 := bbase (se 3 (by rfl) ⟨205880, by rfl⟩ : syracuseStep 1098029 = 411761) (by norm_num)
theorem B770357 : Blo 511796 770357 := bbase (se 5 (by rfl) ⟨36110, by rfl⟩ : syracuseStep 770357 = 72221) (by norm_num)
theorem B770381 : Blo 511796 770381 := bbase (se 3 (by rfl) ⟨144446, by rfl⟩ : syracuseStep 770381 = 288893) (by norm_num)
theorem B770405 : Blo 511796 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B770429 : Blo 511796 770429 := bbase (se 3 (by rfl) ⟨144455, by rfl⟩ : syracuseStep 770429 = 288911) (by norm_num)
theorem B2605445 : Blo 511796 2605445 := bbase (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) (by norm_num)
theorem B770453 : Blo 511796 770453 := bbase (se 6 (by rfl) ⟨18057, by rfl⟩ : syracuseStep 770453 = 36115) (by norm_num)
theorem B868765 : Blo 511796 868765 := bbase (se 3 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 868765 = 325787) (by norm_num)
theorem B770477 : Blo 511796 770477 := bbase (se 3 (by rfl) ⟨144464, by rfl⟩ : syracuseStep 770477 = 288929) (by norm_num)
theorem B770501 : Blo 511796 770501 := bbase (se 4 (by rfl) ⟨72234, by rfl⟩ : syracuseStep 770501 = 144469) (by norm_num)
theorem B770525 : Blo 511796 770525 := bbase (se 3 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 770525 = 288947) (by norm_num)
theorem B1458661 : Blo 511796 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B770549 : Blo 511796 770549 := bbase (se 5 (by rfl) ⟨36119, by rfl⟩ : syracuseStep 770549 = 72239) (by norm_num)
theorem B868853 : Blo 511796 868853 := bbase (se 5 (by rfl) ⟨40727, by rfl⟩ : syracuseStep 868853 = 81455) (by norm_num)
theorem B770573 : Blo 511796 770573 := bbase (se 3 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 770573 = 288965) (by norm_num)
theorem B770597 : Blo 511796 770597 := bbase (se 4 (by rfl) ⟨72243, by rfl⟩ : syracuseStep 770597 = 144487) (by norm_num)
theorem B4375093 : Blo 511796 4375093 := bbase (se 5 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 4375093 = 410165) (by norm_num)
theorem B2769461 : Blo 511796 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B770621 : Blo 511796 770621 := bbase (se 3 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 770621 = 288983) (by norm_num)
theorem B770645 : Blo 511796 770645 := bbase (se 8 (by rfl) ⟨4515, by rfl⟩ : syracuseStep 770645 = 9031) (by norm_num)
theorem B770669 : Blo 511796 770669 := bbase (se 3 (by rfl) ⟨144500, by rfl⟩ : syracuseStep 770669 = 289001) (by norm_num)
theorem B868981 : Blo 511796 868981 := bbase (se 5 (by rfl) ⟨40733, by rfl⟩ : syracuseStep 868981 = 81467) (by norm_num)
theorem B770693 : Blo 511796 770693 := bbase (se 4 (by rfl) ⟨72252, by rfl⟩ : syracuseStep 770693 = 144505) (by norm_num)
theorem B770717 : Blo 511796 770717 := bbase (se 3 (by rfl) ⟨144509, by rfl⟩ : syracuseStep 770717 = 289019) (by norm_num)
theorem B770741 : Blo 511796 770741 := bbase (se 5 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 770741 = 72257) (by norm_num)
theorem B770765 : Blo 511796 770765 := bbase (se 3 (by rfl) ⟨144518, by rfl⟩ : syracuseStep 770765 = 289037) (by norm_num)
theorem B869069 : Blo 511796 869069 := bbase (se 3 (by rfl) ⟨162950, by rfl⟩ : syracuseStep 869069 = 325901) (by norm_num)
theorem B770789 : Blo 511796 770789 := bbase (se 4 (by rfl) ⟨72261, by rfl⟩ : syracuseStep 770789 = 144523) (by norm_num)
theorem B2769653 : Blo 511796 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B770813 : Blo 511796 770813 := bbase (se 3 (by rfl) ⟨144527, by rfl⟩ : syracuseStep 770813 = 289055) (by norm_num)
theorem B770837 : Blo 511796 770837 := bbase (se 6 (by rfl) ⟨18066, by rfl⟩ : syracuseStep 770837 = 36133) (by norm_num)
theorem B770861 : Blo 511796 770861 := bbase (se 3 (by rfl) ⟨144536, by rfl⟩ : syracuseStep 770861 = 289073) (by norm_num)
theorem B770885 : Blo 511796 770885 := bbase (se 4 (by rfl) ⟨72270, by rfl⟩ : syracuseStep 770885 = 144541) (by norm_num)
theorem B869197 : Blo 511796 869197 := bbase (se 3 (by rfl) ⟨162974, by rfl⟩ : syracuseStep 869197 = 325949) (by norm_num)
theorem B20071253 : Blo 511796 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B770909 : Blo 511796 770909 := bbase (se 3 (by rfl) ⟨144545, by rfl⟩ : syracuseStep 770909 = 289091) (by norm_num)
theorem B770933 : Blo 511796 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B770957 : Blo 511796 770957 := bbase (se 3 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 770957 = 289109) (by norm_num)
theorem B770981 : Blo 511796 770981 := bbase (se 4 (by rfl) ⟨72279, by rfl⟩ : syracuseStep 770981 = 144559) (by norm_num)
theorem B869285 : Blo 511796 869285 := bbase (se 4 (by rfl) ⟨81495, by rfl⟩ : syracuseStep 869285 = 162991) (by norm_num)
theorem B771005 : Blo 511796 771005 := bbase (se 3 (by rfl) ⟨144563, by rfl⟩ : syracuseStep 771005 = 289127) (by norm_num)
theorem B771029 : Blo 511796 771029 := bbase (se 7 (by rfl) ⟨9035, by rfl⟩ : syracuseStep 771029 = 18071) (by norm_num)
theorem B771053 : Blo 511796 771053 := bbase (se 3 (by rfl) ⟨144572, by rfl⟩ : syracuseStep 771053 = 289145) (by norm_num)
theorem B771077 : Blo 511796 771077 := bbase (se 4 (by rfl) ⟨72288, by rfl⟩ : syracuseStep 771077 = 144577) (by norm_num)
theorem B771101 : Blo 511796 771101 := bbase (se 3 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 771101 = 289163) (by norm_num)
theorem B869413 : Blo 511796 869413 := bbase (se 4 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 869413 = 163015) (by norm_num)
theorem B771125 : Blo 511796 771125 := bbase (se 5 (by rfl) ⟨36146, by rfl⟩ : syracuseStep 771125 = 72293) (by norm_num)
theorem B771149 : Blo 511796 771149 := bbase (se 3 (by rfl) ⟨144590, by rfl⟩ : syracuseStep 771149 = 289181) (by norm_num)
theorem B771173 : Blo 511796 771173 := bbase (se 4 (by rfl) ⟨72297, by rfl⟩ : syracuseStep 771173 = 144595) (by norm_num)
theorem B771197 : Blo 511796 771197 := bbase (se 3 (by rfl) ⟨144599, by rfl⟩ : syracuseStep 771197 = 289199) (by norm_num)
theorem B869501 : Blo 511796 869501 := bbase (se 3 (by rfl) ⟨163031, by rfl⟩ : syracuseStep 869501 = 326063) (by norm_num)
theorem B771221 : Blo 511796 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B1098917 : Blo 511796 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B771245 : Blo 511796 771245 := bbase (se 3 (by rfl) ⟨144608, by rfl⟩ : syracuseStep 771245 = 289217) (by norm_num)
theorem B771269 : Blo 511796 771269 := bbase (se 4 (by rfl) ⟨72306, by rfl⟩ : syracuseStep 771269 = 144613) (by norm_num)
theorem B771293 : Blo 511796 771293 := bbase (se 3 (by rfl) ⟨144617, by rfl⟩ : syracuseStep 771293 = 289235) (by norm_num)
theorem B771317 : Blo 511796 771317 := bbase (se 5 (by rfl) ⟨36155, by rfl⟩ : syracuseStep 771317 = 72311) (by norm_num)
theorem B1983733 : Blo 511796 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B869629 : Blo 511796 869629 := bbase (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) (by norm_num)
theorem B771341 : Blo 511796 771341 := bbase (se 3 (by rfl) ⟨144626, by rfl⟩ : syracuseStep 771341 = 289253) (by norm_num)
theorem B771365 : Blo 511796 771365 := bbase (se 4 (by rfl) ⟨72315, by rfl⟩ : syracuseStep 771365 = 144631) (by norm_num)
theorem B771389 : Blo 511796 771389 := bbase (se 3 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 771389 = 289271) (by norm_num)
theorem B771413 : Blo 511796 771413 := bbase (se 12 (by rfl) ⟨282, by rfl⟩ : syracuseStep 771413 = 565) (by norm_num)
theorem B869717 : Blo 511796 869717 := bbase (se 12 (by rfl) ⟨318, by rfl⟩ : syracuseStep 869717 = 637) (by norm_num)
theorem B771437 : Blo 511796 771437 := bbase (se 3 (by rfl) ⟨144644, by rfl⟩ : syracuseStep 771437 = 289289) (by norm_num)
theorem B771461 : Blo 511796 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B771485 : Blo 511796 771485 := bbase (se 3 (by rfl) ⟨144653, by rfl⟩ : syracuseStep 771485 = 289307) (by norm_num)
theorem B1099165 : Blo 511796 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B1295797 : Blo 511796 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B771509 : Blo 511796 771509 := bbase (se 5 (by rfl) ⟨36164, by rfl⟩ : syracuseStep 771509 = 72329) (by norm_num)
theorem B771533 : Blo 511796 771533 := bbase (se 3 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 771533 = 289325) (by norm_num)
theorem B869845 : Blo 511796 869845 := bbase (se 7 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 869845 = 20387) (by norm_num)
theorem B771557 : Blo 511796 771557 := bbase (se 4 (by rfl) ⟨72333, by rfl⟩ : syracuseStep 771557 = 144667) (by norm_num)
theorem B771581 : Blo 511796 771581 := bbase (se 3 (by rfl) ⟨144671, by rfl⟩ : syracuseStep 771581 = 289343) (by norm_num)
theorem B771605 : Blo 511796 771605 := bbase (se 6 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 771605 = 36169) (by norm_num)
theorem B1295909 : Blo 511796 1295909 := bbase (se 4 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 1295909 = 242983) (by norm_num)
theorem B771629 : Blo 511796 771629 := bbase (se 3 (by rfl) ⟨144680, by rfl⟩ : syracuseStep 771629 = 289361) (by norm_num)
theorem B869933 : Blo 511796 869933 := bbase (se 3 (by rfl) ⟨163112, by rfl⟩ : syracuseStep 869933 = 326225) (by norm_num)
theorem B5064245 : Blo 511796 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B771653 : Blo 511796 771653 := bbase (se 4 (by rfl) ⟨72342, by rfl⟩ : syracuseStep 771653 = 144685) (by norm_num)
theorem B771677 : Blo 511796 771677 := bbase (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) (by norm_num)
theorem B771701 : Blo 511796 771701 := bbase (se 5 (by rfl) ⟨36173, by rfl⟩ : syracuseStep 771701 = 72347) (by norm_num)
theorem B771725 : Blo 511796 771725 := bbase (se 3 (by rfl) ⟨144698, by rfl⟩ : syracuseStep 771725 = 289397) (by norm_num)
theorem B2606741 : Blo 511796 2606741 := bbase (se 6 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 2606741 = 122191) (by norm_num)
theorem B1951397 : Blo 511796 1951397 := bbase (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) (by norm_num)
theorem B771749 : Blo 511796 771749 := bbase (se 4 (by rfl) ⟨72351, by rfl⟩ : syracuseStep 771749 = 144703) (by norm_num)
theorem B870061 : Blo 511796 870061 := bbase (se 3 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 870061 = 326273) (by norm_num)
theorem B771773 : Blo 511796 771773 := bbase (se 3 (by rfl) ⟨144707, by rfl⟩ : syracuseStep 771773 = 289415) (by norm_num)
theorem B771797 : Blo 511796 771797 := bbase (se 7 (by rfl) ⟨9044, by rfl⟩ : syracuseStep 771797 = 18089) (by norm_num)
theorem B1296101 : Blo 511796 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B771821 : Blo 511796 771821 := bbase (se 3 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 771821 = 289433) (by norm_num)
theorem B771845 : Blo 511796 771845 := bbase (se 4 (by rfl) ⟨72360, by rfl⟩ : syracuseStep 771845 = 144721) (by norm_num)
theorem B870149 : Blo 511796 870149 := bbase (se 4 (by rfl) ⟨81576, by rfl⟩ : syracuseStep 870149 = 163153) (by norm_num)
theorem B771869 : Blo 511796 771869 := bbase (se 3 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 771869 = 289451) (by norm_num)
theorem B771893 : Blo 511796 771893 := bbase (se 5 (by rfl) ⟨36182, by rfl⟩ : syracuseStep 771893 = 72365) (by norm_num)
theorem B771917 : Blo 511796 771917 := bbase (se 3 (by rfl) ⟨144734, by rfl⟩ : syracuseStep 771917 = 289469) (by norm_num)
theorem B771941 : Blo 511796 771941 := bbase (se 4 (by rfl) ⟨72369, by rfl⟩ : syracuseStep 771941 = 144739) (by norm_num)
theorem B771965 : Blo 511796 771965 := bbase (se 3 (by rfl) ⟨144743, by rfl⟩ : syracuseStep 771965 = 289487) (by norm_num)
theorem B870277 : Blo 511796 870277 := bbase (se 4 (by rfl) ⟨81588, by rfl⟩ : syracuseStep 870277 = 163177) (by norm_num)
theorem B771989 : Blo 511796 771989 := bbase (se 6 (by rfl) ⟨18093, by rfl⟩ : syracuseStep 771989 = 36187) (by norm_num)
theorem B1099669 : Blo 511796 1099669 := bbase (se 6 (by rfl) ⟨25773, by rfl⟩ : syracuseStep 1099669 = 51547) (by norm_num)
theorem B772013 : Blo 511796 772013 := bbase (se 3 (by rfl) ⟨144752, by rfl⟩ : syracuseStep 772013 = 289505) (by norm_num)
theorem B1951685 : Blo 511796 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B772037 : Blo 511796 772037 := bbase (se 4 (by rfl) ⟨72378, by rfl⟩ : syracuseStep 772037 = 144757) (by norm_num)
theorem B772061 : Blo 511796 772061 := bbase (se 3 (by rfl) ⟨144761, by rfl⟩ : syracuseStep 772061 = 289523) (by norm_num)
theorem B870365 : Blo 511796 870365 := bbase (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) (by norm_num)
theorem B772085 : Blo 511796 772085 := bbase (se 5 (by rfl) ⟨36191, by rfl⟩ : syracuseStep 772085 = 72383) (by norm_num)
theorem B772109 : Blo 511796 772109 := bbase (se 3 (by rfl) ⟨144770, by rfl⟩ : syracuseStep 772109 = 289541) (by norm_num)
theorem B772133 : Blo 511796 772133 := bbase (se 4 (by rfl) ⟨72387, by rfl⟩ : syracuseStep 772133 = 144775) (by norm_num)
theorem B1296445 : Blo 511796 1296445 := bbase (se 3 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 1296445 = 486167) (by norm_num)
theorem B772157 : Blo 511796 772157 := bbase (se 3 (by rfl) ⟨144779, by rfl⟩ : syracuseStep 772157 = 289559) (by norm_num)
theorem B772181 : Blo 511796 772181 := bbase (se 8 (by rfl) ⟨4524, by rfl⟩ : syracuseStep 772181 = 9049) (by norm_num)
theorem B772205 : Blo 511796 772205 := bbase (se 3 (by rfl) ⟨144788, by rfl⟩ : syracuseStep 772205 = 289577) (by norm_num)
theorem B772229 : Blo 511796 772229 := bbase (se 4 (by rfl) ⟨72396, by rfl⟩ : syracuseStep 772229 = 144793) (by norm_num)
theorem B772253 : Blo 511796 772253 := bbase (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) (by norm_num)
theorem B1296557 : Blo 511796 1296557 := bbase (se 3 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 1296557 = 486209) (by norm_num)
theorem B772277 : Blo 511796 772277 := bbase (se 5 (by rfl) ⟨36200, by rfl⟩ : syracuseStep 772277 = 72401) (by norm_num)
theorem B772301 : Blo 511796 772301 := bbase (se 3 (by rfl) ⟨144806, by rfl⟩ : syracuseStep 772301 = 289613) (by norm_num)
theorem B5556437 : Blo 511796 5556437 := bbase (se 7 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 5556437 = 130229) (by norm_num)
theorem B772325 : Blo 511796 772325 := bbase (se 4 (by rfl) ⟨72405, by rfl⟩ : syracuseStep 772325 = 144811) (by norm_num)
theorem B772349 : Blo 511796 772349 := bbase (se 3 (by rfl) ⟨144815, by rfl⟩ : syracuseStep 772349 = 289631) (by norm_num)
theorem B772373 : Blo 511796 772373 := bbase (se 6 (by rfl) ⟨18102, by rfl⟩ : syracuseStep 772373 = 36205) (by norm_num)
theorem B772397 : Blo 511796 772397 := bbase (se 3 (by rfl) ⟨144824, by rfl⟩ : syracuseStep 772397 = 289649) (by norm_num)
theorem B575797 : Blo 511796 575797 := bbase (se 5 (by rfl) ⟨26990, by rfl⟩ : syracuseStep 575797 = 53981) (by norm_num)
theorem B772421 : Blo 511796 772421 := bbase (se 4 (by rfl) ⟨72414, by rfl⟩ : syracuseStep 772421 = 144829) (by norm_num)
theorem B575833 : Blo 511796 575833 := bbase (se 2 (by rfl) ⟨215937, by rfl⟩ : syracuseStep 575833 = 431875) (by norm_num)
theorem B772445 : Blo 511796 772445 := bbase (se 3 (by rfl) ⟨144833, by rfl⟩ : syracuseStep 772445 = 289667) (by norm_num)
theorem B1296749 : Blo 511796 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B772469 : Blo 511796 772469 := bbase (se 5 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 772469 = 72419) (by norm_num)
theorem B575869 : Blo 511796 575869 := bbase (se 3 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 575869 = 215951) (by norm_num)
theorem B772493 : Blo 511796 772493 := bbase (se 3 (by rfl) ⟨144842, by rfl⟩ : syracuseStep 772493 = 289685) (by norm_num)
theorem B575905 : Blo 511796 575905 := bbase (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) (by norm_num)
theorem B772517 : Blo 511796 772517 := bbase (se 4 (by rfl) ⟨72423, by rfl⟩ : syracuseStep 772517 = 144847) (by norm_num)
theorem B772541 : Blo 511796 772541 := bbase (se 3 (by rfl) ⟨144851, by rfl⟩ : syracuseStep 772541 = 289703) (by norm_num)
theorem B575941 : Blo 511796 575941 := bbase (se 4 (by rfl) ⟨53994, by rfl⟩ : syracuseStep 575941 = 107989) (by norm_num)
theorem B772565 : Blo 511796 772565 := bbase (se 7 (by rfl) ⟨9053, by rfl⟩ : syracuseStep 772565 = 18107) (by norm_num)
theorem B575977 : Blo 511796 575977 := bbase (se 2 (by rfl) ⟨215991, by rfl⟩ : syracuseStep 575977 = 431983) (by norm_num)
theorem B772589 : Blo 511796 772589 := bbase (se 3 (by rfl) ⟨144860, by rfl⟩ : syracuseStep 772589 = 289721) (by norm_num)
theorem B4377077 : Blo 511796 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B772613 : Blo 511796 772613 := bbase (se 4 (by rfl) ⟨72432, by rfl⟩ : syracuseStep 772613 = 144865) (by norm_num)
theorem B576013 : Blo 511796 576013 := bbase (se 3 (by rfl) ⟨108002, by rfl⟩ : syracuseStep 576013 = 216005) (by norm_num)
theorem B772637 : Blo 511796 772637 := bbase (se 3 (by rfl) ⟨144869, by rfl⟩ : syracuseStep 772637 = 289739) (by norm_num)
theorem B576049 : Blo 511796 576049 := bbase (se 2 (by rfl) ⟨216018, by rfl⟩ : syracuseStep 576049 = 432037) (by norm_num)
theorem B772661 : Blo 511796 772661 := bbase (se 5 (by rfl) ⟨36218, by rfl⟩ : syracuseStep 772661 = 72437) (by norm_num)
theorem B772685 : Blo 511796 772685 := bbase (se 3 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 772685 = 289757) (by norm_num)
theorem B576085 : Blo 511796 576085 := bbase (se 8 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 576085 = 6751) (by norm_num)
theorem B772709 : Blo 511796 772709 := bbase (se 4 (by rfl) ⟨72441, by rfl⟩ : syracuseStep 772709 = 144883) (by norm_num)
theorem B576121 : Blo 511796 576121 := bbase (se 2 (by rfl) ⟨216045, by rfl⟩ : syracuseStep 576121 = 432091) (by norm_num)
theorem B772733 : Blo 511796 772733 := bbase (se 3 (by rfl) ⟨144887, by rfl⟩ : syracuseStep 772733 = 289775) (by norm_num)
theorem B772757 : Blo 511796 772757 := bbase (se 6 (by rfl) ⟨18111, by rfl⟩ : syracuseStep 772757 = 36223) (by norm_num)
theorem B576157 : Blo 511796 576157 := bbase (se 3 (by rfl) ⟨108029, by rfl⟩ : syracuseStep 576157 = 216059) (by norm_num)
theorem B772781 : Blo 511796 772781 := bbase (se 3 (by rfl) ⟨144896, by rfl⟩ : syracuseStep 772781 = 289793) (by norm_num)
theorem B576193 : Blo 511796 576193 := bbase (se 2 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 576193 = 432145) (by norm_num)
theorem B1297093 : Blo 511796 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B772805 : Blo 511796 772805 := bbase (se 4 (by rfl) ⟨72450, by rfl⟩ : syracuseStep 772805 = 144901) (by norm_num)
theorem B772829 : Blo 511796 772829 := bbase (se 3 (by rfl) ⟨144905, by rfl⟩ : syracuseStep 772829 = 289811) (by norm_num)
theorem B576229 : Blo 511796 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B1755877 : Blo 511796 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B772853 : Blo 511796 772853 := bbase (se 5 (by rfl) ⟨36227, by rfl⟩ : syracuseStep 772853 = 72455) (by norm_num)
theorem B576265 : Blo 511796 576265 := bbase (se 2 (by rfl) ⟨216099, by rfl⟩ : syracuseStep 576265 = 432199) (by norm_num)
theorem B772877 : Blo 511796 772877 := bbase (se 3 (by rfl) ⟨144914, by rfl⟩ : syracuseStep 772877 = 289829) (by norm_num)
theorem B1100557 : Blo 511796 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B772901 : Blo 511796 772901 := bbase (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) (by norm_num)
theorem B576301 : Blo 511796 576301 := bbase (se 3 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 576301 = 216113) (by norm_num)
theorem B1297205 : Blo 511796 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B772925 : Blo 511796 772925 := bbase (se 3 (by rfl) ⟨144923, by rfl⟩ : syracuseStep 772925 = 289847) (by norm_num)
theorem B576337 : Blo 511796 576337 := bbase (se 2 (by rfl) ⟨216126, by rfl⟩ : syracuseStep 576337 = 432253) (by norm_num)
theorem B772949 : Blo 511796 772949 := bbase (se 9 (by rfl) ⟨2264, by rfl⟩ : syracuseStep 772949 = 4529) (by norm_num)
theorem B772973 : Blo 511796 772973 := bbase (se 3 (by rfl) ⟨144932, by rfl⟩ : syracuseStep 772973 = 289865) (by norm_num)
theorem B576373 : Blo 511796 576373 := bbase (se 5 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 576373 = 54035) (by norm_num)
theorem B772997 : Blo 511796 772997 := bbase (se 4 (by rfl) ⟨72468, by rfl⟩ : syracuseStep 772997 = 144937) (by norm_num)
theorem B576409 : Blo 511796 576409 := bbase (se 2 (by rfl) ⟨216153, by rfl⟩ : syracuseStep 576409 = 432307) (by norm_num)
theorem B773021 : Blo 511796 773021 := bbase (se 3 (by rfl) ⟨144941, by rfl⟩ : syracuseStep 773021 = 289883) (by norm_num)
theorem B2608037 : Blo 511796 2608037 := bbase (se 4 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 2608037 = 489007) (by norm_num)
theorem B773045 : Blo 511796 773045 := bbase (se 5 (by rfl) ⟨36236, by rfl⟩ : syracuseStep 773045 = 72473) (by norm_num)
theorem B576445 : Blo 511796 576445 := bbase (se 3 (by rfl) ⟨108083, by rfl⟩ : syracuseStep 576445 = 216167) (by norm_num)
theorem B773069 : Blo 511796 773069 := bbase (se 3 (by rfl) ⟨144950, by rfl⟩ : syracuseStep 773069 = 289901) (by norm_num)
theorem B576481 : Blo 511796 576481 := bbase (se 2 (by rfl) ⟨216180, by rfl⟩ : syracuseStep 576481 = 432361) (by norm_num)
theorem B773093 : Blo 511796 773093 := bbase (se 4 (by rfl) ⟨72477, by rfl⟩ : syracuseStep 773093 = 144955) (by norm_num)
theorem B1297397 : Blo 511796 1297397 := bbase (se 5 (by rfl) ⟨60815, by rfl⟩ : syracuseStep 1297397 = 121631) (by norm_num)
theorem B773117 : Blo 511796 773117 := bbase (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) (by norm_num)
theorem B576517 : Blo 511796 576517 := bbase (se 4 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 576517 = 108097) (by norm_num)
theorem B773141 : Blo 511796 773141 := bbase (se 6 (by rfl) ⟨18120, by rfl⟩ : syracuseStep 773141 = 36241) (by norm_num)
theorem B576553 : Blo 511796 576553 := bbase (se 2 (by rfl) ⟨216207, by rfl⟩ : syracuseStep 576553 = 432415) (by norm_num)
theorem B773165 : Blo 511796 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B773189 : Blo 511796 773189 := bbase (se 4 (by rfl) ⟨72486, by rfl⟩ : syracuseStep 773189 = 144973) (by norm_num)
theorem B576589 : Blo 511796 576589 := bbase (se 3 (by rfl) ⟨108110, by rfl⟩ : syracuseStep 576589 = 216221) (by norm_num)
theorem B773213 : Blo 511796 773213 := bbase (se 3 (by rfl) ⟨144977, by rfl⟩ : syracuseStep 773213 = 289955) (by norm_num)
theorem B1952869 : Blo 511796 1952869 := bbase (se 4 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 1952869 = 366163) (by norm_num)
theorem B576625 : Blo 511796 576625 := bbase (se 2 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 576625 = 432469) (by norm_num)
theorem B773237 : Blo 511796 773237 := bbase (se 5 (by rfl) ⟨36245, by rfl⟩ : syracuseStep 773237 = 72491) (by norm_num)
theorem B773261 : Blo 511796 773261 := bbase (se 3 (by rfl) ⟨144986, by rfl⟩ : syracuseStep 773261 = 289973) (by norm_num)
theorem B576661 : Blo 511796 576661 := bbase (se 6 (by rfl) ⟨13515, by rfl⟩ : syracuseStep 576661 = 27031) (by norm_num)
theorem B773285 : Blo 511796 773285 := bbase (se 4 (by rfl) ⟨72495, by rfl⟩ : syracuseStep 773285 = 144991) (by norm_num)
theorem B576697 : Blo 511796 576697 := bbase (se 2 (by rfl) ⟨216261, by rfl⟩ : syracuseStep 576697 = 432523) (by norm_num)
theorem B773309 : Blo 511796 773309 := bbase (se 3 (by rfl) ⟨144995, by rfl⟩ : syracuseStep 773309 = 289991) (by norm_num)
theorem B773333 : Blo 511796 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B576733 : Blo 511796 576733 := bbase (se 3 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 576733 = 216275) (by norm_num)
theorem B1232101 : Blo 511796 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B773357 : Blo 511796 773357 := bbase (se 3 (by rfl) ⟨145004, by rfl⟩ : syracuseStep 773357 = 290009) (by norm_num)
theorem B1101053 : Blo 511796 1101053 := bbase (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) (by norm_num)
theorem B576769 : Blo 511796 576769 := bbase (se 2 (by rfl) ⟨216288, by rfl⟩ : syracuseStep 576769 = 432577) (by norm_num)
theorem B1461509 : Blo 511796 1461509 := bbase (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) (by norm_num)
theorem B773381 : Blo 511796 773381 := bbase (se 4 (by rfl) ⟨72504, by rfl⟩ : syracuseStep 773381 = 145009) (by norm_num)
theorem B773405 : Blo 511796 773405 := bbase (se 3 (by rfl) ⟨145013, by rfl⟩ : syracuseStep 773405 = 290027) (by norm_num)
theorem B576805 : Blo 511796 576805 := bbase (se 4 (by rfl) ⟨54075, by rfl⟩ : syracuseStep 576805 = 108151) (by norm_num)
theorem B773429 : Blo 511796 773429 := bbase (se 5 (by rfl) ⟨36254, by rfl⟩ : syracuseStep 773429 = 72509) (by norm_num)
theorem B576841 : Blo 511796 576841 := bbase (se 2 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 576841 = 432631) (by norm_num)
theorem B1297741 : Blo 511796 1297741 := bbase (se 3 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 1297741 = 486653) (by norm_num)
theorem B773453 : Blo 511796 773453 := bbase (se 3 (by rfl) ⟨145022, by rfl⟩ : syracuseStep 773453 = 290045) (by norm_num)
theorem B773477 : Blo 511796 773477 := bbase (se 4 (by rfl) ⟨72513, by rfl⟩ : syracuseStep 773477 = 145027) (by norm_num)
theorem B576877 : Blo 511796 576877 := bbase (se 3 (by rfl) ⟨108164, by rfl⟩ : syracuseStep 576877 = 216329) (by norm_num)
theorem B773501 : Blo 511796 773501 := bbase (se 3 (by rfl) ⟨145031, by rfl⟩ : syracuseStep 773501 = 290063) (by norm_num)
theorem B576913 : Blo 511796 576913 := bbase (se 2 (by rfl) ⟨216342, by rfl⟩ : syracuseStep 576913 = 432685) (by norm_num)
theorem B1953173 : Blo 511796 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B773525 : Blo 511796 773525 := bbase (se 6 (by rfl) ⟨18129, by rfl⟩ : syracuseStep 773525 = 36259) (by norm_num)
theorem B773549 : Blo 511796 773549 := bbase (se 3 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 773549 = 290081) (by norm_num)
theorem B576949 : Blo 511796 576949 := bbase (se 5 (by rfl) ⟨27044, by rfl⟩ : syracuseStep 576949 = 54089) (by norm_num)
theorem B1297853 : Blo 511796 1297853 := bbase (se 3 (by rfl) ⟨243347, by rfl⟩ : syracuseStep 1297853 = 486695) (by norm_num)
theorem B773573 : Blo 511796 773573 := bbase (se 4 (by rfl) ⟨72522, by rfl⟩ : syracuseStep 773573 = 145045) (by norm_num)
theorem B576985 : Blo 511796 576985 := bbase (se 2 (by rfl) ⟨216369, by rfl⟩ : syracuseStep 576985 = 432739) (by norm_num)
theorem B773597 : Blo 511796 773597 := bbase (se 3 (by rfl) ⟨145049, by rfl⟩ : syracuseStep 773597 = 290099) (by norm_num)
theorem B773621 : Blo 511796 773621 := bbase (se 5 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 773621 = 72527) (by norm_num)
theorem B577021 : Blo 511796 577021 := bbase (se 3 (by rfl) ⟨108191, by rfl⟩ : syracuseStep 577021 = 216383) (by norm_num)
theorem B773645 : Blo 511796 773645 := bbase (se 3 (by rfl) ⟨145058, by rfl⟩ : syracuseStep 773645 = 290117) (by norm_num)
theorem B577057 : Blo 511796 577057 := bbase (se 2 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 577057 = 432793) (by norm_num)
theorem B773669 : Blo 511796 773669 := bbase (se 4 (by rfl) ⟨72531, by rfl⟩ : syracuseStep 773669 = 145063) (by norm_num)
theorem B773693 : Blo 511796 773693 := bbase (se 3 (by rfl) ⟨145067, by rfl⟩ : syracuseStep 773693 = 290135) (by norm_num)
theorem B577093 : Blo 511796 577093 := bbase (se 4 (by rfl) ⟨54102, by rfl⟩ : syracuseStep 577093 = 108205) (by norm_num)
theorem B577129 : Blo 511796 577129 := bbase (se 2 (by rfl) ⟨216423, by rfl⟩ : syracuseStep 577129 = 432847) (by norm_num)
theorem B1298045 : Blo 511796 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B577165 : Blo 511796 577165 := bbase (se 3 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 577165 = 216437) (by norm_num)
theorem B577201 : Blo 511796 577201 := bbase (se 2 (by rfl) ⟨216450, by rfl⟩ : syracuseStep 577201 = 432901) (by norm_num)
theorem B577237 : Blo 511796 577237 := bbase (se 7 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 577237 = 13529) (by norm_num)
theorem B577273 : Blo 511796 577273 := bbase (se 2 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 577273 = 432955) (by norm_num)
theorem B577309 : Blo 511796 577309 := bbase (se 3 (by rfl) ⟨108245, by rfl⟩ : syracuseStep 577309 = 216491) (by norm_num)
theorem B577345 : Blo 511796 577345 := bbase (se 2 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 577345 = 433009) (by norm_num)
theorem B577381 : Blo 511796 577381 := bbase (se 4 (by rfl) ⟨54129, by rfl⟩ : syracuseStep 577381 = 108259) (by norm_num)
theorem B1232765 : Blo 511796 1232765 := bbase (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) (by norm_num)
theorem B577417 : Blo 511796 577417 := bbase (se 2 (by rfl) ⟨216531, by rfl⟩ : syracuseStep 577417 = 433063) (by norm_num)
theorem B577453 : Blo 511796 577453 := bbase (se 3 (by rfl) ⟨108272, by rfl⟩ : syracuseStep 577453 = 216545) (by norm_num)
theorem B577489 : Blo 511796 577489 := bbase (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) (by norm_num)
theorem B1298389 : Blo 511796 1298389 := bbase (se 7 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 1298389 = 30431) (by norm_num)
theorem B741349 : Blo 511796 741349 := bbase (se 4 (by rfl) ⟨69501, by rfl⟩ : syracuseStep 741349 = 139003) (by norm_num)
theorem B577525 : Blo 511796 577525 := bbase (se 5 (by rfl) ⟨27071, by rfl⟩ : syracuseStep 577525 = 54143) (by norm_num)
theorem B577561 : Blo 511796 577561 := bbase (se 2 (by rfl) ⟨216585, by rfl⟩ : syracuseStep 577561 = 433171) (by norm_num)
theorem B577597 : Blo 511796 577597 := bbase (se 3 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 577597 = 216599) (by norm_num)
theorem B1298501 : Blo 511796 1298501 := bbase (se 4 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 1298501 = 243469) (by norm_num)
theorem B577633 : Blo 511796 577633 := bbase (se 2 (by rfl) ⟨216612, by rfl⟩ : syracuseStep 577633 = 433225) (by norm_num)
theorem B577669 : Blo 511796 577669 := bbase (se 4 (by rfl) ⟨54156, by rfl⟩ : syracuseStep 577669 = 108313) (by norm_num)
theorem B1233053 : Blo 511796 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B577705 : Blo 511796 577705 := bbase (se 2 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 577705 = 433279) (by norm_num)
theorem B2609333 : Blo 511796 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B577741 : Blo 511796 577741 := bbase (se 3 (by rfl) ⟨108326, by rfl⟩ : syracuseStep 577741 = 216653) (by norm_num)
theorem B577777 : Blo 511796 577777 := bbase (se 2 (by rfl) ⟨216666, by rfl⟩ : syracuseStep 577777 = 433333) (by norm_num)
theorem B1298693 : Blo 511796 1298693 := bbase (se 4 (by rfl) ⟨121752, by rfl⟩ : syracuseStep 1298693 = 243505) (by norm_num)
theorem B577813 : Blo 511796 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B577849 : Blo 511796 577849 := bbase (se 2 (by rfl) ⟨216693, by rfl⟩ : syracuseStep 577849 = 433387) (by norm_num)
theorem B577885 : Blo 511796 577885 := bbase (se 3 (by rfl) ⟨108353, by rfl⟩ : syracuseStep 577885 = 216707) (by norm_num)
theorem B577921 : Blo 511796 577921 := bbase (se 2 (by rfl) ⟨216720, by rfl⟩ : syracuseStep 577921 = 433441) (by norm_num)
theorem B1462693 : Blo 511796 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B577957 : Blo 511796 577957 := bbase (se 4 (by rfl) ⟨54183, by rfl⟩ : syracuseStep 577957 = 108367) (by norm_num)
theorem B577993 : Blo 511796 577993 := bbase (se 2 (by rfl) ⟨216747, by rfl⟩ : syracuseStep 577993 = 433495) (by norm_num)
theorem B938461 : Blo 511796 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B578029 : Blo 511796 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B2118149 : Blo 511796 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B578065 : Blo 511796 578065 := bbase (se 2 (by rfl) ⟨216774, by rfl⟩ : syracuseStep 578065 = 433549) (by norm_num)
theorem B578101 : Blo 511796 578101 := bbase (se 5 (by rfl) ⟨27098, by rfl⟩ : syracuseStep 578101 = 54197) (by norm_num)
theorem B1462853 : Blo 511796 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B578137 : Blo 511796 578137 := bbase (se 2 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 578137 = 433603) (by norm_num)
theorem B1299037 : Blo 511796 1299037 := bbase (se 3 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 1299037 = 487139) (by norm_num)
theorem B578173 : Blo 511796 578173 := bbase (se 3 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 578173 = 216815) (by norm_num)
theorem B578209 : Blo 511796 578209 := bbase (se 2 (by rfl) ⟨216828, by rfl⟩ : syracuseStep 578209 = 433657) (by norm_num)
theorem B938693 : Blo 511796 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B578245 : Blo 511796 578245 := bbase (se 4 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 578245 = 108421) (by norm_num)
theorem B1299149 : Blo 511796 1299149 := bbase (se 3 (by rfl) ⟨243590, by rfl⟩ : syracuseStep 1299149 = 487181) (by norm_num)
theorem B578281 : Blo 511796 578281 := bbase (se 2 (by rfl) ⟨216855, by rfl⟩ : syracuseStep 578281 = 433711) (by norm_num)
theorem B2249461 : Blo 511796 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B578317 : Blo 511796 578317 := bbase (se 3 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 578317 = 216869) (by norm_num)
theorem B578353 : Blo 511796 578353 := bbase (se 2 (by rfl) ⟨216882, by rfl⟩ : syracuseStep 578353 = 433765) (by norm_num)
theorem B1463093 : Blo 511796 1463093 := bbase (se 5 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 1463093 = 137165) (by norm_num)
theorem B578389 : Blo 511796 578389 := bbase (se 9 (by rfl) ⟨1694, by rfl⟩ : syracuseStep 578389 = 3389) (by norm_num)
theorem B3298133 : Blo 511796 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B578425 : Blo 511796 578425 := bbase (se 2 (by rfl) ⟨216909, by rfl⟩ : syracuseStep 578425 = 433819) (by norm_num)
theorem B1299341 : Blo 511796 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B578461 : Blo 511796 578461 := bbase (se 3 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 578461 = 216923) (by norm_num)
theorem B578497 : Blo 511796 578497 := bbase (se 2 (by rfl) ⟨216936, by rfl⟩ : syracuseStep 578497 = 433873) (by norm_num)
theorem B578533 : Blo 511796 578533 := bbase (se 4 (by rfl) ⟨54237, by rfl⟩ : syracuseStep 578533 = 108475) (by norm_num)
theorem B1463285 : Blo 511796 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B578569 : Blo 511796 578569 := bbase (se 2 (by rfl) ⟨216963, by rfl⟩ : syracuseStep 578569 = 433927) (by norm_num)
theorem B578605 : Blo 511796 578605 := bbase (se 3 (by rfl) ⟨108488, by rfl⟩ : syracuseStep 578605 = 216977) (by norm_num)
theorem B578641 : Blo 511796 578641 := bbase (se 2 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 578641 = 433981) (by norm_num)
theorem B1168469 : Blo 511796 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B578677 : Blo 511796 578677 := bbase (se 5 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 578677 = 54251) (by norm_num)
theorem B971909 : Blo 511796 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B578713 : Blo 511796 578713 := bbase (se 2 (by rfl) ⟨217017, by rfl⟩ : syracuseStep 578713 = 434035) (by norm_num)
theorem B578749 : Blo 511796 578749 := bbase (se 3 (by rfl) ⟨108515, by rfl⟩ : syracuseStep 578749 = 217031) (by norm_num)
theorem B578785 : Blo 511796 578785 := bbase (se 2 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 578785 = 434089) (by norm_num)
theorem B1299685 : Blo 511796 1299685 := bbase (se 4 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 1299685 = 243691) (by norm_num)
theorem B578821 : Blo 511796 578821 := bbase (se 4 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 578821 = 108529) (by norm_num)
theorem B578857 : Blo 511796 578857 := bbase (se 2 (by rfl) ⟨217071, by rfl⟩ : syracuseStep 578857 = 434143) (by norm_num)
theorem B578893 : Blo 511796 578893 := bbase (se 3 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 578893 = 217085) (by norm_num)
theorem B1299797 : Blo 511796 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B578929 : Blo 511796 578929 := bbase (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) (by norm_num)
theorem B578965 : Blo 511796 578965 := bbase (se 6 (by rfl) ⟨13569, by rfl⟩ : syracuseStep 578965 = 27139) (by norm_num)
theorem B1168813 : Blo 511796 1168813 := bbase (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) (by norm_num)
theorem B579001 : Blo 511796 579001 := bbase (se 2 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 579001 = 434251) (by norm_num)
theorem B2610629 : Blo 511796 2610629 := bbase (se 4 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 2610629 = 489493) (by norm_num)
theorem B1955285 : Blo 511796 1955285 := bbase (se 7 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 1955285 = 45827) (by norm_num)
theorem B579037 : Blo 511796 579037 := bbase (se 3 (by rfl) ⟨108569, by rfl⟩ : syracuseStep 579037 = 217139) (by norm_num)
theorem B579073 : Blo 511796 579073 := bbase (se 2 (by rfl) ⟨217152, by rfl⟩ : syracuseStep 579073 = 434305) (by norm_num)
theorem B1299989 : Blo 511796 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B579109 : Blo 511796 579109 := bbase (se 4 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 579109 = 108583) (by norm_num)
theorem B579145 : Blo 511796 579145 := bbase (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) (by norm_num)
theorem B579181 : Blo 511796 579181 := bbase (se 3 (by rfl) ⟨108596, by rfl⟩ : syracuseStep 579181 = 217193) (by norm_num)
theorem B579217 : Blo 511796 579217 := bbase (se 2 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 579217 = 434413) (by norm_num)
theorem B579253 : Blo 511796 579253 := bbase (se 5 (by rfl) ⟨27152, by rfl⟩ : syracuseStep 579253 = 54305) (by norm_num)
theorem B1038037 : Blo 511796 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B579289 : Blo 511796 579289 := bbase (se 2 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 579289 = 434467) (by norm_num)
theorem B546545 : Blo 511796 546545 := bbase (se 2 (by rfl) ⟨204954, by rfl⟩ : syracuseStep 546545 = 409909) (by norm_num)
theorem B1955573 : Blo 511796 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B579325 : Blo 511796 579325 := bbase (se 3 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 579325 = 217247) (by norm_num)
theorem B579361 : Blo 511796 579361 := bbase (se 2 (by rfl) ⟨217260, by rfl⟩ : syracuseStep 579361 = 434521) (by norm_num)
theorem B579397 : Blo 511796 579397 := bbase (se 4 (by rfl) ⟨54318, by rfl⟩ : syracuseStep 579397 = 108637) (by norm_num)
theorem B579433 : Blo 511796 579433 := bbase (se 2 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 579433 = 434575) (by norm_num)
theorem B1300333 : Blo 511796 1300333 := bbase (se 3 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 1300333 = 487625) (by norm_num)
theorem B972661 : Blo 511796 972661 := bbase (se 5 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 972661 = 91187) (by norm_num)
theorem B579469 : Blo 511796 579469 := bbase (se 3 (by rfl) ⟨108650, by rfl⟩ : syracuseStep 579469 = 217301) (by norm_num)
theorem B546733 : Blo 511796 546733 := bbase (se 3 (by rfl) ⟨102512, by rfl⟩ : syracuseStep 546733 = 205025) (by norm_num)
theorem B579505 : Blo 511796 579505 := bbase (se 2 (by rfl) ⟨217314, by rfl⟩ : syracuseStep 579505 = 434629) (by norm_num)
theorem B1464277 : Blo 511796 1464277 := bbase (se 7 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 1464277 = 34319) (by norm_num)
theorem B579541 : Blo 511796 579541 := bbase (se 7 (by rfl) ⟨6791, by rfl⟩ : syracuseStep 579541 = 13583) (by norm_num)
theorem B1300445 : Blo 511796 1300445 := bbase (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) (by norm_num)
theorem B579577 : Blo 511796 579577 := bbase (se 2 (by rfl) ⟨217341, by rfl⟩ : syracuseStep 579577 = 434683) (by norm_num)
theorem B972805 : Blo 511796 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B579613 : Blo 511796 579613 := bbase (se 3 (by rfl) ⟨108677, by rfl⟩ : syracuseStep 579613 = 217355) (by norm_num)
theorem B579649 : Blo 511796 579649 := bbase (se 2 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 579649 = 434737) (by norm_num)
theorem B546917 : Blo 511796 546917 := bbase (se 4 (by rfl) ⟨51273, by rfl⟩ : syracuseStep 546917 = 102547) (by norm_num)
theorem B2349157 : Blo 511796 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B579685 : Blo 511796 579685 := bbase (se 4 (by rfl) ⟨54345, by rfl⟩ : syracuseStep 579685 = 108691) (by norm_num)
theorem B579721 : Blo 511796 579721 := bbase (se 2 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 579721 = 434791) (by norm_num)
theorem B1300637 : Blo 511796 1300637 := bbase (se 3 (by rfl) ⟨243869, by rfl⟩ : syracuseStep 1300637 = 487739) (by norm_num)
theorem B1235101 : Blo 511796 1235101 := bbase (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) (by norm_num)
theorem B972965 : Blo 511796 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B579757 : Blo 511796 579757 := bbase (se 3 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 579757 = 217409) (by norm_num)
theorem B579793 : Blo 511796 579793 := bbase (se 2 (by rfl) ⟨217422, by rfl⟩ : syracuseStep 579793 = 434845) (by norm_num)
theorem B579829 : Blo 511796 579829 := bbase (se 5 (by rfl) ⟨27179, by rfl⟩ : syracuseStep 579829 = 54359) (by norm_num)
theorem B579865 : Blo 511796 579865 := bbase (se 2 (by rfl) ⟨217449, by rfl⟩ : syracuseStep 579865 = 434899) (by norm_num)
theorem B973109 : Blo 511796 973109 := bbase (se 5 (by rfl) ⟨45614, by rfl⟩ : syracuseStep 973109 = 91229) (by norm_num)
theorem B579901 : Blo 511796 579901 := bbase (se 3 (by rfl) ⟨108731, by rfl⟩ : syracuseStep 579901 = 217463) (by norm_num)
theorem B579937 : Blo 511796 579937 := bbase (se 2 (by rfl) ⟨217476, by rfl⟩ : syracuseStep 579937 = 434953) (by norm_num)
theorem B579973 : Blo 511796 579973 := bbase (se 4 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 579973 = 108745) (by norm_num)
theorem B580009 : Blo 511796 580009 := bbase (se 2 (by rfl) ⟨217503, by rfl⟩ : syracuseStep 580009 = 435007) (by norm_num)
theorem B580045 : Blo 511796 580045 := bbase (se 3 (by rfl) ⟨108758, by rfl⟩ : syracuseStep 580045 = 217517) (by norm_num)
theorem B580081 : Blo 511796 580081 := bbase (se 2 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 580081 = 435061) (by norm_num)
theorem B1300981 : Blo 511796 1300981 := bbase (se 5 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 1300981 = 121967) (by norm_num)
theorem B580117 : Blo 511796 580117 := bbase (se 6 (by rfl) ⟨13596, by rfl⟩ : syracuseStep 580117 = 27193) (by norm_num)
theorem B1858085 : Blo 511796 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B580153 : Blo 511796 580153 := bbase (se 2 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 580153 = 435115) (by norm_num)
theorem B973397 : Blo 511796 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B580189 : Blo 511796 580189 := bbase (se 3 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 580189 = 217571) (by norm_num)
theorem B1301093 : Blo 511796 1301093 := bbase (se 4 (by rfl) ⟨121977, by rfl⟩ : syracuseStep 1301093 = 243955) (by norm_num)
theorem B580225 : Blo 511796 580225 := bbase (se 2 (by rfl) ⟨217584, by rfl⟩ : syracuseStep 580225 = 435169) (by norm_num)
theorem B580261 : Blo 511796 580261 := bbase (se 4 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 580261 = 108799) (by norm_num)
theorem B973549 : Blo 511796 973549 := bbase (se 3 (by rfl) ⟨182540, by rfl⟩ : syracuseStep 973549 = 365081) (by norm_num)
theorem B1301285 : Blo 511796 1301285 := bbase (se 4 (by rfl) ⟨121995, by rfl⟩ : syracuseStep 1301285 = 243991) (by norm_num)
theorem B1858373 : Blo 511796 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B547669 : Blo 511796 547669 := bbase (se 9 (by rfl) ⟨1604, by rfl⟩ : syracuseStep 547669 = 3209) (by norm_num)
theorem B1956757 : Blo 511796 1956757 := bbase (se 6 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 1956757 = 91723) (by norm_num)
theorem B547741 : Blo 511796 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B973853 : Blo 511796 973853 := bbase (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) (by norm_num)
theorem B1465381 : Blo 511796 1465381 := bbase (se 4 (by rfl) ⟨137379, by rfl⟩ : syracuseStep 1465381 = 274759) (by norm_num)
theorem B547921 : Blo 511796 547921 := bbase (se 2 (by rfl) ⟨205470, by rfl⟩ : syracuseStep 547921 = 410941) (by norm_num)
theorem B1301629 : Blo 511796 1301629 := bbase (se 3 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 1301629 = 488111) (by norm_num)
theorem B1727621 : Blo 511796 1727621 := bbase (se 4 (by rfl) ⟨161964, by rfl⟩ : syracuseStep 1727621 = 323929) (by norm_num)
theorem B1957061 : Blo 511796 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B2186453 : Blo 511796 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B1301741 : Blo 511796 1301741 := bbase (se 3 (by rfl) ⟨244076, by rfl⟩ : syracuseStep 1301741 = 488153) (by norm_num)
theorem B1760501 : Blo 511796 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1301933 : Blo 511796 1301933 := bbase (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) (by norm_num)
theorem B875981 : Blo 511796 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B548365 : Blo 511796 548365 := bbase (se 3 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 548365 = 205637) (by norm_num)
theorem B876077 : Blo 511796 876077 := bbase (se 3 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 876077 = 328529) (by norm_num)
theorem B1728053 : Blo 511796 1728053 := bbase (se 5 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 1728053 = 162005) (by norm_num)
theorem B548489 : Blo 511796 548489 := bbase (se 2 (by rfl) ⟨205683, by rfl⟩ : syracuseStep 548489 = 411367) (by norm_num)
theorem B876221 : Blo 511796 876221 := bbase (se 3 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 876221 = 328583) (by norm_num)
theorem B679657 : Blo 511796 679657 := bbase (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) (by norm_num)
theorem B1302277 : Blo 511796 1302277 := bbase (se 4 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 1302277 = 244177) (by norm_num)
theorem B974605 : Blo 511796 974605 := bbase (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) (by norm_num)
theorem B1302389 : Blo 511796 1302389 := bbase (se 5 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 1302389 = 122099) (by norm_num)
theorem B2088821 : Blo 511796 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B548741 : Blo 511796 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B974749 : Blo 511796 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B2088917 : Blo 511796 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B1728485 : Blo 511796 1728485 := bbase (se 4 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 1728485 = 324091) (by norm_num)
theorem B1564645 : Blo 511796 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B778261 : Blo 511796 778261 := bbase (se 6 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 778261 = 36481) (by norm_num)
theorem B1302581 : Blo 511796 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B974909 : Blo 511796 974909 := bbase (se 3 (by rfl) ⟨182795, by rfl⟩ : syracuseStep 974909 = 365591) (by norm_num)
theorem B1564741 : Blo 511796 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B778333 : Blo 511796 778333 := bbase (se 3 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 778333 = 291875) (by norm_num)
theorem B876637 : Blo 511796 876637 := bbase (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) (by norm_num)
theorem B2384005 : Blo 511796 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B2187445 : Blo 511796 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B975053 : Blo 511796 975053 := bbase (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) (by norm_num)
theorem B549185 : Blo 511796 549185 := bbase (se 2 (by rfl) ⟨205944, by rfl⟩ : syracuseStep 549185 = 411889) (by norm_num)
theorem B1302925 : Blo 511796 1302925 := bbase (se 3 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 1302925 = 488597) (by norm_num)
theorem B1728917 : Blo 511796 1728917 := bbase (se 6 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 1728917 = 81043) (by norm_num)
theorem B975341 : Blo 511796 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B1237493 : Blo 511796 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B1303037 : Blo 511796 1303037 := bbase (se 3 (by rfl) ⟨244319, by rfl⟩ : syracuseStep 1303037 = 488639) (by norm_num)
theorem B1466885 : Blo 511796 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B549433 : Blo 511796 549433 := bbase (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) (by norm_num)
theorem B614989 : Blo 511796 614989 := bbase (se 3 (by rfl) ⟨115310, by rfl⟩ : syracuseStep 614989 = 230621) (by norm_num)
theorem B647777 : Blo 511796 647777 := bbase (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) (by norm_num)
theorem B615017 : Blo 511796 615017 := bbase (se 2 (by rfl) ⟨230631, by rfl⟩ : syracuseStep 615017 = 461263) (by norm_num)
theorem B3302005 : Blo 511796 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B975493 : Blo 511796 975493 := bbase (se 4 (by rfl) ⟨91452, by rfl⟩ : syracuseStep 975493 = 182905) (by norm_num)
theorem B1237637 : Blo 511796 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B647833 : Blo 511796 647833 := bbase (se 2 (by rfl) ⟨242937, by rfl⟩ : syracuseStep 647833 = 485875) (by norm_num)
theorem B1303229 : Blo 511796 1303229 := bbase (se 3 (by rfl) ⟨244355, by rfl⟩ : syracuseStep 1303229 = 488711) (by norm_num)
theorem B647929 : Blo 511796 647929 := bbase (se 2 (by rfl) ⟨242973, by rfl⟩ : syracuseStep 647929 = 485947) (by norm_num)
theorem B615205 : Blo 511796 615205 := bbase (se 4 (by rfl) ⟨57675, by rfl⟩ : syracuseStep 615205 = 115351) (by norm_num)
theorem B1729349 : Blo 511796 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B615325 : Blo 511796 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B648101 : Blo 511796 648101 := bbase (se 4 (by rfl) ⟨60759, by rfl⟩ : syracuseStep 648101 = 121519) (by norm_num)
theorem B975797 : Blo 511796 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B648157 : Blo 511796 648157 := bbase (se 3 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 648157 = 243059) (by norm_num)
theorem B549877 : Blo 511796 549877 := bbase (se 5 (by rfl) ⟨25775, by rfl⟩ : syracuseStep 549877 = 51551) (by norm_num)
theorem B1172501 : Blo 511796 1172501 := bbase (se 6 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 1172501 = 54961) (by norm_num)
theorem B1303573 : Blo 511796 1303573 := bbase (se 6 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 1303573 = 61105) (by norm_num)
theorem B549937 : Blo 511796 549937 := bbase (se 2 (by rfl) ⟨206226, by rfl⟩ : syracuseStep 549937 = 412453) (by norm_num)
theorem B648253 : Blo 511796 648253 := bbase (se 3 (by rfl) ⟨121547, by rfl⟩ : syracuseStep 648253 = 243095) (by norm_num)
theorem B1303685 : Blo 511796 1303685 := bbase (se 4 (by rfl) ⟨122220, by rfl⟩ : syracuseStep 1303685 = 244441) (by norm_num)
theorem B3892373 : Blo 511796 3892373 := bbase (se 6 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 3892373 = 182455) (by norm_num)
theorem B648425 : Blo 511796 648425 := bbase (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) (by norm_num)
theorem B1729781 : Blo 511796 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B779549 : Blo 511796 779549 := bbase (se 3 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 779549 = 292331) (by norm_num)
theorem B648481 : Blo 511796 648481 := bbase (se 2 (by rfl) ⟨243180, by rfl⟩ : syracuseStep 648481 = 486361) (by norm_num)
theorem B1303877 : Blo 511796 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B550253 : Blo 511796 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B648577 : Blo 511796 648577 := bbase (se 2 (by rfl) ⟨243216, by rfl⟩ : syracuseStep 648577 = 486433) (by norm_num)
theorem B1172965 : Blo 511796 1172965 := bbase (se 4 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 1172965 = 219931) (by norm_num)
theorem B648749 : Blo 511796 648749 := bbase (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) (by norm_num)
theorem B648805 : Blo 511796 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B1304221 : Blo 511796 1304221 := bbase (se 3 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 1304221 = 489083) (by norm_num)
theorem B1730213 : Blo 511796 1730213 := bbase (se 4 (by rfl) ⟨162207, by rfl⟩ : syracuseStep 1730213 = 324415) (by norm_num)
theorem B976549 : Blo 511796 976549 := bbase (se 4 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 976549 = 183103) (by norm_num)
theorem B648901 : Blo 511796 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B14804693 : Blo 511796 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B1304333 : Blo 511796 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B550697 : Blo 511796 550697 := bbase (se 2 (by rfl) ⟨206511, by rfl⟩ : syracuseStep 550697 = 413023) (by norm_num)
theorem B976693 : Blo 511796 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B550757 : Blo 511796 550757 := bbase (se 4 (by rfl) ⟨51633, by rfl⟩ : syracuseStep 550757 = 103267) (by norm_num)
theorem B649073 : Blo 511796 649073 := bbase (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) (by norm_num)
theorem B649129 : Blo 511796 649129 := bbase (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) (by norm_num)
theorem B1304525 : Blo 511796 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B976853 : Blo 511796 976853 := bbase (se 7 (by rfl) ⟨11447, by rfl⟩ : syracuseStep 976853 = 22895) (by norm_num)
theorem B649225 : Blo 511796 649225 := bbase (se 2 (by rfl) ⟨243459, by rfl⟩ : syracuseStep 649225 = 486919) (by norm_num)
theorem B1468469 : Blo 511796 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1730645 : Blo 511796 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B976997 : Blo 511796 976997 := bbase (se 4 (by rfl) ⟨91593, by rfl⟩ : syracuseStep 976997 = 183187) (by norm_num)
theorem B2091109 : Blo 511796 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B649397 : Blo 511796 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B649453 : Blo 511796 649453 := bbase (se 3 (by rfl) ⟨121772, by rfl⟩ : syracuseStep 649453 = 243545) (by norm_num)
theorem B2091253 : Blo 511796 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B1173797 : Blo 511796 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B1304869 : Blo 511796 1304869 := bbase (se 4 (by rfl) ⟨122331, by rfl⟩ : syracuseStep 1304869 = 244663) (by norm_num)
theorem B649549 : Blo 511796 649549 := bbase (se 3 (by rfl) ⟨121790, by rfl⟩ : syracuseStep 649549 = 243581) (by norm_num)
theorem B977285 : Blo 511796 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B1304981 : Blo 511796 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B1173941 : Blo 511796 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B616901 : Blo 511796 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B649721 : Blo 511796 649721 := bbase (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) (by norm_num)
theorem B1731077 : Blo 511796 1731077 := bbase (se 4 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 1731077 = 324577) (by norm_num)
theorem B977437 : Blo 511796 977437 := bbase (se 3 (by rfl) ⟨183269, by rfl⟩ : syracuseStep 977437 = 366539) (by norm_num)
theorem B649777 : Blo 511796 649777 := bbase (se 2 (by rfl) ⟨243666, by rfl⟩ : syracuseStep 649777 = 487333) (by norm_num)
theorem B1305173 : Blo 511796 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B649873 : Blo 511796 649873 := bbase (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) (by norm_num)
theorem B1174205 : Blo 511796 1174205 := bbase (se 3 (by rfl) ⟨220163, by rfl⟩ : syracuseStep 1174205 = 440327) (by norm_num)
theorem B879341 : Blo 511796 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B650045 : Blo 511796 650045 := bbase (se 3 (by rfl) ⟨121883, by rfl⟩ : syracuseStep 650045 = 243767) (by norm_num)
theorem B977741 : Blo 511796 977741 := bbase (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) (by norm_num)
theorem B650101 : Blo 511796 650101 := bbase (se 5 (by rfl) ⟨30473, by rfl⟩ : syracuseStep 650101 = 60947) (by norm_num)
theorem B4942741 : Blo 511796 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B584621 : Blo 511796 584621 := bbase (se 3 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 584621 = 219233) (by norm_num)
theorem B1305517 : Blo 511796 1305517 := bbase (se 3 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 1305517 = 489569) (by norm_num)
theorem B1731509 : Blo 511796 1731509 := bbase (se 5 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 1731509 = 162329) (by norm_num)
theorem B1043389 : Blo 511796 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B650197 : Blo 511796 650197 := bbase (se 7 (by rfl) ⟨7619, by rfl⟩ : syracuseStep 650197 = 15239) (by norm_num)
theorem B879581 : Blo 511796 879581 := bbase (se 3 (by rfl) ⟨164921, by rfl⟩ : syracuseStep 879581 = 329843) (by norm_num)
theorem B519229 : Blo 511796 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B617593 : Blo 511796 617593 := bbase (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) (by norm_num)
theorem B650369 : Blo 511796 650369 := bbase (se 2 (by rfl) ⟨243888, by rfl⟩ : syracuseStep 650369 = 487777) (by norm_num)
theorem B650425 : Blo 511796 650425 := bbase (se 2 (by rfl) ⟨243909, by rfl⟩ : syracuseStep 650425 = 487819) (by norm_num)
theorem B617689 : Blo 511796 617689 := bbase (se 2 (by rfl) ⟨231633, by rfl⟩ : syracuseStep 617689 = 463267) (by norm_num)
theorem B650521 : Blo 511796 650521 := bbase (se 2 (by rfl) ⟨243945, by rfl⟩ : syracuseStep 650521 = 487891) (by norm_num)
theorem B519481 : Blo 511796 519481 := bbase (se 2 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 519481 = 389611) (by norm_num)
theorem B781669 : Blo 511796 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B1731941 : Blo 511796 1731941 := bbase (se 4 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 1731941 = 324739) (by norm_num)
theorem B781733 : Blo 511796 781733 := bbase (se 4 (by rfl) ⟨73287, by rfl⟩ : syracuseStep 781733 = 146575) (by norm_num)
theorem B650693 : Blo 511796 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B1174981 : Blo 511796 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B749029 : Blo 511796 749029 := bbase (se 4 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 749029 = 140443) (by norm_num)
theorem B650749 : Blo 511796 650749 := bbase (se 3 (by rfl) ⟨122015, by rfl⟩ : syracuseStep 650749 = 244031) (by norm_num)
theorem B880141 : Blo 511796 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B2780725 : Blo 511796 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B978493 : Blo 511796 978493 := bbase (se 3 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 978493 = 366935) (by norm_num)
theorem B650845 : Blo 511796 650845 := bbase (se 3 (by rfl) ⟨122033, by rfl⟩ : syracuseStep 650845 = 244067) (by norm_num)
theorem B978637 : Blo 511796 978637 := bbase (se 3 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 978637 = 366989) (by norm_num)
theorem B651017 : Blo 511796 651017 := bbase (se 2 (by rfl) ⟨244131, by rfl⟩ : syracuseStep 651017 = 488263) (by norm_num)
theorem B1732373 : Blo 511796 1732373 := bbase (se 6 (by rfl) ⟨40602, by rfl⟩ : syracuseStep 1732373 = 81205) (by norm_num)
theorem B651073 : Blo 511796 651073 := bbase (se 2 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 651073 = 488305) (by norm_num)
theorem B978797 : Blo 511796 978797 := bbase (se 3 (by rfl) ⟨183524, by rfl⟩ : syracuseStep 978797 = 367049) (by norm_num)
theorem B651169 : Blo 511796 651169 := bbase (se 2 (by rfl) ⟨244188, by rfl⟩ : syracuseStep 651169 = 488377) (by norm_num)
theorem B3502037 : Blo 511796 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B618473 : Blo 511796 618473 := bbase (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) (by norm_num)
theorem B978941 : Blo 511796 978941 := bbase (se 3 (by rfl) ⟨183551, by rfl⟩ : syracuseStep 978941 = 367103) (by norm_num)
theorem B880661 : Blo 511796 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B1044517 : Blo 511796 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B651341 : Blo 511796 651341 := bbase (se 3 (by rfl) ⟨122126, by rfl⟩ : syracuseStep 651341 = 244253) (by norm_num)
theorem B1044589 : Blo 511796 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B651397 : Blo 511796 651397 := bbase (se 4 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 651397 = 122137) (by norm_num)
theorem B1732805 : Blo 511796 1732805 := bbase (se 4 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 1732805 = 324901) (by norm_num)
theorem B651493 : Blo 511796 651493 := bbase (se 4 (by rfl) ⟨61077, by rfl⟩ : syracuseStep 651493 = 122155) (by norm_num)
theorem B618781 : Blo 511796 618781 := bbase (se 3 (by rfl) ⟨116021, by rfl⟩ : syracuseStep 618781 = 232043) (by norm_num)
theorem B651665 : Blo 511796 651665 := bbase (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) (by norm_num)
theorem B651721 : Blo 511796 651721 := bbase (se 2 (by rfl) ⟨244395, by rfl⟩ : syracuseStep 651721 = 488791) (by norm_num)
theorem B651817 : Blo 511796 651817 := bbase (se 2 (by rfl) ⟨244431, by rfl⟩ : syracuseStep 651817 = 488863) (by norm_num)
theorem B1045037 : Blo 511796 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B1733237 : Blo 511796 1733237 := bbase (se 5 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 1733237 = 162491) (by norm_num)
theorem B619169 : Blo 511796 619169 := bbase (se 2 (by rfl) ⟨232188, by rfl⟩ : syracuseStep 619169 = 464377) (by norm_num)
theorem B651989 : Blo 511796 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B7533269 : Blo 511796 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B652045 : Blo 511796 652045 := bbase (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) (by norm_num)
theorem B520997 : Blo 511796 520997 := bbase (se 4 (by rfl) ⟨48843, by rfl⟩ : syracuseStep 520997 = 97687) (by norm_num)
theorem B4682549 : Blo 511796 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B652141 : Blo 511796 652141 := bbase (se 3 (by rfl) ⟨122276, by rfl⟩ : syracuseStep 652141 = 244553) (by norm_num)
theorem B1930133 : Blo 511796 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B619525 : Blo 511796 619525 := bbase (se 4 (by rfl) ⟨58080, by rfl⟩ : syracuseStep 619525 = 116161) (by norm_num)
theorem B652313 : Blo 511796 652313 := bbase (se 2 (by rfl) ⟨244617, by rfl⟩ : syracuseStep 652313 = 489235) (by norm_num)
theorem B1733669 : Blo 511796 1733669 := bbase (se 4 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 1733669 = 325063) (by norm_num)
theorem B521273 : Blo 511796 521273 := bbase (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) (by norm_num)
theorem B2192453 : Blo 511796 2192453 := bbase (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) (by norm_num)
theorem B652369 : Blo 511796 652369 := bbase (se 2 (by rfl) ⟨244638, by rfl⟩ : syracuseStep 652369 = 489277) (by norm_num)
theorem B521321 : Blo 511796 521321 := bbase (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) (by norm_num)
theorem B652465 : Blo 511796 652465 := bbase (se 2 (by rfl) ⟨244674, by rfl⟩ : syracuseStep 652465 = 489349) (by norm_num)
theorem B652637 : Blo 511796 652637 := bbase (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) (by norm_num)
theorem B2192741 : Blo 511796 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B652693 : Blo 511796 652693 := bbase (se 6 (by rfl) ⟨15297, by rfl⟩ : syracuseStep 652693 = 30595) (by norm_num)
theorem B2717093 : Blo 511796 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B1734101 : Blo 511796 1734101 := bbase (se 7 (by rfl) ⟨20321, by rfl⟩ : syracuseStep 1734101 = 40643) (by norm_num)
theorem B652789 : Blo 511796 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B1406789 : Blo 511796 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B1734533 : Blo 511796 1734533 := bbase (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) (by norm_num)
theorem B587837 : Blo 511796 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B2193493 : Blo 511796 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B4159669 : Blo 511796 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B4389173 : Blo 511796 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B1734965 : Blo 511796 1734965 := bbase (se 5 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 1734965 = 162653) (by norm_num)
theorem B3340693 : Blo 511796 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B555709 : Blo 511796 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B1735397 : Blo 511796 1735397 := bbase (se 4 (by rfl) ⟨162693, by rfl⟩ : syracuseStep 1735397 = 325387) (by norm_num)
theorem B2194229 : Blo 511796 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B555925 : Blo 511796 555925 := bbase (se 6 (by rfl) ⟨13029, by rfl⟩ : syracuseStep 555925 = 26059) (by norm_num)
theorem B1735829 : Blo 511796 1735829 := bbase (se 6 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 1735829 = 81367) (by norm_num)
theorem B1736261 : Blo 511796 1736261 := bbase (se 4 (by rfl) ⟨162774, by rfl⟩ : syracuseStep 1736261 = 325549) (by norm_num)
theorem B1736693 : Blo 511796 1736693 := bbase (se 5 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 1736693 = 162815) (by norm_num)
theorem B3178673 : Blo 511796 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1736909 : Blo 511796 1736909 := bstep (se 3 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 1736909 = 651341) B651341
theorem B2916593 : Blo 511796 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B1736963 : Blo 511796 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B1737233 : Blo 511796 1737233 := bstep (se 2 (by rfl) ⟨651462, by rfl⟩ : syracuseStep 1737233 = 1302925) B1302925
theorem B5833457 : Blo 511796 5833457 := bstep (se 2 (by rfl) ⟨2187546, by rfl⟩ : syracuseStep 5833457 = 4375093) B4375093
theorem B819985 : Blo 511796 819985 := bstep (se 2 (by rfl) ⟨307494, by rfl⟩ : syracuseStep 819985 = 614989) B614989
theorem B3376163 : Blo 511796 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B1737773 : Blo 511796 1737773 := bstep (se 3 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 1737773 = 651665) B651665
theorem B1737827 : Blo 511796 1737827 := bstep (se 1 (by rfl) ⟨1303370, by rfl⟩ : syracuseStep 1737827 = 2606741) B2606741
theorem B820433 : Blo 511796 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B1738097 : Blo 511796 1738097 := bstep (se 2 (by rfl) ⟨651786, by rfl⟩ : syracuseStep 1738097 = 1303573) B1303573
theorem B3704291 : Blo 511796 3704291 := bstep (se 1 (by rfl) ⟨2778218, by rfl⟩ : syracuseStep 3704291 = 5556437) B5556437
theorem B1640045 : Blo 511796 1640045 := bstep (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) B615017
theorem B4392589 : Blo 511796 4392589 := bstep (se 3 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 4392589 = 1647221) B1647221
theorem B2918051 : Blo 511796 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B1738637 : Blo 511796 1738637 := bstep (se 3 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 1738637 = 651989) B651989
theorem B1738691 : Blo 511796 1738691 := bstep (se 1 (by rfl) ⟨1304018, by rfl⟩ : syracuseStep 1738691 = 2608037) B2608037
theorem B1640483 : Blo 511796 1640483 := bstep (se 1 (by rfl) ⟨1230362, by rfl⟩ : syracuseStep 1640483 = 2460725) B2460725
theorem B1247363 : Blo 511796 1247363 := bstep (se 1 (by rfl) ⟨935522, by rfl⟩ : syracuseStep 1247363 = 1871045) B1871045
theorem B1673389 : Blo 511796 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B1738961 : Blo 511796 1738961 := bstep (se 2 (by rfl) ⟨652110, by rfl⟩ : syracuseStep 1738961 = 1304221) B1304221
theorem B657715 : Blo 511796 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B788867 : Blo 511796 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B5147021 : Blo 511796 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B821843 : Blo 511796 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B11111053 : Blo 511796 11111053 := bstep (se 3 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 11111053 = 4166645) B4166645
theorem B3902093 : Blo 511796 3902093 := bstep (se 3 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 3902093 = 1463285) B1463285
theorem B1739501 : Blo 511796 1739501 := bstep (se 3 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 1739501 = 652313) B652313
theorem B822035 : Blo 511796 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B1739555 : Blo 511796 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B2788145 : Blo 511796 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B4393925 : Blo 511796 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B7048133 : Blo 511796 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B2788337 : Blo 511796 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B1412099 : Blo 511796 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B1739825 : Blo 511796 1739825 := bstep (se 2 (by rfl) ⟨652434, by rfl⟩ : syracuseStep 1739825 = 1304869) B1304869
theorem B2198755 : Blo 511796 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B1740365 : Blo 511796 1740365 := bstep (se 3 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 1740365 = 652637) B652637
theorem B1740419 : Blo 511796 1740419 := bstep (se 1 (by rfl) ⟨1305314, by rfl⟩ : syracuseStep 1740419 = 2610629) B2610629
theorem B6590321 : Blo 511796 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B1740689 : Blo 511796 1740689 := bstep (se 2 (by rfl) ⟨652758, by rfl⟩ : syracuseStep 1740689 = 1305517) B1305517
theorem B1642403 : Blo 511796 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B6655925 : Blo 511796 6655925 := bstep (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) B623993
theorem B790481 : Blo 511796 790481 := bstep (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) B592861
theorem B823457 : Blo 511796 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B3281093 : Blo 511796 3281093 := bstep (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) B615205
theorem B692641 : Blo 511796 692641 := bstep (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) B519481
theorem B2593457 : Blo 511796 2593457 := bstep (se 2 (by rfl) ⟨972546, by rfl⟩ : syracuseStep 2593457 = 1945093) B1945093
theorem B1151729 : Blo 511796 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B3707633 : Blo 511796 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B1151747 : Blo 511796 1151747 := bstep (se 1 (by rfl) ⟨863810, by rfl⟩ : syracuseStep 1151747 = 1727621) B1727621
theorem B1250051 : Blo 511796 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B2921285 : Blo 511796 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B1152017 : Blo 511796 1152017 := bstep (se 2 (by rfl) ⟨432006, by rfl⟩ : syracuseStep 1152017 = 864013) B864013
theorem B1152035 : Blo 511796 1152035 := bstep (se 1 (by rfl) ⟨864026, by rfl⟩ : syracuseStep 1152035 = 1728053) B1728053
theorem B1315921 : Blo 511796 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B2921741 : Blo 511796 2921741 := bstep (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) B1095653
theorem B1152305 : Blo 511796 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B988465 : Blo 511796 988465 := bstep (se 2 (by rfl) ⟨370674, by rfl⟩ : syracuseStep 988465 = 741349) B741349
theorem B1152323 : Blo 511796 1152323 := bstep (se 1 (by rfl) ⟨864242, by rfl⟩ : syracuseStep 1152323 = 1728485) B1728485
theorem B3905009 : Blo 511796 3905009 := bstep (se 2 (by rfl) ⟨1464378, by rfl⟩ : syracuseStep 3905009 = 2928757) B2928757
theorem B2463281 : Blo 511796 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1152593 : Blo 511796 1152593 := bstep (se 2 (by rfl) ⟨432222, by rfl⟩ : syracuseStep 1152593 = 864445) B864445
theorem B1152611 : Blo 511796 1152611 := bstep (se 1 (by rfl) ⟨864458, by rfl⟩ : syracuseStep 1152611 = 1728917) B1728917
theorem B2201201 : Blo 511796 2201201 := bstep (se 2 (by rfl) ⟨825450, by rfl⟩ : syracuseStep 2201201 = 1650901) B1650901
theorem B595571 : Blo 511796 595571 := bstep (se 1 (by rfl) ⟨446678, by rfl⟩ : syracuseStep 595571 = 893357) B893357
theorem B824995 : Blo 511796 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B825041 : Blo 511796 825041 := bstep (se 2 (by rfl) ⟨309390, by rfl⟩ : syracuseStep 825041 = 618781) B618781
theorem B3610403 : Blo 511796 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1152881 : Blo 511796 1152881 := bstep (se 2 (by rfl) ⟨432330, by rfl⟩ : syracuseStep 1152881 = 864661) B864661
theorem B1152899 : Blo 511796 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B1251281 : Blo 511796 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B923651 : Blo 511796 923651 := bstep (se 1 (by rfl) ⟨692738, by rfl⟩ : syracuseStep 923651 = 1385477) B1385477
theorem B2594915 : Blo 511796 2594915 := bstep (se 1 (by rfl) ⟨1946186, by rfl⟩ : syracuseStep 2594915 = 3892373) B3892373
theorem B1153169 : Blo 511796 1153169 := bstep (se 2 (by rfl) ⟨432438, by rfl⟩ : syracuseStep 1153169 = 864877) B864877
theorem B1153187 : Blo 511796 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B1153457 : Blo 511796 1153457 := bstep (se 2 (by rfl) ⟨432546, by rfl⟩ : syracuseStep 1153457 = 865093) B865093
theorem B1153475 : Blo 511796 1153475 := bstep (se 1 (by rfl) ⟨865106, by rfl⟩ : syracuseStep 1153475 = 1730213) B1730213
theorem B9869795 : Blo 511796 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B1645069 : Blo 511796 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B826033 : Blo 511796 826033 := bstep (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) B619525
theorem B1153745 : Blo 511796 1153745 := bstep (se 2 (by rfl) ⟨432654, by rfl⟩ : syracuseStep 1153745 = 865309) B865309
theorem B1153763 : Blo 511796 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B2595725 : Blo 511796 2595725 := bstep (se 3 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 2595725 = 973397) B973397
theorem B1154033 : Blo 511796 1154033 := bstep (se 2 (by rfl) ⟨432762, by rfl⟩ : syracuseStep 1154033 = 865525) B865525
theorem B1154051 : Blo 511796 1154051 := bstep (se 1 (by rfl) ⟨865538, by rfl⟩ : syracuseStep 1154051 = 1731077) B1731077
theorem B924689 : Blo 511796 924689 := bstep (se 2 (by rfl) ⟨346758, by rfl⟩ : syracuseStep 924689 = 693517) B693517
theorem B4168901 : Blo 511796 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B1154321 : Blo 511796 1154321 := bstep (se 2 (by rfl) ⟨432870, by rfl⟩ : syracuseStep 1154321 = 865741) B865741
theorem B1154339 : Blo 511796 1154339 := bstep (se 1 (by rfl) ⟨865754, by rfl⟩ : syracuseStep 1154339 = 1731509) B1731509
theorem B1154609 : Blo 511796 1154609 := bstep (se 2 (by rfl) ⟨432978, by rfl⟩ : syracuseStep 1154609 = 865957) B865957
theorem B1154627 : Blo 511796 1154627 := bstep (se 1 (by rfl) ⟨865970, by rfl⟩ : syracuseStep 1154627 = 1731941) B1731941
theorem B6233669 : Blo 511796 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B1384049 : Blo 511796 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B1154897 : Blo 511796 1154897 := bstep (se 2 (by rfl) ⟨433086, by rfl⟩ : syracuseStep 1154897 = 866173) B866173
theorem B1154915 : Blo 511796 1154915 := bstep (se 1 (by rfl) ⟨866186, by rfl⟩ : syracuseStep 1154915 = 1732373) B1732373
theorem B4398947 : Blo 511796 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B3710861 : Blo 511796 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B728995 : Blo 511796 728995 := bstep (se 1 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 728995 = 1093493) B1093493
theorem B1646531 : Blo 511796 1646531 := bstep (se 1 (by rfl) ⟨1234898, by rfl⟩ : syracuseStep 1646531 = 2469797) B2469797
theorem B2465741 : Blo 511796 2465741 := bstep (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) B924653
theorem B2334691 : Blo 511796 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B729091 : Blo 511796 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B1155185 : Blo 511796 1155185 := bstep (se 2 (by rfl) ⟨433194, by rfl⟩ : syracuseStep 1155185 = 866389) B866389
theorem B2924657 : Blo 511796 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1155203 : Blo 511796 1155203 := bstep (se 1 (by rfl) ⟨866402, by rfl⟩ : syracuseStep 1155203 = 1732805) B1732805
theorem B1646801 : Blo 511796 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B5546225 : Blo 511796 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B1974577 : Blo 511796 1974577 := bstep (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) B1480933
theorem B696691 : Blo 511796 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B3514757 : Blo 511796 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B1155473 : Blo 511796 1155473 := bstep (se 2 (by rfl) ⟨433302, by rfl⟩ : syracuseStep 1155473 = 866605) B866605
theorem B1155491 : Blo 511796 1155491 := bstep (se 1 (by rfl) ⟨866618, by rfl⟩ : syracuseStep 1155491 = 1733237) B1733237
theorem B5022179 : Blo 511796 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B729587 : Blo 511796 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B3121699 : Blo 511796 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B926275 : Blo 511796 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B4694669 : Blo 511796 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B1155761 : Blo 511796 1155761 := bstep (se 2 (by rfl) ⟨433410, by rfl⟩ : syracuseStep 1155761 = 866821) B866821
theorem B1155779 : Blo 511796 1155779 := bstep (se 1 (by rfl) ⟨866834, by rfl⟩ : syracuseStep 1155779 = 1733669) B1733669
theorem B1811395 : Blo 511796 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B1156049 : Blo 511796 1156049 := bstep (se 2 (by rfl) ⟨433518, by rfl⟩ : syracuseStep 1156049 = 867037) B867037
theorem B1156067 : Blo 511796 1156067 := bstep (se 1 (by rfl) ⟨867050, by rfl⟩ : syracuseStep 1156067 = 1734101) B1734101
theorem B730225 : Blo 511796 730225 := bstep (se 2 (by rfl) ⟨273834, by rfl⟩ : syracuseStep 730225 = 547669) B547669
theorem B2335949 : Blo 511796 2335949 := bstep (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) B875981
theorem B1156337 : Blo 511796 1156337 := bstep (se 2 (by rfl) ⟨433626, by rfl⟩ : syracuseStep 1156337 = 867253) B867253
theorem B1156355 : Blo 511796 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B730561 : Blo 511796 730561 := bstep (se 2 (by rfl) ⟨273960, by rfl⟩ : syracuseStep 730561 = 547921) B547921
theorem B1156625 : Blo 511796 1156625 := bstep (se 2 (by rfl) ⟨433734, by rfl⟩ : syracuseStep 1156625 = 867469) B867469
theorem B2926115 : Blo 511796 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B1156643 : Blo 511796 1156643 := bstep (se 1 (by rfl) ⟨867482, by rfl⟩ : syracuseStep 1156643 = 1734965) B1734965
theorem B2598641 : Blo 511796 2598641 := bstep (se 2 (by rfl) ⟨974490, by rfl⟩ : syracuseStep 2598641 = 1948981) B1948981
theorem B1156913 : Blo 511796 1156913 := bstep (se 2 (by rfl) ⟨433842, by rfl⟩ : syracuseStep 1156913 = 867685) B867685
theorem B6235957 : Blo 511796 6235957 := bstep (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) B584621
theorem B1156931 : Blo 511796 1156931 := bstep (se 1 (by rfl) ⟨867698, by rfl⟩ : syracuseStep 1156931 = 1735397) B1735397
theorem B731153 : Blo 511796 731153 := bstep (se 2 (by rfl) ⟨274182, by rfl⟩ : syracuseStep 731153 = 548365) B548365
theorem B1157201 : Blo 511796 1157201 := bstep (se 2 (by rfl) ⟨433950, by rfl⟩ : syracuseStep 1157201 = 867901) B867901
theorem B1157219 : Blo 511796 1157219 := bstep (se 1 (by rfl) ⟨867914, by rfl⟩ : syracuseStep 1157219 = 1735829) B1735829
theorem B1190051 : Blo 511796 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B3287267 : Blo 511796 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B5548301 : Blo 511796 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B1157489 : Blo 511796 1157489 := bstep (se 2 (by rfl) ⟨434058, by rfl⟩ : syracuseStep 1157489 = 868117) B868117
theorem B1157507 : Blo 511796 1157507 := bstep (se 1 (by rfl) ⟨868130, by rfl⟩ : syracuseStep 1157507 = 1736261) B1736261
theorem B2927117 : Blo 511796 2927117 := bstep (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) B1097669
theorem B731683 : Blo 511796 731683 := bstep (se 1 (by rfl) ⟨548762, by rfl⟩ : syracuseStep 731683 = 1097525) B1097525
theorem B1649261 : Blo 511796 1649261 := bstep (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) B618473
theorem B3943025 : Blo 511796 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B1157777 : Blo 511796 1157777 := bstep (se 2 (by rfl) ⟨434166, by rfl⟩ : syracuseStep 1157777 = 868333) B868333
theorem B1157795 : Blo 511796 1157795 := bstep (se 1 (by rfl) ⟨868346, by rfl⟩ : syracuseStep 1157795 = 1736693) B1736693
theorem B3287729 : Blo 511796 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B928465 : Blo 511796 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B732019 : Blo 511796 732019 := bstep (se 1 (by rfl) ⟨549014, by rfl⟩ : syracuseStep 732019 = 1098029) B1098029
theorem B1158065 : Blo 511796 1158065 := bstep (se 2 (by rfl) ⟨434274, by rfl⟩ : syracuseStep 1158065 = 868549) B868549
theorem B1158083 : Blo 511796 1158083 := bstep (se 1 (by rfl) ⟨868562, by rfl⟩ : syracuseStep 1158083 = 1737125) B1737125
theorem B1846307 : Blo 511796 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B2600099 : Blo 511796 2600099 := bstep (se 1 (by rfl) ⟨1950074, by rfl⟩ : syracuseStep 2600099 = 3900149) B3900149
theorem B1158353 : Blo 511796 1158353 := bstep (se 2 (by rfl) ⟨434382, by rfl⟩ : syracuseStep 1158353 = 868765) B868765
theorem B1158371 : Blo 511796 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B1944881 : Blo 511796 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B732577 : Blo 511796 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B732611 : Blo 511796 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B1158641 : Blo 511796 1158641 := bstep (se 2 (by rfl) ⟨434490, by rfl⟩ : syracuseStep 1158641 = 868981) B868981
theorem B4402673 : Blo 511796 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B1158659 : Blo 511796 1158659 := bstep (se 1 (by rfl) ⟨868994, by rfl⟩ : syracuseStep 1158659 = 1737989) B1737989
theorem B863777 : Blo 511796 863777 := bstep (se 2 (by rfl) ⟨323916, by rfl⟩ : syracuseStep 863777 = 647833) B647833
theorem B863905 : Blo 511796 863905 := bstep (se 2 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 863905 = 647929) B647929
theorem B863939 : Blo 511796 863939 := bstep (se 1 (by rfl) ⟨647954, by rfl⟩ : syracuseStep 863939 = 1295909) B1295909
theorem B1158929 : Blo 511796 1158929 := bstep (se 2 (by rfl) ⟨434598, by rfl⟩ : syracuseStep 1158929 = 869197) B869197
theorem B1158947 : Blo 511796 1158947 := bstep (se 1 (by rfl) ⟨869210, by rfl⟩ : syracuseStep 1158947 = 1738421) B1738421
theorem B864067 : Blo 511796 864067 := bstep (se 1 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 864067 = 1296101) B1296101
theorem B2338723 : Blo 511796 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B2600909 : Blo 511796 2600909 := bstep (se 3 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 2600909 = 975341) B975341
theorem B864209 : Blo 511796 864209 := bstep (se 2 (by rfl) ⟨324078, by rfl⟩ : syracuseStep 864209 = 648157) B648157
theorem B1093603 : Blo 511796 1093603 := bstep (se 1 (by rfl) ⟨820202, by rfl⟩ : syracuseStep 1093603 = 1640405) B1640405
theorem B733169 : Blo 511796 733169 := bstep (se 2 (by rfl) ⟨274938, by rfl⟩ : syracuseStep 733169 = 549877) B549877
theorem B1159217 : Blo 511796 1159217 := bstep (se 2 (by rfl) ⟨434706, by rfl⟩ : syracuseStep 1159217 = 869413) B869413
theorem B733249 : Blo 511796 733249 := bstep (se 2 (by rfl) ⟨274968, by rfl⟩ : syracuseStep 733249 = 549937) B549937
theorem B1159235 : Blo 511796 1159235 := bstep (se 1 (by rfl) ⟨869426, by rfl⟩ : syracuseStep 1159235 = 1738853) B1738853
theorem B864337 : Blo 511796 864337 := bstep (se 2 (by rfl) ⟨324126, by rfl⟩ : syracuseStep 864337 = 648253) B648253
theorem B6697073 : Blo 511796 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B864371 : Blo 511796 864371 := bstep (se 1 (by rfl) ⟨648278, by rfl⟩ : syracuseStep 864371 = 1296557) B1296557
theorem B864499 : Blo 511796 864499 := bstep (se 1 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 864499 = 1296749) B1296749
theorem B1159505 : Blo 511796 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B1159523 : Blo 511796 1159523 := bstep (se 1 (by rfl) ⟨869642, by rfl⟩ : syracuseStep 1159523 = 1739285) B1739285
theorem B864641 : Blo 511796 864641 := bstep (se 2 (by rfl) ⟨324240, by rfl⟩ : syracuseStep 864641 = 648481) B648481
theorem B1651117 : Blo 511796 1651117 := bstep (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) B619169
theorem B864769 : Blo 511796 864769 := bstep (se 2 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 864769 = 648577) B648577
theorem B2503181 : Blo 511796 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B864803 : Blo 511796 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B1159793 : Blo 511796 1159793 := bstep (se 2 (by rfl) ⟨434922, by rfl⟩ : syracuseStep 1159793 = 869845) B869845
theorem B1159811 : Blo 511796 1159811 := bstep (se 1 (by rfl) ⟨869858, by rfl⟩ : syracuseStep 1159811 = 1739717) B1739717
theorem B7385741 : Blo 511796 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B864931 : Blo 511796 864931 := bstep (se 1 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 864931 = 1297397) B1297397
theorem B1946339 : Blo 511796 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1389325 : Blo 511796 1389325 := bstep (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) B520997
theorem B865073 : Blo 511796 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B734035 : Blo 511796 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B2667377 : Blo 511796 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B53523341 : Blo 511796 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B1160081 : Blo 511796 1160081 := bstep (se 2 (by rfl) ⟨435030, by rfl⟩ : syracuseStep 1160081 = 870061) B870061
theorem B1160099 : Blo 511796 1160099 := bstep (se 1 (by rfl) ⟨870074, by rfl⟩ : syracuseStep 1160099 = 1740149) B1740149
theorem B865201 : Blo 511796 865201 := bstep (se 2 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 865201 = 648901) B648901
theorem B865235 : Blo 511796 865235 := bstep (se 1 (by rfl) ⟨648926, by rfl⟩ : syracuseStep 865235 = 1297853) B1297853
theorem B865363 : Blo 511796 865363 := bstep (se 1 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 865363 = 1298045) B1298045
theorem B1094833 : Blo 511796 1094833 := bstep (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) B821125
theorem B1160369 : Blo 511796 1160369 := bstep (se 2 (by rfl) ⟨435138, by rfl⟩ : syracuseStep 1160369 = 870277) B870277
theorem B1160387 : Blo 511796 1160387 := bstep (se 1 (by rfl) ⟨870290, by rfl⟩ : syracuseStep 1160387 = 1740581) B1740581
theorem B865505 : Blo 511796 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B865633 : Blo 511796 865633 := bstep (se 2 (by rfl) ⟨324612, by rfl⟩ : syracuseStep 865633 = 649225) B649225
theorem B2930033 : Blo 511796 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B865667 : Blo 511796 865667 := bstep (se 1 (by rfl) ⟨649250, by rfl⟩ : syracuseStep 865667 = 1298501) B1298501
theorem B1390061 : Blo 511796 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B865795 : Blo 511796 865795 := bstep (se 1 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 865795 = 1298693) B1298693
theorem B865937 : Blo 511796 865937 := bstep (se 2 (by rfl) ⟨324726, by rfl⟩ : syracuseStep 865937 = 649453) B649453
theorem B1947341 : Blo 511796 1947341 := bstep (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) B730253
theorem B767699 : Blo 511796 767699 := bstep (se 1 (by rfl) ⟨575774, by rfl⟩ : syracuseStep 767699 = 1151549) B1151549
theorem B767729 : Blo 511796 767729 := bstep (se 2 (by rfl) ⟨287898, by rfl⟩ : syracuseStep 767729 = 575797) B575797
theorem B767747 : Blo 511796 767747 := bstep (se 1 (by rfl) ⟨575810, by rfl⟩ : syracuseStep 767747 = 1151621) B1151621
theorem B866065 : Blo 511796 866065 := bstep (se 2 (by rfl) ⟨324774, by rfl⟩ : syracuseStep 866065 = 649549) B649549
theorem B767777 : Blo 511796 767777 := bstep (se 2 (by rfl) ⟨287916, by rfl⟩ : syracuseStep 767777 = 575833) B575833
theorem B767795 : Blo 511796 767795 := bstep (se 1 (by rfl) ⟨575846, by rfl⟩ : syracuseStep 767795 = 1151693) B1151693
theorem B866099 : Blo 511796 866099 := bstep (se 1 (by rfl) ⟨649574, by rfl⟩ : syracuseStep 866099 = 1299149) B1299149
theorem B767825 : Blo 511796 767825 := bstep (se 2 (by rfl) ⟨287934, by rfl⟩ : syracuseStep 767825 = 575869) B575869
theorem B767843 : Blo 511796 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B767873 : Blo 511796 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B767891 : Blo 511796 767891 := bstep (se 1 (by rfl) ⟨575918, by rfl⟩ : syracuseStep 767891 = 1151837) B1151837
theorem B767921 : Blo 511796 767921 := bstep (se 2 (by rfl) ⟨287970, by rfl⟩ : syracuseStep 767921 = 575941) B575941
theorem B866227 : Blo 511796 866227 := bstep (se 1 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 866227 = 1299341) B1299341
theorem B767939 : Blo 511796 767939 := bstep (se 1 (by rfl) ⟨575954, by rfl⟩ : syracuseStep 767939 = 1151909) B1151909
theorem B1095619 : Blo 511796 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B767969 : Blo 511796 767969 := bstep (se 2 (by rfl) ⟨287988, by rfl⟩ : syracuseStep 767969 = 575977) B575977
theorem B767987 : Blo 511796 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B768017 : Blo 511796 768017 := bstep (se 2 (by rfl) ⟨288006, by rfl⟩ : syracuseStep 768017 = 576013) B576013
theorem B768035 : Blo 511796 768035 := bstep (se 1 (by rfl) ⟨576026, by rfl⟩ : syracuseStep 768035 = 1152053) B1152053
theorem B768065 : Blo 511796 768065 := bstep (se 2 (by rfl) ⟨288024, by rfl⟩ : syracuseStep 768065 = 576049) B576049
theorem B866369 : Blo 511796 866369 := bstep (se 2 (by rfl) ⟨324888, by rfl⟩ : syracuseStep 866369 = 649777) B649777
theorem B2078797 : Blo 511796 2078797 := bstep (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) B779549
theorem B768083 : Blo 511796 768083 := bstep (se 1 (by rfl) ⟨576062, by rfl⟩ : syracuseStep 768083 = 1152125) B1152125
theorem B768113 : Blo 511796 768113 := bstep (se 2 (by rfl) ⟨288042, by rfl⟩ : syracuseStep 768113 = 576085) B576085
theorem B768131 : Blo 511796 768131 := bstep (se 1 (by rfl) ⟨576098, by rfl⟩ : syracuseStep 768131 = 1152197) B1152197
theorem B768161 : Blo 511796 768161 := bstep (se 2 (by rfl) ⟨288060, by rfl⟩ : syracuseStep 768161 = 576121) B576121
theorem B768179 : Blo 511796 768179 := bstep (se 1 (by rfl) ⟨576134, by rfl⟩ : syracuseStep 768179 = 1152269) B1152269
theorem B866497 : Blo 511796 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B1849549 : Blo 511796 1849549 := bstep (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) B693581
theorem B768209 : Blo 511796 768209 := bstep (se 2 (by rfl) ⟨288078, by rfl⟩ : syracuseStep 768209 = 576157) B576157
theorem B768227 : Blo 511796 768227 := bstep (se 1 (by rfl) ⟨576170, by rfl⟩ : syracuseStep 768227 = 1152341) B1152341
theorem B866531 : Blo 511796 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B768257 : Blo 511796 768257 := bstep (se 2 (by rfl) ⟨288096, by rfl⟩ : syracuseStep 768257 = 576193) B576193
theorem B768275 : Blo 511796 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B768305 : Blo 511796 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B2341169 : Blo 511796 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B768323 : Blo 511796 768323 := bstep (se 1 (by rfl) ⟨576242, by rfl⟩ : syracuseStep 768323 = 1152485) B1152485
theorem B768353 : Blo 511796 768353 := bstep (se 2 (by rfl) ⟨288132, by rfl⟩ : syracuseStep 768353 = 576265) B576265
theorem B866659 : Blo 511796 866659 := bstep (se 1 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 866659 = 1299989) B1299989
theorem B768371 : Blo 511796 768371 := bstep (se 1 (by rfl) ⟨576278, by rfl⟩ : syracuseStep 768371 = 1152557) B1152557
theorem B768401 : Blo 511796 768401 := bstep (se 2 (by rfl) ⟨288150, by rfl⟩ : syracuseStep 768401 = 576301) B576301
theorem B768419 : Blo 511796 768419 := bstep (se 1 (by rfl) ⟨576314, by rfl⟩ : syracuseStep 768419 = 1152629) B1152629
theorem B768449 : Blo 511796 768449 := bstep (se 2 (by rfl) ⟨288168, by rfl⟩ : syracuseStep 768449 = 576337) B576337
theorem B768467 : Blo 511796 768467 := bstep (se 1 (by rfl) ⟨576350, by rfl⟩ : syracuseStep 768467 = 1152701) B1152701
theorem B768497 : Blo 511796 768497 := bstep (se 2 (by rfl) ⟨288186, by rfl⟩ : syracuseStep 768497 = 576373) B576373
theorem B866801 : Blo 511796 866801 := bstep (se 2 (by rfl) ⟨325050, by rfl⟩ : syracuseStep 866801 = 650101) B650101
theorem B768515 : Blo 511796 768515 := bstep (se 1 (by rfl) ⟨576386, by rfl⟩ : syracuseStep 768515 = 1152773) B1152773
theorem B768545 : Blo 511796 768545 := bstep (se 2 (by rfl) ⟨288204, by rfl⟩ : syracuseStep 768545 = 576409) B576409
theorem B768563 : Blo 511796 768563 := bstep (se 1 (by rfl) ⟨576422, by rfl⟩ : syracuseStep 768563 = 1152845) B1152845
theorem B768593 : Blo 511796 768593 := bstep (se 2 (by rfl) ⟨288222, by rfl⟩ : syracuseStep 768593 = 576445) B576445
theorem B1391185 : Blo 511796 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B768611 : Blo 511796 768611 := bstep (se 1 (by rfl) ⟨576458, by rfl⟩ : syracuseStep 768611 = 1152917) B1152917
theorem B866929 : Blo 511796 866929 := bstep (se 2 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 866929 = 650197) B650197
theorem B703091 : Blo 511796 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B768641 : Blo 511796 768641 := bstep (se 2 (by rfl) ⟨288240, by rfl⟩ : syracuseStep 768641 = 576481) B576481
theorem B1849997 : Blo 511796 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B1096337 : Blo 511796 1096337 := bstep (se 2 (by rfl) ⟨411126, by rfl⟩ : syracuseStep 1096337 = 822253) B822253
theorem B768659 : Blo 511796 768659 := bstep (se 1 (by rfl) ⟨576494, by rfl⟩ : syracuseStep 768659 = 1152989) B1152989
theorem B866963 : Blo 511796 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B768689 : Blo 511796 768689 := bstep (se 2 (by rfl) ⟨288258, by rfl⟩ : syracuseStep 768689 = 576517) B576517
theorem B768707 : Blo 511796 768707 := bstep (se 1 (by rfl) ⟨576530, by rfl⟩ : syracuseStep 768707 = 1153061) B1153061
theorem B768737 : Blo 511796 768737 := bstep (se 2 (by rfl) ⟨288276, by rfl⟩ : syracuseStep 768737 = 576553) B576553
theorem B768755 : Blo 511796 768755 := bstep (se 1 (by rfl) ⟨576566, by rfl⟩ : syracuseStep 768755 = 1153133) B1153133
theorem B768785 : Blo 511796 768785 := bstep (se 2 (by rfl) ⟨288294, by rfl⟩ : syracuseStep 768785 = 576589) B576589
theorem B867091 : Blo 511796 867091 := bstep (se 1 (by rfl) ⟨650318, by rfl⟩ : syracuseStep 867091 = 1300637) B1300637
theorem B768803 : Blo 511796 768803 := bstep (se 1 (by rfl) ⟨576602, by rfl⟩ : syracuseStep 768803 = 1153205) B1153205
theorem B2931491 : Blo 511796 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B2603825 : Blo 511796 2603825 := bstep (se 2 (by rfl) ⟨976434, by rfl⟩ : syracuseStep 2603825 = 1952869) B1952869
theorem B768833 : Blo 511796 768833 := bstep (se 2 (by rfl) ⟨288312, by rfl⟩ : syracuseStep 768833 = 576625) B576625
theorem B768851 : Blo 511796 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B768881 : Blo 511796 768881 := bstep (se 2 (by rfl) ⟨288330, by rfl⟩ : syracuseStep 768881 = 576661) B576661
theorem B768899 : Blo 511796 768899 := bstep (se 1 (by rfl) ⟨576674, by rfl⟩ : syracuseStep 768899 = 1153349) B1153349
theorem B768929 : Blo 511796 768929 := bstep (se 2 (by rfl) ⟨288348, by rfl⟩ : syracuseStep 768929 = 576697) B576697
theorem B867233 : Blo 511796 867233 := bstep (se 2 (by rfl) ⟨325212, by rfl⟩ : syracuseStep 867233 = 650425) B650425
theorem B768947 : Blo 511796 768947 := bstep (se 1 (by rfl) ⟨576710, by rfl⟩ : syracuseStep 768947 = 1153421) B1153421
theorem B768977 : Blo 511796 768977 := bstep (se 2 (by rfl) ⟨288366, by rfl⟩ : syracuseStep 768977 = 576733) B576733
theorem B768995 : Blo 511796 768995 := bstep (se 1 (by rfl) ⟨576746, by rfl⟩ : syracuseStep 768995 = 1153493) B1153493
theorem B769025 : Blo 511796 769025 := bstep (se 2 (by rfl) ⟨288384, by rfl⟩ : syracuseStep 769025 = 576769) B576769
theorem B769043 : Blo 511796 769043 := bstep (se 1 (by rfl) ⟨576782, by rfl⟩ : syracuseStep 769043 = 1153565) B1153565
theorem B867361 : Blo 511796 867361 := bstep (se 2 (by rfl) ⟨325260, by rfl⟩ : syracuseStep 867361 = 650521) B650521
theorem B769073 : Blo 511796 769073 := bstep (se 2 (by rfl) ⟨288402, by rfl⟩ : syracuseStep 769073 = 576805) B576805
theorem B769091 : Blo 511796 769091 := bstep (se 1 (by rfl) ⟨576818, by rfl⟩ : syracuseStep 769091 = 1153637) B1153637
theorem B867395 : Blo 511796 867395 := bstep (se 1 (by rfl) ⟨650546, by rfl⟩ : syracuseStep 867395 = 1301093) B1301093
theorem B769121 : Blo 511796 769121 := bstep (se 2 (by rfl) ⟨288420, by rfl⟩ : syracuseStep 769121 = 576841) B576841
theorem B769139 : Blo 511796 769139 := bstep (se 1 (by rfl) ⟨576854, by rfl⟩ : syracuseStep 769139 = 1153709) B1153709
theorem B769169 : Blo 511796 769169 := bstep (se 2 (by rfl) ⟨288438, by rfl⟩ : syracuseStep 769169 = 576877) B576877
theorem B1096849 : Blo 511796 1096849 := bstep (se 2 (by rfl) ⟨411318, by rfl⟩ : syracuseStep 1096849 = 822637) B822637
theorem B769187 : Blo 511796 769187 := bstep (se 1 (by rfl) ⟨576890, by rfl⟩ : syracuseStep 769187 = 1153781) B1153781
theorem B769217 : Blo 511796 769217 := bstep (se 2 (by rfl) ⟨288456, by rfl⟩ : syracuseStep 769217 = 576913) B576913
theorem B867523 : Blo 511796 867523 := bstep (se 1 (by rfl) ⟨650642, by rfl⟩ : syracuseStep 867523 = 1301285) B1301285
theorem B769235 : Blo 511796 769235 := bstep (se 1 (by rfl) ⟨576926, by rfl⟩ : syracuseStep 769235 = 1153853) B1153853
theorem B6569201 : Blo 511796 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B769265 : Blo 511796 769265 := bstep (se 2 (by rfl) ⟨288474, by rfl⟩ : syracuseStep 769265 = 576949) B576949
theorem B769283 : Blo 511796 769283 := bstep (se 1 (by rfl) ⟨576962, by rfl⟩ : syracuseStep 769283 = 1153925) B1153925
theorem B769313 : Blo 511796 769313 := bstep (se 2 (by rfl) ⟨288492, by rfl⟩ : syracuseStep 769313 = 576985) B576985
theorem B1457453 : Blo 511796 1457453 := bstep (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) B546545
theorem B998705 : Blo 511796 998705 := bstep (se 2 (by rfl) ⟨374514, by rfl⟩ : syracuseStep 998705 = 749029) B749029
theorem B769331 : Blo 511796 769331 := bstep (se 1 (by rfl) ⟨576998, by rfl⟩ : syracuseStep 769331 = 1153997) B1153997
theorem B769361 : Blo 511796 769361 := bstep (se 2 (by rfl) ⟨288510, by rfl⟩ : syracuseStep 769361 = 577021) B577021
theorem B867665 : Blo 511796 867665 := bstep (se 2 (by rfl) ⟨325374, by rfl⟩ : syracuseStep 867665 = 650749) B650749
theorem B769379 : Blo 511796 769379 := bstep (se 1 (by rfl) ⟨577034, by rfl⟩ : syracuseStep 769379 = 1154069) B1154069
theorem B769409 : Blo 511796 769409 := bstep (se 2 (by rfl) ⟨288528, by rfl⟩ : syracuseStep 769409 = 577057) B577057
theorem B769427 : Blo 511796 769427 := bstep (se 1 (by rfl) ⟨577070, by rfl⟩ : syracuseStep 769427 = 1154141) B1154141
theorem B769457 : Blo 511796 769457 := bstep (se 2 (by rfl) ⟨288546, by rfl⟩ : syracuseStep 769457 = 577093) B577093
theorem B769475 : Blo 511796 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B7421381 : Blo 511796 7421381 := bstep (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) B1391509
theorem B867793 : Blo 511796 867793 := bstep (se 2 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 867793 = 650845) B650845
theorem B769505 : Blo 511796 769505 := bstep (se 2 (by rfl) ⟨288564, by rfl⟩ : syracuseStep 769505 = 577129) B577129
theorem B769523 : Blo 511796 769523 := bstep (se 1 (by rfl) ⟨577142, by rfl⟩ : syracuseStep 769523 = 1154285) B1154285
theorem B867827 : Blo 511796 867827 := bstep (se 1 (by rfl) ⟨650870, by rfl⟩ : syracuseStep 867827 = 1301741) B1301741
theorem B769553 : Blo 511796 769553 := bstep (se 2 (by rfl) ⟨288582, by rfl⟩ : syracuseStep 769553 = 577165) B577165
theorem B769571 : Blo 511796 769571 := bstep (se 1 (by rfl) ⟨577178, by rfl⟩ : syracuseStep 769571 = 1154357) B1154357
theorem B769601 : Blo 511796 769601 := bstep (se 2 (by rfl) ⟨288600, by rfl⟩ : syracuseStep 769601 = 577201) B577201
theorem B769619 : Blo 511796 769619 := bstep (se 1 (by rfl) ⟨577214, by rfl⟩ : syracuseStep 769619 = 1154429) B1154429
theorem B769649 : Blo 511796 769649 := bstep (se 2 (by rfl) ⟨288618, by rfl⟩ : syracuseStep 769649 = 577237) B577237
theorem B867955 : Blo 511796 867955 := bstep (se 1 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 867955 = 1301933) B1301933
theorem B769667 : Blo 511796 769667 := bstep (se 1 (by rfl) ⟨577250, by rfl⟩ : syracuseStep 769667 = 1154501) B1154501
theorem B769697 : Blo 511796 769697 := bstep (se 2 (by rfl) ⟨288636, by rfl⟩ : syracuseStep 769697 = 577273) B577273
theorem B769715 : Blo 511796 769715 := bstep (se 1 (by rfl) ⟨577286, by rfl⟩ : syracuseStep 769715 = 1154573) B1154573
theorem B769745 : Blo 511796 769745 := bstep (se 2 (by rfl) ⟨288654, by rfl⟩ : syracuseStep 769745 = 577309) B577309
theorem B769763 : Blo 511796 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B769793 : Blo 511796 769793 := bstep (se 2 (by rfl) ⟨288672, by rfl⟩ : syracuseStep 769793 = 577345) B577345
theorem B868097 : Blo 511796 868097 := bstep (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) B651073
theorem B1949453 : Blo 511796 1949453 := bstep (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) B731045
theorem B769811 : Blo 511796 769811 := bstep (se 1 (by rfl) ⟨577358, by rfl⟩ : syracuseStep 769811 = 1154717) B1154717
theorem B769841 : Blo 511796 769841 := bstep (se 2 (by rfl) ⟨288690, by rfl⟩ : syracuseStep 769841 = 577381) B577381
theorem B769859 : Blo 511796 769859 := bstep (se 1 (by rfl) ⟨577394, by rfl⟩ : syracuseStep 769859 = 1154789) B1154789
theorem B769889 : Blo 511796 769889 := bstep (se 2 (by rfl) ⟨288708, by rfl⟩ : syracuseStep 769889 = 577417) B577417
theorem B769907 : Blo 511796 769907 := bstep (se 1 (by rfl) ⟨577430, by rfl⟩ : syracuseStep 769907 = 1154861) B1154861
theorem B868225 : Blo 511796 868225 := bstep (se 2 (by rfl) ⟨325584, by rfl⟩ : syracuseStep 868225 = 651169) B651169
theorem B769937 : Blo 511796 769937 := bstep (se 2 (by rfl) ⟨288726, by rfl⟩ : syracuseStep 769937 = 577453) B577453
theorem B769955 : Blo 511796 769955 := bstep (se 1 (by rfl) ⟨577466, by rfl⟩ : syracuseStep 769955 = 1154933) B1154933
theorem B868259 : Blo 511796 868259 := bstep (se 1 (by rfl) ⟨651194, by rfl⟩ : syracuseStep 868259 = 1302389) B1302389
theorem B1392547 : Blo 511796 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B769985 : Blo 511796 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B770003 : Blo 511796 770003 := bstep (se 1 (by rfl) ⟨577502, by rfl⟩ : syracuseStep 770003 = 1155005) B1155005
theorem B1392611 : Blo 511796 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B770033 : Blo 511796 770033 := bstep (se 2 (by rfl) ⟨288762, by rfl⟩ : syracuseStep 770033 = 577525) B577525
theorem B770051 : Blo 511796 770051 := bstep (se 1 (by rfl) ⟨577538, by rfl⟩ : syracuseStep 770051 = 1155077) B1155077
theorem B770081 : Blo 511796 770081 := bstep (se 2 (by rfl) ⟨288780, by rfl⟩ : syracuseStep 770081 = 577561) B577561
theorem B868387 : Blo 511796 868387 := bstep (se 1 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 868387 = 1302581) B1302581
theorem B1392689 : Blo 511796 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B901171 : Blo 511796 901171 := bstep (se 1 (by rfl) ⟨675878, by rfl⟩ : syracuseStep 901171 = 1351757) B1351757
theorem B770099 : Blo 511796 770099 := bstep (se 1 (by rfl) ⟨577574, by rfl⟩ : syracuseStep 770099 = 1155149) B1155149
theorem B770129 : Blo 511796 770129 := bstep (se 2 (by rfl) ⟨288798, by rfl⟩ : syracuseStep 770129 = 577597) B577597
theorem B770147 : Blo 511796 770147 := bstep (se 1 (by rfl) ⟨577610, by rfl⟩ : syracuseStep 770147 = 1155221) B1155221
theorem B770177 : Blo 511796 770177 := bstep (se 2 (by rfl) ⟨288816, by rfl⟩ : syracuseStep 770177 = 577633) B577633
theorem B1392785 : Blo 511796 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B770195 : Blo 511796 770195 := bstep (se 1 (by rfl) ⟨577646, by rfl⟩ : syracuseStep 770195 = 1155293) B1155293
theorem B770225 : Blo 511796 770225 := bstep (se 2 (by rfl) ⟨288834, by rfl⟩ : syracuseStep 770225 = 577669) B577669
theorem B1851569 : Blo 511796 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B868529 : Blo 511796 868529 := bstep (se 2 (by rfl) ⟨325698, by rfl⟩ : syracuseStep 868529 = 651397) B651397
theorem B770243 : Blo 511796 770243 := bstep (se 1 (by rfl) ⟨577682, by rfl⟩ : syracuseStep 770243 = 1155365) B1155365
theorem B770273 : Blo 511796 770273 := bstep (se 2 (by rfl) ⟨288852, by rfl⟩ : syracuseStep 770273 = 577705) B577705
theorem B2605283 : Blo 511796 2605283 := bstep (se 1 (by rfl) ⟨1953962, by rfl⟩ : syracuseStep 2605283 = 3907925) B3907925
theorem B2769137 : Blo 511796 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B770291 : Blo 511796 770291 := bstep (se 1 (by rfl) ⟨577718, by rfl⟩ : syracuseStep 770291 = 1155437) B1155437
theorem B1458445 : Blo 511796 1458445 := bstep (se 3 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 1458445 = 546917) B546917
theorem B770321 : Blo 511796 770321 := bstep (se 2 (by rfl) ⟨288870, by rfl⟩ : syracuseStep 770321 = 577741) B577741
theorem B770339 : Blo 511796 770339 := bstep (se 1 (by rfl) ⟨577754, by rfl⟩ : syracuseStep 770339 = 1155509) B1155509
theorem B868657 : Blo 511796 868657 := bstep (se 2 (by rfl) ⟨325746, by rfl⟩ : syracuseStep 868657 = 651493) B651493
theorem B770369 : Blo 511796 770369 := bstep (se 2 (by rfl) ⟨288888, by rfl⟩ : syracuseStep 770369 = 577777) B577777
theorem B2769221 : Blo 511796 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B770387 : Blo 511796 770387 := bstep (se 1 (by rfl) ⟨577790, by rfl⟩ : syracuseStep 770387 = 1155581) B1155581
theorem B868691 : Blo 511796 868691 := bstep (se 1 (by rfl) ⟨651518, by rfl⟩ : syracuseStep 868691 = 1303037) B1303037
theorem B770417 : Blo 511796 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B770435 : Blo 511796 770435 := bstep (se 1 (by rfl) ⟨577826, by rfl⟩ : syracuseStep 770435 = 1155653) B1155653
theorem B770465 : Blo 511796 770465 := bstep (se 2 (by rfl) ⟨288924, by rfl⟩ : syracuseStep 770465 = 577849) B577849
theorem B770483 : Blo 511796 770483 := bstep (se 1 (by rfl) ⟨577862, by rfl⟩ : syracuseStep 770483 = 1155725) B1155725
theorem B770513 : Blo 511796 770513 := bstep (se 2 (by rfl) ⟨288942, by rfl⟩ : syracuseStep 770513 = 577885) B577885
theorem B868819 : Blo 511796 868819 := bstep (se 1 (by rfl) ⟨651614, by rfl⟩ : syracuseStep 868819 = 1303229) B1303229
theorem B770531 : Blo 511796 770531 := bstep (se 1 (by rfl) ⟨577898, by rfl⟩ : syracuseStep 770531 = 1155797) B1155797
theorem B770561 : Blo 511796 770561 := bstep (se 2 (by rfl) ⟨288960, by rfl⟩ : syracuseStep 770561 = 577921) B577921
theorem B770579 : Blo 511796 770579 := bstep (se 1 (by rfl) ⟨577934, by rfl⟩ : syracuseStep 770579 = 1155869) B1155869
theorem B1950257 : Blo 511796 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B770609 : Blo 511796 770609 := bstep (se 2 (by rfl) ⟨288978, by rfl⟩ : syracuseStep 770609 = 577957) B577957
theorem B770627 : Blo 511796 770627 := bstep (se 1 (by rfl) ⟨577970, by rfl⟩ : syracuseStep 770627 = 1155941) B1155941
theorem B770657 : Blo 511796 770657 := bstep (se 2 (by rfl) ⟨288996, by rfl⟩ : syracuseStep 770657 = 577993) B577993
theorem B868961 : Blo 511796 868961 := bstep (se 2 (by rfl) ⟨325860, by rfl⟩ : syracuseStep 868961 = 651721) B651721
theorem B1098353 : Blo 511796 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B770675 : Blo 511796 770675 := bstep (se 1 (by rfl) ⟨578006, by rfl⟩ : syracuseStep 770675 = 1156013) B1156013
theorem B770705 : Blo 511796 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B770723 : Blo 511796 770723 := bstep (se 1 (by rfl) ⟨578042, by rfl⟩ : syracuseStep 770723 = 1156085) B1156085
theorem B770753 : Blo 511796 770753 := bstep (se 2 (by rfl) ⟨289032, by rfl⟩ : syracuseStep 770753 = 578065) B578065
theorem B770771 : Blo 511796 770771 := bstep (se 1 (by rfl) ⟨578078, by rfl⟩ : syracuseStep 770771 = 1156157) B1156157
theorem B869089 : Blo 511796 869089 := bstep (se 2 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 869089 = 651817) B651817
theorem B770801 : Blo 511796 770801 := bstep (se 2 (by rfl) ⟨289050, by rfl⟩ : syracuseStep 770801 = 578101) B578101
theorem B770819 : Blo 511796 770819 := bstep (se 1 (by rfl) ⟨578114, by rfl⟩ : syracuseStep 770819 = 1156229) B1156229
theorem B869123 : Blo 511796 869123 := bstep (se 1 (by rfl) ⟨651842, by rfl⟩ : syracuseStep 869123 = 1303685) B1303685
theorem B770849 : Blo 511796 770849 := bstep (se 2 (by rfl) ⟨289068, by rfl⟩ : syracuseStep 770849 = 578137) B578137
theorem B770867 : Blo 511796 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B770897 : Blo 511796 770897 := bstep (se 2 (by rfl) ⟨289086, by rfl⟩ : syracuseStep 770897 = 578173) B578173
theorem B770915 : Blo 511796 770915 := bstep (se 1 (by rfl) ⟨578186, by rfl⟩ : syracuseStep 770915 = 1156373) B1156373
theorem B770945 : Blo 511796 770945 := bstep (se 2 (by rfl) ⟨289104, by rfl⟩ : syracuseStep 770945 = 578209) B578209
theorem B869251 : Blo 511796 869251 := bstep (se 1 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 869251 = 1303877) B1303877
theorem B770963 : Blo 511796 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B770993 : Blo 511796 770993 := bstep (se 2 (by rfl) ⟨289122, by rfl⟩ : syracuseStep 770993 = 578245) B578245
theorem B771011 : Blo 511796 771011 := bstep (se 1 (by rfl) ⟨578258, by rfl⟩ : syracuseStep 771011 = 1156517) B1156517
theorem B771041 : Blo 511796 771041 := bstep (se 2 (by rfl) ⟨289140, by rfl⟩ : syracuseStep 771041 = 578281) B578281
theorem B2999281 : Blo 511796 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B771059 : Blo 511796 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B1098755 : Blo 511796 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B2606093 : Blo 511796 2606093 := bstep (se 3 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 2606093 = 977285) B977285
theorem B771089 : Blo 511796 771089 := bstep (se 2 (by rfl) ⟨289158, by rfl⟩ : syracuseStep 771089 = 578317) B578317
theorem B869393 : Blo 511796 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B771107 : Blo 511796 771107 := bstep (se 1 (by rfl) ⟨578330, by rfl⟩ : syracuseStep 771107 = 1156661) B1156661
theorem B771137 : Blo 511796 771137 := bstep (se 2 (by rfl) ⟨289176, by rfl⟩ : syracuseStep 771137 = 578353) B578353
theorem B771155 : Blo 511796 771155 := bstep (se 1 (by rfl) ⟨578366, by rfl⟩ : syracuseStep 771155 = 1156733) B1156733
theorem B771185 : Blo 511796 771185 := bstep (se 2 (by rfl) ⟨289194, by rfl⟩ : syracuseStep 771185 = 578389) B578389
theorem B771203 : Blo 511796 771203 := bstep (se 1 (by rfl) ⟨578402, by rfl⟩ : syracuseStep 771203 = 1156805) B1156805
theorem B3294341 : Blo 511796 3294341 := bstep (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) B617689
theorem B869521 : Blo 511796 869521 := bstep (se 2 (by rfl) ⟨326070, by rfl⟩ : syracuseStep 869521 = 652141) B652141
theorem B771233 : Blo 511796 771233 := bstep (se 2 (by rfl) ⟨289212, by rfl⟩ : syracuseStep 771233 = 578425) B578425
theorem B771251 : Blo 511796 771251 := bstep (se 1 (by rfl) ⟨578438, by rfl⟩ : syracuseStep 771251 = 1156877) B1156877
theorem B869555 : Blo 511796 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B6571205 : Blo 511796 6571205 := bstep (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) B1232101
theorem B1950925 : Blo 511796 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B771281 : Blo 511796 771281 := bstep (se 2 (by rfl) ⟨289230, by rfl⟩ : syracuseStep 771281 = 578461) B578461
theorem B771299 : Blo 511796 771299 := bstep (se 1 (by rfl) ⟨578474, by rfl⟩ : syracuseStep 771299 = 1156949) B1156949
theorem B771329 : Blo 511796 771329 := bstep (se 2 (by rfl) ⟨289248, by rfl⟩ : syracuseStep 771329 = 578497) B578497
theorem B771347 : Blo 511796 771347 := bstep (se 1 (by rfl) ⟨578510, by rfl⟩ : syracuseStep 771347 = 1157021) B1157021
theorem B771377 : Blo 511796 771377 := bstep (se 2 (by rfl) ⟨289266, by rfl⟩ : syracuseStep 771377 = 578533) B578533
theorem B869683 : Blo 511796 869683 := bstep (se 1 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 869683 = 1304525) B1304525
theorem B771395 : Blo 511796 771395 := bstep (se 1 (by rfl) ⟨578546, by rfl⟩ : syracuseStep 771395 = 1157093) B1157093
theorem B771425 : Blo 511796 771425 := bstep (se 2 (by rfl) ⟨289284, by rfl⟩ : syracuseStep 771425 = 578569) B578569
theorem B771443 : Blo 511796 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B1295747 : Blo 511796 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B771473 : Blo 511796 771473 := bstep (se 2 (by rfl) ⟨289302, by rfl⟩ : syracuseStep 771473 = 578605) B578605
theorem B771491 : Blo 511796 771491 := bstep (se 1 (by rfl) ⟨578618, by rfl⟩ : syracuseStep 771491 = 1157237) B1157237
theorem B771521 : Blo 511796 771521 := bstep (se 2 (by rfl) ⟨289320, by rfl⟩ : syracuseStep 771521 = 578641) B578641
theorem B869825 : Blo 511796 869825 := bstep (se 2 (by rfl) ⟨326184, by rfl⟩ : syracuseStep 869825 = 652369) B652369
theorem B771539 : Blo 511796 771539 := bstep (se 1 (by rfl) ⟨578654, by rfl⟩ : syracuseStep 771539 = 1157309) B1157309
theorem B771569 : Blo 511796 771569 := bstep (se 2 (by rfl) ⟨289338, by rfl⟩ : syracuseStep 771569 = 578677) B578677
theorem B771587 : Blo 511796 771587 := bstep (se 1 (by rfl) ⟨578690, by rfl⟩ : syracuseStep 771587 = 1157381) B1157381
theorem B771617 : Blo 511796 771617 := bstep (se 2 (by rfl) ⟨289356, by rfl⟩ : syracuseStep 771617 = 578713) B578713
theorem B771635 : Blo 511796 771635 := bstep (se 1 (by rfl) ⟨578726, by rfl⟩ : syracuseStep 771635 = 1157453) B1157453
theorem B869953 : Blo 511796 869953 := bstep (se 2 (by rfl) ⟨326232, by rfl⟩ : syracuseStep 869953 = 652465) B652465
theorem B1295939 : Blo 511796 1295939 := bstep (se 1 (by rfl) ⟨971954, by rfl⟩ : syracuseStep 1295939 = 1943909) B1943909
theorem B771665 : Blo 511796 771665 := bstep (se 2 (by rfl) ⟨289374, by rfl⟩ : syracuseStep 771665 = 578749) B578749
theorem B771683 : Blo 511796 771683 := bstep (se 1 (by rfl) ⟨578762, by rfl⟩ : syracuseStep 771683 = 1157525) B1157525
theorem B869987 : Blo 511796 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B771713 : Blo 511796 771713 := bstep (se 2 (by rfl) ⟨289392, by rfl⟩ : syracuseStep 771713 = 578785) B578785
theorem B771731 : Blo 511796 771731 := bstep (se 1 (by rfl) ⟨578798, by rfl⟩ : syracuseStep 771731 = 1157597) B1157597
theorem B771761 : Blo 511796 771761 := bstep (se 2 (by rfl) ⟨289410, by rfl⟩ : syracuseStep 771761 = 578821) B578821
theorem B771779 : Blo 511796 771779 := bstep (se 1 (by rfl) ⟨578834, by rfl⟩ : syracuseStep 771779 = 1157669) B1157669
theorem B771809 : Blo 511796 771809 := bstep (se 2 (by rfl) ⟨289428, by rfl⟩ : syracuseStep 771809 = 578857) B578857
theorem B870115 : Blo 511796 870115 := bstep (se 1 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 870115 = 1305173) B1305173
theorem B771827 : Blo 511796 771827 := bstep (se 1 (by rfl) ⟨578870, by rfl⟩ : syracuseStep 771827 = 1157741) B1157741
theorem B771857 : Blo 511796 771857 := bstep (se 2 (by rfl) ⟨289446, by rfl⟩ : syracuseStep 771857 = 578893) B578893
theorem B837395 : Blo 511796 837395 := bstep (se 1 (by rfl) ⟨628046, by rfl⟩ : syracuseStep 837395 = 1256093) B1256093
theorem B771875 : Blo 511796 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B771905 : Blo 511796 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B771923 : Blo 511796 771923 := bstep (se 1 (by rfl) ⟨578942, by rfl⟩ : syracuseStep 771923 = 1157885) B1157885
theorem B837473 : Blo 511796 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B771953 : Blo 511796 771953 := bstep (se 2 (by rfl) ⟨289482, by rfl⟩ : syracuseStep 771953 = 578965) B578965
theorem B870257 : Blo 511796 870257 := bstep (se 2 (by rfl) ⟨326346, by rfl⟩ : syracuseStep 870257 = 652693) B652693
theorem B771971 : Blo 511796 771971 := bstep (se 1 (by rfl) ⟨578978, by rfl⟩ : syracuseStep 771971 = 1157957) B1157957
theorem B1099651 : Blo 511796 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B772001 : Blo 511796 772001 := bstep (se 2 (by rfl) ⟨289500, by rfl⟩ : syracuseStep 772001 = 579001) B579001
theorem B772019 : Blo 511796 772019 := bstep (se 1 (by rfl) ⟨579014, by rfl⟩ : syracuseStep 772019 = 1158029) B1158029
theorem B2344909 : Blo 511796 2344909 := bstep (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) B879341
theorem B1460177 : Blo 511796 1460177 := bstep (se 2 (by rfl) ⟨547566, by rfl⟩ : syracuseStep 1460177 = 1095133) B1095133
theorem B772049 : Blo 511796 772049 := bstep (se 2 (by rfl) ⟨289518, by rfl⟩ : syracuseStep 772049 = 579037) B579037
theorem B1951715 : Blo 511796 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B772067 : Blo 511796 772067 := bstep (se 1 (by rfl) ⟨579050, by rfl⟩ : syracuseStep 772067 = 1158101) B1158101
theorem B870385 : Blo 511796 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B772097 : Blo 511796 772097 := bstep (se 2 (by rfl) ⟨289536, by rfl⟩ : syracuseStep 772097 = 579073) B579073
theorem B772115 : Blo 511796 772115 := bstep (se 1 (by rfl) ⟨579086, by rfl⟩ : syracuseStep 772115 = 1158173) B1158173
theorem B772145 : Blo 511796 772145 := bstep (se 2 (by rfl) ⟨289554, by rfl⟩ : syracuseStep 772145 = 579109) B579109
theorem B772163 : Blo 511796 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B772193 : Blo 511796 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B772211 : Blo 511796 772211 := bstep (se 1 (by rfl) ⟨579158, by rfl⟩ : syracuseStep 772211 = 1158317) B1158317
theorem B1460369 : Blo 511796 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B772241 : Blo 511796 772241 := bstep (se 2 (by rfl) ⟨289590, by rfl⟩ : syracuseStep 772241 = 579181) B579181
theorem B772259 : Blo 511796 772259 := bstep (se 1 (by rfl) ⟨579194, by rfl⟩ : syracuseStep 772259 = 1158389) B1158389
theorem B772289 : Blo 511796 772289 := bstep (se 2 (by rfl) ⟨289608, by rfl⟩ : syracuseStep 772289 = 579217) B579217
theorem B772307 : Blo 511796 772307 := bstep (se 1 (by rfl) ⟨579230, by rfl⟩ : syracuseStep 772307 = 1158461) B1158461
theorem B772337 : Blo 511796 772337 := bstep (se 2 (by rfl) ⟨289626, by rfl⟩ : syracuseStep 772337 = 579253) B579253
theorem B772355 : Blo 511796 772355 := bstep (se 1 (by rfl) ⟨579266, by rfl⟩ : syracuseStep 772355 = 1158533) B1158533
theorem B772385 : Blo 511796 772385 := bstep (se 2 (by rfl) ⟨289644, by rfl⟩ : syracuseStep 772385 = 579289) B579289
theorem B575779 : Blo 511796 575779 := bstep (se 1 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 575779 = 863669) B863669
theorem B772403 : Blo 511796 772403 := bstep (se 1 (by rfl) ⟨579302, by rfl⟩ : syracuseStep 772403 = 1158605) B1158605
theorem B772433 : Blo 511796 772433 := bstep (se 2 (by rfl) ⟨289662, by rfl⟩ : syracuseStep 772433 = 579325) B579325
theorem B772451 : Blo 511796 772451 := bstep (se 1 (by rfl) ⟨579338, by rfl⟩ : syracuseStep 772451 = 1158677) B1158677
theorem B772481 : Blo 511796 772481 := bstep (se 2 (by rfl) ⟨289680, by rfl⟩ : syracuseStep 772481 = 579361) B579361
theorem B772499 : Blo 511796 772499 := bstep (se 1 (by rfl) ⟨579374, by rfl⟩ : syracuseStep 772499 = 1158749) B1158749
theorem B772529 : Blo 511796 772529 := bstep (se 2 (by rfl) ⟨289698, by rfl⟩ : syracuseStep 772529 = 579397) B579397
theorem B575923 : Blo 511796 575923 := bstep (se 1 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 575923 = 863885) B863885
theorem B772547 : Blo 511796 772547 := bstep (se 1 (by rfl) ⟨579410, by rfl⟩ : syracuseStep 772547 = 1158821) B1158821
theorem B772577 : Blo 511796 772577 := bstep (se 2 (by rfl) ⟨289716, by rfl⟩ : syracuseStep 772577 = 579433) B579433
theorem B1296881 : Blo 511796 1296881 := bstep (se 2 (by rfl) ⟨486330, by rfl⟩ : syracuseStep 1296881 = 972661) B972661
theorem B772595 : Blo 511796 772595 := bstep (se 1 (by rfl) ⟨579446, by rfl⟩ : syracuseStep 772595 = 1158893) B1158893
theorem B772625 : Blo 511796 772625 := bstep (se 2 (by rfl) ⟨289734, by rfl⟩ : syracuseStep 772625 = 579469) B579469
theorem B1296931 : Blo 511796 1296931 := bstep (se 1 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 1296931 = 1945397) B1945397
theorem B772643 : Blo 511796 772643 := bstep (se 1 (by rfl) ⟨579482, by rfl⟩ : syracuseStep 772643 = 1158965) B1158965
theorem B772673 : Blo 511796 772673 := bstep (se 2 (by rfl) ⟨289752, by rfl⟩ : syracuseStep 772673 = 579505) B579505
theorem B576067 : Blo 511796 576067 := bstep (se 1 (by rfl) ⟨432050, by rfl⟩ : syracuseStep 576067 = 864101) B864101
theorem B772691 : Blo 511796 772691 := bstep (se 1 (by rfl) ⟨579518, by rfl⟩ : syracuseStep 772691 = 1159037) B1159037
theorem B1952369 : Blo 511796 1952369 := bstep (se 2 (by rfl) ⟨732138, by rfl⟩ : syracuseStep 1952369 = 1464277) B1464277
theorem B772721 : Blo 511796 772721 := bstep (se 2 (by rfl) ⟨289770, by rfl⟩ : syracuseStep 772721 = 579541) B579541
theorem B772739 : Blo 511796 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B772769 : Blo 511796 772769 := bstep (se 2 (by rfl) ⟨289788, by rfl⟩ : syracuseStep 772769 = 579577) B579577
theorem B1297073 : Blo 511796 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B772787 : Blo 511796 772787 := bstep (se 1 (by rfl) ⟨579590, by rfl⟩ : syracuseStep 772787 = 1159181) B1159181
theorem B772817 : Blo 511796 772817 := bstep (se 2 (by rfl) ⟨289806, by rfl⟩ : syracuseStep 772817 = 579613) B579613
theorem B576211 : Blo 511796 576211 := bstep (se 1 (by rfl) ⟨432158, by rfl⟩ : syracuseStep 576211 = 864317) B864317
theorem B772835 : Blo 511796 772835 := bstep (se 1 (by rfl) ⟨579626, by rfl⟩ : syracuseStep 772835 = 1159253) B1159253
theorem B772865 : Blo 511796 772865 := bstep (se 2 (by rfl) ⟨289824, by rfl⟩ : syracuseStep 772865 = 579649) B579649
theorem B772883 : Blo 511796 772883 := bstep (se 1 (by rfl) ⟨579662, by rfl⟩ : syracuseStep 772883 = 1159325) B1159325
theorem B3132209 : Blo 511796 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B772913 : Blo 511796 772913 := bstep (se 2 (by rfl) ⟨289842, by rfl⟩ : syracuseStep 772913 = 579685) B579685
theorem B772931 : Blo 511796 772931 := bstep (se 1 (by rfl) ⟨579698, by rfl⟩ : syracuseStep 772931 = 1159397) B1159397
theorem B772961 : Blo 511796 772961 := bstep (se 2 (by rfl) ⟨289860, by rfl⟩ : syracuseStep 772961 = 579721) B579721
theorem B576355 : Blo 511796 576355 := bstep (se 1 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 576355 = 864533) B864533
theorem B772979 : Blo 511796 772979 := bstep (se 1 (by rfl) ⟨579734, by rfl⟩ : syracuseStep 772979 = 1159469) B1159469
theorem B773009 : Blo 511796 773009 := bstep (se 2 (by rfl) ⟨289878, by rfl⟩ : syracuseStep 773009 = 579757) B579757
theorem B773027 : Blo 511796 773027 := bstep (se 1 (by rfl) ⟨579770, by rfl⟩ : syracuseStep 773027 = 1159541) B1159541
theorem B773057 : Blo 511796 773057 := bstep (se 2 (by rfl) ⟨289896, by rfl⟩ : syracuseStep 773057 = 579793) B579793
theorem B7392197 : Blo 511796 7392197 := bstep (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) B1386037
theorem B773075 : Blo 511796 773075 := bstep (se 1 (by rfl) ⟨579806, by rfl⟩ : syracuseStep 773075 = 1159613) B1159613
theorem B773105 : Blo 511796 773105 := bstep (se 2 (by rfl) ⟨289914, by rfl⟩ : syracuseStep 773105 = 579829) B579829
theorem B576499 : Blo 511796 576499 := bstep (se 1 (by rfl) ⟨432374, by rfl⟩ : syracuseStep 576499 = 864749) B864749
theorem B773123 : Blo 511796 773123 := bstep (se 1 (by rfl) ⟨579842, by rfl⟩ : syracuseStep 773123 = 1159685) B1159685
theorem B773153 : Blo 511796 773153 := bstep (se 2 (by rfl) ⟨289932, by rfl⟩ : syracuseStep 773153 = 579865) B579865
theorem B1756205 : Blo 511796 1756205 := bstep (se 3 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 1756205 = 658577) B658577
theorem B773171 : Blo 511796 773171 := bstep (se 1 (by rfl) ⟨579878, by rfl⟩ : syracuseStep 773171 = 1159757) B1159757
theorem B1100881 : Blo 511796 1100881 := bstep (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) B825661
theorem B773201 : Blo 511796 773201 := bstep (se 2 (by rfl) ⟨289950, by rfl⟩ : syracuseStep 773201 = 579901) B579901
theorem B773219 : Blo 511796 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B1461361 : Blo 511796 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B773249 : Blo 511796 773249 := bstep (se 2 (by rfl) ⟨289968, by rfl⟩ : syracuseStep 773249 = 579937) B579937
theorem B576643 : Blo 511796 576643 := bstep (se 1 (by rfl) ⟨432482, by rfl⟩ : syracuseStep 576643 = 864965) B864965
theorem B773267 : Blo 511796 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B773297 : Blo 511796 773297 := bstep (se 2 (by rfl) ⟨289986, by rfl⟩ : syracuseStep 773297 = 579973) B579973
theorem B773315 : Blo 511796 773315 := bstep (se 1 (by rfl) ⟨579986, by rfl⟩ : syracuseStep 773315 = 1159973) B1159973
theorem B773345 : Blo 511796 773345 := bstep (se 2 (by rfl) ⟨290004, by rfl⟩ : syracuseStep 773345 = 580009) B580009
theorem B4377827 : Blo 511796 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B773363 : Blo 511796 773363 := bstep (se 1 (by rfl) ⟨580022, by rfl⟩ : syracuseStep 773363 = 1160045) B1160045
theorem B773393 : Blo 511796 773393 := bstep (se 2 (by rfl) ⟨290022, by rfl⟩ : syracuseStep 773393 = 580045) B580045
theorem B576787 : Blo 511796 576787 := bstep (se 1 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 576787 = 865181) B865181
theorem B773411 : Blo 511796 773411 := bstep (se 1 (by rfl) ⟨580058, by rfl⟩ : syracuseStep 773411 = 1160117) B1160117
theorem B773441 : Blo 511796 773441 := bstep (se 2 (by rfl) ⟨290040, by rfl⟩ : syracuseStep 773441 = 580081) B580081
theorem B773459 : Blo 511796 773459 := bstep (se 1 (by rfl) ⟨580094, by rfl⟩ : syracuseStep 773459 = 1160189) B1160189
theorem B773489 : Blo 511796 773489 := bstep (se 2 (by rfl) ⟨290058, by rfl⟩ : syracuseStep 773489 = 580117) B580117
theorem B1461635 : Blo 511796 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B773507 : Blo 511796 773507 := bstep (se 1 (by rfl) ⟨580130, by rfl⟩ : syracuseStep 773507 = 1160261) B1160261
theorem B773537 : Blo 511796 773537 := bstep (se 2 (by rfl) ⟨290076, by rfl⟩ : syracuseStep 773537 = 580153) B580153
theorem B576931 : Blo 511796 576931 := bstep (se 1 (by rfl) ⟨432698, by rfl⟩ : syracuseStep 576931 = 865397) B865397
theorem B773555 : Blo 511796 773555 := bstep (se 1 (by rfl) ⟨580166, by rfl⟩ : syracuseStep 773555 = 1160333) B1160333
theorem B773585 : Blo 511796 773585 := bstep (se 2 (by rfl) ⟨290094, by rfl⟩ : syracuseStep 773585 = 580189) B580189
theorem B773603 : Blo 511796 773603 := bstep (se 1 (by rfl) ⟨580202, by rfl⟩ : syracuseStep 773603 = 1160405) B1160405
theorem B773633 : Blo 511796 773633 := bstep (se 2 (by rfl) ⟨290112, by rfl⟩ : syracuseStep 773633 = 580225) B580225
theorem B773651 : Blo 511796 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B773681 : Blo 511796 773681 := bstep (se 2 (by rfl) ⟨290130, by rfl⟩ : syracuseStep 773681 = 580261) B580261
theorem B577075 : Blo 511796 577075 := bstep (se 1 (by rfl) ⟨432806, by rfl⟩ : syracuseStep 577075 = 865613) B865613
theorem B1461827 : Blo 511796 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B740945 : Blo 511796 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B1298065 : Blo 511796 1298065 := bstep (se 2 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 1298065 = 973549) B973549
theorem B1756835 : Blo 511796 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B577219 : Blo 511796 577219 := bstep (se 1 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 577219 = 865829) B865829
theorem B5557987 : Blo 511796 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B2084621 : Blo 511796 2084621 := bstep (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) B781733
theorem B511811 : Blo 511796 511811 := bstep (se 1 (by rfl) ⟨383858, by rfl⟩ : syracuseStep 511811 = 767717) B767717
theorem B511827 : Blo 511796 511827 := bstep (se 1 (by rfl) ⟨383870, by rfl⟩ : syracuseStep 511827 = 767741) B767741
theorem B577363 : Blo 511796 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B511843 : Blo 511796 511843 := bstep (se 1 (by rfl) ⟨383882, by rfl⟩ : syracuseStep 511843 = 767765) B767765
theorem B741233 : Blo 511796 741233 := bstep (se 2 (by rfl) ⟨277962, by rfl⟩ : syracuseStep 741233 = 555925) B555925
theorem B2609009 : Blo 511796 2609009 := bstep (se 2 (by rfl) ⟨978378, by rfl⟩ : syracuseStep 2609009 = 1956757) B1956757
theorem B511859 : Blo 511796 511859 := bstep (se 1 (by rfl) ⟨383894, by rfl⟩ : syracuseStep 511859 = 767789) B767789
theorem B511875 : Blo 511796 511875 := bstep (se 1 (by rfl) ⟨383906, by rfl⟩ : syracuseStep 511875 = 767813) B767813
theorem B511891 : Blo 511796 511891 := bstep (se 1 (by rfl) ⟨383918, by rfl⟩ : syracuseStep 511891 = 767837) B767837
theorem B511907 : Blo 511796 511907 := bstep (se 1 (by rfl) ⟨383930, by rfl⟩ : syracuseStep 511907 = 767861) B767861
theorem B1298339 : Blo 511796 1298339 := bstep (se 1 (by rfl) ⟨973754, by rfl⟩ : syracuseStep 1298339 = 1947509) B1947509
theorem B511923 : Blo 511796 511923 := bstep (se 1 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 511923 = 767885) B767885
theorem B511939 : Blo 511796 511939 := bstep (se 1 (by rfl) ⟨383954, by rfl⟩ : syracuseStep 511939 = 767909) B767909
theorem B511955 : Blo 511796 511955 := bstep (se 1 (by rfl) ⟨383966, by rfl⟩ : syracuseStep 511955 = 767933) B767933
theorem B511971 : Blo 511796 511971 := bstep (se 1 (by rfl) ⟨383978, by rfl⟩ : syracuseStep 511971 = 767957) B767957
theorem B577507 : Blo 511796 577507 := bstep (se 1 (by rfl) ⟨433130, by rfl⟩ : syracuseStep 577507 = 866261) B866261
theorem B511987 : Blo 511796 511987 := bstep (se 1 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 511987 = 767981) B767981
theorem B512003 : Blo 511796 512003 := bstep (se 1 (by rfl) ⟨384002, by rfl⟩ : syracuseStep 512003 = 768005) B768005
theorem B512019 : Blo 511796 512019 := bstep (se 1 (by rfl) ⟨384014, by rfl⟩ : syracuseStep 512019 = 768029) B768029
theorem B512035 : Blo 511796 512035 := bstep (se 1 (by rfl) ⟨384026, by rfl⟩ : syracuseStep 512035 = 768053) B768053
theorem B1953827 : Blo 511796 1953827 := bstep (se 1 (by rfl) ⟨1465370, by rfl⟩ : syracuseStep 1953827 = 2930741) B2930741
theorem B1953841 : Blo 511796 1953841 := bstep (se 2 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 1953841 = 1465381) B1465381
theorem B512051 : Blo 511796 512051 := bstep (se 1 (by rfl) ⟨384038, by rfl⟩ : syracuseStep 512051 = 768077) B768077
theorem B512067 : Blo 511796 512067 := bstep (se 1 (by rfl) ⟨384050, by rfl⟩ : syracuseStep 512067 = 768101) B768101
theorem B512083 : Blo 511796 512083 := bstep (se 1 (by rfl) ⟨384062, by rfl⟩ : syracuseStep 512083 = 768125) B768125
theorem B512099 : Blo 511796 512099 := bstep (se 1 (by rfl) ⟨384074, by rfl⟩ : syracuseStep 512099 = 768149) B768149
theorem B1298531 : Blo 511796 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B512115 : Blo 511796 512115 := bstep (se 1 (by rfl) ⟨384086, by rfl⟩ : syracuseStep 512115 = 768173) B768173
theorem B577651 : Blo 511796 577651 := bstep (se 1 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 577651 = 866477) B866477
theorem B512131 : Blo 511796 512131 := bstep (se 1 (by rfl) ⟨384098, by rfl⟩ : syracuseStep 512131 = 768197) B768197
theorem B512147 : Blo 511796 512147 := bstep (se 1 (by rfl) ⟨384110, by rfl⟩ : syracuseStep 512147 = 768221) B768221
theorem B512163 : Blo 511796 512163 := bstep (se 1 (by rfl) ⟨384122, by rfl⟩ : syracuseStep 512163 = 768245) B768245
theorem B512179 : Blo 511796 512179 := bstep (se 1 (by rfl) ⟨384134, by rfl⟩ : syracuseStep 512179 = 768269) B768269
theorem B512195 : Blo 511796 512195 := bstep (se 1 (by rfl) ⟨384146, by rfl⟩ : syracuseStep 512195 = 768293) B768293
theorem B512211 : Blo 511796 512211 := bstep (se 1 (by rfl) ⟨384158, by rfl⟩ : syracuseStep 512211 = 768317) B768317
theorem B512227 : Blo 511796 512227 := bstep (se 1 (by rfl) ⟨384170, by rfl⟩ : syracuseStep 512227 = 768341) B768341
theorem B512243 : Blo 511796 512243 := bstep (se 1 (by rfl) ⟨384182, by rfl⟩ : syracuseStep 512243 = 768365) B768365
theorem B512259 : Blo 511796 512259 := bstep (se 1 (by rfl) ⟨384194, by rfl⟩ : syracuseStep 512259 = 768389) B768389
theorem B577795 : Blo 511796 577795 := bstep (se 1 (by rfl) ⟨433346, by rfl⟩ : syracuseStep 577795 = 866693) B866693
theorem B512275 : Blo 511796 512275 := bstep (se 1 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 512275 = 768413) B768413
theorem B512291 : Blo 511796 512291 := bstep (se 1 (by rfl) ⟨384218, by rfl⟩ : syracuseStep 512291 = 768437) B768437
theorem B512307 : Blo 511796 512307 := bstep (se 1 (by rfl) ⟨384230, by rfl⟩ : syracuseStep 512307 = 768461) B768461
theorem B512323 : Blo 511796 512323 := bstep (se 1 (by rfl) ⟨384242, by rfl⟩ : syracuseStep 512323 = 768485) B768485
theorem B512339 : Blo 511796 512339 := bstep (se 1 (by rfl) ⟨384254, by rfl⟩ : syracuseStep 512339 = 768509) B768509
theorem B512355 : Blo 511796 512355 := bstep (se 1 (by rfl) ⟨384266, by rfl⟩ : syracuseStep 512355 = 768533) B768533
theorem B1462637 : Blo 511796 1462637 := bstep (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) B548489
theorem B512371 : Blo 511796 512371 := bstep (se 1 (by rfl) ⟨384278, by rfl⟩ : syracuseStep 512371 = 768557) B768557
theorem B512387 : Blo 511796 512387 := bstep (se 1 (by rfl) ⟨384290, by rfl⟩ : syracuseStep 512387 = 768581) B768581
theorem B512403 : Blo 511796 512403 := bstep (se 1 (by rfl) ⟨384302, by rfl⟩ : syracuseStep 512403 = 768605) B768605
theorem B577939 : Blo 511796 577939 := bstep (se 1 (by rfl) ⟨433454, by rfl⟩ : syracuseStep 577939 = 866909) B866909
theorem B512419 : Blo 511796 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B512435 : Blo 511796 512435 := bstep (se 1 (by rfl) ⟨384326, by rfl⟩ : syracuseStep 512435 = 768653) B768653
theorem B512451 : Blo 511796 512451 := bstep (se 1 (by rfl) ⟨384338, by rfl⟩ : syracuseStep 512451 = 768677) B768677
theorem B512467 : Blo 511796 512467 := bstep (se 1 (by rfl) ⟨384350, by rfl⟩ : syracuseStep 512467 = 768701) B768701
theorem B512483 : Blo 511796 512483 := bstep (se 1 (by rfl) ⟨384362, by rfl⟩ : syracuseStep 512483 = 768725) B768725
theorem B512499 : Blo 511796 512499 := bstep (se 1 (by rfl) ⟨384374, by rfl⟩ : syracuseStep 512499 = 768749) B768749
theorem B512515 : Blo 511796 512515 := bstep (se 1 (by rfl) ⟨384386, by rfl⟩ : syracuseStep 512515 = 768773) B768773
theorem B512531 : Blo 511796 512531 := bstep (se 1 (by rfl) ⟨384398, by rfl⟩ : syracuseStep 512531 = 768797) B768797
theorem B512547 : Blo 511796 512547 := bstep (se 1 (by rfl) ⟨384410, by rfl⟩ : syracuseStep 512547 = 768821) B768821
theorem B1462819 : Blo 511796 1462819 := bstep (se 1 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 1462819 = 2194229) B2194229
theorem B578083 : Blo 511796 578083 := bstep (se 1 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 578083 = 867125) B867125
theorem B512563 : Blo 511796 512563 := bstep (se 1 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 512563 = 768845) B768845
theorem B512579 : Blo 511796 512579 := bstep (se 1 (by rfl) ⟨384434, by rfl⟩ : syracuseStep 512579 = 768869) B768869
theorem B512595 : Blo 511796 512595 := bstep (se 1 (by rfl) ⟨384446, by rfl⟩ : syracuseStep 512595 = 768893) B768893
theorem B512611 : Blo 511796 512611 := bstep (se 1 (by rfl) ⟨384458, by rfl⟩ : syracuseStep 512611 = 768917) B768917
theorem B1692269 : Blo 511796 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B3297905 : Blo 511796 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B512627 : Blo 511796 512627 := bstep (se 1 (by rfl) ⟨384470, by rfl⟩ : syracuseStep 512627 = 768941) B768941
theorem B512643 : Blo 511796 512643 := bstep (se 1 (by rfl) ⟨384482, by rfl⟩ : syracuseStep 512643 = 768965) B768965
theorem B512659 : Blo 511796 512659 := bstep (se 1 (by rfl) ⟨384494, by rfl⟩ : syracuseStep 512659 = 768989) B768989
theorem B512675 : Blo 511796 512675 := bstep (se 1 (by rfl) ⟨384506, by rfl⟩ : syracuseStep 512675 = 769013) B769013
theorem B1233571 : Blo 511796 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B512691 : Blo 511796 512691 := bstep (se 1 (by rfl) ⟨384518, by rfl⟩ : syracuseStep 512691 = 769037) B769037
theorem B578227 : Blo 511796 578227 := bstep (se 1 (by rfl) ⟨433670, by rfl⟩ : syracuseStep 578227 = 867341) B867341
theorem B512707 : Blo 511796 512707 := bstep (se 1 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 512707 = 769061) B769061
theorem B512723 : Blo 511796 512723 := bstep (se 1 (by rfl) ⟨384542, by rfl⟩ : syracuseStep 512723 = 769085) B769085
theorem B512739 : Blo 511796 512739 := bstep (se 1 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 512739 = 769109) B769109
theorem B512755 : Blo 511796 512755 := bstep (se 1 (by rfl) ⟨384566, by rfl⟩ : syracuseStep 512755 = 769133) B769133
theorem B512771 : Blo 511796 512771 := bstep (se 1 (by rfl) ⟨384578, by rfl⟩ : syracuseStep 512771 = 769157) B769157
theorem B512787 : Blo 511796 512787 := bstep (se 1 (by rfl) ⟨384590, by rfl⟩ : syracuseStep 512787 = 769181) B769181
theorem B512803 : Blo 511796 512803 := bstep (se 1 (by rfl) ⟨384602, by rfl⟩ : syracuseStep 512803 = 769205) B769205
theorem B512819 : Blo 511796 512819 := bstep (se 1 (by rfl) ⟨384614, by rfl⟩ : syracuseStep 512819 = 769229) B769229
theorem B1168195 : Blo 511796 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B512835 : Blo 511796 512835 := bstep (se 1 (by rfl) ⟨384626, by rfl⟩ : syracuseStep 512835 = 769253) B769253
theorem B578371 : Blo 511796 578371 := bstep (se 1 (by rfl) ⟨433778, by rfl⟩ : syracuseStep 578371 = 867557) B867557
theorem B512851 : Blo 511796 512851 := bstep (se 1 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 512851 = 769277) B769277
theorem B512867 : Blo 511796 512867 := bstep (se 1 (by rfl) ⟨384650, by rfl⟩ : syracuseStep 512867 = 769301) B769301
theorem B512883 : Blo 511796 512883 := bstep (se 1 (by rfl) ⟨384662, by rfl⟩ : syracuseStep 512883 = 769325) B769325
theorem B971651 : Blo 511796 971651 := bstep (se 1 (by rfl) ⟨728738, by rfl⟩ : syracuseStep 971651 = 1457477) B1457477
theorem B512899 : Blo 511796 512899 := bstep (se 1 (by rfl) ⟨384674, by rfl⟩ : syracuseStep 512899 = 769349) B769349
theorem B512915 : Blo 511796 512915 := bstep (se 1 (by rfl) ⟨384686, by rfl⟩ : syracuseStep 512915 = 769373) B769373
theorem B512931 : Blo 511796 512931 := bstep (se 1 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 512931 = 769397) B769397
theorem B512947 : Blo 511796 512947 := bstep (se 1 (by rfl) ⟨384710, by rfl⟩ : syracuseStep 512947 = 769421) B769421
theorem B512963 : Blo 511796 512963 := bstep (se 1 (by rfl) ⟨384722, by rfl⟩ : syracuseStep 512963 = 769445) B769445
theorem B512979 : Blo 511796 512979 := bstep (se 1 (by rfl) ⟨384734, by rfl⟩ : syracuseStep 512979 = 769469) B769469
theorem B578515 : Blo 511796 578515 := bstep (se 1 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 578515 = 867773) B867773
theorem B906209 : Blo 511796 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B512995 : Blo 511796 512995 := bstep (se 1 (by rfl) ⟨384746, by rfl⟩ : syracuseStep 512995 = 769493) B769493
theorem B513011 : Blo 511796 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B513027 : Blo 511796 513027 := bstep (se 1 (by rfl) ⟨384770, by rfl⟩ : syracuseStep 513027 = 769541) B769541
theorem B1463309 : Blo 511796 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B1299473 : Blo 511796 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B513043 : Blo 511796 513043 := bstep (se 1 (by rfl) ⟨384782, by rfl⟩ : syracuseStep 513043 = 769565) B769565
theorem B513059 : Blo 511796 513059 := bstep (se 1 (by rfl) ⟨384794, by rfl⟩ : syracuseStep 513059 = 769589) B769589
theorem B513075 : Blo 511796 513075 := bstep (se 1 (by rfl) ⟨384806, by rfl⟩ : syracuseStep 513075 = 769613) B769613
theorem B513091 : Blo 511796 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B1299523 : Blo 511796 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B513107 : Blo 511796 513107 := bstep (se 1 (by rfl) ⟨384830, by rfl⟩ : syracuseStep 513107 = 769661) B769661
theorem B513123 : Blo 511796 513123 := bstep (se 1 (by rfl) ⟨384842, by rfl⟩ : syracuseStep 513123 = 769685) B769685
theorem B578659 : Blo 511796 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B513139 : Blo 511796 513139 := bstep (se 1 (by rfl) ⟨384854, by rfl⟩ : syracuseStep 513139 = 769709) B769709
theorem B513155 : Blo 511796 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B513171 : Blo 511796 513171 := bstep (se 1 (by rfl) ⟨384878, by rfl⟩ : syracuseStep 513171 = 769757) B769757
theorem B971939 : Blo 511796 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B513187 : Blo 511796 513187 := bstep (se 1 (by rfl) ⟨384890, by rfl⟩ : syracuseStep 513187 = 769781) B769781
theorem B513203 : Blo 511796 513203 := bstep (se 1 (by rfl) ⟨384902, by rfl⟩ : syracuseStep 513203 = 769805) B769805
theorem B513219 : Blo 511796 513219 := bstep (se 1 (by rfl) ⟨384914, by rfl⟩ : syracuseStep 513219 = 769829) B769829
theorem B1299665 : Blo 511796 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B1234129 : Blo 511796 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B513235 : Blo 511796 513235 := bstep (se 1 (by rfl) ⟨384926, by rfl⟩ : syracuseStep 513235 = 769853) B769853
theorem B513251 : Blo 511796 513251 := bstep (se 1 (by rfl) ⟨384938, by rfl⟩ : syracuseStep 513251 = 769877) B769877
theorem B513267 : Blo 511796 513267 := bstep (se 1 (by rfl) ⟨384950, by rfl⟩ : syracuseStep 513267 = 769901) B769901
theorem B578803 : Blo 511796 578803 := bstep (se 1 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 578803 = 868205) B868205
theorem B513283 : Blo 511796 513283 := bstep (se 1 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 513283 = 769925) B769925
theorem B513299 : Blo 511796 513299 := bstep (se 1 (by rfl) ⟨384974, by rfl⟩ : syracuseStep 513299 = 769949) B769949
theorem B513315 : Blo 511796 513315 := bstep (se 1 (by rfl) ⟨384986, by rfl⟩ : syracuseStep 513315 = 769973) B769973
theorem B2610467 : Blo 511796 2610467 := bstep (se 1 (by rfl) ⟨1957850, by rfl⟩ : syracuseStep 2610467 = 3915701) B3915701
theorem B2086193 : Blo 511796 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B513331 : Blo 511796 513331 := bstep (se 1 (by rfl) ⟨384998, by rfl⟩ : syracuseStep 513331 = 769997) B769997
theorem B513347 : Blo 511796 513347 := bstep (se 1 (by rfl) ⟨385010, by rfl⟩ : syracuseStep 513347 = 770021) B770021
theorem B513363 : Blo 511796 513363 := bstep (se 1 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 513363 = 770045) B770045
theorem B2643299 : Blo 511796 2643299 := bstep (se 1 (by rfl) ⟨1982474, by rfl⟩ : syracuseStep 2643299 = 3964949) B3964949
theorem B513379 : Blo 511796 513379 := bstep (se 1 (by rfl) ⟨385034, by rfl⟩ : syracuseStep 513379 = 770069) B770069
theorem B1037681 : Blo 511796 1037681 := bstep (se 2 (by rfl) ⟨389130, by rfl⟩ : syracuseStep 1037681 = 778261) B778261
theorem B513395 : Blo 511796 513395 := bstep (se 1 (by rfl) ⟨385046, by rfl⟩ : syracuseStep 513395 = 770093) B770093
theorem B513411 : Blo 511796 513411 := bstep (se 1 (by rfl) ⟨385058, by rfl⟩ : syracuseStep 513411 = 770117) B770117
theorem B578947 : Blo 511796 578947 := bstep (se 1 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 578947 = 868421) B868421
theorem B513427 : Blo 511796 513427 := bstep (se 1 (by rfl) ⟨385070, by rfl⟩ : syracuseStep 513427 = 770141) B770141
theorem B513443 : Blo 511796 513443 := bstep (se 1 (by rfl) ⟨385082, by rfl⟩ : syracuseStep 513443 = 770165) B770165
theorem B513459 : Blo 511796 513459 := bstep (se 1 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 513459 = 770189) B770189
theorem B513475 : Blo 511796 513475 := bstep (se 1 (by rfl) ⟨385106, by rfl⟩ : syracuseStep 513475 = 770213) B770213
theorem B1037777 : Blo 511796 1037777 := bstep (se 2 (by rfl) ⟨389166, by rfl⟩ : syracuseStep 1037777 = 778333) B778333
theorem B1168849 : Blo 511796 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B513491 : Blo 511796 513491 := bstep (se 1 (by rfl) ⟨385118, by rfl⟩ : syracuseStep 513491 = 770237) B770237
theorem B513507 : Blo 511796 513507 := bstep (se 1 (by rfl) ⟨385130, by rfl⟩ : syracuseStep 513507 = 770261) B770261
theorem B1955299 : Blo 511796 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B513523 : Blo 511796 513523 := bstep (se 1 (by rfl) ⟨385142, by rfl⟩ : syracuseStep 513523 = 770285) B770285
theorem B513539 : Blo 511796 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B513555 : Blo 511796 513555 := bstep (se 1 (by rfl) ⟨385166, by rfl⟩ : syracuseStep 513555 = 770333) B770333
theorem B579091 : Blo 511796 579091 := bstep (se 1 (by rfl) ⟨434318, by rfl⟩ : syracuseStep 579091 = 868637) B868637
theorem B513571 : Blo 511796 513571 := bstep (se 1 (by rfl) ⟨385178, by rfl⟩ : syracuseStep 513571 = 770357) B770357
theorem B513587 : Blo 511796 513587 := bstep (se 1 (by rfl) ⟨385190, by rfl⟩ : syracuseStep 513587 = 770381) B770381
theorem B513603 : Blo 511796 513603 := bstep (se 1 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 513603 = 770405) B770405
theorem B513619 : Blo 511796 513619 := bstep (se 1 (by rfl) ⟨385214, by rfl⟩ : syracuseStep 513619 = 770429) B770429
theorem B513635 : Blo 511796 513635 := bstep (se 1 (by rfl) ⟨385226, by rfl⟩ : syracuseStep 513635 = 770453) B770453
theorem B513651 : Blo 511796 513651 := bstep (se 1 (by rfl) ⟨385238, by rfl⟩ : syracuseStep 513651 = 770477) B770477
theorem B513667 : Blo 511796 513667 := bstep (se 1 (by rfl) ⟨385250, by rfl⟩ : syracuseStep 513667 = 770501) B770501
theorem B513683 : Blo 511796 513683 := bstep (se 1 (by rfl) ⟨385262, by rfl⟩ : syracuseStep 513683 = 770525) B770525
theorem B513699 : Blo 511796 513699 := bstep (se 1 (by rfl) ⟨385274, by rfl⟩ : syracuseStep 513699 = 770549) B770549
theorem B579235 : Blo 511796 579235 := bstep (se 1 (by rfl) ⟨434426, by rfl⟩ : syracuseStep 579235 = 868853) B868853
theorem B513715 : Blo 511796 513715 := bstep (se 1 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 513715 = 770573) B770573
theorem B513731 : Blo 511796 513731 := bstep (se 1 (by rfl) ⟨385298, by rfl⟩ : syracuseStep 513731 = 770597) B770597
theorem B8345285 : Blo 511796 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B513747 : Blo 511796 513747 := bstep (se 1 (by rfl) ⟨385310, by rfl⟩ : syracuseStep 513747 = 770621) B770621
theorem B513763 : Blo 511796 513763 := bstep (se 1 (by rfl) ⟨385322, by rfl⟩ : syracuseStep 513763 = 770645) B770645
theorem B513779 : Blo 511796 513779 := bstep (se 1 (by rfl) ⟨385334, by rfl⟩ : syracuseStep 513779 = 770669) B770669
theorem B513795 : Blo 511796 513795 := bstep (se 1 (by rfl) ⟨385346, by rfl⟩ : syracuseStep 513795 = 770693) B770693
theorem B513811 : Blo 511796 513811 := bstep (se 1 (by rfl) ⟨385358, by rfl⟩ : syracuseStep 513811 = 770717) B770717
theorem B513827 : Blo 511796 513827 := bstep (se 1 (by rfl) ⟨385370, by rfl⟩ : syracuseStep 513827 = 770741) B770741
theorem B513843 : Blo 511796 513843 := bstep (se 1 (by rfl) ⟨385382, by rfl⟩ : syracuseStep 513843 = 770765) B770765
theorem B579379 : Blo 511796 579379 := bstep (se 1 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 579379 = 869069) B869069
theorem B513859 : Blo 511796 513859 := bstep (se 1 (by rfl) ⟨385394, by rfl⟩ : syracuseStep 513859 = 770789) B770789
theorem B513875 : Blo 511796 513875 := bstep (se 1 (by rfl) ⟨385406, by rfl⟩ : syracuseStep 513875 = 770813) B770813
theorem B513891 : Blo 511796 513891 := bstep (se 1 (by rfl) ⟨385418, by rfl⟩ : syracuseStep 513891 = 770837) B770837
theorem B1234801 : Blo 511796 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B513907 : Blo 511796 513907 := bstep (se 1 (by rfl) ⟨385430, by rfl⟩ : syracuseStep 513907 = 770861) B770861
theorem B513923 : Blo 511796 513923 := bstep (se 1 (by rfl) ⟨385442, by rfl⟩ : syracuseStep 513923 = 770885) B770885
theorem B513939 : Blo 511796 513939 := bstep (se 1 (by rfl) ⟨385454, by rfl⟩ : syracuseStep 513939 = 770909) B770909
theorem B513955 : Blo 511796 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B513971 : Blo 511796 513971 := bstep (se 1 (by rfl) ⟨385478, by rfl⟩ : syracuseStep 513971 = 770957) B770957
theorem B513987 : Blo 511796 513987 := bstep (se 1 (by rfl) ⟨385490, by rfl⟩ : syracuseStep 513987 = 770981) B770981
theorem B579523 : Blo 511796 579523 := bstep (se 1 (by rfl) ⟨434642, by rfl⟩ : syracuseStep 579523 = 869285) B869285
theorem B514003 : Blo 511796 514003 := bstep (se 1 (by rfl) ⟨385502, by rfl⟩ : syracuseStep 514003 = 771005) B771005
theorem B514019 : Blo 511796 514019 := bstep (se 1 (by rfl) ⟨385514, by rfl⟩ : syracuseStep 514019 = 771029) B771029
theorem B514035 : Blo 511796 514035 := bstep (se 1 (by rfl) ⟨385526, by rfl⟩ : syracuseStep 514035 = 771053) B771053
theorem B514051 : Blo 511796 514051 := bstep (se 1 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 514051 = 771077) B771077
theorem B514067 : Blo 511796 514067 := bstep (se 1 (by rfl) ⟨385550, by rfl⟩ : syracuseStep 514067 = 771101) B771101
theorem B514083 : Blo 511796 514083 := bstep (se 1 (by rfl) ⟨385562, by rfl⟩ : syracuseStep 514083 = 771125) B771125
theorem B3299363 : Blo 511796 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B514099 : Blo 511796 514099 := bstep (se 1 (by rfl) ⟨385574, by rfl⟩ : syracuseStep 514099 = 771149) B771149
theorem B514115 : Blo 511796 514115 := bstep (se 1 (by rfl) ⟨385586, by rfl⟩ : syracuseStep 514115 = 771173) B771173
theorem B972881 : Blo 511796 972881 := bstep (se 2 (by rfl) ⟨364830, by rfl⟩ : syracuseStep 972881 = 729661) B729661
theorem B514131 : Blo 511796 514131 := bstep (se 1 (by rfl) ⟨385598, by rfl⟩ : syracuseStep 514131 = 771197) B771197
theorem B579667 : Blo 511796 579667 := bstep (se 1 (by rfl) ⟨434750, by rfl⟩ : syracuseStep 579667 = 869501) B869501
theorem B514147 : Blo 511796 514147 := bstep (se 1 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 514147 = 771221) B771221
theorem B514163 : Blo 511796 514163 := bstep (se 1 (by rfl) ⟨385622, by rfl⟩ : syracuseStep 514163 = 771245) B771245
theorem B514179 : Blo 511796 514179 := bstep (se 1 (by rfl) ⟨385634, by rfl⟩ : syracuseStep 514179 = 771269) B771269
theorem B514195 : Blo 511796 514195 := bstep (se 1 (by rfl) ⟨385646, by rfl⟩ : syracuseStep 514195 = 771293) B771293
theorem B514211 : Blo 511796 514211 := bstep (se 1 (by rfl) ⟨385658, by rfl⟩ : syracuseStep 514211 = 771317) B771317
theorem B1464493 : Blo 511796 1464493 := bstep (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) B549185
theorem B1300657 : Blo 511796 1300657 := bstep (se 2 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 1300657 = 975493) B975493
theorem B514227 : Blo 511796 514227 := bstep (se 1 (by rfl) ⟨385670, by rfl⟩ : syracuseStep 514227 = 771341) B771341
theorem B514243 : Blo 511796 514243 := bstep (se 1 (by rfl) ⟨385682, by rfl⟩ : syracuseStep 514243 = 771365) B771365
theorem B514259 : Blo 511796 514259 := bstep (se 1 (by rfl) ⟨385694, by rfl⟩ : syracuseStep 514259 = 771389) B771389
theorem B514275 : Blo 511796 514275 := bstep (se 1 (by rfl) ⟨385706, by rfl⟩ : syracuseStep 514275 = 771413) B771413
theorem B579811 : Blo 511796 579811 := bstep (se 1 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 579811 = 869717) B869717
theorem B514291 : Blo 511796 514291 := bstep (se 1 (by rfl) ⟨385718, by rfl⟩ : syracuseStep 514291 = 771437) B771437
theorem B547075 : Blo 511796 547075 := bstep (se 1 (by rfl) ⟨410306, by rfl⟩ : syracuseStep 547075 = 820613) B820613
theorem B514307 : Blo 511796 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B514323 : Blo 511796 514323 := bstep (se 1 (by rfl) ⟨385742, by rfl⟩ : syracuseStep 514323 = 771485) B771485
theorem B514339 : Blo 511796 514339 := bstep (se 1 (by rfl) ⟨385754, by rfl⟩ : syracuseStep 514339 = 771509) B771509
theorem B514355 : Blo 511796 514355 := bstep (se 1 (by rfl) ⟨385766, by rfl⟩ : syracuseStep 514355 = 771533) B771533
theorem B514371 : Blo 511796 514371 := bstep (se 1 (by rfl) ⟨385778, by rfl⟩ : syracuseStep 514371 = 771557) B771557
theorem B514387 : Blo 511796 514387 := bstep (se 1 (by rfl) ⟨385790, by rfl⟩ : syracuseStep 514387 = 771581) B771581
theorem B514403 : Blo 511796 514403 := bstep (se 1 (by rfl) ⟨385802, by rfl⟩ : syracuseStep 514403 = 771605) B771605
theorem B514419 : Blo 511796 514419 := bstep (se 1 (by rfl) ⟨385814, by rfl⟩ : syracuseStep 514419 = 771629) B771629
theorem B579955 : Blo 511796 579955 := bstep (se 1 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 579955 = 869933) B869933
theorem B514435 : Blo 511796 514435 := bstep (se 1 (by rfl) ⟨385826, by rfl⟩ : syracuseStep 514435 = 771653) B771653
theorem B514451 : Blo 511796 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B514467 : Blo 511796 514467 := bstep (se 1 (by rfl) ⟨385850, by rfl⟩ : syracuseStep 514467 = 771701) B771701
theorem B514483 : Blo 511796 514483 := bstep (se 1 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 514483 = 771725) B771725
theorem B5560757 : Blo 511796 5560757 := bstep (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) B521321
theorem B1300931 : Blo 511796 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B514499 : Blo 511796 514499 := bstep (se 1 (by rfl) ⟨385874, by rfl⟩ : syracuseStep 514499 = 771749) B771749
theorem B514515 : Blo 511796 514515 := bstep (se 1 (by rfl) ⟨385886, by rfl⟩ : syracuseStep 514515 = 771773) B771773
theorem B514531 : Blo 511796 514531 := bstep (se 1 (by rfl) ⟨385898, by rfl⟩ : syracuseStep 514531 = 771797) B771797
theorem B514547 : Blo 511796 514547 := bstep (se 1 (by rfl) ⟨385910, by rfl⟩ : syracuseStep 514547 = 771821) B771821
theorem B547331 : Blo 511796 547331 := bstep (se 1 (by rfl) ⟨410498, by rfl⟩ : syracuseStep 547331 = 820997) B820997
theorem B514563 : Blo 511796 514563 := bstep (se 1 (by rfl) ⟨385922, by rfl⟩ : syracuseStep 514563 = 771845) B771845
theorem B580099 : Blo 511796 580099 := bstep (se 1 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 580099 = 870149) B870149
theorem B514579 : Blo 511796 514579 := bstep (se 1 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 514579 = 771869) B771869
theorem B514595 : Blo 511796 514595 := bstep (se 1 (by rfl) ⟨385946, by rfl⟩ : syracuseStep 514595 = 771893) B771893
theorem B514611 : Blo 511796 514611 := bstep (se 1 (by rfl) ⟨385958, by rfl⟩ : syracuseStep 514611 = 771917) B771917
theorem B514627 : Blo 511796 514627 := bstep (se 1 (by rfl) ⟨385970, by rfl⟩ : syracuseStep 514627 = 771941) B771941
theorem B514643 : Blo 511796 514643 := bstep (se 1 (by rfl) ⟨385982, by rfl⟩ : syracuseStep 514643 = 771965) B771965
theorem B514659 : Blo 511796 514659 := bstep (se 1 (by rfl) ⟨385994, by rfl⟩ : syracuseStep 514659 = 771989) B771989
theorem B514675 : Blo 511796 514675 := bstep (se 1 (by rfl) ⟨386006, by rfl⟩ : syracuseStep 514675 = 772013) B772013
theorem B1301123 : Blo 511796 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B514691 : Blo 511796 514691 := bstep (se 1 (by rfl) ⟨386018, by rfl⟩ : syracuseStep 514691 = 772037) B772037
theorem B514707 : Blo 511796 514707 := bstep (se 1 (by rfl) ⟨386030, by rfl⟩ : syracuseStep 514707 = 772061) B772061
theorem B580243 : Blo 511796 580243 := bstep (se 1 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 580243 = 870365) B870365
theorem B514723 : Blo 511796 514723 := bstep (se 1 (by rfl) ⟨386042, by rfl⟩ : syracuseStep 514723 = 772085) B772085
theorem B514739 : Blo 511796 514739 := bstep (se 1 (by rfl) ⟨386054, by rfl⟩ : syracuseStep 514739 = 772109) B772109
theorem B514755 : Blo 511796 514755 := bstep (se 1 (by rfl) ⟨386066, by rfl⟩ : syracuseStep 514755 = 772133) B772133
theorem B514771 : Blo 511796 514771 := bstep (se 1 (by rfl) ⟨386078, by rfl⟩ : syracuseStep 514771 = 772157) B772157
theorem B514787 : Blo 511796 514787 := bstep (se 1 (by rfl) ⟨386090, by rfl⟩ : syracuseStep 514787 = 772181) B772181
theorem B514803 : Blo 511796 514803 := bstep (se 1 (by rfl) ⟨386102, by rfl⟩ : syracuseStep 514803 = 772205) B772205
theorem B514819 : Blo 511796 514819 := bstep (se 1 (by rfl) ⟨386114, by rfl⟩ : syracuseStep 514819 = 772229) B772229
theorem B514835 : Blo 511796 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B514851 : Blo 511796 514851 := bstep (se 1 (by rfl) ⟨386138, by rfl⟩ : syracuseStep 514851 = 772277) B772277
theorem B514867 : Blo 511796 514867 := bstep (se 1 (by rfl) ⟨386150, by rfl⟩ : syracuseStep 514867 = 772301) B772301
theorem B514883 : Blo 511796 514883 := bstep (se 1 (by rfl) ⟨386162, by rfl⟩ : syracuseStep 514883 = 772325) B772325
theorem B514899 : Blo 511796 514899 := bstep (se 1 (by rfl) ⟨386174, by rfl⟩ : syracuseStep 514899 = 772349) B772349
theorem B514915 : Blo 511796 514915 := bstep (se 1 (by rfl) ⟨386186, by rfl⟩ : syracuseStep 514915 = 772373) B772373
theorem B7035761 : Blo 511796 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B514931 : Blo 511796 514931 := bstep (se 1 (by rfl) ⟨386198, by rfl⟩ : syracuseStep 514931 = 772397) B772397
theorem B514947 : Blo 511796 514947 := bstep (se 1 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 514947 = 772421) B772421
theorem B514963 : Blo 511796 514963 := bstep (se 1 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 514963 = 772445) B772445
theorem B2775971 : Blo 511796 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B514979 : Blo 511796 514979 := bstep (se 1 (by rfl) ⟨386234, by rfl⟩ : syracuseStep 514979 = 772469) B772469
theorem B1727405 : Blo 511796 1727405 := bstep (se 3 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 1727405 = 647777) B647777
theorem B514995 : Blo 511796 514995 := bstep (se 1 (by rfl) ⟨386246, by rfl⟩ : syracuseStep 514995 = 772493) B772493
theorem B515011 : Blo 511796 515011 := bstep (se 1 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 515011 = 772517) B772517
theorem B973777 : Blo 511796 973777 := bstep (se 2 (by rfl) ⟨365166, by rfl⟩ : syracuseStep 973777 = 730333) B730333
theorem B515027 : Blo 511796 515027 := bstep (se 1 (by rfl) ⟨386270, by rfl⟩ : syracuseStep 515027 = 772541) B772541
theorem B1727459 : Blo 511796 1727459 := bstep (se 1 (by rfl) ⟨1295594, by rfl⟩ : syracuseStep 1727459 = 2591189) B2591189
theorem B515043 : Blo 511796 515043 := bstep (se 1 (by rfl) ⟨386282, by rfl⟩ : syracuseStep 515043 = 772565) B772565
theorem B515059 : Blo 511796 515059 := bstep (se 1 (by rfl) ⟨386294, by rfl⟩ : syracuseStep 515059 = 772589) B772589
theorem B515075 : Blo 511796 515075 := bstep (se 1 (by rfl) ⟨386306, by rfl⟩ : syracuseStep 515075 = 772613) B772613
theorem B3300365 : Blo 511796 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B515091 : Blo 511796 515091 := bstep (se 1 (by rfl) ⟨386318, by rfl⟩ : syracuseStep 515091 = 772637) B772637
theorem B515107 : Blo 511796 515107 := bstep (se 1 (by rfl) ⟨386330, by rfl⟩ : syracuseStep 515107 = 772661) B772661
theorem B515123 : Blo 511796 515123 := bstep (se 1 (by rfl) ⟨386342, by rfl⟩ : syracuseStep 515123 = 772685) B772685
theorem B515139 : Blo 511796 515139 := bstep (se 1 (by rfl) ⟨386354, by rfl⟩ : syracuseStep 515139 = 772709) B772709
theorem B515155 : Blo 511796 515155 := bstep (se 1 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 515155 = 772733) B772733
theorem B515171 : Blo 511796 515171 := bstep (se 1 (by rfl) ⟨386378, by rfl⟩ : syracuseStep 515171 = 772757) B772757
theorem B973937 : Blo 511796 973937 := bstep (se 2 (by rfl) ⟨365226, by rfl⟩ : syracuseStep 973937 = 730453) B730453
theorem B515187 : Blo 511796 515187 := bstep (se 1 (by rfl) ⟨386390, by rfl⟩ : syracuseStep 515187 = 772781) B772781
theorem B515203 : Blo 511796 515203 := bstep (se 1 (by rfl) ⟨386402, by rfl⟩ : syracuseStep 515203 = 772805) B772805
theorem B515219 : Blo 511796 515219 := bstep (se 1 (by rfl) ⟨386414, by rfl⟩ : syracuseStep 515219 = 772829) B772829
theorem B515235 : Blo 511796 515235 := bstep (se 1 (by rfl) ⟨386426, by rfl⟩ : syracuseStep 515235 = 772853) B772853
theorem B515251 : Blo 511796 515251 := bstep (se 1 (by rfl) ⟨386438, by rfl⟩ : syracuseStep 515251 = 772877) B772877
theorem B515267 : Blo 511796 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B1465553 : Blo 511796 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B515283 : Blo 511796 515283 := bstep (se 1 (by rfl) ⟨386462, by rfl⟩ : syracuseStep 515283 = 772925) B772925
theorem B515299 : Blo 511796 515299 := bstep (se 1 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 515299 = 772949) B772949
theorem B1727729 : Blo 511796 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B548083 : Blo 511796 548083 := bstep (se 1 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 548083 = 822125) B822125
theorem B515315 : Blo 511796 515315 := bstep (se 1 (by rfl) ⟨386486, by rfl⟩ : syracuseStep 515315 = 772973) B772973
theorem B515331 : Blo 511796 515331 := bstep (se 1 (by rfl) ⟨386498, by rfl⟩ : syracuseStep 515331 = 772997) B772997
theorem B515347 : Blo 511796 515347 := bstep (se 1 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 515347 = 773021) B773021
theorem B515363 : Blo 511796 515363 := bstep (se 1 (by rfl) ⟨386522, by rfl⟩ : syracuseStep 515363 = 773045) B773045
theorem B1563953 : Blo 511796 1563953 := bstep (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) B1172965
theorem B515379 : Blo 511796 515379 := bstep (se 1 (by rfl) ⟨386534, by rfl⟩ : syracuseStep 515379 = 773069) B773069
theorem B515395 : Blo 511796 515395 := bstep (se 1 (by rfl) ⟨386546, by rfl⟩ : syracuseStep 515395 = 773093) B773093
theorem B515411 : Blo 511796 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B515427 : Blo 511796 515427 := bstep (se 1 (by rfl) ⟨386570, by rfl⟩ : syracuseStep 515427 = 773141) B773141
theorem B515443 : Blo 511796 515443 := bstep (se 1 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 515443 = 773165) B773165
theorem B515459 : Blo 511796 515459 := bstep (se 1 (by rfl) ⟨386594, by rfl⟩ : syracuseStep 515459 = 773189) B773189
theorem B515475 : Blo 511796 515475 := bstep (se 1 (by rfl) ⟨386606, by rfl⟩ : syracuseStep 515475 = 773213) B773213
theorem B515491 : Blo 511796 515491 := bstep (se 1 (by rfl) ⟨386618, by rfl⟩ : syracuseStep 515491 = 773237) B773237
theorem B515507 : Blo 511796 515507 := bstep (se 1 (by rfl) ⟨386630, by rfl⟩ : syracuseStep 515507 = 773261) B773261
theorem B515523 : Blo 511796 515523 := bstep (se 1 (by rfl) ⟨386642, by rfl⟩ : syracuseStep 515523 = 773285) B773285
theorem B17817029 : Blo 511796 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B515539 : Blo 511796 515539 := bstep (se 1 (by rfl) ⟨386654, by rfl⟩ : syracuseStep 515539 = 773309) B773309
theorem B515555 : Blo 511796 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B515571 : Blo 511796 515571 := bstep (se 1 (by rfl) ⟨386678, by rfl⟩ : syracuseStep 515571 = 773357) B773357
theorem B974339 : Blo 511796 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B515587 : Blo 511796 515587 := bstep (se 1 (by rfl) ⟨386690, by rfl⟩ : syracuseStep 515587 = 773381) B773381
theorem B515603 : Blo 511796 515603 := bstep (se 1 (by rfl) ⟨386702, by rfl⟩ : syracuseStep 515603 = 773405) B773405
theorem B515619 : Blo 511796 515619 := bstep (se 1 (by rfl) ⟨386714, by rfl⟩ : syracuseStep 515619 = 773429) B773429
theorem B1302065 : Blo 511796 1302065 := bstep (se 2 (by rfl) ⟨488274, by rfl⟩ : syracuseStep 1302065 = 976549) B976549
theorem B515635 : Blo 511796 515635 := bstep (se 1 (by rfl) ⟨386726, by rfl⟩ : syracuseStep 515635 = 773453) B773453
theorem B515651 : Blo 511796 515651 := bstep (se 1 (by rfl) ⟨386738, by rfl⟩ : syracuseStep 515651 = 773477) B773477
theorem B515667 : Blo 511796 515667 := bstep (se 1 (by rfl) ⟨386750, by rfl⟩ : syracuseStep 515667 = 773501) B773501
theorem B1302115 : Blo 511796 1302115 := bstep (se 1 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 1302115 = 1953173) B1953173
theorem B515683 : Blo 511796 515683 := bstep (se 1 (by rfl) ⟨386762, by rfl⟩ : syracuseStep 515683 = 773525) B773525
theorem B515699 : Blo 511796 515699 := bstep (se 1 (by rfl) ⟨386774, by rfl⟩ : syracuseStep 515699 = 773549) B773549
theorem B515715 : Blo 511796 515715 := bstep (se 1 (by rfl) ⟨386786, by rfl⟩ : syracuseStep 515715 = 773573) B773573
theorem B1957517 : Blo 511796 1957517 := bstep (se 3 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 1957517 = 734069) B734069
theorem B515731 : Blo 511796 515731 := bstep (se 1 (by rfl) ⟨386798, by rfl⟩ : syracuseStep 515731 = 773597) B773597
theorem B515747 : Blo 511796 515747 := bstep (se 1 (by rfl) ⟨386810, by rfl⟩ : syracuseStep 515747 = 773621) B773621
theorem B515763 : Blo 511796 515763 := bstep (se 1 (by rfl) ⟨386822, by rfl⟩ : syracuseStep 515763 = 773645) B773645
theorem B515779 : Blo 511796 515779 := bstep (se 1 (by rfl) ⟨386834, by rfl⟩ : syracuseStep 515779 = 773669) B773669
theorem B515795 : Blo 511796 515795 := bstep (se 1 (by rfl) ⟨386846, by rfl⟩ : syracuseStep 515795 = 773693) B773693
theorem B3890915 : Blo 511796 3890915 := bstep (se 1 (by rfl) ⟨2918186, by rfl⟩ : syracuseStep 3890915 = 5836373) B5836373
theorem B1302257 : Blo 511796 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B1728269 : Blo 511796 1728269 := bstep (se 3 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 1728269 = 648101) B648101
theorem B1728323 : Blo 511796 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B2187121 : Blo 511796 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B1466225 : Blo 511796 1466225 := bstep (se 2 (by rfl) ⟨549834, by rfl⟩ : syracuseStep 1466225 = 1099669) B1099669
theorem B1728593 : Blo 511796 1728593 := bstep (se 2 (by rfl) ⟨648222, by rfl⟩ : syracuseStep 1728593 = 1296445) B1296445
theorem B975235 : Blo 511796 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B2646413 : Blo 511796 2646413 := bstep (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) B992405
theorem B549347 : Blo 511796 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B975395 : Blo 511796 975395 := bstep (se 1 (by rfl) ⟨731546, by rfl⟩ : syracuseStep 975395 = 1463093) B1463093
theorem B1729133 : Blo 511796 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B1467011 : Blo 511796 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B1729187 : Blo 511796 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B1303249 : Blo 511796 1303249 := bstep (se 2 (by rfl) ⟨488718, by rfl⟩ : syracuseStep 1303249 = 977437) B977437
theorem B778979 : Blo 511796 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B647939 : Blo 511796 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B1729457 : Blo 511796 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1467341 : Blo 511796 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B1303523 : Blo 511796 1303523 := bstep (se 1 (by rfl) ⟨977642, by rfl⟩ : syracuseStep 1303523 = 1955285) B1955285
theorem B1467409 : Blo 511796 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B1303715 : Blo 511796 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B550099 : Blo 511796 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B1467683 : Blo 511796 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B648643 : Blo 511796 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B1729997 : Blo 511796 1729997 := bstep (se 3 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 1729997 = 648749) B648749
theorem B1730051 : Blo 511796 1730051 := bstep (se 1 (by rfl) ⟨1297538, by rfl⟩ : syracuseStep 1730051 = 2595077) B2595077
theorem B648739 : Blo 511796 648739 := bstep (se 1 (by rfl) ⟨486554, by rfl⟩ : syracuseStep 648739 = 973109) B973109
theorem B976465 : Blo 511796 976465 := bstep (se 2 (by rfl) ⟨366174, by rfl⟩ : syracuseStep 976465 = 732349) B732349
theorem B1238723 : Blo 511796 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1730321 : Blo 511796 1730321 := bstep (se 2 (by rfl) ⟨648870, by rfl⟩ : syracuseStep 1730321 = 1297741) B1297741
theorem B1238915 : Blo 511796 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B1566641 : Blo 511796 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1173521 : Blo 511796 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B649235 : Blo 511796 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B1304657 : Blo 511796 1304657 := bstep (se 2 (by rfl) ⟨489246, by rfl⟩ : syracuseStep 1304657 = 978493) B978493
theorem B1468525 : Blo 511796 1468525 := bstep (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) B550697
theorem B1304707 : Blo 511796 1304707 := bstep (se 1 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 1304707 = 1957061) B1957061
theorem B25389283 : Blo 511796 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B1468685 : Blo 511796 1468685 := bstep (se 3 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 1468685 = 550757) B550757
theorem B1304849 : Blo 511796 1304849 := bstep (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) B978637
theorem B1730861 : Blo 511796 1730861 := bstep (se 3 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 1730861 = 649073) B649073
theorem B1730915 : Blo 511796 1730915 := bstep (se 1 (by rfl) ⟨1298186, by rfl⟩ : syracuseStep 1730915 = 2596373) B2596373
theorem B584051 : Blo 511796 584051 := bstep (se 1 (by rfl) ⟨438038, by rfl⟩ : syracuseStep 584051 = 876077) B876077
theorem B584147 : Blo 511796 584147 := bstep (se 1 (by rfl) ⟨438110, by rfl⟩ : syracuseStep 584147 = 876221) B876221
theorem B1731185 : Blo 511796 1731185 := bstep (se 2 (by rfl) ⟨649194, by rfl⟩ : syracuseStep 1731185 = 1298389) B1298389
theorem B977521 : Blo 511796 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B2976389 : Blo 511796 2976389 := bstep (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) B558073
theorem B649939 : Blo 511796 649939 := bstep (se 1 (by rfl) ⟨487454, by rfl⟩ : syracuseStep 649939 = 974909) B974909
theorem B5073635 : Blo 511796 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B650035 : Blo 511796 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B1567565 : Blo 511796 1567565 := bstep (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) B587837
theorem B2190179 : Blo 511796 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B977923 : Blo 511796 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B977969 : Blo 511796 977969 := bstep (se 2 (by rfl) ⟨366738, by rfl⟩ : syracuseStep 977969 = 733477) B733477
theorem B1731725 : Blo 511796 1731725 := bstep (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) B649397
theorem B1731779 : Blo 511796 1731779 := bstep (se 1 (by rfl) ⟨1298834, by rfl⟩ : syracuseStep 1731779 = 2597669) B2597669
theorem B650531 : Blo 511796 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B978257 : Blo 511796 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B781667 : Blo 511796 781667 := bstep (se 1 (by rfl) ⟨586250, by rfl⟩ : syracuseStep 781667 = 1172501) B1172501
theorem B1732049 : Blo 511796 1732049 := bstep (se 2 (by rfl) ⟨649518, by rfl⟩ : syracuseStep 1732049 = 1299037) B1299037
theorem B617987 : Blo 511796 617987 := bstep (se 1 (by rfl) ⟨463490, by rfl⟩ : syracuseStep 617987 = 926981) B926981
theorem B618323 : Blo 511796 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B10579909 : Blo 511796 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B651235 : Blo 511796 651235 := bstep (se 1 (by rfl) ⟨488426, by rfl⟩ : syracuseStep 651235 = 976853) B976853
theorem B1732589 : Blo 511796 1732589 := bstep (se 3 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 1732589 = 649721) B649721
theorem B1732643 : Blo 511796 1732643 := bstep (se 1 (by rfl) ⟨1299482, by rfl⟩ : syracuseStep 1732643 = 2598965) B2598965
theorem B978979 : Blo 511796 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B651331 : Blo 511796 651331 := bstep (se 1 (by rfl) ⟨488498, by rfl⟩ : syracuseStep 651331 = 976997) B976997
theorem B782531 : Blo 511796 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B782627 : Blo 511796 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B1732913 : Blo 511796 1732913 := bstep (se 2 (by rfl) ⟨649842, by rfl⟩ : syracuseStep 1732913 = 1299685) B1299685
theorem B782803 : Blo 511796 782803 := bstep (se 1 (by rfl) ⟨587102, by rfl⟩ : syracuseStep 782803 = 1174205) B1174205
theorem B651827 : Blo 511796 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B586387 : Blo 511796 586387 := bstep (se 1 (by rfl) ⟨439790, by rfl⟩ : syracuseStep 586387 = 879581) B879581
theorem B1733453 : Blo 511796 1733453 := bstep (se 3 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 1733453 = 650045) B650045
theorem B4944739 : Blo 511796 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B1733507 : Blo 511796 1733507 := bstep (se 1 (by rfl) ⟨1300130, by rfl⟩ : syracuseStep 1733507 = 2600261) B2600261
theorem B3896261 : Blo 511796 3896261 := bstep (se 4 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 3896261 = 730549) B730549
theorem B7206029 : Blo 511796 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1733777 : Blo 511796 1733777 := bstep (se 2 (by rfl) ⟨650166, by rfl⟩ : syracuseStep 1733777 = 1300333) B1300333
theorem B652531 : Blo 511796 652531 := bstep (se 1 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 652531 = 978797) B978797
theorem B652627 : Blo 511796 652627 := bstep (se 1 (by rfl) ⟨489470, by rfl⟩ : syracuseStep 652627 = 978941) B978941
theorem B587107 : Blo 511796 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B1734317 : Blo 511796 1734317 := bstep (se 3 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 1734317 = 650369) B650369
theorem B1734371 : Blo 511796 1734371 := bstep (se 1 (by rfl) ⟨1300778, by rfl⟩ : syracuseStep 1734371 = 2601557) B2601557
theorem B5830541 : Blo 511796 5830541 := bstep (se 3 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 5830541 = 2186453) B2186453
theorem B1734641 : Blo 511796 1734641 := bstep (se 2 (by rfl) ⟨650490, by rfl⟩ : syracuseStep 1734641 = 1300981) B1300981
theorem B15005749 : Blo 511796 15005749 := bstep (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) B1406789
theorem B1735181 : Blo 511796 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B1735235 : Blo 511796 1735235 := bstep (se 1 (by rfl) ⟨1301426, by rfl⟩ : syracuseStep 1735235 = 2602853) B2602853
theorem B1735505 : Blo 511796 1735505 := bstep (se 2 (by rfl) ⟨650814, by rfl⟩ : syracuseStep 1735505 = 1301629) B1301629
theorem B2194381 : Blo 511796 2194381 := bstep (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) B822893
theorem B1736045 : Blo 511796 1736045 := bstep (se 3 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 1736045 = 651017) B651017
theorem B1736099 : Blo 511796 1736099 := bstep (se 1 (by rfl) ⟨1302074, by rfl⟩ : syracuseStep 1736099 = 2604149) B2604149
theorem B2915909 : Blo 511796 2915909 := bstep (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) B546733
theorem B1736369 : Blo 511796 1736369 := bstep (se 2 (by rfl) ⟨651138, by rfl⟩ : syracuseStep 1736369 = 1302277) B1302277
theorem B1736855 : Blo 511796 1736855 := bstep (se 1 (by rfl) ⟨1302641, by rfl⟩ : syracuseStep 1736855 = 2605283) B2605283
theorem B2195885 : Blo 511796 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B1737395 : Blo 511796 1737395 := bstep (se 1 (by rfl) ⟨1303046, by rfl⟩ : syracuseStep 1737395 = 2606093) B2606093
theorem B4162265 : Blo 511796 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B2196227 : Blo 511796 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B1737665 : Blo 511796 1737665 := bstep (se 2 (by rfl) ⟨651624, by rfl⟩ : syracuseStep 1737665 = 1303249) B1303249
theorem B9372685 : Blo 511796 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B558263 : Blo 511796 558263 := bstep (se 1 (by rfl) ⟨418697, by rfl⟩ : syracuseStep 558263 = 837395) B837395
theorem B3999041 : Blo 511796 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B1738205 : Blo 511796 1738205 := bstep (se 3 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 1738205 = 651827) B651827
theorem B525911 : Blo 511796 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B2918551 : Blo 511796 2918551 := bstep (se 1 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 2918551 = 4377827) B4377827
theorem B7113005 : Blo 511796 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B4393547 : Blo 511796 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1739339 : Blo 511796 1739339 := bstep (se 1 (by rfl) ⟨1304504, by rfl⟩ : syracuseStep 1739339 = 2609009) B2609009
theorem B1739609 : Blo 511796 1739609 := bstep (se 2 (by rfl) ⟨652353, by rfl⟩ : syracuseStep 1739609 = 1304707) B1304707
theorem B2231185 : Blo 511796 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B33852377 : Blo 511796 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B2198603 : Blo 511796 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2591837 : Blo 511796 2591837 := bstep (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) B971939
theorem B14814737 : Blo 511796 14814737 := bstep (se 2 (by rfl) ⟨5555526, by rfl⟩ : syracuseStep 14814737 = 11111053) B11111053
theorem B1740311 : Blo 511796 1740311 := bstep (se 1 (by rfl) ⟨1305233, by rfl⟩ : syracuseStep 1740311 = 2610467) B2610467
theorem B691787 : Blo 511796 691787 := bstep (se 1 (by rfl) ⟨518840, by rfl⟩ : syracuseStep 691787 = 1037681) B1037681
theorem B1642187 : Blo 511796 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B4951813 : Blo 511796 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B3706829 : Blo 511796 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B2199575 : Blo 511796 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B3707171 : Blo 511796 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B4690507 : Blo 511796 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1151603 : Blo 511796 1151603 := bstep (se 1 (by rfl) ⟨863702, by rfl⟩ : syracuseStep 1151603 = 1727405) B1727405
theorem B1151639 : Blo 511796 1151639 := bstep (se 1 (by rfl) ⟨863729, by rfl⟩ : syracuseStep 1151639 = 1727459) B1727459
theorem B2200243 : Blo 511796 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B1151819 : Blo 511796 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B1151873 : Blo 511796 1151873 := bstep (se 2 (by rfl) ⟨431952, by rfl⟩ : syracuseStep 1151873 = 863905) B863905
theorem B2233261 : Blo 511796 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B922699 : Blo 511796 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B1152089 : Blo 511796 1152089 := bstep (se 2 (by rfl) ⟨432033, by rfl⟩ : syracuseStep 1152089 = 864067) B864067
theorem B2593943 : Blo 511796 2593943 := bstep (se 1 (by rfl) ⟨1945457, by rfl⟩ : syracuseStep 2593943 = 3890915) B3890915
theorem B1152179 : Blo 511796 1152179 := bstep (se 1 (by rfl) ⟨864134, by rfl⟩ : syracuseStep 1152179 = 1728269) B1728269
theorem B1152215 : Blo 511796 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B3118297 : Blo 511796 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B1643827 : Blo 511796 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B1152395 : Blo 511796 1152395 := bstep (se 1 (by rfl) ⟨864296, by rfl⟩ : syracuseStep 1152395 = 1728593) B1728593
theorem B1152449 : Blo 511796 1152449 := bstep (se 2 (by rfl) ⟨432168, by rfl⟩ : syracuseStep 1152449 = 864337) B864337
theorem B3348119 : Blo 511796 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1152665 : Blo 511796 1152665 := bstep (se 2 (by rfl) ⟨432249, by rfl⟩ : syracuseStep 1152665 = 864499) B864499
theorem B1152755 : Blo 511796 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B5871365 : Blo 511796 5871365 := bstep (se 4 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 5871365 = 1100881) B1100881
theorem B1152791 : Blo 511796 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B2201489 : Blo 511796 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B1152971 : Blo 511796 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B1153025 : Blo 511796 1153025 := bstep (se 2 (by rfl) ⟨432384, by rfl⟩ : syracuseStep 1153025 = 864769) B864769
theorem B1153241 : Blo 511796 1153241 := bstep (se 2 (by rfl) ⟨432465, by rfl⟩ : syracuseStep 1153241 = 864931) B864931
theorem B1644761 : Blo 511796 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B1153331 : Blo 511796 1153331 := bstep (se 1 (by rfl) ⟨864998, by rfl⟩ : syracuseStep 1153331 = 1729997) B1729997
theorem B1153367 : Blo 511796 1153367 := bstep (se 1 (by rfl) ⟨865025, by rfl⟩ : syracuseStep 1153367 = 1730051) B1730051
theorem B825815 : Blo 511796 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B6592985 : Blo 511796 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B1153547 : Blo 511796 1153547 := bstep (se 1 (by rfl) ⟨865160, by rfl⟩ : syracuseStep 1153547 = 1730321) B1730321
theorem B1153601 : Blo 511796 1153601 := bstep (se 2 (by rfl) ⟨432600, by rfl⟩ : syracuseStep 1153601 = 865201) B865201
theorem B793367 : Blo 511796 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B1153817 : Blo 511796 1153817 := bstep (se 2 (by rfl) ⟨432681, by rfl⟩ : syracuseStep 1153817 = 865363) B865363
theorem B1153907 : Blo 511796 1153907 := bstep (se 1 (by rfl) ⟨865430, by rfl⟩ : syracuseStep 1153907 = 1730861) B1730861
theorem B1153943 : Blo 511796 1153943 := bstep (se 1 (by rfl) ⟨865457, by rfl⟩ : syracuseStep 1153943 = 1730915) B1730915
theorem B1645505 : Blo 511796 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B1874909 : Blo 511796 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B1317953 : Blo 511796 1317953 := bstep (se 2 (by rfl) ⟨494232, by rfl⟩ : syracuseStep 1317953 = 988465) B988465
theorem B2628683 : Blo 511796 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1154123 : Blo 511796 1154123 := bstep (se 1 (by rfl) ⟨865592, by rfl⟩ : syracuseStep 1154123 = 1731185) B1731185
theorem B1154177 : Blo 511796 1154177 := bstep (se 2 (by rfl) ⟨432816, by rfl⟩ : syracuseStep 1154177 = 865633) B865633
theorem B1154393 : Blo 511796 1154393 := bstep (se 2 (by rfl) ⟨432897, by rfl⟩ : syracuseStep 1154393 = 865795) B865795
theorem B1154483 : Blo 511796 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B1154519 : Blo 511796 1154519 := bstep (se 1 (by rfl) ⟨865889, by rfl⟩ : syracuseStep 1154519 = 1731779) B1731779
theorem B1154699 : Blo 511796 1154699 := bstep (se 1 (by rfl) ⟨866024, by rfl⟩ : syracuseStep 1154699 = 1732049) B1732049
theorem B1154753 : Blo 511796 1154753 := bstep (se 2 (by rfl) ⟨433032, by rfl⟩ : syracuseStep 1154753 = 866065) B866065
theorem B6233861 : Blo 511796 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B1646401 : Blo 511796 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B1154969 : Blo 511796 1154969 := bstep (se 2 (by rfl) ⟨433113, by rfl⟩ : syracuseStep 1154969 = 866227) B866227
theorem B1155059 : Blo 511796 1155059 := bstep (se 1 (by rfl) ⟨866294, by rfl⟩ : syracuseStep 1155059 = 1732589) B1732589
theorem B1155095 : Blo 511796 1155095 := bstep (se 1 (by rfl) ⟨866321, by rfl⟩ : syracuseStep 1155095 = 1732643) B1732643
theorem B4464715 : Blo 511796 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B1155275 : Blo 511796 1155275 := bstep (se 1 (by rfl) ⟨866456, by rfl⟩ : syracuseStep 1155275 = 1732913) B1732913
theorem B1155329 : Blo 511796 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B2466065 : Blo 511796 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B729433 : Blo 511796 729433 := bstep (se 2 (by rfl) ⟨273537, by rfl⟩ : syracuseStep 729433 = 547075) B547075
theorem B4923827 : Blo 511796 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B1155545 : Blo 511796 1155545 := bstep (se 2 (by rfl) ⟨433329, by rfl⟩ : syracuseStep 1155545 = 866659) B866659
theorem B1155635 : Blo 511796 1155635 := bstep (se 1 (by rfl) ⟨866726, by rfl⟩ : syracuseStep 1155635 = 1733453) B1733453
theorem B1155671 : Blo 511796 1155671 := bstep (se 1 (by rfl) ⟨866753, by rfl⟩ : syracuseStep 1155671 = 1733507) B1733507
theorem B2597507 : Blo 511796 2597507 := bstep (se 1 (by rfl) ⟨1948130, by rfl⟩ : syracuseStep 2597507 = 3896261) B3896261
theorem B1155851 : Blo 511796 1155851 := bstep (se 1 (by rfl) ⟨866888, by rfl⟩ : syracuseStep 1155851 = 1733777) B1733777
theorem B4170541 : Blo 511796 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B1155905 : Blo 511796 1155905 := bstep (se 2 (by rfl) ⟨433464, by rfl⟩ : syracuseStep 1155905 = 866929) B866929
theorem B6595445 : Blo 511796 6595445 := bstep (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) B618323
theorem B1156121 : Blo 511796 1156121 := bstep (se 2 (by rfl) ⟨433545, by rfl⟩ : syracuseStep 1156121 = 867091) B867091
theorem B1156211 : Blo 511796 1156211 := bstep (se 1 (by rfl) ⟨867158, by rfl⟩ : syracuseStep 1156211 = 1734317) B1734317
theorem B1156247 : Blo 511796 1156247 := bstep (se 1 (by rfl) ⟨867185, by rfl⟩ : syracuseStep 1156247 = 1734371) B1734371
theorem B2925841 : Blo 511796 2925841 := bstep (se 2 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 2925841 = 2194381) B2194381
theorem B1156427 : Blo 511796 1156427 := bstep (se 1 (by rfl) ⟨867320, by rfl⟩ : syracuseStep 1156427 = 1734641) B1734641
theorem B1647965 : Blo 511796 1647965 := bstep (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) B617987
theorem B1156481 : Blo 511796 1156481 := bstep (se 2 (by rfl) ⟨433680, by rfl⟩ : syracuseStep 1156481 = 867361) B867361
theorem B1975853 : Blo 511796 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1156697 : Blo 511796 1156697 := bstep (se 2 (by rfl) ⟨433761, by rfl⟩ : syracuseStep 1156697 = 867523) B867523
theorem B730777 : Blo 511796 730777 := bstep (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) B548083
theorem B1156787 : Blo 511796 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B1156823 : Blo 511796 1156823 := bstep (se 1 (by rfl) ⟨867617, by rfl⟩ : syracuseStep 1156823 = 1735235) B1735235
theorem B730891 : Blo 511796 730891 := bstep (se 1 (by rfl) ⟨548168, by rfl⟩ : syracuseStep 730891 = 1096337) B1096337
theorem B1157003 : Blo 511796 1157003 := bstep (se 1 (by rfl) ⟨867752, by rfl⟩ : syracuseStep 1157003 = 1735505) B1735505
theorem B1157057 : Blo 511796 1157057 := bstep (se 2 (by rfl) ⟨433896, by rfl⟩ : syracuseStep 1157057 = 867793) B867793
theorem B1157273 : Blo 511796 1157273 := bstep (se 2 (by rfl) ⟨433977, by rfl⟩ : syracuseStep 1157273 = 867955) B867955
theorem B665803 : Blo 511796 665803 := bstep (se 1 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 665803 = 998705) B998705
theorem B1157363 : Blo 511796 1157363 := bstep (se 1 (by rfl) ⟨868022, by rfl⟩ : syracuseStep 1157363 = 1736045) B1736045
theorem B1157399 : Blo 511796 1157399 := bstep (se 1 (by rfl) ⟨868049, by rfl⟩ : syracuseStep 1157399 = 1736099) B1736099
theorem B1976621 : Blo 511796 1976621 := bstep (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) B741233
theorem B1943939 : Blo 511796 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B1157579 : Blo 511796 1157579 := bstep (se 1 (by rfl) ⟨868184, by rfl⟩ : syracuseStep 1157579 = 1736369) B1736369
theorem B1157633 : Blo 511796 1157633 := bstep (se 2 (by rfl) ⟨434112, by rfl⟩ : syracuseStep 1157633 = 868225) B868225
theorem B2107949 : Blo 511796 2107949 := bstep (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) B790481
theorem B3713629 : Blo 511796 3713629 := bstep (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) B1392611
theorem B928459 : Blo 511796 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B1157849 : Blo 511796 1157849 := bstep (se 2 (by rfl) ⟨434193, by rfl⟩ : syracuseStep 1157849 = 868387) B868387
theorem B928523 : Blo 511796 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B1157939 : Blo 511796 1157939 := bstep (se 1 (by rfl) ⟨868454, by rfl⟩ : syracuseStep 1157939 = 1736909) B1736909
theorem B1944395 : Blo 511796 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B1846091 : Blo 511796 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B1157975 : Blo 511796 1157975 := bstep (se 1 (by rfl) ⟨868481, by rfl⟩ : syracuseStep 1157975 = 1736963) B1736963
theorem B1846147 : Blo 511796 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B1158155 : Blo 511796 1158155 := bstep (se 1 (by rfl) ⟨868616, by rfl⟩ : syracuseStep 1158155 = 1737233) B1737233
theorem B1944593 : Blo 511796 1944593 := bstep (se 2 (by rfl) ⟨729222, by rfl⟩ : syracuseStep 1944593 = 1458445) B1458445
theorem B2632769 : Blo 511796 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B1158209 : Blo 511796 1158209 := bstep (se 2 (by rfl) ⟨434328, by rfl⟩ : syracuseStep 1158209 = 868657) B868657
theorem B732235 : Blo 511796 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B928921 : Blo 511796 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B1158425 : Blo 511796 1158425 := bstep (se 2 (by rfl) ⟨434409, by rfl⟩ : syracuseStep 1158425 = 868819) B868819
theorem B732503 : Blo 511796 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B1158515 : Blo 511796 1158515 := bstep (se 1 (by rfl) ⟨868886, by rfl⟩ : syracuseStep 1158515 = 1737773) B1737773
theorem B1158551 : Blo 511796 1158551 := bstep (se 1 (by rfl) ⟨868913, by rfl⟩ : syracuseStep 1158551 = 1737827) B1737827
theorem B1158731 : Blo 511796 1158731 := bstep (se 1 (by rfl) ⟨869048, by rfl⟩ : syracuseStep 1158731 = 1738097) B1738097
theorem B863831 : Blo 511796 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B1158785 : Blo 511796 1158785 := bstep (se 2 (by rfl) ⟨434544, by rfl⟩ : syracuseStep 1158785 = 869089) B869089
theorem B2469527 : Blo 511796 2469527 := bstep (se 1 (by rfl) ⟨1852145, by rfl⟩ : syracuseStep 2469527 = 3704291) B3704291
theorem B1093313 : Blo 511796 1093313 := bstep (se 2 (by rfl) ⟨409992, by rfl⟩ : syracuseStep 1093313 = 819985) B819985
theorem B863959 : Blo 511796 863959 := bstep (se 1 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 863959 = 1295939) B1295939
theorem B1945367 : Blo 511796 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B1159001 : Blo 511796 1159001 := bstep (se 2 (by rfl) ⟨434625, by rfl⟩ : syracuseStep 1159001 = 869251) B869251
theorem B1159091 : Blo 511796 1159091 := bstep (se 1 (by rfl) ⟨869318, by rfl⟩ : syracuseStep 1159091 = 1738637) B1738637
theorem B1159127 : Blo 511796 1159127 := bstep (se 1 (by rfl) ⟨869345, by rfl⟩ : syracuseStep 1159127 = 1738691) B1738691
theorem B1945565 : Blo 511796 1945565 := bstep (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) B729587
theorem B1093655 : Blo 511796 1093655 := bstep (se 1 (by rfl) ⟨820241, by rfl⟩ : syracuseStep 1093655 = 1640483) B1640483
theorem B831575 : Blo 511796 831575 := bstep (se 1 (by rfl) ⟨623681, by rfl⟩ : syracuseStep 831575 = 1247363) B1247363
theorem B1159307 : Blo 511796 1159307 := bstep (se 1 (by rfl) ⟨869480, by rfl⟩ : syracuseStep 1159307 = 1738961) B1738961
theorem B1159361 : Blo 511796 1159361 := bstep (se 2 (by rfl) ⟨434760, by rfl⟩ : syracuseStep 1159361 = 869521) B869521
theorem B2601233 : Blo 511796 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B733465 : Blo 511796 733465 := bstep (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) B550099
theorem B864587 : Blo 511796 864587 := bstep (se 1 (by rfl) ⟨648440, by rfl⟩ : syracuseStep 864587 = 1296881) B1296881
theorem B1159577 : Blo 511796 1159577 := bstep (se 2 (by rfl) ⟨434841, by rfl⟩ : syracuseStep 1159577 = 869683) B869683
theorem B2601395 : Blo 511796 2601395 := bstep (se 1 (by rfl) ⟨1951046, by rfl⟩ : syracuseStep 2601395 = 3902093) B3902093
theorem B864715 : Blo 511796 864715 := bstep (se 1 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 864715 = 1297073) B1297073
theorem B1159667 : Blo 511796 1159667 := bstep (se 1 (by rfl) ⟨869750, by rfl⟩ : syracuseStep 1159667 = 1739501) B1739501
theorem B1159703 : Blo 511796 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B864857 : Blo 511796 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B4928131 : Blo 511796 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B2929283 : Blo 511796 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B4698755 : Blo 511796 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B1159883 : Blo 511796 1159883 := bstep (se 1 (by rfl) ⟨869912, by rfl⟩ : syracuseStep 1159883 = 1739825) B1739825
theorem B864985 : Blo 511796 864985 := bstep (se 2 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 864985 = 648739) B648739
theorem B1159937 : Blo 511796 1159937 := bstep (se 2 (by rfl) ⟨434976, by rfl⟩ : syracuseStep 1159937 = 869953) B869953
theorem B1160153 : Blo 511796 1160153 := bstep (se 2 (by rfl) ⟨435057, by rfl⟩ : syracuseStep 1160153 = 870115) B870115
theorem B1160243 : Blo 511796 1160243 := bstep (se 1 (by rfl) ⟨870182, by rfl⟩ : syracuseStep 1160243 = 1740365) B1740365
theorem B1160279 : Blo 511796 1160279 := bstep (se 1 (by rfl) ⟨870209, by rfl⟩ : syracuseStep 1160279 = 1740419) B1740419
theorem B4174949 : Blo 511796 4174949 := bstep (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) B782803
theorem B1160459 : Blo 511796 1160459 := bstep (se 1 (by rfl) ⟨870344, by rfl⟩ : syracuseStep 1160459 = 1740689) B1740689
theorem B3126545 : Blo 511796 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B865559 : Blo 511796 865559 := bstep (se 1 (by rfl) ⟨649169, by rfl⟩ : syracuseStep 865559 = 1298339) B1298339
theorem B4437283 : Blo 511796 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B1160513 : Blo 511796 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B865687 : Blo 511796 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B767705 : Blo 511796 767705 := bstep (se 2 (by rfl) ⟨287889, by rfl⟩ : syracuseStep 767705 = 575779) B575779
theorem B1128179 : Blo 511796 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B767819 : Blo 511796 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B2471755 : Blo 511796 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B767831 : Blo 511796 767831 := bstep (se 1 (by rfl) ⟨575873, by rfl⟩ : syracuseStep 767831 = 1151747) B1151747
theorem B1947523 : Blo 511796 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B767897 : Blo 511796 767897 := bstep (se 2 (by rfl) ⟨287961, by rfl⟩ : syracuseStep 767897 = 575923) B575923
theorem B604139 : Blo 511796 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B768011 : Blo 511796 768011 := bstep (se 1 (by rfl) ⟨576008, by rfl⟩ : syracuseStep 768011 = 1152017) B1152017
theorem B866315 : Blo 511796 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B768023 : Blo 511796 768023 := bstep (se 1 (by rfl) ⟨576017, by rfl⟩ : syracuseStep 768023 = 1152035) B1152035
theorem B768089 : Blo 511796 768089 := bstep (se 2 (by rfl) ⟨288033, by rfl⟩ : syracuseStep 768089 = 576067) B576067
theorem B866443 : Blo 511796 866443 := bstep (se 1 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 866443 = 1299665) B1299665
theorem B1947827 : Blo 511796 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B768203 : Blo 511796 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B768215 : Blo 511796 768215 := bstep (se 1 (by rfl) ⟨576161, by rfl⟩ : syracuseStep 768215 = 1152323) B1152323
theorem B768281 : Blo 511796 768281 := bstep (se 2 (by rfl) ⟨288105, by rfl⟩ : syracuseStep 768281 = 576211) B576211
theorem B866585 : Blo 511796 866585 := bstep (se 2 (by rfl) ⟨324969, by rfl⟩ : syracuseStep 866585 = 649939) B649939
theorem B2603339 : Blo 511796 2603339 := bstep (se 1 (by rfl) ⟨1952504, by rfl⟩ : syracuseStep 2603339 = 3905009) B3905009
theorem B768395 : Blo 511796 768395 := bstep (se 1 (by rfl) ⟨576296, by rfl⟩ : syracuseStep 768395 = 1152593) B1152593
theorem B768407 : Blo 511796 768407 := bstep (se 1 (by rfl) ⟨576305, by rfl⟩ : syracuseStep 768407 = 1152611) B1152611
theorem B866713 : Blo 511796 866713 := bstep (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) B650035
theorem B768473 : Blo 511796 768473 := bstep (se 2 (by rfl) ⟨288177, by rfl⟩ : syracuseStep 768473 = 576355) B576355
theorem B2406935 : Blo 511796 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B2767405 : Blo 511796 2767405 := bstep (se 3 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 2767405 = 1037777) B1037777
theorem B768587 : Blo 511796 768587 := bstep (se 1 (by rfl) ⟨576440, by rfl⟩ : syracuseStep 768587 = 1152881) B1152881
theorem B768599 : Blo 511796 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B834187 : Blo 511796 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B768665 : Blo 511796 768665 := bstep (se 2 (by rfl) ⟨288249, by rfl⟩ : syracuseStep 768665 = 576499) B576499
theorem B768779 : Blo 511796 768779 := bstep (se 1 (by rfl) ⟨576584, by rfl⟩ : syracuseStep 768779 = 1153169) B1153169
theorem B768791 : Blo 511796 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B1948481 : Blo 511796 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B768857 : Blo 511796 768857 := bstep (se 2 (by rfl) ⟨288321, by rfl⟩ : syracuseStep 768857 = 576643) B576643
theorem B768971 : Blo 511796 768971 := bstep (se 1 (by rfl) ⟨576728, by rfl⟩ : syracuseStep 768971 = 1153457) B1153457
theorem B4373453 : Blo 511796 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B768983 : Blo 511796 768983 := bstep (se 1 (by rfl) ⟨576737, by rfl⟩ : syracuseStep 768983 = 1153475) B1153475
theorem B867287 : Blo 511796 867287 := bstep (se 1 (by rfl) ⟨650465, by rfl⟩ : syracuseStep 867287 = 1300931) B1300931
theorem B2931673 : Blo 511796 2931673 := bstep (se 2 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 2931673 = 2198755) B2198755
theorem B769049 : Blo 511796 769049 := bstep (se 2 (by rfl) ⟨288393, by rfl⟩ : syracuseStep 769049 = 576787) B576787
theorem B867415 : Blo 511796 867415 := bstep (se 1 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 867415 = 1301123) B1301123
theorem B769163 : Blo 511796 769163 := bstep (se 1 (by rfl) ⟨576872, by rfl⟩ : syracuseStep 769163 = 1153745) B1153745
theorem B769175 : Blo 511796 769175 := bstep (se 1 (by rfl) ⟨576881, by rfl⟩ : syracuseStep 769175 = 1153763) B1153763
theorem B769241 : Blo 511796 769241 := bstep (se 2 (by rfl) ⟨288465, by rfl⟩ : syracuseStep 769241 = 576931) B576931
theorem B1850647 : Blo 511796 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B769355 : Blo 511796 769355 := bstep (se 1 (by rfl) ⟨577016, by rfl⟩ : syracuseStep 769355 = 1154033) B1154033
theorem B769367 : Blo 511796 769367 := bstep (se 1 (by rfl) ⟨577025, by rfl⟩ : syracuseStep 769367 = 1154051) B1154051
theorem B769433 : Blo 511796 769433 := bstep (se 2 (by rfl) ⟨288537, by rfl⟩ : syracuseStep 769433 = 577075) B577075
theorem B769547 : Blo 511796 769547 := bstep (se 1 (by rfl) ⟨577160, by rfl⟩ : syracuseStep 769547 = 1154321) B1154321
theorem B769559 : Blo 511796 769559 := bstep (se 1 (by rfl) ⟨577169, by rfl⟩ : syracuseStep 769559 = 1154339) B1154339
theorem B769625 : Blo 511796 769625 := bstep (se 2 (by rfl) ⟨288609, by rfl⟩ : syracuseStep 769625 = 577219) B577219
theorem B11878019 : Blo 511796 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B769739 : Blo 511796 769739 := bstep (se 1 (by rfl) ⟨577304, by rfl⟩ : syracuseStep 769739 = 1154609) B1154609
theorem B868043 : Blo 511796 868043 := bstep (se 1 (by rfl) ⟨651032, by rfl⟩ : syracuseStep 868043 = 1302065) B1302065
theorem B769751 : Blo 511796 769751 := bstep (se 1 (by rfl) ⟨577313, by rfl⟩ : syracuseStep 769751 = 1154627) B1154627
theorem B769817 : Blo 511796 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B868171 : Blo 511796 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B769931 : Blo 511796 769931 := bstep (se 1 (by rfl) ⟨577448, by rfl⟩ : syracuseStep 769931 = 1154897) B1154897
theorem B769943 : Blo 511796 769943 := bstep (se 1 (by rfl) ⟨577457, by rfl⟩ : syracuseStep 769943 = 1154915) B1154915
theorem B2932631 : Blo 511796 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B14106545 : Blo 511796 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B2473907 : Blo 511796 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1097687 : Blo 511796 1097687 := bstep (se 1 (by rfl) ⟨823265, by rfl⟩ : syracuseStep 1097687 = 1646531) B1646531
theorem B1458137 : Blo 511796 1458137 := bstep (se 2 (by rfl) ⟨546801, by rfl⟩ : syracuseStep 1458137 = 1093603) B1093603
theorem B770009 : Blo 511796 770009 := bstep (se 2 (by rfl) ⟨288753, by rfl⟩ : syracuseStep 770009 = 577507) B577507
theorem B868313 : Blo 511796 868313 := bstep (se 2 (by rfl) ⟨325617, by rfl⟩ : syracuseStep 868313 = 651235) B651235
theorem B1949741 : Blo 511796 1949741 := bstep (se 3 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 1949741 = 731153) B731153
theorem B2605121 : Blo 511796 2605121 := bstep (se 2 (by rfl) ⟨976920, by rfl⟩ : syracuseStep 2605121 = 1953841) B1953841
theorem B770123 : Blo 511796 770123 := bstep (se 1 (by rfl) ⟨577592, by rfl⟩ : syracuseStep 770123 = 1155185) B1155185
theorem B1949771 : Blo 511796 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B770135 : Blo 511796 770135 := bstep (se 1 (by rfl) ⟨577601, by rfl⟩ : syracuseStep 770135 = 1155203) B1155203
theorem B868441 : Blo 511796 868441 := bstep (se 2 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 868441 = 651331) B651331
theorem B1097867 : Blo 511796 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B770201 : Blo 511796 770201 := bstep (se 2 (by rfl) ⟨288825, by rfl⟩ : syracuseStep 770201 = 577651) B577651
theorem B770315 : Blo 511796 770315 := bstep (se 1 (by rfl) ⟨577736, by rfl⟩ : syracuseStep 770315 = 1155473) B1155473
theorem B770327 : Blo 511796 770327 := bstep (se 1 (by rfl) ⟨577745, by rfl⟩ : syracuseStep 770327 = 1155491) B1155491
theorem B770393 : Blo 511796 770393 := bstep (se 2 (by rfl) ⟨288897, by rfl⟩ : syracuseStep 770393 = 577795) B577795
theorem B3129779 : Blo 511796 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B770507 : Blo 511796 770507 := bstep (se 1 (by rfl) ⟨577880, by rfl⟩ : syracuseStep 770507 = 1155761) B1155761
theorem B770519 : Blo 511796 770519 := bstep (se 1 (by rfl) ⟨577889, by rfl⟩ : syracuseStep 770519 = 1155779) B1155779
theorem B770585 : Blo 511796 770585 := bstep (se 2 (by rfl) ⟨288969, by rfl⟩ : syracuseStep 770585 = 577939) B577939
theorem B770699 : Blo 511796 770699 := bstep (se 1 (by rfl) ⟨578024, by rfl⟩ : syracuseStep 770699 = 1156049) B1156049
theorem B770711 : Blo 511796 770711 := bstep (se 1 (by rfl) ⟨578033, by rfl⟩ : syracuseStep 770711 = 1156067) B1156067
theorem B869015 : Blo 511796 869015 := bstep (se 1 (by rfl) ⟨651761, by rfl⟩ : syracuseStep 869015 = 1303523) B1303523
theorem B1950425 : Blo 511796 1950425 := bstep (se 2 (by rfl) ⟨731409, by rfl⟩ : syracuseStep 1950425 = 1462819) B1462819
theorem B770777 : Blo 511796 770777 := bstep (se 2 (by rfl) ⟨289041, by rfl⟩ : syracuseStep 770777 = 578083) B578083
theorem B869143 : Blo 511796 869143 := bstep (se 1 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 869143 = 1303715) B1303715
theorem B1557299 : Blo 511796 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B770891 : Blo 511796 770891 := bstep (se 1 (by rfl) ⟨578168, by rfl⟩ : syracuseStep 770891 = 1156337) B1156337
theorem B770903 : Blo 511796 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B770969 : Blo 511796 770969 := bstep (se 2 (by rfl) ⟨289113, by rfl⟩ : syracuseStep 770969 = 578227) B578227
theorem B1557469 : Blo 511796 1557469 := bstep (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) B584051
theorem B771083 : Blo 511796 771083 := bstep (se 1 (by rfl) ⟨578312, by rfl⟩ : syracuseStep 771083 = 1156625) B1156625
theorem B1852433 : Blo 511796 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B1950743 : Blo 511796 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B771095 : Blo 511796 771095 := bstep (se 1 (by rfl) ⟨578321, by rfl⟩ : syracuseStep 771095 = 1156643) B1156643
theorem B1557593 : Blo 511796 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B771161 : Blo 511796 771161 := bstep (se 2 (by rfl) ⟨289185, by rfl⟩ : syracuseStep 771161 = 578371) B578371
theorem B771275 : Blo 511796 771275 := bstep (se 1 (by rfl) ⟨578456, by rfl⟩ : syracuseStep 771275 = 1156913) B1156913
theorem B771287 : Blo 511796 771287 := bstep (se 1 (by rfl) ⟨578465, by rfl⟩ : syracuseStep 771287 = 1156931) B1156931
theorem B1557725 : Blo 511796 1557725 := bstep (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) B584147
theorem B771353 : Blo 511796 771353 := bstep (se 2 (by rfl) ⟨289257, by rfl⟩ : syracuseStep 771353 = 578515) B578515
theorem B1459549 : Blo 511796 1459549 := bstep (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) B547331
theorem B771467 : Blo 511796 771467 := bstep (se 1 (by rfl) ⟨578600, by rfl⟩ : syracuseStep 771467 = 1157201) B1157201
theorem B869771 : Blo 511796 869771 := bstep (se 1 (by rfl) ⟨652328, by rfl⟩ : syracuseStep 869771 = 1304657) B1304657
theorem B771479 : Blo 511796 771479 := bstep (se 1 (by rfl) ⟨578609, by rfl⟩ : syracuseStep 771479 = 1157219) B1157219
theorem B1754561 : Blo 511796 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B771545 : Blo 511796 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B869899 : Blo 511796 869899 := bstep (se 1 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 869899 = 1304849) B1304849
theorem B1459777 : Blo 511796 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B771659 : Blo 511796 771659 := bstep (se 1 (by rfl) ⟨578744, by rfl⟩ : syracuseStep 771659 = 1157489) B1157489
theorem B771671 : Blo 511796 771671 := bstep (se 1 (by rfl) ⟨578753, by rfl⟩ : syracuseStep 771671 = 1157507) B1157507
theorem B771737 : Blo 511796 771737 := bstep (se 2 (by rfl) ⟨289401, by rfl⟩ : syracuseStep 771737 = 578803) B578803
theorem B870041 : Blo 511796 870041 := bstep (se 2 (by rfl) ⟨326265, by rfl⟩ : syracuseStep 870041 = 652531) B652531
theorem B1951411 : Blo 511796 1951411 := bstep (se 1 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 1951411 = 2927117) B2927117
theorem B4933325 : Blo 511796 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B1099507 : Blo 511796 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B1984259 : Blo 511796 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B771851 : Blo 511796 771851 := bstep (se 1 (by rfl) ⟨578888, by rfl⟩ : syracuseStep 771851 = 1157777) B1157777
theorem B771863 : Blo 511796 771863 := bstep (se 1 (by rfl) ⟨578897, by rfl⟩ : syracuseStep 771863 = 1157795) B1157795
theorem B870169 : Blo 511796 870169 := bstep (se 2 (by rfl) ⟨326313, by rfl⟩ : syracuseStep 870169 = 652627) B652627
theorem B771929 : Blo 511796 771929 := bstep (se 2 (by rfl) ⟨289473, by rfl⟩ : syracuseStep 771929 = 578947) B578947
theorem B3131237 : Blo 511796 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B1460119 : Blo 511796 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B772043 : Blo 511796 772043 := bstep (se 1 (by rfl) ⟨579032, by rfl⟩ : syracuseStep 772043 = 1158065) B1158065
theorem B772055 : Blo 511796 772055 := bstep (se 1 (by rfl) ⟨579041, by rfl⟩ : syracuseStep 772055 = 1158083) B1158083
theorem B2607065 : Blo 511796 2607065 := bstep (se 2 (by rfl) ⟨977649, by rfl⟩ : syracuseStep 2607065 = 1955299) B1955299
theorem B1230871 : Blo 511796 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B772121 : Blo 511796 772121 := bstep (se 2 (by rfl) ⟨289545, by rfl⟩ : syracuseStep 772121 = 579091) B579091
theorem B772235 : Blo 511796 772235 := bstep (se 1 (by rfl) ⟨579176, by rfl⟩ : syracuseStep 772235 = 1158353) B1158353
theorem B772247 : Blo 511796 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B1296587 : Blo 511796 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B772313 : Blo 511796 772313 := bstep (se 2 (by rfl) ⟨289617, by rfl⟩ : syracuseStep 772313 = 579235) B579235
theorem B1099993 : Blo 511796 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B772427 : Blo 511796 772427 := bstep (se 1 (by rfl) ⟨579320, by rfl⟩ : syracuseStep 772427 = 1158641) B1158641
theorem B2935115 : Blo 511796 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B772439 : Blo 511796 772439 := bstep (se 1 (by rfl) ⟨579329, by rfl⟩ : syracuseStep 772439 = 1158659) B1158659
theorem B575851 : Blo 511796 575851 := bstep (se 1 (by rfl) ⟨431888, by rfl⟩ : syracuseStep 575851 = 863777) B863777
theorem B772505 : Blo 511796 772505 := bstep (se 2 (by rfl) ⟨289689, by rfl⟩ : syracuseStep 772505 = 579379) B579379
theorem B575959 : Blo 511796 575959 := bstep (se 1 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 575959 = 863939) B863939
theorem B772619 : Blo 511796 772619 := bstep (se 1 (by rfl) ⟨579464, by rfl⟩ : syracuseStep 772619 = 1158929) B1158929
theorem B772631 : Blo 511796 772631 := bstep (se 1 (by rfl) ⟨579473, by rfl⟩ : syracuseStep 772631 = 1158947) B1158947
theorem B1460825 : Blo 511796 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B772697 : Blo 511796 772697 := bstep (se 2 (by rfl) ⟨289761, by rfl⟩ : syracuseStep 772697 = 579523) B579523
theorem B576139 : Blo 511796 576139 := bstep (se 1 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 576139 = 864209) B864209
theorem B772811 : Blo 511796 772811 := bstep (se 1 (by rfl) ⟨579608, by rfl⟩ : syracuseStep 772811 = 1159217) B1159217
theorem B772823 : Blo 511796 772823 := bstep (se 1 (by rfl) ⟨579617, by rfl⟩ : syracuseStep 772823 = 1159235) B1159235
theorem B20007665 : Blo 511796 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B576247 : Blo 511796 576247 := bstep (se 1 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 576247 = 864371) B864371
theorem B2771729 : Blo 511796 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B772889 : Blo 511796 772889 := bstep (se 2 (by rfl) ⟨289833, by rfl⟩ : syracuseStep 772889 = 579667) B579667
theorem B773003 : Blo 511796 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B1952657 : Blo 511796 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B773015 : Blo 511796 773015 := bstep (se 1 (by rfl) ⟨579761, by rfl⟩ : syracuseStep 773015 = 1159523) B1159523
theorem B576427 : Blo 511796 576427 := bstep (se 1 (by rfl) ⟨432320, by rfl⟩ : syracuseStep 576427 = 864641) B864641
theorem B773081 : Blo 511796 773081 := bstep (se 2 (by rfl) ⟨289905, by rfl⟩ : syracuseStep 773081 = 579811) B579811
theorem B576535 : Blo 511796 576535 := bstep (se 1 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 576535 = 864803) B864803
theorem B773195 : Blo 511796 773195 := bstep (se 1 (by rfl) ⟨579896, by rfl⟩ : syracuseStep 773195 = 1159793) B1159793
theorem B773207 : Blo 511796 773207 := bstep (se 1 (by rfl) ⟨579905, by rfl⟩ : syracuseStep 773207 = 1159811) B1159811
theorem B1297559 : Blo 511796 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B773273 : Blo 511796 773273 := bstep (se 2 (by rfl) ⟨289977, by rfl⟩ : syracuseStep 773273 = 579955) B579955
theorem B576715 : Blo 511796 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B773387 : Blo 511796 773387 := bstep (se 1 (by rfl) ⟨580040, by rfl⟩ : syracuseStep 773387 = 1160081) B1160081
theorem B773399 : Blo 511796 773399 := bstep (se 1 (by rfl) ⟨580049, by rfl⟩ : syracuseStep 773399 = 1160099) B1160099
theorem B576823 : Blo 511796 576823 := bstep (se 1 (by rfl) ⟨432617, by rfl⟩ : syracuseStep 576823 = 865235) B865235
theorem B773465 : Blo 511796 773465 := bstep (se 2 (by rfl) ⟨290049, by rfl⟩ : syracuseStep 773465 = 580099) B580099
theorem B4804019 : Blo 511796 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B1854913 : Blo 511796 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B773579 : Blo 511796 773579 := bstep (se 1 (by rfl) ⟨580184, by rfl⟩ : syracuseStep 773579 = 1160369) B1160369
theorem B3886541 : Blo 511796 3886541 := bstep (se 3 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 3886541 = 1457453) B1457453
theorem B773591 : Blo 511796 773591 := bstep (se 1 (by rfl) ⟨580193, by rfl⟩ : syracuseStep 773591 = 1160387) B1160387
theorem B577003 : Blo 511796 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B773657 : Blo 511796 773657 := bstep (se 2 (by rfl) ⟨290121, by rfl⟩ : syracuseStep 773657 = 580243) B580243
theorem B2608685 : Blo 511796 2608685 := bstep (se 3 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 2608685 = 978257) B978257
theorem B1101377 : Blo 511796 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B1953355 : Blo 511796 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B577111 : Blo 511796 577111 := bstep (se 1 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 577111 = 865667) B865667
theorem B577291 : Blo 511796 577291 := bstep (se 1 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 577291 = 865937) B865937
theorem B1298227 : Blo 511796 1298227 := bstep (se 1 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 1298227 = 1947341) B1947341
theorem B511799 : Blo 511796 511799 := bstep (se 1 (by rfl) ⟨383849, by rfl⟩ : syracuseStep 511799 = 767699) B767699
theorem B511819 : Blo 511796 511819 := bstep (se 1 (by rfl) ⟨383864, by rfl⟩ : syracuseStep 511819 = 767729) B767729
theorem B511831 : Blo 511796 511831 := bstep (se 1 (by rfl) ⟨383873, by rfl⟩ : syracuseStep 511831 = 767747) B767747
theorem B1953629 : Blo 511796 1953629 := bstep (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) B732611
theorem B29642597 : Blo 511796 29642597 := bstep (se 4 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 29642597 = 5557987) B5557987
theorem B511851 : Blo 511796 511851 := bstep (se 1 (by rfl) ⟨383888, by rfl⟩ : syracuseStep 511851 = 767777) B767777
theorem B511863 : Blo 511796 511863 := bstep (se 1 (by rfl) ⟨383897, by rfl⟩ : syracuseStep 511863 = 767795) B767795
theorem B577399 : Blo 511796 577399 := bstep (se 1 (by rfl) ⟨433049, by rfl⟩ : syracuseStep 577399 = 866099) B866099
theorem B511883 : Blo 511796 511883 := bstep (se 1 (by rfl) ⟨383912, by rfl⟩ : syracuseStep 511883 = 767825) B767825
theorem B511895 : Blo 511796 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B511915 : Blo 511796 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B3887027 : Blo 511796 3887027 := bstep (se 1 (by rfl) ⟨2915270, by rfl⟩ : syracuseStep 3887027 = 5830541) B5830541
theorem B511927 : Blo 511796 511927 := bstep (se 1 (by rfl) ⟨383945, by rfl⟩ : syracuseStep 511927 = 767891) B767891
theorem B1298369 : Blo 511796 1298369 := bstep (se 2 (by rfl) ⟨486888, by rfl⟩ : syracuseStep 1298369 = 973777) B973777
theorem B511947 : Blo 511796 511947 := bstep (se 1 (by rfl) ⟨383960, by rfl⟩ : syracuseStep 511947 = 767921) B767921
theorem B511959 : Blo 511796 511959 := bstep (se 1 (by rfl) ⟨383969, by rfl⟩ : syracuseStep 511959 = 767939) B767939
theorem B511979 : Blo 511796 511979 := bstep (se 1 (by rfl) ⟨383984, by rfl⟩ : syracuseStep 511979 = 767969) B767969
theorem B511991 : Blo 511796 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B512011 : Blo 511796 512011 := bstep (se 1 (by rfl) ⟨384008, by rfl⟩ : syracuseStep 512011 = 768017) B768017
theorem B512023 : Blo 511796 512023 := bstep (se 1 (by rfl) ⟨384017, by rfl⟩ : syracuseStep 512023 = 768035) B768035
theorem B512043 : Blo 511796 512043 := bstep (se 1 (by rfl) ⟨384032, by rfl⟩ : syracuseStep 512043 = 768065) B768065
theorem B577579 : Blo 511796 577579 := bstep (se 1 (by rfl) ⟨433184, by rfl⟩ : syracuseStep 577579 = 866369) B866369
theorem B512055 : Blo 511796 512055 := bstep (se 1 (by rfl) ⟨384041, by rfl⟩ : syracuseStep 512055 = 768083) B768083
theorem B512075 : Blo 511796 512075 := bstep (se 1 (by rfl) ⟨384056, by rfl⟩ : syracuseStep 512075 = 768113) B768113
theorem B512087 : Blo 511796 512087 := bstep (se 1 (by rfl) ⟨384065, by rfl⟩ : syracuseStep 512087 = 768131) B768131
theorem B512107 : Blo 511796 512107 := bstep (se 1 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 512107 = 768161) B768161
theorem B512119 : Blo 511796 512119 := bstep (se 1 (by rfl) ⟨384089, by rfl⟩ : syracuseStep 512119 = 768179) B768179
theorem B512139 : Blo 511796 512139 := bstep (se 1 (by rfl) ⟨384104, by rfl⟩ : syracuseStep 512139 = 768209) B768209
theorem B512151 : Blo 511796 512151 := bstep (se 1 (by rfl) ⟨384113, by rfl⟩ : syracuseStep 512151 = 768227) B768227
theorem B577687 : Blo 511796 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B512171 : Blo 511796 512171 := bstep (se 1 (by rfl) ⟨384128, by rfl⟩ : syracuseStep 512171 = 768257) B768257
theorem B512183 : Blo 511796 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B1462465 : Blo 511796 1462465 := bstep (se 2 (by rfl) ⟨548424, by rfl⟩ : syracuseStep 1462465 = 1096849) B1096849
theorem B512203 : Blo 511796 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B1560779 : Blo 511796 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B512215 : Blo 511796 512215 := bstep (se 1 (by rfl) ⟨384161, by rfl⟩ : syracuseStep 512215 = 768323) B768323
theorem B512235 : Blo 511796 512235 := bstep (se 1 (by rfl) ⟨384176, by rfl⟩ : syracuseStep 512235 = 768353) B768353
theorem B512247 : Blo 511796 512247 := bstep (se 1 (by rfl) ⟨384185, by rfl⟩ : syracuseStep 512247 = 768371) B768371
theorem B512267 : Blo 511796 512267 := bstep (se 1 (by rfl) ⟨384200, by rfl⟩ : syracuseStep 512267 = 768401) B768401
theorem B512279 : Blo 511796 512279 := bstep (se 1 (by rfl) ⟨384209, by rfl⟩ : syracuseStep 512279 = 768419) B768419
theorem B512299 : Blo 511796 512299 := bstep (se 1 (by rfl) ⟨384224, by rfl⟩ : syracuseStep 512299 = 768449) B768449
theorem B512311 : Blo 511796 512311 := bstep (se 1 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 512311 = 768467) B768467
theorem B512331 : Blo 511796 512331 := bstep (se 1 (by rfl) ⟨384248, by rfl⟩ : syracuseStep 512331 = 768497) B768497
theorem B577867 : Blo 511796 577867 := bstep (se 1 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 577867 = 866801) B866801
theorem B512343 : Blo 511796 512343 := bstep (se 1 (by rfl) ⟨384257, by rfl⟩ : syracuseStep 512343 = 768515) B768515
theorem B512363 : Blo 511796 512363 := bstep (se 1 (by rfl) ⟨384272, by rfl⟩ : syracuseStep 512363 = 768545) B768545
theorem B512375 : Blo 511796 512375 := bstep (se 1 (by rfl) ⟨384281, by rfl⟩ : syracuseStep 512375 = 768563) B768563
theorem B512395 : Blo 511796 512395 := bstep (se 1 (by rfl) ⟨384296, by rfl⟩ : syracuseStep 512395 = 768593) B768593
theorem B512407 : Blo 511796 512407 := bstep (se 1 (by rfl) ⟨384305, by rfl⟩ : syracuseStep 512407 = 768611) B768611
theorem B512427 : Blo 511796 512427 := bstep (se 1 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 512427 = 768641) B768641
theorem B512439 : Blo 511796 512439 := bstep (se 1 (by rfl) ⟨384329, by rfl⟩ : syracuseStep 512439 = 768659) B768659
theorem B577975 : Blo 511796 577975 := bstep (se 1 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 577975 = 866963) B866963
theorem B512459 : Blo 511796 512459 := bstep (se 1 (by rfl) ⟨384344, by rfl⟩ : syracuseStep 512459 = 768689) B768689
theorem B512471 : Blo 511796 512471 := bstep (se 1 (by rfl) ⟨384353, by rfl⟩ : syracuseStep 512471 = 768707) B768707
theorem B512491 : Blo 511796 512491 := bstep (se 1 (by rfl) ⟨384368, by rfl⟩ : syracuseStep 512491 = 768737) B768737
theorem B512503 : Blo 511796 512503 := bstep (se 1 (by rfl) ⟨384377, by rfl⟩ : syracuseStep 512503 = 768755) B768755
theorem B512523 : Blo 511796 512523 := bstep (se 1 (by rfl) ⟨384392, by rfl⟩ : syracuseStep 512523 = 768785) B768785
theorem B512535 : Blo 511796 512535 := bstep (se 1 (by rfl) ⟨384401, by rfl⟩ : syracuseStep 512535 = 768803) B768803
theorem B1954327 : Blo 511796 1954327 := bstep (se 1 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 1954327 = 2931491) B2931491
theorem B512555 : Blo 511796 512555 := bstep (se 1 (by rfl) ⟨384416, by rfl⟩ : syracuseStep 512555 = 768833) B768833
theorem B512567 : Blo 511796 512567 := bstep (se 1 (by rfl) ⟨384425, by rfl⟩ : syracuseStep 512567 = 768851) B768851
theorem B512587 : Blo 511796 512587 := bstep (se 1 (by rfl) ⟨384440, by rfl⟩ : syracuseStep 512587 = 768881) B768881
theorem B512599 : Blo 511796 512599 := bstep (se 1 (by rfl) ⟨384449, by rfl⟩ : syracuseStep 512599 = 768899) B768899
theorem B512619 : Blo 511796 512619 := bstep (se 1 (by rfl) ⟨384464, by rfl⟩ : syracuseStep 512619 = 768929) B768929
theorem B578155 : Blo 511796 578155 := bstep (se 1 (by rfl) ⟨433616, by rfl⟩ : syracuseStep 578155 = 867233) B867233
theorem B512631 : Blo 511796 512631 := bstep (se 1 (by rfl) ⟨384473, by rfl⟩ : syracuseStep 512631 = 768947) B768947
theorem B512651 : Blo 511796 512651 := bstep (se 1 (by rfl) ⟨384488, by rfl⟩ : syracuseStep 512651 = 768977) B768977
theorem B512663 : Blo 511796 512663 := bstep (se 1 (by rfl) ⟨384497, by rfl⟩ : syracuseStep 512663 = 768995) B768995
theorem B512683 : Blo 511796 512683 := bstep (se 1 (by rfl) ⟨384512, by rfl⟩ : syracuseStep 512683 = 769025) B769025
theorem B512695 : Blo 511796 512695 := bstep (se 1 (by rfl) ⟨384521, by rfl⟩ : syracuseStep 512695 = 769043) B769043
theorem B512715 : Blo 511796 512715 := bstep (se 1 (by rfl) ⟨384536, by rfl⟩ : syracuseStep 512715 = 769073) B769073
theorem B5558989 : Blo 511796 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B512727 : Blo 511796 512727 := bstep (se 1 (by rfl) ⟨384545, by rfl⟩ : syracuseStep 512727 = 769091) B769091
theorem B578263 : Blo 511796 578263 := bstep (se 1 (by rfl) ⟨433697, by rfl⟩ : syracuseStep 578263 = 867395) B867395
theorem B512747 : Blo 511796 512747 := bstep (se 1 (by rfl) ⟨384560, by rfl⟩ : syracuseStep 512747 = 769121) B769121
theorem B512759 : Blo 511796 512759 := bstep (se 1 (by rfl) ⟨384569, by rfl⟩ : syracuseStep 512759 = 769139) B769139
theorem B512779 : Blo 511796 512779 := bstep (se 1 (by rfl) ⟨384584, by rfl⟩ : syracuseStep 512779 = 769169) B769169
theorem B512791 : Blo 511796 512791 := bstep (se 1 (by rfl) ⟨384593, by rfl⟩ : syracuseStep 512791 = 769187) B769187
theorem B512811 : Blo 511796 512811 := bstep (se 1 (by rfl) ⟨384608, by rfl⟩ : syracuseStep 512811 = 769217) B769217
theorem B512823 : Blo 511796 512823 := bstep (se 1 (by rfl) ⟨384617, by rfl⟩ : syracuseStep 512823 = 769235) B769235
theorem B4379467 : Blo 511796 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B512843 : Blo 511796 512843 := bstep (se 1 (by rfl) ⟨384632, by rfl⟩ : syracuseStep 512843 = 769265) B769265
theorem B512855 : Blo 511796 512855 := bstep (se 1 (by rfl) ⟨384641, by rfl⟩ : syracuseStep 512855 = 769283) B769283
theorem B512875 : Blo 511796 512875 := bstep (se 1 (by rfl) ⟨384656, by rfl⟩ : syracuseStep 512875 = 769313) B769313
theorem B512887 : Blo 511796 512887 := bstep (se 1 (by rfl) ⟨384665, by rfl⟩ : syracuseStep 512887 = 769331) B769331
theorem B512907 : Blo 511796 512907 := bstep (se 1 (by rfl) ⟨384680, by rfl⟩ : syracuseStep 512907 = 769361) B769361
theorem B578443 : Blo 511796 578443 := bstep (se 1 (by rfl) ⟨433832, by rfl⟩ : syracuseStep 578443 = 867665) B867665
theorem B512919 : Blo 511796 512919 := bstep (se 1 (by rfl) ⟨384689, by rfl⟩ : syracuseStep 512919 = 769379) B769379
theorem B512939 : Blo 511796 512939 := bstep (se 1 (by rfl) ⟨384704, by rfl⟩ : syracuseStep 512939 = 769409) B769409
theorem B512951 : Blo 511796 512951 := bstep (se 1 (by rfl) ⟨384713, by rfl⟩ : syracuseStep 512951 = 769427) B769427
theorem B512971 : Blo 511796 512971 := bstep (se 1 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 512971 = 769457) B769457
theorem B512983 : Blo 511796 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B513003 : Blo 511796 513003 := bstep (se 1 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 513003 = 769505) B769505
theorem B513015 : Blo 511796 513015 := bstep (se 1 (by rfl) ⟨384761, by rfl⟩ : syracuseStep 513015 = 769523) B769523
theorem B578551 : Blo 511796 578551 := bstep (se 1 (by rfl) ⟨433913, by rfl⟩ : syracuseStep 578551 = 867827) B867827
theorem B513035 : Blo 511796 513035 := bstep (se 1 (by rfl) ⟨384776, by rfl⟩ : syracuseStep 513035 = 769553) B769553
theorem B513047 : Blo 511796 513047 := bstep (se 1 (by rfl) ⟨384785, by rfl⟩ : syracuseStep 513047 = 769571) B769571
theorem B513067 : Blo 511796 513067 := bstep (se 1 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 513067 = 769601) B769601
theorem B513079 : Blo 511796 513079 := bstep (se 1 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 513079 = 769619) B769619
theorem B513099 : Blo 511796 513099 := bstep (se 1 (by rfl) ⟨384824, by rfl⟩ : syracuseStep 513099 = 769649) B769649
theorem B513111 : Blo 511796 513111 := bstep (se 1 (by rfl) ⟨384833, by rfl⟩ : syracuseStep 513111 = 769667) B769667
theorem B4379741 : Blo 511796 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B513131 : Blo 511796 513131 := bstep (se 1 (by rfl) ⟨384848, by rfl⟩ : syracuseStep 513131 = 769697) B769697
theorem B513143 : Blo 511796 513143 := bstep (se 1 (by rfl) ⟨384857, by rfl⟩ : syracuseStep 513143 = 769715) B769715
theorem B513163 : Blo 511796 513163 := bstep (se 1 (by rfl) ⟨384872, by rfl⟩ : syracuseStep 513163 = 769745) B769745
theorem B513175 : Blo 511796 513175 := bstep (se 1 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 513175 = 769763) B769763
theorem B513195 : Blo 511796 513195 := bstep (se 1 (by rfl) ⟨384896, by rfl⟩ : syracuseStep 513195 = 769793) B769793
theorem B578731 : Blo 511796 578731 := bstep (se 1 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 578731 = 868097) B868097
theorem B1299635 : Blo 511796 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B513207 : Blo 511796 513207 := bstep (se 1 (by rfl) ⟨384905, by rfl⟩ : syracuseStep 513207 = 769811) B769811
theorem B513227 : Blo 511796 513227 := bstep (se 1 (by rfl) ⟨384920, by rfl⟩ : syracuseStep 513227 = 769841) B769841
theorem B513239 : Blo 511796 513239 := bstep (se 1 (by rfl) ⟨384929, by rfl⟩ : syracuseStep 513239 = 769859) B769859
theorem B1856729 : Blo 511796 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B971993 : Blo 511796 971993 := bstep (se 2 (by rfl) ⟨364497, by rfl⟩ : syracuseStep 971993 = 728995) B728995
theorem B513259 : Blo 511796 513259 := bstep (se 1 (by rfl) ⟨384944, by rfl⟩ : syracuseStep 513259 = 769889) B769889
theorem B513271 : Blo 511796 513271 := bstep (se 1 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 513271 = 769907) B769907
theorem B513291 : Blo 511796 513291 := bstep (se 1 (by rfl) ⟨384968, by rfl⟩ : syracuseStep 513291 = 769937) B769937
theorem B513303 : Blo 511796 513303 := bstep (se 1 (by rfl) ⟨384977, by rfl⟩ : syracuseStep 513303 = 769955) B769955
theorem B578839 : Blo 511796 578839 := bstep (se 1 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 578839 = 868259) B868259
theorem B513323 : Blo 511796 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B1955117 : Blo 511796 1955117 := bstep (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) B733169
theorem B513335 : Blo 511796 513335 := bstep (se 1 (by rfl) ⟨385001, by rfl⟩ : syracuseStep 513335 = 770003) B770003
theorem B513355 : Blo 511796 513355 := bstep (se 1 (by rfl) ⟨385016, by rfl⟩ : syracuseStep 513355 = 770033) B770033
theorem B513367 : Blo 511796 513367 := bstep (se 1 (by rfl) ⟨385025, by rfl⟩ : syracuseStep 513367 = 770051) B770051
theorem B3888485 : Blo 511796 3888485 := bstep (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) B729091
theorem B513387 : Blo 511796 513387 := bstep (se 1 (by rfl) ⟨385040, by rfl⟩ : syracuseStep 513387 = 770081) B770081
theorem B513399 : Blo 511796 513399 := bstep (se 1 (by rfl) ⟨385049, by rfl⟩ : syracuseStep 513399 = 770099) B770099
theorem B513419 : Blo 511796 513419 := bstep (se 1 (by rfl) ⟨385064, by rfl⟩ : syracuseStep 513419 = 770129) B770129
theorem B513431 : Blo 511796 513431 := bstep (se 1 (by rfl) ⟨385073, by rfl⟩ : syracuseStep 513431 = 770147) B770147
theorem B513451 : Blo 511796 513451 := bstep (se 1 (by rfl) ⟨385088, by rfl⟩ : syracuseStep 513451 = 770177) B770177
theorem B513463 : Blo 511796 513463 := bstep (se 1 (by rfl) ⟨385097, by rfl⟩ : syracuseStep 513463 = 770195) B770195
theorem B513483 : Blo 511796 513483 := bstep (se 1 (by rfl) ⟨385112, by rfl⟩ : syracuseStep 513483 = 770225) B770225
theorem B1234379 : Blo 511796 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B579019 : Blo 511796 579019 := bstep (se 1 (by rfl) ⟨434264, by rfl⟩ : syracuseStep 579019 = 868529) B868529
theorem B2119115 : Blo 511796 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B513495 : Blo 511796 513495 := bstep (se 1 (by rfl) ⟨385121, by rfl⟩ : syracuseStep 513495 = 770243) B770243
theorem B513515 : Blo 511796 513515 := bstep (se 1 (by rfl) ⟨385136, by rfl⟩ : syracuseStep 513515 = 770273) B770273
theorem B513527 : Blo 511796 513527 := bstep (se 1 (by rfl) ⟨385145, by rfl⟩ : syracuseStep 513527 = 770291) B770291
theorem B513547 : Blo 511796 513547 := bstep (se 1 (by rfl) ⟨385160, by rfl⟩ : syracuseStep 513547 = 770321) B770321
theorem B513559 : Blo 511796 513559 := bstep (se 1 (by rfl) ⟨385169, by rfl⟩ : syracuseStep 513559 = 770339) B770339
theorem B513579 : Blo 511796 513579 := bstep (se 1 (by rfl) ⟨385184, by rfl⟩ : syracuseStep 513579 = 770369) B770369
theorem B513591 : Blo 511796 513591 := bstep (se 1 (by rfl) ⟨385193, by rfl⟩ : syracuseStep 513591 = 770387) B770387
theorem B579127 : Blo 511796 579127 := bstep (se 1 (by rfl) ⟨434345, by rfl⟩ : syracuseStep 579127 = 868691) B868691
theorem B513611 : Blo 511796 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B513623 : Blo 511796 513623 := bstep (se 1 (by rfl) ⟨385217, by rfl⟩ : syracuseStep 513623 = 770435) B770435
theorem B4806245 : Blo 511796 4806245 := bstep (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) B901171
theorem B513643 : Blo 511796 513643 := bstep (se 1 (by rfl) ⟨385232, by rfl⟩ : syracuseStep 513643 = 770465) B770465
theorem B513655 : Blo 511796 513655 := bstep (se 1 (by rfl) ⟨385241, by rfl⟩ : syracuseStep 513655 = 770483) B770483
theorem B513675 : Blo 511796 513675 := bstep (se 1 (by rfl) ⟨385256, by rfl⟩ : syracuseStep 513675 = 770513) B770513
theorem B513687 : Blo 511796 513687 := bstep (se 1 (by rfl) ⟨385265, by rfl⟩ : syracuseStep 513687 = 770531) B770531
theorem B513707 : Blo 511796 513707 := bstep (se 1 (by rfl) ⟨385280, by rfl⟩ : syracuseStep 513707 = 770561) B770561
theorem B513719 : Blo 511796 513719 := bstep (se 1 (by rfl) ⟨385289, by rfl⟩ : syracuseStep 513719 = 770579) B770579
theorem B1300171 : Blo 511796 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B513739 : Blo 511796 513739 := bstep (se 1 (by rfl) ⟨385304, by rfl⟩ : syracuseStep 513739 = 770609) B770609
theorem B513751 : Blo 511796 513751 := bstep (se 1 (by rfl) ⟨385313, by rfl⟩ : syracuseStep 513751 = 770627) B770627
theorem B513771 : Blo 511796 513771 := bstep (se 1 (by rfl) ⟨385328, by rfl⟩ : syracuseStep 513771 = 770657) B770657
theorem B579307 : Blo 511796 579307 := bstep (se 1 (by rfl) ⟨434480, by rfl⟩ : syracuseStep 579307 = 868961) B868961
theorem B513783 : Blo 511796 513783 := bstep (se 1 (by rfl) ⟨385337, by rfl⟩ : syracuseStep 513783 = 770675) B770675
theorem B513803 : Blo 511796 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B513815 : Blo 511796 513815 := bstep (se 1 (by rfl) ⟨385361, by rfl⟩ : syracuseStep 513815 = 770723) B770723
theorem B513835 : Blo 511796 513835 := bstep (se 1 (by rfl) ⟨385376, by rfl⟩ : syracuseStep 513835 = 770753) B770753
theorem B513847 : Blo 511796 513847 := bstep (se 1 (by rfl) ⟨385385, by rfl⟩ : syracuseStep 513847 = 770771) B770771
theorem B3888971 : Blo 511796 3888971 := bstep (se 1 (by rfl) ⟨2916728, by rfl⟩ : syracuseStep 3888971 = 5833457) B5833457
theorem B513867 : Blo 511796 513867 := bstep (se 1 (by rfl) ⟨385400, by rfl⟩ : syracuseStep 513867 = 770801) B770801
theorem B513879 : Blo 511796 513879 := bstep (se 1 (by rfl) ⟨385409, by rfl⟩ : syracuseStep 513879 = 770819) B770819
theorem B1300313 : Blo 511796 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B579415 : Blo 511796 579415 := bstep (se 1 (by rfl) ⟨434561, by rfl⟩ : syracuseStep 579415 = 869123) B869123
theorem B513899 : Blo 511796 513899 := bstep (se 1 (by rfl) ⟨385424, by rfl⟩ : syracuseStep 513899 = 770849) B770849
theorem B513911 : Blo 511796 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B513931 : Blo 511796 513931 := bstep (se 1 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 513931 = 770897) B770897
theorem B513943 : Blo 511796 513943 := bstep (se 1 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 513943 = 770915) B770915
theorem B513963 : Blo 511796 513963 := bstep (se 1 (by rfl) ⟨385472, by rfl⟩ : syracuseStep 513963 = 770945) B770945
theorem B513975 : Blo 511796 513975 := bstep (se 1 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 513975 = 770963) B770963
theorem B513995 : Blo 511796 513995 := bstep (se 1 (by rfl) ⟨385496, by rfl⟩ : syracuseStep 513995 = 770993) B770993
theorem B514007 : Blo 511796 514007 := bstep (se 1 (by rfl) ⟨385505, by rfl⟩ : syracuseStep 514007 = 771011) B771011
theorem B514027 : Blo 511796 514027 := bstep (se 1 (by rfl) ⟨385520, by rfl⟩ : syracuseStep 514027 = 771041) B771041
theorem B514039 : Blo 511796 514039 := bstep (se 1 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 514039 = 771059) B771059
theorem B514059 : Blo 511796 514059 := bstep (se 1 (by rfl) ⟨385544, by rfl⟩ : syracuseStep 514059 = 771089) B771089
theorem B579595 : Blo 511796 579595 := bstep (se 1 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 579595 = 869393) B869393
theorem B2250775 : Blo 511796 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B514071 : Blo 511796 514071 := bstep (se 1 (by rfl) ⟨385553, by rfl⟩ : syracuseStep 514071 = 771107) B771107
theorem B514091 : Blo 511796 514091 := bstep (se 1 (by rfl) ⟨385568, by rfl⟩ : syracuseStep 514091 = 771137) B771137
theorem B514103 : Blo 511796 514103 := bstep (se 1 (by rfl) ⟨385577, by rfl⟩ : syracuseStep 514103 = 771155) B771155
theorem B514123 : Blo 511796 514123 := bstep (se 1 (by rfl) ⟨385592, by rfl⟩ : syracuseStep 514123 = 771185) B771185
theorem B514135 : Blo 511796 514135 := bstep (se 1 (by rfl) ⟨385601, by rfl⟩ : syracuseStep 514135 = 771203) B771203
theorem B1235033 : Blo 511796 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B514155 : Blo 511796 514155 := bstep (se 1 (by rfl) ⟨385616, by rfl⟩ : syracuseStep 514155 = 771233) B771233
theorem B514167 : Blo 511796 514167 := bstep (se 1 (by rfl) ⟨385625, by rfl⟩ : syracuseStep 514167 = 771251) B771251
theorem B579703 : Blo 511796 579703 := bstep (se 1 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 579703 = 869555) B869555
theorem B4380803 : Blo 511796 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B546955 : Blo 511796 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B514187 : Blo 511796 514187 := bstep (se 1 (by rfl) ⟨385640, by rfl⟩ : syracuseStep 514187 = 771281) B771281
theorem B514199 : Blo 511796 514199 := bstep (se 1 (by rfl) ⟨385649, by rfl⟩ : syracuseStep 514199 = 771299) B771299
theorem B514219 : Blo 511796 514219 := bstep (se 1 (by rfl) ⟨385664, by rfl⟩ : syracuseStep 514219 = 771329) B771329
theorem B514231 : Blo 511796 514231 := bstep (se 1 (by rfl) ⟨385673, by rfl⟩ : syracuseStep 514231 = 771347) B771347
theorem B514251 : Blo 511796 514251 := bstep (se 1 (by rfl) ⟨385688, by rfl⟩ : syracuseStep 514251 = 771377) B771377
theorem B514263 : Blo 511796 514263 := bstep (se 1 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 514263 = 771395) B771395
theorem B514283 : Blo 511796 514283 := bstep (se 1 (by rfl) ⟨385712, by rfl⟩ : syracuseStep 514283 = 771425) B771425
theorem B514295 : Blo 511796 514295 := bstep (se 1 (by rfl) ⟨385721, by rfl⟩ : syracuseStep 514295 = 771443) B771443
theorem B514315 : Blo 511796 514315 := bstep (se 1 (by rfl) ⟨385736, by rfl⟩ : syracuseStep 514315 = 771473) B771473
theorem B514327 : Blo 511796 514327 := bstep (se 1 (by rfl) ⟨385745, by rfl⟩ : syracuseStep 514327 = 771491) B771491
theorem B514347 : Blo 511796 514347 := bstep (se 1 (by rfl) ⟨385760, by rfl⟩ : syracuseStep 514347 = 771521) B771521
theorem B579883 : Blo 511796 579883 := bstep (se 1 (by rfl) ⟨434912, by rfl⟩ : syracuseStep 579883 = 869825) B869825
theorem B514359 : Blo 511796 514359 := bstep (se 1 (by rfl) ⟨385769, by rfl⟩ : syracuseStep 514359 = 771539) B771539
theorem B514379 : Blo 511796 514379 := bstep (se 1 (by rfl) ⟨385784, by rfl⟩ : syracuseStep 514379 = 771569) B771569
theorem B514391 : Blo 511796 514391 := bstep (se 1 (by rfl) ⟨385793, by rfl⟩ : syracuseStep 514391 = 771587) B771587
theorem B514411 : Blo 511796 514411 := bstep (se 1 (by rfl) ⟨385808, by rfl⟩ : syracuseStep 514411 = 771617) B771617
theorem B514423 : Blo 511796 514423 := bstep (se 1 (by rfl) ⟨385817, by rfl⟩ : syracuseStep 514423 = 771635) B771635
theorem B514443 : Blo 511796 514443 := bstep (se 1 (by rfl) ⟨385832, by rfl⟩ : syracuseStep 514443 = 771665) B771665
theorem B514455 : Blo 511796 514455 := bstep (se 1 (by rfl) ⟨385841, by rfl⟩ : syracuseStep 514455 = 771683) B771683
theorem B579991 : Blo 511796 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B514475 : Blo 511796 514475 := bstep (se 1 (by rfl) ⟨385856, by rfl⟩ : syracuseStep 514475 = 771713) B771713
theorem B514487 : Blo 511796 514487 := bstep (se 1 (by rfl) ⟨385865, by rfl⟩ : syracuseStep 514487 = 771731) B771731
theorem B514507 : Blo 511796 514507 := bstep (se 1 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 514507 = 771761) B771761
theorem B514519 : Blo 511796 514519 := bstep (se 1 (by rfl) ⟨385889, by rfl⟩ : syracuseStep 514519 = 771779) B771779
theorem B514539 : Blo 511796 514539 := bstep (se 1 (by rfl) ⟨385904, by rfl⟩ : syracuseStep 514539 = 771809) B771809
theorem B514551 : Blo 511796 514551 := bstep (se 1 (by rfl) ⟨385913, by rfl⟩ : syracuseStep 514551 = 771827) B771827
theorem B514571 : Blo 511796 514571 := bstep (se 1 (by rfl) ⟨385928, by rfl⟩ : syracuseStep 514571 = 771857) B771857
theorem B514583 : Blo 511796 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B514603 : Blo 511796 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B514615 : Blo 511796 514615 := bstep (se 1 (by rfl) ⟨385961, by rfl⟩ : syracuseStep 514615 = 771923) B771923
theorem B514635 : Blo 511796 514635 := bstep (se 1 (by rfl) ⟨385976, by rfl⟩ : syracuseStep 514635 = 771953) B771953
theorem B580171 : Blo 511796 580171 := bstep (se 1 (by rfl) ⟨435128, by rfl⟩ : syracuseStep 580171 = 870257) B870257
theorem B514647 : Blo 511796 514647 := bstep (se 1 (by rfl) ⟨385985, by rfl⟩ : syracuseStep 514647 = 771971) B771971
theorem B2415193 : Blo 511796 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B514667 : Blo 511796 514667 := bstep (se 1 (by rfl) ⟨386000, by rfl⟩ : syracuseStep 514667 = 772001) B772001
theorem B514679 : Blo 511796 514679 := bstep (se 1 (by rfl) ⟨386009, by rfl⟩ : syracuseStep 514679 = 772019) B772019
theorem B973451 : Blo 511796 973451 := bstep (se 1 (by rfl) ⟨730088, by rfl⟩ : syracuseStep 973451 = 1460177) B1460177
theorem B514699 : Blo 511796 514699 := bstep (se 1 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 514699 = 772049) B772049
theorem B1301143 : Blo 511796 1301143 := bstep (se 1 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 1301143 = 1951715) B1951715
theorem B514711 : Blo 511796 514711 := bstep (se 1 (by rfl) ⟨386033, by rfl⟩ : syracuseStep 514711 = 772067) B772067
theorem B514731 : Blo 511796 514731 := bstep (se 1 (by rfl) ⟨386048, by rfl⟩ : syracuseStep 514731 = 772097) B772097
theorem B514743 : Blo 511796 514743 := bstep (se 1 (by rfl) ⟨386057, by rfl⟩ : syracuseStep 514743 = 772115) B772115
theorem B1956545 : Blo 511796 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B514763 : Blo 511796 514763 := bstep (se 1 (by rfl) ⟨386072, by rfl⟩ : syracuseStep 514763 = 772145) B772145
theorem B6675149 : Blo 511796 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B514775 : Blo 511796 514775 := bstep (se 1 (by rfl) ⟨386081, by rfl⟩ : syracuseStep 514775 = 772163) B772163
theorem B514795 : Blo 511796 514795 := bstep (se 1 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 514795 = 772193) B772193
theorem B514807 : Blo 511796 514807 := bstep (se 1 (by rfl) ⟨386105, by rfl⟩ : syracuseStep 514807 = 772211) B772211
theorem B514827 : Blo 511796 514827 := bstep (se 1 (by rfl) ⟨386120, by rfl⟩ : syracuseStep 514827 = 772241) B772241
theorem B514839 : Blo 511796 514839 := bstep (se 1 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 514839 = 772259) B772259
theorem B514859 : Blo 511796 514859 := bstep (se 1 (by rfl) ⟨386144, by rfl⟩ : syracuseStep 514859 = 772289) B772289
theorem B514871 : Blo 511796 514871 := bstep (se 1 (by rfl) ⟨386153, by rfl⟩ : syracuseStep 514871 = 772307) B772307
theorem B973633 : Blo 511796 973633 := bstep (se 2 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 973633 = 730225) B730225
theorem B514891 : Blo 511796 514891 := bstep (se 1 (by rfl) ⟨386168, by rfl⟩ : syracuseStep 514891 = 772337) B772337
theorem B514903 : Blo 511796 514903 := bstep (se 1 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 514903 = 772355) B772355
theorem B514923 : Blo 511796 514923 := bstep (se 1 (by rfl) ⟨386192, by rfl⟩ : syracuseStep 514923 = 772385) B772385
theorem B514935 : Blo 511796 514935 := bstep (se 1 (by rfl) ⟨386201, by rfl⟩ : syracuseStep 514935 = 772403) B772403
theorem B514955 : Blo 511796 514955 := bstep (se 1 (by rfl) ⟨386216, by rfl⟩ : syracuseStep 514955 = 772433) B772433
theorem B514967 : Blo 511796 514967 := bstep (se 1 (by rfl) ⟨386225, by rfl⟩ : syracuseStep 514967 = 772451) B772451
theorem B514987 : Blo 511796 514987 := bstep (se 1 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 514987 = 772481) B772481
theorem B3431347 : Blo 511796 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B514999 : Blo 511796 514999 := bstep (se 1 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 514999 = 772499) B772499
theorem B515019 : Blo 511796 515019 := bstep (se 1 (by rfl) ⟨386264, by rfl⟩ : syracuseStep 515019 = 772529) B772529
theorem B515031 : Blo 511796 515031 := bstep (se 1 (by rfl) ⟨386273, by rfl⟩ : syracuseStep 515031 = 772547) B772547
theorem B515051 : Blo 511796 515051 := bstep (se 1 (by rfl) ⟨386288, by rfl⟩ : syracuseStep 515051 = 772577) B772577
theorem B515063 : Blo 511796 515063 := bstep (se 1 (by rfl) ⟨386297, by rfl⟩ : syracuseStep 515063 = 772595) B772595
theorem B515083 : Blo 511796 515083 := bstep (se 1 (by rfl) ⟨386312, by rfl⟩ : syracuseStep 515083 = 772625) B772625
theorem B515095 : Blo 511796 515095 := bstep (se 1 (by rfl) ⟨386321, by rfl⟩ : syracuseStep 515095 = 772643) B772643
theorem B515115 : Blo 511796 515115 := bstep (se 1 (by rfl) ⟨386336, by rfl⟩ : syracuseStep 515115 = 772673) B772673
theorem B547895 : Blo 511796 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B515127 : Blo 511796 515127 := bstep (se 1 (by rfl) ⟨386345, by rfl⟩ : syracuseStep 515127 = 772691) B772691
theorem B1301579 : Blo 511796 1301579 := bstep (se 1 (by rfl) ⟨976184, by rfl⟩ : syracuseStep 1301579 = 1952369) B1952369
theorem B515147 : Blo 511796 515147 := bstep (se 1 (by rfl) ⟨386360, by rfl⟩ : syracuseStep 515147 = 772721) B772721
theorem B515159 : Blo 511796 515159 := bstep (se 1 (by rfl) ⟨386369, by rfl⟩ : syracuseStep 515159 = 772739) B772739
theorem B515179 : Blo 511796 515179 := bstep (se 1 (by rfl) ⟨386384, by rfl⟩ : syracuseStep 515179 = 772769) B772769
theorem B515191 : Blo 511796 515191 := bstep (se 1 (by rfl) ⟨386393, by rfl⟩ : syracuseStep 515191 = 772787) B772787
theorem B515211 : Blo 511796 515211 := bstep (se 1 (by rfl) ⟨386408, by rfl⟩ : syracuseStep 515211 = 772817) B772817
theorem B515223 : Blo 511796 515223 := bstep (se 1 (by rfl) ⟨386417, by rfl⟩ : syracuseStep 515223 = 772835) B772835
theorem B515243 : Blo 511796 515243 := bstep (se 1 (by rfl) ⟨386432, by rfl⟩ : syracuseStep 515243 = 772865) B772865
theorem B515255 : Blo 511796 515255 := bstep (se 1 (by rfl) ⟨386441, by rfl⟩ : syracuseStep 515255 = 772883) B772883
theorem B2088139 : Blo 511796 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B515275 : Blo 511796 515275 := bstep (se 1 (by rfl) ⟨386456, by rfl⟩ : syracuseStep 515275 = 772913) B772913
theorem B1858763 : Blo 511796 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B515287 : Blo 511796 515287 := bstep (se 1 (by rfl) ⟨386465, by rfl⟩ : syracuseStep 515287 = 772931) B772931
theorem B515307 : Blo 511796 515307 := bstep (se 1 (by rfl) ⟨386480, by rfl⟩ : syracuseStep 515307 = 772961) B772961
theorem B515319 : Blo 511796 515319 := bstep (se 1 (by rfl) ⟨386489, by rfl⟩ : syracuseStep 515319 = 772979) B772979
theorem B974081 : Blo 511796 974081 := bstep (se 2 (by rfl) ⟨365280, by rfl⟩ : syracuseStep 974081 = 730561) B730561
theorem B515339 : Blo 511796 515339 := bstep (se 1 (by rfl) ⟨386504, by rfl⟩ : syracuseStep 515339 = 773009) B773009
theorem B515351 : Blo 511796 515351 := bstep (se 1 (by rfl) ⟨386513, by rfl⟩ : syracuseStep 515351 = 773027) B773027
theorem B515371 : Blo 511796 515371 := bstep (se 1 (by rfl) ⟨386528, by rfl⟩ : syracuseStep 515371 = 773057) B773057
theorem B515383 : Blo 511796 515383 := bstep (se 1 (by rfl) ⟨386537, by rfl⟩ : syracuseStep 515383 = 773075) B773075
theorem B515403 : Blo 511796 515403 := bstep (se 1 (by rfl) ⟨386552, by rfl⟩ : syracuseStep 515403 = 773105) B773105
theorem B1858891 : Blo 511796 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B941399 : Blo 511796 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B515415 : Blo 511796 515415 := bstep (se 1 (by rfl) ⟨386561, by rfl⟩ : syracuseStep 515415 = 773123) B773123
theorem B1727837 : Blo 511796 1727837 := bstep (se 3 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 1727837 = 647939) B647939
theorem B3333469 : Blo 511796 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B515435 : Blo 511796 515435 := bstep (se 1 (by rfl) ⟨386576, by rfl⟩ : syracuseStep 515435 = 773153) B773153
theorem B1170803 : Blo 511796 1170803 := bstep (se 1 (by rfl) ⟨878102, by rfl⟩ : syracuseStep 1170803 = 1756205) B1756205
theorem B515447 : Blo 511796 515447 := bstep (se 1 (by rfl) ⟨386585, by rfl⟩ : syracuseStep 515447 = 773171) B773171
theorem B515467 : Blo 511796 515467 := bstep (se 1 (by rfl) ⟨386600, by rfl⟩ : syracuseStep 515467 = 773201) B773201
theorem B515479 : Blo 511796 515479 := bstep (se 1 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 515479 = 773219) B773219
theorem B515499 : Blo 511796 515499 := bstep (se 1 (by rfl) ⟨386624, by rfl⟩ : syracuseStep 515499 = 773249) B773249
theorem B515511 : Blo 511796 515511 := bstep (se 1 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 515511 = 773267) B773267
theorem B1301953 : Blo 511796 1301953 := bstep (se 2 (by rfl) ⟨488232, by rfl⟩ : syracuseStep 1301953 = 976465) B976465
theorem B515531 : Blo 511796 515531 := bstep (se 1 (by rfl) ⟨386648, by rfl⟩ : syracuseStep 515531 = 773297) B773297
theorem B515543 : Blo 511796 515543 := bstep (se 1 (by rfl) ⟨386657, by rfl⟩ : syracuseStep 515543 = 773315) B773315
theorem B515563 : Blo 511796 515563 := bstep (se 1 (by rfl) ⟨386672, by rfl⟩ : syracuseStep 515563 = 773345) B773345
theorem B515575 : Blo 511796 515575 := bstep (se 1 (by rfl) ⟨386681, by rfl⟩ : syracuseStep 515575 = 773363) B773363
theorem B3694085 : Blo 511796 3694085 := bstep (se 4 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 3694085 = 692641) B692641
theorem B515595 : Blo 511796 515595 := bstep (se 1 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 515595 = 773393) B773393
theorem B5856785 : Blo 511796 5856785 := bstep (se 2 (by rfl) ⟨2196294, by rfl⟩ : syracuseStep 5856785 = 4392589) B4392589
theorem B515607 : Blo 511796 515607 := bstep (se 1 (by rfl) ⟨386705, by rfl⟩ : syracuseStep 515607 = 773411) B773411
theorem B515627 : Blo 511796 515627 := bstep (se 1 (by rfl) ⟨386720, by rfl⟩ : syracuseStep 515627 = 773441) B773441
theorem B515639 : Blo 511796 515639 := bstep (se 1 (by rfl) ⟨386729, by rfl⟩ : syracuseStep 515639 = 773459) B773459
theorem B515659 : Blo 511796 515659 := bstep (se 1 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 515659 = 773489) B773489
theorem B974423 : Blo 511796 974423 := bstep (se 1 (by rfl) ⟨730817, by rfl⟩ : syracuseStep 974423 = 1461635) B1461635
theorem B515671 : Blo 511796 515671 := bstep (se 1 (by rfl) ⟨386753, by rfl⟩ : syracuseStep 515671 = 773507) B773507
theorem B515691 : Blo 511796 515691 := bstep (se 1 (by rfl) ⟨386768, by rfl⟩ : syracuseStep 515691 = 773537) B773537
theorem B515703 : Blo 511796 515703 := bstep (se 1 (by rfl) ⟨386777, by rfl⟩ : syracuseStep 515703 = 773555) B773555
theorem B515723 : Blo 511796 515723 := bstep (se 1 (by rfl) ⟨386792, by rfl⟩ : syracuseStep 515723 = 773585) B773585
theorem B515735 : Blo 511796 515735 := bstep (se 1 (by rfl) ⟨386801, by rfl⟩ : syracuseStep 515735 = 773603) B773603
theorem B515755 : Blo 511796 515755 := bstep (se 1 (by rfl) ⟨386816, by rfl⟩ : syracuseStep 515755 = 773633) B773633
theorem B515767 : Blo 511796 515767 := bstep (se 1 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 515767 = 773651) B773651
theorem B515787 : Blo 511796 515787 := bstep (se 1 (by rfl) ⟨386840, by rfl⟩ : syracuseStep 515787 = 773681) B773681
theorem B8314609 : Blo 511796 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B1171223 : Blo 511796 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B1466201 : Blo 511796 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B1302551 : Blo 511796 1302551 := bstep (se 1 (by rfl) ⟨976913, by rfl⟩ : syracuseStep 1302551 = 1953827) B1953827
theorem B2187395 : Blo 511796 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B1958033 : Blo 511796 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B975091 : Blo 511796 975091 := bstep (se 1 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 975091 = 1462637) B1462637
theorem B8348021 : Blo 511796 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B876953 : Blo 511796 876953 := bstep (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) B657715
theorem B1728971 : Blo 511796 1728971 := bstep (se 1 (by rfl) ⟨1296728, by rfl⟩ : syracuseStep 1728971 = 2593457) B2593457
theorem B647767 : Blo 511796 647767 := bstep (se 1 (by rfl) ⟨485825, by rfl⟩ : syracuseStep 647767 = 971651) B971651
theorem B975539 : Blo 511796 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B1729241 : Blo 511796 1729241 := bstep (se 2 (by rfl) ⟨648465, by rfl⟩ : syracuseStep 1729241 = 1296931) B1296931
theorem B975577 : Blo 511796 975577 := bstep (se 2 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 975577 = 731683) B731683
theorem B5563181 : Blo 511796 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B1303361 : Blo 511796 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B1762199 : Blo 511796 1762199 := bstep (se 1 (by rfl) ⟨1321649, by rfl⟩ : syracuseStep 1762199 = 2643299) B2643299
theorem B1467467 : Blo 511796 1467467 := bstep (se 1 (by rfl) ⟨1100600, by rfl⟩ : syracuseStep 1467467 = 2201201) B2201201
theorem B5563523 : Blo 511796 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B550027 : Blo 511796 550027 := bstep (se 1 (by rfl) ⟨412520, by rfl⟩ : syracuseStep 550027 = 825041) B825041
theorem B976025 : Blo 511796 976025 := bstep (se 2 (by rfl) ⟨366009, by rfl⟩ : syracuseStep 976025 = 732019) B732019
theorem B615767 : Blo 511796 615767 := bstep (se 1 (by rfl) ⟨461825, by rfl⟩ : syracuseStep 615767 = 923651) B923651
theorem B1303897 : Blo 511796 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B648587 : Blo 511796 648587 := bstep (se 1 (by rfl) ⟨486440, by rfl⟩ : syracuseStep 648587 = 972881) B972881
theorem B1729943 : Blo 511796 1729943 := bstep (se 1 (by rfl) ⟨1297457, by rfl⟩ : syracuseStep 1729943 = 2594915) B2594915
theorem B6579863 : Blo 511796 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B976769 : Blo 511796 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B1730483 : Blo 511796 1730483 := bstep (se 1 (by rfl) ⟨1297862, by rfl⟩ : syracuseStep 1730483 = 2595725) B2595725
theorem B616459 : Blo 511796 616459 := bstep (se 1 (by rfl) ⟨462344, by rfl⟩ : syracuseStep 616459 = 924689) B924689
theorem B649291 : Blo 511796 649291 := bstep (se 1 (by rfl) ⟨486968, by rfl⟩ : syracuseStep 649291 = 973937) B973937
theorem B2779267 : Blo 511796 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B977035 : Blo 511796 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B1730753 : Blo 511796 1730753 := bstep (se 2 (by rfl) ⟨649032, by rfl⟩ : syracuseStep 1730753 = 1298065) B1298065
theorem B649559 : Blo 511796 649559 := bstep (se 1 (by rfl) ⟨487169, by rfl⟩ : syracuseStep 649559 = 974339) B974339
theorem B3303773 : Blo 511796 3303773 := bstep (se 3 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 3303773 = 1238915) B1238915
theorem B5859701 : Blo 511796 5859701 := bstep (se 5 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 5859701 = 549347) B549347
theorem B4155779 : Blo 511796 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B1305011 : Blo 511796 1305011 := bstep (se 1 (by rfl) ⟨978758, by rfl⟩ : syracuseStep 1305011 = 1957517) B1957517
theorem B977483 : Blo 511796 977483 := bstep (se 1 (by rfl) ⟨733112, by rfl⟩ : syracuseStep 977483 = 1466225) B1466225
theorem B1305305 : Blo 511796 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B1731293 : Blo 511796 1731293 := bstep (se 3 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 1731293 = 649235) B649235
theorem B977665 : Blo 511796 977665 := bstep (se 2 (by rfl) ⟨366624, by rfl⟩ : syracuseStep 977665 = 733249) B733249
theorem B3697483 : Blo 511796 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1764275 : Blo 511796 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B650263 : Blo 511796 650263 := bstep (se 1 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 650263 = 975395) B975395
theorem B3894317 : Blo 511796 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B978007 : Blo 511796 978007 := bstep (se 1 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 978007 = 1467011) B1467011
theorem B519319 : Blo 511796 519319 := bstep (se 1 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 519319 = 778979) B778979
theorem B978227 : Blo 511796 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B978455 : Blo 511796 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B781849 : Blo 511796 781849 := bstep (se 2 (by rfl) ⟨293193, by rfl⟩ : syracuseStep 781849 = 586387) B586387
theorem B978713 : Blo 511796 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B1732427 : Blo 511796 1732427 := bstep (se 1 (by rfl) ⟨1299320, by rfl⟩ : syracuseStep 1732427 = 2598641) B2598641
theorem B6352757 : Blo 511796 6352757 := bstep (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) B595571
theorem B1044427 : Blo 511796 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B782347 : Blo 511796 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B1732697 : Blo 511796 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B2191511 : Blo 511796 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B3698867 : Blo 511796 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B979123 : Blo 511796 979123 := bstep (se 1 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 979123 = 1468685) B1468685
theorem B2191819 : Blo 511796 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B1045043 : Blo 511796 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B13529693 : Blo 511796 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B651979 : Blo 511796 651979 := bstep (se 1 (by rfl) ⟨488984, by rfl⟩ : syracuseStep 651979 = 977969) B977969
theorem B2192093 : Blo 511796 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B1733399 : Blo 511796 1733399 := bstep (se 1 (by rfl) ⟨1300049, by rfl⟩ : syracuseStep 1733399 = 2600099) B2600099
theorem B521111 : Blo 511796 521111 := bstep (se 1 (by rfl) ⟨390833, by rfl⟩ : syracuseStep 521111 = 781667) B781667
theorem B1733939 : Blo 511796 1733939 := bstep (se 1 (by rfl) ⟨1300454, by rfl⟩ : syracuseStep 1733939 = 2600909) B2600909
theorem B521687 : Blo 511796 521687 := bstep (se 1 (by rfl) ⟨391265, by rfl⟩ : syracuseStep 521687 = 782531) B782531
theorem B1734209 : Blo 511796 1734209 := bstep (se 2 (by rfl) ⟨650328, by rfl⟩ : syracuseStep 1734209 = 1300657) B1300657
theorem B35682227 : Blo 511796 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B2193425 : Blo 511796 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B1734749 : Blo 511796 1734749 := bstep (se 3 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 1734749 = 650531) B650531
theorem B3898205 : Blo 511796 3898205 := bstep (se 3 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 3898205 = 1461827) B1461827
theorem B1735883 : Blo 511796 1735883 := bstep (se 1 (by rfl) ⟨1301912, by rfl⟩ : syracuseStep 1735883 = 2603825) B2603825
theorem B1736153 : Blo 511796 1736153 := bstep (se 2 (by rfl) ⟨651057, by rfl⟩ : syracuseStep 1736153 = 1302115) B1302115
theorem B4947587 : Blo 511796 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B2916161 : Blo 511796 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B3112921 : Blo 511796 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1736747 : Blo 511796 1736747 := bstep (se 1 (by rfl) ⟨1302560, by rfl⟩ : syracuseStep 1736747 = 2605121) B2605121
theorem B5865533 : Blo 511796 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B2917093 : Blo 511796 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B1738043 : Blo 511796 1738043 := bstep (se 1 (by rfl) ⟨1303532, by rfl⟩ : syracuseStep 1738043 = 2607065) B2607065
theorem B36079181 : Blo 511796 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B3901121 : Blo 511796 3901121 := bstep (se 2 (by rfl) ⟨1462920, by rfl⟩ : syracuseStep 3901121 = 2925841) B2925841
theorem B1738529 : Blo 511796 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B13338443 : Blo 511796 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B2591027 : Blo 511796 2591027 := bstep (se 1 (by rfl) ⟨1943270, by rfl⟩ : syracuseStep 2591027 = 3886541) B3886541
theorem B1739123 : Blo 511796 1739123 := bstep (se 1 (by rfl) ⟨1304342, by rfl⟩ : syracuseStep 1739123 = 2608685) B2608685
theorem B19761731 : Blo 511796 19761731 := bstep (se 1 (by rfl) ⟨14821298, by rfl⟩ : syracuseStep 19761731 = 29642597) B29642597
theorem B2591351 : Blo 511796 2591351 := bstep (se 1 (by rfl) ⟨1943513, by rfl⟩ : syracuseStep 2591351 = 3887027) B3887027
theorem B821945 : Blo 511796 821945 := bstep (se 2 (by rfl) ⟨308229, by rfl⟩ : syracuseStep 821945 = 616459) B616459
theorem B1641161 : Blo 511796 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B3705689 : Blo 511796 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B12881029 : Blo 511796 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B4951277 : Blo 511796 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B2919827 : Blo 511796 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B4951505 : Blo 511796 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B1642045 : Blo 511796 1642045 := bstep (se 3 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 1642045 = 615767) B615767
theorem B2592323 : Blo 511796 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B4394573 : Blo 511796 4394573 := bstep (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) B1647965
theorem B1412743 : Blo 511796 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B2461529 : Blo 511796 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B2592647 : Blo 511796 2592647 := bstep (se 1 (by rfl) ⟨1944485, by rfl⟩ : syracuseStep 2592647 = 3888971) B3888971
theorem B823355 : Blo 511796 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B2920535 : Blo 511796 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B692425 : Blo 511796 692425 := bstep (se 2 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 692425 = 519319) B519319
theorem B4395323 : Blo 511796 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B528911 : Blo 511796 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B1249939 : Blo 511796 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B627599 : Blo 511796 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B1151891 : Blo 511796 1151891 := bstep (se 1 (by rfl) ⟨863918, by rfl⟩ : syracuseStep 1151891 = 1727837) B1727837
theorem B1151945 : Blo 511796 1151945 := bstep (se 2 (by rfl) ⟨431979, by rfl⟩ : syracuseStep 1151945 = 863959) B863959
theorem B2462723 : Blo 511796 2462723 := bstep (se 1 (by rfl) ⟨1847042, by rfl⟩ : syracuseStep 2462723 = 3694085) B3694085
theorem B3904523 : Blo 511796 3904523 := bstep (se 1 (by rfl) ⟨2928392, by rfl⟩ : syracuseStep 3904523 = 5856785) B5856785
theorem B1611037 : Blo 511796 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B3282551 : Blo 511796 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B1152647 : Blo 511796 1152647 := bstep (se 1 (by rfl) ⟨864485, by rfl⟩ : syracuseStep 1152647 = 1728971) B1728971
theorem B22484789 : Blo 511796 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1152827 : Blo 511796 1152827 := bstep (se 1 (by rfl) ⟨864620, by rfl⟩ : syracuseStep 1152827 = 1729241) B1729241
theorem B3708787 : Blo 511796 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B4396963 : Blo 511796 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B1152953 : Blo 511796 1152953 := bstep (se 2 (by rfl) ⟨432357, by rfl⟩ : syracuseStep 1152953 = 864715) B864715
theorem B2922425 : Blo 511796 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B1153295 : Blo 511796 1153295 := bstep (se 1 (by rfl) ⟨864971, by rfl⟩ : syracuseStep 1153295 = 1729943) B1729943
theorem B7411985 : Blo 511796 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B1153313 : Blo 511796 1153313 := bstep (se 2 (by rfl) ⟨432492, by rfl⟩ : syracuseStep 1153313 = 864985) B864985
theorem B1317235 : Blo 511796 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B5839289 : Blo 511796 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B2202173 : Blo 511796 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1153655 : Blo 511796 1153655 := bstep (se 1 (by rfl) ⟨865241, by rfl⟩ : syracuseStep 1153655 = 1730483) B1730483
theorem B1153835 : Blo 511796 1153835 := bstep (se 1 (by rfl) ⟨865376, by rfl⟩ : syracuseStep 1153835 = 1730753) B1730753
theorem B2202515 : Blo 511796 2202515 := bstep (se 1 (by rfl) ⟨1651886, by rfl⟩ : syracuseStep 2202515 = 3303773) B3303773
theorem B3906467 : Blo 511796 3906467 := bstep (se 1 (by rfl) ⟨2929850, by rfl⟩ : syracuseStep 3906467 = 5859701) B5859701
theorem B1154195 : Blo 511796 1154195 := bstep (se 1 (by rfl) ⟨865646, by rfl⟩ : syracuseStep 1154195 = 1731293) B1731293
theorem B1154249 : Blo 511796 1154249 := bstep (se 2 (by rfl) ⟨432843, by rfl⟩ : syracuseStep 1154249 = 865687) B865687
theorem B2596211 : Blo 511796 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1646351 : Blo 511796 1646351 := bstep (se 1 (by rfl) ⟨1234763, by rfl⟩ : syracuseStep 1646351 = 2469527) B2469527
theorem B728875 : Blo 511796 728875 := bstep (se 1 (by rfl) ⟨546656, by rfl⟩ : syracuseStep 728875 = 1093313) B1093313
theorem B2596697 : Blo 511796 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B1154951 : Blo 511796 1154951 := bstep (se 1 (by rfl) ⟨866213, by rfl⟩ : syracuseStep 1154951 = 1732427) B1732427
theorem B4235171 : Blo 511796 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B729103 : Blo 511796 729103 := bstep (se 1 (by rfl) ⟨546827, by rfl⟩ : syracuseStep 729103 = 1093655) B1093655
theorem B1155131 : Blo 511796 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B2465911 : Blo 511796 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B1155257 : Blo 511796 1155257 := bstep (se 2 (by rfl) ⟨433221, by rfl⟩ : syracuseStep 1155257 = 866443) B866443
theorem B696695 : Blo 511796 696695 := bstep (se 1 (by rfl) ⟨522521, by rfl⟩ : syracuseStep 696695 = 1045043) B1045043
theorem B1155599 : Blo 511796 1155599 := bstep (se 1 (by rfl) ⟨866699, by rfl⟩ : syracuseStep 1155599 = 1733399) B1733399
theorem B1155617 : Blo 511796 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B1155959 : Blo 511796 1155959 := bstep (se 1 (by rfl) ⟨866969, by rfl⟩ : syracuseStep 1155959 = 1733939) B1733939
theorem B1156139 : Blo 511796 1156139 := bstep (se 1 (by rfl) ⟨867104, by rfl⟩ : syracuseStep 1156139 = 1734209) B1734209
theorem B3908897 : Blo 511796 3908897 := bstep (se 2 (by rfl) ⟨1465836, by rfl⟩ : syracuseStep 3908897 = 2931673) B2931673
theorem B1156499 : Blo 511796 1156499 := bstep (se 1 (by rfl) ⟨867374, by rfl⟩ : syracuseStep 1156499 = 1734749) B1734749
theorem B1156553 : Blo 511796 1156553 := bstep (se 2 (by rfl) ⟨433707, by rfl⟩ : syracuseStep 1156553 = 867415) B867415
theorem B1844765 : Blo 511796 1844765 := bstep (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) B691787
theorem B2467529 : Blo 511796 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B2598803 : Blo 511796 2598803 := bstep (se 1 (by rfl) ⟨1949102, by rfl⟩ : syracuseStep 2598803 = 3898205) B3898205
theorem B16623629 : Blo 511796 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B1157255 : Blo 511796 1157255 := bstep (se 1 (by rfl) ⟨867941, by rfl⟩ : syracuseStep 1157255 = 1735883) B1735883
theorem B3909869 : Blo 511796 3909869 := bstep (se 3 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 3909869 = 1466201) B1466201
theorem B1157435 : Blo 511796 1157435 := bstep (se 1 (by rfl) ⟨868076, by rfl⟩ : syracuseStep 1157435 = 1736153) B1736153
theorem B11086145 : Blo 511796 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B1157561 : Blo 511796 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B6597085 : Blo 511796 6597085 := bstep (se 3 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 6597085 = 2473907) B2473907
theorem B1944107 : Blo 511796 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B731791 : Blo 511796 731791 := bstep (se 1 (by rfl) ⟨548843, by rfl⟩ : syracuseStep 731791 = 1097687) B1097687
theorem B731911 : Blo 511796 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B1157903 : Blo 511796 1157903 := bstep (se 1 (by rfl) ⟨868427, by rfl⟩ : syracuseStep 1157903 = 1736855) B1736855
theorem B1157921 : Blo 511796 1157921 := bstep (se 2 (by rfl) ⟨434220, by rfl⟩ : syracuseStep 1157921 = 868441) B868441
theorem B1158263 : Blo 511796 1158263 := bstep (se 1 (by rfl) ⟨868697, by rfl⟩ : syracuseStep 1158263 = 1737395) B1737395
theorem B1158443 : Blo 511796 1158443 := bstep (se 1 (by rfl) ⟨868832, by rfl⟩ : syracuseStep 1158443 = 1737665) B1737665
theorem B863689 : Blo 511796 863689 := bstep (se 2 (by rfl) ⟨323883, by rfl⟩ : syracuseStep 863689 = 647767) B647767
theorem B2666027 : Blo 511796 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B1158803 : Blo 511796 1158803 := bstep (se 1 (by rfl) ⟨869102, by rfl⟩ : syracuseStep 1158803 = 1738205) B1738205
theorem B1158857 : Blo 511796 1158857 := bstep (se 2 (by rfl) ⟨434571, by rfl⟩ : syracuseStep 1158857 = 869143) B869143
theorem B3550949 : Blo 511796 3550949 := bstep (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) B665803
theorem B2338541 : Blo 511796 2338541 := bstep (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) B876953
theorem B3288883 : Blo 511796 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B1322839 : Blo 511796 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B2076625 : Blo 511796 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B12496913 : Blo 511796 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B3911813 : Blo 511796 3911813 := bstep (se 4 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 3911813 = 733465) B733465
theorem B864391 : Blo 511796 864391 := bstep (se 1 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 864391 = 1296587) B1296587
theorem B733369 : Blo 511796 733369 := bstep (se 2 (by rfl) ⟨275013, by rfl⟩ : syracuseStep 733369 = 550027) B550027
theorem B2929031 : Blo 511796 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B1159559 : Blo 511796 1159559 := bstep (se 1 (by rfl) ⟨869669, by rfl⟩ : syracuseStep 1159559 = 1739339) B1739339
theorem B1946065 : Blo 511796 1946065 := bstep (se 2 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 1946065 = 1459549) B1459549
theorem B1847819 : Blo 511796 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B1159739 : Blo 511796 1159739 := bstep (se 1 (by rfl) ⟨869804, by rfl⟩ : syracuseStep 1159739 = 1739609) B1739609
theorem B1159865 : Blo 511796 1159865 := bstep (se 2 (by rfl) ⟨434949, by rfl⟩ : syracuseStep 1159865 = 869899) B869899
theorem B1946369 : Blo 511796 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B865039 : Blo 511796 865039 := bstep (se 1 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 865039 = 1297559) B1297559
theorem B2601881 : Blo 511796 2601881 := bstep (se 2 (by rfl) ⟨975705, by rfl⟩ : syracuseStep 2601881 = 1951411) B1951411
theorem B9876491 : Blo 511796 9876491 := bstep (se 1 (by rfl) ⟨7407368, by rfl⟩ : syracuseStep 9876491 = 14814737) B14814737
theorem B1160207 : Blo 511796 1160207 := bstep (se 1 (by rfl) ⟨870155, by rfl⟩ : syracuseStep 1160207 = 1740311) B1740311
theorem B1160225 : Blo 511796 1160225 := bstep (se 2 (by rfl) ⟨435084, by rfl⟩ : syracuseStep 1160225 = 870169) B870169
theorem B1389629 : Blo 511796 1389629 := bstep (se 3 (by rfl) ⟨260555, by rfl⟩ : syracuseStep 1389629 = 521111) B521111
theorem B1094791 : Blo 511796 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B1946825 : Blo 511796 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B865579 : Blo 511796 865579 := bstep (se 1 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 865579 = 1298369) B1298369
theorem B2471219 : Blo 511796 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B865721 : Blo 511796 865721 := bstep (se 2 (by rfl) ⟨324645, by rfl⟩ : syracuseStep 865721 = 649291) B649291
theorem B2471447 : Blo 511796 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B767735 : Blo 511796 767735 := bstep (se 1 (by rfl) ⟨575801, by rfl⟩ : syracuseStep 767735 = 1151603) B1151603
theorem B767759 : Blo 511796 767759 := bstep (se 1 (by rfl) ⟨575819, by rfl⟩ : syracuseStep 767759 = 1151639) B1151639
theorem B767801 : Blo 511796 767801 := bstep (se 2 (by rfl) ⟨287925, by rfl⟩ : syracuseStep 767801 = 575851) B575851
theorem B1488701 : Blo 511796 1488701 := bstep (se 3 (by rfl) ⟨279131, by rfl⟩ : syracuseStep 1488701 = 558263) B558263
theorem B767879 : Blo 511796 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B767915 : Blo 511796 767915 := bstep (se 1 (by rfl) ⟨575936, by rfl⟩ : syracuseStep 767915 = 1151873) B1151873
theorem B767945 : Blo 511796 767945 := bstep (se 2 (by rfl) ⟨287979, by rfl⟩ : syracuseStep 767945 = 575959) B575959
theorem B768059 : Blo 511796 768059 := bstep (se 1 (by rfl) ⟨576044, by rfl⟩ : syracuseStep 768059 = 1152089) B1152089
theorem B768119 : Blo 511796 768119 := bstep (se 1 (by rfl) ⟨576089, by rfl⟩ : syracuseStep 768119 = 1152179) B1152179
theorem B866423 : Blo 511796 866423 := bstep (se 1 (by rfl) ⟨649817, by rfl⟩ : syracuseStep 866423 = 1299635) B1299635
theorem B768143 : Blo 511796 768143 := bstep (se 1 (by rfl) ⟨576107, by rfl⟩ : syracuseStep 768143 = 1152215) B1152215
theorem B768185 : Blo 511796 768185 := bstep (se 2 (by rfl) ⟨288069, by rfl⟩ : syracuseStep 768185 = 576139) B576139
theorem B768263 : Blo 511796 768263 := bstep (se 1 (by rfl) ⟨576197, by rfl⟩ : syracuseStep 768263 = 1152395) B1152395
theorem B768299 : Blo 511796 768299 := bstep (se 1 (by rfl) ⟨576224, by rfl⟩ : syracuseStep 768299 = 1152449) B1152449
theorem B768329 : Blo 511796 768329 := bstep (se 2 (by rfl) ⟨288123, by rfl⟩ : syracuseStep 768329 = 576247) B576247
theorem B4929977 : Blo 511796 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B768443 : Blo 511796 768443 := bstep (se 1 (by rfl) ⟨576332, by rfl⟩ : syracuseStep 768443 = 1152665) B1152665
theorem B768503 : Blo 511796 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B3914243 : Blo 511796 3914243 := bstep (se 1 (by rfl) ⟨2935682, by rfl⟩ : syracuseStep 3914243 = 5871365) B5871365
theorem B768527 : Blo 511796 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B3291677 : Blo 511796 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B768569 : Blo 511796 768569 := bstep (se 2 (by rfl) ⟨288213, by rfl⟩ : syracuseStep 768569 = 576427) B576427
theorem B866875 : Blo 511796 866875 := bstep (se 1 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 866875 = 1300313) B1300313
theorem B1391165 : Blo 511796 1391165 := bstep (se 3 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 1391165 = 521687) B521687
theorem B768647 : Blo 511796 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B768683 : Blo 511796 768683 := bstep (se 1 (by rfl) ⟨576512, by rfl⟩ : syracuseStep 768683 = 1153025) B1153025
theorem B768713 : Blo 511796 768713 := bstep (se 2 (by rfl) ⟨288267, by rfl⟩ : syracuseStep 768713 = 576535) B576535
theorem B867017 : Blo 511796 867017 := bstep (se 2 (by rfl) ⟨325131, by rfl⟩ : syracuseStep 867017 = 650263) B650263
theorem B768827 : Blo 511796 768827 := bstep (se 1 (by rfl) ⟨576620, by rfl⟩ : syracuseStep 768827 = 1153241) B1153241
theorem B1096507 : Blo 511796 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B768887 : Blo 511796 768887 := bstep (se 1 (by rfl) ⟨576665, by rfl⟩ : syracuseStep 768887 = 1153331) B1153331
theorem B768911 : Blo 511796 768911 := bstep (se 1 (by rfl) ⟨576683, by rfl⟩ : syracuseStep 768911 = 1153367) B1153367
theorem B768953 : Blo 511796 768953 := bstep (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) B576715
theorem B769031 : Blo 511796 769031 := bstep (se 1 (by rfl) ⟨576773, by rfl⟩ : syracuseStep 769031 = 1153547) B1153547
theorem B769067 : Blo 511796 769067 := bstep (se 1 (by rfl) ⟨576800, by rfl⟩ : syracuseStep 769067 = 1153601) B1153601
theorem B8928317 : Blo 511796 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B769097 : Blo 511796 769097 := bstep (se 2 (by rfl) ⟨288411, by rfl⟩ : syracuseStep 769097 = 576823) B576823
theorem B769211 : Blo 511796 769211 := bstep (se 1 (by rfl) ⟨576908, by rfl⟩ : syracuseStep 769211 = 1153817) B1153817
theorem B769271 : Blo 511796 769271 := bstep (se 1 (by rfl) ⟨576953, by rfl⟩ : syracuseStep 769271 = 1153907) B1153907
theorem B2473217 : Blo 511796 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B769295 : Blo 511796 769295 := bstep (se 1 (by rfl) ⟨576971, by rfl⟩ : syracuseStep 769295 = 1153943) B1153943
theorem B1097003 : Blo 511796 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B769337 : Blo 511796 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B1752455 : Blo 511796 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B769415 : Blo 511796 769415 := bstep (se 1 (by rfl) ⟨577061, by rfl⟩ : syracuseStep 769415 = 1154123) B1154123
theorem B867719 : Blo 511796 867719 := bstep (se 1 (by rfl) ⟨650789, by rfl⟩ : syracuseStep 867719 = 1301579) B1301579
theorem B769451 : Blo 511796 769451 := bstep (se 1 (by rfl) ⟨577088, by rfl⟩ : syracuseStep 769451 = 1154177) B1154177
theorem B2604473 : Blo 511796 2604473 := bstep (se 2 (by rfl) ⟨976677, by rfl⟩ : syracuseStep 2604473 = 1953355) B1953355
theorem B769481 : Blo 511796 769481 := bstep (se 2 (by rfl) ⟨288555, by rfl⟩ : syracuseStep 769481 = 577111) B577111
theorem B769595 : Blo 511796 769595 := bstep (se 1 (by rfl) ⟨577196, by rfl⟩ : syracuseStep 769595 = 1154393) B1154393
theorem B769655 : Blo 511796 769655 := bstep (se 1 (by rfl) ⟨577241, by rfl⟩ : syracuseStep 769655 = 1154483) B1154483
theorem B769679 : Blo 511796 769679 := bstep (se 1 (by rfl) ⟨577259, by rfl⟩ : syracuseStep 769679 = 1154519) B1154519
theorem B6602417 : Blo 511796 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B769721 : Blo 511796 769721 := bstep (se 2 (by rfl) ⟨288645, by rfl⟩ : syracuseStep 769721 = 577291) B577291
theorem B769799 : Blo 511796 769799 := bstep (se 1 (by rfl) ⟨577349, by rfl⟩ : syracuseStep 769799 = 1154699) B1154699
theorem B769835 : Blo 511796 769835 := bstep (se 1 (by rfl) ⟨577376, by rfl⟩ : syracuseStep 769835 = 1154753) B1154753
theorem B769865 : Blo 511796 769865 := bstep (se 2 (by rfl) ⟨288699, by rfl⟩ : syracuseStep 769865 = 577399) B577399
theorem B1392569 : Blo 511796 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B769979 : Blo 511796 769979 := bstep (se 1 (by rfl) ⟨577484, by rfl⟩ : syracuseStep 769979 = 1154969) B1154969
theorem B770039 : Blo 511796 770039 := bstep (se 1 (by rfl) ⟨577529, by rfl⟩ : syracuseStep 770039 = 1155059) B1155059
theorem B770063 : Blo 511796 770063 := bstep (se 1 (by rfl) ⟨577547, by rfl⟩ : syracuseStep 770063 = 1155095) B1155095
theorem B868367 : Blo 511796 868367 := bstep (se 1 (by rfl) ⟨651275, by rfl⟩ : syracuseStep 868367 = 1302551) B1302551
theorem B770105 : Blo 511796 770105 := bstep (se 2 (by rfl) ⟨288789, by rfl⟩ : syracuseStep 770105 = 577579) B577579
theorem B1458263 : Blo 511796 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B770183 : Blo 511796 770183 := bstep (se 1 (by rfl) ⟨577637, by rfl⟩ : syracuseStep 770183 = 1155275) B1155275
theorem B770219 : Blo 511796 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B770249 : Blo 511796 770249 := bstep (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) B577687
theorem B1949953 : Blo 511796 1949953 := bstep (se 2 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 1949953 = 1462465) B1462465
theorem B770363 : Blo 511796 770363 := bstep (se 1 (by rfl) ⟨577772, by rfl⟩ : syracuseStep 770363 = 1155545) B1155545
theorem B770423 : Blo 511796 770423 := bstep (se 1 (by rfl) ⟨577817, by rfl⟩ : syracuseStep 770423 = 1155635) B1155635
theorem B770447 : Blo 511796 770447 := bstep (se 1 (by rfl) ⟨577835, by rfl⟩ : syracuseStep 770447 = 1155671) B1155671
theorem B770489 : Blo 511796 770489 := bstep (se 2 (by rfl) ⟨288933, by rfl⟩ : syracuseStep 770489 = 577867) B577867
theorem B770567 : Blo 511796 770567 := bstep (se 1 (by rfl) ⟨577925, by rfl⟩ : syracuseStep 770567 = 1155851) B1155851
theorem B770603 : Blo 511796 770603 := bstep (se 1 (by rfl) ⟨577952, by rfl⟩ : syracuseStep 770603 = 1155905) B1155905
theorem B868907 : Blo 511796 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B770633 : Blo 511796 770633 := bstep (se 2 (by rfl) ⟨288987, by rfl⟩ : syracuseStep 770633 = 577975) B577975
theorem B770747 : Blo 511796 770747 := bstep (se 1 (by rfl) ⟨578060, by rfl⟩ : syracuseStep 770747 = 1156121) B1156121
theorem B2605769 : Blo 511796 2605769 := bstep (se 2 (by rfl) ⟨977163, by rfl⟩ : syracuseStep 2605769 = 1954327) B1954327
theorem B770807 : Blo 511796 770807 := bstep (se 1 (by rfl) ⟨578105, by rfl⟩ : syracuseStep 770807 = 1156211) B1156211
theorem B770831 : Blo 511796 770831 := bstep (se 1 (by rfl) ⟨578123, by rfl⟩ : syracuseStep 770831 = 1156247) B1156247
theorem B770873 : Blo 511796 770873 := bstep (se 2 (by rfl) ⟨289077, by rfl⟩ : syracuseStep 770873 = 578155) B578155
theorem B6570841 : Blo 511796 6570841 := bstep (se 2 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 6570841 = 4928131) B4928131
theorem B770951 : Blo 511796 770951 := bstep (se 1 (by rfl) ⟨578213, by rfl⟩ : syracuseStep 770951 = 1156427) B1156427
theorem B2933657 : Blo 511796 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B770987 : Blo 511796 770987 := bstep (se 1 (by rfl) ⟨578240, by rfl⟩ : syracuseStep 770987 = 1156481) B1156481
theorem B869305 : Blo 511796 869305 := bstep (se 2 (by rfl) ⟨325989, by rfl⟩ : syracuseStep 869305 = 651979) B651979
theorem B771017 : Blo 511796 771017 := bstep (se 2 (by rfl) ⟨289131, by rfl⟩ : syracuseStep 771017 = 578263) B578263
theorem B771131 : Blo 511796 771131 := bstep (se 1 (by rfl) ⟨578348, by rfl⟩ : syracuseStep 771131 = 1156697) B1156697
theorem B771191 : Blo 511796 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B771215 : Blo 511796 771215 := bstep (se 1 (by rfl) ⟨578411, by rfl⟩ : syracuseStep 771215 = 1156823) B1156823
theorem B771257 : Blo 511796 771257 := bstep (se 2 (by rfl) ⟨289221, by rfl⟩ : syracuseStep 771257 = 578443) B578443
theorem B771335 : Blo 511796 771335 := bstep (se 1 (by rfl) ⟨578501, by rfl⟩ : syracuseStep 771335 = 1157003) B1157003
theorem B771371 : Blo 511796 771371 := bstep (se 1 (by rfl) ⟨578528, by rfl⟩ : syracuseStep 771371 = 1157057) B1157057
theorem B771401 : Blo 511796 771401 := bstep (se 2 (by rfl) ⟨289275, by rfl⟩ : syracuseStep 771401 = 578551) B578551
theorem B1230265 : Blo 511796 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B771515 : Blo 511796 771515 := bstep (se 1 (by rfl) ⟨578636, by rfl⟩ : syracuseStep 771515 = 1157273) B1157273
theorem B771575 : Blo 511796 771575 := bstep (se 1 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 771575 = 1157363) B1157363
theorem B771599 : Blo 511796 771599 := bstep (se 1 (by rfl) ⟨578699, by rfl⟩ : syracuseStep 771599 = 1157399) B1157399
theorem B771641 : Blo 511796 771641 := bstep (se 2 (by rfl) ⟨289365, by rfl⟩ : syracuseStep 771641 = 578731) B578731
theorem B1295959 : Blo 511796 1295959 := bstep (se 1 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 1295959 = 1943939) B1943939
theorem B2770519 : Blo 511796 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B870007 : Blo 511796 870007 := bstep (se 1 (by rfl) ⟨652505, by rfl⟩ : syracuseStep 870007 = 1305011) B1305011
theorem B771719 : Blo 511796 771719 := bstep (se 1 (by rfl) ⟨578789, by rfl⟩ : syracuseStep 771719 = 1157579) B1157579
theorem B771755 : Blo 511796 771755 := bstep (se 1 (by rfl) ⟨578816, by rfl⟩ : syracuseStep 771755 = 1157633) B1157633
theorem B771785 : Blo 511796 771785 := bstep (se 2 (by rfl) ⟨289419, by rfl⟩ : syracuseStep 771785 = 578839) B578839
theorem B5916377 : Blo 511796 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B771899 : Blo 511796 771899 := bstep (se 1 (by rfl) ⟨578924, by rfl⟩ : syracuseStep 771899 = 1157849) B1157849
theorem B870203 : Blo 511796 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B771959 : Blo 511796 771959 := bstep (se 1 (by rfl) ⟨578969, by rfl⟩ : syracuseStep 771959 = 1157939) B1157939
theorem B1296263 : Blo 511796 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B1230727 : Blo 511796 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B771983 : Blo 511796 771983 := bstep (se 1 (by rfl) ⟨578987, by rfl⟩ : syracuseStep 771983 = 1157975) B1157975
theorem B772025 : Blo 511796 772025 := bstep (se 2 (by rfl) ⟨289509, by rfl⟩ : syracuseStep 772025 = 579019) B579019
theorem B772103 : Blo 511796 772103 := bstep (se 1 (by rfl) ⟨579077, by rfl⟩ : syracuseStep 772103 = 1158155) B1158155
theorem B1296395 : Blo 511796 1296395 := bstep (se 1 (by rfl) ⟨972296, by rfl⟩ : syracuseStep 1296395 = 1944593) B1944593
theorem B2476061 : Blo 511796 2476061 := bstep (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) B928523
theorem B1755179 : Blo 511796 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B772139 : Blo 511796 772139 := bstep (se 1 (by rfl) ⟨579104, by rfl⟩ : syracuseStep 772139 = 1158209) B1158209
theorem B772169 : Blo 511796 772169 := bstep (se 2 (by rfl) ⟨289563, by rfl⟩ : syracuseStep 772169 = 579127) B579127
theorem B772283 : Blo 511796 772283 := bstep (se 1 (by rfl) ⟨579212, by rfl⟩ : syracuseStep 772283 = 1158425) B1158425
theorem B772343 : Blo 511796 772343 := bstep (se 1 (by rfl) ⟨579257, by rfl⟩ : syracuseStep 772343 = 1158515) B1158515
theorem B772367 : Blo 511796 772367 := bstep (se 1 (by rfl) ⟨579275, by rfl⟩ : syracuseStep 772367 = 1158551) B1158551
theorem B772409 : Blo 511796 772409 := bstep (se 2 (by rfl) ⟨289653, by rfl⟩ : syracuseStep 772409 = 579307) B579307
theorem B772487 : Blo 511796 772487 := bstep (se 1 (by rfl) ⟨579365, by rfl⟩ : syracuseStep 772487 = 1158731) B1158731
theorem B575887 : Blo 511796 575887 := bstep (se 1 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 575887 = 863831) B863831
theorem B772523 : Blo 511796 772523 := bstep (se 1 (by rfl) ⟨579392, by rfl⟩ : syracuseStep 772523 = 1158785) B1158785
theorem B3295673 : Blo 511796 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B772553 : Blo 511796 772553 := bstep (se 2 (by rfl) ⟨289707, by rfl⟩ : syracuseStep 772553 = 579415) B579415
theorem B4704733 : Blo 511796 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B1296911 : Blo 511796 1296911 := bstep (se 1 (by rfl) ⟨972683, by rfl⟩ : syracuseStep 1296911 = 1945367) B1945367
theorem B772667 : Blo 511796 772667 := bstep (se 1 (by rfl) ⟨579500, by rfl⟩ : syracuseStep 772667 = 1159001) B1159001
theorem B772727 : Blo 511796 772727 := bstep (se 1 (by rfl) ⟨579545, by rfl⟩ : syracuseStep 772727 = 1159091) B1159091
theorem B772751 : Blo 511796 772751 := bstep (se 1 (by rfl) ⟨579563, by rfl⟩ : syracuseStep 772751 = 1159127) B1159127
theorem B1297043 : Blo 511796 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B772793 : Blo 511796 772793 := bstep (se 2 (by rfl) ⟨289797, by rfl⟩ : syracuseStep 772793 = 579595) B579595
theorem B3001033 : Blo 511796 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B772871 : Blo 511796 772871 := bstep (se 1 (by rfl) ⟨579653, by rfl⟩ : syracuseStep 772871 = 1159307) B1159307
theorem B1461007 : Blo 511796 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B772907 : Blo 511796 772907 := bstep (se 1 (by rfl) ⟨579680, by rfl⟩ : syracuseStep 772907 = 1159361) B1159361
theorem B1461053 : Blo 511796 1461053 := bstep (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) B547895
theorem B772937 : Blo 511796 772937 := bstep (se 2 (by rfl) ⟨289851, by rfl⟩ : syracuseStep 772937 = 579703) B579703
theorem B576391 : Blo 511796 576391 := bstep (se 1 (by rfl) ⟨432293, by rfl⟩ : syracuseStep 576391 = 864587) B864587
theorem B773051 : Blo 511796 773051 := bstep (se 1 (by rfl) ⟨579788, by rfl⟩ : syracuseStep 773051 = 1159577) B1159577
theorem B773111 : Blo 511796 773111 := bstep (se 1 (by rfl) ⟨579833, by rfl⟩ : syracuseStep 773111 = 1159667) B1159667
theorem B773135 : Blo 511796 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B773177 : Blo 511796 773177 := bstep (se 2 (by rfl) ⟨289941, by rfl⟩ : syracuseStep 773177 = 579883) B579883
theorem B576571 : Blo 511796 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B1952855 : Blo 511796 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B3132503 : Blo 511796 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B773255 : Blo 511796 773255 := bstep (se 1 (by rfl) ⟨579941, by rfl⟩ : syracuseStep 773255 = 1159883) B1159883
theorem B1461395 : Blo 511796 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B773291 : Blo 511796 773291 := bstep (se 1 (by rfl) ⟨579968, by rfl⟩ : syracuseStep 773291 = 1159937) B1159937
theorem B773321 : Blo 511796 773321 := bstep (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) B579991
theorem B773435 : Blo 511796 773435 := bstep (se 1 (by rfl) ⟨580076, by rfl⟩ : syracuseStep 773435 = 1160153) B1160153
theorem B773495 : Blo 511796 773495 := bstep (se 1 (by rfl) ⟨580121, by rfl⟩ : syracuseStep 773495 = 1160243) B1160243
theorem B773519 : Blo 511796 773519 := bstep (se 1 (by rfl) ⟨580139, by rfl⟩ : syracuseStep 773519 = 1160279) B1160279
theorem B3689873 : Blo 511796 3689873 := bstep (se 2 (by rfl) ⟨1383702, by rfl⟩ : syracuseStep 3689873 = 2767405) B2767405
theorem B773561 : Blo 511796 773561 := bstep (se 2 (by rfl) ⟨290085, by rfl⟩ : syracuseStep 773561 = 580171) B580171
theorem B773639 : Blo 511796 773639 := bstep (se 1 (by rfl) ⟨580229, by rfl⟩ : syracuseStep 773639 = 1160459) B1160459
theorem B2084363 : Blo 511796 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B577039 : Blo 511796 577039 := bstep (se 1 (by rfl) ⟨432779, by rfl⟩ : syracuseStep 577039 = 865559) B865559
theorem B773675 : Blo 511796 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B1953341 : Blo 511796 1953341 := bstep (se 3 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 1953341 = 732503) B732503
theorem B1298177 : Blo 511796 1298177 := bstep (se 2 (by rfl) ⟨486816, by rfl⟩ : syracuseStep 1298177 = 973633) B973633
theorem B511803 : Blo 511796 511803 := bstep (se 1 (by rfl) ⟨383852, by rfl⟩ : syracuseStep 511803 = 767705) B767705
theorem B511879 : Blo 511796 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B511887 : Blo 511796 511887 := bstep (se 1 (by rfl) ⟨383915, by rfl⟩ : syracuseStep 511887 = 767831) B767831
theorem B511931 : Blo 511796 511931 := bstep (se 1 (by rfl) ⟨383948, by rfl⟩ : syracuseStep 511931 = 767897) B767897
theorem B512007 : Blo 511796 512007 := bstep (se 1 (by rfl) ⟨384005, by rfl⟩ : syracuseStep 512007 = 768011) B768011
theorem B577543 : Blo 511796 577543 := bstep (se 1 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 577543 = 866315) B866315
theorem B1462283 : Blo 511796 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B512015 : Blo 511796 512015 := bstep (se 1 (by rfl) ⟨384011, by rfl⟩ : syracuseStep 512015 = 768023) B768023
theorem B512059 : Blo 511796 512059 := bstep (se 1 (by rfl) ⟨384044, by rfl⟩ : syracuseStep 512059 = 768089) B768089
theorem B1298551 : Blo 511796 1298551 := bstep (se 1 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 1298551 = 1947827) B1947827
theorem B512135 : Blo 511796 512135 := bstep (se 1 (by rfl) ⟨384101, by rfl⟩ : syracuseStep 512135 = 768203) B768203
theorem B512143 : Blo 511796 512143 := bstep (se 1 (by rfl) ⟨384107, by rfl⟩ : syracuseStep 512143 = 768215) B768215
theorem B2937005 : Blo 511796 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B512187 : Blo 511796 512187 := bstep (se 1 (by rfl) ⟨384140, by rfl⟩ : syracuseStep 512187 = 768281) B768281
theorem B577723 : Blo 511796 577723 := bstep (se 1 (by rfl) ⟨433292, by rfl⟩ : syracuseStep 577723 = 866585) B866585
theorem B512263 : Blo 511796 512263 := bstep (se 1 (by rfl) ⟨384197, by rfl⟩ : syracuseStep 512263 = 768395) B768395
theorem B512271 : Blo 511796 512271 := bstep (se 1 (by rfl) ⟨384203, by rfl⟩ : syracuseStep 512271 = 768407) B768407
theorem B512315 : Blo 511796 512315 := bstep (se 1 (by rfl) ⟨384236, by rfl⟩ : syracuseStep 512315 = 768473) B768473
theorem B512391 : Blo 511796 512391 := bstep (se 1 (by rfl) ⟨384293, by rfl⟩ : syracuseStep 512391 = 768587) B768587
theorem B512399 : Blo 511796 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B2478521 : Blo 511796 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B512443 : Blo 511796 512443 := bstep (se 1 (by rfl) ⟨384332, by rfl⟩ : syracuseStep 512443 = 768665) B768665
theorem B4444625 : Blo 511796 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B512519 : Blo 511796 512519 := bstep (se 1 (by rfl) ⟨384389, by rfl⟩ : syracuseStep 512519 = 768779) B768779
theorem B512527 : Blo 511796 512527 := bstep (se 1 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 512527 = 768791) B768791
theorem B1298987 : Blo 511796 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B512571 : Blo 511796 512571 := bstep (se 1 (by rfl) ⟨384428, by rfl⟩ : syracuseStep 512571 = 768857) B768857
theorem B512647 : Blo 511796 512647 := bstep (se 1 (by rfl) ⟨384485, by rfl⟩ : syracuseStep 512647 = 768971) B768971
theorem B512655 : Blo 511796 512655 := bstep (se 1 (by rfl) ⟨384491, by rfl⟩ : syracuseStep 512655 = 768983) B768983
theorem B578191 : Blo 511796 578191 := bstep (se 1 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 578191 = 867287) B867287
theorem B512699 : Blo 511796 512699 := bstep (se 1 (by rfl) ⟨384524, by rfl⟩ : syracuseStep 512699 = 769049) B769049
theorem B512775 : Blo 511796 512775 := bstep (se 1 (by rfl) ⟨384581, by rfl⟩ : syracuseStep 512775 = 769163) B769163
theorem B512783 : Blo 511796 512783 := bstep (se 1 (by rfl) ⟨384587, by rfl⟩ : syracuseStep 512783 = 769175) B769175
theorem B512827 : Blo 511796 512827 := bstep (se 1 (by rfl) ⟨384620, by rfl⟩ : syracuseStep 512827 = 769241) B769241
theorem B512903 : Blo 511796 512903 := bstep (se 1 (by rfl) ⟨384677, by rfl⟩ : syracuseStep 512903 = 769355) B769355
theorem B512911 : Blo 511796 512911 := bstep (se 1 (by rfl) ⟨384683, by rfl⟩ : syracuseStep 512911 = 769367) B769367
theorem B512955 : Blo 511796 512955 := bstep (se 1 (by rfl) ⟨384716, by rfl⟩ : syracuseStep 512955 = 769433) B769433
theorem B513031 : Blo 511796 513031 := bstep (se 1 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 513031 = 769547) B769547
theorem B513039 : Blo 511796 513039 := bstep (se 1 (by rfl) ⟨384779, by rfl⟩ : syracuseStep 513039 = 769559) B769559
theorem B513083 : Blo 511796 513083 := bstep (se 1 (by rfl) ⟨384812, by rfl⟩ : syracuseStep 513083 = 769625) B769625
theorem B7918679 : Blo 511796 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B3298391 : Blo 511796 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B513159 : Blo 511796 513159 := bstep (se 1 (by rfl) ⟨384869, by rfl⟩ : syracuseStep 513159 = 769739) B769739
theorem B578695 : Blo 511796 578695 := bstep (se 1 (by rfl) ⟨434021, by rfl⟩ : syracuseStep 578695 = 868043) B868043
theorem B513167 : Blo 511796 513167 := bstep (se 1 (by rfl) ⟨384875, by rfl⟩ : syracuseStep 513167 = 769751) B769751
theorem B513211 : Blo 511796 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B513287 : Blo 511796 513287 := bstep (se 1 (by rfl) ⟨384965, by rfl⟩ : syracuseStep 513287 = 769931) B769931
theorem B513295 : Blo 511796 513295 := bstep (se 1 (by rfl) ⟨384971, by rfl⟩ : syracuseStep 513295 = 769943) B769943
theorem B1955087 : Blo 511796 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B4150561 : Blo 511796 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B972091 : Blo 511796 972091 := bstep (se 1 (by rfl) ⟨729068, by rfl⟩ : syracuseStep 972091 = 1458137) B1458137
theorem B513339 : Blo 511796 513339 := bstep (se 1 (by rfl) ⟨385004, by rfl⟩ : syracuseStep 513339 = 770009) B770009
theorem B578875 : Blo 511796 578875 := bstep (se 1 (by rfl) ⟨434156, by rfl⟩ : syracuseStep 578875 = 868313) B868313
theorem B1299827 : Blo 511796 1299827 := bstep (se 1 (by rfl) ⟨974870, by rfl⟩ : syracuseStep 1299827 = 1949741) B1949741
theorem B513415 : Blo 511796 513415 := bstep (se 1 (by rfl) ⟨385061, by rfl⟩ : syracuseStep 513415 = 770123) B770123
theorem B1299847 : Blo 511796 1299847 := bstep (se 1 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 1299847 = 1949771) B1949771
theorem B513423 : Blo 511796 513423 := bstep (se 1 (by rfl) ⟨385067, by rfl⟩ : syracuseStep 513423 = 770135) B770135
theorem B5952953 : Blo 511796 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B513467 : Blo 511796 513467 := bstep (se 1 (by rfl) ⟨385100, by rfl⟩ : syracuseStep 513467 = 770201) B770201
theorem B513543 : Blo 511796 513543 := bstep (se 1 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 513543 = 770315) B770315
theorem B513551 : Blo 511796 513551 := bstep (se 1 (by rfl) ⟨385163, by rfl⟩ : syracuseStep 513551 = 770327) B770327
theorem B513595 : Blo 511796 513595 := bstep (se 1 (by rfl) ⟨385196, by rfl⟩ : syracuseStep 513595 = 770393) B770393
theorem B1463923 : Blo 511796 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B2086519 : Blo 511796 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B513671 : Blo 511796 513671 := bstep (se 1 (by rfl) ⟨385253, by rfl⟩ : syracuseStep 513671 = 770507) B770507
theorem B513679 : Blo 511796 513679 := bstep (se 1 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 513679 = 770519) B770519
theorem B1300121 : Blo 511796 1300121 := bstep (se 2 (by rfl) ⟨487545, by rfl⟩ : syracuseStep 1300121 = 975091) B975091
theorem B513723 : Blo 511796 513723 := bstep (se 1 (by rfl) ⟨385292, by rfl⟩ : syracuseStep 513723 = 770585) B770585
theorem B513799 : Blo 511796 513799 := bstep (se 1 (by rfl) ⟨385349, by rfl⟩ : syracuseStep 513799 = 770699) B770699
theorem B513807 : Blo 511796 513807 := bstep (se 1 (by rfl) ⟨385355, by rfl⟩ : syracuseStep 513807 = 770711) B770711
theorem B579343 : Blo 511796 579343 := bstep (se 1 (by rfl) ⟨434507, by rfl⟩ : syracuseStep 579343 = 869015) B869015
theorem B972577 : Blo 511796 972577 := bstep (se 2 (by rfl) ⟨364716, by rfl⟩ : syracuseStep 972577 = 729433) B729433
theorem B2774843 : Blo 511796 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B1300283 : Blo 511796 1300283 := bstep (se 1 (by rfl) ⟨975212, by rfl⟩ : syracuseStep 1300283 = 1950425) B1950425
theorem B513851 : Blo 511796 513851 := bstep (se 1 (by rfl) ⟨385388, by rfl⟩ : syracuseStep 513851 = 770777) B770777
theorem B1464151 : Blo 511796 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B1038199 : Blo 511796 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B513927 : Blo 511796 513927 := bstep (se 1 (by rfl) ⟨385445, by rfl⟩ : syracuseStep 513927 = 770891) B770891
theorem B513935 : Blo 511796 513935 := bstep (se 1 (by rfl) ⟨385451, by rfl⟩ : syracuseStep 513935 = 770903) B770903
theorem B513979 : Blo 511796 513979 := bstep (se 1 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 513979 = 770969) B770969
theorem B514055 : Blo 511796 514055 := bstep (se 1 (by rfl) ⟨385541, by rfl⟩ : syracuseStep 514055 = 771083) B771083
theorem B1234955 : Blo 511796 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B1300495 : Blo 511796 1300495 := bstep (se 1 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 1300495 = 1950743) B1950743
theorem B514063 : Blo 511796 514063 := bstep (se 1 (by rfl) ⟨385547, by rfl⟩ : syracuseStep 514063 = 771095) B771095
theorem B6576173 : Blo 511796 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B1038395 : Blo 511796 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B514107 : Blo 511796 514107 := bstep (se 1 (by rfl) ⟨385580, by rfl⟩ : syracuseStep 514107 = 771161) B771161
theorem B514183 : Blo 511796 514183 := bstep (se 1 (by rfl) ⟨385637, by rfl⟩ : syracuseStep 514183 = 771275) B771275
theorem B514191 : Blo 511796 514191 := bstep (se 1 (by rfl) ⟨385643, by rfl⟩ : syracuseStep 514191 = 771287) B771287
theorem B514235 : Blo 511796 514235 := bstep (se 1 (by rfl) ⟨385676, by rfl⟩ : syracuseStep 514235 = 771353) B771353
theorem B514311 : Blo 511796 514311 := bstep (se 1 (by rfl) ⟨385733, by rfl⟩ : syracuseStep 514311 = 771467) B771467
theorem B579847 : Blo 511796 579847 := bstep (se 1 (by rfl) ⟨434885, by rfl⟩ : syracuseStep 579847 = 869771) B869771
theorem B514319 : Blo 511796 514319 := bstep (se 1 (by rfl) ⟨385739, by rfl⟩ : syracuseStep 514319 = 771479) B771479
theorem B1300769 : Blo 511796 1300769 := bstep (se 2 (by rfl) ⟨487788, by rfl⟩ : syracuseStep 1300769 = 975577) B975577
theorem B514363 : Blo 511796 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B514439 : Blo 511796 514439 := bstep (se 1 (by rfl) ⟨385829, by rfl⟩ : syracuseStep 514439 = 771659) B771659
theorem B514447 : Blo 511796 514447 := bstep (se 1 (by rfl) ⟨385835, by rfl⟩ : syracuseStep 514447 = 771671) B771671
theorem B5560721 : Blo 511796 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B514491 : Blo 511796 514491 := bstep (se 1 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 514491 = 771737) B771737
theorem B580027 : Blo 511796 580027 := bstep (se 1 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 580027 = 870041) B870041
theorem B514567 : Blo 511796 514567 := bstep (se 1 (by rfl) ⟨385925, by rfl⟩ : syracuseStep 514567 = 771851) B771851
theorem B514575 : Blo 511796 514575 := bstep (se 1 (by rfl) ⟨385931, by rfl⟩ : syracuseStep 514575 = 771863) B771863
theorem B514619 : Blo 511796 514619 := bstep (se 1 (by rfl) ⟨385964, by rfl⟩ : syracuseStep 514619 = 771929) B771929
theorem B514695 : Blo 511796 514695 := bstep (se 1 (by rfl) ⟨386021, by rfl⟩ : syracuseStep 514695 = 772043) B772043
theorem B514703 : Blo 511796 514703 := bstep (se 1 (by rfl) ⟨386027, by rfl⟩ : syracuseStep 514703 = 772055) B772055
theorem B514747 : Blo 511796 514747 := bstep (se 1 (by rfl) ⟨386060, by rfl⟩ : syracuseStep 514747 = 772121) B772121
theorem B514823 : Blo 511796 514823 := bstep (se 1 (by rfl) ⟨386117, by rfl⟩ : syracuseStep 514823 = 772235) B772235
theorem B514831 : Blo 511796 514831 := bstep (se 1 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 514831 = 772247) B772247
theorem B514875 : Blo 511796 514875 := bstep (se 1 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 514875 = 772313) B772313
theorem B4742003 : Blo 511796 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B514951 : Blo 511796 514951 := bstep (se 1 (by rfl) ⟨386213, by rfl⟩ : syracuseStep 514951 = 772427) B772427
theorem B1956743 : Blo 511796 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B514959 : Blo 511796 514959 := bstep (se 1 (by rfl) ⟨386219, by rfl⟩ : syracuseStep 514959 = 772439) B772439
theorem B515003 : Blo 511796 515003 := bstep (se 1 (by rfl) ⟨386252, by rfl⟩ : syracuseStep 515003 = 772505) B772505
theorem B515079 : Blo 511796 515079 := bstep (se 1 (by rfl) ⟨386309, by rfl⟩ : syracuseStep 515079 = 772619) B772619
theorem B515087 : Blo 511796 515087 := bstep (se 1 (by rfl) ⟨386315, by rfl⟩ : syracuseStep 515087 = 772631) B772631
theorem B973883 : Blo 511796 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B515131 : Blo 511796 515131 := bstep (se 1 (by rfl) ⟨386348, by rfl⟩ : syracuseStep 515131 = 772697) B772697
theorem B515207 : Blo 511796 515207 := bstep (se 1 (by rfl) ⟨386405, by rfl⟩ : syracuseStep 515207 = 772811) B772811
theorem B515215 : Blo 511796 515215 := bstep (se 1 (by rfl) ⟨386411, by rfl⟩ : syracuseStep 515215 = 772823) B772823
theorem B515259 : Blo 511796 515259 := bstep (se 1 (by rfl) ⟨386444, by rfl⟩ : syracuseStep 515259 = 772889) B772889
theorem B515335 : Blo 511796 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B1301771 : Blo 511796 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B515343 : Blo 511796 515343 := bstep (se 1 (by rfl) ⟨386507, by rfl⟩ : syracuseStep 515343 = 773015) B773015
theorem B515387 : Blo 511796 515387 := bstep (se 1 (by rfl) ⟨386540, by rfl⟩ : syracuseStep 515387 = 773081) B773081
theorem B1465735 : Blo 511796 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B515463 : Blo 511796 515463 := bstep (se 1 (by rfl) ⟨386597, by rfl⟩ : syracuseStep 515463 = 773195) B773195
theorem B515471 : Blo 511796 515471 := bstep (se 1 (by rfl) ⟨386603, by rfl⟩ : syracuseStep 515471 = 773207) B773207
theorem B1727891 : Blo 511796 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B515515 : Blo 511796 515515 := bstep (se 1 (by rfl) ⟨386636, by rfl⟩ : syracuseStep 515515 = 773273) B773273
theorem B515591 : Blo 511796 515591 := bstep (se 1 (by rfl) ⟨386693, by rfl⟩ : syracuseStep 515591 = 773387) B773387
theorem B515599 : Blo 511796 515599 := bstep (se 1 (by rfl) ⟨386699, by rfl⟩ : syracuseStep 515599 = 773399) B773399
theorem B974369 : Blo 511796 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B515643 : Blo 511796 515643 := bstep (se 1 (by rfl) ⟨386732, by rfl⟩ : syracuseStep 515643 = 773465) B773465
theorem B3202679 : Blo 511796 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B515719 : Blo 511796 515719 := bstep (se 1 (by rfl) ⟨386789, by rfl⟩ : syracuseStep 515719 = 773579) B773579
theorem B515727 : Blo 511796 515727 := bstep (se 1 (by rfl) ⟨386795, by rfl⟩ : syracuseStep 515727 = 773591) B773591
theorem B1466009 : Blo 511796 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B974521 : Blo 511796 974521 := bstep (se 2 (by rfl) ⟨365445, by rfl⟩ : syracuseStep 974521 = 730891) B730891
theorem B515771 : Blo 511796 515771 := bstep (se 1 (by rfl) ⟨386828, by rfl⟩ : syracuseStep 515771 = 773657) B773657
theorem B1302419 : Blo 511796 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B1040519 : Blo 511796 1040519 := bstep (se 1 (by rfl) ⟨780389, by rfl⟩ : syracuseStep 1040519 = 1560779) B1560779
theorem B1302713 : Blo 511796 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B3891401 : Blo 511796 3891401 := bstep (se 2 (by rfl) ⟨1459275, by rfl⟩ : syracuseStep 3891401 = 2918551) B2918551
theorem B11133197 : Blo 511796 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B1466657 : Blo 511796 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B14836061 : Blo 511796 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B4153933 : Blo 511796 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B1729295 : Blo 511796 1729295 := bstep (se 1 (by rfl) ⟨1296971, by rfl⟩ : syracuseStep 1729295 = 2593943) B2593943
theorem B647995 : Blo 511796 647995 := bstep (se 1 (by rfl) ⟨485996, by rfl⟩ : syracuseStep 647995 = 971993) B971993
theorem B1303411 : Blo 511796 1303411 := bstep (se 1 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 1303411 = 1955117) B1955117
theorem B1237945 : Blo 511796 1237945 := bstep (se 2 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 1237945 = 928459) B928459
theorem B1303553 : Blo 511796 1303553 := bstep (se 2 (by rfl) ⟨488832, by rfl⟩ : syracuseStep 1303553 = 977665) B977665
theorem B1729565 : Blo 511796 1729565 := bstep (se 3 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 1729565 = 648587) B648587
theorem B3204163 : Blo 511796 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B4678829 : Blo 511796 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B2974913 : Blo 511796 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1467659 : Blo 511796 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B976313 : Blo 511796 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B1304009 : Blo 511796 1304009 := bstep (se 2 (by rfl) ⟨489003, by rfl⟩ : syracuseStep 1304009 = 978007) B978007
theorem B1238561 : Blo 511796 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B1402429 : Blo 511796 1402429 := bstep (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) B525911
theorem B648967 : Blo 511796 648967 := bstep (se 1 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 648967 = 973451) B973451
theorem B1304363 : Blo 511796 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B4450099 : Blo 511796 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B3008477 : Blo 511796 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B1042465 : Blo 511796 1042465 := bstep (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) B781849
theorem B878635 : Blo 511796 878635 := bstep (se 1 (by rfl) ⟨658976, by rfl⟩ : syracuseStep 878635 = 1317953) B1317953
theorem B1239175 : Blo 511796 1239175 := bstep (se 1 (by rfl) ⟨929381, by rfl⟩ : syracuseStep 1239175 = 1858763) B1858763
theorem B649387 : Blo 511796 649387 := bstep (se 1 (by rfl) ⟨487040, by rfl⟩ : syracuseStep 649387 = 974081) B974081
theorem B780535 : Blo 511796 780535 := bstep (se 1 (by rfl) ⟨585401, by rfl⟩ : syracuseStep 780535 = 1170803) B1170803
theorem B8349965 : Blo 511796 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B649615 : Blo 511796 649615 := bstep (se 1 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 649615 = 974423) B974423
theorem B1730969 : Blo 511796 1730969 := bstep (se 2 (by rfl) ⟨649113, by rfl⟩ : syracuseStep 1730969 = 1298227) B1298227
theorem B780815 : Blo 511796 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B1043129 : Blo 511796 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B1305355 : Blo 511796 1305355 := bstep (se 1 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 1305355 = 1958033) B1958033
theorem B1305497 : Blo 511796 1305497 := bstep (se 2 (by rfl) ⟨489561, by rfl⟩ : syracuseStep 1305497 = 979123) B979123
theorem B5565347 : Blo 511796 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B1731671 : Blo 511796 1731671 := bstep (se 1 (by rfl) ⟨1298753, by rfl⟩ : syracuseStep 1731671 = 2597507) B2597507
theorem B650359 : Blo 511796 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B1174799 : Blo 511796 1174799 := bstep (se 1 (by rfl) ⟨881099, by rfl⟩ : syracuseStep 1174799 = 1762199) B1762199
theorem B978311 : Blo 511796 978311 := bstep (se 1 (by rfl) ⟨733733, by rfl⟩ : syracuseStep 978311 = 1467467) B1467467
theorem B6254009 : Blo 511796 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B650683 : Blo 511796 650683 := bstep (se 1 (by rfl) ⟨488012, by rfl⟩ : syracuseStep 650683 = 976025) B976025
theorem B5270989 : Blo 511796 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B1732157 : Blo 511796 1732157 := bstep (se 3 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 1732157 = 649559) B649559
theorem B4386575 : Blo 511796 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B2977681 : Blo 511796 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B651179 : Blo 511796 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B4157729 : Blo 511796 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B651655 : Blo 511796 651655 := bstep (se 1 (by rfl) ⟨488741, by rfl⟩ : syracuseStep 651655 = 977483) B977483
theorem B2191769 : Blo 511796 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B652151 : Blo 511796 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B1733561 : Blo 511796 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B652303 : Blo 511796 652303 := bstep (se 1 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 652303 = 978455) B978455
theorem B652475 : Blo 511796 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B90273005 : Blo 511796 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B554383 : Blo 511796 554383 := bstep (se 1 (by rfl) ⟨415787, by rfl⟩ : syracuseStep 554383 = 831575) B831575
theorem B1734155 : Blo 511796 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B1734263 : Blo 511796 1734263 := bstep (se 1 (by rfl) ⟨1300697, by rfl⟩ : syracuseStep 1734263 = 2601395) B2601395
theorem B1112249 : Blo 511796 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B1734857 : Blo 511796 1734857 := bstep (se 2 (by rfl) ⟨650571, by rfl⟩ : syracuseStep 1734857 = 1301143) B1301143
theorem B73202069 : Blo 511796 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B23788151 : Blo 511796 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B1735559 : Blo 511796 1735559 := bstep (se 1 (by rfl) ⟨1301669, by rfl⟩ : syracuseStep 1735559 = 2603339) B2603339
theorem B2784185 : Blo 511796 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B1604623 : Blo 511796 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1735937 : Blo 511796 1735937 := bstep (se 2 (by rfl) ⟨650976, by rfl⟩ : syracuseStep 1735937 = 1301953) B1301953
theorem B2915635 : Blo 511796 2915635 := bstep (se 1 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 2915635 = 4373453) B4373453
theorem B2195201 : Blo 511796 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B9404363 : Blo 511796 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B1737179 : Blo 511796 1737179 := bstep (se 1 (by rfl) ⟨1302884, by rfl⟩ : syracuseStep 1737179 = 2605769) B2605769
theorem B5538577 : Blo 511796 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B24052787 : Blo 511796 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1737881 : Blo 511796 1737881 := bstep (se 2 (by rfl) ⟨651705, by rfl⟩ : syracuseStep 1737881 = 1303411) B1303411
theorem B4162853 : Blo 511796 4162853 := bstep (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) B780535
theorem B2197115 : Blo 511796 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B13174487 : Blo 511796 13174487 := bstep (se 1 (by rfl) ⟨9880865, by rfl⟩ : syracuseStep 13174487 = 19761731) B19761731
theorem B1640353 : Blo 511796 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1869905 : Blo 511796 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B2459915 : Blo 511796 2459915 := bstep (se 1 (by rfl) ⟨1844936, by rfl⟩ : syracuseStep 2459915 = 3689873) B3689873
theorem B1739069 : Blo 511796 1739069 := bstep (se 3 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 1739069 = 652151) B652151
theorem B1673597 : Blo 511796 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B5933465 : Blo 511796 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B1640969 : Blo 511796 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B1739933 : Blo 511796 1739933 := bstep (se 3 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 1739933 = 652475) B652475
theorem B1641815 : Blo 511796 1641815 := bstep (se 1 (by rfl) ⟨1231361, by rfl⟩ : syracuseStep 1641815 = 2462723) B2462723
theorem B2198927 : Blo 511796 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B3968635 : Blo 511796 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1740473 : Blo 511796 1740473 := bstep (se 2 (by rfl) ⟨652677, by rfl⟩ : syracuseStep 1740473 = 1305355) B1305355
theorem B823303 : Blo 511796 823303 := bstep (se 1 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 823303 = 1234955) B1234955
theorem B692263 : Blo 511796 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B17174705 : Blo 511796 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B3707147 : Blo 511796 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B1151585 : Blo 511796 1151585 := bstep (se 2 (by rfl) ⟨431844, by rfl⟩ : syracuseStep 1151585 = 863689) B863689
theorem B1151927 : Blo 511796 1151927 := bstep (se 1 (by rfl) ⟨863945, by rfl⟩ : syracuseStep 1151927 = 1727891) B1727891
theorem B3970241 : Blo 511796 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B693679 : Blo 511796 693679 := bstep (se 1 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 693679 = 1040519) B1040519
theorem B2594267 : Blo 511796 2594267 := bstep (se 1 (by rfl) ⟨1945700, by rfl⟩ : syracuseStep 2594267 = 3891401) B3891401
theorem B1152521 : Blo 511796 1152521 := bstep (se 2 (by rfl) ⟨432195, by rfl⟩ : syracuseStep 1152521 = 864391) B864391
theorem B923233 : Blo 511796 923233 := bstep (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) B692425
theorem B1152863 : Blo 511796 1152863 := bstep (se 1 (by rfl) ⟨864647, by rfl⟩ : syracuseStep 1152863 = 1729295) B1729295
theorem B2594753 : Blo 511796 2594753 := bstep (se 2 (by rfl) ⟨973032, by rfl⟩ : syracuseStep 2594753 = 1946065) B1946065
theorem B1153043 : Blo 511796 1153043 := bstep (se 1 (by rfl) ⟨864782, by rfl⟩ : syracuseStep 1153043 = 1729565) B1729565
theorem B3119219 : Blo 511796 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1153385 : Blo 511796 1153385 := bstep (se 2 (by rfl) ⟨432519, by rfl⟩ : syracuseStep 1153385 = 865039) B865039
theorem B825707 : Blo 511796 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B1645019 : Blo 511796 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B2005651 : Blo 511796 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B11082419 : Blo 511796 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1153979 : Blo 511796 1153979 := bstep (se 1 (by rfl) ⟨865484, by rfl⟩ : syracuseStep 1153979 = 1730969) B1730969
theorem B1154105 : Blo 511796 1154105 := bstep (se 2 (by rfl) ⟨432789, by rfl⟩ : syracuseStep 1154105 = 865579) B865579
theorem B3710231 : Blo 511796 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B1154447 : Blo 511796 1154447 := bstep (se 1 (by rfl) ⟨865835, by rfl⟩ : syracuseStep 1154447 = 1731671) B1731671
theorem B2956709 : Blo 511796 2956709 := bstep (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) B554383
theorem B4169339 : Blo 511796 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B1777351 : Blo 511796 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B1154771 : Blo 511796 1154771 := bstep (se 1 (by rfl) ⟨866078, by rfl⟩ : syracuseStep 1154771 = 1732157) B1732157
theorem B2367299 : Blo 511796 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B1384265 : Blo 511796 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B2924383 : Blo 511796 2924383 := bstep (se 1 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 2924383 = 4386575) B4386575
theorem B8331275 : Blo 511796 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B2597021 : Blo 511796 2597021 := bstep (se 3 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 2597021 = 973883) B973883
theorem B1155707 : Blo 511796 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B926419 : Blo 511796 926419 := bstep (se 1 (by rfl) ⟨694814, by rfl⟩ : syracuseStep 926419 = 1389629) B1389629
theorem B1155833 : Blo 511796 1155833 := bstep (se 2 (by rfl) ⟨433437, by rfl⟩ : syracuseStep 1155833 = 866875) B866875
theorem B2925341 : Blo 511796 2925341 := bstep (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) B1097003
theorem B1647479 : Blo 511796 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B1156103 : Blo 511796 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B1647631 : Blo 511796 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B1156175 : Blo 511796 1156175 := bstep (se 1 (by rfl) ⟨867131, by rfl⟩ : syracuseStep 1156175 = 1734263) B1734263
theorem B992467 : Blo 511796 992467 := bstep (se 1 (by rfl) ⟨744350, by rfl⟩ : syracuseStep 992467 = 1488701) B1488701
theorem B2139497 : Blo 511796 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B2598317 : Blo 511796 2598317 := bstep (se 3 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 2598317 = 974369) B974369
theorem B1156571 : Blo 511796 1156571 := bstep (se 1 (by rfl) ⟨867428, by rfl⟩ : syracuseStep 1156571 = 1734857) B1734857
theorem B48801379 : Blo 511796 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B3286651 : Blo 511796 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B927443 : Blo 511796 927443 := bstep (se 1 (by rfl) ⟨695582, by rfl⟩ : syracuseStep 927443 = 1391165) B1391165
theorem B1157039 : Blo 511796 1157039 := bstep (se 1 (by rfl) ⟨867779, by rfl⟩ : syracuseStep 1157039 = 1735559) B1735559
theorem B1157291 : Blo 511796 1157291 := bstep (se 1 (by rfl) ⟨867968, by rfl⟩ : syracuseStep 1157291 = 1735937) B1735937
theorem B1648811 : Blo 511796 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B6564077 : Blo 511796 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B4401611 : Blo 511796 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B928379 : Blo 511796 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B6269575 : Blo 511796 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B1157831 : Blo 511796 1157831 := bstep (se 1 (by rfl) ⟨868373, by rfl⟩ : syracuseStep 1157831 = 1736747) B1736747
theorem B3910355 : Blo 511796 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B3287881 : Blo 511796 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B2599937 : Blo 511796 2599937 := bstep (se 2 (by rfl) ⟨974976, by rfl⟩ : syracuseStep 2599937 = 1949953) B1949953
theorem B1158695 : Blo 511796 1158695 := bstep (se 1 (by rfl) ⟨869021, by rfl⟩ : syracuseStep 1158695 = 1738043) B1738043
theorem B863993 : Blo 511796 863993 := bstep (se 2 (by rfl) ⟨323997, by rfl⟩ : syracuseStep 863993 = 647995) B647995
theorem B8761121 : Blo 511796 8761121 := bstep (se 2 (by rfl) ⟨3285420, by rfl⟩ : syracuseStep 8761121 = 6570841) B6570841
theorem B2600747 : Blo 511796 2600747 := bstep (se 1 (by rfl) ⟨1950560, by rfl⟩ : syracuseStep 2600747 = 3901121) B3901121
theorem B3944251 : Blo 511796 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B1159019 : Blo 511796 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B1159073 : Blo 511796 1159073 := bstep (se 2 (by rfl) ⟨434652, by rfl⟩ : syracuseStep 1159073 = 869305) B869305
theorem B1650593 : Blo 511796 1650593 := bstep (se 2 (by rfl) ⟨618972, by rfl⟩ : syracuseStep 1650593 = 1237945) B1237945
theorem B864175 : Blo 511796 864175 := bstep (se 1 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 864175 = 1296263) B1296263
theorem B864263 : Blo 511796 864263 := bstep (se 1 (by rfl) ⟨648197, by rfl⟩ : syracuseStep 864263 = 1296395) B1296395
theorem B1650707 : Blo 511796 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B4927517 : Blo 511796 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B1159415 : Blo 511796 1159415 := bstep (se 1 (by rfl) ⟨869561, by rfl⟩ : syracuseStep 1159415 = 1739123) B1739123
theorem B864607 : Blo 511796 864607 := bstep (se 1 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 864607 = 1296911) B1296911
theorem B864695 : Blo 511796 864695 := bstep (se 1 (by rfl) ⟨648521, by rfl⟩ : syracuseStep 864695 = 1297043) B1297043
theorem B2470459 : Blo 511796 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B1160009 : Blo 511796 1160009 := bstep (se 2 (by rfl) ⟨435003, by rfl⟩ : syracuseStep 1160009 = 870007) B870007
theorem B1946551 : Blo 511796 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B1389575 : Blo 511796 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B865289 : Blo 511796 865289 := bstep (se 2 (by rfl) ⟨324483, by rfl⟩ : syracuseStep 865289 = 648967) B648967
theorem B2929715 : Blo 511796 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B865451 : Blo 511796 865451 := bstep (se 1 (by rfl) ⟨649088, by rfl⟩ : syracuseStep 865451 = 1298177) B1298177
theorem B1389953 : Blo 511796 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B1947023 : Blo 511796 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B1652233 : Blo 511796 1652233 := bstep (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) B1239175
theorem B2930215 : Blo 511796 2930215 := bstep (se 1 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 2930215 = 4395323) B4395323
theorem B865849 : Blo 511796 865849 := bstep (se 2 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 865849 = 649387) B649387
theorem B21116477 : Blo 511796 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B1652347 : Blo 511796 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B2963083 : Blo 511796 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B865991 : Blo 511796 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B767849 : Blo 511796 767849 := bstep (se 2 (by rfl) ⟨287943, by rfl⟩ : syracuseStep 767849 = 575887) B575887
theorem B866153 : Blo 511796 866153 := bstep (se 2 (by rfl) ⟨324807, by rfl⟩ : syracuseStep 866153 = 649615) B649615
theorem B767927 : Blo 511796 767927 := bstep (se 1 (by rfl) ⟨575945, by rfl⟩ : syracuseStep 767927 = 1151891) B1151891
theorem B8796113 : Blo 511796 8796113 := bstep (se 2 (by rfl) ⟨3298542, by rfl⟩ : syracuseStep 8796113 = 6597085) B6597085
theorem B6272977 : Blo 511796 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B767963 : Blo 511796 767963 := bstep (se 1 (by rfl) ⟨575972, by rfl⟩ : syracuseStep 767963 = 1151945) B1151945
theorem B2603015 : Blo 511796 2603015 := bstep (se 1 (by rfl) ⟨1952261, by rfl⟩ : syracuseStep 2603015 = 3904523) B3904523
theorem B3913757 : Blo 511796 3913757 := bstep (se 3 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 3913757 = 1467659) B1467659
theorem B866551 : Blo 511796 866551 := bstep (se 1 (by rfl) ⟨649913, by rfl⟩ : syracuseStep 866551 = 1299827) B1299827
theorem B1948009 : Blo 511796 1948009 := bstep (se 2 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 1948009 = 1461007) B1461007
theorem B16005509 : Blo 511796 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B768431 : Blo 511796 768431 := bstep (se 1 (by rfl) ⟨576323, by rfl⟩ : syracuseStep 768431 = 1152647) B1152647
theorem B866747 : Blo 511796 866747 := bstep (se 1 (by rfl) ⟨650060, by rfl⟩ : syracuseStep 866747 = 1300121) B1300121
theorem B2603501 : Blo 511796 2603501 := bstep (se 3 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 2603501 = 976313) B976313
theorem B768521 : Blo 511796 768521 := bstep (se 2 (by rfl) ⟨288195, by rfl⟩ : syracuseStep 768521 = 576391) B576391
theorem B14989859 : Blo 511796 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B768551 : Blo 511796 768551 := bstep (se 1 (by rfl) ⟨576413, by rfl⟩ : syracuseStep 768551 = 1152827) B1152827
theorem B1849895 : Blo 511796 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B866855 : Blo 511796 866855 := bstep (se 1 (by rfl) ⟨650141, by rfl⟩ : syracuseStep 866855 = 1300283) B1300283
theorem B768635 : Blo 511796 768635 := bstep (se 1 (by rfl) ⟨576476, by rfl⟩ : syracuseStep 768635 = 1152953) B1152953
theorem B1948283 : Blo 511796 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B768761 : Blo 511796 768761 := bstep (se 2 (by rfl) ⟨288285, by rfl⟩ : syracuseStep 768761 = 576571) B576571
theorem B867145 : Blo 511796 867145 := bstep (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) B650359
theorem B768863 : Blo 511796 768863 := bstep (se 1 (by rfl) ⟨576647, by rfl⟩ : syracuseStep 768863 = 1153295) B1153295
theorem B768875 : Blo 511796 768875 := bstep (se 1 (by rfl) ⟨576656, by rfl⟩ : syracuseStep 768875 = 1153313) B1153313
theorem B867179 : Blo 511796 867179 := bstep (se 1 (by rfl) ⟨650384, by rfl⟩ : syracuseStep 867179 = 1300769) B1300769
theorem B5848037 : Blo 511796 5848037 := bstep (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) B1096507
theorem B769103 : Blo 511796 769103 := bstep (se 1 (by rfl) ⟨576827, by rfl⟩ : syracuseStep 769103 = 1153655) B1153655
theorem B769223 : Blo 511796 769223 := bstep (se 1 (by rfl) ⟨576917, by rfl⟩ : syracuseStep 769223 = 1153835) B1153835
theorem B867577 : Blo 511796 867577 := bstep (se 2 (by rfl) ⟨325341, by rfl⟩ : syracuseStep 867577 = 650683) B650683
theorem B7027985 : Blo 511796 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B2604311 : Blo 511796 2604311 := bstep (se 1 (by rfl) ⟨1953233, by rfl⟩ : syracuseStep 2604311 = 3906467) B3906467
theorem B769385 : Blo 511796 769385 := bstep (se 2 (by rfl) ⟨288519, by rfl⟩ : syracuseStep 769385 = 577039) B577039
theorem B769463 : Blo 511796 769463 := bstep (se 1 (by rfl) ⟨577097, by rfl⟩ : syracuseStep 769463 = 1154195) B1154195
theorem B769499 : Blo 511796 769499 := bstep (se 1 (by rfl) ⟨577124, by rfl⟩ : syracuseStep 769499 = 1154249) B1154249
theorem B867847 : Blo 511796 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B1883657 : Blo 511796 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B35569181 : Blo 511796 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B1097567 : Blo 511796 1097567 := bstep (se 1 (by rfl) ⟨823175, by rfl⟩ : syracuseStep 1097567 = 1646351) B1646351
theorem B769967 : Blo 511796 769967 := bstep (se 1 (by rfl) ⟨577475, by rfl⟩ : syracuseStep 769967 = 1154951) B1154951
theorem B868279 : Blo 511796 868279 := bstep (se 1 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 868279 = 1302419) B1302419
theorem B2768833 : Blo 511796 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B770057 : Blo 511796 770057 := bstep (se 2 (by rfl) ⟨288771, by rfl⟩ : syracuseStep 770057 = 577543) B577543
theorem B770087 : Blo 511796 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B770171 : Blo 511796 770171 := bstep (se 1 (by rfl) ⟨577628, by rfl⟩ : syracuseStep 770171 = 1155257) B1155257
theorem B868475 : Blo 511796 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B7422131 : Blo 511796 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B770297 : Blo 511796 770297 := bstep (se 2 (by rfl) ⟨288861, by rfl⟩ : syracuseStep 770297 = 577723) B577723
theorem B770399 : Blo 511796 770399 := bstep (se 1 (by rfl) ⟨577799, by rfl⟩ : syracuseStep 770399 = 1155599) B1155599
theorem B17088869 : Blo 511796 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B770411 : Blo 511796 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B2965997 : Blo 511796 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B868873 : Blo 511796 868873 := bstep (se 2 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 868873 = 651655) B651655
theorem B770639 : Blo 511796 770639 := bstep (se 1 (by rfl) ⟨577979, by rfl⟩ : syracuseStep 770639 = 1155959) B1155959
theorem B869035 : Blo 511796 869035 := bstep (se 1 (by rfl) ⟨651776, by rfl⟩ : syracuseStep 869035 = 1303553) B1303553
theorem B770759 : Blo 511796 770759 := bstep (se 1 (by rfl) ⟨578069, by rfl⟩ : syracuseStep 770759 = 1156139) B1156139
theorem B1983275 : Blo 511796 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B770921 : Blo 511796 770921 := bstep (se 2 (by rfl) ⟨289095, by rfl⟩ : syracuseStep 770921 = 578191) B578191
theorem B2605931 : Blo 511796 2605931 := bstep (se 1 (by rfl) ⟨1954448, by rfl⟩ : syracuseStep 2605931 = 3908897) B3908897
theorem B770999 : Blo 511796 770999 := bstep (se 1 (by rfl) ⟨578249, by rfl⟩ : syracuseStep 770999 = 1156499) B1156499
theorem B771035 : Blo 511796 771035 := bstep (se 1 (by rfl) ⟨578276, by rfl⟩ : syracuseStep 771035 = 1156553) B1156553
theorem B869339 : Blo 511796 869339 := bstep (se 1 (by rfl) ⟨652004, by rfl⟩ : syracuseStep 869339 = 1304009) B1304009
theorem B1229843 : Blo 511796 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B869575 : Blo 511796 869575 := bstep (se 1 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 869575 = 1304363) B1304363
theorem B869737 : Blo 511796 869737 := bstep (se 2 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 869737 = 652303) B652303
theorem B771503 : Blo 511796 771503 := bstep (se 1 (by rfl) ⟨578627, by rfl⟩ : syracuseStep 771503 = 1157255) B1157255
theorem B2606579 : Blo 511796 2606579 := bstep (se 1 (by rfl) ⟨1954934, by rfl⟩ : syracuseStep 2606579 = 3909869) B3909869
theorem B1459721 : Blo 511796 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B771593 : Blo 511796 771593 := bstep (se 2 (by rfl) ⟨289347, by rfl⟩ : syracuseStep 771593 = 578695) B578695
theorem B771623 : Blo 511796 771623 := bstep (se 1 (by rfl) ⟨578717, by rfl⟩ : syracuseStep 771623 = 1157435) B1157435
theorem B7390763 : Blo 511796 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B771707 : Blo 511796 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B1296071 : Blo 511796 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B2148049 : Blo 511796 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1296121 : Blo 511796 1296121 := bstep (se 2 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 1296121 = 972091) B972091
theorem B771833 : Blo 511796 771833 := bstep (se 2 (by rfl) ⟨289437, by rfl⟩ : syracuseStep 771833 = 578875) B578875
theorem B771935 : Blo 511796 771935 := bstep (se 1 (by rfl) ⟨578951, by rfl⟩ : syracuseStep 771935 = 1157903) B1157903
theorem B771947 : Blo 511796 771947 := bstep (se 1 (by rfl) ⟨578960, by rfl⟩ : syracuseStep 771947 = 1157921) B1157921
theorem B4376429 : Blo 511796 4376429 := bstep (se 3 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 4376429 = 1641161) B1641161
theorem B870331 : Blo 511796 870331 := bstep (se 1 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 870331 = 1305497) B1305497
theorem B772175 : Blo 511796 772175 := bstep (se 1 (by rfl) ⟨579131, by rfl⟩ : syracuseStep 772175 = 1158263) B1158263
theorem B1951897 : Blo 511796 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B772295 : Blo 511796 772295 := bstep (se 1 (by rfl) ⟨579221, by rfl⟩ : syracuseStep 772295 = 1158443) B1158443
theorem B772457 : Blo 511796 772457 := bstep (se 2 (by rfl) ⟨289671, by rfl⟩ : syracuseStep 772457 = 579343) B579343
theorem B1296769 : Blo 511796 1296769 := bstep (se 2 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 1296769 = 972577) B972577
theorem B772535 : Blo 511796 772535 := bstep (se 1 (by rfl) ⟨579401, by rfl⟩ : syracuseStep 772535 = 1158803) B1158803
theorem B1952201 : Blo 511796 1952201 := bstep (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) B1464151
theorem B772571 : Blo 511796 772571 := bstep (se 1 (by rfl) ⟨579428, by rfl⟩ : syracuseStep 772571 = 1158857) B1158857
theorem B1559027 : Blo 511796 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B2607875 : Blo 511796 2607875 := bstep (se 1 (by rfl) ⟨1955906, by rfl⟩ : syracuseStep 2607875 = 3911813) B3911813
theorem B2771819 : Blo 511796 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B1952687 : Blo 511796 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B773039 : Blo 511796 773039 := bstep (se 1 (by rfl) ⟨579779, by rfl⟩ : syracuseStep 773039 = 1159559) B1159559
theorem B1461179 : Blo 511796 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B773129 : Blo 511796 773129 := bstep (se 2 (by rfl) ⟨289923, by rfl⟩ : syracuseStep 773129 = 579847) B579847
theorem B773159 : Blo 511796 773159 := bstep (se 1 (by rfl) ⟨579869, by rfl⟩ : syracuseStep 773159 = 1159739) B1159739
theorem B773243 : Blo 511796 773243 := bstep (se 1 (by rfl) ⟨579932, by rfl⟩ : syracuseStep 773243 = 1159865) B1159865
theorem B1756313 : Blo 511796 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B1297579 : Blo 511796 1297579 := bstep (se 1 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 1297579 = 1946369) B1946369
theorem B773369 : Blo 511796 773369 := bstep (se 2 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 773369 = 580027) B580027
theorem B773471 : Blo 511796 773471 := bstep (se 1 (by rfl) ⟨580103, by rfl⟩ : syracuseStep 773471 = 1160207) B1160207
theorem B773483 : Blo 511796 773483 := bstep (se 1 (by rfl) ⟨580112, by rfl⟩ : syracuseStep 773483 = 1160225) B1160225
theorem B1297883 : Blo 511796 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B60182003 : Blo 511796 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B577147 : Blo 511796 577147 := bstep (se 1 (by rfl) ⟨432860, by rfl⟩ : syracuseStep 577147 = 865721) B865721
theorem B511823 : Blo 511796 511823 := bstep (se 1 (by rfl) ⟨383867, by rfl⟩ : syracuseStep 511823 = 767735) B767735
theorem B511839 : Blo 511796 511839 := bstep (se 1 (by rfl) ⟨383879, by rfl⟩ : syracuseStep 511839 = 767759) B767759
theorem B511867 : Blo 511796 511867 := bstep (se 1 (by rfl) ⟨383900, by rfl⟩ : syracuseStep 511867 = 767801) B767801
theorem B511919 : Blo 511796 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B511943 : Blo 511796 511943 := bstep (se 1 (by rfl) ⟨383957, by rfl⟩ : syracuseStep 511943 = 767915) B767915
theorem B511963 : Blo 511796 511963 := bstep (se 1 (by rfl) ⟨383972, by rfl⟩ : syracuseStep 511963 = 767945) B767945
theorem B512039 : Blo 511796 512039 := bstep (se 1 (by rfl) ⟨384029, by rfl⟩ : syracuseStep 512039 = 768059) B768059
theorem B512079 : Blo 511796 512079 := bstep (se 1 (by rfl) ⟨384059, by rfl⟩ : syracuseStep 512079 = 768119) B768119
theorem B577615 : Blo 511796 577615 := bstep (se 1 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 577615 = 866423) B866423
theorem B512095 : Blo 511796 512095 := bstep (se 1 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 512095 = 768143) B768143
theorem B512123 : Blo 511796 512123 := bstep (se 1 (by rfl) ⟨384092, by rfl⟩ : syracuseStep 512123 = 768185) B768185
theorem B512175 : Blo 511796 512175 := bstep (se 1 (by rfl) ⟨384131, by rfl⟩ : syracuseStep 512175 = 768263) B768263
theorem B512199 : Blo 511796 512199 := bstep (se 1 (by rfl) ⟨384149, by rfl⟩ : syracuseStep 512199 = 768299) B768299
theorem B512219 : Blo 511796 512219 := bstep (se 1 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 512219 = 768329) B768329
theorem B512295 : Blo 511796 512295 := bstep (se 1 (by rfl) ⟨384221, by rfl⟩ : syracuseStep 512295 = 768443) B768443
theorem B8540477 : Blo 511796 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B512335 : Blo 511796 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B2609495 : Blo 511796 2609495 := bstep (se 1 (by rfl) ⟨1957121, by rfl⟩ : syracuseStep 2609495 = 3914243) B3914243
theorem B512351 : Blo 511796 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B512379 : Blo 511796 512379 := bstep (se 1 (by rfl) ⟨384284, by rfl⟩ : syracuseStep 512379 = 768569) B768569
theorem B3887513 : Blo 511796 3887513 := bstep (se 2 (by rfl) ⟨1457817, by rfl⟩ : syracuseStep 3887513 = 2915635) B2915635
theorem B512431 : Blo 511796 512431 := bstep (se 1 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 512431 = 768647) B768647
theorem B512455 : Blo 511796 512455 := bstep (se 1 (by rfl) ⟨384341, by rfl⟩ : syracuseStep 512455 = 768683) B768683
theorem B512475 : Blo 511796 512475 := bstep (se 1 (by rfl) ⟨384356, by rfl⟩ : syracuseStep 512475 = 768713) B768713
theorem B578011 : Blo 511796 578011 := bstep (se 1 (by rfl) ⟨433508, by rfl⟩ : syracuseStep 578011 = 867017) B867017
theorem B1954313 : Blo 511796 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B512551 : Blo 511796 512551 := bstep (se 1 (by rfl) ⟨384413, by rfl⟩ : syracuseStep 512551 = 768827) B768827
theorem B512591 : Blo 511796 512591 := bstep (se 1 (by rfl) ⟨384443, by rfl⟩ : syracuseStep 512591 = 768887) B768887
theorem B512607 : Blo 511796 512607 := bstep (se 1 (by rfl) ⟨384455, by rfl⟩ : syracuseStep 512607 = 768911) B768911
theorem B512635 : Blo 511796 512635 := bstep (se 1 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 512635 = 768953) B768953
theorem B1856123 : Blo 511796 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B5853869 : Blo 511796 5853869 := bstep (se 3 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 5853869 = 2195201) B2195201
theorem B512687 : Blo 511796 512687 := bstep (se 1 (by rfl) ⟨384515, by rfl⟩ : syracuseStep 512687 = 769031) B769031
theorem B512711 : Blo 511796 512711 := bstep (se 1 (by rfl) ⟨384533, by rfl⟩ : syracuseStep 512711 = 769067) B769067
theorem B5952211 : Blo 511796 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B512731 : Blo 511796 512731 := bstep (se 1 (by rfl) ⟨384548, by rfl⟩ : syracuseStep 512731 = 769097) B769097
theorem B512807 : Blo 511796 512807 := bstep (se 1 (by rfl) ⟨384605, by rfl⟩ : syracuseStep 512807 = 769211) B769211
theorem B512847 : Blo 511796 512847 := bstep (se 1 (by rfl) ⟨384635, by rfl⟩ : syracuseStep 512847 = 769271) B769271
theorem B512863 : Blo 511796 512863 := bstep (se 1 (by rfl) ⟨384647, by rfl⟩ : syracuseStep 512863 = 769295) B769295
theorem B512891 : Blo 511796 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B1299361 : Blo 511796 1299361 := bstep (se 2 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 1299361 = 974521) B974521
theorem B1168303 : Blo 511796 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B512943 : Blo 511796 512943 := bstep (se 1 (by rfl) ⟨384707, by rfl⟩ : syracuseStep 512943 = 769415) B769415
theorem B578479 : Blo 511796 578479 := bstep (se 1 (by rfl) ⟨433859, by rfl⟩ : syracuseStep 578479 = 867719) B867719
theorem B512967 : Blo 511796 512967 := bstep (se 1 (by rfl) ⟨384725, by rfl⟩ : syracuseStep 512967 = 769451) B769451
theorem B512987 : Blo 511796 512987 := bstep (se 1 (by rfl) ⟨384740, by rfl⟩ : syracuseStep 512987 = 769481) B769481
theorem B513063 : Blo 511796 513063 := bstep (se 1 (by rfl) ⟨384797, by rfl⟩ : syracuseStep 513063 = 769595) B769595
theorem B971833 : Blo 511796 971833 := bstep (se 2 (by rfl) ⟨364437, by rfl⟩ : syracuseStep 971833 = 728875) B728875
theorem B513103 : Blo 511796 513103 := bstep (se 1 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 513103 = 769655) B769655
theorem B11293789 : Blo 511796 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B513119 : Blo 511796 513119 := bstep (se 1 (by rfl) ⟨384839, by rfl⟩ : syracuseStep 513119 = 769679) B769679
theorem B513147 : Blo 511796 513147 := bstep (se 1 (by rfl) ⟨384860, by rfl⟩ : syracuseStep 513147 = 769721) B769721
theorem B513199 : Blo 511796 513199 := bstep (se 1 (by rfl) ⟨384899, by rfl⟩ : syracuseStep 513199 = 769799) B769799
theorem B513223 : Blo 511796 513223 := bstep (se 1 (by rfl) ⟨384917, by rfl⟩ : syracuseStep 513223 = 769835) B769835
theorem B513243 : Blo 511796 513243 := bstep (se 1 (by rfl) ⟨384932, by rfl⟩ : syracuseStep 513243 = 769865) B769865
theorem B513319 : Blo 511796 513319 := bstep (se 1 (by rfl) ⟨384989, by rfl⟩ : syracuseStep 513319 = 769979) B769979
theorem B513359 : Blo 511796 513359 := bstep (se 1 (by rfl) ⟨385019, by rfl⟩ : syracuseStep 513359 = 770039) B770039
theorem B513375 : Blo 511796 513375 := bstep (se 1 (by rfl) ⟨385031, by rfl⟩ : syracuseStep 513375 = 770063) B770063
theorem B578911 : Blo 511796 578911 := bstep (se 1 (by rfl) ⟨434183, by rfl⟩ : syracuseStep 578911 = 868367) B868367
theorem B972137 : Blo 511796 972137 := bstep (se 2 (by rfl) ⟨364551, by rfl⟩ : syracuseStep 972137 = 729103) B729103
theorem B513403 : Blo 511796 513403 := bstep (se 1 (by rfl) ⟨385052, by rfl⟩ : syracuseStep 513403 = 770105) B770105
theorem B972175 : Blo 511796 972175 := bstep (se 1 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 972175 = 1458263) B1458263
theorem B513455 : Blo 511796 513455 := bstep (se 1 (by rfl) ⟨385091, by rfl⟩ : syracuseStep 513455 = 770183) B770183
theorem B513479 : Blo 511796 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B513499 : Blo 511796 513499 := bstep (se 1 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 513499 = 770249) B770249
theorem B513575 : Blo 511796 513575 := bstep (se 1 (by rfl) ⟨385181, by rfl⟩ : syracuseStep 513575 = 770363) B770363
theorem B513615 : Blo 511796 513615 := bstep (se 1 (by rfl) ⟨385211, by rfl⟩ : syracuseStep 513615 = 770423) B770423
theorem B513631 : Blo 511796 513631 := bstep (se 1 (by rfl) ⟨385223, by rfl⟩ : syracuseStep 513631 = 770447) B770447
theorem B513659 : Blo 511796 513659 := bstep (se 1 (by rfl) ⟨385244, by rfl⟩ : syracuseStep 513659 = 770489) B770489
theorem B513711 : Blo 511796 513711 := bstep (se 1 (by rfl) ⟨385283, by rfl⟩ : syracuseStep 513711 = 770567) B770567
theorem B513735 : Blo 511796 513735 := bstep (se 1 (by rfl) ⟨385301, by rfl⟩ : syracuseStep 513735 = 770603) B770603
theorem B579271 : Blo 511796 579271 := bstep (se 1 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 579271 = 868907) B868907
theorem B513755 : Blo 511796 513755 := bstep (se 1 (by rfl) ⟨385316, by rfl⟩ : syracuseStep 513755 = 770633) B770633
theorem B513831 : Blo 511796 513831 := bstep (se 1 (by rfl) ⟨385373, by rfl⟩ : syracuseStep 513831 = 770747) B770747
theorem B513871 : Blo 511796 513871 := bstep (se 1 (by rfl) ⟨385403, by rfl⟩ : syracuseStep 513871 = 770807) B770807
theorem B513887 : Blo 511796 513887 := bstep (se 1 (by rfl) ⟨385415, by rfl⟩ : syracuseStep 513887 = 770831) B770831
theorem B513915 : Blo 511796 513915 := bstep (se 1 (by rfl) ⟨385436, by rfl⟩ : syracuseStep 513915 = 770873) B770873
theorem B513967 : Blo 511796 513967 := bstep (se 1 (by rfl) ⟨385475, by rfl⟩ : syracuseStep 513967 = 770951) B770951
theorem B1955771 : Blo 511796 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B513991 : Blo 511796 513991 := bstep (se 1 (by rfl) ⟨385493, by rfl⟩ : syracuseStep 513991 = 770987) B770987
theorem B22566869 : Blo 511796 22566869 := bstep (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) B528911
theorem B514011 : Blo 511796 514011 := bstep (se 1 (by rfl) ⟨385508, by rfl⟩ : syracuseStep 514011 = 771017) B771017
theorem B514087 : Blo 511796 514087 := bstep (se 1 (by rfl) ⟨385565, by rfl⟩ : syracuseStep 514087 = 771131) B771131
theorem B514127 : Blo 511796 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B514143 : Blo 511796 514143 := bstep (se 1 (by rfl) ⟨385607, by rfl⟩ : syracuseStep 514143 = 771215) B771215
theorem B514171 : Blo 511796 514171 := bstep (se 1 (by rfl) ⟨385628, by rfl⟩ : syracuseStep 514171 = 771257) B771257
theorem B514223 : Blo 511796 514223 := bstep (se 1 (by rfl) ⟨385667, by rfl⟩ : syracuseStep 514223 = 771335) B771335
theorem B514247 : Blo 511796 514247 := bstep (se 1 (by rfl) ⟨385685, by rfl⟩ : syracuseStep 514247 = 771371) B771371
theorem B514267 : Blo 511796 514267 := bstep (se 1 (by rfl) ⟨385700, by rfl⟩ : syracuseStep 514267 = 771401) B771401
theorem B514343 : Blo 511796 514343 := bstep (se 1 (by rfl) ⟨385757, by rfl⟩ : syracuseStep 514343 = 771515) B771515
theorem B3889457 : Blo 511796 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1857853 : Blo 511796 1857853 := bstep (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) B696695
theorem B514383 : Blo 511796 514383 := bstep (se 1 (by rfl) ⟨385787, by rfl⟩ : syracuseStep 514383 = 771575) B771575
theorem B514399 : Blo 511796 514399 := bstep (se 1 (by rfl) ⟨385799, by rfl⟩ : syracuseStep 514399 = 771599) B771599
theorem B514427 : Blo 511796 514427 := bstep (se 1 (by rfl) ⟨385820, by rfl⟩ : syracuseStep 514427 = 771641) B771641
theorem B514479 : Blo 511796 514479 := bstep (se 1 (by rfl) ⟨385859, by rfl⟩ : syracuseStep 514479 = 771719) B771719
theorem B514503 : Blo 511796 514503 := bstep (se 1 (by rfl) ⟨385877, by rfl⟩ : syracuseStep 514503 = 771755) B771755
theorem B514523 : Blo 511796 514523 := bstep (se 1 (by rfl) ⟨385892, by rfl⟩ : syracuseStep 514523 = 771785) B771785
theorem B514599 : Blo 511796 514599 := bstep (se 1 (by rfl) ⟨385949, by rfl⟩ : syracuseStep 514599 = 771899) B771899
theorem B580135 : Blo 511796 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B514639 : Blo 511796 514639 := bstep (se 1 (by rfl) ⟨385979, by rfl⟩ : syracuseStep 514639 = 771959) B771959
theorem B514655 : Blo 511796 514655 := bstep (se 1 (by rfl) ⟨385991, by rfl⟩ : syracuseStep 514655 = 771983) B771983
theorem B514683 : Blo 511796 514683 := bstep (se 1 (by rfl) ⟨386012, by rfl⟩ : syracuseStep 514683 = 772025) B772025
theorem B514735 : Blo 511796 514735 := bstep (se 1 (by rfl) ⟨386051, by rfl⟩ : syracuseStep 514735 = 772103) B772103
theorem B1170119 : Blo 511796 1170119 := bstep (se 1 (by rfl) ⟨877589, by rfl⟩ : syracuseStep 1170119 = 1755179) B1755179
theorem B514759 : Blo 511796 514759 := bstep (se 1 (by rfl) ⟨386069, by rfl⟩ : syracuseStep 514759 = 772139) B772139
theorem B514779 : Blo 511796 514779 := bstep (se 1 (by rfl) ⟨386084, by rfl⟩ : syracuseStep 514779 = 772169) B772169
theorem B514855 : Blo 511796 514855 := bstep (se 1 (by rfl) ⟨386141, by rfl⟩ : syracuseStep 514855 = 772283) B772283
theorem B514895 : Blo 511796 514895 := bstep (se 1 (by rfl) ⟨386171, by rfl⟩ : syracuseStep 514895 = 772343) B772343
theorem B514911 : Blo 511796 514911 := bstep (se 1 (by rfl) ⟨386183, by rfl⟩ : syracuseStep 514911 = 772367) B772367
theorem B1727351 : Blo 511796 1727351 := bstep (se 1 (by rfl) ⟨1295513, by rfl⟩ : syracuseStep 1727351 = 2591027) B2591027
theorem B514939 : Blo 511796 514939 := bstep (se 1 (by rfl) ⟨386204, by rfl⟩ : syracuseStep 514939 = 772409) B772409
theorem B514991 : Blo 511796 514991 := bstep (se 1 (by rfl) ⟨386243, by rfl⟩ : syracuseStep 514991 = 772487) B772487
theorem B515015 : Blo 511796 515015 := bstep (se 1 (by rfl) ⟨386261, by rfl⟩ : syracuseStep 515015 = 772523) B772523
theorem B515035 : Blo 511796 515035 := bstep (se 1 (by rfl) ⟨386276, by rfl⟩ : syracuseStep 515035 = 772553) B772553
theorem B515111 : Blo 511796 515111 := bstep (se 1 (by rfl) ⟨386333, by rfl⟩ : syracuseStep 515111 = 772667) B772667
theorem B1727567 : Blo 511796 1727567 := bstep (se 1 (by rfl) ⟨1295675, by rfl⟩ : syracuseStep 1727567 = 2591351) B2591351
theorem B515151 : Blo 511796 515151 := bstep (se 1 (by rfl) ⟨386363, by rfl⟩ : syracuseStep 515151 = 772727) B772727
theorem B515167 : Blo 511796 515167 := bstep (se 1 (by rfl) ⟨386375, by rfl⟩ : syracuseStep 515167 = 772751) B772751
theorem B515195 : Blo 511796 515195 := bstep (se 1 (by rfl) ⟨386396, by rfl⟩ : syracuseStep 515195 = 772793) B772793
theorem B515247 : Blo 511796 515247 := bstep (se 1 (by rfl) ⟨386435, by rfl⟩ : syracuseStep 515247 = 772871) B772871
theorem B515271 : Blo 511796 515271 := bstep (se 1 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 515271 = 772907) B772907
theorem B974035 : Blo 511796 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B515291 : Blo 511796 515291 := bstep (se 1 (by rfl) ⟨386468, by rfl⟩ : syracuseStep 515291 = 772937) B772937
theorem B515367 : Blo 511796 515367 := bstep (se 1 (by rfl) ⟨386525, by rfl⟩ : syracuseStep 515367 = 773051) B773051
theorem B515407 : Blo 511796 515407 := bstep (se 1 (by rfl) ⟨386555, by rfl⟩ : syracuseStep 515407 = 773111) B773111
theorem B515423 : Blo 511796 515423 := bstep (se 1 (by rfl) ⟨386567, by rfl⟩ : syracuseStep 515423 = 773135) B773135
theorem B515451 : Blo 511796 515451 := bstep (se 1 (by rfl) ⟨386588, by rfl⟩ : syracuseStep 515451 = 773177) B773177
theorem B1301903 : Blo 511796 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B2088335 : Blo 511796 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B515503 : Blo 511796 515503 := bstep (se 1 (by rfl) ⟨386627, by rfl⟩ : syracuseStep 515503 = 773255) B773255
theorem B974263 : Blo 511796 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B515527 : Blo 511796 515527 := bstep (se 1 (by rfl) ⟨386645, by rfl⟩ : syracuseStep 515527 = 773291) B773291
theorem B1727945 : Blo 511796 1727945 := bstep (se 2 (by rfl) ⟨647979, by rfl⟩ : syracuseStep 1727945 = 1295959) B1295959
theorem B3694025 : Blo 511796 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B515547 : Blo 511796 515547 := bstep (se 1 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 515547 = 773321) B773321
theorem B3300851 : Blo 511796 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B515623 : Blo 511796 515623 := bstep (se 1 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 515623 = 773435) B773435
theorem B515663 : Blo 511796 515663 := bstep (se 1 (by rfl) ⟨386747, by rfl⟩ : syracuseStep 515663 = 773495) B773495
theorem B515679 : Blo 511796 515679 := bstep (se 1 (by rfl) ⟨386759, by rfl⟩ : syracuseStep 515679 = 773519) B773519
theorem B515707 : Blo 511796 515707 := bstep (se 1 (by rfl) ⟨386780, by rfl⟩ : syracuseStep 515707 = 773561) B773561
theorem B3301003 : Blo 511796 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B515759 : Blo 511796 515759 := bstep (se 1 (by rfl) ⟨386819, by rfl⟩ : syracuseStep 515759 = 773639) B773639
theorem B515783 : Blo 511796 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B1302227 : Blo 511796 1302227 := bstep (se 1 (by rfl) ⟨976670, by rfl⟩ : syracuseStep 1302227 = 1953341) B1953341
theorem B1728215 : Blo 511796 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B1728431 : Blo 511796 1728431 := bstep (se 1 (by rfl) ⟨1296323, by rfl⟩ : syracuseStep 1728431 = 2592647) B2592647
theorem B974855 : Blo 511796 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B548903 : Blo 511796 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B1171513 : Blo 511796 1171513 := bstep (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) B878635
theorem B1958003 : Blo 511796 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1303391 : Blo 511796 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B975721 : Blo 511796 975721 := bstep (se 2 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 975721 = 731791) B731791
theorem B975881 : Blo 511796 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B2188367 : Blo 511796 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B4384115 : Blo 511796 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B4941323 : Blo 511796 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B3892859 : Blo 511796 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B1468115 : Blo 511796 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1304495 : Blo 511796 1304495 := bstep (se 1 (by rfl) ⟨978371, by rfl⟩ : syracuseStep 1304495 = 1956743) B1956743
theorem B1468343 : Blo 511796 1468343 := bstep (se 1 (by rfl) ⟨1101257, by rfl⟩ : syracuseStep 1468343 = 2202515) B2202515
theorem B2189393 : Blo 511796 2189393 := bstep (se 2 (by rfl) ⟨821022, by rfl⟩ : syracuseStep 2189393 = 1642045) B1642045
theorem B1730807 : Blo 511796 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B4385177 : Blo 511796 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B977339 : Blo 511796 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B1763785 : Blo 511796 1763785 := bstep (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) B1322839
theorem B1731131 : Blo 511796 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B1731401 : Blo 511796 1731401 := bstep (se 2 (by rfl) ⟨649275, by rfl⟩ : syracuseStep 1731401 = 1298551) B1298551
theorem B977771 : Blo 511796 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B9890707 : Blo 511796 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B977825 : Blo 511796 977825 := bstep (se 2 (by rfl) ⟨366684, by rfl⟩ : syracuseStep 977825 = 733369) B733369
theorem B1666585 : Blo 511796 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B1732535 : Blo 511796 1732535 := bstep (se 1 (by rfl) ⟨1299401, by rfl⟩ : syracuseStep 1732535 = 2598803) B2598803
theorem B5566643 : Blo 511796 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B520543 : Blo 511796 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B5534081 : Blo 511796 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B2191853 : Blo 511796 2191853 := bstep (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) B821945
theorem B2781677 : Blo 511796 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B1733129 : Blo 511796 1733129 := bstep (se 2 (by rfl) ⟨649923, by rfl⟩ : syracuseStep 1733129 = 1299847) B1299847
theorem B2782025 : Blo 511796 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B783199 : Blo 511796 783199 := bstep (se 1 (by rfl) ⟨587399, by rfl⟩ : syracuseStep 783199 = 1174799) B1174799
theorem B652207 : Blo 511796 652207 := bstep (se 1 (by rfl) ⟨489155, by rfl⟩ : syracuseStep 652207 = 978311) B978311
theorem B12645341 : Blo 511796 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B4945049 : Blo 511796 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B5862617 : Blo 511796 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B1733993 : Blo 511796 1733993 := bstep (se 2 (by rfl) ⟨650247, by rfl⟩ : syracuseStep 1733993 = 1300495) B1300495
theorem B1734587 : Blo 511796 1734587 := bstep (se 1 (by rfl) ⟨1300940, by rfl⟩ : syracuseStep 1734587 = 2601881) B2601881
theorem B6584327 : Blo 511796 6584327 := bstep (se 1 (by rfl) ⟨4938245, by rfl⟩ : syracuseStep 6584327 = 9876491) B9876491
theorem B2194451 : Blo 511796 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B15858767 : Blo 511796 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B1736315 : Blo 511796 1736315 := bstep (se 1 (by rfl) ⟨1302236, by rfl⟩ : syracuseStep 1736315 = 2604473) B2604473
theorem B1736477 : Blo 511796 1736477 := bstep (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) B651179
theorem B4390949 : Blo 511796 4390949 := bstep (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) B823303
theorem B4948087 : Blo 511796 4948087 := bstep (se 1 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 4948087 = 7422131) B7422131
theorem B1737287 : Blo 511796 1737287 := bstep (se 1 (by rfl) ⟨1302965, by rfl⟩ : syracuseStep 1737287 = 2605931) B2605931
theorem B819895 : Blo 511796 819895 := bstep (se 1 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 819895 = 1229843) B1229843
theorem B1737719 : Blo 511796 1737719 := bstep (se 1 (by rfl) ⟨1303289, by rfl⟩ : syracuseStep 1737719 = 2606579) B2606579
theorem B8782991 : Blo 511796 8782991 := bstep (se 1 (by rfl) ⟨6587243, by rfl⟩ : syracuseStep 8782991 = 13174487) B13174487
theorem B2917619 : Blo 511796 2917619 := bstep (se 1 (by rfl) ⟨2188214, by rfl⟩ : syracuseStep 2917619 = 4376429) B4376429
theorem B1246603 : Blo 511796 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B1639943 : Blo 511796 1639943 := bstep (se 1 (by rfl) ⟨1229957, by rfl⟩ : syracuseStep 1639943 = 2459915) B2459915
theorem B1115731 : Blo 511796 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B1738583 : Blo 511796 1738583 := bstep (se 1 (by rfl) ⟨1303937, by rfl⟩ : syracuseStep 1738583 = 2607875) B2607875
theorem B1739663 : Blo 511796 1739663 := bstep (se 1 (by rfl) ⟨1304747, by rfl⟩ : syracuseStep 1739663 = 2609495) B2609495
theorem B2591675 : Blo 511796 2591675 := bstep (se 1 (by rfl) ⟨1943756, by rfl⟩ : syracuseStep 2591675 = 3887513) B3887513
theorem B3902579 : Blo 511796 3902579 := bstep (se 1 (by rfl) ⟨2926934, by rfl⟩ : syracuseStep 3902579 = 5853869) B5853869
theorem B8359433 : Blo 511796 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B15044579 : Blo 511796 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B2592971 : Blo 511796 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1151567 : Blo 511796 1151567 := bstep (se 1 (by rfl) ⟨863675, by rfl⟩ : syracuseStep 1151567 = 1727351) B1727351
theorem B1151711 : Blo 511796 1151711 := bstep (se 1 (by rfl) ⟨863783, by rfl⟩ : syracuseStep 1151711 = 1727567) B1727567
theorem B1151963 : Blo 511796 1151963 := bstep (se 1 (by rfl) ⟨863972, by rfl⟩ : syracuseStep 1151963 = 1727945) B1727945
theorem B2462683 : Blo 511796 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B2200567 : Blo 511796 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B1152143 : Blo 511796 1152143 := bstep (se 1 (by rfl) ⟨864107, by rfl⟩ : syracuseStep 1152143 = 1728215) B1728215
theorem B1578199 : Blo 511796 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B922843 : Blo 511796 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B1152233 : Blo 511796 1152233 := bstep (se 2 (by rfl) ⟨432087, by rfl⟩ : syracuseStep 1152233 = 864175) B864175
theorem B1152287 : Blo 511796 1152287 := bstep (se 1 (by rfl) ⟨864215, by rfl⟩ : syracuseStep 1152287 = 1728431) B1728431
theorem B923017 : Blo 511796 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B8787365 : Blo 511796 8787365 := bstep (se 4 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 8787365 = 1647631) B1647631
theorem B1152809 : Blo 511796 1152809 := bstep (se 2 (by rfl) ⟨432303, by rfl⟩ : syracuseStep 1152809 = 864607) B864607
theorem B694057 : Blo 511796 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B2922743 : Blo 511796 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B2595239 : Blo 511796 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B2595401 : Blo 511796 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B1153871 : Blo 511796 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B2923451 : Blo 511796 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B1154087 : Blo 511796 1154087 := bstep (se 1 (by rfl) ⟨865565, by rfl⟩ : syracuseStep 1154087 = 1731131) B1731131
theorem B1154267 : Blo 511796 1154267 := bstep (se 1 (by rfl) ⟨865700, by rfl⟩ : syracuseStep 1154267 = 1731401) B1731401
theorem B924905 : Blo 511796 924905 := bstep (se 2 (by rfl) ⟨346839, by rfl⟩ : syracuseStep 924905 = 693679) B693679
theorem B2202977 : Blo 511796 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B3906953 : Blo 511796 3906953 := bstep (se 2 (by rfl) ⟨1465107, by rfl⟩ : syracuseStep 3906953 = 2930215) B2930215
theorem B1154465 : Blo 511796 1154465 := bstep (se 2 (by rfl) ⟨432924, by rfl⟩ : syracuseStep 1154465 = 865849) B865849
theorem B2203129 : Blo 511796 2203129 := bstep (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) B1652347
theorem B5840747 : Blo 511796 5840747 := bstep (se 1 (by rfl) ⟨4380560, by rfl⟩ : syracuseStep 5840747 = 8761121) B8761121
theorem B8363969 : Blo 511796 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B1155023 : Blo 511796 1155023 := bstep (se 1 (by rfl) ⟨866267, by rfl⟩ : syracuseStep 1155023 = 1732535) B1732535
theorem B3285011 : Blo 511796 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B3711095 : Blo 511796 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B1155401 : Blo 511796 1155401 := bstep (se 2 (by rfl) ⟨433275, by rfl⟩ : syracuseStep 1155401 = 866551) B866551
theorem B1155419 : Blo 511796 1155419 := bstep (se 1 (by rfl) ⟨866564, by rfl⟩ : syracuseStep 1155419 = 1733129) B1733129
theorem B2597345 : Blo 511796 2597345 := bstep (se 2 (by rfl) ⟨974004, by rfl⟩ : syracuseStep 2597345 = 1948009) B1948009
theorem B8430227 : Blo 511796 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B926383 : Blo 511796 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B3908411 : Blo 511796 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B1155995 : Blo 511796 1155995 := bstep (se 1 (by rfl) ⟨866996, by rfl⟩ : syracuseStep 1155995 = 1733993) B1733993
theorem B926635 : Blo 511796 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B1156193 : Blo 511796 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B1156391 : Blo 511796 1156391 := bstep (se 1 (by rfl) ⟨867293, by rfl⟩ : syracuseStep 1156391 = 1734587) B1734587
theorem B1156769 : Blo 511796 1156769 := bstep (se 2 (by rfl) ⟨433788, by rfl⟩ : syracuseStep 1156769 = 867577) B867577
theorem B1157129 : Blo 511796 1157129 := bstep (se 2 (by rfl) ⟨433923, by rfl⟩ : syracuseStep 1157129 = 867847) B867847
theorem B4401337 : Blo 511796 4401337 := bstep (se 2 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 4401337 = 3301003) B3301003
theorem B2369801 : Blo 511796 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B1255771 : Blo 511796 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B1157543 : Blo 511796 1157543 := bstep (se 1 (by rfl) ⟨868157, by rfl⟩ : syracuseStep 1157543 = 1736315) B1736315
theorem B1157651 : Blo 511796 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B731711 : Blo 511796 731711 := bstep (se 1 (by rfl) ⟨548783, by rfl⟩ : syracuseStep 731711 = 1097567) B1097567
theorem B1157705 : Blo 511796 1157705 := bstep (se 2 (by rfl) ⟨434139, by rfl⟩ : syracuseStep 1157705 = 868279) B868279
theorem B2599613 : Blo 511796 2599613 := bstep (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) B974855
theorem B1158119 : Blo 511796 1158119 := bstep (se 1 (by rfl) ⟨868589, by rfl⟩ : syracuseStep 1158119 = 1737179) B1737179
theorem B1977331 : Blo 511796 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B1322183 : Blo 511796 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1158497 : Blo 511796 1158497 := bstep (se 2 (by rfl) ⟨434436, by rfl⟩ : syracuseStep 1158497 = 868873) B868873
theorem B16035191 : Blo 511796 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B1158587 : Blo 511796 1158587 := bstep (se 1 (by rfl) ⟨868940, by rfl⟩ : syracuseStep 1158587 = 1737881) B1737881
theorem B1158713 : Blo 511796 1158713 := bstep (se 2 (by rfl) ⟨434517, by rfl⟩ : syracuseStep 1158713 = 869035) B869035
theorem B7384769 : Blo 511796 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B4927175 : Blo 511796 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B864047 : Blo 511796 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B1159379 : Blo 511796 1159379 := bstep (se 1 (by rfl) ⟨869534, by rfl⟩ : syracuseStep 1159379 = 1739069) B1739069
theorem B1159433 : Blo 511796 1159433 := bstep (se 2 (by rfl) ⟨434787, by rfl⟩ : syracuseStep 1159433 = 869575) B869575
theorem B1323289 : Blo 511796 1323289 := bstep (se 2 (by rfl) ⟨496233, by rfl⟩ : syracuseStep 1323289 = 992467) B992467
theorem B1093979 : Blo 511796 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B1159649 : Blo 511796 1159649 := bstep (se 2 (by rfl) ⟨434868, by rfl⟩ : syracuseStep 1159649 = 869737) B869737
theorem B1847879 : Blo 511796 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1159955 : Blo 511796 1159955 := bstep (se 1 (by rfl) ⟨869966, by rfl⟩ : syracuseStep 1159955 = 1739933) B1739933
theorem B1094543 : Blo 511796 1094543 := bstep (se 1 (by rfl) ⟨820907, by rfl⟩ : syracuseStep 1094543 = 1641815) B1641815
theorem B2864065 : Blo 511796 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B865255 : Blo 511796 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B40121335 : Blo 511796 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B1160315 : Blo 511796 1160315 := bstep (se 1 (by rfl) ⟨870236, by rfl⟩ : syracuseStep 1160315 = 1740473) B1740473
theorem B1160441 : Blo 511796 1160441 := bstep (se 2 (by rfl) ⟨435165, by rfl⟩ : syracuseStep 1160441 = 870331) B870331
theorem B2471431 : Blo 511796 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B2602529 : Blo 511796 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B767723 : Blo 511796 767723 := bstep (se 1 (by rfl) ⟨575792, by rfl⟩ : syracuseStep 767723 = 1151585) B1151585
theorem B767951 : Blo 511796 767951 := bstep (se 1 (by rfl) ⟨575963, by rfl⟩ : syracuseStep 767951 = 1151927) B1151927
theorem B768347 : Blo 511796 768347 := bstep (se 1 (by rfl) ⟨576260, by rfl⟩ : syracuseStep 768347 = 1152521) B1152521
theorem B13187609 : Blo 511796 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B768575 : Blo 511796 768575 := bstep (se 1 (by rfl) ⟨576431, by rfl⟩ : syracuseStep 768575 = 1152863) B1152863
theorem B768695 : Blo 511796 768695 := bstep (se 1 (by rfl) ⟨576521, by rfl⟩ : syracuseStep 768695 = 1153043) B1153043
theorem B2079479 : Blo 511796 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B768923 : Blo 511796 768923 := bstep (se 1 (by rfl) ⟨576692, by rfl⟩ : syracuseStep 768923 = 1153385) B1153385
theorem B1096679 : Blo 511796 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B7388279 : Blo 511796 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B769319 : Blo 511796 769319 := bstep (se 1 (by rfl) ⟨576989, by rfl⟩ : syracuseStep 769319 = 1153979) B1153979
theorem B769403 : Blo 511796 769403 := bstep (se 1 (by rfl) ⟨577052, by rfl⟩ : syracuseStep 769403 = 1154105) B1154105
theorem B769529 : Blo 511796 769529 := bstep (se 2 (by rfl) ⟨288573, by rfl⟩ : syracuseStep 769529 = 577147) B577147
theorem B5291513 : Blo 511796 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B2473487 : Blo 511796 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B769631 : Blo 511796 769631 := bstep (se 1 (by rfl) ⟨577223, by rfl⟩ : syracuseStep 769631 = 1154447) B1154447
theorem B867935 : Blo 511796 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B1392223 : Blo 511796 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B5259001 : Blo 511796 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B769847 : Blo 511796 769847 := bstep (se 1 (by rfl) ⟨577385, by rfl⟩ : syracuseStep 769847 = 1154771) B1154771
theorem B868151 : Blo 511796 868151 := bstep (se 1 (by rfl) ⟨651113, by rfl⟩ : syracuseStep 868151 = 1302227) B1302227
theorem B5554183 : Blo 511796 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B770153 : Blo 511796 770153 := bstep (se 2 (by rfl) ⟨288807, by rfl⟩ : syracuseStep 770153 = 577615) B577615
theorem B770471 : Blo 511796 770471 := bstep (se 1 (by rfl) ⟨577853, by rfl⟩ : syracuseStep 770471 = 1155707) B1155707
theorem B770555 : Blo 511796 770555 := bstep (se 1 (by rfl) ⟨577916, by rfl⟩ : syracuseStep 770555 = 1155833) B1155833
theorem B1950227 : Blo 511796 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B868927 : Blo 511796 868927 := bstep (se 1 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 868927 = 1303391) B1303391
theorem B1098319 : Blo 511796 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B770681 : Blo 511796 770681 := bstep (se 2 (by rfl) ⟨289005, by rfl⟩ : syracuseStep 770681 = 578011) B578011
theorem B770735 : Blo 511796 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B1458911 : Blo 511796 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B770783 : Blo 511796 770783 := bstep (se 1 (by rfl) ⟨578087, by rfl⟩ : syracuseStep 770783 = 1156175) B1156175
theorem B3293945 : Blo 511796 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B1426331 : Blo 511796 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B771047 : Blo 511796 771047 := bstep (se 1 (by rfl) ⟨578285, by rfl⟩ : syracuseStep 771047 = 1156571) B1156571
theorem B3294215 : Blo 511796 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B1557737 : Blo 511796 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B771305 : Blo 511796 771305 := bstep (se 2 (by rfl) ⟨289239, by rfl⟩ : syracuseStep 771305 = 578479) B578479
theorem B869609 : Blo 511796 869609 := bstep (se 2 (by rfl) ⟨326103, by rfl⟩ : syracuseStep 869609 = 652207) B652207
theorem B771359 : Blo 511796 771359 := bstep (se 1 (by rfl) ⟨578519, by rfl⟩ : syracuseStep 771359 = 1157039) B1157039
theorem B869663 : Blo 511796 869663 := bstep (se 1 (by rfl) ⟨652247, by rfl⟩ : syracuseStep 869663 = 1304495) B1304495
theorem B1459595 : Blo 511796 1459595 := bstep (se 1 (by rfl) ⟨1094696, by rfl⟩ : syracuseStep 1459595 = 2189393) B2189393
theorem B1295777 : Blo 511796 1295777 := bstep (se 2 (by rfl) ⟨485916, by rfl⟩ : syracuseStep 1295777 = 971833) B971833
theorem B771527 : Blo 511796 771527 := bstep (se 1 (by rfl) ⟨578645, by rfl⟩ : syracuseStep 771527 = 1157291) B1157291
theorem B1099207 : Blo 511796 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B15058385 : Blo 511796 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B4376051 : Blo 511796 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B2934407 : Blo 511796 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2475677 : Blo 511796 2475677 := bstep (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) B928379
theorem B771881 : Blo 511796 771881 := bstep (se 2 (by rfl) ⟨289455, by rfl⟩ : syracuseStep 771881 = 578911) B578911
theorem B771887 : Blo 511796 771887 := bstep (se 1 (by rfl) ⟨578915, by rfl⟩ : syracuseStep 771887 = 1157831) B1157831
theorem B2606903 : Blo 511796 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B1296233 : Blo 511796 1296233 := bstep (se 2 (by rfl) ⟨486087, by rfl⟩ : syracuseStep 1296233 = 972175) B972175
theorem B1230977 : Blo 511796 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B3950777 : Blo 511796 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B772361 : Blo 511796 772361 := bstep (se 2 (by rfl) ⟨289635, by rfl⟩ : syracuseStep 772361 = 579271) B579271
theorem B2607389 : Blo 511796 2607389 := bstep (se 3 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 2607389 = 977771) B977771
theorem B772463 : Blo 511796 772463 := bstep (se 1 (by rfl) ⟨579347, by rfl⟩ : syracuseStep 772463 = 1158695) B1158695
theorem B575995 : Blo 511796 575995 := bstep (se 1 (by rfl) ⟨431996, by rfl⟩ : syracuseStep 575995 = 863993) B863993
theorem B772679 : Blo 511796 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B772715 : Blo 511796 772715 := bstep (se 1 (by rfl) ⟨579536, by rfl⟩ : syracuseStep 772715 = 1159073) B1159073
theorem B1100395 : Blo 511796 1100395 := bstep (se 1 (by rfl) ⟨825296, by rfl⟩ : syracuseStep 1100395 = 1650593) B1650593
theorem B576175 : Blo 511796 576175 := bstep (se 1 (by rfl) ⟨432131, by rfl⟩ : syracuseStep 576175 = 864263) B864263
theorem B1100471 : Blo 511796 1100471 := bstep (se 1 (by rfl) ⟨825353, by rfl⟩ : syracuseStep 1100471 = 1650707) B1650707
theorem B772943 : Blo 511796 772943 := bstep (se 1 (by rfl) ⟨579707, by rfl⟩ : syracuseStep 772943 = 1159415) B1159415
theorem B3689387 : Blo 511796 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B576463 : Blo 511796 576463 := bstep (se 1 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 576463 = 864695) B864695
theorem B1461235 : Blo 511796 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B1854451 : Blo 511796 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B2477137 : Blo 511796 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B1854683 : Blo 511796 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B773339 : Blo 511796 773339 := bstep (se 1 (by rfl) ⟨580004, by rfl⟩ : syracuseStep 773339 = 1160009) B1160009
theorem B576859 : Blo 511796 576859 := bstep (se 1 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 576859 = 865289) B865289
theorem B1953143 : Blo 511796 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B773513 : Blo 511796 773513 := bstep (se 2 (by rfl) ⟨290067, by rfl⟩ : syracuseStep 773513 = 580135) B580135
theorem B3296699 : Blo 511796 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B576967 : Blo 511796 576967 := bstep (se 1 (by rfl) ⟨432725, by rfl⟩ : syracuseStep 576967 = 865451) B865451
theorem B2674201 : Blo 511796 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B1298015 : Blo 511796 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B14077651 : Blo 511796 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B7884557 : Blo 511796 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B577327 : Blo 511796 577327 := bstep (se 1 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 577327 = 865991) B865991
theorem B511899 : Blo 511796 511899 := bstep (se 1 (by rfl) ⟨383924, by rfl⟩ : syracuseStep 511899 = 767849) B767849
theorem B577435 : Blo 511796 577435 := bstep (se 1 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 577435 = 866153) B866153
theorem B511951 : Blo 511796 511951 := bstep (se 1 (by rfl) ⟨383963, by rfl⟩ : syracuseStep 511951 = 767927) B767927
theorem B511975 : Blo 511796 511975 := bstep (se 1 (by rfl) ⟨383981, by rfl⟩ : syracuseStep 511975 = 767963) B767963
theorem B2609171 : Blo 511796 2609171 := bstep (se 1 (by rfl) ⟨1956878, by rfl⟩ : syracuseStep 2609171 = 3913757) B3913757
theorem B10670339 : Blo 511796 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B1298713 : Blo 511796 1298713 := bstep (se 2 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 1298713 = 974035) B974035
theorem B512287 : Blo 511796 512287 := bstep (se 1 (by rfl) ⟨384215, by rfl⟩ : syracuseStep 512287 = 768431) B768431
theorem B577831 : Blo 511796 577831 := bstep (se 1 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 577831 = 866747) B866747
theorem B512347 : Blo 511796 512347 := bstep (se 1 (by rfl) ⟨384260, by rfl⟩ : syracuseStep 512347 = 768521) B768521
theorem B512367 : Blo 511796 512367 := bstep (se 1 (by rfl) ⟨384275, by rfl⟩ : syracuseStep 512367 = 768551) B768551
theorem B1233263 : Blo 511796 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B577903 : Blo 511796 577903 := bstep (se 1 (by rfl) ⟨433427, by rfl⟩ : syracuseStep 577903 = 866855) B866855
theorem B512423 : Blo 511796 512423 := bstep (se 1 (by rfl) ⟨384317, by rfl⟩ : syracuseStep 512423 = 768635) B768635
theorem B1298855 : Blo 511796 1298855 := bstep (se 1 (by rfl) ⟨974141, by rfl⟩ : syracuseStep 1298855 = 1948283) B1948283
theorem B512507 : Blo 511796 512507 := bstep (se 1 (by rfl) ⟨384380, by rfl⟩ : syracuseStep 512507 = 768761) B768761
theorem B512575 : Blo 511796 512575 := bstep (se 1 (by rfl) ⟨384431, by rfl⟩ : syracuseStep 512575 = 768863) B768863
theorem B512583 : Blo 511796 512583 := bstep (se 1 (by rfl) ⟨384437, by rfl⟩ : syracuseStep 512583 = 768875) B768875
theorem B578119 : Blo 511796 578119 := bstep (se 1 (by rfl) ⟨433589, by rfl⟩ : syracuseStep 578119 = 867179) B867179
theorem B1299017 : Blo 511796 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B1462967 : Blo 511796 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B512735 : Blo 511796 512735 := bstep (se 1 (by rfl) ⟨384551, by rfl⟩ : syracuseStep 512735 = 769103) B769103
theorem B10572511 : Blo 511796 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B512815 : Blo 511796 512815 := bstep (se 1 (by rfl) ⟨384611, by rfl⟩ : syracuseStep 512815 = 769223) B769223
theorem B512923 : Blo 511796 512923 := bstep (se 1 (by rfl) ⟨384692, by rfl⟩ : syracuseStep 512923 = 769385) B769385
theorem B512975 : Blo 511796 512975 := bstep (se 1 (by rfl) ⟨384731, by rfl⟩ : syracuseStep 512975 = 769463) B769463
theorem B512999 : Blo 511796 512999 := bstep (se 1 (by rfl) ⟨384749, by rfl⟩ : syracuseStep 512999 = 769499) B769499
theorem B23712787 : Blo 511796 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B3691777 : Blo 511796 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B513311 : Blo 511796 513311 := bstep (se 1 (by rfl) ⟨384983, by rfl⟩ : syracuseStep 513311 = 769967) B769967
theorem B513371 : Blo 511796 513371 := bstep (se 1 (by rfl) ⟨385028, by rfl⟩ : syracuseStep 513371 = 770057) B770057
theorem B513391 : Blo 511796 513391 := bstep (se 1 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 513391 = 770087) B770087
theorem B1562017 : Blo 511796 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B513447 : Blo 511796 513447 := bstep (se 1 (by rfl) ⟨385085, by rfl⟩ : syracuseStep 513447 = 770171) B770171
theorem B578983 : Blo 511796 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B1463741 : Blo 511796 1463741 := bstep (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) B548903
theorem B513531 : Blo 511796 513531 := bstep (se 1 (by rfl) ⟨385148, by rfl⟩ : syracuseStep 513531 = 770297) B770297
theorem B513599 : Blo 511796 513599 := bstep (se 1 (by rfl) ⟨385199, by rfl⟩ : syracuseStep 513599 = 770399) B770399
theorem B11392579 : Blo 511796 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B513607 : Blo 511796 513607 := bstep (se 1 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 513607 = 770411) B770411
theorem B513759 : Blo 511796 513759 := bstep (se 1 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 513759 = 770639) B770639
theorem B513839 : Blo 511796 513839 := bstep (se 1 (by rfl) ⟨385379, by rfl⟩ : syracuseStep 513839 = 770759) B770759
theorem B513947 : Blo 511796 513947 := bstep (se 1 (by rfl) ⟨385460, by rfl⟩ : syracuseStep 513947 = 770921) B770921
theorem B513999 : Blo 511796 513999 := bstep (se 1 (by rfl) ⟨385499, by rfl⟩ : syracuseStep 513999 = 770999) B770999
theorem B514023 : Blo 511796 514023 := bstep (se 1 (by rfl) ⟨385517, by rfl⟩ : syracuseStep 514023 = 771035) B771035
theorem B579559 : Blo 511796 579559 := bstep (se 1 (by rfl) ⟨434669, by rfl⟩ : syracuseStep 579559 = 869339) B869339
theorem B2775235 : Blo 511796 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B1235225 : Blo 511796 1235225 := bstep (se 2 (by rfl) ⟨463209, by rfl⟩ : syracuseStep 1235225 = 926419) B926419
theorem B514335 : Blo 511796 514335 := bstep (se 1 (by rfl) ⟨385751, by rfl⟩ : syracuseStep 514335 = 771503) B771503
theorem B973147 : Blo 511796 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B514395 : Blo 511796 514395 := bstep (se 1 (by rfl) ⟨385796, by rfl⟩ : syracuseStep 514395 = 771593) B771593
theorem B514415 : Blo 511796 514415 := bstep (se 1 (by rfl) ⟨385811, by rfl⟩ : syracuseStep 514415 = 771623) B771623
theorem B1464743 : Blo 511796 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B514471 : Blo 511796 514471 := bstep (se 1 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 514471 = 771707) B771707
theorem B1300961 : Blo 511796 1300961 := bstep (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) B975721
theorem B514555 : Blo 511796 514555 := bstep (se 1 (by rfl) ⟨385916, by rfl⟩ : syracuseStep 514555 = 771833) B771833
theorem B514623 : Blo 511796 514623 := bstep (se 1 (by rfl) ⟨385967, by rfl⟩ : syracuseStep 514623 = 771935) B771935
theorem B514631 : Blo 511796 514631 := bstep (se 1 (by rfl) ⟨385973, by rfl⟩ : syracuseStep 514631 = 771947) B771947
theorem B514783 : Blo 511796 514783 := bstep (se 1 (by rfl) ⟨386087, by rfl⟩ : syracuseStep 514783 = 772175) B772175
theorem B514863 : Blo 511796 514863 := bstep (se 1 (by rfl) ⟨386147, by rfl⟩ : syracuseStep 514863 = 772295) B772295
theorem B514971 : Blo 511796 514971 := bstep (se 1 (by rfl) ⟨386228, by rfl⟩ : syracuseStep 514971 = 772457) B772457
theorem B3955643 : Blo 511796 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B515023 : Blo 511796 515023 := bstep (se 1 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 515023 = 772535) B772535
theorem B1301467 : Blo 511796 1301467 := bstep (se 1 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 1301467 = 1952201) B1952201
theorem B515047 : Blo 511796 515047 := bstep (se 1 (by rfl) ⟨386285, by rfl⟩ : syracuseStep 515047 = 772571) B772571
theorem B183196853 : Blo 511796 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B1301791 : Blo 511796 1301791 := bstep (se 1 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 1301791 = 1952687) B1952687
theorem B515359 : Blo 511796 515359 := bstep (se 1 (by rfl) ⟨386519, by rfl⟩ : syracuseStep 515359 = 773039) B773039
theorem B974119 : Blo 511796 974119 := bstep (se 1 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 974119 = 1461179) B1461179
theorem B515419 : Blo 511796 515419 := bstep (se 1 (by rfl) ⟨386564, by rfl⟩ : syracuseStep 515419 = 773129) B773129
theorem B515439 : Blo 511796 515439 := bstep (se 1 (by rfl) ⟨386579, by rfl⟩ : syracuseStep 515439 = 773159) B773159
theorem B515495 : Blo 511796 515495 := bstep (se 1 (by rfl) ⟨386621, by rfl⟩ : syracuseStep 515495 = 773243) B773243
theorem B1170875 : Blo 511796 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B65068505 : Blo 511796 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B4382201 : Blo 511796 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B515579 : Blo 511796 515579 := bstep (se 1 (by rfl) ⟨386684, by rfl⟩ : syracuseStep 515579 = 773369) B773369
theorem B515647 : Blo 511796 515647 := bstep (se 1 (by rfl) ⟨386735, by rfl⟩ : syracuseStep 515647 = 773471) B773471
theorem B515655 : Blo 511796 515655 := bstep (se 1 (by rfl) ⟨386741, by rfl⟩ : syracuseStep 515655 = 773483) B773483
theorem B1465951 : Blo 511796 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B1728161 : Blo 511796 1728161 := bstep (se 2 (by rfl) ⟨648060, by rfl⟩ : syracuseStep 1728161 = 1296121) B1296121
theorem B2187137 : Blo 511796 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B5693651 : Blo 511796 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1302875 : Blo 511796 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B1237415 : Blo 511796 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B1729025 : Blo 511796 1729025 := bstep (se 2 (by rfl) ⟨648384, by rfl⟩ : syracuseStep 1729025 = 1296769) B1296769
theorem B2351713 : Blo 511796 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B2646827 : Blo 511796 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B648091 : Blo 511796 648091 := bstep (se 1 (by rfl) ⟨486068, by rfl⟩ : syracuseStep 648091 = 972137) B972137
theorem B1729511 : Blo 511796 1729511 := bstep (se 1 (by rfl) ⟨1297133, by rfl⟩ : syracuseStep 1729511 = 2594267) B2594267
theorem B4383841 : Blo 511796 4383841 := bstep (se 2 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 4383841 = 3287881) B3287881
theorem B31745125 : Blo 511796 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1303847 : Blo 511796 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1729835 : Blo 511796 1729835 := bstep (se 1 (by rfl) ⟨1297376, by rfl⟩ : syracuseStep 1729835 = 2594753) B2594753
theorem B1730105 : Blo 511796 1730105 := bstep (se 2 (by rfl) ⟨648789, by rfl⟩ : syracuseStep 1730105 = 1297579) B1297579
theorem B550471 : Blo 511796 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B780079 : Blo 511796 780079 := bstep (se 1 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 780079 = 1170119) B1170119
theorem B2222113 : Blo 511796 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B2779559 : Blo 511796 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B1305335 : Blo 511796 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1731347 : Blo 511796 1731347 := bstep (se 1 (by rfl) ⟨1298510, by rfl⟩ : syracuseStep 1731347 = 2597021) B2597021
theorem B650587 : Blo 511796 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B1732211 : Blo 511796 1732211 := bstep (se 1 (by rfl) ⟨1299158, by rfl⟩ : syracuseStep 1732211 = 2598317) B2598317
theorem B1044265 : Blo 511796 1044265 := bstep (se 2 (by rfl) ⟨391599, by rfl⟩ : syracuseStep 1044265 = 783199) B783199
theorem B618295 : Blo 511796 618295 := bstep (se 1 (by rfl) ⟨463721, by rfl⟩ : syracuseStep 618295 = 927443) B927443
theorem B978743 : Blo 511796 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B1732481 : Blo 511796 1732481 := bstep (se 2 (by rfl) ⟨649680, by rfl⟩ : syracuseStep 1732481 = 1299361) B1299361
theorem B978895 : Blo 511796 978895 := bstep (se 1 (by rfl) ⟨734171, by rfl⟩ : syracuseStep 978895 = 1468343) B1468343
theorem B4157405 : Blo 511796 4157405 := bstep (se 3 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 4157405 = 1559027) B1559027
theorem B651559 : Blo 511796 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B651883 : Blo 511796 651883 := bstep (se 1 (by rfl) ⟨488912, by rfl⟩ : syracuseStep 651883 = 977825) B977825
theorem B1733291 : Blo 511796 1733291 := bstep (se 1 (by rfl) ⟨1299968, by rfl⟩ : syracuseStep 1733291 = 2599937) B2599937
theorem B1733831 : Blo 511796 1733831 := bstep (se 1 (by rfl) ⟨1300373, by rfl⟩ : syracuseStep 1733831 = 2600747) B2600747
theorem B18741293 : Blo 511796 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B5864075 : Blo 511796 5864075 := bstep (se 1 (by rfl) ⟨4398056, by rfl⟩ : syracuseStep 5864075 = 8796113) B8796113
theorem B4389551 : Blo 511796 4389551 := bstep (se 1 (by rfl) ⟨3292163, by rfl⟩ : syracuseStep 4389551 = 6584327) B6584327
theorem B1735343 : Blo 511796 1735343 := bstep (se 1 (by rfl) ⟨1301507, by rfl⟩ : syracuseStep 1735343 = 2603015) B2603015
theorem B1735667 : Blo 511796 1735667 := bstep (se 1 (by rfl) ⟨1301750, by rfl⟩ : syracuseStep 1735667 = 2603501) B2603501
theorem B9993239 : Blo 511796 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B3898691 : Blo 511796 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B1736207 : Blo 511796 1736207 := bstep (se 1 (by rfl) ⟨1302155, by rfl⟩ : syracuseStep 1736207 = 2604311) B2604311
theorem B3899177 : Blo 511796 3899177 := bstep (se 2 (by rfl) ⟨1462191, by rfl⟩ : syracuseStep 3899177 = 2924383) B2924383
theorem B7405577 : Blo 511796 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B2195963 : Blo 511796 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B950887 : Blo 511796 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B2196143 : Blo 511796 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B2917367 : Blo 511796 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B1737935 : Blo 511796 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B1738259 : Blo 511796 1738259 := bstep (se 1 (by rfl) ⟨1303694, by rfl⟩ : syracuseStep 1738259 = 2607389) B2607389
theorem B2459591 : Blo 511796 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B2197799 : Blo 511796 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B5572955 : Blo 511796 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B10029719 : Blo 511796 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1739447 : Blo 511796 1739447 := bstep (se 1 (by rfl) ⟨1304585, by rfl⟩ : syracuseStep 1739447 = 2609171) B2609171
theorem B5868449 : Blo 511796 5868449 := bstep (se 2 (by rfl) ⟨2200668, by rfl⟩ : syracuseStep 5868449 = 4401337) B4401337
theorem B1674361 : Blo 511796 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B823483 : Blo 511796 823483 := bstep (se 1 (by rfl) ⟨617612, by rfl⟩ : syracuseStep 823483 = 1235225) B1235225
theorem B122131235 : Blo 511796 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B2921467 : Blo 511796 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B824393 : Blo 511796 824393 := bstep (se 2 (by rfl) ⟨309147, by rfl⟩ : syracuseStep 824393 = 618295) B618295
theorem B1152107 : Blo 511796 1152107 := bstep (se 1 (by rfl) ⟨864080, by rfl⟩ : syracuseStep 1152107 = 1728161) B1728161
theorem B5575979 : Blo 511796 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B1152683 : Blo 511796 1152683 := bstep (se 1 (by rfl) ⟨864512, by rfl⟩ : syracuseStep 1152683 = 1729025) B1729025
theorem B3282605 : Blo 511796 3282605 := bstep (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) B1230977
theorem B1153007 : Blo 511796 1153007 := bstep (se 1 (by rfl) ⟨864755, by rfl⟩ : syracuseStep 1153007 = 1729511) B1729511
theorem B1153223 : Blo 511796 1153223 := bstep (se 1 (by rfl) ⟨864917, by rfl⟩ : syracuseStep 1153223 = 1729835) B1729835
theorem B14096681 : Blo 511796 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B1153403 : Blo 511796 1153403 := bstep (se 1 (by rfl) ⟨865052, by rfl⟩ : syracuseStep 1153403 = 1730105) B1730105
theorem B3905981 : Blo 511796 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B4921829 : Blo 511796 4921829 := bstep (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) B922843
theorem B3283577 : Blo 511796 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B1153673 : Blo 511796 1153673 := bstep (se 2 (by rfl) ⟨432627, by rfl⟩ : syracuseStep 1153673 = 865255) B865255
theorem B1579867 : Blo 511796 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B2104265 : Blo 511796 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B4922369 : Blo 511796 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B1154231 : Blo 511796 1154231 := bstep (se 1 (by rfl) ⟨865673, by rfl⟩ : syracuseStep 1154231 = 1731347) B1731347
theorem B10690127 : Blo 511796 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B925409 : Blo 511796 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B1154807 : Blo 511796 1154807 := bstep (se 1 (by rfl) ⟨866105, by rfl⟩ : syracuseStep 1154807 = 1732211) B1732211
theorem B4923179 : Blo 511796 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B3284783 : Blo 511796 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B1154987 : Blo 511796 1154987 := bstep (se 1 (by rfl) ⟨866240, by rfl⟩ : syracuseStep 1154987 = 1732481) B1732481
theorem B729319 : Blo 511796 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B1155527 : Blo 511796 1155527 := bstep (se 1 (by rfl) ⟨866645, by rfl⟩ : syracuseStep 1155527 = 1733291) B1733291
theorem B729695 : Blo 511796 729695 := bstep (se 1 (by rfl) ⟨547271, by rfl⟩ : syracuseStep 729695 = 1094543) B1094543
theorem B2466413 : Blo 511796 2466413 := bstep (se 3 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 2466413 = 924905) B924905
theorem B1155887 : Blo 511796 1155887 := bstep (se 1 (by rfl) ⟨866915, by rfl⟩ : syracuseStep 1155887 = 1733831) B1733831
theorem B3122333 : Blo 511796 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B12494195 : Blo 511796 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B8791739 : Blo 511796 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B3909383 : Blo 511796 3909383 := bstep (se 1 (by rfl) ⟨2932037, by rfl⟩ : syracuseStep 3909383 = 5864075) B5864075
theorem B2926367 : Blo 511796 2926367 := bstep (se 1 (by rfl) ⟨2194775, by rfl⟩ : syracuseStep 2926367 = 4389551) B4389551
theorem B1156895 : Blo 511796 1156895 := bstep (se 1 (by rfl) ⟨867671, by rfl⟩ : syracuseStep 1156895 = 1735343) B1735343
theorem B1386319 : Blo 511796 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B731119 : Blo 511796 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B1157111 : Blo 511796 1157111 := bstep (se 1 (by rfl) ⟨867833, by rfl⟩ : syracuseStep 1157111 = 1735667) B1735667
theorem B6662159 : Blo 511796 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B4925519 : Blo 511796 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B2599127 : Blo 511796 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B1157471 : Blo 511796 1157471 := bstep (se 1 (by rfl) ⟨868103, by rfl⟩ : syracuseStep 1157471 = 1736207) B1736207
theorem B1648991 : Blo 511796 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B2599451 : Blo 511796 2599451 := bstep (se 1 (by rfl) ⟨1949588, by rfl⟩ : syracuseStep 2599451 = 3899177) B3899177
theorem B2927299 : Blo 511796 2927299 := bstep (se 1 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 2927299 = 4390949) B4390949
theorem B6597449 : Blo 511796 6597449 := bstep (se 2 (by rfl) ⟨2474043, by rfl⟩ : syracuseStep 6597449 = 4948087) B4948087
theorem B1158191 : Blo 511796 1158191 := bstep (se 1 (by rfl) ⟨868643, by rfl⟩ : syracuseStep 1158191 = 1737287) B1737287
theorem B1158479 : Blo 511796 1158479 := bstep (se 1 (by rfl) ⟨868859, by rfl⟩ : syracuseStep 1158479 = 1737719) B1737719
theorem B28454237 : Blo 511796 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B1158569 : Blo 511796 1158569 := bstep (se 2 (by rfl) ⟨434463, by rfl⟩ : syracuseStep 1158569 = 868927) B868927
theorem B1945079 : Blo 511796 1945079 := bstep (se 1 (by rfl) ⟨1458809, by rfl⟩ : syracuseStep 1945079 = 2917619) B2917619
theorem B1093193 : Blo 511796 1093193 := bstep (se 2 (by rfl) ⟨409947, by rfl⟩ : syracuseStep 1093193 = 819895) B819895
theorem B863851 : Blo 511796 863851 := bstep (se 1 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 863851 = 1295777) B1295777
theorem B3288701 : Blo 511796 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B10038923 : Blo 511796 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B1093295 : Blo 511796 1093295 := bstep (se 1 (by rfl) ⟨819971, by rfl⟩ : syracuseStep 1093295 = 1639943) B1639943
theorem B1650451 : Blo 511796 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B864121 : Blo 511796 864121 := bstep (se 2 (by rfl) ⟨324045, by rfl⟩ : syracuseStep 864121 = 648091) B648091
theorem B1159055 : Blo 511796 1159055 := bstep (se 1 (by rfl) ⟨869291, by rfl⟩ : syracuseStep 1159055 = 1738583) B1738583
theorem B864155 : Blo 511796 864155 := bstep (se 1 (by rfl) ⟨648116, by rfl⟩ : syracuseStep 864155 = 1296233) B1296233
theorem B2633851 : Blo 511796 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B5845121 : Blo 511796 5845121 := bstep (se 2 (by rfl) ⟨2191920, by rfl⟩ : syracuseStep 5845121 = 4383841) B4383841
theorem B1159775 : Blo 511796 1159775 := bstep (se 1 (by rfl) ⟨869831, by rfl⟩ : syracuseStep 1159775 = 1739663) B1739663
theorem B2601719 : Blo 511796 2601719 := bstep (se 1 (by rfl) ⟨1951289, by rfl⟩ : syracuseStep 2601719 = 3902579) B3902579
theorem B733961 : Blo 511796 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1487641 : Blo 511796 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B865343 : Blo 511796 865343 := bstep (se 1 (by rfl) ⟨649007, by rfl⟩ : syracuseStep 865343 = 1298015) B1298015
theorem B5256371 : Blo 511796 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B2962817 : Blo 511796 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B865903 : Blo 511796 865903 := bstep (se 1 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 865903 = 1298855) B1298855
theorem B866011 : Blo 511796 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B767711 : Blo 511796 767711 := bstep (se 1 (by rfl) ⟨575783, by rfl⟩ : syracuseStep 767711 = 1151567) B1151567
theorem B767807 : Blo 511796 767807 := bstep (se 1 (by rfl) ⟨575855, by rfl⟩ : syracuseStep 767807 = 1151711) B1151711
theorem B767975 : Blo 511796 767975 := bstep (se 1 (by rfl) ⟨575981, by rfl⟩ : syracuseStep 767975 = 1151963) B1151963
theorem B767993 : Blo 511796 767993 := bstep (se 2 (by rfl) ⟨287997, by rfl⟩ : syracuseStep 767993 = 575995) B575995
theorem B768095 : Blo 511796 768095 := bstep (se 1 (by rfl) ⟨576071, by rfl⟩ : syracuseStep 768095 = 1152143) B1152143
theorem B768155 : Blo 511796 768155 := bstep (se 1 (by rfl) ⟨576116, by rfl⟩ : syracuseStep 768155 = 1152233) B1152233
theorem B768191 : Blo 511796 768191 := bstep (se 1 (by rfl) ⟨576143, by rfl⟩ : syracuseStep 768191 = 1152287) B1152287
theorem B768233 : Blo 511796 768233 := bstep (se 2 (by rfl) ⟨288087, by rfl⟩ : syracuseStep 768233 = 576175) B576175
theorem B768539 : Blo 511796 768539 := bstep (se 1 (by rfl) ⟨576404, by rfl⟩ : syracuseStep 768539 = 1152809) B1152809
theorem B768617 : Blo 511796 768617 := bstep (se 2 (by rfl) ⟨288231, by rfl⟩ : syracuseStep 768617 = 576463) B576463
theorem B1948313 : Blo 511796 1948313 := bstep (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) B1461235
theorem B2636441 : Blo 511796 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B2472601 : Blo 511796 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B1948495 : Blo 511796 1948495 := bstep (se 1 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 1948495 = 2922743) B2922743
theorem B867307 : Blo 511796 867307 := bstep (se 1 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 867307 = 1300961) B1300961
theorem B769145 : Blo 511796 769145 := bstep (se 2 (by rfl) ⟨288429, by rfl⟩ : syracuseStep 769145 = 576859) B576859
theorem B867449 : Blo 511796 867449 := bstep (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) B650587
theorem B769247 : Blo 511796 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B769289 : Blo 511796 769289 := bstep (se 2 (by rfl) ⟨288483, by rfl⟩ : syracuseStep 769289 = 576967) B576967
theorem B1948967 : Blo 511796 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B2637095 : Blo 511796 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B769391 : Blo 511796 769391 := bstep (se 1 (by rfl) ⟨577043, by rfl⟩ : syracuseStep 769391 = 1154087) B1154087
theorem B769511 : Blo 511796 769511 := bstep (se 1 (by rfl) ⟨577133, by rfl⟩ : syracuseStep 769511 = 1154267) B1154267
theorem B2604635 : Blo 511796 2604635 := bstep (se 1 (by rfl) ⟨1953476, by rfl⟩ : syracuseStep 2604635 = 3906953) B3906953
theorem B769643 : Blo 511796 769643 := bstep (se 1 (by rfl) ⟨577232, by rfl⟩ : syracuseStep 769643 = 1154465) B1154465
theorem B1392353 : Blo 511796 1392353 := bstep (se 2 (by rfl) ⟨522132, by rfl⟩ : syracuseStep 1392353 = 1044265) B1044265
theorem B769769 : Blo 511796 769769 := bstep (se 2 (by rfl) ⟨288663, by rfl⟩ : syracuseStep 769769 = 577327) B577327
theorem B769913 : Blo 511796 769913 := bstep (se 2 (by rfl) ⟨288717, by rfl⟩ : syracuseStep 769913 = 577435) B577435
theorem B1458091 : Blo 511796 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B770015 : Blo 511796 770015 := bstep (se 1 (by rfl) ⟨577511, by rfl⟩ : syracuseStep 770015 = 1155023) B1155023
theorem B2474063 : Blo 511796 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B770267 : Blo 511796 770267 := bstep (se 1 (by rfl) ⟨577700, by rfl⟩ : syracuseStep 770267 = 1155401) B1155401
theorem B770279 : Blo 511796 770279 := bstep (se 1 (by rfl) ⟨577709, by rfl⟩ : syracuseStep 770279 = 1155419) B1155419
theorem B868583 : Blo 511796 868583 := bstep (se 1 (by rfl) ⟨651437, by rfl⟩ : syracuseStep 868583 = 1302875) B1302875
theorem B770441 : Blo 511796 770441 := bstep (se 2 (by rfl) ⟨288915, by rfl⟩ : syracuseStep 770441 = 577831) B577831
theorem B868745 : Blo 511796 868745 := bstep (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) B651559
theorem B5620151 : Blo 511796 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B770537 : Blo 511796 770537 := bstep (se 2 (by rfl) ⟨288951, by rfl⟩ : syracuseStep 770537 = 577903) B577903
theorem B2605607 : Blo 511796 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B770663 : Blo 511796 770663 := bstep (se 1 (by rfl) ⟨577997, by rfl⟩ : syracuseStep 770663 = 1155995) B1155995
theorem B770795 : Blo 511796 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B770825 : Blo 511796 770825 := bstep (se 2 (by rfl) ⟨289059, by rfl⟩ : syracuseStep 770825 = 578119) B578119
theorem B869177 : Blo 511796 869177 := bstep (se 2 (by rfl) ⟨325941, by rfl⟩ : syracuseStep 869177 = 651883) B651883
theorem B770927 : Blo 511796 770927 := bstep (se 1 (by rfl) ⟨578195, by rfl⟩ : syracuseStep 770927 = 1156391) B1156391
theorem B869231 : Blo 511796 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B771179 : Blo 511796 771179 := bstep (se 1 (by rfl) ⟨578384, by rfl⟩ : syracuseStep 771179 = 1156769) B1156769
theorem B3818753 : Blo 511796 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B53495113 : Blo 511796 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B2934089 : Blo 511796 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B771419 : Blo 511796 771419 := bstep (se 1 (by rfl) ⟨578564, by rfl⟩ : syracuseStep 771419 = 1157129) B1157129
theorem B1951229 : Blo 511796 1951229 := bstep (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) B731711
theorem B1853039 : Blo 511796 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B771695 : Blo 511796 771695 := bstep (se 1 (by rfl) ⟨578771, by rfl⟩ : syracuseStep 771695 = 1157543) B1157543
theorem B771767 : Blo 511796 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B771803 : Blo 511796 771803 := bstep (se 1 (by rfl) ⟨578852, by rfl⟩ : syracuseStep 771803 = 1157705) B1157705
theorem B2934589 : Blo 511796 2934589 := bstep (se 3 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 2934589 = 1100471) B1100471
theorem B870223 : Blo 511796 870223 := bstep (se 1 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 870223 = 1305335) B1305335
theorem B1230689 : Blo 511796 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B2082689 : Blo 511796 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B771977 : Blo 511796 771977 := bstep (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) B578983
theorem B772079 : Blo 511796 772079 := bstep (se 1 (by rfl) ⟨579059, by rfl⟩ : syracuseStep 772079 = 1158119) B1158119
theorem B3295241 : Blo 511796 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B15190105 : Blo 511796 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B772331 : Blo 511796 772331 := bstep (se 1 (by rfl) ⟨579248, by rfl⟩ : syracuseStep 772331 = 1158497) B1158497
theorem B772391 : Blo 511796 772391 := bstep (se 1 (by rfl) ⟨579293, by rfl⟩ : syracuseStep 772391 = 1158587) B1158587
theorem B772475 : Blo 511796 772475 := bstep (se 1 (by rfl) ⟨579356, by rfl⟩ : syracuseStep 772475 = 1158713) B1158713
theorem B576031 : Blo 511796 576031 := bstep (se 1 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 576031 = 864047) B864047
theorem B772745 : Blo 511796 772745 := bstep (se 2 (by rfl) ⟨289779, by rfl⟩ : syracuseStep 772745 = 579559) B579559
theorem B2771603 : Blo 511796 2771603 := bstep (se 1 (by rfl) ⟨2078702, by rfl⟩ : syracuseStep 2771603 = 4157405) B4157405
theorem B772919 : Blo 511796 772919 := bstep (se 1 (by rfl) ⟨579689, by rfl⟩ : syracuseStep 772919 = 1159379) B1159379
theorem B772955 : Blo 511796 772955 := bstep (se 1 (by rfl) ⟨579716, by rfl⟩ : syracuseStep 772955 = 1159433) B1159433
theorem B773099 : Blo 511796 773099 := bstep (se 1 (by rfl) ⟨579824, by rfl⟩ : syracuseStep 773099 = 1159649) B1159649
theorem B1231919 : Blo 511796 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B1297529 : Blo 511796 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B773303 : Blo 511796 773303 := bstep (se 1 (by rfl) ⟨579977, by rfl⟩ : syracuseStep 773303 = 1159955) B1159955
theorem B773543 : Blo 511796 773543 := bstep (se 1 (by rfl) ⟨580157, by rfl⟩ : syracuseStep 773543 = 1160315) B1160315
theorem B773627 : Blo 511796 773627 := bstep (se 1 (by rfl) ⟨580220, by rfl⟩ : syracuseStep 773627 = 1160441) B1160441
theorem B511815 : Blo 511796 511815 := bstep (se 1 (by rfl) ⟨383861, by rfl⟩ : syracuseStep 511815 = 767723) B767723
theorem B511967 : Blo 511796 511967 := bstep (se 1 (by rfl) ⟨383975, by rfl⟩ : syracuseStep 511967 = 767951) B767951
theorem B512231 : Blo 511796 512231 := bstep (se 1 (by rfl) ⟨384173, by rfl⟩ : syracuseStep 512231 = 768347) B768347
theorem B512383 : Blo 511796 512383 := bstep (se 1 (by rfl) ⟨384287, by rfl⟩ : syracuseStep 512383 = 768575) B768575
theorem B1298825 : Blo 511796 1298825 := bstep (se 2 (by rfl) ⟨487059, by rfl⟩ : syracuseStep 1298825 = 974119) B974119
theorem B512463 : Blo 511796 512463 := bstep (se 1 (by rfl) ⟨384347, by rfl⟩ : syracuseStep 512463 = 768695) B768695
theorem B512615 : Blo 511796 512615 := bstep (se 1 (by rfl) ⟨384461, by rfl⟩ : syracuseStep 512615 = 768923) B768923
theorem B2937505 : Blo 511796 2937505 := bstep (se 2 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 2937505 = 2203129) B2203129
theorem B1954601 : Blo 511796 1954601 := bstep (se 2 (by rfl) ⟨732975, by rfl⟩ : syracuseStep 1954601 = 1465951) B1465951
theorem B1856297 : Blo 511796 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B2609981 : Blo 511796 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B512879 : Blo 511796 512879 := bstep (se 1 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 512879 = 769319) B769319
theorem B512935 : Blo 511796 512935 := bstep (se 1 (by rfl) ⟨384701, by rfl⟩ : syracuseStep 512935 = 769403) B769403
theorem B513019 : Blo 511796 513019 := bstep (se 1 (by rfl) ⟨384764, by rfl⟩ : syracuseStep 513019 = 769529) B769529
theorem B3527675 : Blo 511796 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B513087 : Blo 511796 513087 := bstep (se 1 (by rfl) ⟨384815, by rfl⟩ : syracuseStep 513087 = 769631) B769631
theorem B578623 : Blo 511796 578623 := bstep (se 1 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 578623 = 867935) B867935
theorem B513231 : Blo 511796 513231 := bstep (se 1 (by rfl) ⟨384923, by rfl⟩ : syracuseStep 513231 = 769847) B769847
theorem B578767 : Blo 511796 578767 := bstep (se 1 (by rfl) ⟨434075, by rfl⟩ : syracuseStep 578767 = 868151) B868151
theorem B513435 : Blo 511796 513435 := bstep (se 1 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 513435 = 770153) B770153
theorem B513647 : Blo 511796 513647 := bstep (se 1 (by rfl) ⟨385235, by rfl⟩ : syracuseStep 513647 = 770471) B770471
theorem B513703 : Blo 511796 513703 := bstep (se 1 (by rfl) ⟨385277, by rfl⟩ : syracuseStep 513703 = 770555) B770555
theorem B1300151 : Blo 511796 1300151 := bstep (se 1 (by rfl) ⟨975113, by rfl⟩ : syracuseStep 1300151 = 1950227) B1950227
theorem B513787 : Blo 511796 513787 := bstep (se 1 (by rfl) ⟨385340, by rfl⟩ : syracuseStep 513787 = 770681) B770681
theorem B513823 : Blo 511796 513823 := bstep (se 1 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 513823 = 770735) B770735
theorem B513855 : Blo 511796 513855 := bstep (se 1 (by rfl) ⟨385391, by rfl⟩ : syracuseStep 513855 = 770783) B770783
theorem B514031 : Blo 511796 514031 := bstep (se 1 (by rfl) ⟨385523, by rfl⟩ : syracuseStep 514031 = 771047) B771047
theorem B5855327 : Blo 511796 5855327 := bstep (se 1 (by rfl) ⟨4391495, by rfl⟩ : syracuseStep 5855327 = 8782991) B8782991
theorem B1464425 : Blo 511796 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B3135617 : Blo 511796 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B1038491 : Blo 511796 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B514203 : Blo 511796 514203 := bstep (se 1 (by rfl) ⟨385652, by rfl⟩ : syracuseStep 514203 = 771305) B771305
theorem B579739 : Blo 511796 579739 := bstep (se 1 (by rfl) ⟨434804, by rfl⟩ : syracuseStep 579739 = 869609) B869609
theorem B514239 : Blo 511796 514239 := bstep (se 1 (by rfl) ⟨385679, by rfl⟩ : syracuseStep 514239 = 771359) B771359
theorem B579775 : Blo 511796 579775 := bstep (se 1 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 579775 = 869663) B869663
theorem B1235177 : Blo 511796 1235177 := bstep (se 2 (by rfl) ⟨463191, by rfl⟩ : syracuseStep 1235177 = 926383) B926383
theorem B973063 : Blo 511796 973063 := bstep (se 1 (by rfl) ⟨729797, by rfl⟩ : syracuseStep 973063 = 1459595) B1459595
theorem B514351 : Blo 511796 514351 := bstep (se 1 (by rfl) ⟨385763, by rfl⟩ : syracuseStep 514351 = 771527) B771527
theorem B1956271 : Blo 511796 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B3299773 : Blo 511796 3299773 := bstep (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) B1237415
theorem B514587 : Blo 511796 514587 := bstep (se 1 (by rfl) ⟨385940, by rfl⟩ : syracuseStep 514587 = 771881) B771881
theorem B514591 : Blo 511796 514591 := bstep (se 1 (by rfl) ⟨385943, by rfl⟩ : syracuseStep 514591 = 771887) B771887
theorem B1235513 : Blo 511796 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B42326833 : Blo 511796 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B514907 : Blo 511796 514907 := bstep (se 1 (by rfl) ⟨386180, by rfl⟩ : syracuseStep 514907 = 772361) B772361
theorem B514975 : Blo 511796 514975 := bstep (se 1 (by rfl) ⟨386231, by rfl⟩ : syracuseStep 514975 = 772463) B772463
theorem B515119 : Blo 511796 515119 := bstep (se 1 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 515119 = 772679) B772679
theorem B515143 : Blo 511796 515143 := bstep (se 1 (by rfl) ⟨386357, by rfl⟩ : syracuseStep 515143 = 772715) B772715
theorem B1662137 : Blo 511796 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B515295 : Blo 511796 515295 := bstep (se 1 (by rfl) ⟨386471, by rfl⟩ : syracuseStep 515295 = 772943) B772943
theorem B3890429 : Blo 511796 3890429 := bstep (se 3 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 3890429 = 1458911) B1458911
theorem B1465609 : Blo 511796 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B1727783 : Blo 511796 1727783 := bstep (se 1 (by rfl) ⟨1295837, by rfl⟩ : syracuseStep 1727783 = 2591675) B2591675
theorem B1236455 : Blo 511796 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B515559 : Blo 511796 515559 := bstep (se 1 (by rfl) ⟨386669, by rfl⟩ : syracuseStep 515559 = 773339) B773339
theorem B1302095 : Blo 511796 1302095 := bstep (se 1 (by rfl) ⟨976571, by rfl⟩ : syracuseStep 1302095 = 1953143) B1953143
theorem B515675 : Blo 511796 515675 := bstep (se 1 (by rfl) ⟨386756, by rfl⟩ : syracuseStep 515675 = 773513) B773513
theorem B1040105 : Blo 511796 1040105 := bstep (se 2 (by rfl) ⟨390039, by rfl⟩ : syracuseStep 1040105 = 780079) B780079
theorem B1728647 : Blo 511796 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B975311 : Blo 511796 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B1467193 : Blo 511796 1467193 := bstep (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) B1100395
theorem B5858243 : Blo 511796 5858243 := bstep (se 1 (by rfl) ⟨4393682, by rfl⟩ : syracuseStep 5858243 = 8787365) B8787365
theorem B975827 : Blo 511796 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B3302849 : Blo 511796 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B1730159 : Blo 511796 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B1730267 : Blo 511796 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B3565601 : Blo 511796 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B1468651 : Blo 511796 1468651 := bstep (se 1 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 1468651 = 2202977) B2202977
theorem B18770201 : Blo 511796 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B43379003 : Blo 511796 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B3893831 : Blo 511796 3893831 := bstep (se 1 (by rfl) ⟨2920373, by rfl⟩ : syracuseStep 3893831 = 5840747) B5840747
theorem B1305193 : Blo 511796 1305193 := bstep (se 2 (by rfl) ⟨489447, by rfl⟩ : syracuseStep 1305193 = 978895) B978895
theorem B2190007 : Blo 511796 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B3795767 : Blo 511796 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B1731563 : Blo 511796 1731563 := bstep (se 1 (by rfl) ⟨1298672, by rfl⟩ : syracuseStep 1731563 = 2597345) B2597345
theorem B1731617 : Blo 511796 1731617 := bstep (se 2 (by rfl) ⟨649356, by rfl⟩ : syracuseStep 1731617 = 1298713) B1298713
theorem B1764385 : Blo 511796 1764385 := bstep (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) B1323289
theorem B1764551 : Blo 511796 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B31617049 : Blo 511796 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B1733075 : Blo 511796 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B881455 : Blo 511796 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B3700313 : Blo 511796 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B1735019 : Blo 511796 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B1735289 : Blo 511796 1735289 := bstep (se 2 (by rfl) ⟨650733, by rfl⟩ : syracuseStep 1735289 = 1301467) B1301467
theorem B1735721 : Blo 511796 1735721 := bstep (se 2 (by rfl) ⟨650895, by rfl⟩ : syracuseStep 1735721 = 1301791) B1301791
theorem B7012001 : Blo 511796 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B1737071 : Blo 511796 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B820459 : Blo 511796 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B1639727 : Blo 511796 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B2196827 : Blo 511796 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B6686479 : Blo 511796 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B821279 : Blo 511796 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B20253473 : Blo 511796 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B1739987 : Blo 511796 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B1740257 : Blo 511796 1740257 := bstep (se 2 (by rfl) ⟨652596, by rfl⟩ : syracuseStep 1740257 = 1305193) B1305193
theorem B2920009 : Blo 511796 2920009 := bstep (se 2 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 2920009 = 2190007) B2190007
theorem B3903065 : Blo 511796 3903065 := bstep (se 2 (by rfl) ⟨1463649, by rfl⟩ : syracuseStep 3903065 = 2927299) B2927299
theorem B3903551 : Blo 511796 3903551 := bstep (se 1 (by rfl) ⟨2927663, by rfl⟩ : syracuseStep 3903551 = 5855327) B5855327
theorem B692327 : Blo 511796 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B823451 : Blo 511796 823451 := bstep (se 1 (by rfl) ⟨617588, by rfl⟩ : syracuseStep 823451 = 1235177) B1235177
theorem B3281219 : Blo 511796 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B8425957 : Blo 511796 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B3281579 : Blo 511796 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B1151801 : Blo 511796 1151801 := bstep (se 2 (by rfl) ⟨431925, by rfl⟩ : syracuseStep 1151801 = 863851) B863851
theorem B2593619 : Blo 511796 2593619 := bstep (se 1 (by rfl) ⟨1945214, by rfl⟩ : syracuseStep 2593619 = 3890429) B3890429
theorem B1151855 : Blo 511796 1151855 := bstep (se 1 (by rfl) ⟨863891, by rfl⟩ : syracuseStep 1151855 = 1727783) B1727783
theorem B824303 : Blo 511796 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B2200601 : Blo 511796 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B693403 : Blo 511796 693403 := bstep (se 1 (by rfl) ⟨520052, by rfl⟩ : syracuseStep 693403 = 1040105) B1040105
theorem B1152161 : Blo 511796 1152161 := bstep (se 2 (by rfl) ⟨432060, by rfl⟩ : syracuseStep 1152161 = 864121) B864121
theorem B3282119 : Blo 511796 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B1152431 : Blo 511796 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B3511801 : Blo 511796 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B9410053 : Blo 511796 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B1644275 : Blo 511796 1644275 := bstep (se 1 (by rfl) ⟨1233206, by rfl⟩ : syracuseStep 1644275 = 2466413) B2466413
theorem B3905495 : Blo 511796 3905495 := bstep (se 1 (by rfl) ⟨2929121, by rfl⟩ : syracuseStep 3905495 = 5858243) B5858243
theorem B115677341 : Blo 511796 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B8329463 : Blo 511796 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B2201899 : Blo 511796 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B1153439 : Blo 511796 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B1153511 : Blo 511796 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B3283679 : Blo 511796 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B2595887 : Blo 511796 2595887 := bstep (se 1 (by rfl) ⟨1946915, by rfl⟩ : syracuseStep 2595887 = 3893831) B3893831
theorem B2530511 : Blo 511796 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B4398299 : Blo 511796 4398299 := bstep (se 1 (by rfl) ⟨3298724, by rfl⟩ : syracuseStep 4398299 = 6597449) B6597449
theorem B1154375 : Blo 511796 1154375 := bstep (se 1 (by rfl) ⟨865781, by rfl⟩ : syracuseStep 1154375 = 1731563) B1731563
theorem B1154411 : Blo 511796 1154411 := bstep (se 1 (by rfl) ⟨865808, by rfl⟩ : syracuseStep 1154411 = 1731617) B1731617
theorem B1154537 : Blo 511796 1154537 := bstep (se 2 (by rfl) ⟨432951, by rfl⟩ : syracuseStep 1154537 = 865903) B865903
theorem B1154681 : Blo 511796 1154681 := bstep (se 2 (by rfl) ⟨433005, by rfl⟩ : syracuseStep 1154681 = 866011) B866011
theorem B728795 : Blo 511796 728795 := bstep (se 1 (by rfl) ⟨546596, by rfl⟩ : syracuseStep 728795 = 1093193) B1093193
theorem B6692615 : Blo 511796 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B5611373 : Blo 511796 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B1155383 : Blo 511796 1155383 := bstep (se 1 (by rfl) ⟨866537, by rfl⟩ : syracuseStep 1155383 = 1733075) B1733075
theorem B4399697 : Blo 511796 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B1975211 : Blo 511796 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B2466875 : Blo 511796 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B56435777 : Blo 511796 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B2597993 : Blo 511796 2597993 := bstep (se 2 (by rfl) ⟨974247, by rfl⟩ : syracuseStep 2597993 = 1948495) B1948495
theorem B1156409 : Blo 511796 1156409 := bstep (se 2 (by rfl) ⟨433653, by rfl⟩ : syracuseStep 1156409 = 867307) B867307
theorem B1156679 : Blo 511796 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B1156859 : Blo 511796 1156859 := bstep (se 1 (by rfl) ⟨867644, by rfl⟩ : syracuseStep 1156859 = 1735289) B1735289
theorem B1157147 : Blo 511796 1157147 := bstep (se 1 (by rfl) ⟨867860, by rfl⟩ : syracuseStep 1157147 = 1735721) B1735721
theorem B928235 : Blo 511796 928235 := bstep (se 1 (by rfl) ⟨696176, by rfl⟩ : syracuseStep 928235 = 1392353) B1392353
theorem B1944121 : Blo 511796 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B1649375 : Blo 511796 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B3746767 : Blo 511796 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B1944911 : Blo 511796 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B1158623 : Blo 511796 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B1158839 : Blo 511796 1158839 := bstep (se 1 (by rfl) ⟨869129, by rfl⟩ : syracuseStep 1158839 = 1738259) B1738259
theorem B1388459 : Blo 511796 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B3715303 : Blo 511796 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B1945853 : Blo 511796 1945853 := bstep (se 3 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 1945853 = 729695) B729695
theorem B1847735 : Blo 511796 1847735 := bstep (se 1 (by rfl) ⟨1385801, by rfl⟩ : syracuseStep 1847735 = 2771603) B2771603
theorem B1159631 : Blo 511796 1159631 := bstep (se 1 (by rfl) ⟨869723, by rfl⟩ : syracuseStep 1159631 = 1739447) B1739447
theorem B3912299 : Blo 511796 3912299 := bstep (se 1 (by rfl) ⟨2934224, by rfl⟩ : syracuseStep 3912299 = 5868449) B5868449
theorem B865019 : Blo 511796 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B3912785 : Blo 511796 3912785 := bstep (se 2 (by rfl) ⟨1467294, by rfl⟩ : syracuseStep 3912785 = 2934589) B2934589
theorem B1848425 : Blo 511796 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B1160297 : Blo 511796 1160297 := bstep (se 2 (by rfl) ⟨435111, by rfl⟩ : syracuseStep 1160297 = 870223) B870223
theorem B2602205 : Blo 511796 2602205 := bstep (se 3 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 2602205 = 975827) B975827
theorem B865883 : Blo 511796 865883 := bstep (se 1 (by rfl) ⟨649412, by rfl⟩ : syracuseStep 865883 = 1298825) B1298825
theorem B768041 : Blo 511796 768041 := bstep (se 2 (by rfl) ⟨288015, by rfl⟩ : syracuseStep 768041 = 576031) B576031
theorem B768071 : Blo 511796 768071 := bstep (se 1 (by rfl) ⟨576053, by rfl⟩ : syracuseStep 768071 = 1152107) B1152107
theorem B768455 : Blo 511796 768455 := bstep (se 1 (by rfl) ⟨576341, by rfl⟩ : syracuseStep 768455 = 1152683) B1152683
theorem B866767 : Blo 511796 866767 := bstep (se 1 (by rfl) ⟨650075, by rfl⟩ : syracuseStep 866767 = 1300151) B1300151
theorem B768671 : Blo 511796 768671 := bstep (se 1 (by rfl) ⟨576503, by rfl⟩ : syracuseStep 768671 = 1153007) B1153007
theorem B768815 : Blo 511796 768815 := bstep (se 1 (by rfl) ⟨576611, by rfl⟩ : syracuseStep 768815 = 1153223) B1153223
theorem B768935 : Blo 511796 768935 := bstep (se 1 (by rfl) ⟨576701, by rfl⟩ : syracuseStep 768935 = 1153403) B1153403
theorem B2603987 : Blo 511796 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B769115 : Blo 511796 769115 := bstep (se 1 (by rfl) ⟨576836, by rfl⟩ : syracuseStep 769115 = 1153673) B1153673
theorem B769487 : Blo 511796 769487 := bstep (se 1 (by rfl) ⟨577115, by rfl⟩ : syracuseStep 769487 = 1154231) B1154231
theorem B7126751 : Blo 511796 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B868063 : Blo 511796 868063 := bstep (se 1 (by rfl) ⟨651047, by rfl⟩ : syracuseStep 868063 = 1302095) B1302095
theorem B769871 : Blo 511796 769871 := bstep (se 1 (by rfl) ⟨577403, by rfl⟩ : syracuseStep 769871 = 1154807) B1154807
theorem B769991 : Blo 511796 769991 := bstep (se 1 (by rfl) ⟨577493, by rfl⟩ : syracuseStep 769991 = 1154987) B1154987
theorem B42156065 : Blo 511796 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B1097977 : Blo 511796 1097977 := bstep (se 2 (by rfl) ⟨411741, by rfl⟩ : syracuseStep 1097977 = 823483) B823483
theorem B770351 : Blo 511796 770351 := bstep (se 1 (by rfl) ⟨577763, by rfl⟩ : syracuseStep 770351 = 1155527) B1155527
theorem B770591 : Blo 511796 770591 := bstep (se 1 (by rfl) ⟨577943, by rfl⟩ : syracuseStep 770591 = 1155887) B1155887
theorem B8929925 : Blo 511796 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B2081555 : Blo 511796 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B3916673 : Blo 511796 3916673 := bstep (se 2 (by rfl) ⟨1468752, by rfl⟩ : syracuseStep 3916673 = 2937505) B2937505
theorem B1983521 : Blo 511796 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B2606255 : Blo 511796 2606255 := bstep (se 1 (by rfl) ⟨1954691, by rfl⟩ : syracuseStep 2606255 = 3909383) B3909383
theorem B1950911 : Blo 511796 1950911 := bstep (se 1 (by rfl) ⟨1463183, by rfl⟩ : syracuseStep 1950911 = 2926367) B2926367
theorem B771263 : Blo 511796 771263 := bstep (se 1 (by rfl) ⟨578447, by rfl⟩ : syracuseStep 771263 = 1156895) B1156895
theorem B771407 : Blo 511796 771407 := bstep (se 1 (by rfl) ⟨578555, by rfl⟩ : syracuseStep 771407 = 1157111) B1157111
theorem B4441439 : Blo 511796 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B2377067 : Blo 511796 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B771497 : Blo 511796 771497 := bstep (se 2 (by rfl) ⟨289311, by rfl⟩ : syracuseStep 771497 = 578623) B578623
theorem B3294701 : Blo 511796 3294701 := bstep (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) B1235513
theorem B771647 : Blo 511796 771647 := bstep (se 1 (by rfl) ⟨578735, by rfl⟩ : syracuseStep 771647 = 1157471) B1157471
theorem B1099327 : Blo 511796 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B771689 : Blo 511796 771689 := bstep (se 2 (by rfl) ⟨289383, by rfl⟩ : syracuseStep 771689 = 578767) B578767
theorem B772127 : Blo 511796 772127 := bstep (se 1 (by rfl) ⟨579095, by rfl⟩ : syracuseStep 772127 = 1158191) B1158191
theorem B772319 : Blo 511796 772319 := bstep (se 1 (by rfl) ⟨579239, by rfl⟩ : syracuseStep 772319 = 1158479) B1158479
theorem B772379 : Blo 511796 772379 := bstep (se 1 (by rfl) ⟨579284, by rfl⟩ : syracuseStep 772379 = 1158569) B1158569
theorem B1296719 : Blo 511796 1296719 := bstep (se 1 (by rfl) ⟨972539, by rfl⟩ : syracuseStep 1296719 = 1945079) B1945079
theorem B772703 : Blo 511796 772703 := bstep (se 1 (by rfl) ⟨579527, by rfl⟩ : syracuseStep 772703 = 1159055) B1159055
theorem B576103 : Blo 511796 576103 := bstep (se 1 (by rfl) ⟨432077, by rfl⟩ : syracuseStep 576103 = 864155) B864155
theorem B772985 : Blo 511796 772985 := bstep (se 2 (by rfl) ⟨289869, by rfl⟩ : syracuseStep 772985 = 579739) B579739
theorem B773033 : Blo 511796 773033 := bstep (se 2 (by rfl) ⟨289887, by rfl⟩ : syracuseStep 773033 = 579775) B579775
theorem B1297417 : Blo 511796 1297417 := bstep (se 2 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 1297417 = 973063) B973063
theorem B773183 : Blo 511796 773183 := bstep (se 1 (by rfl) ⟨579887, by rfl⟩ : syracuseStep 773183 = 1159775) B1159775
theorem B2608361 : Blo 511796 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B576895 : Blo 511796 576895 := bstep (se 1 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 576895 = 865343) B865343
theorem B7032253 : Blo 511796 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B3296801 : Blo 511796 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B511807 : Blo 511796 511807 := bstep (se 1 (by rfl) ⟨383855, by rfl⟩ : syracuseStep 511807 = 767711) B767711
theorem B511871 : Blo 511796 511871 := bstep (se 1 (by rfl) ⟨383903, by rfl⟩ : syracuseStep 511871 = 767807) B767807
theorem B511983 : Blo 511796 511983 := bstep (se 1 (by rfl) ⟨383987, by rfl⟩ : syracuseStep 511983 = 767975) B767975
theorem B511995 : Blo 511796 511995 := bstep (se 1 (by rfl) ⟨383996, by rfl⟩ : syracuseStep 511995 = 767993) B767993
theorem B512063 : Blo 511796 512063 := bstep (se 1 (by rfl) ⟨384047, by rfl⟩ : syracuseStep 512063 = 768095) B768095
theorem B512103 : Blo 511796 512103 := bstep (se 1 (by rfl) ⟨384077, by rfl⟩ : syracuseStep 512103 = 768155) B768155
theorem B512127 : Blo 511796 512127 := bstep (se 1 (by rfl) ⟨384095, by rfl⟩ : syracuseStep 512127 = 768191) B768191
theorem B512155 : Blo 511796 512155 := bstep (se 1 (by rfl) ⟨384116, by rfl⟩ : syracuseStep 512155 = 768233) B768233
theorem B8769869 : Blo 511796 8769869 := bstep (se 3 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 8769869 = 3288701) B3288701
theorem B1954145 : Blo 511796 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B512359 : Blo 511796 512359 := bstep (se 1 (by rfl) ⟨384269, by rfl⟩ : syracuseStep 512359 = 768539) B768539
theorem B512411 : Blo 511796 512411 := bstep (se 1 (by rfl) ⟨384308, by rfl⟩ : syracuseStep 512411 = 768617) B768617
theorem B1298875 : Blo 511796 1298875 := bstep (se 1 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 1298875 = 1948313) B1948313
theorem B1757627 : Blo 511796 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B512763 : Blo 511796 512763 := bstep (se 1 (by rfl) ⟨384572, by rfl⟩ : syracuseStep 512763 = 769145) B769145
theorem B578299 : Blo 511796 578299 := bstep (se 1 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 578299 = 867449) B867449
theorem B512831 : Blo 511796 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B512859 : Blo 511796 512859 := bstep (se 1 (by rfl) ⟨384644, by rfl⟩ : syracuseStep 512859 = 769289) B769289
theorem B1299311 : Blo 511796 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B512927 : Blo 511796 512927 := bstep (se 1 (by rfl) ⟨384695, by rfl⟩ : syracuseStep 512927 = 769391) B769391
theorem B513007 : Blo 511796 513007 := bstep (se 1 (by rfl) ⟨384755, by rfl⟩ : syracuseStep 513007 = 769511) B769511
theorem B513095 : Blo 511796 513095 := bstep (se 1 (by rfl) ⟨384821, by rfl⟩ : syracuseStep 513095 = 769643) B769643
theorem B4674667 : Blo 511796 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B513179 : Blo 511796 513179 := bstep (se 1 (by rfl) ⟨384884, by rfl⟩ : syracuseStep 513179 = 769769) B769769
theorem B513275 : Blo 511796 513275 := bstep (se 1 (by rfl) ⟨384956, by rfl⟩ : syracuseStep 513275 = 769913) B769913
theorem B513343 : Blo 511796 513343 := bstep (se 1 (by rfl) ⟨385007, by rfl⟩ : syracuseStep 513343 = 770015) B770015
theorem B4937051 : Blo 511796 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B513511 : Blo 511796 513511 := bstep (se 1 (by rfl) ⟨385133, by rfl⟩ : syracuseStep 513511 = 770267) B770267
theorem B513519 : Blo 511796 513519 := bstep (se 1 (by rfl) ⟨385139, by rfl⟩ : syracuseStep 513519 = 770279) B770279
theorem B579055 : Blo 511796 579055 := bstep (se 1 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 579055 = 868583) B868583
theorem B513627 : Blo 511796 513627 := bstep (se 1 (by rfl) ⟨385220, by rfl⟩ : syracuseStep 513627 = 770441) B770441
theorem B579163 : Blo 511796 579163 := bstep (se 1 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 579163 = 868745) B868745
theorem B972425 : Blo 511796 972425 := bstep (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) B729319
theorem B513691 : Blo 511796 513691 := bstep (se 1 (by rfl) ⟨385268, by rfl⟩ : syracuseStep 513691 = 770537) B770537
theorem B1463975 : Blo 511796 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B513775 : Blo 511796 513775 := bstep (se 1 (by rfl) ⟨385331, by rfl⟩ : syracuseStep 513775 = 770663) B770663
theorem B1464095 : Blo 511796 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B513863 : Blo 511796 513863 := bstep (se 1 (by rfl) ⟨385397, by rfl⟩ : syracuseStep 513863 = 770795) B770795
theorem B513883 : Blo 511796 513883 := bstep (se 1 (by rfl) ⟨385412, by rfl⟩ : syracuseStep 513883 = 770825) B770825
theorem B579451 : Blo 511796 579451 := bstep (se 1 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 579451 = 869177) B869177
theorem B513951 : Blo 511796 513951 := bstep (se 1 (by rfl) ⟨385463, by rfl⟩ : syracuseStep 513951 = 770927) B770927
theorem B579487 : Blo 511796 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B514119 : Blo 511796 514119 := bstep (se 1 (by rfl) ⟨385589, by rfl⟩ : syracuseStep 514119 = 771179) B771179
theorem B1267849 : Blo 511796 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B2545835 : Blo 511796 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B1956059 : Blo 511796 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B514279 : Blo 511796 514279 := bstep (se 1 (by rfl) ⟨385709, by rfl⟩ : syracuseStep 514279 = 771419) B771419
theorem B1300819 : Blo 511796 1300819 := bstep (se 1 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 1300819 = 1951229) B1951229
theorem B1235359 : Blo 511796 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B514463 : Blo 511796 514463 := bstep (se 1 (by rfl) ⟨385847, by rfl⟩ : syracuseStep 514463 = 771695) B771695
theorem B1956257 : Blo 511796 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B514511 : Blo 511796 514511 := bstep (se 1 (by rfl) ⟨385883, by rfl⟩ : syracuseStep 514511 = 771767) B771767
theorem B514535 : Blo 511796 514535 := bstep (se 1 (by rfl) ⟨385901, by rfl⟩ : syracuseStep 514535 = 771803) B771803
theorem B514651 : Blo 511796 514651 := bstep (se 1 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 514651 = 771977) B771977
theorem B514719 : Blo 511796 514719 := bstep (se 1 (by rfl) ⟨386039, by rfl⟩ : syracuseStep 514719 = 772079) B772079
theorem B514887 : Blo 511796 514887 := bstep (se 1 (by rfl) ⟨386165, by rfl⟩ : syracuseStep 514887 = 772331) B772331
theorem B1465199 : Blo 511796 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B514927 : Blo 511796 514927 := bstep (se 1 (by rfl) ⟨386195, by rfl⟩ : syracuseStep 514927 = 772391) B772391
theorem B514983 : Blo 511796 514983 := bstep (se 1 (by rfl) ⟨386237, by rfl⟩ : syracuseStep 514983 = 772475) B772475
theorem B515163 : Blo 511796 515163 := bstep (se 1 (by rfl) ⟨386372, by rfl⟩ : syracuseStep 515163 = 772745) B772745
theorem B71326817 : Blo 511796 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B515279 : Blo 511796 515279 := bstep (se 1 (by rfl) ⟨386459, by rfl⟩ : syracuseStep 515279 = 772919) B772919
theorem B515303 : Blo 511796 515303 := bstep (se 1 (by rfl) ⟨386477, by rfl⟩ : syracuseStep 515303 = 772955) B772955
theorem B515399 : Blo 511796 515399 := bstep (se 1 (by rfl) ⟨386549, by rfl⟩ : syracuseStep 515399 = 773099) B773099
theorem B1957229 : Blo 511796 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B515535 : Blo 511796 515535 := bstep (se 1 (by rfl) ⟨386651, by rfl⟩ : syracuseStep 515535 = 773303) B773303
theorem B515695 : Blo 511796 515695 := bstep (se 1 (by rfl) ⟨386771, by rfl⟩ : syracuseStep 515695 = 773543) B773543
theorem B515751 : Blo 511796 515751 := bstep (se 1 (by rfl) ⟨386813, by rfl⟩ : syracuseStep 515751 = 773627) B773627
theorem B974825 : Blo 511796 974825 := bstep (se 2 (by rfl) ⟨365559, by rfl⟩ : syracuseStep 974825 = 731119) B731119
theorem B1958201 : Blo 511796 1958201 := bstep (se 2 (by rfl) ⟨734325, by rfl⟩ : syracuseStep 1958201 = 1468651) B1468651
theorem B14016989 : Blo 511796 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B81420823 : Blo 511796 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B1303067 : Blo 511796 1303067 := bstep (se 1 (by rfl) ⟨977300, by rfl⟩ : syracuseStep 1303067 = 1954601) B1954601
theorem B1237531 : Blo 511796 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B2351783 : Blo 511796 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B549595 : Blo 511796 549595 := bstep (se 1 (by rfl) ⟨412196, by rfl⟩ : syracuseStep 549595 = 824393) B824393
theorem B14869277 : Blo 511796 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B2188403 : Blo 511796 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B976283 : Blo 511796 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B2090411 : Blo 511796 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B9397787 : Blo 511796 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B2189051 : Blo 511796 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B1108091 : Blo 511796 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B616939 : Blo 511796 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B2189855 : Blo 511796 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B650207 : Blo 511796 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B1175273 : Blo 511796 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B5861159 : Blo 511796 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B3895289 : Blo 511796 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B1732751 : Blo 511796 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B12513467 : Blo 511796 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B1732967 : Blo 511796 1732967 := bstep (se 1 (by rfl) ⟨1299725, by rfl⟩ : syracuseStep 1732967 = 2599451) B2599451
theorem B1176367 : Blo 511796 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B18969491 : Blo 511796 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B3896747 : Blo 511796 3896747 := bstep (se 1 (by rfl) ⟨2922560, by rfl⟩ : syracuseStep 3896747 = 5845121) B5845121
theorem B1734479 : Blo 511796 1734479 := bstep (se 1 (by rfl) ⟨1300859, by rfl⟩ : syracuseStep 1734479 = 2601719) B2601719
theorem B2915453 : Blo 511796 2915453 := bstep (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) B1093295
theorem B1736423 : Blo 511796 1736423 := bstep (se 1 (by rfl) ⟨1302317, by rfl⟩ : syracuseStep 1736423 = 2604635) B2604635
theorem B2195869 : Blo 511796 2195869 := bstep (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) B823451
theorem B108561097 : Blo 511796 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B1737503 : Blo 511796 1737503 := bstep (se 1 (by rfl) ⟨1303127, by rfl⟩ : syracuseStep 1737503 = 2606255) B2606255
theorem B2196467 : Blo 511796 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B13502315 : Blo 511796 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B1738907 : Blo 511796 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B2197867 : Blo 511796 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2198141 : Blo 511796 2198141 := bstep (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) B824303
theorem B2592161 : Blo 511796 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B2593133 : Blo 511796 2593133 := bstep (se 3 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 2593133 = 972425) B972425
theorem B9376337 : Blo 511796 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B47551211 : Blo 511796 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B4461743 : Blo 511796 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B3740915 : Blo 511796 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B4953737 : Blo 511796 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B9344659 : Blo 511796 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B2954909 : Blo 511796 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B6788893 : Blo 511796 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1316807 : Blo 511796 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B1644583 : Blo 511796 1644583 := bstep (se 1 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 1644583 = 2466875) B2466875
theorem B37623851 : Blo 511796 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B6232889 : Blo 511796 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B3907439 : Blo 511796 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B2596859 : Blo 511796 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B1155167 : Blo 511796 1155167 := bstep (se 1 (by rfl) ⟨866375, by rfl⟩ : syracuseStep 1155167 = 1732751) B1732751
theorem B1155311 : Blo 511796 1155311 := bstep (se 1 (by rfl) ⟨866483, by rfl⟩ : syracuseStep 1155311 = 1732967) B1732967
theorem B1647145 : Blo 511796 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B1155689 : Blo 511796 1155689 := bstep (se 2 (by rfl) ⟨433383, by rfl⟩ : syracuseStep 1155689 = 866767) B866767
theorem B2597831 : Blo 511796 2597831 := bstep (se 1 (by rfl) ⟨1948373, by rfl⟩ : syracuseStep 2597831 = 3896747) B3896747
theorem B1156319 : Blo 511796 1156319 := bstep (se 1 (by rfl) ⟨867239, by rfl⟩ : syracuseStep 1156319 = 1734479) B1734479
theorem B35661221 : Blo 511796 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B1943453 : Blo 511796 1943453 := bstep (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) B728795
theorem B1943635 : Blo 511796 1943635 := bstep (se 1 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 1943635 = 2915453) B2915453
theorem B1157417 : Blo 511796 1157417 := bstep (se 2 (by rfl) ⟨434031, by rfl⟩ : syracuseStep 1157417 = 868063) B868063
theorem B1157615 : Blo 511796 1157615 := bstep (se 1 (by rfl) ⟨868211, by rfl⟩ : syracuseStep 1157615 = 1736423) B1736423
theorem B1158047 : Blo 511796 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1846205 : Blo 511796 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B1387703 : Blo 511796 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B1322347 : Blo 511796 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B1650041 : Blo 511796 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B6761861 : Blo 511796 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B1093151 : Blo 511796 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B2960959 : Blo 511796 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B864479 : Blo 511796 864479 := bstep (se 1 (by rfl) ⟨648359, by rfl⟩ : syracuseStep 864479 = 1296719) B1296719
theorem B1093945 : Blo 511796 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B1159991 : Blo 511796 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1160171 : Blo 511796 1160171 := bstep (se 1 (by rfl) ⟨870128, by rfl⟩ : syracuseStep 1160171 = 1740257) B1740257
theorem B2602043 : Blo 511796 2602043 := bstep (se 1 (by rfl) ⟨1951532, by rfl⟩ : syracuseStep 2602043 = 3903065) B3903065
theorem B2602367 : Blo 511796 2602367 := bstep (se 1 (by rfl) ⟨1951775, by rfl⟩ : syracuseStep 2602367 = 3903551) B3903551
theorem B5846579 : Blo 511796 5846579 := bstep (se 1 (by rfl) ⟨4384934, by rfl⟩ : syracuseStep 5846579 = 8769869) B8769869
theorem B4929133 : Blo 511796 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B767867 : Blo 511796 767867 := bstep (se 1 (by rfl) ⟨575900, by rfl⟩ : syracuseStep 767867 = 1151801) B1151801
theorem B767903 : Blo 511796 767903 := bstep (se 1 (by rfl) ⟨575927, by rfl⟩ : syracuseStep 767903 = 1151855) B1151855
theorem B866207 : Blo 511796 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B768107 : Blo 511796 768107 := bstep (se 1 (by rfl) ⟨576080, by rfl⟩ : syracuseStep 768107 = 1152161) B1152161
theorem B768137 : Blo 511796 768137 := bstep (se 2 (by rfl) ⟨288051, by rfl⟩ : syracuseStep 768137 = 576103) B576103
theorem B3291367 : Blo 511796 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B6338845 : Blo 511796 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B768287 : Blo 511796 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B2931173 : Blo 511796 2931173 := bstep (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) B549595
theorem B1096183 : Blo 511796 1096183 := bstep (se 1 (by rfl) ⟨822137, by rfl⟩ : syracuseStep 1096183 = 1644275) B1644275
theorem B4995689 : Blo 511796 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B2603663 : Blo 511796 2603663 := bstep (se 1 (by rfl) ⟨1952747, by rfl⟩ : syracuseStep 2603663 = 3905495) B3905495
theorem B77118227 : Blo 511796 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B5552975 : Blo 511796 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B768959 : Blo 511796 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B769007 : Blo 511796 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B769193 : Blo 511796 769193 := bstep (se 2 (by rfl) ⟨288447, by rfl⟩ : syracuseStep 769193 = 576895) B576895
theorem B1687007 : Blo 511796 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B2932199 : Blo 511796 2932199 := bstep (se 1 (by rfl) ⟨2199149, by rfl⟩ : syracuseStep 2932199 = 4398299) B4398299
theorem B769583 : Blo 511796 769583 := bstep (se 1 (by rfl) ⟨577187, by rfl⟩ : syracuseStep 769583 = 1154375) B1154375
theorem B769607 : Blo 511796 769607 := bstep (se 1 (by rfl) ⟨577205, by rfl⟩ : syracuseStep 769607 = 1154411) B1154411
theorem B769691 : Blo 511796 769691 := bstep (se 1 (by rfl) ⟨577268, by rfl⟩ : syracuseStep 769691 = 1154537) B1154537
theorem B769787 : Blo 511796 769787 := bstep (se 1 (by rfl) ⟨577340, by rfl⟩ : syracuseStep 769787 = 1154681) B1154681
theorem B770255 : Blo 511796 770255 := bstep (se 1 (by rfl) ⟨577691, by rfl⟩ : syracuseStep 770255 = 1155383) B1155383
theorem B868711 : Blo 511796 868711 := bstep (se 1 (by rfl) ⟨651533, by rfl⟩ : syracuseStep 868711 = 1303067) B1303067
theorem B2933131 : Blo 511796 2933131 := bstep (se 1 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 2933131 = 4399697) B4399697
theorem B9912851 : Blo 511796 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B1458935 : Blo 511796 1458935 := bstep (se 1 (by rfl) ⟨1094201, by rfl⟩ : syracuseStep 1458935 = 2188403) B2188403
theorem B770939 : Blo 511796 770939 := bstep (se 1 (by rfl) ⟨578204, by rfl⟩ : syracuseStep 770939 = 1156409) B1156409
theorem B1393607 : Blo 511796 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B771065 : Blo 511796 771065 := bstep (se 2 (by rfl) ⟨289149, by rfl⟩ : syracuseStep 771065 = 578299) B578299
theorem B771119 : Blo 511796 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B1459367 : Blo 511796 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B771239 : Blo 511796 771239 := bstep (se 1 (by rfl) ⟨578429, by rfl⟩ : syracuseStep 771239 = 1156859) B1156859
theorem B771431 : Blo 511796 771431 := bstep (se 1 (by rfl) ⟨578573, by rfl⟩ : syracuseStep 771431 = 1157147) B1157147
theorem B1459903 : Blo 511796 1459903 := bstep (se 1 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 1459903 = 2189855) B2189855
theorem B1099583 : Blo 511796 1099583 := bstep (se 1 (by rfl) ⟨824687, by rfl⟩ : syracuseStep 1099583 = 1649375) B1649375
theorem B772073 : Blo 511796 772073 := bstep (se 2 (by rfl) ⟨289527, by rfl⟩ : syracuseStep 772073 = 579055) B579055
theorem B772217 : Blo 511796 772217 := bstep (se 2 (by rfl) ⟨289581, by rfl⟩ : syracuseStep 772217 = 579163) B579163
theorem B1296607 : Blo 511796 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B772415 : Blo 511796 772415 := bstep (se 1 (by rfl) ⟨579311, by rfl⟩ : syracuseStep 772415 = 1158623) B1158623
theorem B772559 : Blo 511796 772559 := bstep (se 1 (by rfl) ⟨579419, by rfl⟩ : syracuseStep 772559 = 1158839) B1158839
theorem B772601 : Blo 511796 772601 := bstep (se 2 (by rfl) ⟨289725, by rfl⟩ : syracuseStep 772601 = 579451) B579451
theorem B772649 : Blo 511796 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B18729605 : Blo 511796 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B8342311 : Blo 511796 8342311 := bstep (se 1 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 8342311 = 12513467) B12513467
theorem B1297235 : Blo 511796 1297235 := bstep (se 1 (by rfl) ⟨972926, by rfl⟩ : syracuseStep 1297235 = 1945853) B1945853
theorem B1231823 : Blo 511796 1231823 := bstep (se 1 (by rfl) ⟨923867, by rfl⟩ : syracuseStep 1231823 = 1847735) B1847735
theorem B773087 : Blo 511796 773087 := bstep (se 1 (by rfl) ⟨579815, by rfl⟩ : syracuseStep 773087 = 1159631) B1159631
theorem B2935865 : Blo 511796 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B2608199 : Blo 511796 2608199 := bstep (se 1 (by rfl) ⟨1956149, by rfl⟩ : syracuseStep 2608199 = 3912299) B3912299
theorem B576679 : Blo 511796 576679 := bstep (se 1 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 576679 = 865019) B865019
theorem B2608523 : Blo 511796 2608523 := bstep (se 1 (by rfl) ⟨1956392, by rfl⟩ : syracuseStep 2608523 = 3912785) B3912785
theorem B773531 : Blo 511796 773531 := bstep (se 1 (by rfl) ⟨580148, by rfl⟩ : syracuseStep 773531 = 1160297) B1160297
theorem B577255 : Blo 511796 577255 := bstep (se 1 (by rfl) ⟨432941, by rfl⟩ : syracuseStep 577255 = 865883) B865883
theorem B512027 : Blo 511796 512027 := bstep (se 1 (by rfl) ⟨384020, by rfl⟩ : syracuseStep 512027 = 768041) B768041
theorem B512047 : Blo 511796 512047 := bstep (se 1 (by rfl) ⟨384035, by rfl⟩ : syracuseStep 512047 = 768071) B768071
theorem B512303 : Blo 511796 512303 := bstep (se 1 (by rfl) ⟨384227, by rfl⟩ : syracuseStep 512303 = 768455) B768455
theorem B512447 : Blo 511796 512447 := bstep (se 1 (by rfl) ⟨384335, by rfl⟩ : syracuseStep 512447 = 768671) B768671
theorem B512543 : Blo 511796 512543 := bstep (se 1 (by rfl) ⟨384407, by rfl⟩ : syracuseStep 512543 = 768815) B768815
theorem B512623 : Blo 511796 512623 := bstep (se 1 (by rfl) ⟨384467, by rfl⟩ : syracuseStep 512623 = 768935) B768935
theorem B512743 : Blo 511796 512743 := bstep (se 1 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 512743 = 769115) B769115
theorem B13161365 : Blo 511796 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B512991 : Blo 511796 512991 := bstep (se 1 (by rfl) ⟨384743, by rfl⟩ : syracuseStep 512991 = 769487) B769487
theorem B513247 : Blo 511796 513247 := bstep (se 1 (by rfl) ⟨384935, by rfl⟩ : syracuseStep 513247 = 769871) B769871
theorem B513327 : Blo 511796 513327 := bstep (se 1 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 513327 = 769991) B769991
theorem B28104043 : Blo 511796 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B513567 : Blo 511796 513567 := bstep (se 1 (by rfl) ⟨385175, by rfl⟩ : syracuseStep 513567 = 770351) B770351
theorem B1463969 : Blo 511796 1463969 := bstep (se 2 (by rfl) ⟨548988, by rfl⟩ : syracuseStep 1463969 = 1097977) B1097977
theorem B513727 : Blo 511796 513727 := bstep (se 1 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 513727 = 770591) B770591
theorem B5953283 : Blo 511796 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B2611115 : Blo 511796 2611115 := bstep (se 1 (by rfl) ⟨1958336, by rfl⟩ : syracuseStep 2611115 = 3916673) B3916673
theorem B1300607 : Blo 511796 1300607 := bstep (se 1 (by rfl) ⟨975455, by rfl⟩ : syracuseStep 1300607 = 1950911) B1950911
theorem B514175 : Blo 511796 514175 := bstep (se 1 (by rfl) ⟨385631, by rfl⟩ : syracuseStep 514175 = 771263) B771263
theorem B514271 : Blo 511796 514271 := bstep (se 1 (by rfl) ⟨385703, by rfl⟩ : syracuseStep 514271 = 771407) B771407
theorem B1464551 : Blo 511796 1464551 := bstep (se 1 (by rfl) ⟨1098413, by rfl⟩ : syracuseStep 1464551 = 2196827) B2196827
theorem B514331 : Blo 511796 514331 := bstep (se 1 (by rfl) ⟨385748, by rfl⟩ : syracuseStep 514331 = 771497) B771497
theorem B514431 : Blo 511796 514431 := bstep (se 1 (by rfl) ⟨385823, by rfl⟩ : syracuseStep 514431 = 771647) B771647
theorem B514459 : Blo 511796 514459 := bstep (se 1 (by rfl) ⟨385844, by rfl⟩ : syracuseStep 514459 = 771689) B771689
theorem B514751 : Blo 511796 514751 := bstep (se 1 (by rfl) ⟨386063, by rfl⟩ : syracuseStep 514751 = 772127) B772127
theorem B514879 : Blo 511796 514879 := bstep (se 1 (by rfl) ⟨386159, by rfl⟩ : syracuseStep 514879 = 772319) B772319
theorem B514919 : Blo 511796 514919 := bstep (se 1 (by rfl) ⟨386189, by rfl⟩ : syracuseStep 514919 = 772379) B772379
theorem B515135 : Blo 511796 515135 := bstep (se 1 (by rfl) ⟨386351, by rfl⟩ : syracuseStep 515135 = 772703) B772703
theorem B515323 : Blo 511796 515323 := bstep (se 1 (by rfl) ⟨386492, by rfl⟩ : syracuseStep 515323 = 772985) B772985
theorem B515355 : Blo 511796 515355 := bstep (se 1 (by rfl) ⟨386516, by rfl⟩ : syracuseStep 515355 = 773033) B773033
theorem B515455 : Blo 511796 515455 := bstep (se 1 (by rfl) ⟨386591, by rfl⟩ : syracuseStep 515455 = 773183) B773183
theorem B1465769 : Blo 511796 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B50585309 : Blo 511796 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B2187479 : Blo 511796 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1302763 : Blo 511796 1302763 := bstep (se 1 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 1302763 = 1954145) B1954145
theorem B1171751 : Blo 511796 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B2187719 : Blo 511796 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B1729079 : Blo 511796 1729079 := bstep (se 1 (by rfl) ⟨1296809, by rfl⟩ : syracuseStep 1729079 = 2593619) B2593619
theorem B1467067 : Blo 511796 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B2188079 : Blo 511796 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B975983 : Blo 511796 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B976063 : Blo 511796 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B1729889 : Blo 511796 1729889 := bstep (se 2 (by rfl) ⟨648708, by rfl⟩ : syracuseStep 1729889 = 1297417) B1297417
theorem B25060765 : Blo 511796 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B1304039 : Blo 511796 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B1304171 : Blo 511796 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B2189119 : Blo 511796 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B976799 : Blo 511796 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B1730591 : Blo 511796 1730591 := bstep (se 1 (by rfl) ⟨1297943, by rfl⟩ : syracuseStep 1730591 = 2595887) B2595887
theorem B3893345 : Blo 511796 3893345 := bstep (se 2 (by rfl) ⟨1460004, by rfl⟩ : syracuseStep 3893345 = 2920009) B2920009
theorem B1304819 : Blo 511796 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B649883 : Blo 511796 649883 := bstep (se 1 (by rfl) ⟨487412, by rfl⟩ : syracuseStep 649883 = 974825) B974825
theorem B2190077 : Blo 511796 2190077 := bstep (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) B821279
theorem B1305467 : Blo 511796 1305467 := bstep (se 1 (by rfl) ⟨979100, by rfl⟩ : syracuseStep 1305467 = 1958201) B1958201
theorem B1567855 : Blo 511796 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1731833 : Blo 511796 1731833 := bstep (se 2 (by rfl) ⟨649437, by rfl⟩ : syracuseStep 1731833 = 1298875) B1298875
theorem B11234609 : Blo 511796 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B1731995 : Blo 511796 1731995 := bstep (se 1 (by rfl) ⟨1298996, by rfl⟩ : syracuseStep 1731995 = 2597993) B2597993
theorem B3698149 : Blo 511796 3698149 := bstep (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) B693403
theorem B650855 : Blo 511796 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B1568489 : Blo 511796 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B618823 : Blo 511796 618823 := bstep (se 1 (by rfl) ⟨464117, by rfl⟩ : syracuseStep 618823 = 928235) B928235
theorem B12546737 : Blo 511796 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B783515 : Blo 511796 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B1733885 : Blo 511796 1733885 := bstep (se 3 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 1733885 = 650207) B650207
theorem B1734425 : Blo 511796 1734425 := bstep (se 2 (by rfl) ⟨650409, by rfl⟩ : syracuseStep 1734425 = 1300819) B1300819
theorem B1734803 : Blo 511796 1734803 := bstep (se 1 (by rfl) ⟨1301102, by rfl⟩ : syracuseStep 1734803 = 2602205) B2602205
theorem B19004669 : Blo 511796 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B1735991 : Blo 511796 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B3702557 : Blo 511796 3702557 := bstep (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) B1388459
theorem B1737017 : Blo 511796 1737017 := bstep (se 2 (by rfl) ⟨651381, by rfl⟩ : syracuseStep 1737017 = 1302763) B1302763
theorem B2196193 : Blo 511796 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B12486403 : Blo 511796 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B821215 : Blo 511796 821215 := bstep (se 1 (by rfl) ⟨615911, by rfl⟩ : syracuseStep 821215 = 1231823) B1231823
theorem B1738799 : Blo 511796 1738799 := bstep (se 1 (by rfl) ⟨1304099, by rfl⟩ : syracuseStep 1738799 = 2608199) B2608199
theorem B1739015 : Blo 511796 1739015 := bstep (se 1 (by rfl) ⟨1304261, by rfl⟩ : syracuseStep 1739015 = 2608523) B2608523
theorem B2918825 : Blo 511796 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B2591513 : Blo 511796 2591513 := bstep (se 2 (by rfl) ⟨971817, by rfl⟩ : syracuseStep 2591513 = 1943635) B1943635
theorem B1969939 : Blo 511796 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B3968855 : Blo 511796 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B1740743 : Blo 511796 1740743 := bstep (se 1 (by rfl) ⟨1305557, by rfl⟩ : syracuseStep 1740743 = 2611115) B2611115
theorem B33723539 : Blo 511796 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B1152719 : Blo 511796 1152719 := bstep (se 1 (by rfl) ⟨864539, by rfl⟩ : syracuseStep 1152719 = 1729079) B1729079
theorem B8361893 : Blo 511796 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B1153259 : Blo 511796 1153259 := bstep (se 1 (by rfl) ⟨864944, by rfl⟩ : syracuseStep 1153259 = 1729889) B1729889
theorem B1153727 : Blo 511796 1153727 := bstep (se 1 (by rfl) ⟨865295, by rfl⟩ : syracuseStep 1153727 = 1730591) B1730591
theorem B2595563 : Blo 511796 2595563 := bstep (se 1 (by rfl) ⟨1946672, by rfl⟩ : syracuseStep 2595563 = 3893345) B3893345
theorem B1154555 : Blo 511796 1154555 := bstep (se 1 (by rfl) ⟨865916, by rfl⟩ : syracuseStep 1154555 = 1731833) B1731833
theorem B12459545 : Blo 511796 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B1154663 : Blo 511796 1154663 := bstep (se 1 (by rfl) ⟨865997, by rfl⟩ : syracuseStep 1154663 = 1731995) B1731995
theorem B728767 : Blo 511796 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B9051857 : Blo 511796 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B8364491 : Blo 511796 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B1155923 : Blo 511796 1155923 := bstep (se 1 (by rfl) ⟨866942, by rfl⟩ : syracuseStep 1155923 = 1733885) B1733885
theorem B1156283 : Blo 511796 1156283 := bstep (se 1 (by rfl) ⟨867212, by rfl⟩ : syracuseStep 1156283 = 1734425) B1734425
theorem B1156535 : Blo 511796 1156535 := bstep (se 1 (by rfl) ⟨867401, by rfl⟩ : syracuseStep 1156535 = 1734803) B1734803
theorem B9873485 : Blo 511796 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B1157327 : Blo 511796 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B1124671 : Blo 511796 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B1158281 : Blo 511796 1158281 := bstep (se 2 (by rfl) ⟨434355, by rfl⟩ : syracuseStep 1158281 = 868711) B868711
theorem B3910841 : Blo 511796 3910841 := bstep (se 2 (by rfl) ⟨1466565, by rfl⟩ : syracuseStep 3910841 = 2933131) B2933131
theorem B1158335 : Blo 511796 1158335 := bstep (se 1 (by rfl) ⟨868751, by rfl⟩ : syracuseStep 1158335 = 1737503) B1737503
theorem B2927825 : Blo 511796 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B929071 : Blo 511796 929071 := bstep (se 1 (by rfl) ⟨696803, by rfl⟩ : syracuseStep 929071 = 1393607) B1393607
theorem B3124669 : Blo 511796 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B144748129 : Blo 511796 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B733055 : Blo 511796 733055 := bstep (se 1 (by rfl) ⟨549791, by rfl⟩ : syracuseStep 733055 = 1099583) B1099583
theorem B1159271 : Blo 511796 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B864823 : Blo 511796 864823 := bstep (se 1 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 864823 = 1297235) B1297235
theorem B1946537 : Blo 511796 1946537 := bstep (se 2 (by rfl) ⟨729951, by rfl⟩ : syracuseStep 1946537 = 1459903) B1459903
theorem B2602621 : Blo 511796 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B2930489 : Blo 511796 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B31700807 : Blo 511796 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B9975773 : Blo 511796 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B11123081 : Blo 511796 11123081 := bstep (se 2 (by rfl) ⟨4171155, by rfl⟩ : syracuseStep 11123081 = 8342311) B8342311
theorem B25082567 : Blo 511796 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B867071 : Blo 511796 867071 := bstep (se 1 (by rfl) ⟨650303, by rfl⟩ : syracuseStep 867071 = 1300607) B1300607
theorem B768905 : Blo 511796 768905 := bstep (se 2 (by rfl) ⟨288339, by rfl⟩ : syracuseStep 768905 = 576679) B576679
theorem B4930865 : Blo 511796 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3947945 : Blo 511796 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B769673 : Blo 511796 769673 := bstep (se 2 (by rfl) ⟨288627, by rfl⟩ : syracuseStep 769673 = 577255) B577255
theorem B2604797 : Blo 511796 2604797 := bstep (se 3 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 2604797 = 976799) B976799
theorem B2604959 : Blo 511796 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B770111 : Blo 511796 770111 := bstep (se 1 (by rfl) ⟨577583, by rfl⟩ : syracuseStep 770111 = 1155167) B1155167
theorem B1458319 : Blo 511796 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B770207 : Blo 511796 770207 := bstep (se 1 (by rfl) ⟨577655, by rfl⟩ : syracuseStep 770207 = 1155311) B1155311
theorem B1458479 : Blo 511796 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B770459 : Blo 511796 770459 := bstep (se 1 (by rfl) ⟨577844, by rfl⟩ : syracuseStep 770459 = 1155689) B1155689
theorem B1458593 : Blo 511796 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B1458719 : Blo 511796 1458719 := bstep (se 1 (by rfl) ⟨1094039, by rfl⟩ : syracuseStep 1458719 = 2188079) B2188079
theorem B770879 : Blo 511796 770879 := bstep (se 1 (by rfl) ⟨578159, by rfl⟩ : syracuseStep 770879 = 1156319) B1156319
theorem B23774147 : Blo 511796 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B869359 : Blo 511796 869359 := bstep (se 1 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 869359 = 1304039) B1304039
theorem B869447 : Blo 511796 869447 := bstep (se 1 (by rfl) ⟨652085, by rfl⟩ : syracuseStep 869447 = 1304171) B1304171
theorem B1295635 : Blo 511796 1295635 := bstep (se 1 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 1295635 = 1943453) B1943453
theorem B869879 : Blo 511796 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B771611 : Blo 511796 771611 := bstep (se 1 (by rfl) ⟨578708, by rfl⟩ : syracuseStep 771611 = 1157417) B1157417
theorem B13321837 : Blo 511796 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B771743 : Blo 511796 771743 := bstep (se 1 (by rfl) ⟨578807, by rfl⟩ : syracuseStep 771743 = 1157615) B1157615
theorem B37472057 : Blo 511796 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B1460051 : Blo 511796 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B870311 : Blo 511796 870311 := bstep (se 1 (by rfl) ⟨652733, by rfl⟩ : syracuseStep 870311 = 1305467) B1305467
theorem B772031 : Blo 511796 772031 := bstep (se 1 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 772031 = 1158047) B1158047
theorem B1230803 : Blo 511796 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B6572177 : Blo 511796 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B7489739 : Blo 511796 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B1100027 : Blo 511796 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B4507907 : Blo 511796 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B16730549 : Blo 511796 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B576319 : Blo 511796 576319 := bstep (se 1 (by rfl) ⟨432239, by rfl⟩ : syracuseStep 576319 = 864479) B864479
theorem B773327 : Blo 511796 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B773447 : Blo 511796 773447 := bstep (se 1 (by rfl) ⟨580085, by rfl⟩ : syracuseStep 773447 = 1160171) B1160171
theorem B1461577 : Blo 511796 1461577 := bstep (se 2 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 1461577 = 1096183) B1096183
theorem B511911 : Blo 511796 511911 := bstep (se 1 (by rfl) ⟨383933, by rfl⟩ : syracuseStep 511911 = 767867) B767867
theorem B511935 : Blo 511796 511935 := bstep (se 1 (by rfl) ⟨383951, by rfl⟩ : syracuseStep 511935 = 767903) B767903
theorem B577471 : Blo 511796 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B512071 : Blo 511796 512071 := bstep (se 1 (by rfl) ⟨384053, by rfl⟩ : syracuseStep 512071 = 768107) B768107
theorem B512091 : Blo 511796 512091 := bstep (se 1 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 512091 = 768137) B768137
theorem B512191 : Blo 511796 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B1954115 : Blo 511796 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B512639 : Blo 511796 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B512671 : Blo 511796 512671 := bstep (se 1 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 512671 = 769007) B769007
theorem B512795 : Blo 511796 512795 := bstep (se 1 (by rfl) ⟨384596, by rfl⟩ : syracuseStep 512795 = 769193) B769193
theorem B12669779 : Blo 511796 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B1954799 : Blo 511796 1954799 := bstep (se 1 (by rfl) ⟨1466099, by rfl⟩ : syracuseStep 1954799 = 2932199) B2932199
theorem B513055 : Blo 511796 513055 := bstep (se 1 (by rfl) ⟨384791, by rfl⟩ : syracuseStep 513055 = 769583) B769583
theorem B513071 : Blo 511796 513071 := bstep (se 1 (by rfl) ⟨384803, by rfl⟩ : syracuseStep 513071 = 769607) B769607
theorem B513127 : Blo 511796 513127 := bstep (se 1 (by rfl) ⟨384845, by rfl⟩ : syracuseStep 513127 = 769691) B769691
theorem B513191 : Blo 511796 513191 := bstep (se 1 (by rfl) ⟨384893, by rfl⟩ : syracuseStep 513191 = 769787) B769787
theorem B513503 : Blo 511796 513503 := bstep (se 1 (by rfl) ⟨385127, by rfl⟩ : syracuseStep 513503 = 770255) B770255
theorem B6608567 : Blo 511796 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B972623 : Blo 511796 972623 := bstep (se 1 (by rfl) ⟨729467, by rfl⟩ : syracuseStep 972623 = 1458935) B1458935
theorem B513959 : Blo 511796 513959 := bstep (se 1 (by rfl) ⟨385469, by rfl⟩ : syracuseStep 513959 = 770939) B770939
theorem B1464311 : Blo 511796 1464311 := bstep (se 1 (by rfl) ⟨1098233, by rfl⟩ : syracuseStep 1464311 = 2196467) B2196467
theorem B514043 : Blo 511796 514043 := bstep (se 1 (by rfl) ⟨385532, by rfl⟩ : syracuseStep 514043 = 771065) B771065
theorem B514079 : Blo 511796 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B972911 : Blo 511796 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B514159 : Blo 511796 514159 := bstep (se 1 (by rfl) ⟨385619, by rfl⟩ : syracuseStep 514159 = 771239) B771239
theorem B514287 : Blo 511796 514287 := bstep (se 1 (by rfl) ⟨385715, by rfl⟩ : syracuseStep 514287 = 771431) B771431
theorem B1956089 : Blo 511796 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B9001543 : Blo 511796 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B514715 : Blo 511796 514715 := bstep (se 1 (by rfl) ⟨386036, by rfl⟩ : syracuseStep 514715 = 772073) B772073
theorem B514811 : Blo 511796 514811 := bstep (se 1 (by rfl) ⟨386108, by rfl⟩ : syracuseStep 514811 = 772217) B772217
theorem B514943 : Blo 511796 514943 := bstep (se 1 (by rfl) ⟨386207, by rfl⟩ : syracuseStep 514943 = 772415) B772415
theorem B1301417 : Blo 511796 1301417 := bstep (se 2 (by rfl) ⟨488031, by rfl⟩ : syracuseStep 1301417 = 976063) B976063
theorem B515039 : Blo 511796 515039 := bstep (se 1 (by rfl) ⟨386279, by rfl⟩ : syracuseStep 515039 = 772559) B772559
theorem B515067 : Blo 511796 515067 := bstep (se 1 (by rfl) ⟨386300, by rfl⟩ : syracuseStep 515067 = 772601) B772601
theorem B515099 : Blo 511796 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B3300389 : Blo 511796 3300389 := bstep (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) B618823
theorem B1465427 : Blo 511796 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B33414353 : Blo 511796 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B515391 : Blo 511796 515391 := bstep (se 1 (by rfl) ⟨386543, by rfl⟩ : syracuseStep 515391 = 773087) B773087
theorem B1957243 : Blo 511796 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B515687 : Blo 511796 515687 := bstep (se 1 (by rfl) ⟨386765, by rfl⟩ : syracuseStep 515687 = 773531) B773531
theorem B1728107 : Blo 511796 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1728755 : Blo 511796 1728755 := bstep (se 1 (by rfl) ⟨1296566, by rfl⟩ : syracuseStep 1728755 = 2593133) B2593133
theorem B1728809 : Blo 511796 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B6250891 : Blo 511796 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B8774243 : Blo 511796 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B2974495 : Blo 511796 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B3302491 : Blo 511796 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B975979 : Blo 511796 975979 := bstep (se 1 (by rfl) ⟨731984, by rfl⟩ : syracuseStep 975979 = 1463969) B1463969
theorem B877871 : Blo 511796 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B976367 : Blo 511796 976367 := bstep (se 1 (by rfl) ⟨732275, by rfl⟩ : syracuseStep 976367 = 1464551) B1464551
theorem B1763129 : Blo 511796 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B4155259 : Blo 511796 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B977179 : Blo 511796 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B1731239 : Blo 511796 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B1731887 : Blo 511796 1731887 := bstep (se 1 (by rfl) ⟨1298915, by rfl⟩ : syracuseStep 1731887 = 2597831) B2597831
theorem B1733021 : Blo 511796 1733021 := bstep (se 3 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 1733021 = 649883) B649883
theorem B2192777 : Blo 511796 2192777 := bstep (se 2 (by rfl) ⟨822291, by rfl⟩ : syracuseStep 2192777 = 1644583) B1644583
theorem B4388489 : Blo 511796 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B8451793 : Blo 511796 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B3700541 : Blo 511796 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B1734695 : Blo 511796 1734695 := bstep (se 1 (by rfl) ⟨1301021, by rfl⟩ : syracuseStep 1734695 = 2602043) B2602043
theorem B522343 : Blo 511796 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1734911 : Blo 511796 1734911 := bstep (se 1 (by rfl) ⟨1301183, by rfl⟩ : syracuseStep 1734911 = 2602367) B2602367
theorem B3897719 : Blo 511796 3897719 := bstep (se 1 (by rfl) ⟨2923289, by rfl⟩ : syracuseStep 3897719 = 5846579) B5846579
theorem B1735613 : Blo 511796 1735613 := bstep (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) B650855
theorem B1735775 : Blo 511796 1735775 := bstep (se 1 (by rfl) ⟨1301831, by rfl⟩ : syracuseStep 1735775 = 2603663) B2603663
theorem B51412151 : Blo 511796 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B3701983 : Blo 511796 3701983 := bstep (se 1 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 3701983 = 5552975) B5552975
theorem B3965993 : Blo 511796 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B820535 : Blo 511796 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B17762449 : Blo 511796 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B16648537 : Blo 511796 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B5540345 : Blo 511796 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B22482359 : Blo 511796 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B5574595 : Blo 511796 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B4166225 : Blo 511796 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B2200259 : Blo 511796 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B1152071 : Blo 511796 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B6034571 : Blo 511796 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1152503 : Blo 511796 1152503 := bstep (se 1 (by rfl) ⟨864377, by rfl⟩ : syracuseStep 1152503 = 1728755) B1728755
theorem B1152539 : Blo 511796 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B2594429 : Blo 511796 2594429 := bstep (se 3 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 2594429 = 972911) B972911
theorem B5576327 : Blo 511796 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B1153097 : Blo 511796 1153097 := bstep (se 2 (by rfl) ⟨432411, by rfl⟩ : syracuseStep 1153097 = 864823) B864823
theorem B1154159 : Blo 511796 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B1154591 : Blo 511796 1154591 := bstep (se 1 (by rfl) ⟨865943, by rfl⟩ : syracuseStep 1154591 = 1731887) B1731887
theorem B696457 : Blo 511796 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B1155347 : Blo 511796 1155347 := bstep (se 1 (by rfl) ⟨866510, by rfl⟩ : syracuseStep 1155347 = 1733021) B1733021
theorem B12002057 : Blo 511796 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B2925659 : Blo 511796 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B10527853 : Blo 511796 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B2467027 : Blo 511796 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1156463 : Blo 511796 1156463 := bstep (se 1 (by rfl) ⟨867347, by rfl⟩ : syracuseStep 1156463 = 1734695) B1734695
theorem B1156607 : Blo 511796 1156607 := bstep (se 1 (by rfl) ⟨867455, by rfl⟩ : syracuseStep 1156607 = 1734911) B1734911
theorem B2598479 : Blo 511796 2598479 := bstep (se 1 (by rfl) ⟨1948859, by rfl⟩ : syracuseStep 2598479 = 3897719) B3897719
theorem B7415387 : Blo 511796 7415387 := bstep (se 1 (by rfl) ⟨5561540, by rfl⟩ : syracuseStep 7415387 = 11123081) B11123081
theorem B16721711 : Blo 511796 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B1157075 : Blo 511796 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B1157183 : Blo 511796 1157183 := bstep (se 1 (by rfl) ⟨867887, by rfl⟩ : syracuseStep 1157183 = 1735775) B1735775
theorem B3287243 : Blo 511796 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B1944425 : Blo 511796 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B1158011 : Blo 511796 1158011 := bstep (se 1 (by rfl) ⟨868508, by rfl⟩ : syracuseStep 1158011 = 1737017) B1737017
theorem B8334521 : Blo 511796 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B2928257 : Blo 511796 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B24981371 : Blo 511796 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B1159145 : Blo 511796 1159145 := bstep (se 2 (by rfl) ⟨434679, by rfl⟩ : syracuseStep 1159145 = 869359) B869359
theorem B1159199 : Blo 511796 1159199 := bstep (se 1 (by rfl) ⟨869399, by rfl⟩ : syracuseStep 1159199 = 1738799) B1738799
theorem B4403321 : Blo 511796 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B4993159 : Blo 511796 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B1159343 : Blo 511796 1159343 := bstep (se 1 (by rfl) ⟨869507, by rfl⟩ : syracuseStep 1159343 = 1739015) B1739015
theorem B1945883 : Blo 511796 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B11153699 : Blo 511796 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B1094953 : Blo 511796 1094953 := bstep (se 2 (by rfl) ⟨410607, by rfl⟩ : syracuseStep 1094953 = 821215) B821215
theorem B1160495 : Blo 511796 1160495 := bstep (se 1 (by rfl) ⟨870371, by rfl⟩ : syracuseStep 1160495 = 1740743) B1740743
theorem B768425 : Blo 511796 768425 := bstep (se 2 (by rfl) ⟨288159, by rfl⟩ : syracuseStep 768425 = 576319) B576319
theorem B4405711 : Blo 511796 4405711 := bstep (se 1 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 4405711 = 6608567) B6608567
theorem B768479 : Blo 511796 768479 := bstep (se 1 (by rfl) ⟨576359, by rfl⟩ : syracuseStep 768479 = 1152719) B1152719
theorem B768839 : Blo 511796 768839 := bstep (se 1 (by rfl) ⟨576629, by rfl⟩ : syracuseStep 768839 = 1153259) B1153259
theorem B1948769 : Blo 511796 1948769 := bstep (se 2 (by rfl) ⟨730788, by rfl⟩ : syracuseStep 1948769 = 1461577) B1461577
theorem B769151 : Blo 511796 769151 := bstep (se 1 (by rfl) ⟨576863, by rfl⟩ : syracuseStep 769151 = 1153727) B1153727
theorem B867611 : Blo 511796 867611 := bstep (se 1 (by rfl) ⟨650708, by rfl⟩ : syracuseStep 867611 = 1301417) B1301417
theorem B769703 : Blo 511796 769703 := bstep (se 1 (by rfl) ⟨577277, by rfl⟩ : syracuseStep 769703 = 1154555) B1154555
theorem B8306363 : Blo 511796 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B769775 : Blo 511796 769775 := bstep (se 1 (by rfl) ⟨577331, by rfl⟩ : syracuseStep 769775 = 1154663) B1154663
theorem B769961 : Blo 511796 769961 := bstep (se 2 (by rfl) ⟨288735, by rfl⟩ : syracuseStep 769961 = 577471) B577471
theorem B5849495 : Blo 511796 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B770615 : Blo 511796 770615 := bstep (se 1 (by rfl) ⟨577961, by rfl⟩ : syracuseStep 770615 = 1155923) B1155923
theorem B2933405 : Blo 511796 2933405 := bstep (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) B1100027
theorem B770855 : Blo 511796 770855 := bstep (se 1 (by rfl) ⟨578141, by rfl⟩ : syracuseStep 770855 = 1156283) B1156283
theorem B771023 : Blo 511796 771023 := bstep (se 1 (by rfl) ⟨578267, by rfl⟩ : syracuseStep 771023 = 1156535) B1156535
theorem B771551 : Blo 511796 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B772187 : Blo 511796 772187 := bstep (se 1 (by rfl) ⟨579140, by rfl⟩ : syracuseStep 772187 = 1158281) B1158281
theorem B2607227 : Blo 511796 2607227 := bstep (se 1 (by rfl) ⟨1955420, by rfl⟩ : syracuseStep 2607227 = 3910841) B3910841
theorem B772223 : Blo 511796 772223 := bstep (se 1 (by rfl) ⟨579167, by rfl⟩ : syracuseStep 772223 = 1158335) B1158335
theorem B1951883 : Blo 511796 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B772847 : Blo 511796 772847 := bstep (se 1 (by rfl) ⟨579635, by rfl⟩ : syracuseStep 772847 = 1159271) B1159271
theorem B1297691 : Blo 511796 1297691 := bstep (se 1 (by rfl) ⟨973268, by rfl⟩ : syracuseStep 1297691 = 1946537) B1946537
theorem B1461851 : Blo 511796 1461851 := bstep (se 1 (by rfl) ⟨1096388, by rfl⟩ : syracuseStep 1461851 = 2192777) B2192777
theorem B1953659 : Blo 511796 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B10506341 : Blo 511796 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B4935977 : Blo 511796 4935977 := bstep (se 2 (by rfl) ⟨1850991, by rfl⟩ : syracuseStep 4935977 = 3701983) B3701983
theorem B2609657 : Blo 511796 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B578047 : Blo 511796 578047 := bstep (se 1 (by rfl) ⟨433535, by rfl⟩ : syracuseStep 578047 = 867071) B867071
theorem B512603 : Blo 511796 512603 := bstep (se 1 (by rfl) ⟨384452, by rfl⟩ : syracuseStep 512603 = 768905) B768905
theorem B971689 : Blo 511796 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B1954813 : Blo 511796 1954813 := bstep (se 3 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 1954813 = 733055) B733055
theorem B513115 : Blo 511796 513115 := bstep (se 1 (by rfl) ⟨384836, by rfl⟩ : syracuseStep 513115 = 769673) B769673
theorem B513407 : Blo 511796 513407 := bstep (se 1 (by rfl) ⟨385055, by rfl⟩ : syracuseStep 513407 = 770111) B770111
theorem B513471 : Blo 511796 513471 := bstep (se 1 (by rfl) ⟨385103, by rfl⟩ : syracuseStep 513471 = 770207) B770207
theorem B972319 : Blo 511796 972319 := bstep (se 1 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 972319 = 1458479) B1458479
theorem B513639 : Blo 511796 513639 := bstep (se 1 (by rfl) ⟨385229, by rfl⟩ : syracuseStep 513639 = 770459) B770459
theorem B972395 : Blo 511796 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B972479 : Blo 511796 972479 := bstep (se 1 (by rfl) ⟨729359, by rfl⟩ : syracuseStep 972479 = 1458719) B1458719
theorem B513919 : Blo 511796 513919 := bstep (se 1 (by rfl) ⟨385439, by rfl⟩ : syracuseStep 513919 = 770879) B770879
theorem B15849431 : Blo 511796 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B579631 : Blo 511796 579631 := bstep (se 1 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 579631 = 869447) B869447
theorem B579919 : Blo 511796 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B514407 : Blo 511796 514407 := bstep (se 1 (by rfl) ⟨385805, by rfl⟩ : syracuseStep 514407 = 771611) B771611
theorem B514495 : Blo 511796 514495 := bstep (se 1 (by rfl) ⟨385871, by rfl⟩ : syracuseStep 514495 = 771743) B771743
theorem B973367 : Blo 511796 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B580207 : Blo 511796 580207 := bstep (se 1 (by rfl) ⟨435155, by rfl⟩ : syracuseStep 580207 = 870311) B870311
theorem B514687 : Blo 511796 514687 := bstep (se 1 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 514687 = 772031) B772031
theorem B4381451 : Blo 511796 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1301305 : Blo 511796 1301305 := bstep (se 2 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 1301305 = 975979) B975979
theorem B1727513 : Blo 511796 1727513 := bstep (se 2 (by rfl) ⟨647817, by rfl⟩ : syracuseStep 1727513 = 1295635) B1295635
theorem B1727675 : Blo 511796 1727675 := bstep (se 1 (by rfl) ⟨1295756, by rfl⟩ : syracuseStep 1727675 = 2591513) B2591513
theorem B515551 : Blo 511796 515551 := bstep (se 1 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 515551 = 773327) B773327
theorem B515631 : Blo 511796 515631 := bstep (se 1 (by rfl) ⟨386723, by rfl⟩ : syracuseStep 515631 = 773447) B773447
theorem B2645903 : Blo 511796 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B1302743 : Blo 511796 1302743 := bstep (se 1 (by rfl) ⟨977057, by rfl⟩ : syracuseStep 1302743 = 1954115) B1954115
theorem B1302905 : Blo 511796 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B1499561 : Blo 511796 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B8446519 : Blo 511796 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B1303199 : Blo 511796 1303199 := bstep (se 1 (by rfl) ⟨977399, by rfl⟩ : syracuseStep 1303199 = 1954799) B1954799
theorem B648415 : Blo 511796 648415 := bstep (se 1 (by rfl) ⟨486311, by rfl⟩ : syracuseStep 648415 = 972623) B972623
theorem B976207 : Blo 511796 976207 := bstep (se 1 (by rfl) ⟨732155, by rfl⟩ : syracuseStep 976207 = 1464311) B1464311
theorem B1304059 : Blo 511796 1304059 := bstep (se 1 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 1304059 = 1956089) B1956089
theorem B1238761 : Blo 511796 1238761 := bstep (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) B929071
theorem B1730375 : Blo 511796 1730375 := bstep (se 1 (by rfl) ⟨1297781, by rfl⟩ : syracuseStep 1730375 = 2595563) B2595563
theorem B976951 : Blo 511796 976951 := bstep (se 1 (by rfl) ⟨732713, by rfl⟩ : syracuseStep 976951 = 1465427) B1465427
theorem B192997505 : Blo 511796 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B22276235 : Blo 511796 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B12021085 : Blo 511796 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B585247 : Blo 511796 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B650911 : Blo 511796 650911 := bstep (se 1 (by rfl) ⟨488183, by rfl⟩ : syracuseStep 650911 = 976367) B976367
theorem B1175419 : Blo 511796 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B6582323 : Blo 511796 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B3470161 : Blo 511796 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B11269057 : Blo 511796 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B21133871 : Blo 511796 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B6650515 : Blo 511796 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B34274767 : Blo 511796 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B1736531 : Blo 511796 1736531 := bstep (se 1 (by rfl) ⟨1302398, by rfl⟩ : syracuseStep 1736531 = 2604797) B2604797
theorem B1736639 : Blo 511796 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B3899663 : Blo 511796 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B1738151 : Blo 511796 1738151 := bstep (se 1 (by rfl) ⟨1303613, by rfl⟩ : syracuseStep 1738151 = 2607227) B2607227
theorem B1738745 : Blo 511796 1738745 := bstep (se 2 (by rfl) ⟨652029, by rfl⟩ : syracuseStep 1738745 = 1304059) B1304059
theorem B1739771 : Blo 511796 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B8752373 : Blo 511796 8752373 := bstep (se 5 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 8752373 = 820535) B820535
theorem B16028113 : Blo 511796 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B2920967 : Blo 511796 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1151675 : Blo 511796 1151675 := bstep (se 1 (by rfl) ⟨863756, by rfl⟩ : syracuseStep 1151675 = 1727513) B1727513
theorem B1151783 : Blo 511796 1151783 := bstep (se 1 (by rfl) ⟨863837, by rfl⟩ : syracuseStep 1151783 = 1727675) B1727675
theorem B6657545 : Blo 511796 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B514660013 : Blo 511796 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B8001371 : Blo 511796 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B4626881 : Blo 511796 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B11147807 : Blo 511796 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B1153583 : Blo 511796 1153583 := bstep (se 1 (by rfl) ⟨865187, by rfl⟩ : syracuseStep 1153583 = 1730375) B1730375
theorem B14850823 : Blo 511796 14850823 := bstep (se 1 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 14850823 = 22276235) B22276235
theorem B16654247 : Blo 511796 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B5874281 : Blo 511796 5874281 := bstep (se 2 (by rfl) ⟨2202855, by rfl⟩ : syracuseStep 5874281 = 4405711) B4405711
theorem B7055741 : Blo 511796 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B1157687 : Blo 511796 1157687 := bstep (se 1 (by rfl) ⟨868265, by rfl⟩ : syracuseStep 1157687 = 1736531) B1736531
theorem B1157759 : Blo 511796 1157759 := bstep (se 1 (by rfl) ⟨868319, by rfl⟩ : syracuseStep 1157759 = 1736639) B1736639
theorem B3714437 : Blo 511796 3714437 := bstep (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) B696457
theorem B14037137 : Blo 511796 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B3289369 : Blo 511796 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B864553 : Blo 511796 864553 := bstep (se 2 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 864553 = 648415) B648415
theorem B865127 : Blo 511796 865127 := bstep (se 1 (by rfl) ⟨648845, by rfl⟩ : syracuseStep 865127 = 1297691) B1297691
theorem B14988239 : Blo 511796 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B1651681 : Blo 511796 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B3290651 : Blo 511796 3290651 := bstep (se 1 (by rfl) ⟨2467988, by rfl⟩ : syracuseStep 3290651 = 4935977) B4935977
theorem B22198049 : Blo 511796 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B768047 : Blo 511796 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B768335 : Blo 511796 768335 := bstep (se 1 (by rfl) ⟨576251, by rfl⟩ : syracuseStep 768335 = 1152503) B1152503
theorem B768359 : Blo 511796 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B3717551 : Blo 511796 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B10566287 : Blo 511796 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B768731 : Blo 511796 768731 := bstep (se 1 (by rfl) ⟨576548, by rfl⟩ : syracuseStep 768731 = 1153097) B1153097
theorem B769439 : Blo 511796 769439 := bstep (se 1 (by rfl) ⟨577079, by rfl⟩ : syracuseStep 769439 = 1154159) B1154159
theorem B867881 : Blo 511796 867881 := bstep (se 2 (by rfl) ⟨325455, by rfl⟩ : syracuseStep 867881 = 650911) B650911
theorem B769727 : Blo 511796 769727 := bstep (se 1 (by rfl) ⟨577295, by rfl⟩ : syracuseStep 769727 = 1154591) B1154591
theorem B868495 : Blo 511796 868495 := bstep (se 1 (by rfl) ⟨651371, by rfl⟩ : syracuseStep 868495 = 1302743) B1302743
theorem B770231 : Blo 511796 770231 := bstep (se 1 (by rfl) ⟨577673, by rfl⟩ : syracuseStep 770231 = 1155347) B1155347
theorem B868603 : Blo 511796 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B999707 : Blo 511796 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B868799 : Blo 511796 868799 := bstep (se 1 (by rfl) ⟨651599, by rfl⟩ : syracuseStep 868799 = 1303199) B1303199
theorem B770729 : Blo 511796 770729 := bstep (se 2 (by rfl) ⟨289023, by rfl⟩ : syracuseStep 770729 = 578047) B578047
theorem B1950439 : Blo 511796 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B770975 : Blo 511796 770975 := bstep (se 1 (by rfl) ⟨578231, by rfl⟩ : syracuseStep 770975 = 1156463) B1156463
theorem B771071 : Blo 511796 771071 := bstep (se 1 (by rfl) ⟨578303, by rfl⟩ : syracuseStep 771071 = 1156607) B1156607
theorem B1295585 : Blo 511796 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B15025409 : Blo 511796 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B771383 : Blo 511796 771383 := bstep (se 1 (by rfl) ⟨578537, by rfl⟩ : syracuseStep 771383 = 1157075) B1157075
theorem B2606417 : Blo 511796 2606417 := bstep (se 2 (by rfl) ⟨977406, by rfl⟩ : syracuseStep 2606417 = 1954813) B1954813
theorem B771455 : Blo 511796 771455 := bstep (se 1 (by rfl) ⟨578591, by rfl⟩ : syracuseStep 771455 = 1157183) B1157183
theorem B1459937 : Blo 511796 1459937 := bstep (se 2 (by rfl) ⟨547476, by rfl⟩ : syracuseStep 1459937 = 1094953) B1094953
theorem B1296283 : Blo 511796 1296283 := bstep (se 1 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 1296283 = 1944425) B1944425
theorem B772007 : Blo 511796 772007 := bstep (se 1 (by rfl) ⟨579005, by rfl⟩ : syracuseStep 772007 = 1158011) B1158011
theorem B1296425 : Blo 511796 1296425 := bstep (se 2 (by rfl) ⟨486159, by rfl⟩ : syracuseStep 1296425 = 972319) B972319
theorem B5556347 : Blo 511796 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1952171 : Blo 511796 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B772763 : Blo 511796 772763 := bstep (se 1 (by rfl) ⟨579572, by rfl⟩ : syracuseStep 772763 = 1159145) B1159145
theorem B772799 : Blo 511796 772799 := bstep (se 1 (by rfl) ⟨579599, by rfl⟩ : syracuseStep 772799 = 1159199) B1159199
theorem B772841 : Blo 511796 772841 := bstep (se 2 (by rfl) ⟨289815, by rfl⟩ : syracuseStep 772841 = 579631) B579631
theorem B2935547 : Blo 511796 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B772895 : Blo 511796 772895 := bstep (se 1 (by rfl) ⟨579671, by rfl⟩ : syracuseStep 772895 = 1159343) B1159343
theorem B1297255 : Blo 511796 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B773225 : Blo 511796 773225 := bstep (se 2 (by rfl) ⟨289959, by rfl⟩ : syracuseStep 773225 = 579919) B579919
theorem B773609 : Blo 511796 773609 := bstep (se 2 (by rfl) ⟨290103, by rfl⟩ : syracuseStep 773609 = 580207) B580207
theorem B8867353 : Blo 511796 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B773663 : Blo 511796 773663 := bstep (se 1 (by rfl) ⟨580247, by rfl⟩ : syracuseStep 773663 = 1160495) B1160495
theorem B512283 : Blo 511796 512283 := bstep (se 1 (by rfl) ⟨384212, by rfl⟩ : syracuseStep 512283 = 768425) B768425
theorem B512319 : Blo 511796 512319 := bstep (se 1 (by rfl) ⟨384239, by rfl⟩ : syracuseStep 512319 = 768479) B768479
theorem B512559 : Blo 511796 512559 := bstep (se 1 (by rfl) ⟨384419, by rfl⟩ : syracuseStep 512559 = 768839) B768839
theorem B45699689 : Blo 511796 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B1299179 : Blo 511796 1299179 := bstep (se 1 (by rfl) ⟨974384, by rfl⟩ : syracuseStep 1299179 = 1948769) B1948769
theorem B512767 : Blo 511796 512767 := bstep (se 1 (by rfl) ⟨384575, by rfl⟩ : syracuseStep 512767 = 769151) B769151
theorem B578407 : Blo 511796 578407 := bstep (se 1 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 578407 = 867611) B867611
theorem B513135 : Blo 511796 513135 := bstep (se 1 (by rfl) ⟨384851, by rfl⟩ : syracuseStep 513135 = 769703) B769703
theorem B513183 : Blo 511796 513183 := bstep (se 1 (by rfl) ⟨384887, by rfl⟩ : syracuseStep 513183 = 769775) B769775
theorem B513307 : Blo 511796 513307 := bstep (se 1 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 513307 = 769961) B769961
theorem B513743 : Blo 511796 513743 := bstep (se 1 (by rfl) ⟨385307, by rfl⟩ : syracuseStep 513743 = 770615) B770615
theorem B1955603 : Blo 511796 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B513903 : Blo 511796 513903 := bstep (se 1 (by rfl) ⟨385427, by rfl⟩ : syracuseStep 513903 = 770855) B770855
theorem B514015 : Blo 511796 514015 := bstep (se 1 (by rfl) ⟨385511, by rfl⟩ : syracuseStep 514015 = 771023) B771023
theorem B2643995 : Blo 511796 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B11262025 : Blo 511796 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B514367 : Blo 511796 514367 := bstep (se 1 (by rfl) ⟨385775, by rfl⟩ : syracuseStep 514367 = 771551) B771551
theorem B514791 : Blo 511796 514791 := bstep (se 1 (by rfl) ⟨386093, by rfl⟩ : syracuseStep 514791 = 772187) B772187
theorem B514815 : Blo 511796 514815 := bstep (se 1 (by rfl) ⟨386111, by rfl⟩ : syracuseStep 514815 = 772223) B772223
theorem B1301255 : Blo 511796 1301255 := bstep (se 1 (by rfl) ⟨975941, by rfl⟩ : syracuseStep 1301255 = 1951883) B1951883
theorem B3693563 : Blo 511796 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B1301609 : Blo 511796 1301609 := bstep (se 2 (by rfl) ⟨488103, by rfl⟩ : syracuseStep 1301609 = 976207) B976207
theorem B515231 : Blo 511796 515231 := bstep (se 1 (by rfl) ⟨386423, by rfl⟩ : syracuseStep 515231 = 772847) B772847
theorem B974567 : Blo 511796 974567 := bstep (se 1 (by rfl) ⟨730925, by rfl⟩ : syracuseStep 974567 = 1461851) B1461851
theorem B1302439 : Blo 511796 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B7004227 : Blo 511796 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B1302601 : Blo 511796 1302601 := bstep (se 2 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 1302601 = 976951) B976951
theorem B23683265 : Blo 511796 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B2777483 : Blo 511796 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B1466839 : Blo 511796 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B4023047 : Blo 511796 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B648263 : Blo 511796 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B1729619 : Blo 511796 1729619 := bstep (se 1 (by rfl) ⟨1297214, by rfl⟩ : syracuseStep 1729619 = 2594429) B2594429
theorem B648319 : Blo 511796 648319 := bstep (se 1 (by rfl) ⟨486239, by rfl⟩ : syracuseStep 648319 = 972479) B972479
theorem B648911 : Blo 511796 648911 := bstep (se 1 (by rfl) ⟨486683, by rfl⟩ : syracuseStep 648911 = 973367) B973367
theorem B780329 : Blo 511796 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1567225 : Blo 511796 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B7432793 : Blo 511796 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B1732319 : Blo 511796 1732319 := bstep (se 1 (by rfl) ⟨1299239, by rfl⟩ : syracuseStep 1732319 = 2598479) B2598479
theorem B4943591 : Blo 511796 4943591 := bstep (se 1 (by rfl) ⟨3707693, by rfl⟩ : syracuseStep 4943591 = 7415387) B7415387
theorem B2191495 : Blo 511796 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B4388215 : Blo 511796 4388215 := bstep (se 1 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 4388215 = 6582323) B6582323
theorem B7435799 : Blo 511796 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B1735073 : Blo 511796 1735073 := bstep (se 2 (by rfl) ⟨650652, by rfl⟩ : syracuseStep 1735073 = 1301305) B1301305
theorem B14089247 : Blo 511796 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B5537575 : Blo 511796 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B9338969 : Blo 511796 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1736801 : Blo 511796 1736801 := bstep (se 2 (by rfl) ⟨651300, by rfl⟩ : syracuseStep 1736801 = 1302601) B1302601
theorem B1737611 : Blo 511796 1737611 := bstep (se 1 (by rfl) ⟨1303208, by rfl⟩ : syracuseStep 1737611 = 2606417) B2606417
theorem B3704231 : Blo 511796 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B5834915 : Blo 511796 5834915 := bstep (se 1 (by rfl) ⟨4376186, by rfl⟩ : syracuseStep 5834915 = 8752373) B8752373
theorem B3084587 : Blo 511796 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B2462375 : Blo 511796 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B2921993 : Blo 511796 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B1152737 : Blo 511796 1152737 := bstep (se 2 (by rfl) ⟨432276, by rfl⟩ : syracuseStep 1152737 = 864553) B864553
theorem B21370817 : Blo 511796 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B1153079 : Blo 511796 1153079 := bstep (se 1 (by rfl) ⟨864809, by rfl⟩ : syracuseStep 1153079 = 1729619) B1729619
theorem B2202241 : Blo 511796 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B4955195 : Blo 511796 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B1154879 : Blo 511796 1154879 := bstep (se 1 (by rfl) ⟨866159, by rfl⟩ : syracuseStep 1154879 = 1732319) B1732319
theorem B15016033 : Blo 511796 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B19801097 : Blo 511796 19801097 := bstep (se 2 (by rfl) ⟨7425411, by rfl⟩ : syracuseStep 19801097 = 14850823) B14850823
theorem B9905165 : Blo 511796 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B4957199 : Blo 511796 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B1156715 : Blo 511796 1156715 := bstep (se 1 (by rfl) ⟨867536, by rfl⟩ : syracuseStep 1156715 = 1735073) B1735073
theorem B7383433 : Blo 511796 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B2599775 : Blo 511796 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B1157993 : Blo 511796 1157993 := bstep (se 2 (by rfl) ⟨434247, by rfl⟩ : syracuseStep 1157993 = 868495) B868495
theorem B1158137 : Blo 511796 1158137 := bstep (se 2 (by rfl) ⟨434301, by rfl⟩ : syracuseStep 1158137 = 868603) B868603
theorem B2665885 : Blo 511796 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B863723 : Blo 511796 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B1158767 : Blo 511796 1158767 := bstep (se 1 (by rfl) ⟨869075, by rfl⟩ : syracuseStep 1158767 = 1738151) B1738151
theorem B2600585 : Blo 511796 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B1159163 : Blo 511796 1159163 := bstep (se 1 (by rfl) ⟨869372, by rfl⟩ : syracuseStep 1159163 = 1738745) B1738745
theorem B864283 : Blo 511796 864283 := bstep (se 1 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 864283 = 1296425) B1296425
theorem B864425 : Blo 511796 864425 := bstep (se 2 (by rfl) ⟨324159, by rfl⟩ : syracuseStep 864425 = 648319) B648319
theorem B1159847 : Blo 511796 1159847 := bstep (se 1 (by rfl) ⟨869885, by rfl⟩ : syracuseStep 1159847 = 1739771) B1739771
theorem B10728125 : Blo 511796 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1947311 : Blo 511796 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B767783 : Blo 511796 767783 := bstep (se 1 (by rfl) ⟨575837, by rfl⟩ : syracuseStep 767783 = 1151675) B1151675
theorem B866119 : Blo 511796 866119 := bstep (se 1 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 866119 = 1299179) B1299179
theorem B767855 : Blo 511796 767855 := bstep (se 1 (by rfl) ⟨575891, by rfl⟩ : syracuseStep 767855 = 1151783) B1151783
theorem B4438363 : Blo 511796 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B769055 : Blo 511796 769055 := bstep (se 1 (by rfl) ⟨576791, by rfl⟩ : syracuseStep 769055 = 1153583) B1153583
theorem B867503 : Blo 511796 867503 := bstep (se 1 (by rfl) ⟨650627, by rfl⟩ : syracuseStep 867503 = 1301255) B1301255
theorem B867739 : Blo 511796 867739 := bstep (se 1 (by rfl) ⟨650804, by rfl⟩ : syracuseStep 867739 = 1301609) B1301609
theorem B1851655 : Blo 511796 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B3916187 : Blo 511796 3916187 := bstep (se 1 (by rfl) ⟨2937140, by rfl⟩ : syracuseStep 3916187 = 5874281) B5874281
theorem B771209 : Blo 511796 771209 := bstep (se 2 (by rfl) ⟨289203, by rfl⟩ : syracuseStep 771209 = 578407) B578407
theorem B4703827 : Blo 511796 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B771791 : Blo 511796 771791 := bstep (se 1 (by rfl) ⟨578843, by rfl⟩ : syracuseStep 771791 = 1157687) B1157687
theorem B771839 : Blo 511796 771839 := bstep (se 1 (by rfl) ⟨578879, by rfl⟩ : syracuseStep 771839 = 1157759) B1157759
theorem B5850953 : Blo 511796 5850953 := bstep (se 2 (by rfl) ⟨2194107, by rfl⟩ : syracuseStep 5850953 = 4388215) B4388215
theorem B3295727 : Blo 511796 3295727 := bstep (se 1 (by rfl) ⟨2471795, by rfl⟩ : syracuseStep 3295727 = 4943591) B4943591
theorem B9358091 : Blo 511796 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B576751 : Blo 511796 576751 := bstep (se 1 (by rfl) ⟨432563, by rfl⟩ : syracuseStep 576751 = 865127) B865127
theorem B14798699 : Blo 511796 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B512031 : Blo 511796 512031 := bstep (se 1 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 512031 = 768047) B768047
theorem B512223 : Blo 511796 512223 := bstep (se 1 (by rfl) ⟨384167, by rfl⟩ : syracuseStep 512223 = 768335) B768335
theorem B512239 : Blo 511796 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B2478367 : Blo 511796 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B512487 : Blo 511796 512487 := bstep (se 1 (by rfl) ⟨384365, by rfl⟩ : syracuseStep 512487 = 768731) B768731
theorem B9392831 : Blo 511796 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B512959 : Blo 511796 512959 := bstep (se 1 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 512959 = 769439) B769439
theorem B578587 : Blo 511796 578587 := bstep (se 1 (by rfl) ⟨433940, by rfl⟩ : syracuseStep 578587 = 867881) B867881
theorem B513151 : Blo 511796 513151 := bstep (se 1 (by rfl) ⟨384863, by rfl⟩ : syracuseStep 513151 = 769727) B769727
theorem B513487 : Blo 511796 513487 := bstep (se 1 (by rfl) ⟨385115, by rfl⟩ : syracuseStep 513487 = 770231) B770231
theorem B579199 : Blo 511796 579199 := bstep (se 1 (by rfl) ⟨434399, by rfl⟩ : syracuseStep 579199 = 868799) B868799
theorem B513819 : Blo 511796 513819 := bstep (se 1 (by rfl) ⟨385364, by rfl⟩ : syracuseStep 513819 = 770729) B770729
theorem B513983 : Blo 511796 513983 := bstep (se 1 (by rfl) ⟨385487, by rfl⟩ : syracuseStep 513983 = 770975) B770975
theorem B1955785 : Blo 511796 1955785 := bstep (se 2 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 1955785 = 1466839) B1466839
theorem B514047 : Blo 511796 514047 := bstep (se 1 (by rfl) ⟨385535, by rfl⟩ : syracuseStep 514047 = 771071) B771071
theorem B10016939 : Blo 511796 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B514255 : Blo 511796 514255 := bstep (se 1 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 514255 = 771383) B771383
theorem B514303 : Blo 511796 514303 := bstep (se 1 (by rfl) ⟨385727, by rfl⟩ : syracuseStep 514303 = 771455) B771455
theorem B973291 : Blo 511796 973291 := bstep (se 1 (by rfl) ⟨729968, by rfl⟩ : syracuseStep 973291 = 1459937) B1459937
theorem B514671 : Blo 511796 514671 := bstep (se 1 (by rfl) ⟨386003, by rfl⟩ : syracuseStep 514671 = 772007) B772007
theorem B1301447 : Blo 511796 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B515175 : Blo 511796 515175 := bstep (se 1 (by rfl) ⟨386381, by rfl⟩ : syracuseStep 515175 = 772763) B772763
theorem B515199 : Blo 511796 515199 := bstep (se 1 (by rfl) ⟨386399, by rfl⟩ : syracuseStep 515199 = 772799) B772799
theorem B515227 : Blo 511796 515227 := bstep (se 1 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 515227 = 772841) B772841
theorem B1957031 : Blo 511796 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B515263 : Blo 511796 515263 := bstep (se 1 (by rfl) ⟨386447, by rfl⟩ : syracuseStep 515263 = 772895) B772895
theorem B515483 : Blo 511796 515483 := bstep (se 1 (by rfl) ⟨386612, by rfl⟩ : syracuseStep 515483 = 773225) B773225
theorem B515739 : Blo 511796 515739 := bstep (se 1 (by rfl) ⟨386804, by rfl⟩ : syracuseStep 515739 = 773609) B773609
theorem B515775 : Blo 511796 515775 := bstep (se 1 (by rfl) ⟨386831, by rfl⟩ : syracuseStep 515775 = 773663) B773663
theorem B1728377 : Blo 511796 1728377 := bstep (se 2 (by rfl) ⟨648141, by rfl⟩ : syracuseStep 1728377 = 1296283) B1296283
theorem B1728701 : Blo 511796 1728701 := bstep (se 3 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 1728701 = 648263) B648263
theorem B30466459 : Blo 511796 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B2089633 : Blo 511796 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B343106675 : Blo 511796 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B1729673 : Blo 511796 1729673 := bstep (se 2 (by rfl) ⟨648627, by rfl⟩ : syracuseStep 1729673 = 1297255) B1297255
theorem B1303735 : Blo 511796 1303735 := bstep (se 1 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 1303735 = 1955603) B1955603
theorem B5334247 : Blo 511796 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B1762663 : Blo 511796 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B7431871 : Blo 511796 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1730429 : Blo 511796 1730429 := bstep (se 3 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 1730429 = 648911) B648911
theorem B11823137 : Blo 511796 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B649711 : Blo 511796 649711 := bstep (se 1 (by rfl) ⟨487283, by rfl⟩ : syracuseStep 649711 = 974567) B974567
theorem B11102831 : Blo 511796 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B15788843 : Blo 511796 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B4385825 : Blo 511796 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B520219 : Blo 511796 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B9992159 : Blo 511796 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B2193767 : Blo 511796 2193767 := bstep (se 1 (by rfl) ⟨1645325, by rfl⟩ : syracuseStep 2193767 = 3290651) B3290651
theorem B7044191 : Blo 511796 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B1736585 : Blo 511796 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B6225979 : Blo 511796 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B20021377 : Blo 511796 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B2786177 : Blo 511796 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B3900635 : Blo 511796 3900635 := bstep (se 1 (by rfl) ⟨2925476, by rfl⟩ : syracuseStep 3900635 = 5850953) B5850953
theorem B1738313 : Blo 511796 1738313 := bstep (se 2 (by rfl) ⟨651867, by rfl⟩ : syracuseStep 1738313 = 1303735) B1303735
theorem B7112329 : Blo 511796 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B2197151 : Blo 511796 2197151 := bstep (se 1 (by rfl) ⟨1647863, by rfl⟩ : syracuseStep 2197151 = 3295727) B3295727
theorem B9865799 : Blo 511796 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B1641583 : Blo 511796 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B6261887 : Blo 511796 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B56988845 : Blo 511796 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B1152251 : Blo 511796 1152251 := bstep (se 1 (by rfl) ⟨864188, by rfl⟩ : syracuseStep 1152251 = 1728377) B1728377
theorem B1152377 : Blo 511796 1152377 := bstep (se 2 (by rfl) ⟨432141, by rfl⟩ : syracuseStep 1152377 = 864283) B864283
theorem B693625 : Blo 511796 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B1152467 : Blo 511796 1152467 := bstep (se 1 (by rfl) ⟨864350, by rfl⟩ : syracuseStep 1152467 = 1728701) B1728701
theorem B1153115 : Blo 511796 1153115 := bstep (se 1 (by rfl) ⟨864836, by rfl⟩ : syracuseStep 1153115 = 1729673) B1729673
theorem B1153619 : Blo 511796 1153619 := bstep (se 1 (by rfl) ⟨865214, by rfl⟩ : syracuseStep 1153619 = 1730429) B1730429
theorem B10525895 : Blo 511796 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B2923883 : Blo 511796 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B1154825 : Blo 511796 1154825 := bstep (se 2 (by rfl) ⟨433059, by rfl⟩ : syracuseStep 1154825 = 866119) B866119
theorem B13213853 : Blo 511796 13213853 := bstep (se 3 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 13213853 = 4955195) B4955195
theorem B7152083 : Blo 511796 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B6661439 : Blo 511796 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B1156985 : Blo 511796 1156985 := bstep (se 2 (by rfl) ⟨433869, by rfl⟩ : syracuseStep 1156985 = 867739) B867739
theorem B4696127 : Blo 511796 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B1157723 : Blo 511796 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1157867 : Blo 511796 1157867 := bstep (se 1 (by rfl) ⟨868400, by rfl⟩ : syracuseStep 1157867 = 1736801) B1736801
theorem B2468873 : Blo 511796 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B1158407 : Blo 511796 1158407 := bstep (se 1 (by rfl) ⟨868805, by rfl⟩ : syracuseStep 1158407 = 1737611) B1737611
theorem B6238727 : Blo 511796 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B6271769 : Blo 511796 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B9909161 : Blo 511796 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B9844577 : Blo 511796 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B866281 : Blo 511796 866281 := bstep (se 2 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 866281 = 649711) B649711
theorem B1947995 : Blo 511796 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B9877949 : Blo 511796 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B768491 : Blo 511796 768491 := bstep (se 1 (by rfl) ⟨576368, by rfl⟩ : syracuseStep 768491 = 1152737) B1152737
theorem B768719 : Blo 511796 768719 := bstep (se 1 (by rfl) ⟨576539, by rfl⟩ : syracuseStep 768719 = 1153079) B1153079
theorem B769001 : Blo 511796 769001 := bstep (se 2 (by rfl) ⟨288375, by rfl⟩ : syracuseStep 769001 = 576751) B576751
theorem B3554513 : Blo 511796 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B867631 : Blo 511796 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B769919 : Blo 511796 769919 := bstep (se 1 (by rfl) ⟨577439, by rfl⟩ : syracuseStep 769919 = 1154879) B1154879
theorem B6603443 : Blo 511796 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B228737783 : Blo 511796 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B771143 : Blo 511796 771143 := bstep (se 1 (by rfl) ⟨578357, by rfl⟩ : syracuseStep 771143 = 1156715) B1156715
theorem B7882091 : Blo 511796 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B771449 : Blo 511796 771449 := bstep (se 2 (by rfl) ⟨289293, by rfl⟩ : syracuseStep 771449 = 578587) B578587
theorem B771995 : Blo 511796 771995 := bstep (se 1 (by rfl) ⟨578996, by rfl⟩ : syracuseStep 771995 = 1157993) B1157993
theorem B772091 : Blo 511796 772091 := bstep (se 1 (by rfl) ⟨579068, by rfl⟩ : syracuseStep 772091 = 1158137) B1158137
theorem B772265 : Blo 511796 772265 := bstep (se 2 (by rfl) ⟨289599, by rfl⟩ : syracuseStep 772265 = 579199) B579199
theorem B575815 : Blo 511796 575815 := bstep (se 1 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 575815 = 863723) B863723
theorem B772511 : Blo 511796 772511 := bstep (se 1 (by rfl) ⟨579383, by rfl⟩ : syracuseStep 772511 = 1158767) B1158767
theorem B2607713 : Blo 511796 2607713 := bstep (se 2 (by rfl) ⟨977892, by rfl⟩ : syracuseStep 2607713 = 1955785) B1955785
theorem B772775 : Blo 511796 772775 := bstep (se 1 (by rfl) ⟨579581, by rfl⟩ : syracuseStep 772775 = 1159163) B1159163
theorem B576283 : Blo 511796 576283 := bstep (se 1 (by rfl) ⟨432212, by rfl⟩ : syracuseStep 576283 = 864425) B864425
theorem B773231 : Blo 511796 773231 := bstep (se 1 (by rfl) ⟨579923, by rfl⟩ : syracuseStep 773231 = 1159847) B1159847
theorem B5917817 : Blo 511796 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B1297721 : Blo 511796 1297721 := bstep (se 2 (by rfl) ⟨486645, by rfl⟩ : syracuseStep 1297721 = 973291) B973291
theorem B2936321 : Blo 511796 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B1298207 : Blo 511796 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B511855 : Blo 511796 511855 := bstep (se 1 (by rfl) ⟨383891, by rfl⟩ : syracuseStep 511855 = 767783) B767783
theorem B511903 : Blo 511796 511903 := bstep (se 1 (by rfl) ⟨383927, by rfl⟩ : syracuseStep 511903 = 767855) B767855
theorem B1462511 : Blo 511796 1462511 := bstep (se 1 (by rfl) ⟨1096883, by rfl⟩ : syracuseStep 1462511 = 2193767) B2193767
theorem B512703 : Blo 511796 512703 := bstep (se 1 (by rfl) ⟨384527, by rfl⟩ : syracuseStep 512703 = 769055) B769055
theorem B578335 : Blo 511796 578335 := bstep (se 1 (by rfl) ⟨433751, by rfl⟩ : syracuseStep 578335 = 867503) B867503
theorem B2610791 : Blo 511796 2610791 := bstep (se 1 (by rfl) ⟨1958093, by rfl⟩ : syracuseStep 2610791 = 3916187) B3916187
theorem B514139 : Blo 511796 514139 := bstep (se 1 (by rfl) ⟨385604, by rfl⟩ : syracuseStep 514139 = 771209) B771209
theorem B514527 : Blo 511796 514527 := bstep (se 1 (by rfl) ⟨385895, by rfl⟩ : syracuseStep 514527 = 771791) B771791
theorem B514559 : Blo 511796 514559 := bstep (se 1 (by rfl) ⟨385919, by rfl⟩ : syracuseStep 514559 = 771839) B771839
theorem B3889943 : Blo 511796 3889943 := bstep (se 1 (by rfl) ⟨2917457, by rfl⟩ : syracuseStep 3889943 = 5834915) B5834915
theorem B2350217 : Blo 511796 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B162487781 : Blo 511796 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B2056391 : Blo 511796 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B6677959 : Blo 511796 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B1304687 : Blo 511796 1304687 := bstep (se 1 (by rfl) ⟨978515, by rfl⟩ : syracuseStep 1304687 = 1957031) B1957031
theorem B3304489 : Blo 511796 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B13200731 : Blo 511796 13200731 := bstep (se 1 (by rfl) ⟨9900548, by rfl⟩ : syracuseStep 13200731 = 19801097) B19801097
theorem B3304799 : Blo 511796 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B7401887 : Blo 511796 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B1733183 : Blo 511796 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B1733723 : Blo 511796 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B1738475 : Blo 511796 1738475 := bstep (se 1 (by rfl) ⟨1303856, by rfl⟩ : syracuseStep 1738475 = 2607713) B2607713
theorem B1740527 : Blo 511796 1740527 := bstep (se 1 (by rfl) ⟨1305395, by rfl⟩ : syracuseStep 1740527 = 2610791) B2610791
theorem B2593295 : Blo 511796 2593295 := bstep (se 1 (by rfl) ⟨1944971, by rfl⟩ : syracuseStep 2593295 = 3889943) B3889943
theorem B7017263 : Blo 511796 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B924833 : Blo 511796 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B1645915 : Blo 511796 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B2203199 : Blo 511796 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B1155041 : Blo 511796 1155041 := bstep (se 2 (by rfl) ⟨433140, by rfl⟩ : syracuseStep 1155041 = 866281) B866281
theorem B1155455 : Blo 511796 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B1155815 : Blo 511796 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B6563051 : Blo 511796 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B1156841 : Blo 511796 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B2369675 : Blo 511796 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B8301305 : Blo 511796 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B4402295 : Blo 511796 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B2600423 : Blo 511796 2600423 := bstep (se 1 (by rfl) ⟨1950317, by rfl⟩ : syracuseStep 2600423 = 3900635) B3900635
theorem B5254727 : Blo 511796 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B1158875 : Blo 511796 1158875 := bstep (se 1 (by rfl) ⟨869156, by rfl⟩ : syracuseStep 1158875 = 1738313) B1738313
theorem B4174591 : Blo 511796 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B865147 : Blo 511796 865147 := bstep (se 1 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 865147 = 1297721) B1297721
theorem B865471 : Blo 511796 865471 := bstep (se 1 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 865471 = 1298207) B1298207
theorem B767753 : Blo 511796 767753 := bstep (se 2 (by rfl) ⟨287907, by rfl⟩ : syracuseStep 767753 = 575815) B575815
theorem B37992563 : Blo 511796 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B768167 : Blo 511796 768167 := bstep (se 1 (by rfl) ⟨576125, by rfl⟩ : syracuseStep 768167 = 1152251) B1152251
theorem B768251 : Blo 511796 768251 := bstep (se 1 (by rfl) ⟨576188, by rfl⟩ : syracuseStep 768251 = 1152377) B1152377
theorem B768311 : Blo 511796 768311 := bstep (se 1 (by rfl) ⟨576233, by rfl⟩ : syracuseStep 768311 = 1152467) B1152467
theorem B768377 : Blo 511796 768377 := bstep (se 2 (by rfl) ⟨288141, by rfl⟩ : syracuseStep 768377 = 576283) B576283
theorem B4405985 : Blo 511796 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B768743 : Blo 511796 768743 := bstep (se 1 (by rfl) ⟨576557, by rfl⟩ : syracuseStep 768743 = 1153115) B1153115
theorem B769079 : Blo 511796 769079 := bstep (se 1 (by rfl) ⟨576809, by rfl⟩ : syracuseStep 769079 = 1153619) B1153619
theorem B1949255 : Blo 511796 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B769883 : Blo 511796 769883 := bstep (se 1 (by rfl) ⟨577412, by rfl⟩ : syracuseStep 769883 = 1154825) B1154825
theorem B4768055 : Blo 511796 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B4440959 : Blo 511796 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B771113 : Blo 511796 771113 := bstep (se 2 (by rfl) ⟨289167, by rfl⟩ : syracuseStep 771113 = 578335) B578335
theorem B771323 : Blo 511796 771323 := bstep (se 1 (by rfl) ⟨578492, by rfl⟩ : syracuseStep 771323 = 1156985) B1156985
theorem B3130751 : Blo 511796 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B869791 : Blo 511796 869791 := bstep (se 1 (by rfl) ⟨652343, by rfl⟩ : syracuseStep 869791 = 1304687) B1304687
theorem B771815 : Blo 511796 771815 := bstep (se 1 (by rfl) ⟨578861, by rfl⟩ : syracuseStep 771815 = 1157723) B1157723
theorem B771911 : Blo 511796 771911 := bstep (se 1 (by rfl) ⟨578933, by rfl⟩ : syracuseStep 771911 = 1157867) B1157867
theorem B772271 : Blo 511796 772271 := bstep (se 1 (by rfl) ⟨579203, by rfl⟩ : syracuseStep 772271 = 1158407) B1158407
theorem B8800487 : Blo 511796 8800487 := bstep (se 1 (by rfl) ⟨6600365, by rfl⟩ : syracuseStep 8800487 = 13200731) B13200731
theorem B4934591 : Blo 511796 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B15780845 : Blo 511796 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B4181179 : Blo 511796 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B6606107 : Blo 511796 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B37932421 : Blo 511796 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B1298663 : Blo 511796 1298663 := bstep (se 1 (by rfl) ⟨973997, by rfl⟩ : syracuseStep 1298663 = 1947995) B1947995
theorem B512327 : Blo 511796 512327 := bstep (se 1 (by rfl) ⟨384245, by rfl⟩ : syracuseStep 512327 = 768491) B768491
theorem B512479 : Blo 511796 512479 := bstep (se 1 (by rfl) ⟨384359, by rfl⟩ : syracuseStep 512479 = 768719) B768719
theorem B512667 : Blo 511796 512667 := bstep (se 1 (by rfl) ⟨384500, by rfl⟩ : syracuseStep 512667 = 769001) B769001
theorem B513279 : Blo 511796 513279 := bstep (se 1 (by rfl) ⟨384959, by rfl⟩ : syracuseStep 513279 = 769919) B769919
theorem B26695169 : Blo 511796 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B152491855 : Blo 511796 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B1857451 : Blo 511796 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B514095 : Blo 511796 514095 := bstep (se 1 (by rfl) ⟨385571, by rfl⟩ : syracuseStep 514095 = 771143) B771143
theorem B514299 : Blo 511796 514299 := bstep (se 1 (by rfl) ⟨385724, by rfl⟩ : syracuseStep 514299 = 771449) B771449
theorem B1464767 : Blo 511796 1464767 := bstep (se 1 (by rfl) ⟨1098575, by rfl⟩ : syracuseStep 1464767 = 2197151) B2197151
theorem B514663 : Blo 511796 514663 := bstep (se 1 (by rfl) ⟨385997, by rfl⟩ : syracuseStep 514663 = 771995) B771995
theorem B514727 : Blo 511796 514727 := bstep (se 1 (by rfl) ⟨386045, by rfl⟩ : syracuseStep 514727 = 772091) B772091
theorem B514843 : Blo 511796 514843 := bstep (se 1 (by rfl) ⟨386132, by rfl⟩ : syracuseStep 514843 = 772265) B772265
theorem B515007 : Blo 511796 515007 := bstep (se 1 (by rfl) ⟨386255, by rfl⟩ : syracuseStep 515007 = 772511) B772511
theorem B6577199 : Blo 511796 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B515183 : Blo 511796 515183 := bstep (se 1 (by rfl) ⟨386387, by rfl⟩ : syracuseStep 515183 = 772775) B772775
theorem B8903945 : Blo 511796 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B515487 : Blo 511796 515487 := bstep (se 1 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 515487 = 773231) B773231
theorem B1957547 : Blo 511796 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B975007 : Blo 511796 975007 := bstep (se 1 (by rfl) ⟨731255, by rfl⟩ : syracuseStep 975007 = 1462511) B1462511
theorem B2188777 : Blo 511796 2188777 := bstep (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) B1641583
theorem B1566811 : Blo 511796 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B108325187 : Blo 511796 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B8809235 : Blo 511796 8809235 := bstep (se 1 (by rfl) ⟨6606926, by rfl⟩ : syracuseStep 8809235 = 13213853) B13213853
theorem B1370927 : Blo 511796 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B4159151 : Blo 511796 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B6585299 : Blo 511796 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B3178703 : Blo 511796 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B5866991 : Blo 511796 5866991 := bstep (se 1 (by rfl) ⟨4400243, by rfl⟩ : syracuseStep 5866991 = 8800487) B8800487
theorem B2918369 : Blo 511796 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B10520563 : Blo 511796 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B17796779 : Blo 511796 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B5574905 : Blo 511796 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B5935963 : Blo 511796 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B1153529 : Blo 511796 1153529 := bstep (se 2 (by rfl) ⟨432573, by rfl⟩ : syracuseStep 1153529 = 865147) B865147
theorem B1153961 : Blo 511796 1153961 := bstep (se 2 (by rfl) ⟨432735, by rfl⟩ : syracuseStep 1153961 = 865471) B865471
theorem B5872823 : Blo 511796 5872823 := bstep (se 1 (by rfl) ⟨4404617, by rfl⟩ : syracuseStep 5872823 = 8809235) B8809235
theorem B2960639 : Blo 511796 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B1158983 : Blo 511796 1158983 := bstep (se 1 (by rfl) ⟨869237, by rfl⟩ : syracuseStep 1158983 = 1738475) B1738475
theorem B1159721 : Blo 511796 1159721 := bstep (se 2 (by rfl) ⟨434895, by rfl⟩ : syracuseStep 1159721 = 869791) B869791
theorem B3289727 : Blo 511796 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B4404071 : Blo 511796 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B1160351 : Blo 511796 1160351 := bstep (se 1 (by rfl) ⟨870263, by rfl⟩ : syracuseStep 1160351 = 1740527) B1740527
theorem B865775 : Blo 511796 865775 := bstep (se 1 (by rfl) ⟨649331, by rfl⟩ : syracuseStep 865775 = 1298663) B1298663
theorem B50576561 : Blo 511796 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B770027 : Blo 511796 770027 := bstep (se 1 (by rfl) ⟨577520, by rfl⟩ : syracuseStep 770027 = 1155041) B1155041
theorem B770303 : Blo 511796 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B770543 : Blo 511796 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B4375367 : Blo 511796 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B771227 : Blo 511796 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B22136813 : Blo 511796 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B2934863 : Blo 511796 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B772583 : Blo 511796 772583 := bstep (se 1 (by rfl) ⟨579437, by rfl⟩ : syracuseStep 772583 = 1158875) B1158875
theorem B2476601 : Blo 511796 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B2772767 : Blo 511796 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B511835 : Blo 511796 511835 := bstep (se 1 (by rfl) ⟨383876, by rfl⟩ : syracuseStep 511835 = 767753) B767753
theorem B512111 : Blo 511796 512111 := bstep (se 1 (by rfl) ⟨384083, by rfl⟩ : syracuseStep 512111 = 768167) B768167
theorem B512167 : Blo 511796 512167 := bstep (se 1 (by rfl) ⟨384125, by rfl⟩ : syracuseStep 512167 = 768251) B768251
theorem B14012605 : Blo 511796 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B512207 : Blo 511796 512207 := bstep (se 1 (by rfl) ⟨384155, by rfl⟩ : syracuseStep 512207 = 768311) B768311
theorem B512251 : Blo 511796 512251 := bstep (se 1 (by rfl) ⟨384188, by rfl⟩ : syracuseStep 512251 = 768377) B768377
theorem B2937323 : Blo 511796 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B512495 : Blo 511796 512495 := bstep (se 1 (by rfl) ⟨384371, by rfl⟩ : syracuseStep 512495 = 768743) B768743
theorem B512719 : Blo 511796 512719 := bstep (se 1 (by rfl) ⟨384539, by rfl⟩ : syracuseStep 512719 = 769079) B769079
theorem B1299503 : Blo 511796 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B513255 : Blo 511796 513255 := bstep (se 1 (by rfl) ⟨384941, by rfl⟩ : syracuseStep 513255 = 769883) B769883
theorem B1300009 : Blo 511796 1300009 := bstep (se 2 (by rfl) ⟨487503, by rfl⟩ : syracuseStep 1300009 = 975007) B975007
theorem B514075 : Blo 511796 514075 := bstep (se 1 (by rfl) ⟨385556, by rfl⟩ : syracuseStep 514075 = 771113) B771113
theorem B514215 : Blo 511796 514215 := bstep (se 1 (by rfl) ⟨385661, by rfl⟩ : syracuseStep 514215 = 771323) B771323
theorem B514543 : Blo 511796 514543 := bstep (se 1 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 514543 = 771815) B771815
theorem B514607 : Blo 511796 514607 := bstep (se 1 (by rfl) ⟨385955, by rfl⟩ : syracuseStep 514607 = 771911) B771911
theorem B514847 : Blo 511796 514847 := bstep (se 1 (by rfl) ⟨386135, by rfl⟩ : syracuseStep 514847 = 772271) B772271
theorem B2089081 : Blo 511796 2089081 := bstep (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) B1566811
theorem B1728863 : Blo 511796 1728863 := bstep (se 1 (by rfl) ⟨1296647, by rfl⟩ : syracuseStep 1728863 = 2593295) B2593295
theorem B4678175 : Blo 511796 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B8348669 : Blo 511796 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B976511 : Blo 511796 976511 := bstep (se 1 (by rfl) ⟨732383, by rfl⟩ : syracuseStep 976511 = 1464767) B1464767
theorem B4384799 : Blo 511796 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B616555 : Blo 511796 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B1468799 : Blo 511796 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B1305031 : Blo 511796 1305031 := bstep (se 1 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 1305031 = 1957547) B1957547
theorem B6319133 : Blo 511796 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B5566121 : Blo 511796 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B72216791 : Blo 511796 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B913951 : Blo 511796 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B1733615 : Blo 511796 1733615 := bstep (se 1 (by rfl) ⟨1300211, by rfl⟩ : syracuseStep 1733615 = 2600423) B2600423
theorem B203322473 : Blo 511796 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B25328375 : Blo 511796 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B2194553 : Blo 511796 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B4390199 : Blo 511796 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B2785441 : Blo 511796 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B2916911 : Blo 511796 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B11864519 : Blo 511796 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B14027417 : Blo 511796 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B822073 : Blo 511796 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B1740041 : Blo 511796 1740041 := bstep (se 2 (by rfl) ⟨652515, by rfl⟩ : syracuseStep 1740041 = 1305031) B1305031
theorem B1152575 : Blo 511796 1152575 := bstep (se 1 (by rfl) ⟨864431, by rfl⟩ : syracuseStep 1152575 = 1728863) B1728863
theorem B18683473 : Blo 511796 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B3118783 : Blo 511796 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B1218601 : Blo 511796 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B2923199 : Blo 511796 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B1973759 : Blo 511796 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B3710747 : Blo 511796 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B48144527 : Blo 511796 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B1155743 : Blo 511796 1155743 := bstep (se 1 (by rfl) ⟨866807, by rfl⟩ : syracuseStep 1155743 = 1733615) B1733615
theorem B16885583 : Blo 511796 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2926799 : Blo 511796 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B3911327 : Blo 511796 3911327 := bstep (se 1 (by rfl) ⟨2933495, by rfl⟩ : syracuseStep 3911327 = 5866991) B5866991
theorem B1945579 : Blo 511796 1945579 := bstep (se 1 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 1945579 = 2918369) B2918369
theorem B14757875 : Blo 511796 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B1651067 : Blo 511796 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B1848511 : Blo 511796 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B3716603 : Blo 511796 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B866335 : Blo 511796 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B769019 : Blo 511796 769019 := bstep (se 1 (by rfl) ⟨576764, by rfl⟩ : syracuseStep 769019 = 1153529) B1153529
theorem B769307 : Blo 511796 769307 := bstep (se 1 (by rfl) ⟨576980, by rfl⟩ : syracuseStep 769307 = 1153961) B1153961
theorem B3915215 : Blo 511796 3915215 := bstep (se 1 (by rfl) ⟨2936411, by rfl⟩ : syracuseStep 3915215 = 5872823) B5872823
theorem B7914617 : Blo 511796 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B4212755 : Blo 511796 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B772655 : Blo 511796 772655 := bstep (se 1 (by rfl) ⟨579491, by rfl⟩ : syracuseStep 772655 = 1158983) B1158983
theorem B773147 : Blo 511796 773147 := bstep (se 1 (by rfl) ⟨579860, by rfl⟩ : syracuseStep 773147 = 1159721) B1159721
theorem B2936047 : Blo 511796 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B135548315 : Blo 511796 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B773567 : Blo 511796 773567 := bstep (se 1 (by rfl) ⟨580175, by rfl⟩ : syracuseStep 773567 = 1160351) B1160351
theorem B577183 : Blo 511796 577183 := bstep (se 1 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 577183 = 865775) B865775
theorem B1463035 : Blo 511796 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B513351 : Blo 511796 513351 := bstep (se 1 (by rfl) ⟨385013, by rfl⟩ : syracuseStep 513351 = 770027) B770027
theorem B2119135 : Blo 511796 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B513535 : Blo 511796 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B513695 : Blo 511796 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B514151 : Blo 511796 514151 := bstep (se 1 (by rfl) ⟨385613, by rfl⟩ : syracuseStep 514151 = 771227) B771227
theorem B1956575 : Blo 511796 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B515055 : Blo 511796 515055 := bstep (se 1 (by rfl) ⟨386291, by rfl⟩ : syracuseStep 515055 = 772583) B772583
theorem B1958215 : Blo 511796 1958215 := bstep (se 1 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 1958215 = 2937323) B2937323
theorem B5565779 : Blo 511796 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B651007 : Blo 511796 651007 := bstep (se 1 (by rfl) ⟨488255, by rfl⟩ : syracuseStep 651007 = 976511) B976511
theorem B979199 : Blo 511796 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B1733345 : Blo 511796 1733345 := bstep (se 2 (by rfl) ⟨650004, by rfl⟩ : syracuseStep 1733345 = 1300009) B1300009
theorem B2193151 : Blo 511796 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B33717707 : Blo 511796 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B5276411 : Blo 511796 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2594105 : Blo 511796 2594105 := bstep (se 2 (by rfl) ⟨972789, by rfl⟩ : syracuseStep 2594105 = 1945579) B1945579
theorem B2464681 : Blo 511796 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B2825513 : Blo 511796 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B24911297 : Blo 511796 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B3710519 : Blo 511796 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B2924201 : Blo 511796 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B9838583 : Blo 511796 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B1155113 : Blo 511796 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B1155563 : Blo 511796 1155563 := bstep (se 1 (by rfl) ⟨866672, by rfl⟩ : syracuseStep 1155563 = 1733345) B1733345
theorem B3713921 : Blo 511796 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B1944607 : Blo 511796 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B7909679 : Blo 511796 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B9351611 : Blo 511796 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B1160027 : Blo 511796 1160027 := bstep (se 1 (by rfl) ⟨870020, by rfl⟩ : syracuseStep 1160027 = 1740041) B1740041
theorem B768383 : Blo 511796 768383 := bstep (se 1 (by rfl) ⟨576287, by rfl⟩ : syracuseStep 768383 = 1152575) B1152575
theorem B1096097 : Blo 511796 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B3914729 : Blo 511796 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B1948799 : Blo 511796 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B769577 : Blo 511796 769577 := bstep (se 2 (by rfl) ⟨288591, by rfl⟩ : syracuseStep 769577 = 577183) B577183
theorem B868009 : Blo 511796 868009 := bstep (se 2 (by rfl) ⟨325503, by rfl⟩ : syracuseStep 868009 = 651007) B651007
theorem B2473831 : Blo 511796 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B21053429 : Blo 511796 21053429 := bstep (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) B1973759
theorem B32096351 : Blo 511796 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B770495 : Blo 511796 770495 := bstep (se 1 (by rfl) ⟨577871, by rfl⟩ : syracuseStep 770495 = 1155743) B1155743
theorem B1950713 : Blo 511796 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B11257055 : Blo 511796 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B1951199 : Blo 511796 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B2607551 : Blo 511796 2607551 := bstep (se 1 (by rfl) ⟨1955663, by rfl⟩ : syracuseStep 2607551 = 3911327) B3911327
theorem B1624801 : Blo 511796 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B1100711 : Blo 511796 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B2477735 : Blo 511796 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B512679 : Blo 511796 512679 := bstep (se 1 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 512679 = 769019) B769019
theorem B512871 : Blo 511796 512871 := bstep (se 1 (by rfl) ⟨384653, by rfl⟩ : syracuseStep 512871 = 769307) B769307
theorem B2610143 : Blo 511796 2610143 := bstep (se 1 (by rfl) ⟨1957607, by rfl⟩ : syracuseStep 2610143 = 3915215) B3915215
theorem B2610953 : Blo 511796 2610953 := bstep (se 2 (by rfl) ⟨979107, by rfl⟩ : syracuseStep 2610953 = 1958215) B1958215
theorem B2808503 : Blo 511796 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B515103 : Blo 511796 515103 := bstep (se 1 (by rfl) ⟨386327, by rfl⟩ : syracuseStep 515103 = 772655) B772655
theorem B515431 : Blo 511796 515431 := bstep (se 1 (by rfl) ⟨386573, by rfl⟩ : syracuseStep 515431 = 773147) B773147
theorem B90365543 : Blo 511796 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B515711 : Blo 511796 515711 := bstep (se 1 (by rfl) ⟨386783, by rfl⟩ : syracuseStep 515711 = 773567) B773567
theorem B1304383 : Blo 511796 1304383 := bstep (se 1 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 1304383 = 1956575) B1956575
theorem B4158377 : Blo 511796 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B652799 : Blo 511796 652799 := bstep (se 1 (by rfl) ⟨489599, by rfl⟩ : syracuseStep 652799 = 979199) B979199
theorem B22478471 : Blo 511796 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B21397567 : Blo 511796 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B7504703 : Blo 511796 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B1738367 : Blo 511796 1738367 := bstep (se 1 (by rfl) ⟨1303775, by rfl⟩ : syracuseStep 1738367 = 2607551) B2607551
theorem B1739177 : Blo 511796 1739177 := bstep (se 2 (by rfl) ⟨652191, by rfl⟩ : syracuseStep 1739177 = 1304383) B1304383
theorem B1740095 : Blo 511796 1740095 := bstep (se 1 (by rfl) ⟨1305071, by rfl⟩ : syracuseStep 1740095 = 2610143) B2610143
theorem B2166401 : Blo 511796 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1740635 : Blo 511796 1740635 := bstep (se 1 (by rfl) ⟨1305476, by rfl⟩ : syracuseStep 1740635 = 2610953) B2610953
theorem B1740797 : Blo 511796 1740797 := bstep (se 3 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 1740797 = 652799) B652799
theorem B2592809 : Blo 511796 2592809 := bstep (se 2 (by rfl) ⟨972303, by rfl⟩ : syracuseStep 2592809 = 1944607) B1944607
theorem B1872335 : Blo 511796 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B6559055 : Blo 511796 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B2922925 : Blo 511796 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B6234407 : Blo 511796 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B3286241 : Blo 511796 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B1157345 : Blo 511796 1157345 := bstep (se 2 (by rfl) ⟨434004, by rfl⟩ : syracuseStep 1157345 = 868009) B868009
theorem B14985647 : Blo 511796 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B14035619 : Blo 511796 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B3517607 : Blo 511796 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B733807 : Blo 511796 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B1651823 : Blo 511796 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B1883675 : Blo 511796 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B2473679 : Blo 511796 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B60243695 : Blo 511796 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B1949467 : Blo 511796 1949467 := bstep (se 1 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 1949467 = 2924201) B2924201
theorem B770075 : Blo 511796 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B770375 : Blo 511796 770375 := bstep (se 1 (by rfl) ⟨577781, by rfl⟩ : syracuseStep 770375 = 1155563) B1155563
theorem B2475947 : Blo 511796 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B773351 : Blo 511796 773351 := bstep (se 1 (by rfl) ⟨580013, by rfl⟩ : syracuseStep 773351 = 1160027) B1160027
theorem B2772251 : Blo 511796 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B512255 : Blo 511796 512255 := bstep (se 1 (by rfl) ⟨384191, by rfl⟩ : syracuseStep 512255 = 768383) B768383
theorem B2609819 : Blo 511796 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B1299199 : Blo 511796 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B513051 : Blo 511796 513051 := bstep (se 1 (by rfl) ⟨384788, by rfl⟩ : syracuseStep 513051 = 769577) B769577
theorem B3298441 : Blo 511796 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B513663 : Blo 511796 513663 := bstep (se 1 (by rfl) ⟨385247, by rfl⟩ : syracuseStep 513663 = 770495) B770495
theorem B1300475 : Blo 511796 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B1300799 : Blo 511796 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B1729403 : Blo 511796 1729403 := bstep (se 1 (by rfl) ⟨1297052, by rfl⟩ : syracuseStep 1729403 = 2594105) B2594105
theorem B16607531 : Blo 511796 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B5273119 : Blo 511796 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B1444267 : Blo 511796 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B1248223 : Blo 511796 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B1739879 : Blo 511796 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B1152935 : Blo 511796 1152935 := bstep (se 1 (by rfl) ⟨864701, by rfl⟩ : syracuseStep 1152935 = 1729403) B1729403
theorem B4397921 : Blo 511796 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B28123301 : Blo 511796 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B9380285 : Blo 511796 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B1255783 : Blo 511796 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B2599289 : Blo 511796 2599289 := bstep (se 2 (by rfl) ⟨974733, by rfl⟩ : syracuseStep 2599289 = 1949467) B1949467
theorem B1649119 : Blo 511796 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B1158911 : Blo 511796 1158911 := bstep (se 1 (by rfl) ⟨869183, by rfl⟩ : syracuseStep 1158911 = 1738367) B1738367
theorem B1650631 : Blo 511796 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B1159451 : Blo 511796 1159451 := bstep (se 1 (by rfl) ⟨869588, by rfl⟩ : syracuseStep 1159451 = 1739177) B1739177
theorem B1848167 : Blo 511796 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B1160063 : Blo 511796 1160063 := bstep (se 1 (by rfl) ⟨870047, by rfl⟩ : syracuseStep 1160063 = 1740095) B1740095
theorem B1160423 : Blo 511796 1160423 := bstep (se 1 (by rfl) ⟨870317, by rfl⟩ : syracuseStep 1160423 = 1740635) B1740635
theorem B1160531 : Blo 511796 1160531 := bstep (se 1 (by rfl) ⟨870398, by rfl⟩ : syracuseStep 1160531 = 1740797) B1740797
theorem B4372703 : Blo 511796 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B866983 : Blo 511796 866983 := bstep (se 1 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 866983 = 1300475) B1300475
theorem B867199 : Blo 511796 867199 := bstep (se 1 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 867199 = 1300799) B1300799
theorem B44286749 : Blo 511796 44286749 := bstep (se 3 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 44286749 = 16607531) B16607531
theorem B771563 : Blo 511796 771563 := bstep (se 1 (by rfl) ⟨578672, by rfl⟩ : syracuseStep 771563 = 1157345) B1157345
theorem B9357079 : Blo 511796 9357079 := bstep (se 1 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 9357079 = 14035619) B14035619
theorem B1101215 : Blo 511796 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B40162463 : Blo 511796 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B513383 : Blo 511796 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B28530089 : Blo 511796 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B513583 : Blo 511796 513583 := bstep (se 1 (by rfl) ⟨385187, by rfl⟩ : syracuseStep 513583 = 770375) B770375
theorem B5003135 : Blo 511796 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B515567 : Blo 511796 515567 := bstep (se 1 (by rfl) ⟨386675, by rfl⟩ : syracuseStep 515567 = 773351) B773351
theorem B1728539 : Blo 511796 1728539 := bstep (se 1 (by rfl) ⟨1296404, by rfl⟩ : syracuseStep 1728539 = 2592809) B2592809
theorem B4156271 : Blo 511796 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B978409 : Blo 511796 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B2190827 : Blo 511796 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B1732265 : Blo 511796 1732265 := bstep (se 2 (by rfl) ⟨649599, by rfl⟩ : syracuseStep 1732265 = 1299199) B1299199
theorem B9990431 : Blo 511796 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B3897233 : Blo 511796 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B29524499 : Blo 511796 29524499 := bstep (se 1 (by rfl) ⟨22143374, by rfl⟩ : syracuseStep 29524499 = 44286749) B44286749
theorem B1674377 : Blo 511796 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B2198825 : Blo 511796 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B26774975 : Blo 511796 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2200841 : Blo 511796 2200841 := bstep (se 2 (by rfl) ⟨825315, by rfl⟩ : syracuseStep 2200841 = 1650631) B1650631
theorem B1152359 : Blo 511796 1152359 := bstep (se 1 (by rfl) ⟨864269, by rfl⟩ : syracuseStep 1152359 = 1728539) B1728539
theorem B18748867 : Blo 511796 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B1154843 : Blo 511796 1154843 := bstep (se 1 (by rfl) ⟨866132, by rfl⟩ : syracuseStep 1154843 = 1732265) B1732265
theorem B6660287 : Blo 511796 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B1155977 : Blo 511796 1155977 := bstep (se 2 (by rfl) ⟨433491, by rfl⟩ : syracuseStep 1155977 = 866983) B866983
theorem B1156265 : Blo 511796 1156265 := bstep (se 2 (by rfl) ⟨433599, by rfl⟩ : syracuseStep 1156265 = 867199) B867199
theorem B2598155 : Blo 511796 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B5842205 : Blo 511796 5842205 := bstep (se 3 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 5842205 = 2190827) B2190827
theorem B1159919 : Blo 511796 1159919 := bstep (se 1 (by rfl) ⟨869939, by rfl⟩ : syracuseStep 1159919 = 1739879) B1739879
theorem B19020059 : Blo 511796 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B768623 : Blo 511796 768623 := bstep (se 1 (by rfl) ⟨576467, by rfl⟩ : syracuseStep 768623 = 1152935) B1152935
theorem B2931947 : Blo 511796 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B2770847 : Blo 511796 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B772607 : Blo 511796 772607 := bstep (se 1 (by rfl) ⟨579455, by rfl⟩ : syracuseStep 772607 = 1158911) B1158911
theorem B772967 : Blo 511796 772967 := bstep (se 1 (by rfl) ⟨579725, by rfl⟩ : syracuseStep 772967 = 1159451) B1159451
theorem B1232111 : Blo 511796 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B773375 : Blo 511796 773375 := bstep (se 1 (by rfl) ⟨580031, by rfl⟩ : syracuseStep 773375 = 1160063) B1160063
theorem B773615 : Blo 511796 773615 := bstep (se 1 (by rfl) ⟨580211, by rfl⟩ : syracuseStep 773615 = 1160423) B1160423
theorem B773687 : Blo 511796 773687 := bstep (se 1 (by rfl) ⟨580265, by rfl⟩ : syracuseStep 773687 = 1160531) B1160531
theorem B2936573 : Blo 511796 2936573 := bstep (se 3 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 2936573 = 1101215) B1101215
theorem B514375 : Blo 511796 514375 := bstep (se 1 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 514375 = 771563) B771563
theorem B12476105 : Blo 511796 12476105 := bstep (se 2 (by rfl) ⟨4678539, by rfl⟩ : syracuseStep 12476105 = 9357079) B9357079
theorem B1925689 : Blo 511796 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B3335423 : Blo 511796 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B1664297 : Blo 511796 1664297 := bstep (se 2 (by rfl) ⟨624111, by rfl⟩ : syracuseStep 1664297 = 1248223) B1248223
theorem B1304545 : Blo 511796 1304545 := bstep (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) B978409
theorem B6253523 : Blo 511796 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B1732859 : Blo 511796 1732859 := bstep (se 1 (by rfl) ⟨1299644, by rfl⟩ : syracuseStep 1732859 = 2599289) B2599289
theorem B2915135 : Blo 511796 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B1116251 : Blo 511796 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B821407 : Blo 511796 821407 := bstep (se 1 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 821407 = 1232111) B1232111
theorem B1739393 : Blo 511796 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B4169015 : Blo 511796 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B1155239 : Blo 511796 1155239 := bstep (se 1 (by rfl) ⟨866429, by rfl⟩ : syracuseStep 1155239 = 1732859) B1732859
theorem B1943423 : Blo 511796 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B2567585 : Blo 511796 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B1847231 : Blo 511796 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B8894461 : Blo 511796 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B768239 : Blo 511796 768239 := bstep (se 1 (by rfl) ⟨576179, by rfl⟩ : syracuseStep 768239 = 1152359) B1152359
theorem B769895 : Blo 511796 769895 := bstep (se 1 (by rfl) ⟨577421, by rfl⟩ : syracuseStep 769895 = 1154843) B1154843
theorem B4440191 : Blo 511796 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B770651 : Blo 511796 770651 := bstep (se 1 (by rfl) ⟨577988, by rfl⟩ : syracuseStep 770651 = 1155977) B1155977
theorem B770843 : Blo 511796 770843 := bstep (se 1 (by rfl) ⟨578132, by rfl⟩ : syracuseStep 770843 = 1156265) B1156265
theorem B773279 : Blo 511796 773279 := bstep (se 1 (by rfl) ⟨579959, by rfl⟩ : syracuseStep 773279 = 1159919) B1159919
theorem B512415 : Blo 511796 512415 := bstep (se 1 (by rfl) ⟨384311, by rfl⟩ : syracuseStep 512415 = 768623) B768623
theorem B1954631 : Blo 511796 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B19682999 : Blo 511796 19682999 := bstep (se 1 (by rfl) ⟨14762249, by rfl⟩ : syracuseStep 19682999 = 29524499) B29524499
theorem B515071 : Blo 511796 515071 := bstep (se 1 (by rfl) ⟨386303, by rfl⟩ : syracuseStep 515071 = 772607) B772607
theorem B515311 : Blo 511796 515311 := bstep (se 1 (by rfl) ⟨386483, by rfl⟩ : syracuseStep 515311 = 772967) B772967
theorem B515583 : Blo 511796 515583 := bstep (se 1 (by rfl) ⟨386687, by rfl⟩ : syracuseStep 515583 = 773375) B773375
theorem B1465883 : Blo 511796 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B17849983 : Blo 511796 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B515743 : Blo 511796 515743 := bstep (se 1 (by rfl) ⟨386807, by rfl⟩ : syracuseStep 515743 = 773615) B773615
theorem B515791 : Blo 511796 515791 := bstep (se 1 (by rfl) ⟨386843, by rfl⟩ : syracuseStep 515791 = 773687) B773687
theorem B1957715 : Blo 511796 1957715 := bstep (se 1 (by rfl) ⟨1468286, by rfl⟩ : syracuseStep 1957715 = 2936573) B2936573
theorem B1467227 : Blo 511796 1467227 := bstep (se 1 (by rfl) ⟨1100420, by rfl⟩ : syracuseStep 1467227 = 2200841) B2200841
theorem B8317403 : Blo 511796 8317403 := bstep (se 1 (by rfl) ⟨6238052, by rfl⟩ : syracuseStep 8317403 = 12476105) B12476105
theorem B1732103 : Blo 511796 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B3894803 : Blo 511796 3894803 := bstep (se 1 (by rfl) ⟨2921102, by rfl⟩ : syracuseStep 3894803 = 5842205) B5842205
theorem B1109531 : Blo 511796 1109531 := bstep (se 1 (by rfl) ⟨832148, by rfl⟩ : syracuseStep 1109531 = 1664297) B1664297
theorem B24998489 : Blo 511796 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B12680039 : Blo 511796 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B5544935 : Blo 511796 5544935 := bstep (se 1 (by rfl) ⟨4158701, by rfl⟩ : syracuseStep 5544935 = 8317403) B8317403
theorem B1154735 : Blo 511796 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B2596535 : Blo 511796 2596535 := bstep (se 1 (by rfl) ⟨1947401, by rfl⟩ : syracuseStep 2596535 = 3894803) B3894803
theorem B23799977 : Blo 511796 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B11840509 : Blo 511796 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B1159595 : Blo 511796 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B1095209 : Blo 511796 1095209 := bstep (se 2 (by rfl) ⟨410703, by rfl⟩ : syracuseStep 1095209 = 821407) B821407
theorem B13121999 : Blo 511796 13121999 := bstep (se 1 (by rfl) ⟨9841499, by rfl⟩ : syracuseStep 13121999 = 19682999) B19682999
theorem B770159 : Blo 511796 770159 := bstep (se 1 (by rfl) ⟨577619, by rfl⟩ : syracuseStep 770159 = 1155239) B1155239
theorem B1295615 : Blo 511796 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B739687 : Blo 511796 739687 := bstep (se 1 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 739687 = 1109531) B1109531
theorem B1231487 : Blo 511796 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B16665659 : Blo 511796 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B512159 : Blo 511796 512159 := bstep (se 1 (by rfl) ⟨384119, by rfl⟩ : syracuseStep 512159 = 768239) B768239
theorem B513263 : Blo 511796 513263 := bstep (se 1 (by rfl) ⟨384947, by rfl⟩ : syracuseStep 513263 = 769895) B769895
theorem B513767 : Blo 511796 513767 := bstep (se 1 (by rfl) ⟨385325, by rfl⟩ : syracuseStep 513767 = 770651) B770651
theorem B513895 : Blo 511796 513895 := bstep (se 1 (by rfl) ⟨385421, by rfl⟩ : syracuseStep 513895 = 770843) B770843
theorem B744167 : Blo 511796 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B515519 : Blo 511796 515519 := bstep (se 1 (by rfl) ⟨386639, by rfl⟩ : syracuseStep 515519 = 773279) B773279
theorem B1303087 : Blo 511796 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B2779343 : Blo 511796 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B977255 : Blo 511796 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B1305143 : Blo 511796 1305143 := bstep (se 1 (by rfl) ⟨978857, by rfl⟩ : syracuseStep 1305143 = 1957715) B1957715
theorem B978151 : Blo 511796 978151 := bstep (se 1 (by rfl) ⟨733613, by rfl⟩ : syracuseStep 978151 = 1467227) B1467227
theorem B11859281 : Blo 511796 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B6846893 : Blo 511796 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B8453359 : Blo 511796 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B1737449 : Blo 511796 1737449 := bstep (se 2 (by rfl) ⟨651543, by rfl⟩ : syracuseStep 1737449 = 1303087) B1303087
theorem B820991 : Blo 511796 820991 := bstep (se 1 (by rfl) ⟨615743, by rfl⟩ : syracuseStep 820991 = 1231487) B1231487
theorem B11110439 : Blo 511796 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B986249 : Blo 511796 986249 := bstep (se 2 (by rfl) ⟨369843, by rfl⟩ : syracuseStep 986249 = 739687) B739687
theorem B15866651 : Blo 511796 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B7906187 : Blo 511796 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B730139 : Blo 511796 730139 := bstep (se 1 (by rfl) ⟨547604, by rfl⟩ : syracuseStep 730139 = 1095209) B1095209
theorem B4564595 : Blo 511796 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B863743 : Blo 511796 863743 := bstep (se 1 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 863743 = 1295615) B1295615
theorem B769823 : Blo 511796 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B1852895 : Blo 511796 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B870095 : Blo 511796 870095 := bstep (se 1 (by rfl) ⟨652571, by rfl⟩ : syracuseStep 870095 = 1305143) B1305143
theorem B1984445 : Blo 511796 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B773063 : Blo 511796 773063 := bstep (se 1 (by rfl) ⟨579797, by rfl⟩ : syracuseStep 773063 = 1159595) B1159595
theorem B513439 : Blo 511796 513439 := bstep (se 1 (by rfl) ⟨385079, by rfl⟩ : syracuseStep 513439 = 770159) B770159
theorem B15787345 : Blo 511796 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B1304201 : Blo 511796 1304201 := bstep (se 2 (by rfl) ⟨489075, by rfl⟩ : syracuseStep 1304201 = 978151) B978151
theorem B3696623 : Blo 511796 3696623 := bstep (se 1 (by rfl) ⟨2772467, by rfl⟩ : syracuseStep 3696623 = 5544935) B5544935
theorem B1731023 : Blo 511796 1731023 := bstep (se 1 (by rfl) ⟨1298267, by rfl⟩ : syracuseStep 1731023 = 2596535) B2596535
theorem B651503 : Blo 511796 651503 := bstep (se 1 (by rfl) ⟨488627, by rfl⟩ : syracuseStep 651503 = 977255) B977255
theorem B8747999 : Blo 511796 8747999 := bstep (se 1 (by rfl) ⟨6560999, by rfl⟩ : syracuseStep 8747999 = 13121999) B13121999
theorem B11271145 : Blo 511796 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B1737341 : Blo 511796 1737341 := bstep (se 3 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 1737341 = 651503) B651503
theorem B7406959 : Blo 511796 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B657499 : Blo 511796 657499 := bstep (se 1 (by rfl) ⟨493124, by rfl⟩ : syracuseStep 657499 = 986249) B986249
theorem B1151657 : Blo 511796 1151657 := bstep (se 2 (by rfl) ⟨431871, by rfl⟩ : syracuseStep 1151657 = 863743) B863743
theorem B2464415 : Blo 511796 2464415 := bstep (se 1 (by rfl) ⟨1848311, by rfl⟩ : syracuseStep 2464415 = 3696623) B3696623
theorem B1154015 : Blo 511796 1154015 := bstep (se 1 (by rfl) ⟨865511, by rfl⟩ : syracuseStep 1154015 = 1731023) B1731023
theorem B42311069 : Blo 511796 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B1158299 : Blo 511796 1158299 := bstep (se 1 (by rfl) ⟨868724, by rfl⟩ : syracuseStep 1158299 = 1737449) B1737449
theorem B1322963 : Blo 511796 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B21049793 : Blo 511796 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B1947037 : Blo 511796 1947037 := bstep (se 3 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 1947037 = 730139) B730139
theorem B869467 : Blo 511796 869467 := bstep (se 1 (by rfl) ⟨652100, by rfl⟩ : syracuseStep 869467 = 1304201) B1304201
theorem B15028193 : Blo 511796 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B513215 : Blo 511796 513215 := bstep (se 1 (by rfl) ⟨384911, by rfl⟩ : syracuseStep 513215 = 769823) B769823
theorem B1235263 : Blo 511796 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B580063 : Blo 511796 580063 := bstep (se 1 (by rfl) ⟨435047, by rfl⟩ : syracuseStep 580063 = 870095) B870095
theorem B547327 : Blo 511796 547327 := bstep (se 1 (by rfl) ⟨410495, by rfl⟩ : syracuseStep 547327 = 820991) B820991
theorem B515375 : Blo 511796 515375 := bstep (se 1 (by rfl) ⟨386531, by rfl⟩ : syracuseStep 515375 = 773063) B773063
theorem B5270791 : Blo 511796 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B3043063 : Blo 511796 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B5831999 : Blo 511796 5831999 := bstep (se 1 (by rfl) ⟨4373999, by rfl⟩ : syracuseStep 5831999 = 8747999) B8747999
theorem B2919077 : Blo 511796 2919077 := bstep (se 4 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 2919077 = 547327) B547327
theorem B1642943 : Blo 511796 1642943 := bstep (se 1 (by rfl) ⟨1232207, by rfl⟩ : syracuseStep 1642943 = 2464415) B2464415
theorem B2596049 : Blo 511796 2596049 := bstep (se 2 (by rfl) ⟨973518, by rfl⟩ : syracuseStep 2596049 = 1947037) B1947037
theorem B14033195 : Blo 511796 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B1647017 : Blo 511796 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B1158227 : Blo 511796 1158227 := bstep (se 1 (by rfl) ⟨868670, by rfl⟩ : syracuseStep 1158227 = 1737341) B1737341
theorem B1159289 : Blo 511796 1159289 := bstep (se 2 (by rfl) ⟨434733, by rfl⟩ : syracuseStep 1159289 = 869467) B869467
theorem B9875945 : Blo 511796 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B767771 : Blo 511796 767771 := bstep (se 1 (by rfl) ⟨575828, by rfl⟩ : syracuseStep 767771 = 1151657) B1151657
theorem B7027721 : Blo 511796 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B769343 : Blo 511796 769343 := bstep (se 1 (by rfl) ⟨577007, by rfl⟩ : syracuseStep 769343 = 1154015) B1154015
theorem B772199 : Blo 511796 772199 := bstep (se 1 (by rfl) ⟨579149, by rfl⟩ : syracuseStep 772199 = 1158299) B1158299
theorem B773417 : Blo 511796 773417 := bstep (se 2 (by rfl) ⟨290031, by rfl⟩ : syracuseStep 773417 = 580063) B580063
theorem B3887999 : Blo 511796 3887999 := bstep (se 1 (by rfl) ⟨2915999, by rfl⟩ : syracuseStep 3887999 = 5831999) B5831999
theorem B876665 : Blo 511796 876665 := bstep (se 2 (by rfl) ⟨328749, by rfl⟩ : syracuseStep 876665 = 657499) B657499
theorem B28207379 : Blo 511796 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B4057417 : Blo 511796 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B881975 : Blo 511796 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B40075181 : Blo 511796 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B2591999 : Blo 511796 2591999 := bstep (se 1 (by rfl) ⟨1943999, by rfl⟩ : syracuseStep 2591999 = 3887999) B3887999
theorem B26716787 : Blo 511796 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B21639557 : Blo 511796 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B1946051 : Blo 511796 1946051 := bstep (se 1 (by rfl) ⟨1459538, by rfl⟩ : syracuseStep 1946051 = 2919077) B2919077
theorem B1095295 : Blo 511796 1095295 := bstep (se 1 (by rfl) ⟨821471, by rfl⟩ : syracuseStep 1095295 = 1642943) B1642943
theorem B9355463 : Blo 511796 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B1098011 : Blo 511796 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B772151 : Blo 511796 772151 := bstep (se 1 (by rfl) ⟨579113, by rfl⟩ : syracuseStep 772151 = 1158227) B1158227
theorem B772859 : Blo 511796 772859 := bstep (se 1 (by rfl) ⟨579644, by rfl⟩ : syracuseStep 772859 = 1159289) B1159289
theorem B511847 : Blo 511796 511847 := bstep (se 1 (by rfl) ⟨383885, by rfl⟩ : syracuseStep 511847 = 767771) B767771
theorem B512895 : Blo 511796 512895 := bstep (se 1 (by rfl) ⟨384671, by rfl⟩ : syracuseStep 512895 = 769343) B769343
theorem B514799 : Blo 511796 514799 := bstep (se 1 (by rfl) ⟨386099, by rfl⟩ : syracuseStep 514799 = 772199) B772199
theorem B515611 : Blo 511796 515611 := bstep (se 1 (by rfl) ⟨386708, by rfl⟩ : syracuseStep 515611 = 773417) B773417
theorem B1730699 : Blo 511796 1730699 := bstep (se 1 (by rfl) ⟨1298024, by rfl⟩ : syracuseStep 1730699 = 2596049) B2596049
theorem B584443 : Blo 511796 584443 := bstep (se 1 (by rfl) ⟨438332, by rfl⟩ : syracuseStep 584443 = 876665) B876665
theorem B18804919 : Blo 511796 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B6583963 : Blo 511796 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B587983 : Blo 511796 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B4685147 : Blo 511796 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B25073225 : Blo 511796 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B1153799 : Blo 511796 1153799 := bstep (se 1 (by rfl) ⟨865349, by rfl⟩ : syracuseStep 1153799 = 1730699) B1730699
theorem B14426371 : Blo 511796 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B3123431 : Blo 511796 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B6236975 : Blo 511796 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B732007 : Blo 511796 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B17811191 : Blo 511796 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B1460393 : Blo 511796 1460393 := bstep (se 2 (by rfl) ⟨547647, by rfl⟩ : syracuseStep 1460393 = 1095295) B1095295
theorem B1297367 : Blo 511796 1297367 := bstep (se 1 (by rfl) ⟨973025, by rfl⟩ : syracuseStep 1297367 = 1946051) B1946051
theorem B514767 : Blo 511796 514767 := bstep (se 1 (by rfl) ⟨386075, by rfl⟩ : syracuseStep 514767 = 772151) B772151
theorem B515239 : Blo 511796 515239 := bstep (se 1 (by rfl) ⟨386429, by rfl⟩ : syracuseStep 515239 = 772859) B772859
theorem B1727999 : Blo 511796 1727999 := bstep (se 1 (by rfl) ⟨1295999, by rfl⟩ : syracuseStep 1727999 = 2591999) B2591999
theorem B779257 : Blo 511796 779257 := bstep (se 2 (by rfl) ⟨292221, by rfl⟩ : syracuseStep 779257 = 584443) B584443
theorem B8778617 : Blo 511796 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B783977 : Blo 511796 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B19235161 : Blo 511796 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B16715483 : Blo 511796 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B3904037 : Blo 511796 3904037 := bstep (se 4 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 3904037 = 732007) B732007
theorem B1151999 : Blo 511796 1151999 := bstep (se 1 (by rfl) ⟨863999, by rfl⟩ : syracuseStep 1151999 = 1727999) B1727999
theorem B11874127 : Blo 511796 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B864911 : Blo 511796 864911 := bstep (se 1 (by rfl) ⟨648683, by rfl⟩ : syracuseStep 864911 = 1297367) B1297367
theorem B769199 : Blo 511796 769199 := bstep (se 1 (by rfl) ⟨576899, by rfl⟩ : syracuseStep 769199 = 1153799) B1153799
theorem B2082287 : Blo 511796 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B5852411 : Blo 511796 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B1039009 : Blo 511796 1039009 := bstep (se 2 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 1039009 = 779257) B779257
theorem B973595 : Blo 511796 973595 := bstep (se 1 (by rfl) ⟨730196, by rfl⟩ : syracuseStep 973595 = 1460393) B1460393
theorem B2090605 : Blo 511796 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B4157983 : Blo 511796 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B2787473 : Blo 511796 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B3901607 : Blo 511796 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B11143655 : Blo 511796 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B15832169 : Blo 511796 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B5543977 : Blo 511796 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B1385345 : Blo 511796 1385345 := bstep (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) B1039009
theorem B1388191 : Blo 511796 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B2602691 : Blo 511796 2602691 := bstep (se 1 (by rfl) ⟨1952018, by rfl⟩ : syracuseStep 2602691 = 3904037) B3904037
theorem B767999 : Blo 511796 767999 := bstep (se 1 (by rfl) ⟨575999, by rfl⟩ : syracuseStep 767999 = 1151999) B1151999
theorem B576607 : Blo 511796 576607 := bstep (se 1 (by rfl) ⟨432455, by rfl⟩ : syracuseStep 576607 = 864911) B864911
theorem B512799 : Blo 511796 512799 := bstep (se 1 (by rfl) ⟨384599, by rfl⟩ : syracuseStep 512799 = 769199) B769199
theorem B25646881 : Blo 511796 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B649063 : Blo 511796 649063 := bstep (se 1 (by rfl) ⟨486797, by rfl⟩ : syracuseStep 649063 = 973595) B973595
theorem B10554779 : Blo 511796 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B2601071 : Blo 511796 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B865417 : Blo 511796 865417 := bstep (se 2 (by rfl) ⟨324531, by rfl⟩ : syracuseStep 865417 = 649063) B649063
theorem B768809 : Blo 511796 768809 := bstep (se 2 (by rfl) ⟨288303, by rfl⟩ : syracuseStep 768809 = 576607) B576607
theorem B1850921 : Blo 511796 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B34195841 : Blo 511796 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B7391969 : Blo 511796 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B511999 : Blo 511796 511999 := bstep (se 1 (by rfl) ⟨383999, by rfl⟩ : syracuseStep 511999 = 767999) B767999
theorem B1858315 : Blo 511796 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B7429103 : Blo 511796 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B3694253 : Blo 511796 3694253 := bstep (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) B1385345
theorem B1735127 : Blo 511796 1735127 := bstep (se 1 (by rfl) ⟨1301345, by rfl⟩ : syracuseStep 1735127 = 2602691) B2602691
theorem B4952735 : Blo 511796 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B1153889 : Blo 511796 1153889 := bstep (se 2 (by rfl) ⟨432708, by rfl⟩ : syracuseStep 1153889 = 865417) B865417
theorem B1156751 : Blo 511796 1156751 := bstep (se 1 (by rfl) ⟨867563, by rfl⟩ : syracuseStep 1156751 = 1735127) B1735127
theorem B4927979 : Blo 511796 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B2477753 : Blo 511796 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B9851341 : Blo 511796 9851341 := bstep (se 3 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 9851341 = 3694253) B3694253
theorem B512539 : Blo 511796 512539 := bstep (se 1 (by rfl) ⟨384404, by rfl⟩ : syracuseStep 512539 = 768809) B768809
theorem B1233947 : Blo 511796 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B22797227 : Blo 511796 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B7036519 : Blo 511796 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B1734047 : Blo 511796 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B822631 : Blo 511796 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B3285319 : Blo 511796 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B1156031 : Blo 511796 1156031 := bstep (se 1 (by rfl) ⟨867023, by rfl⟩ : syracuseStep 1156031 = 1734047) B1734047
theorem B9382025 : Blo 511796 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B1651835 : Blo 511796 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B769259 : Blo 511796 769259 := bstep (se 1 (by rfl) ⟨576944, by rfl⟩ : syracuseStep 769259 = 1153889) B1153889
theorem B771167 : Blo 511796 771167 := bstep (se 1 (by rfl) ⟨578375, by rfl⟩ : syracuseStep 771167 = 1156751) B1156751
theorem B3301823 : Blo 511796 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B15198151 : Blo 511796 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B13135121 : Blo 511796 13135121 := bstep (se 2 (by rfl) ⟨4925670, by rfl⟩ : syracuseStep 13135121 = 9851341) B9851341
theorem B8756747 : Blo 511796 8756747 := bstep (se 1 (by rfl) ⟨6567560, by rfl⟩ : syracuseStep 8756747 = 13135121) B13135121
theorem B20264201 : Blo 511796 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B1096841 : Blo 511796 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B25018733 : Blo 511796 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B770687 : Blo 511796 770687 := bstep (se 1 (by rfl) ⟨578015, by rfl⟩ : syracuseStep 770687 = 1156031) B1156031
theorem B1101223 : Blo 511796 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B512839 : Blo 511796 512839 := bstep (se 1 (by rfl) ⟨384629, by rfl⟩ : syracuseStep 512839 = 769259) B769259
theorem B4380425 : Blo 511796 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B514111 : Blo 511796 514111 := bstep (se 1 (by rfl) ⟨385583, by rfl⟩ : syracuseStep 514111 = 771167) B771167
theorem B8804861 : Blo 511796 8804861 := bstep (se 3 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 8804861 = 3301823) B3301823
theorem B16679155 : Blo 511796 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B2920283 : Blo 511796 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B5869907 : Blo 511796 5869907 := bstep (se 1 (by rfl) ⟨4402430, by rfl⟩ : syracuseStep 5869907 = 8804861) B8804861
theorem B5837831 : Blo 511796 5837831 := bstep (se 1 (by rfl) ⟨4378373, by rfl⟩ : syracuseStep 5837831 = 8756747) B8756747
theorem B2924909 : Blo 511796 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B13509467 : Blo 511796 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B513791 : Blo 511796 513791 := bstep (se 1 (by rfl) ⟨385343, by rfl⟩ : syracuseStep 513791 = 770687) B770687
theorem B1468297 : Blo 511796 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B1946855 : Blo 511796 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B3913271 : Blo 511796 3913271 := bstep (se 1 (by rfl) ⟨2934953, by rfl⟩ : syracuseStep 3913271 = 5869907) B5869907
theorem B1949939 : Blo 511796 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B22238873 : Blo 511796 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B1957729 : Blo 511796 1957729 := bstep (se 2 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 1957729 = 1468297) B1468297
theorem B3891887 : Blo 511796 3891887 := bstep (se 1 (by rfl) ⟨2918915, by rfl⟩ : syracuseStep 3891887 = 5837831) B5837831
theorem B9006311 : Blo 511796 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B2594591 : Blo 511796 2594591 := bstep (se 1 (by rfl) ⟨1945943, by rfl⟩ : syracuseStep 2594591 = 3891887) B3891887
theorem B6004207 : Blo 511796 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B14825915 : Blo 511796 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B1297903 : Blo 511796 1297903 := bstep (se 1 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 1297903 = 1946855) B1946855
theorem B2608847 : Blo 511796 2608847 := bstep (se 1 (by rfl) ⟨1956635, by rfl⟩ : syracuseStep 2608847 = 3913271) B3913271
theorem B2610305 : Blo 511796 2610305 := bstep (se 2 (by rfl) ⟨978864, by rfl⟩ : syracuseStep 2610305 = 1957729) B1957729
theorem B1299959 : Blo 511796 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B1739231 : Blo 511796 1739231 := bstep (se 1 (by rfl) ⟨1304423, by rfl⟩ : syracuseStep 1739231 = 2608847) B2608847
theorem B1740203 : Blo 511796 1740203 := bstep (se 1 (by rfl) ⟨1305152, by rfl⟩ : syracuseStep 1740203 = 2610305) B2610305
theorem B8005609 : Blo 511796 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B866639 : Blo 511796 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B9883943 : Blo 511796 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B1729727 : Blo 511796 1729727 := bstep (se 1 (by rfl) ⟨1297295, by rfl⟩ : syracuseStep 1729727 = 2594591) B2594591
theorem B1730537 : Blo 511796 1730537 := bstep (se 2 (by rfl) ⟨648951, by rfl⟩ : syracuseStep 1730537 = 1297903) B1297903
theorem B6589295 : Blo 511796 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B1153151 : Blo 511796 1153151 := bstep (se 1 (by rfl) ⟨864863, by rfl⟩ : syracuseStep 1153151 = 1729727) B1729727
theorem B1153691 : Blo 511796 1153691 := bstep (se 1 (by rfl) ⟨865268, by rfl⟩ : syracuseStep 1153691 = 1730537) B1730537
theorem B1159487 : Blo 511796 1159487 := bstep (se 1 (by rfl) ⟨869615, by rfl⟩ : syracuseStep 1159487 = 1739231) B1739231
theorem B1160135 : Blo 511796 1160135 := bstep (se 1 (by rfl) ⟨870101, by rfl⟩ : syracuseStep 1160135 = 1740203) B1740203
theorem B577759 : Blo 511796 577759 := bstep (se 1 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 577759 = 866639) B866639
theorem B10674145 : Blo 511796 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B4392863 : Blo 511796 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B14232193 : Blo 511796 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B768767 : Blo 511796 768767 := bstep (se 1 (by rfl) ⟨576575, by rfl⟩ : syracuseStep 768767 = 1153151) B1153151
theorem B769127 : Blo 511796 769127 := bstep (se 1 (by rfl) ⟨576845, by rfl⟩ : syracuseStep 769127 = 1153691) B1153691
theorem B770345 : Blo 511796 770345 := bstep (se 2 (by rfl) ⟨288879, by rfl⟩ : syracuseStep 770345 = 577759) B577759
theorem B772991 : Blo 511796 772991 := bstep (se 1 (by rfl) ⟨579743, by rfl⟩ : syracuseStep 772991 = 1159487) B1159487
theorem B773423 : Blo 511796 773423 := bstep (se 1 (by rfl) ⟨580067, by rfl⟩ : syracuseStep 773423 = 1160135) B1160135
theorem B2928575 : Blo 511796 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B75905029 : Blo 511796 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B512511 : Blo 511796 512511 := bstep (se 1 (by rfl) ⟨384383, by rfl⟩ : syracuseStep 512511 = 768767) B768767
theorem B512751 : Blo 511796 512751 := bstep (se 1 (by rfl) ⟨384563, by rfl⟩ : syracuseStep 512751 = 769127) B769127
theorem B513563 : Blo 511796 513563 := bstep (se 1 (by rfl) ⟨385172, by rfl⟩ : syracuseStep 513563 = 770345) B770345
theorem B515327 : Blo 511796 515327 := bstep (se 1 (by rfl) ⟨386495, by rfl⟩ : syracuseStep 515327 = 772991) B772991
theorem B515615 : Blo 511796 515615 := bstep (se 1 (by rfl) ⟨386711, by rfl⟩ : syracuseStep 515615 = 773423) B773423
theorem B1952383 : Blo 511796 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B101206705 : Blo 511796 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B134942273 : Blo 511796 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B2603177 : Blo 511796 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B89961515 : Blo 511796 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B1735451 : Blo 511796 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B59974343 : Blo 511796 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B1156967 : Blo 511796 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B39982895 : Blo 511796 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B771311 : Blo 511796 771311 := bstep (se 1 (by rfl) ⟨578483, by rfl⟩ : syracuseStep 771311 = 1156967) B1156967
theorem B26655263 : Blo 511796 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B514207 : Blo 511796 514207 := bstep (se 1 (by rfl) ⟨385655, by rfl⟩ : syracuseStep 514207 = 771311) B771311
theorem B17770175 : Blo 511796 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B11846783 : Blo 511796 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B31591421 : Blo 511796 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B21060947 : Blo 511796 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B14040631 : Blo 511796 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B18720841 : Blo 511796 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B24961121 : Blo 511796 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B16640747 : Blo 511796 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B11093831 : Blo 511796 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B7395887 : Blo 511796 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B19722365 : Blo 511796 19722365 := bstep (se 3 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 19722365 = 7395887) B7395887
theorem B13148243 : Blo 511796 13148243 := bstep (se 1 (by rfl) ⟨9861182, by rfl⟩ : syracuseStep 13148243 = 19722365) B19722365
theorem B8765495 : Blo 511796 8765495 := bstep (se 1 (by rfl) ⟨6574121, by rfl⟩ : syracuseStep 8765495 = 13148243) B13148243
theorem B5843663 : Blo 511796 5843663 := bstep (se 1 (by rfl) ⟨4382747, by rfl⟩ : syracuseStep 5843663 = 8765495) B8765495
theorem B3895775 : Blo 511796 3895775 := bstep (se 1 (by rfl) ⟨2921831, by rfl⟩ : syracuseStep 3895775 = 5843663) B5843663
theorem B2597183 : Blo 511796 2597183 := bstep (se 1 (by rfl) ⟨1947887, by rfl⟩ : syracuseStep 2597183 = 3895775) B3895775
theorem B1731455 : Blo 511796 1731455 := bstep (se 1 (by rfl) ⟨1298591, by rfl⟩ : syracuseStep 1731455 = 2597183) B2597183
theorem B1154303 : Blo 511796 1154303 := bstep (se 1 (by rfl) ⟨865727, by rfl⟩ : syracuseStep 1154303 = 1731455) B1731455
theorem B769535 : Blo 511796 769535 := bstep (se 1 (by rfl) ⟨577151, by rfl⟩ : syracuseStep 769535 = 1154303) B1154303
theorem B513023 : Blo 511796 513023 := bstep (se 1 (by rfl) ⟨384767, by rfl⟩ : syracuseStep 513023 = 769535) B769535

theorem C0 (j : ℕ) (h1 : 127949 ≤ j) (h2 : j ≤ 128648) : Blo 511796 (4 * j + 3) := by
  interval_cases j
  · exact B511799
  · exact B511803
  · exact B511807
  · exact B511811
  · exact B511815
  · exact B511819
  · exact B511823
  · exact B511827
  · exact B511831
  · exact B511835
  · exact B511839
  · exact B511843
  · exact B511847
  · exact B511851
  · exact B511855
  · exact B511859
  · exact B511863
  · exact B511867
  · exact B511871
  · exact B511875
  · exact B511879
  · exact B511883
  · exact B511887
  · exact B511891
  · exact B511895
  · exact B511899
  · exact B511903
  · exact B511907
  · exact B511911
  · exact B511915
  · exact B511919
  · exact B511923
  · exact B511927
  · exact B511931
  · exact B511935
  · exact B511939
  · exact B511943
  · exact B511947
  · exact B511951
  · exact B511955
  · exact B511959
  · exact B511963
  · exact B511967
  · exact B511971
  · exact B511975
  · exact B511979
  · exact B511983
  · exact B511987
  · exact B511991
  · exact B511995
  · exact B511999
  · exact B512003
  · exact B512007
  · exact B512011
  · exact B512015
  · exact B512019
  · exact B512023
  · exact B512027
  · exact B512031
  · exact B512035
  · exact B512039
  · exact B512043
  · exact B512047
  · exact B512051
  · exact B512055
  · exact B512059
  · exact B512063
  · exact B512067
  · exact B512071
  · exact B512075
  · exact B512079
  · exact B512083
  · exact B512087
  · exact B512091
  · exact B512095
  · exact B512099
  · exact B512103
  · exact B512107
  · exact B512111
  · exact B512115
  · exact B512119
  · exact B512123
  · exact B512127
  · exact B512131
  · exact B512135
  · exact B512139
  · exact B512143
  · exact B512147
  · exact B512151
  · exact B512155
  · exact B512159
  · exact B512163
  · exact B512167
  · exact B512171
  · exact B512175
  · exact B512179
  · exact B512183
  · exact B512187
  · exact B512191
  · exact B512195
  · exact B512199
  · exact B512203
  · exact B512207
  · exact B512211
  · exact B512215
  · exact B512219
  · exact B512223
  · exact B512227
  · exact B512231
  · exact B512235
  · exact B512239
  · exact B512243
  · exact B512247
  · exact B512251
  · exact B512255
  · exact B512259
  · exact B512263
  · exact B512267
  · exact B512271
  · exact B512275
  · exact B512279
  · exact B512283
  · exact B512287
  · exact B512291
  · exact B512295
  · exact B512299
  · exact B512303
  · exact B512307
  · exact B512311
  · exact B512315
  · exact B512319
  · exact B512323
  · exact B512327
  · exact B512331
  · exact B512335
  · exact B512339
  · exact B512343
  · exact B512347
  · exact B512351
  · exact B512355
  · exact B512359
  · exact B512363
  · exact B512367
  · exact B512371
  · exact B512375
  · exact B512379
  · exact B512383
  · exact B512387
  · exact B512391
  · exact B512395
  · exact B512399
  · exact B512403
  · exact B512407
  · exact B512411
  · exact B512415
  · exact B512419
  · exact B512423
  · exact B512427
  · exact B512431
  · exact B512435
  · exact B512439
  · exact B512443
  · exact B512447
  · exact B512451
  · exact B512455
  · exact B512459
  · exact B512463
  · exact B512467
  · exact B512471
  · exact B512475
  · exact B512479
  · exact B512483
  · exact B512487
  · exact B512491
  · exact B512495
  · exact B512499
  · exact B512503
  · exact B512507
  · exact B512511
  · exact B512515
  · exact B512519
  · exact B512523
  · exact B512527
  · exact B512531
  · exact B512535
  · exact B512539
  · exact B512543
  · exact B512547
  · exact B512551
  · exact B512555
  · exact B512559
  · exact B512563
  · exact B512567
  · exact B512571
  · exact B512575
  · exact B512579
  · exact B512583
  · exact B512587
  · exact B512591
  · exact B512595
  · exact B512599
  · exact B512603
  · exact B512607
  · exact B512611
  · exact B512615
  · exact B512619
  · exact B512623
  · exact B512627
  · exact B512631
  · exact B512635
  · exact B512639
  · exact B512643
  · exact B512647
  · exact B512651
  · exact B512655
  · exact B512659
  · exact B512663
  · exact B512667
  · exact B512671
  · exact B512675
  · exact B512679
  · exact B512683
  · exact B512687
  · exact B512691
  · exact B512695
  · exact B512699
  · exact B512703
  · exact B512707
  · exact B512711
  · exact B512715
  · exact B512719
  · exact B512723
  · exact B512727
  · exact B512731
  · exact B512735
  · exact B512739
  · exact B512743
  · exact B512747
  · exact B512751
  · exact B512755
  · exact B512759
  · exact B512763
  · exact B512767
  · exact B512771
  · exact B512775
  · exact B512779
  · exact B512783
  · exact B512787
  · exact B512791
  · exact B512795
  · exact B512799
  · exact B512803
  · exact B512807
  · exact B512811
  · exact B512815
  · exact B512819
  · exact B512823
  · exact B512827
  · exact B512831
  · exact B512835
  · exact B512839
  · exact B512843
  · exact B512847
  · exact B512851
  · exact B512855
  · exact B512859
  · exact B512863
  · exact B512867
  · exact B512871
  · exact B512875
  · exact B512879
  · exact B512883
  · exact B512887
  · exact B512891
  · exact B512895
  · exact B512899
  · exact B512903
  · exact B512907
  · exact B512911
  · exact B512915
  · exact B512919
  · exact B512923
  · exact B512927
  · exact B512931
  · exact B512935
  · exact B512939
  · exact B512943
  · exact B512947
  · exact B512951
  · exact B512955
  · exact B512959
  · exact B512963
  · exact B512967
  · exact B512971
  · exact B512975
  · exact B512979
  · exact B512983
  · exact B512987
  · exact B512991
  · exact B512995
  · exact B512999
  · exact B513003
  · exact B513007
  · exact B513011
  · exact B513015
  · exact B513019
  · exact B513023
  · exact B513027
  · exact B513031
  · exact B513035
  · exact B513039
  · exact B513043
  · exact B513047
  · exact B513051
  · exact B513055
  · exact B513059
  · exact B513063
  · exact B513067
  · exact B513071
  · exact B513075
  · exact B513079
  · exact B513083
  · exact B513087
  · exact B513091
  · exact B513095
  · exact B513099
  · exact B513103
  · exact B513107
  · exact B513111
  · exact B513115
  · exact B513119
  · exact B513123
  · exact B513127
  · exact B513131
  · exact B513135
  · exact B513139
  · exact B513143
  · exact B513147
  · exact B513151
  · exact B513155
  · exact B513159
  · exact B513163
  · exact B513167
  · exact B513171
  · exact B513175
  · exact B513179
  · exact B513183
  · exact B513187
  · exact B513191
  · exact B513195
  · exact B513199
  · exact B513203
  · exact B513207
  · exact B513211
  · exact B513215
  · exact B513219
  · exact B513223
  · exact B513227
  · exact B513231
  · exact B513235
  · exact B513239
  · exact B513243
  · exact B513247
  · exact B513251
  · exact B513255
  · exact B513259
  · exact B513263
  · exact B513267
  · exact B513271
  · exact B513275
  · exact B513279
  · exact B513283
  · exact B513287
  · exact B513291
  · exact B513295
  · exact B513299
  · exact B513303
  · exact B513307
  · exact B513311
  · exact B513315
  · exact B513319
  · exact B513323
  · exact B513327
  · exact B513331
  · exact B513335
  · exact B513339
  · exact B513343
  · exact B513347
  · exact B513351
  · exact B513355
  · exact B513359
  · exact B513363
  · exact B513367
  · exact B513371
  · exact B513375
  · exact B513379
  · exact B513383
  · exact B513387
  · exact B513391
  · exact B513395
  · exact B513399
  · exact B513403
  · exact B513407
  · exact B513411
  · exact B513415
  · exact B513419
  · exact B513423
  · exact B513427
  · exact B513431
  · exact B513435
  · exact B513439
  · exact B513443
  · exact B513447
  · exact B513451
  · exact B513455
  · exact B513459
  · exact B513463
  · exact B513467
  · exact B513471
  · exact B513475
  · exact B513479
  · exact B513483
  · exact B513487
  · exact B513491
  · exact B513495
  · exact B513499
  · exact B513503
  · exact B513507
  · exact B513511
  · exact B513515
  · exact B513519
  · exact B513523
  · exact B513527
  · exact B513531
  · exact B513535
  · exact B513539
  · exact B513543
  · exact B513547
  · exact B513551
  · exact B513555
  · exact B513559
  · exact B513563
  · exact B513567
  · exact B513571
  · exact B513575
  · exact B513579
  · exact B513583
  · exact B513587
  · exact B513591
  · exact B513595
  · exact B513599
  · exact B513603
  · exact B513607
  · exact B513611
  · exact B513615
  · exact B513619
  · exact B513623
  · exact B513627
  · exact B513631
  · exact B513635
  · exact B513639
  · exact B513643
  · exact B513647
  · exact B513651
  · exact B513655
  · exact B513659
  · exact B513663
  · exact B513667
  · exact B513671
  · exact B513675
  · exact B513679
  · exact B513683
  · exact B513687
  · exact B513691
  · exact B513695
  · exact B513699
  · exact B513703
  · exact B513707
  · exact B513711
  · exact B513715
  · exact B513719
  · exact B513723
  · exact B513727
  · exact B513731
  · exact B513735
  · exact B513739
  · exact B513743
  · exact B513747
  · exact B513751
  · exact B513755
  · exact B513759
  · exact B513763
  · exact B513767
  · exact B513771
  · exact B513775
  · exact B513779
  · exact B513783
  · exact B513787
  · exact B513791
  · exact B513795
  · exact B513799
  · exact B513803
  · exact B513807
  · exact B513811
  · exact B513815
  · exact B513819
  · exact B513823
  · exact B513827
  · exact B513831
  · exact B513835
  · exact B513839
  · exact B513843
  · exact B513847
  · exact B513851
  · exact B513855
  · exact B513859
  · exact B513863
  · exact B513867
  · exact B513871
  · exact B513875
  · exact B513879
  · exact B513883
  · exact B513887
  · exact B513891
  · exact B513895
  · exact B513899
  · exact B513903
  · exact B513907
  · exact B513911
  · exact B513915
  · exact B513919
  · exact B513923
  · exact B513927
  · exact B513931
  · exact B513935
  · exact B513939
  · exact B513943
  · exact B513947
  · exact B513951
  · exact B513955
  · exact B513959
  · exact B513963
  · exact B513967
  · exact B513971
  · exact B513975
  · exact B513979
  · exact B513983
  · exact B513987
  · exact B513991
  · exact B513995
  · exact B513999
  · exact B514003
  · exact B514007
  · exact B514011
  · exact B514015
  · exact B514019
  · exact B514023
  · exact B514027
  · exact B514031
  · exact B514035
  · exact B514039
  · exact B514043
  · exact B514047
  · exact B514051
  · exact B514055
  · exact B514059
  · exact B514063
  · exact B514067
  · exact B514071
  · exact B514075
  · exact B514079
  · exact B514083
  · exact B514087
  · exact B514091
  · exact B514095
  · exact B514099
  · exact B514103
  · exact B514107
  · exact B514111
  · exact B514115
  · exact B514119
  · exact B514123
  · exact B514127
  · exact B514131
  · exact B514135
  · exact B514139
  · exact B514143
  · exact B514147
  · exact B514151
  · exact B514155
  · exact B514159
  · exact B514163
  · exact B514167
  · exact B514171
  · exact B514175
  · exact B514179
  · exact B514183
  · exact B514187
  · exact B514191
  · exact B514195
  · exact B514199
  · exact B514203
  · exact B514207
  · exact B514211
  · exact B514215
  · exact B514219
  · exact B514223
  · exact B514227
  · exact B514231
  · exact B514235
  · exact B514239
  · exact B514243
  · exact B514247
  · exact B514251
  · exact B514255
  · exact B514259
  · exact B514263
  · exact B514267
  · exact B514271
  · exact B514275
  · exact B514279
  · exact B514283
  · exact B514287
  · exact B514291
  · exact B514295
  · exact B514299
  · exact B514303
  · exact B514307
  · exact B514311
  · exact B514315
  · exact B514319
  · exact B514323
  · exact B514327
  · exact B514331
  · exact B514335
  · exact B514339
  · exact B514343
  · exact B514347
  · exact B514351
  · exact B514355
  · exact B514359
  · exact B514363
  · exact B514367
  · exact B514371
  · exact B514375
  · exact B514379
  · exact B514383
  · exact B514387
  · exact B514391
  · exact B514395
  · exact B514399
  · exact B514403
  · exact B514407
  · exact B514411
  · exact B514415
  · exact B514419
  · exact B514423
  · exact B514427
  · exact B514431
  · exact B514435
  · exact B514439
  · exact B514443
  · exact B514447
  · exact B514451
  · exact B514455
  · exact B514459
  · exact B514463
  · exact B514467
  · exact B514471
  · exact B514475
  · exact B514479
  · exact B514483
  · exact B514487
  · exact B514491
  · exact B514495
  · exact B514499
  · exact B514503
  · exact B514507
  · exact B514511
  · exact B514515
  · exact B514519
  · exact B514523
  · exact B514527
  · exact B514531
  · exact B514535
  · exact B514539
  · exact B514543
  · exact B514547
  · exact B514551
  · exact B514555
  · exact B514559
  · exact B514563
  · exact B514567
  · exact B514571
  · exact B514575
  · exact B514579
  · exact B514583
  · exact B514587
  · exact B514591
  · exact B514595

theorem C1 (j : ℕ) (h1 : 128649 ≤ j) (h2 : j ≤ 128948) : Blo 511796 (4 * j + 3) := by
  interval_cases j
  · exact B514599
  · exact B514603
  · exact B514607
  · exact B514611
  · exact B514615
  · exact B514619
  · exact B514623
  · exact B514627
  · exact B514631
  · exact B514635
  · exact B514639
  · exact B514643
  · exact B514647
  · exact B514651
  · exact B514655
  · exact B514659
  · exact B514663
  · exact B514667
  · exact B514671
  · exact B514675
  · exact B514679
  · exact B514683
  · exact B514687
  · exact B514691
  · exact B514695
  · exact B514699
  · exact B514703
  · exact B514707
  · exact B514711
  · exact B514715
  · exact B514719
  · exact B514723
  · exact B514727
  · exact B514731
  · exact B514735
  · exact B514739
  · exact B514743
  · exact B514747
  · exact B514751
  · exact B514755
  · exact B514759
  · exact B514763
  · exact B514767
  · exact B514771
  · exact B514775
  · exact B514779
  · exact B514783
  · exact B514787
  · exact B514791
  · exact B514795
  · exact B514799
  · exact B514803
  · exact B514807
  · exact B514811
  · exact B514815
  · exact B514819
  · exact B514823
  · exact B514827
  · exact B514831
  · exact B514835
  · exact B514839
  · exact B514843
  · exact B514847
  · exact B514851
  · exact B514855
  · exact B514859
  · exact B514863
  · exact B514867
  · exact B514871
  · exact B514875
  · exact B514879
  · exact B514883
  · exact B514887
  · exact B514891
  · exact B514895
  · exact B514899
  · exact B514903
  · exact B514907
  · exact B514911
  · exact B514915
  · exact B514919
  · exact B514923
  · exact B514927
  · exact B514931
  · exact B514935
  · exact B514939
  · exact B514943
  · exact B514947
  · exact B514951
  · exact B514955
  · exact B514959
  · exact B514963
  · exact B514967
  · exact B514971
  · exact B514975
  · exact B514979
  · exact B514983
  · exact B514987
  · exact B514991
  · exact B514995
  · exact B514999
  · exact B515003
  · exact B515007
  · exact B515011
  · exact B515015
  · exact B515019
  · exact B515023
  · exact B515027
  · exact B515031
  · exact B515035
  · exact B515039
  · exact B515043
  · exact B515047
  · exact B515051
  · exact B515055
  · exact B515059
  · exact B515063
  · exact B515067
  · exact B515071
  · exact B515075
  · exact B515079
  · exact B515083
  · exact B515087
  · exact B515091
  · exact B515095
  · exact B515099
  · exact B515103
  · exact B515107
  · exact B515111
  · exact B515115
  · exact B515119
  · exact B515123
  · exact B515127
  · exact B515131
  · exact B515135
  · exact B515139
  · exact B515143
  · exact B515147
  · exact B515151
  · exact B515155
  · exact B515159
  · exact B515163
  · exact B515167
  · exact B515171
  · exact B515175
  · exact B515179
  · exact B515183
  · exact B515187
  · exact B515191
  · exact B515195
  · exact B515199
  · exact B515203
  · exact B515207
  · exact B515211
  · exact B515215
  · exact B515219
  · exact B515223
  · exact B515227
  · exact B515231
  · exact B515235
  · exact B515239
  · exact B515243
  · exact B515247
  · exact B515251
  · exact B515255
  · exact B515259
  · exact B515263
  · exact B515267
  · exact B515271
  · exact B515275
  · exact B515279
  · exact B515283
  · exact B515287
  · exact B515291
  · exact B515295
  · exact B515299
  · exact B515303
  · exact B515307
  · exact B515311
  · exact B515315
  · exact B515319
  · exact B515323
  · exact B515327
  · exact B515331
  · exact B515335
  · exact B515339
  · exact B515343
  · exact B515347
  · exact B515351
  · exact B515355
  · exact B515359
  · exact B515363
  · exact B515367
  · exact B515371
  · exact B515375
  · exact B515379
  · exact B515383
  · exact B515387
  · exact B515391
  · exact B515395
  · exact B515399
  · exact B515403
  · exact B515407
  · exact B515411
  · exact B515415
  · exact B515419
  · exact B515423
  · exact B515427
  · exact B515431
  · exact B515435
  · exact B515439
  · exact B515443
  · exact B515447
  · exact B515451
  · exact B515455
  · exact B515459
  · exact B515463
  · exact B515467
  · exact B515471
  · exact B515475
  · exact B515479
  · exact B515483
  · exact B515487
  · exact B515491
  · exact B515495
  · exact B515499
  · exact B515503
  · exact B515507
  · exact B515511
  · exact B515515
  · exact B515519
  · exact B515523
  · exact B515527
  · exact B515531
  · exact B515535
  · exact B515539
  · exact B515543
  · exact B515547
  · exact B515551
  · exact B515555
  · exact B515559
  · exact B515563
  · exact B515567
  · exact B515571
  · exact B515575
  · exact B515579
  · exact B515583
  · exact B515587
  · exact B515591
  · exact B515595
  · exact B515599
  · exact B515603
  · exact B515607
  · exact B515611
  · exact B515615
  · exact B515619
  · exact B515623
  · exact B515627
  · exact B515631
  · exact B515635
  · exact B515639
  · exact B515643
  · exact B515647
  · exact B515651
  · exact B515655
  · exact B515659
  · exact B515663
  · exact B515667
  · exact B515671
  · exact B515675
  · exact B515679
  · exact B515683
  · exact B515687
  · exact B515691
  · exact B515695
  · exact B515699
  · exact B515703
  · exact B515707
  · exact B515711
  · exact B515715
  · exact B515719
  · exact B515723
  · exact B515727
  · exact B515731
  · exact B515735
  · exact B515739
  · exact B515743
  · exact B515747
  · exact B515751
  · exact B515755
  · exact B515759
  · exact B515763
  · exact B515767
  · exact B515771
  · exact B515775
  · exact B515779
  · exact B515783
  · exact B515787
  · exact B515791
  · exact B515795

theorem solution (m : ℕ) (hlo : 511796 ≤ m) (hhi : m ≤ 515796) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 127949 ≤ j := by omega
    have hj2 : j ≤ 128948 := by omega
    have hb : Blo 511796 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 128649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
