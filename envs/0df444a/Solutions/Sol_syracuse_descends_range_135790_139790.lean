-- Prove2me | solution 1 for syracuse_descends_range_135790_139790
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:35.815321+00:00
-- url     : https://prove2.me/submissions/11e6fb50-ebb3-4cbf-82ec-1864b6000586

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


theorem B229405 : Blo 135790 229405 := bbase (se 3 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 229405 = 86027) (by norm_num)
theorem B163885 : Blo 135790 163885 := bbase (se 3 (by rfl) ⟨30728, by rfl⟩ : syracuseStep 163885 = 61457) (by norm_num)
theorem B458837 : Blo 135790 458837 := bbase (se 8 (by rfl) ⟨2688, by rfl⟩ : syracuseStep 458837 = 5377) (by norm_num)
theorem B229493 : Blo 135790 229493 := bbase (se 5 (by rfl) ⟨10757, by rfl⟩ : syracuseStep 229493 = 21515) (by norm_num)
theorem B163981 : Blo 135790 163981 := bbase (se 3 (by rfl) ⟨30746, by rfl⟩ : syracuseStep 163981 = 61493) (by norm_num)
theorem B327845 : Blo 135790 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B950453 : Blo 135790 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B262349 : Blo 135790 262349 := bbase (se 3 (by rfl) ⟨49190, by rfl⟩ : syracuseStep 262349 = 98381) (by norm_num)
theorem B524501 : Blo 135790 524501 := bbase (se 7 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 524501 = 12293) (by norm_num)
theorem B229621 : Blo 135790 229621 := bbase (se 5 (by rfl) ⟨10763, by rfl⟩ : syracuseStep 229621 = 21527) (by norm_num)
theorem B196933 : Blo 135790 196933 := bbase (se 4 (by rfl) ⟨18462, by rfl⟩ : syracuseStep 196933 = 36925) (by norm_num)
theorem B229709 : Blo 135790 229709 := bbase (se 3 (by rfl) ⟨43070, by rfl⟩ : syracuseStep 229709 = 86141) (by norm_num)
theorem B786773 : Blo 135790 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B164269 : Blo 135790 164269 := bbase (se 3 (by rfl) ⟨30800, by rfl⟩ : syracuseStep 164269 = 61601) (by norm_num)
theorem B229837 : Blo 135790 229837 := bbase (se 3 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 229837 = 86189) (by norm_num)
theorem B524789 : Blo 135790 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B459269 : Blo 135790 459269 := bbase (se 4 (by rfl) ⟨43056, by rfl⟩ : syracuseStep 459269 = 86113) (by norm_num)
theorem B688661 : Blo 135790 688661 := bbase (se 6 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 688661 = 32281) (by norm_num)
theorem B197149 : Blo 135790 197149 := bbase (se 3 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 197149 = 73931) (by norm_num)
theorem B229925 : Blo 135790 229925 := bbase (se 4 (by rfl) ⟨21555, by rfl⟩ : syracuseStep 229925 = 43111) (by norm_num)
theorem B393797 : Blo 135790 393797 := bbase (se 4 (by rfl) ⟨36918, by rfl⟩ : syracuseStep 393797 = 73837) (by norm_num)
theorem B164461 : Blo 135790 164461 := bbase (se 3 (by rfl) ⟨30836, by rfl⟩ : syracuseStep 164461 = 61673) (by norm_num)
theorem B230053 : Blo 135790 230053 := bbase (se 4 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 230053 = 43135) (by norm_num)
theorem B230141 : Blo 135790 230141 := bbase (se 3 (by rfl) ⟨43151, by rfl⟩ : syracuseStep 230141 = 86303) (by norm_num)
theorem B295741 : Blo 135790 295741 := bbase (se 3 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 295741 = 110903) (by norm_num)
theorem B394069 : Blo 135790 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B230269 : Blo 135790 230269 := bbase (se 3 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 230269 = 86351) (by norm_num)
theorem B197525 : Blo 135790 197525 := bbase (se 6 (by rfl) ⟨4629, by rfl⟩ : syracuseStep 197525 = 9259) (by norm_num)
theorem B459701 : Blo 135790 459701 := bbase (se 5 (by rfl) ⟨21548, by rfl⟩ : syracuseStep 459701 = 43097) (by norm_num)
theorem B263101 : Blo 135790 263101 := bbase (se 3 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 263101 = 98663) (by norm_num)
theorem B230357 : Blo 135790 230357 := bbase (se 7 (by rfl) ⟨2699, by rfl⟩ : syracuseStep 230357 = 5399) (by norm_num)
theorem B590885 : Blo 135790 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B263245 : Blo 135790 263245 := bbase (se 3 (by rfl) ⟨49358, by rfl⟩ : syracuseStep 263245 = 98717) (by norm_num)
theorem B230485 : Blo 135790 230485 := bbase (se 8 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 230485 = 2701) (by norm_num)
theorem B230573 : Blo 135790 230573 := bbase (se 3 (by rfl) ⟨43232, by rfl⟩ : syracuseStep 230573 = 86465) (by norm_num)
theorem B885941 : Blo 135790 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B263405 : Blo 135790 263405 := bbase (se 3 (by rfl) ⟨49388, by rfl⟩ : syracuseStep 263405 = 98777) (by norm_num)
theorem B230701 : Blo 135790 230701 := bbase (se 3 (by rfl) ⟨43256, by rfl⟩ : syracuseStep 230701 = 86513) (by norm_num)
theorem B296237 : Blo 135790 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B656693 : Blo 135790 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B460133 : Blo 135790 460133 := bbase (se 4 (by rfl) ⟨43137, by rfl⟩ : syracuseStep 460133 = 86275) (by norm_num)
theorem B263549 : Blo 135790 263549 := bbase (se 3 (by rfl) ⟨49415, by rfl⟩ : syracuseStep 263549 = 98831) (by norm_num)
theorem B230789 : Blo 135790 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B165341 : Blo 135790 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B230917 : Blo 135790 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B231005 : Blo 135790 231005 := bbase (se 3 (by rfl) ⟨43313, by rfl⟩ : syracuseStep 231005 = 86627) (by norm_num)
theorem B525973 : Blo 135790 525973 := bbase (se 6 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 525973 = 24655) (by norm_num)
theorem B263837 : Blo 135790 263837 := bbase (se 3 (by rfl) ⟨49469, by rfl⟩ : syracuseStep 263837 = 98939) (by norm_num)
theorem B624293 : Blo 135790 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B362165 : Blo 135790 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B231133 : Blo 135790 231133 := bbase (se 3 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 231133 = 86675) (by norm_num)
theorem B460565 : Blo 135790 460565 := bbase (se 6 (by rfl) ⟨10794, by rfl⟩ : syracuseStep 460565 = 21589) (by norm_num)
theorem B689957 : Blo 135790 689957 := bbase (se 4 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 689957 = 129367) (by norm_num)
theorem B231221 : Blo 135790 231221 := bbase (se 5 (by rfl) ⟨10838, by rfl⟩ : syracuseStep 231221 = 21677) (by norm_num)
theorem B263989 : Blo 135790 263989 := bbase (se 5 (by rfl) ⟨12374, by rfl⟩ : syracuseStep 263989 = 24749) (by norm_num)
theorem B231349 : Blo 135790 231349 := bbase (se 5 (by rfl) ⟨10844, by rfl⟩ : syracuseStep 231349 = 21689) (by norm_num)
theorem B526277 : Blo 135790 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B165845 : Blo 135790 165845 := bbase (se 7 (by rfl) ⟨1943, by rfl⟩ : syracuseStep 165845 = 3887) (by norm_num)
theorem B165893 : Blo 135790 165893 := bbase (se 4 (by rfl) ⟨15552, by rfl⟩ : syracuseStep 165893 = 31105) (by norm_num)
theorem B231437 : Blo 135790 231437 := bbase (se 3 (by rfl) ⟨43394, by rfl⟩ : syracuseStep 231437 = 86789) (by norm_num)
theorem B591893 : Blo 135790 591893 := bbase (se 6 (by rfl) ⟨13872, by rfl⟩ : syracuseStep 591893 = 27745) (by norm_num)
theorem B264293 : Blo 135790 264293 := bbase (se 4 (by rfl) ⟨24777, by rfl⟩ : syracuseStep 264293 = 49555) (by norm_num)
theorem B329845 : Blo 135790 329845 := bbase (se 5 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 329845 = 30923) (by norm_num)
theorem B395381 : Blo 135790 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B231565 : Blo 135790 231565 := bbase (se 3 (by rfl) ⟨43418, by rfl⟩ : syracuseStep 231565 = 86837) (by norm_num)
theorem B297125 : Blo 135790 297125 := bbase (se 4 (by rfl) ⟨27855, by rfl⟩ : syracuseStep 297125 = 55711) (by norm_num)
theorem B460997 : Blo 135790 460997 := bbase (se 4 (by rfl) ⟨43218, by rfl⟩ : syracuseStep 460997 = 86437) (by norm_num)
theorem B329941 : Blo 135790 329941 := bbase (se 7 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 329941 = 7733) (by norm_num)
theorem B231653 : Blo 135790 231653 := bbase (se 4 (by rfl) ⟨21717, by rfl⟩ : syracuseStep 231653 = 43435) (by norm_num)
theorem B166153 : Blo 135790 166153 := bbase (se 2 (by rfl) ⟨62307, by rfl⟩ : syracuseStep 166153 = 124615) (by norm_num)
theorem B297245 : Blo 135790 297245 := bbase (se 3 (by rfl) ⟨55733, by rfl⟩ : syracuseStep 297245 = 111467) (by norm_num)
theorem B264485 : Blo 135790 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B198949 : Blo 135790 198949 := bbase (se 4 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 198949 = 37303) (by norm_num)
theorem B231781 : Blo 135790 231781 := bbase (se 4 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 231781 = 43459) (by norm_num)
theorem B231869 : Blo 135790 231869 := bbase (se 3 (by rfl) ⟨43475, by rfl⟩ : syracuseStep 231869 = 86951) (by norm_num)
theorem B428485 : Blo 135790 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B1051093 : Blo 135790 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B166417 : Blo 135790 166417 := bbase (se 2 (by rfl) ⟨62406, by rfl⟩ : syracuseStep 166417 = 124813) (by norm_num)
theorem B625205 : Blo 135790 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B231997 : Blo 135790 231997 := bbase (se 3 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 231997 = 86999) (by norm_num)
theorem B461429 : Blo 135790 461429 := bbase (se 5 (by rfl) ⟨21629, by rfl⟩ : syracuseStep 461429 = 43259) (by norm_num)
theorem B658037 : Blo 135790 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B166537 : Blo 135790 166537 := bbase (se 2 (by rfl) ⟨62451, by rfl⟩ : syracuseStep 166537 = 124903) (by norm_num)
theorem B232085 : Blo 135790 232085 := bbase (se 6 (by rfl) ⟨5439, by rfl⟩ : syracuseStep 232085 = 10879) (by norm_num)
theorem B232213 : Blo 135790 232213 := bbase (se 6 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 232213 = 10885) (by norm_num)
theorem B396053 : Blo 135790 396053 := bbase (se 6 (by rfl) ⟨9282, by rfl⟩ : syracuseStep 396053 = 18565) (by norm_num)
theorem B265045 : Blo 135790 265045 := bbase (se 9 (by rfl) ⟨776, by rfl⟩ : syracuseStep 265045 = 1553) (by norm_num)
theorem B232301 : Blo 135790 232301 := bbase (se 3 (by rfl) ⟨43556, by rfl⟩ : syracuseStep 232301 = 87113) (by norm_num)
theorem B297877 : Blo 135790 297877 := bbase (se 6 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 297877 = 13963) (by norm_num)
theorem B330725 : Blo 135790 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B265189 : Blo 135790 265189 := bbase (se 4 (by rfl) ⟨24861, by rfl⟩ : syracuseStep 265189 = 49723) (by norm_num)
theorem B232429 : Blo 135790 232429 := bbase (se 3 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 232429 = 87161) (by norm_num)
theorem B461861 : Blo 135790 461861 := bbase (se 4 (by rfl) ⟨43299, by rfl⟩ : syracuseStep 461861 = 86599) (by norm_num)
theorem B691253 : Blo 135790 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B232517 : Blo 135790 232517 := bbase (se 4 (by rfl) ⟨21798, by rfl⟩ : syracuseStep 232517 = 43597) (by norm_num)
theorem B265349 : Blo 135790 265349 := bbase (se 4 (by rfl) ⟨24876, by rfl⟩ : syracuseStep 265349 = 49753) (by norm_num)
theorem B232645 : Blo 135790 232645 := bbase (se 4 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 232645 = 43621) (by norm_num)
theorem B396485 : Blo 135790 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B331037 : Blo 135790 331037 := bbase (se 3 (by rfl) ⟨62069, by rfl⟩ : syracuseStep 331037 = 124139) (by norm_num)
theorem B232733 : Blo 135790 232733 := bbase (se 3 (by rfl) ⟨43637, by rfl⟩ : syracuseStep 232733 = 87275) (by norm_num)
theorem B232861 : Blo 135790 232861 := bbase (se 3 (by rfl) ⟨43661, by rfl⟩ : syracuseStep 232861 = 87323) (by norm_num)
theorem B462293 : Blo 135790 462293 := bbase (se 7 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 462293 = 10835) (by norm_num)
theorem B167393 : Blo 135790 167393 := bbase (se 2 (by rfl) ⟨62772, by rfl⟩ : syracuseStep 167393 = 125545) (by norm_num)
theorem B232949 : Blo 135790 232949 := bbase (se 5 (by rfl) ⟨10919, by rfl⟩ : syracuseStep 232949 = 21839) (by norm_num)
theorem B233077 : Blo 135790 233077 := bbase (se 5 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 233077 = 21851) (by norm_num)
theorem B298669 : Blo 135790 298669 := bbase (se 3 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 298669 = 112001) (by norm_num)
theorem B233165 : Blo 135790 233165 := bbase (se 3 (by rfl) ⟨43718, by rfl⟩ : syracuseStep 233165 = 87437) (by norm_num)
theorem B593669 : Blo 135790 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B233293 : Blo 135790 233293 := bbase (se 3 (by rfl) ⟨43742, by rfl⟩ : syracuseStep 233293 = 87485) (by norm_num)
theorem B462725 : Blo 135790 462725 := bbase (se 4 (by rfl) ⟨43380, by rfl⟩ : syracuseStep 462725 = 86761) (by norm_num)
theorem B233381 : Blo 135790 233381 := bbase (se 4 (by rfl) ⟨21879, by rfl⟩ : syracuseStep 233381 = 43759) (by norm_num)
theorem B397237 : Blo 135790 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B528389 : Blo 135790 528389 := bbase (se 4 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 528389 = 99073) (by norm_num)
theorem B233509 : Blo 135790 233509 := bbase (se 4 (by rfl) ⟨21891, by rfl⟩ : syracuseStep 233509 = 43783) (by norm_num)
theorem B233597 : Blo 135790 233597 := bbase (se 3 (by rfl) ⟨43799, by rfl⟩ : syracuseStep 233597 = 87599) (by norm_num)
theorem B331997 : Blo 135790 331997 := bbase (se 3 (by rfl) ⟨62249, by rfl⟩ : syracuseStep 331997 = 124499) (by norm_num)
theorem B233725 : Blo 135790 233725 := bbase (se 3 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 233725 = 87647) (by norm_num)
theorem B528677 : Blo 135790 528677 := bbase (se 4 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 528677 = 99127) (by norm_num)
theorem B463157 : Blo 135790 463157 := bbase (se 5 (by rfl) ⟨21710, by rfl⟩ : syracuseStep 463157 = 43421) (by norm_num)
theorem B692549 : Blo 135790 692549 := bbase (se 4 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 692549 = 129853) (by norm_num)
theorem B1118549 : Blo 135790 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B233813 : Blo 135790 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B1249717 : Blo 135790 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B233941 : Blo 135790 233941 := bbase (se 7 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 233941 = 5483) (by norm_num)
theorem B234029 : Blo 135790 234029 := bbase (se 3 (by rfl) ⟨43880, by rfl⟩ : syracuseStep 234029 = 87761) (by norm_num)
theorem B234157 : Blo 135790 234157 := bbase (se 3 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 234157 = 87809) (by norm_num)
theorem B463589 : Blo 135790 463589 := bbase (se 4 (by rfl) ⟨43461, by rfl⟩ : syracuseStep 463589 = 86923) (by norm_num)
theorem B234245 : Blo 135790 234245 := bbase (se 4 (by rfl) ⟨21960, by rfl⟩ : syracuseStep 234245 = 43921) (by norm_num)
theorem B2954069 : Blo 135790 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B234373 : Blo 135790 234373 := bbase (se 4 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 234373 = 43945) (by norm_num)
theorem B234461 : Blo 135790 234461 := bbase (se 3 (by rfl) ⟨43961, by rfl⟩ : syracuseStep 234461 = 87923) (by norm_num)
theorem B234589 : Blo 135790 234589 := bbase (se 3 (by rfl) ⟨43985, by rfl⟩ : syracuseStep 234589 = 87971) (by norm_num)
theorem B464021 : Blo 135790 464021 := bbase (se 6 (by rfl) ⟨10875, by rfl⟩ : syracuseStep 464021 = 21751) (by norm_num)
theorem B234677 : Blo 135790 234677 := bbase (se 5 (by rfl) ⟨11000, by rfl⟩ : syracuseStep 234677 = 22001) (by norm_num)
theorem B627941 : Blo 135790 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B300269 : Blo 135790 300269 := bbase (se 3 (by rfl) ⟨56300, by rfl⟩ : syracuseStep 300269 = 112601) (by norm_num)
theorem B234805 : Blo 135790 234805 := bbase (se 5 (by rfl) ⟨11006, by rfl⟩ : syracuseStep 234805 = 22013) (by norm_num)
theorem B300349 : Blo 135790 300349 := bbase (se 3 (by rfl) ⟨56315, by rfl⟩ : syracuseStep 300349 = 112631) (by norm_num)
theorem B234893 : Blo 135790 234893 := bbase (se 3 (by rfl) ⟨44042, by rfl⟩ : syracuseStep 234893 = 88085) (by norm_num)
theorem B1054133 : Blo 135790 1054133 := bbase (se 5 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 1054133 = 98825) (by norm_num)
theorem B529861 : Blo 135790 529861 := bbase (se 4 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 529861 = 99349) (by norm_num)
theorem B235021 : Blo 135790 235021 := bbase (se 3 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 235021 = 88133) (by norm_num)
theorem B955925 : Blo 135790 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B464453 : Blo 135790 464453 := bbase (se 4 (by rfl) ⟨43542, by rfl⟩ : syracuseStep 464453 = 87085) (by norm_num)
theorem B693845 : Blo 135790 693845 := bbase (se 8 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 693845 = 8131) (by norm_num)
theorem B235109 : Blo 135790 235109 := bbase (se 4 (by rfl) ⟨22041, by rfl⟩ : syracuseStep 235109 = 44083) (by norm_num)
theorem B235237 : Blo 135790 235237 := bbase (se 4 (by rfl) ⟨22053, by rfl⟩ : syracuseStep 235237 = 44107) (by norm_num)
theorem B530165 : Blo 135790 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B235325 : Blo 135790 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B333757 : Blo 135790 333757 := bbase (se 3 (by rfl) ⟨62579, by rfl⟩ : syracuseStep 333757 = 125159) (by norm_num)
theorem B235453 : Blo 135790 235453 := bbase (se 3 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 235453 = 88295) (by norm_num)
theorem B464885 : Blo 135790 464885 := bbase (se 5 (by rfl) ⟨21791, by rfl⟩ : syracuseStep 464885 = 43583) (by norm_num)
theorem B235541 : Blo 135790 235541 := bbase (se 6 (by rfl) ⟨5520, by rfl⟩ : syracuseStep 235541 = 11041) (by norm_num)
theorem B497765 : Blo 135790 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B235669 : Blo 135790 235669 := bbase (se 6 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 235669 = 11047) (by norm_num)
theorem B333989 : Blo 135790 333989 := bbase (se 4 (by rfl) ⟨31311, by rfl⟩ : syracuseStep 333989 = 62623) (by norm_num)
theorem B235757 : Blo 135790 235757 := bbase (se 3 (by rfl) ⟨44204, by rfl⟩ : syracuseStep 235757 = 88409) (by norm_num)
theorem B661765 : Blo 135790 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B235781 : Blo 135790 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B891157 : Blo 135790 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B235885 : Blo 135790 235885 := bbase (se 3 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 235885 = 88457) (by norm_num)
theorem B465317 : Blo 135790 465317 := bbase (se 4 (by rfl) ⟨43623, by rfl⟩ : syracuseStep 465317 = 87247) (by norm_num)
theorem B203293 : Blo 135790 203293 := bbase (se 3 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 203293 = 76235) (by norm_num)
theorem B334381 : Blo 135790 334381 := bbase (se 3 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 334381 = 125393) (by norm_num)
theorem B662069 : Blo 135790 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B465749 : Blo 135790 465749 := bbase (se 9 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 465749 = 2729) (by norm_num)
theorem B695141 : Blo 135790 695141 := bbase (se 4 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 695141 = 130339) (by norm_num)
theorem B203693 : Blo 135790 203693 := bbase (se 3 (by rfl) ⟨38192, by rfl⟩ : syracuseStep 203693 = 76385) (by norm_num)
theorem B203717 : Blo 135790 203717 := bbase (se 4 (by rfl) ⟨19098, by rfl⟩ : syracuseStep 203717 = 38197) (by norm_num)
theorem B203741 : Blo 135790 203741 := bbase (se 3 (by rfl) ⟨38201, by rfl⟩ : syracuseStep 203741 = 76403) (by norm_num)
theorem B203765 : Blo 135790 203765 := bbase (se 5 (by rfl) ⟨9551, by rfl⟩ : syracuseStep 203765 = 19103) (by norm_num)
theorem B203789 : Blo 135790 203789 := bbase (se 3 (by rfl) ⟨38210, by rfl⟩ : syracuseStep 203789 = 76421) (by norm_num)
theorem B203813 : Blo 135790 203813 := bbase (se 4 (by rfl) ⟨19107, by rfl⟩ : syracuseStep 203813 = 38215) (by norm_num)
theorem B203837 : Blo 135790 203837 := bbase (se 3 (by rfl) ⟨38219, by rfl⟩ : syracuseStep 203837 = 76439) (by norm_num)
theorem B203861 : Blo 135790 203861 := bbase (se 8 (by rfl) ⟨1194, by rfl⟩ : syracuseStep 203861 = 2389) (by norm_num)
theorem B203885 : Blo 135790 203885 := bbase (se 3 (by rfl) ⟨38228, by rfl⟩ : syracuseStep 203885 = 76457) (by norm_num)
theorem B1055861 : Blo 135790 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B203909 : Blo 135790 203909 := bbase (se 4 (by rfl) ⟨19116, by rfl⟩ : syracuseStep 203909 = 38233) (by norm_num)
theorem B203933 : Blo 135790 203933 := bbase (se 3 (by rfl) ⟨38237, by rfl⟩ : syracuseStep 203933 = 76475) (by norm_num)
theorem B203957 : Blo 135790 203957 := bbase (se 5 (by rfl) ⟨9560, by rfl⟩ : syracuseStep 203957 = 19121) (by norm_num)
theorem B203981 : Blo 135790 203981 := bbase (se 3 (by rfl) ⟨38246, by rfl⟩ : syracuseStep 203981 = 76493) (by norm_num)
theorem B204005 : Blo 135790 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B204029 : Blo 135790 204029 := bbase (se 3 (by rfl) ⟨38255, by rfl⟩ : syracuseStep 204029 = 76511) (by norm_num)
theorem B466181 : Blo 135790 466181 := bbase (se 4 (by rfl) ⟨43704, by rfl⟩ : syracuseStep 466181 = 87409) (by norm_num)
theorem B204053 : Blo 135790 204053 := bbase (se 6 (by rfl) ⟨4782, by rfl⟩ : syracuseStep 204053 = 9565) (by norm_num)
theorem B204077 : Blo 135790 204077 := bbase (se 3 (by rfl) ⟨38264, by rfl⟩ : syracuseStep 204077 = 76529) (by norm_num)
theorem B204101 : Blo 135790 204101 := bbase (se 4 (by rfl) ⟨19134, by rfl⟩ : syracuseStep 204101 = 38269) (by norm_num)
theorem B204125 : Blo 135790 204125 := bbase (se 3 (by rfl) ⟨38273, by rfl⟩ : syracuseStep 204125 = 76547) (by norm_num)
theorem B204149 : Blo 135790 204149 := bbase (se 5 (by rfl) ⟨9569, by rfl⟩ : syracuseStep 204149 = 19139) (by norm_num)
theorem B204173 : Blo 135790 204173 := bbase (se 3 (by rfl) ⟨38282, by rfl⟩ : syracuseStep 204173 = 76565) (by norm_num)
theorem B204197 : Blo 135790 204197 := bbase (se 4 (by rfl) ⟨19143, by rfl⟩ : syracuseStep 204197 = 38287) (by norm_num)
theorem B204221 : Blo 135790 204221 := bbase (se 3 (by rfl) ⟨38291, by rfl⟩ : syracuseStep 204221 = 76583) (by norm_num)
theorem B204245 : Blo 135790 204245 := bbase (se 7 (by rfl) ⟨2393, by rfl⟩ : syracuseStep 204245 = 4787) (by norm_num)
theorem B204269 : Blo 135790 204269 := bbase (se 3 (by rfl) ⟨38300, by rfl⟩ : syracuseStep 204269 = 76601) (by norm_num)
theorem B204293 : Blo 135790 204293 := bbase (se 4 (by rfl) ⟨19152, by rfl⟩ : syracuseStep 204293 = 38305) (by norm_num)
theorem B204317 : Blo 135790 204317 := bbase (se 3 (by rfl) ⟨38309, by rfl⟩ : syracuseStep 204317 = 76619) (by norm_num)
theorem B138781 : Blo 135790 138781 := bbase (se 3 (by rfl) ⟨26021, by rfl⟩ : syracuseStep 138781 = 52043) (by norm_num)
theorem B466469 : Blo 135790 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B204341 : Blo 135790 204341 := bbase (se 5 (by rfl) ⟨9578, by rfl⟩ : syracuseStep 204341 = 19157) (by norm_num)
theorem B204365 : Blo 135790 204365 := bbase (se 3 (by rfl) ⟨38318, by rfl⟩ : syracuseStep 204365 = 76637) (by norm_num)
theorem B204389 : Blo 135790 204389 := bbase (se 4 (by rfl) ⟨19161, by rfl⟩ : syracuseStep 204389 = 38323) (by norm_num)
theorem B335477 : Blo 135790 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B204413 : Blo 135790 204413 := bbase (se 3 (by rfl) ⟨38327, by rfl⟩ : syracuseStep 204413 = 76655) (by norm_num)
theorem B204437 : Blo 135790 204437 := bbase (se 6 (by rfl) ⟨4791, by rfl⟩ : syracuseStep 204437 = 9583) (by norm_num)
theorem B204461 : Blo 135790 204461 := bbase (se 3 (by rfl) ⟨38336, by rfl⟩ : syracuseStep 204461 = 76673) (by norm_num)
theorem B466613 : Blo 135790 466613 := bbase (se 5 (by rfl) ⟨21872, by rfl⟩ : syracuseStep 466613 = 43745) (by norm_num)
theorem B204485 : Blo 135790 204485 := bbase (se 4 (by rfl) ⟨19170, by rfl⟩ : syracuseStep 204485 = 38341) (by norm_num)
theorem B204509 : Blo 135790 204509 := bbase (se 3 (by rfl) ⟨38345, by rfl⟩ : syracuseStep 204509 = 76691) (by norm_num)
theorem B204533 : Blo 135790 204533 := bbase (se 5 (by rfl) ⟨9587, by rfl⟩ : syracuseStep 204533 = 19175) (by norm_num)
theorem B204557 : Blo 135790 204557 := bbase (se 3 (by rfl) ⟨38354, by rfl⟩ : syracuseStep 204557 = 76709) (by norm_num)
theorem B204581 : Blo 135790 204581 := bbase (se 4 (by rfl) ⟨19179, by rfl⟩ : syracuseStep 204581 = 38359) (by norm_num)
theorem B466741 : Blo 135790 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B204605 : Blo 135790 204605 := bbase (se 3 (by rfl) ⟨38363, by rfl⟩ : syracuseStep 204605 = 76727) (by norm_num)
theorem B204629 : Blo 135790 204629 := bbase (se 9 (by rfl) ⟨599, by rfl⟩ : syracuseStep 204629 = 1199) (by norm_num)
theorem B171877 : Blo 135790 171877 := bbase (se 4 (by rfl) ⟨16113, by rfl⟩ : syracuseStep 171877 = 32227) (by norm_num)
theorem B204653 : Blo 135790 204653 := bbase (se 3 (by rfl) ⟨38372, by rfl⟩ : syracuseStep 204653 = 76745) (by norm_num)
theorem B204677 : Blo 135790 204677 := bbase (se 4 (by rfl) ⟨19188, by rfl⟩ : syracuseStep 204677 = 38377) (by norm_num)
theorem B335765 : Blo 135790 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B204701 : Blo 135790 204701 := bbase (se 3 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 204701 = 76763) (by norm_num)
theorem B204725 : Blo 135790 204725 := bbase (se 5 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 204725 = 19193) (by norm_num)
theorem B171973 : Blo 135790 171973 := bbase (se 4 (by rfl) ⟨16122, by rfl⟩ : syracuseStep 171973 = 32245) (by norm_num)
theorem B204749 : Blo 135790 204749 := bbase (se 3 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 204749 = 76781) (by norm_num)
theorem B1253333 : Blo 135790 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B204773 : Blo 135790 204773 := bbase (se 4 (by rfl) ⟨19197, by rfl⟩ : syracuseStep 204773 = 38395) (by norm_num)
theorem B204797 : Blo 135790 204797 := bbase (se 3 (by rfl) ⟨38399, by rfl⟩ : syracuseStep 204797 = 76799) (by norm_num)
theorem B204821 : Blo 135790 204821 := bbase (se 6 (by rfl) ⟨4800, by rfl⟩ : syracuseStep 204821 = 9601) (by norm_num)
theorem B204845 : Blo 135790 204845 := bbase (se 3 (by rfl) ⟨38408, by rfl⟩ : syracuseStep 204845 = 76817) (by norm_num)
theorem B204869 : Blo 135790 204869 := bbase (se 4 (by rfl) ⟨19206, by rfl⟩ : syracuseStep 204869 = 38413) (by norm_num)
theorem B204893 : Blo 135790 204893 := bbase (se 3 (by rfl) ⟨38417, by rfl⟩ : syracuseStep 204893 = 76835) (by norm_num)
theorem B467045 : Blo 135790 467045 := bbase (se 4 (by rfl) ⟨43785, by rfl⟩ : syracuseStep 467045 = 87571) (by norm_num)
theorem B172145 : Blo 135790 172145 := bbase (se 2 (by rfl) ⟨64554, by rfl⟩ : syracuseStep 172145 = 129109) (by norm_num)
theorem B204917 : Blo 135790 204917 := bbase (se 5 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 204917 = 19211) (by norm_num)
theorem B696437 : Blo 135790 696437 := bbase (se 5 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 696437 = 65291) (by norm_num)
theorem B204941 : Blo 135790 204941 := bbase (se 3 (by rfl) ⟨38426, by rfl⟩ : syracuseStep 204941 = 76853) (by norm_num)
theorem B204965 : Blo 135790 204965 := bbase (se 4 (by rfl) ⟨19215, by rfl⟩ : syracuseStep 204965 = 38431) (by norm_num)
theorem B172201 : Blo 135790 172201 := bbase (se 2 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 172201 = 129151) (by norm_num)
theorem B204989 : Blo 135790 204989 := bbase (se 3 (by rfl) ⟨38435, by rfl⟩ : syracuseStep 204989 = 76871) (by norm_num)
theorem B205013 : Blo 135790 205013 := bbase (se 7 (by rfl) ⟨2402, by rfl⟩ : syracuseStep 205013 = 4805) (by norm_num)
theorem B205037 : Blo 135790 205037 := bbase (se 3 (by rfl) ⟨38444, by rfl⟩ : syracuseStep 205037 = 76889) (by norm_num)
theorem B205061 : Blo 135790 205061 := bbase (se 4 (by rfl) ⟨19224, by rfl⟩ : syracuseStep 205061 = 38449) (by norm_num)
theorem B172297 : Blo 135790 172297 := bbase (se 2 (by rfl) ⟨64611, by rfl⟩ : syracuseStep 172297 = 129223) (by norm_num)
theorem B205085 : Blo 135790 205085 := bbase (se 3 (by rfl) ⟨38453, by rfl⟩ : syracuseStep 205085 = 76907) (by norm_num)
theorem B205109 : Blo 135790 205109 := bbase (se 5 (by rfl) ⟨9614, by rfl⟩ : syracuseStep 205109 = 19229) (by norm_num)
theorem B205133 : Blo 135790 205133 := bbase (se 3 (by rfl) ⟨38462, by rfl⟩ : syracuseStep 205133 = 76925) (by norm_num)
theorem B237917 : Blo 135790 237917 := bbase (se 3 (by rfl) ⟨44609, by rfl⟩ : syracuseStep 237917 = 89219) (by norm_num)
theorem B205157 : Blo 135790 205157 := bbase (se 4 (by rfl) ⟨19233, by rfl⟩ : syracuseStep 205157 = 38467) (by norm_num)
theorem B205181 : Blo 135790 205181 := bbase (se 3 (by rfl) ⟨38471, by rfl⟩ : syracuseStep 205181 = 76943) (by norm_num)
theorem B205205 : Blo 135790 205205 := bbase (se 6 (by rfl) ⟨4809, by rfl⟩ : syracuseStep 205205 = 9619) (by norm_num)
theorem B205229 : Blo 135790 205229 := bbase (se 3 (by rfl) ⟨38480, by rfl⟩ : syracuseStep 205229 = 76961) (by norm_num)
theorem B172469 : Blo 135790 172469 := bbase (se 5 (by rfl) ⟨8084, by rfl⟩ : syracuseStep 172469 = 16169) (by norm_num)
theorem B205253 : Blo 135790 205253 := bbase (se 4 (by rfl) ⟨19242, by rfl⟩ : syracuseStep 205253 = 38485) (by norm_num)
theorem B205277 : Blo 135790 205277 := bbase (se 3 (by rfl) ⟨38489, by rfl⟩ : syracuseStep 205277 = 76979) (by norm_num)
theorem B172525 : Blo 135790 172525 := bbase (se 3 (by rfl) ⟨32348, by rfl⟩ : syracuseStep 172525 = 64697) (by norm_num)
theorem B205301 : Blo 135790 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B205325 : Blo 135790 205325 := bbase (se 3 (by rfl) ⟨38498, by rfl⟩ : syracuseStep 205325 = 76997) (by norm_num)
theorem B369173 : Blo 135790 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B467477 : Blo 135790 467477 := bbase (se 6 (by rfl) ⟨10956, by rfl⟩ : syracuseStep 467477 = 21913) (by norm_num)
theorem B205349 : Blo 135790 205349 := bbase (se 4 (by rfl) ⟨19251, by rfl⟩ : syracuseStep 205349 = 38503) (by norm_num)
theorem B205373 : Blo 135790 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B172621 : Blo 135790 172621 := bbase (se 3 (by rfl) ⟨32366, by rfl⟩ : syracuseStep 172621 = 64733) (by norm_num)
theorem B205397 : Blo 135790 205397 := bbase (se 8 (by rfl) ⟨1203, by rfl⟩ : syracuseStep 205397 = 2407) (by norm_num)
theorem B205421 : Blo 135790 205421 := bbase (se 3 (by rfl) ⟨38516, by rfl⟩ : syracuseStep 205421 = 77033) (by norm_num)
theorem B205445 : Blo 135790 205445 := bbase (se 4 (by rfl) ⟨19260, by rfl⟩ : syracuseStep 205445 = 38521) (by norm_num)
theorem B205469 : Blo 135790 205469 := bbase (se 3 (by rfl) ⟨38525, by rfl⟩ : syracuseStep 205469 = 77051) (by norm_num)
theorem B205493 : Blo 135790 205493 := bbase (se 5 (by rfl) ⟨9632, by rfl⟩ : syracuseStep 205493 = 19265) (by norm_num)
theorem B205517 : Blo 135790 205517 := bbase (se 3 (by rfl) ⟨38534, by rfl⟩ : syracuseStep 205517 = 77069) (by norm_num)
theorem B205541 : Blo 135790 205541 := bbase (se 4 (by rfl) ⟨19269, by rfl⟩ : syracuseStep 205541 = 38539) (by norm_num)
theorem B172793 : Blo 135790 172793 := bbase (se 2 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 172793 = 129595) (by norm_num)
theorem B205565 : Blo 135790 205565 := bbase (se 3 (by rfl) ⟨38543, by rfl⟩ : syracuseStep 205565 = 77087) (by norm_num)
theorem B205589 : Blo 135790 205589 := bbase (se 6 (by rfl) ⟨4818, by rfl⟩ : syracuseStep 205589 = 9637) (by norm_num)
theorem B205613 : Blo 135790 205613 := bbase (se 3 (by rfl) ⟨38552, by rfl⟩ : syracuseStep 205613 = 77105) (by norm_num)
theorem B172849 : Blo 135790 172849 := bbase (se 2 (by rfl) ⟨64818, by rfl⟩ : syracuseStep 172849 = 129637) (by norm_num)
theorem B205637 : Blo 135790 205637 := bbase (se 4 (by rfl) ⟨19278, by rfl⟩ : syracuseStep 205637 = 38557) (by norm_num)
theorem B205661 : Blo 135790 205661 := bbase (se 3 (by rfl) ⟨38561, by rfl⟩ : syracuseStep 205661 = 77123) (by norm_num)
theorem B205685 : Blo 135790 205685 := bbase (se 5 (by rfl) ⟨9641, by rfl⟩ : syracuseStep 205685 = 19283) (by norm_num)
theorem B205709 : Blo 135790 205709 := bbase (se 3 (by rfl) ⟨38570, by rfl⟩ : syracuseStep 205709 = 77141) (by norm_num)
theorem B172945 : Blo 135790 172945 := bbase (se 2 (by rfl) ⟨64854, by rfl⟩ : syracuseStep 172945 = 129709) (by norm_num)
theorem B205733 : Blo 135790 205733 := bbase (se 4 (by rfl) ⟨19287, by rfl⟩ : syracuseStep 205733 = 38575) (by norm_num)
theorem B205757 : Blo 135790 205757 := bbase (se 3 (by rfl) ⟨38579, by rfl⟩ : syracuseStep 205757 = 77159) (by norm_num)
theorem B467909 : Blo 135790 467909 := bbase (se 4 (by rfl) ⟨43866, by rfl⟩ : syracuseStep 467909 = 87733) (by norm_num)
theorem B205781 : Blo 135790 205781 := bbase (se 7 (by rfl) ⟨2411, by rfl⟩ : syracuseStep 205781 = 4823) (by norm_num)
theorem B205805 : Blo 135790 205805 := bbase (se 3 (by rfl) ⟨38588, by rfl⟩ : syracuseStep 205805 = 77177) (by norm_num)
theorem B205829 : Blo 135790 205829 := bbase (se 4 (by rfl) ⟨19296, by rfl⟩ : syracuseStep 205829 = 38593) (by norm_num)
theorem B140297 : Blo 135790 140297 := bbase (se 2 (by rfl) ⟨52611, by rfl⟩ : syracuseStep 140297 = 105223) (by norm_num)
theorem B205853 : Blo 135790 205853 := bbase (se 3 (by rfl) ⟨38597, by rfl⟩ : syracuseStep 205853 = 77195) (by norm_num)
theorem B205877 : Blo 135790 205877 := bbase (se 5 (by rfl) ⟨9650, by rfl⟩ : syracuseStep 205877 = 19301) (by norm_num)
theorem B173117 : Blo 135790 173117 := bbase (se 3 (by rfl) ⟨32459, by rfl⟩ : syracuseStep 173117 = 64919) (by norm_num)
theorem B205901 : Blo 135790 205901 := bbase (se 3 (by rfl) ⟨38606, by rfl⟩ : syracuseStep 205901 = 77213) (by norm_num)
theorem B205925 : Blo 135790 205925 := bbase (se 4 (by rfl) ⟨19305, by rfl⟩ : syracuseStep 205925 = 38611) (by norm_num)
theorem B173173 : Blo 135790 173173 := bbase (se 5 (by rfl) ⟨8117, by rfl⟩ : syracuseStep 173173 = 16235) (by norm_num)
theorem B205949 : Blo 135790 205949 := bbase (se 3 (by rfl) ⟨38615, by rfl⟩ : syracuseStep 205949 = 77231) (by norm_num)
theorem B205973 : Blo 135790 205973 := bbase (se 6 (by rfl) ⟨4827, by rfl⟩ : syracuseStep 205973 = 9655) (by norm_num)
theorem B205997 : Blo 135790 205997 := bbase (se 3 (by rfl) ⟨38624, by rfl⟩ : syracuseStep 205997 = 77249) (by norm_num)
theorem B206021 : Blo 135790 206021 := bbase (se 4 (by rfl) ⟨19314, by rfl⟩ : syracuseStep 206021 = 38629) (by norm_num)
theorem B173269 : Blo 135790 173269 := bbase (se 7 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 173269 = 4061) (by norm_num)
theorem B206045 : Blo 135790 206045 := bbase (se 3 (by rfl) ⟨38633, by rfl⟩ : syracuseStep 206045 = 77267) (by norm_num)
theorem B206069 : Blo 135790 206069 := bbase (se 5 (by rfl) ⟨9659, by rfl⟩ : syracuseStep 206069 = 19319) (by norm_num)
theorem B140545 : Blo 135790 140545 := bbase (se 2 (by rfl) ⟨52704, by rfl⟩ : syracuseStep 140545 = 105409) (by norm_num)
theorem B206093 : Blo 135790 206093 := bbase (se 3 (by rfl) ⟨38642, by rfl⟩ : syracuseStep 206093 = 77285) (by norm_num)
theorem B992533 : Blo 135790 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B206117 : Blo 135790 206117 := bbase (se 4 (by rfl) ⟨19323, by rfl⟩ : syracuseStep 206117 = 38647) (by norm_num)
theorem B206141 : Blo 135790 206141 := bbase (se 3 (by rfl) ⟨38651, by rfl⟩ : syracuseStep 206141 = 77303) (by norm_num)
theorem B206165 : Blo 135790 206165 := bbase (se 12 (by rfl) ⟨75, by rfl⟩ : syracuseStep 206165 = 151) (by norm_num)
theorem B599381 : Blo 135790 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B206189 : Blo 135790 206189 := bbase (se 3 (by rfl) ⟨38660, by rfl⟩ : syracuseStep 206189 = 77321) (by norm_num)
theorem B468341 : Blo 135790 468341 := bbase (se 5 (by rfl) ⟨21953, by rfl⟩ : syracuseStep 468341 = 43907) (by norm_num)
theorem B173441 : Blo 135790 173441 := bbase (se 2 (by rfl) ⟨65040, by rfl⟩ : syracuseStep 173441 = 130081) (by norm_num)
theorem B206213 : Blo 135790 206213 := bbase (se 4 (by rfl) ⟨19332, by rfl⟩ : syracuseStep 206213 = 38665) (by norm_num)
theorem B697733 : Blo 135790 697733 := bbase (se 4 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 697733 = 130825) (by norm_num)
theorem B206237 : Blo 135790 206237 := bbase (se 3 (by rfl) ⟨38669, by rfl⟩ : syracuseStep 206237 = 77339) (by norm_num)
theorem B206261 : Blo 135790 206261 := bbase (se 5 (by rfl) ⟨9668, by rfl⟩ : syracuseStep 206261 = 19337) (by norm_num)
theorem B173497 : Blo 135790 173497 := bbase (se 2 (by rfl) ⟨65061, by rfl⟩ : syracuseStep 173497 = 130123) (by norm_num)
theorem B206285 : Blo 135790 206285 := bbase (se 3 (by rfl) ⟨38678, by rfl⟩ : syracuseStep 206285 = 77357) (by norm_num)
theorem B4793813 : Blo 135790 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B206309 : Blo 135790 206309 := bbase (se 4 (by rfl) ⟨19341, by rfl⟩ : syracuseStep 206309 = 38683) (by norm_num)
theorem B206333 : Blo 135790 206333 := bbase (se 3 (by rfl) ⟨38687, by rfl⟩ : syracuseStep 206333 = 77375) (by norm_num)
theorem B206357 : Blo 135790 206357 := bbase (se 6 (by rfl) ⟨4836, by rfl⟩ : syracuseStep 206357 = 9673) (by norm_num)
theorem B173593 : Blo 135790 173593 := bbase (se 2 (by rfl) ⟨65097, by rfl⟩ : syracuseStep 173593 = 130195) (by norm_num)
theorem B206381 : Blo 135790 206381 := bbase (se 3 (by rfl) ⟨38696, by rfl⟩ : syracuseStep 206381 = 77393) (by norm_num)
theorem B206405 : Blo 135790 206405 := bbase (se 4 (by rfl) ⟨19350, by rfl⟩ : syracuseStep 206405 = 38701) (by norm_num)
theorem B206429 : Blo 135790 206429 := bbase (se 3 (by rfl) ⟨38705, by rfl⟩ : syracuseStep 206429 = 77411) (by norm_num)
theorem B206453 : Blo 135790 206453 := bbase (se 5 (by rfl) ⟨9677, by rfl⟩ : syracuseStep 206453 = 19355) (by norm_num)
theorem B206477 : Blo 135790 206477 := bbase (se 3 (by rfl) ⟨38714, by rfl⟩ : syracuseStep 206477 = 77429) (by norm_num)
theorem B206501 : Blo 135790 206501 := bbase (se 4 (by rfl) ⟨19359, by rfl⟩ : syracuseStep 206501 = 38719) (by norm_num)
theorem B206525 : Blo 135790 206525 := bbase (se 3 (by rfl) ⟨38723, by rfl⟩ : syracuseStep 206525 = 77447) (by norm_num)
theorem B173765 : Blo 135790 173765 := bbase (se 4 (by rfl) ⟨16290, by rfl⟩ : syracuseStep 173765 = 32581) (by norm_num)
theorem B206549 : Blo 135790 206549 := bbase (se 7 (by rfl) ⟨2420, by rfl⟩ : syracuseStep 206549 = 4841) (by norm_num)
theorem B206573 : Blo 135790 206573 := bbase (se 3 (by rfl) ⟨38732, by rfl⟩ : syracuseStep 206573 = 77465) (by norm_num)
theorem B173821 : Blo 135790 173821 := bbase (se 3 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 173821 = 65183) (by norm_num)
theorem B206597 : Blo 135790 206597 := bbase (se 4 (by rfl) ⟨19368, by rfl⟩ : syracuseStep 206597 = 38737) (by norm_num)
theorem B206621 : Blo 135790 206621 := bbase (se 3 (by rfl) ⟨38741, by rfl⟩ : syracuseStep 206621 = 77483) (by norm_num)
theorem B468773 : Blo 135790 468773 := bbase (se 4 (by rfl) ⟨43947, by rfl⟩ : syracuseStep 468773 = 87895) (by norm_num)
theorem B206645 : Blo 135790 206645 := bbase (se 5 (by rfl) ⟨9686, by rfl⟩ : syracuseStep 206645 = 19373) (by norm_num)
theorem B206669 : Blo 135790 206669 := bbase (se 3 (by rfl) ⟨38750, by rfl⟩ : syracuseStep 206669 = 77501) (by norm_num)
theorem B173917 : Blo 135790 173917 := bbase (se 3 (by rfl) ⟨32609, by rfl⟩ : syracuseStep 173917 = 65219) (by norm_num)
theorem B141149 : Blo 135790 141149 := bbase (se 3 (by rfl) ⟨26465, by rfl⟩ : syracuseStep 141149 = 52931) (by norm_num)
theorem B206693 : Blo 135790 206693 := bbase (se 4 (by rfl) ⟨19377, by rfl⟩ : syracuseStep 206693 = 38755) (by norm_num)
theorem B206717 : Blo 135790 206717 := bbase (se 3 (by rfl) ⟨38759, by rfl⟩ : syracuseStep 206717 = 77519) (by norm_num)
theorem B141197 : Blo 135790 141197 := bbase (se 3 (by rfl) ⟨26474, by rfl⟩ : syracuseStep 141197 = 52949) (by norm_num)
theorem B206741 : Blo 135790 206741 := bbase (se 6 (by rfl) ⟨4845, by rfl⟩ : syracuseStep 206741 = 9691) (by norm_num)
theorem B206765 : Blo 135790 206765 := bbase (se 3 (by rfl) ⟨38768, by rfl⟩ : syracuseStep 206765 = 77537) (by norm_num)
theorem B206789 : Blo 135790 206789 := bbase (se 4 (by rfl) ⟨19386, by rfl⟩ : syracuseStep 206789 = 38773) (by norm_num)
theorem B206797 : Blo 135790 206797 := bbase (se 3 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 206797 = 77549) (by norm_num)
theorem B206813 : Blo 135790 206813 := bbase (se 3 (by rfl) ⟨38777, by rfl⟩ : syracuseStep 206813 = 77555) (by norm_num)
theorem B206837 : Blo 135790 206837 := bbase (se 5 (by rfl) ⟨9695, by rfl⟩ : syracuseStep 206837 = 19391) (by norm_num)
theorem B174089 : Blo 135790 174089 := bbase (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) (by norm_num)
theorem B206861 : Blo 135790 206861 := bbase (se 3 (by rfl) ⟨38786, by rfl⟩ : syracuseStep 206861 = 77573) (by norm_num)
theorem B206885 : Blo 135790 206885 := bbase (se 4 (by rfl) ⟨19395, by rfl⟩ : syracuseStep 206885 = 38791) (by norm_num)
theorem B206909 : Blo 135790 206909 := bbase (se 3 (by rfl) ⟨38795, by rfl⟩ : syracuseStep 206909 = 77591) (by norm_num)
theorem B174145 : Blo 135790 174145 := bbase (se 2 (by rfl) ⟨65304, by rfl⟩ : syracuseStep 174145 = 130609) (by norm_num)
theorem B206933 : Blo 135790 206933 := bbase (se 8 (by rfl) ⟨1212, by rfl⟩ : syracuseStep 206933 = 2425) (by norm_num)
theorem B206957 : Blo 135790 206957 := bbase (se 3 (by rfl) ⟨38804, by rfl⟩ : syracuseStep 206957 = 77609) (by norm_num)
theorem B206981 : Blo 135790 206981 := bbase (se 4 (by rfl) ⟨19404, by rfl⟩ : syracuseStep 206981 = 38809) (by norm_num)
theorem B207005 : Blo 135790 207005 := bbase (se 3 (by rfl) ⟨38813, by rfl⟩ : syracuseStep 207005 = 77627) (by norm_num)
theorem B174241 : Blo 135790 174241 := bbase (se 2 (by rfl) ⟨65340, by rfl⟩ : syracuseStep 174241 = 130681) (by norm_num)
theorem B665765 : Blo 135790 665765 := bbase (se 4 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 665765 = 124831) (by norm_num)
theorem B207029 : Blo 135790 207029 := bbase (se 5 (by rfl) ⟨9704, by rfl⟩ : syracuseStep 207029 = 19409) (by norm_num)
theorem B174269 : Blo 135790 174269 := bbase (se 3 (by rfl) ⟨32675, by rfl⟩ : syracuseStep 174269 = 65351) (by norm_num)
theorem B207053 : Blo 135790 207053 := bbase (se 3 (by rfl) ⟨38822, by rfl⟩ : syracuseStep 207053 = 77645) (by norm_num)
theorem B469205 : Blo 135790 469205 := bbase (se 7 (by rfl) ⟨5498, by rfl⟩ : syracuseStep 469205 = 10997) (by norm_num)
theorem B403685 : Blo 135790 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B207077 : Blo 135790 207077 := bbase (se 4 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 207077 = 38827) (by norm_num)
theorem B207101 : Blo 135790 207101 := bbase (se 3 (by rfl) ⟨38831, by rfl⟩ : syracuseStep 207101 = 77663) (by norm_num)
theorem B141577 : Blo 135790 141577 := bbase (se 2 (by rfl) ⟨53091, by rfl⟩ : syracuseStep 141577 = 106183) (by norm_num)
theorem B207125 : Blo 135790 207125 := bbase (se 6 (by rfl) ⟨4854, by rfl⟩ : syracuseStep 207125 = 9709) (by norm_num)
theorem B207149 : Blo 135790 207149 := bbase (se 3 (by rfl) ⟨38840, by rfl⟩ : syracuseStep 207149 = 77681) (by norm_num)
theorem B207173 : Blo 135790 207173 := bbase (se 4 (by rfl) ⟨19422, by rfl⟩ : syracuseStep 207173 = 38845) (by norm_num)
theorem B174413 : Blo 135790 174413 := bbase (se 3 (by rfl) ⟨32702, by rfl⟩ : syracuseStep 174413 = 65405) (by norm_num)
theorem B207197 : Blo 135790 207197 := bbase (se 3 (by rfl) ⟨38849, by rfl⟩ : syracuseStep 207197 = 77699) (by norm_num)
theorem B207221 : Blo 135790 207221 := bbase (se 5 (by rfl) ⟨9713, by rfl⟩ : syracuseStep 207221 = 19427) (by norm_num)
theorem B174469 : Blo 135790 174469 := bbase (se 4 (by rfl) ⟨16356, by rfl⟩ : syracuseStep 174469 = 32713) (by norm_num)
theorem B305549 : Blo 135790 305549 := bbase (se 3 (by rfl) ⟨57290, by rfl⟩ : syracuseStep 305549 = 114581) (by norm_num)
theorem B207245 : Blo 135790 207245 := bbase (se 3 (by rfl) ⟨38858, by rfl⟩ : syracuseStep 207245 = 77717) (by norm_num)
theorem B207269 : Blo 135790 207269 := bbase (se 4 (by rfl) ⟨19431, by rfl⟩ : syracuseStep 207269 = 38863) (by norm_num)
theorem B207293 : Blo 135790 207293 := bbase (se 3 (by rfl) ⟨38867, by rfl⟩ : syracuseStep 207293 = 77735) (by norm_num)
theorem B502213 : Blo 135790 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B305621 : Blo 135790 305621 := bbase (se 7 (by rfl) ⟨3581, by rfl⟩ : syracuseStep 305621 = 7163) (by norm_num)
theorem B207317 : Blo 135790 207317 := bbase (se 7 (by rfl) ⟨2429, by rfl⟩ : syracuseStep 207317 = 4859) (by norm_num)
theorem B174565 : Blo 135790 174565 := bbase (se 4 (by rfl) ⟨16365, by rfl⟩ : syracuseStep 174565 = 32731) (by norm_num)
theorem B141805 : Blo 135790 141805 := bbase (se 3 (by rfl) ⟨26588, by rfl⟩ : syracuseStep 141805 = 53177) (by norm_num)
theorem B207341 : Blo 135790 207341 := bbase (se 3 (by rfl) ⟨38876, by rfl⟩ : syracuseStep 207341 = 77753) (by norm_num)
theorem B207365 : Blo 135790 207365 := bbase (se 4 (by rfl) ⟨19440, by rfl⟩ : syracuseStep 207365 = 38881) (by norm_num)
theorem B305669 : Blo 135790 305669 := bbase (se 4 (by rfl) ⟨28656, by rfl⟩ : syracuseStep 305669 = 57313) (by norm_num)
theorem B305693 : Blo 135790 305693 := bbase (se 3 (by rfl) ⟨57317, by rfl⟩ : syracuseStep 305693 = 114635) (by norm_num)
theorem B207389 : Blo 135790 207389 := bbase (se 3 (by rfl) ⟨38885, by rfl⟩ : syracuseStep 207389 = 77771) (by norm_num)
theorem B207413 : Blo 135790 207413 := bbase (se 5 (by rfl) ⟨9722, by rfl⟩ : syracuseStep 207413 = 19445) (by norm_num)
theorem B207437 : Blo 135790 207437 := bbase (se 3 (by rfl) ⟨38894, by rfl⟩ : syracuseStep 207437 = 77789) (by norm_num)
theorem B305765 : Blo 135790 305765 := bbase (se 4 (by rfl) ⟨28665, by rfl⟩ : syracuseStep 305765 = 57331) (by norm_num)
theorem B207461 : Blo 135790 207461 := bbase (se 4 (by rfl) ⟨19449, by rfl⟩ : syracuseStep 207461 = 38899) (by norm_num)
theorem B207485 : Blo 135790 207485 := bbase (se 3 (by rfl) ⟨38903, by rfl⟩ : syracuseStep 207485 = 77807) (by norm_num)
theorem B469637 : Blo 135790 469637 := bbase (se 4 (by rfl) ⟨44028, by rfl⟩ : syracuseStep 469637 = 88057) (by norm_num)
theorem B174737 : Blo 135790 174737 := bbase (se 2 (by rfl) ⟨65526, by rfl⟩ : syracuseStep 174737 = 131053) (by norm_num)
theorem B699029 : Blo 135790 699029 := bbase (se 6 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 699029 = 32767) (by norm_num)
theorem B207509 : Blo 135790 207509 := bbase (se 6 (by rfl) ⟨4863, by rfl⟩ : syracuseStep 207509 = 9727) (by norm_num)
theorem B174757 : Blo 135790 174757 := bbase (se 4 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 174757 = 32767) (by norm_num)
theorem B305837 : Blo 135790 305837 := bbase (se 3 (by rfl) ⟨57344, by rfl⟩ : syracuseStep 305837 = 114689) (by norm_num)
theorem B207533 : Blo 135790 207533 := bbase (se 3 (by rfl) ⟨38912, by rfl⟩ : syracuseStep 207533 = 77825) (by norm_num)
theorem B207557 : Blo 135790 207557 := bbase (se 4 (by rfl) ⟨19458, by rfl⟩ : syracuseStep 207557 = 38917) (by norm_num)
theorem B174793 : Blo 135790 174793 := bbase (se 2 (by rfl) ⟨65547, by rfl⟩ : syracuseStep 174793 = 131095) (by norm_num)
theorem B207581 : Blo 135790 207581 := bbase (se 3 (by rfl) ⟨38921, by rfl⟩ : syracuseStep 207581 = 77843) (by norm_num)
theorem B305909 : Blo 135790 305909 := bbase (se 5 (by rfl) ⟨14339, by rfl⟩ : syracuseStep 305909 = 28679) (by norm_num)
theorem B207605 : Blo 135790 207605 := bbase (se 5 (by rfl) ⟨9731, by rfl⟩ : syracuseStep 207605 = 19463) (by norm_num)
theorem B207629 : Blo 135790 207629 := bbase (se 3 (by rfl) ⟨38930, by rfl⟩ : syracuseStep 207629 = 77861) (by norm_num)
theorem B207653 : Blo 135790 207653 := bbase (se 4 (by rfl) ⟨19467, by rfl⟩ : syracuseStep 207653 = 38935) (by norm_num)
theorem B174889 : Blo 135790 174889 := bbase (se 2 (by rfl) ⟨65583, by rfl⟩ : syracuseStep 174889 = 131167) (by norm_num)
theorem B305981 : Blo 135790 305981 := bbase (se 3 (by rfl) ⟨57371, by rfl⟩ : syracuseStep 305981 = 114743) (by norm_num)
theorem B207677 : Blo 135790 207677 := bbase (se 3 (by rfl) ⟨38939, by rfl⟩ : syracuseStep 207677 = 77879) (by norm_num)
theorem B207701 : Blo 135790 207701 := bbase (se 9 (by rfl) ⟨608, by rfl⟩ : syracuseStep 207701 = 1217) (by norm_num)
theorem B207725 : Blo 135790 207725 := bbase (se 3 (by rfl) ⟨38948, by rfl⟩ : syracuseStep 207725 = 77897) (by norm_num)
theorem B306053 : Blo 135790 306053 := bbase (se 4 (by rfl) ⟨28692, by rfl⟩ : syracuseStep 306053 = 57385) (by norm_num)
theorem B207749 : Blo 135790 207749 := bbase (se 4 (by rfl) ⟨19476, by rfl⟩ : syracuseStep 207749 = 38953) (by norm_num)
theorem B207773 : Blo 135790 207773 := bbase (se 3 (by rfl) ⟨38957, by rfl⟩ : syracuseStep 207773 = 77915) (by norm_num)
theorem B207797 : Blo 135790 207797 := bbase (se 5 (by rfl) ⟨9740, by rfl⟩ : syracuseStep 207797 = 19481) (by norm_num)
theorem B306125 : Blo 135790 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B207821 : Blo 135790 207821 := bbase (se 3 (by rfl) ⟨38966, by rfl⟩ : syracuseStep 207821 = 77933) (by norm_num)
theorem B175061 : Blo 135790 175061 := bbase (se 7 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 175061 = 4103) (by norm_num)
theorem B207845 : Blo 135790 207845 := bbase (se 4 (by rfl) ⟨19485, by rfl⟩ : syracuseStep 207845 = 38971) (by norm_num)
theorem B207869 : Blo 135790 207869 := bbase (se 3 (by rfl) ⟨38975, by rfl⟩ : syracuseStep 207869 = 77951) (by norm_num)
theorem B175117 : Blo 135790 175117 := bbase (se 3 (by rfl) ⟨32834, by rfl⟩ : syracuseStep 175117 = 65669) (by norm_num)
theorem B306197 : Blo 135790 306197 := bbase (se 6 (by rfl) ⟨7176, by rfl⟩ : syracuseStep 306197 = 14353) (by norm_num)
theorem B207893 : Blo 135790 207893 := bbase (se 6 (by rfl) ⟨4872, by rfl⟩ : syracuseStep 207893 = 9745) (by norm_num)
theorem B207917 : Blo 135790 207917 := bbase (se 3 (by rfl) ⟨38984, by rfl⟩ : syracuseStep 207917 = 77969) (by norm_num)
theorem B470069 : Blo 135790 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B207941 : Blo 135790 207941 := bbase (se 4 (by rfl) ⟨19494, by rfl⟩ : syracuseStep 207941 = 38989) (by norm_num)
theorem B306269 : Blo 135790 306269 := bbase (se 3 (by rfl) ⟨57425, by rfl⟩ : syracuseStep 306269 = 114851) (by norm_num)
theorem B207965 : Blo 135790 207965 := bbase (se 3 (by rfl) ⟨38993, by rfl⟩ : syracuseStep 207965 = 77987) (by norm_num)
theorem B175213 : Blo 135790 175213 := bbase (se 3 (by rfl) ⟨32852, by rfl⟩ : syracuseStep 175213 = 65705) (by norm_num)
theorem B207989 : Blo 135790 207989 := bbase (se 5 (by rfl) ⟨9749, by rfl⟩ : syracuseStep 207989 = 19499) (by norm_num)
theorem B208013 : Blo 135790 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B306341 : Blo 135790 306341 := bbase (se 4 (by rfl) ⟨28719, by rfl⟩ : syracuseStep 306341 = 57439) (by norm_num)
theorem B208037 : Blo 135790 208037 := bbase (se 4 (by rfl) ⟨19503, by rfl⟩ : syracuseStep 208037 = 39007) (by norm_num)
theorem B208061 : Blo 135790 208061 := bbase (se 3 (by rfl) ⟨39011, by rfl⟩ : syracuseStep 208061 = 78023) (by norm_num)
theorem B208085 : Blo 135790 208085 := bbase (se 7 (by rfl) ⟨2438, by rfl⟩ : syracuseStep 208085 = 4877) (by norm_num)
theorem B306413 : Blo 135790 306413 := bbase (se 3 (by rfl) ⟨57452, by rfl⟩ : syracuseStep 306413 = 114905) (by norm_num)
theorem B208109 : Blo 135790 208109 := bbase (se 3 (by rfl) ⟨39020, by rfl⟩ : syracuseStep 208109 = 78041) (by norm_num)
theorem B208133 : Blo 135790 208133 := bbase (se 4 (by rfl) ⟨19512, by rfl⟩ : syracuseStep 208133 = 39025) (by norm_num)
theorem B175385 : Blo 135790 175385 := bbase (se 2 (by rfl) ⟨65769, by rfl⟩ : syracuseStep 175385 = 131539) (by norm_num)
theorem B208157 : Blo 135790 208157 := bbase (se 3 (by rfl) ⟨39029, by rfl⟩ : syracuseStep 208157 = 78059) (by norm_num)
theorem B666917 : Blo 135790 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B306485 : Blo 135790 306485 := bbase (se 5 (by rfl) ⟨14366, by rfl⟩ : syracuseStep 306485 = 28733) (by norm_num)
theorem B208181 : Blo 135790 208181 := bbase (se 5 (by rfl) ⟨9758, by rfl⟩ : syracuseStep 208181 = 19517) (by norm_num)
theorem B208205 : Blo 135790 208205 := bbase (se 3 (by rfl) ⟨39038, by rfl⟩ : syracuseStep 208205 = 78077) (by norm_num)
theorem B175441 : Blo 135790 175441 := bbase (se 2 (by rfl) ⟨65790, by rfl⟩ : syracuseStep 175441 = 131581) (by norm_num)
theorem B699749 : Blo 135790 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B208229 : Blo 135790 208229 := bbase (se 4 (by rfl) ⟨19521, by rfl⟩ : syracuseStep 208229 = 39043) (by norm_num)
theorem B306557 : Blo 135790 306557 := bbase (se 3 (by rfl) ⟨57479, by rfl⟩ : syracuseStep 306557 = 114959) (by norm_num)
theorem B208253 : Blo 135790 208253 := bbase (se 3 (by rfl) ⟨39047, by rfl⟩ : syracuseStep 208253 = 78095) (by norm_num)
theorem B208277 : Blo 135790 208277 := bbase (se 6 (by rfl) ⟨4881, by rfl⟩ : syracuseStep 208277 = 9763) (by norm_num)
theorem B208301 : Blo 135790 208301 := bbase (se 3 (by rfl) ⟨39056, by rfl⟩ : syracuseStep 208301 = 78113) (by norm_num)
theorem B175537 : Blo 135790 175537 := bbase (se 2 (by rfl) ⟨65826, by rfl⟩ : syracuseStep 175537 = 131653) (by norm_num)
theorem B306629 : Blo 135790 306629 := bbase (se 4 (by rfl) ⟨28746, by rfl⟩ : syracuseStep 306629 = 57493) (by norm_num)
theorem B208325 : Blo 135790 208325 := bbase (se 4 (by rfl) ⟨19530, by rfl⟩ : syracuseStep 208325 = 39061) (by norm_num)
theorem B208349 : Blo 135790 208349 := bbase (se 3 (by rfl) ⟨39065, by rfl⟩ : syracuseStep 208349 = 78131) (by norm_num)
theorem B470501 : Blo 135790 470501 := bbase (se 4 (by rfl) ⟨44109, by rfl⟩ : syracuseStep 470501 = 88219) (by norm_num)
theorem B208373 : Blo 135790 208373 := bbase (se 5 (by rfl) ⟨9767, by rfl⟩ : syracuseStep 208373 = 19535) (by norm_num)
theorem B306701 : Blo 135790 306701 := bbase (se 3 (by rfl) ⟨57506, by rfl⟩ : syracuseStep 306701 = 115013) (by norm_num)
theorem B208397 : Blo 135790 208397 := bbase (se 3 (by rfl) ⟨39074, by rfl⟩ : syracuseStep 208397 = 78149) (by norm_num)
theorem B208421 : Blo 135790 208421 := bbase (se 4 (by rfl) ⟨19539, by rfl⟩ : syracuseStep 208421 = 39079) (by norm_num)
theorem B208445 : Blo 135790 208445 := bbase (se 3 (by rfl) ⟨39083, by rfl⟩ : syracuseStep 208445 = 78167) (by norm_num)
theorem B306773 : Blo 135790 306773 := bbase (se 8 (by rfl) ⟨1797, by rfl⟩ : syracuseStep 306773 = 3595) (by norm_num)
theorem B437845 : Blo 135790 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B208469 : Blo 135790 208469 := bbase (se 8 (by rfl) ⟨1221, by rfl⟩ : syracuseStep 208469 = 2443) (by norm_num)
theorem B175709 : Blo 135790 175709 := bbase (se 3 (by rfl) ⟨32945, by rfl⟩ : syracuseStep 175709 = 65891) (by norm_num)
theorem B208493 : Blo 135790 208493 := bbase (se 3 (by rfl) ⟨39092, by rfl⟩ : syracuseStep 208493 = 78185) (by norm_num)
theorem B208517 : Blo 135790 208517 := bbase (se 4 (by rfl) ⟨19548, by rfl⟩ : syracuseStep 208517 = 39097) (by norm_num)
theorem B175765 : Blo 135790 175765 := bbase (se 6 (by rfl) ⟨4119, by rfl⟩ : syracuseStep 175765 = 8239) (by norm_num)
theorem B306845 : Blo 135790 306845 := bbase (se 3 (by rfl) ⟨57533, by rfl⟩ : syracuseStep 306845 = 115067) (by norm_num)
theorem B208541 : Blo 135790 208541 := bbase (se 3 (by rfl) ⟨39101, by rfl⟩ : syracuseStep 208541 = 78203) (by norm_num)
theorem B208565 : Blo 135790 208565 := bbase (se 5 (by rfl) ⟨9776, by rfl⟩ : syracuseStep 208565 = 19553) (by norm_num)
theorem B208589 : Blo 135790 208589 := bbase (se 3 (by rfl) ⟨39110, by rfl⟩ : syracuseStep 208589 = 78221) (by norm_num)
theorem B306917 : Blo 135790 306917 := bbase (se 4 (by rfl) ⟨28773, by rfl⟩ : syracuseStep 306917 = 57547) (by norm_num)
theorem B208613 : Blo 135790 208613 := bbase (se 4 (by rfl) ⟨19557, by rfl⟩ : syracuseStep 208613 = 39115) (by norm_num)
theorem B175861 : Blo 135790 175861 := bbase (se 5 (by rfl) ⟨8243, by rfl⟩ : syracuseStep 175861 = 16487) (by norm_num)
theorem B208637 : Blo 135790 208637 := bbase (se 3 (by rfl) ⟨39119, by rfl⟩ : syracuseStep 208637 = 78239) (by norm_num)
theorem B208661 : Blo 135790 208661 := bbase (se 6 (by rfl) ⟨4890, by rfl⟩ : syracuseStep 208661 = 9781) (by norm_num)
theorem B306989 : Blo 135790 306989 := bbase (se 3 (by rfl) ⟨57560, by rfl⟩ : syracuseStep 306989 = 115121) (by norm_num)
theorem B208685 : Blo 135790 208685 := bbase (se 3 (by rfl) ⟨39128, by rfl⟩ : syracuseStep 208685 = 78257) (by norm_num)
theorem B208709 : Blo 135790 208709 := bbase (se 4 (by rfl) ⟨19566, by rfl⟩ : syracuseStep 208709 = 39133) (by norm_num)
theorem B208733 : Blo 135790 208733 := bbase (se 3 (by rfl) ⟨39137, by rfl⟩ : syracuseStep 208733 = 78275) (by norm_num)
theorem B307061 : Blo 135790 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B208757 : Blo 135790 208757 := bbase (se 5 (by rfl) ⟨9785, by rfl⟩ : syracuseStep 208757 = 19571) (by norm_num)
theorem B208781 : Blo 135790 208781 := bbase (se 3 (by rfl) ⟨39146, by rfl⟩ : syracuseStep 208781 = 78293) (by norm_num)
theorem B470933 : Blo 135790 470933 := bbase (se 6 (by rfl) ⟨11037, by rfl⟩ : syracuseStep 470933 = 22075) (by norm_num)
theorem B176033 : Blo 135790 176033 := bbase (se 2 (by rfl) ⟨66012, by rfl⟩ : syracuseStep 176033 = 132025) (by norm_num)
theorem B700325 : Blo 135790 700325 := bbase (se 4 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 700325 = 131311) (by norm_num)
theorem B208805 : Blo 135790 208805 := bbase (se 4 (by rfl) ⟨19575, by rfl⟩ : syracuseStep 208805 = 39151) (by norm_num)
theorem B307133 : Blo 135790 307133 := bbase (se 3 (by rfl) ⟨57587, by rfl⟩ : syracuseStep 307133 = 115175) (by norm_num)
theorem B208829 : Blo 135790 208829 := bbase (se 3 (by rfl) ⟨39155, by rfl⟩ : syracuseStep 208829 = 78311) (by norm_num)
theorem B208853 : Blo 135790 208853 := bbase (se 7 (by rfl) ⟨2447, by rfl⟩ : syracuseStep 208853 = 4895) (by norm_num)
theorem B176089 : Blo 135790 176089 := bbase (se 2 (by rfl) ⟨66033, by rfl⟩ : syracuseStep 176089 = 132067) (by norm_num)
theorem B372709 : Blo 135790 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B208877 : Blo 135790 208877 := bbase (se 3 (by rfl) ⟨39164, by rfl⟩ : syracuseStep 208877 = 78329) (by norm_num)
theorem B307205 : Blo 135790 307205 := bbase (se 4 (by rfl) ⟨28800, by rfl⟩ : syracuseStep 307205 = 57601) (by norm_num)
theorem B208901 : Blo 135790 208901 := bbase (se 4 (by rfl) ⟨19584, by rfl⟩ : syracuseStep 208901 = 39169) (by norm_num)
theorem B208925 : Blo 135790 208925 := bbase (se 3 (by rfl) ⟨39173, by rfl⟩ : syracuseStep 208925 = 78347) (by norm_num)
theorem B667685 : Blo 135790 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B208949 : Blo 135790 208949 := bbase (se 5 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 208949 = 19589) (by norm_num)
theorem B176185 : Blo 135790 176185 := bbase (se 2 (by rfl) ⟨66069, by rfl⟩ : syracuseStep 176185 = 132139) (by norm_num)
theorem B634949 : Blo 135790 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B307277 : Blo 135790 307277 := bbase (se 3 (by rfl) ⟨57614, by rfl⟩ : syracuseStep 307277 = 115229) (by norm_num)
theorem B208973 : Blo 135790 208973 := bbase (se 3 (by rfl) ⟨39182, by rfl⟩ : syracuseStep 208973 = 78365) (by norm_num)
theorem B208997 : Blo 135790 208997 := bbase (se 4 (by rfl) ⟨19593, by rfl⟩ : syracuseStep 208997 = 39187) (by norm_num)
theorem B209021 : Blo 135790 209021 := bbase (se 3 (by rfl) ⟨39191, by rfl⟩ : syracuseStep 209021 = 78383) (by norm_num)
theorem B307349 : Blo 135790 307349 := bbase (se 6 (by rfl) ⟨7203, by rfl⟩ : syracuseStep 307349 = 14407) (by norm_num)
theorem B209045 : Blo 135790 209045 := bbase (se 6 (by rfl) ⟨4899, by rfl⟩ : syracuseStep 209045 = 9799) (by norm_num)
theorem B209069 : Blo 135790 209069 := bbase (se 3 (by rfl) ⟨39200, by rfl⟩ : syracuseStep 209069 = 78401) (by norm_num)
theorem B209093 : Blo 135790 209093 := bbase (se 4 (by rfl) ⟨19602, by rfl⟩ : syracuseStep 209093 = 39205) (by norm_num)
theorem B307421 : Blo 135790 307421 := bbase (se 3 (by rfl) ⟨57641, by rfl⟩ : syracuseStep 307421 = 115283) (by norm_num)
theorem B209117 : Blo 135790 209117 := bbase (se 3 (by rfl) ⟨39209, by rfl⟩ : syracuseStep 209117 = 78419) (by norm_num)
theorem B176357 : Blo 135790 176357 := bbase (se 4 (by rfl) ⟨16533, by rfl⟩ : syracuseStep 176357 = 33067) (by norm_num)
theorem B209141 : Blo 135790 209141 := bbase (se 5 (by rfl) ⟨9803, by rfl⟩ : syracuseStep 209141 = 19607) (by norm_num)
theorem B143617 : Blo 135790 143617 := bbase (se 2 (by rfl) ⟨53856, by rfl⟩ : syracuseStep 143617 = 107713) (by norm_num)
theorem B209165 : Blo 135790 209165 := bbase (se 3 (by rfl) ⟨39218, by rfl⟩ : syracuseStep 209165 = 78437) (by norm_num)
theorem B176413 : Blo 135790 176413 := bbase (se 3 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 176413 = 66155) (by norm_num)
theorem B307493 : Blo 135790 307493 := bbase (se 4 (by rfl) ⟨28827, by rfl⟩ : syracuseStep 307493 = 57655) (by norm_num)
theorem B209189 : Blo 135790 209189 := bbase (se 4 (by rfl) ⟨19611, by rfl⟩ : syracuseStep 209189 = 39223) (by norm_num)
theorem B1323317 : Blo 135790 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B209213 : Blo 135790 209213 := bbase (se 3 (by rfl) ⟨39227, by rfl⟩ : syracuseStep 209213 = 78455) (by norm_num)
theorem B471365 : Blo 135790 471365 := bbase (se 4 (by rfl) ⟨44190, by rfl⟩ : syracuseStep 471365 = 88381) (by norm_num)
theorem B209237 : Blo 135790 209237 := bbase (se 10 (by rfl) ⟨306, by rfl⟩ : syracuseStep 209237 = 613) (by norm_num)
theorem B307565 : Blo 135790 307565 := bbase (se 3 (by rfl) ⟨57668, by rfl⟩ : syracuseStep 307565 = 115337) (by norm_num)
theorem B209261 : Blo 135790 209261 := bbase (se 3 (by rfl) ⟨39236, by rfl⟩ : syracuseStep 209261 = 78473) (by norm_num)
theorem B176509 : Blo 135790 176509 := bbase (se 3 (by rfl) ⟨33095, by rfl⟩ : syracuseStep 176509 = 66191) (by norm_num)
theorem B209285 : Blo 135790 209285 := bbase (se 4 (by rfl) ⟨19620, by rfl⟩ : syracuseStep 209285 = 39241) (by norm_num)
theorem B209309 : Blo 135790 209309 := bbase (se 3 (by rfl) ⟨39245, by rfl⟩ : syracuseStep 209309 = 78491) (by norm_num)
theorem B307637 : Blo 135790 307637 := bbase (se 5 (by rfl) ⟨14420, by rfl⟩ : syracuseStep 307637 = 28841) (by norm_num)
theorem B209333 : Blo 135790 209333 := bbase (se 5 (by rfl) ⟨9812, by rfl⟩ : syracuseStep 209333 = 19625) (by norm_num)
theorem B209357 : Blo 135790 209357 := bbase (se 3 (by rfl) ⟨39254, by rfl⟩ : syracuseStep 209357 = 78509) (by norm_num)
theorem B209381 : Blo 135790 209381 := bbase (se 4 (by rfl) ⟨19629, by rfl⟩ : syracuseStep 209381 = 39259) (by norm_num)
theorem B307709 : Blo 135790 307709 := bbase (se 3 (by rfl) ⟨57695, by rfl⟩ : syracuseStep 307709 = 115391) (by norm_num)
theorem B209405 : Blo 135790 209405 := bbase (se 3 (by rfl) ⟨39263, by rfl⟩ : syracuseStep 209405 = 78527) (by norm_num)
theorem B209429 : Blo 135790 209429 := bbase (se 6 (by rfl) ⟨4908, by rfl⟩ : syracuseStep 209429 = 9817) (by norm_num)
theorem B176681 : Blo 135790 176681 := bbase (se 2 (by rfl) ⟨66255, by rfl⟩ : syracuseStep 176681 = 132511) (by norm_num)
theorem B209453 : Blo 135790 209453 := bbase (se 3 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 209453 = 78545) (by norm_num)
theorem B307781 : Blo 135790 307781 := bbase (se 4 (by rfl) ⟨28854, by rfl⟩ : syracuseStep 307781 = 57709) (by norm_num)
theorem B209477 : Blo 135790 209477 := bbase (se 4 (by rfl) ⟨19638, by rfl⟩ : syracuseStep 209477 = 39277) (by norm_num)
theorem B209501 : Blo 135790 209501 := bbase (se 3 (by rfl) ⟨39281, by rfl⟩ : syracuseStep 209501 = 78563) (by norm_num)
theorem B176737 : Blo 135790 176737 := bbase (se 2 (by rfl) ⟨66276, by rfl⟩ : syracuseStep 176737 = 132553) (by norm_num)
theorem B209525 : Blo 135790 209525 := bbase (se 5 (by rfl) ⟨9821, by rfl⟩ : syracuseStep 209525 = 19643) (by norm_num)
theorem B307853 : Blo 135790 307853 := bbase (se 3 (by rfl) ⟨57722, by rfl⟩ : syracuseStep 307853 = 115445) (by norm_num)
theorem B209549 : Blo 135790 209549 := bbase (se 3 (by rfl) ⟨39290, by rfl⟩ : syracuseStep 209549 = 78581) (by norm_num)
theorem B209573 : Blo 135790 209573 := bbase (se 4 (by rfl) ⟨19647, by rfl⟩ : syracuseStep 209573 = 39295) (by norm_num)
theorem B209597 : Blo 135790 209597 := bbase (se 3 (by rfl) ⟨39299, by rfl⟩ : syracuseStep 209597 = 78599) (by norm_num)
theorem B176833 : Blo 135790 176833 := bbase (se 2 (by rfl) ⟨66312, by rfl⟩ : syracuseStep 176833 = 132625) (by norm_num)
theorem B307925 : Blo 135790 307925 := bbase (se 7 (by rfl) ⟨3608, by rfl⟩ : syracuseStep 307925 = 7217) (by norm_num)
theorem B209621 : Blo 135790 209621 := bbase (se 7 (by rfl) ⟨2456, by rfl⟩ : syracuseStep 209621 = 4913) (by norm_num)
theorem B209645 : Blo 135790 209645 := bbase (se 3 (by rfl) ⟨39308, by rfl⟩ : syracuseStep 209645 = 78617) (by norm_num)
theorem B209669 : Blo 135790 209669 := bbase (se 4 (by rfl) ⟨19656, by rfl⟩ : syracuseStep 209669 = 39313) (by norm_num)
theorem B307997 : Blo 135790 307997 := bbase (se 3 (by rfl) ⟨57749, by rfl⟩ : syracuseStep 307997 = 115499) (by norm_num)
theorem B308069 : Blo 135790 308069 := bbase (se 4 (by rfl) ⟨28881, by rfl⟩ : syracuseStep 308069 = 57763) (by norm_num)
theorem B1880981 : Blo 135790 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B177061 : Blo 135790 177061 := bbase (se 4 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 177061 = 33199) (by norm_num)
theorem B308141 : Blo 135790 308141 := bbase (se 3 (by rfl) ⟨57776, by rfl⟩ : syracuseStep 308141 = 115553) (by norm_num)
theorem B308213 : Blo 135790 308213 := bbase (se 5 (by rfl) ⟨14447, by rfl⟩ : syracuseStep 308213 = 28895) (by norm_num)
theorem B308285 : Blo 135790 308285 := bbase (se 3 (by rfl) ⟨57803, by rfl⟩ : syracuseStep 308285 = 115607) (by norm_num)
theorem B1979477 : Blo 135790 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B308357 : Blo 135790 308357 := bbase (se 4 (by rfl) ⟨28908, by rfl⟩ : syracuseStep 308357 = 57817) (by norm_num)
theorem B701621 : Blo 135790 701621 := bbase (se 5 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 701621 = 65777) (by norm_num)
theorem B308429 : Blo 135790 308429 := bbase (se 3 (by rfl) ⟨57830, by rfl⟩ : syracuseStep 308429 = 115661) (by norm_num)
theorem B177385 : Blo 135790 177385 := bbase (se 2 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 177385 = 133039) (by norm_num)
theorem B308501 : Blo 135790 308501 := bbase (se 6 (by rfl) ⟨7230, by rfl⟩ : syracuseStep 308501 = 14461) (by norm_num)
theorem B308573 : Blo 135790 308573 := bbase (se 3 (by rfl) ⟨57857, by rfl⟩ : syracuseStep 308573 = 115715) (by norm_num)
theorem B308645 : Blo 135790 308645 := bbase (se 4 (by rfl) ⟨28935, by rfl⟩ : syracuseStep 308645 = 57871) (by norm_num)
theorem B308717 : Blo 135790 308717 := bbase (se 3 (by rfl) ⟨57884, by rfl⟩ : syracuseStep 308717 = 115769) (by norm_num)
theorem B308789 : Blo 135790 308789 := bbase (se 5 (by rfl) ⟨14474, by rfl⟩ : syracuseStep 308789 = 28949) (by norm_num)
theorem B308861 : Blo 135790 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B308933 : Blo 135790 308933 := bbase (se 4 (by rfl) ⟨28962, by rfl⟩ : syracuseStep 308933 = 57925) (by norm_num)
theorem B309005 : Blo 135790 309005 := bbase (se 3 (by rfl) ⟨57938, by rfl⟩ : syracuseStep 309005 = 115877) (by norm_num)
theorem B309077 : Blo 135790 309077 := bbase (se 9 (by rfl) ⟨905, by rfl⟩ : syracuseStep 309077 = 1811) (by norm_num)
theorem B145261 : Blo 135790 145261 := bbase (se 3 (by rfl) ⟨27236, by rfl⟩ : syracuseStep 145261 = 54473) (by norm_num)
theorem B309149 : Blo 135790 309149 := bbase (se 3 (by rfl) ⟨57965, by rfl⟩ : syracuseStep 309149 = 115931) (by norm_num)
theorem B145333 : Blo 135790 145333 := bbase (se 5 (by rfl) ⟨6812, by rfl⟩ : syracuseStep 145333 = 13625) (by norm_num)
theorem B309221 : Blo 135790 309221 := bbase (se 4 (by rfl) ⟨28989, by rfl⟩ : syracuseStep 309221 = 57979) (by norm_num)
theorem B309293 : Blo 135790 309293 := bbase (se 3 (by rfl) ⟨57992, by rfl⟩ : syracuseStep 309293 = 115985) (by norm_num)
theorem B145513 : Blo 135790 145513 := bbase (se 2 (by rfl) ⟨54567, by rfl⟩ : syracuseStep 145513 = 109135) (by norm_num)
theorem B309365 : Blo 135790 309365 := bbase (se 5 (by rfl) ⟨14501, by rfl⟩ : syracuseStep 309365 = 29003) (by norm_num)
theorem B309437 : Blo 135790 309437 := bbase (se 3 (by rfl) ⟨58019, by rfl⟩ : syracuseStep 309437 = 116039) (by norm_num)
theorem B178369 : Blo 135790 178369 := bbase (se 2 (by rfl) ⟨66888, by rfl⟩ : syracuseStep 178369 = 133777) (by norm_num)
theorem B669941 : Blo 135790 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B309509 : Blo 135790 309509 := bbase (se 4 (by rfl) ⟨29016, by rfl⟩ : syracuseStep 309509 = 58033) (by norm_num)
theorem B178453 : Blo 135790 178453 := bbase (se 6 (by rfl) ⟨4182, by rfl⟩ : syracuseStep 178453 = 8365) (by norm_num)
theorem B899381 : Blo 135790 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B309581 : Blo 135790 309581 := bbase (se 3 (by rfl) ⟨58046, by rfl⟩ : syracuseStep 309581 = 116093) (by norm_num)
theorem B309653 : Blo 135790 309653 := bbase (se 6 (by rfl) ⟨7257, by rfl⟩ : syracuseStep 309653 = 14515) (by norm_num)
theorem B440741 : Blo 135790 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B702917 : Blo 135790 702917 := bbase (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) (by norm_num)
theorem B309725 : Blo 135790 309725 := bbase (se 3 (by rfl) ⟨58073, by rfl⟩ : syracuseStep 309725 = 116147) (by norm_num)
theorem B506341 : Blo 135790 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B145957 : Blo 135790 145957 := bbase (se 4 (by rfl) ⟨13683, by rfl⟩ : syracuseStep 145957 = 27367) (by norm_num)
theorem B309797 : Blo 135790 309797 := bbase (se 4 (by rfl) ⟨29043, by rfl⟩ : syracuseStep 309797 = 58087) (by norm_num)
theorem B309869 : Blo 135790 309869 := bbase (se 3 (by rfl) ⟨58100, by rfl⟩ : syracuseStep 309869 = 116201) (by norm_num)
theorem B146081 : Blo 135790 146081 := bbase (se 2 (by rfl) ⟨54780, by rfl⟩ : syracuseStep 146081 = 109561) (by norm_num)
theorem B309941 : Blo 135790 309941 := bbase (se 5 (by rfl) ⟨14528, by rfl⟩ : syracuseStep 309941 = 29057) (by norm_num)
theorem B310013 : Blo 135790 310013 := bbase (se 3 (by rfl) ⟨58127, by rfl⟩ : syracuseStep 310013 = 116255) (by norm_num)
theorem B310085 : Blo 135790 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B310157 : Blo 135790 310157 := bbase (se 3 (by rfl) ⟨58154, by rfl⟩ : syracuseStep 310157 = 116309) (by norm_num)
theorem B146333 : Blo 135790 146333 := bbase (se 3 (by rfl) ⟨27437, by rfl⟩ : syracuseStep 146333 = 54875) (by norm_num)
theorem B310229 : Blo 135790 310229 := bbase (se 7 (by rfl) ⟨3635, by rfl⟩ : syracuseStep 310229 = 7271) (by norm_num)
theorem B310301 : Blo 135790 310301 := bbase (se 3 (by rfl) ⟨58181, by rfl⟩ : syracuseStep 310301 = 116363) (by norm_num)
theorem B310373 : Blo 135790 310373 := bbase (se 4 (by rfl) ⟨29097, by rfl⟩ : syracuseStep 310373 = 58195) (by norm_num)
theorem B310445 : Blo 135790 310445 := bbase (se 3 (by rfl) ⟨58208, by rfl⟩ : syracuseStep 310445 = 116417) (by norm_num)
theorem B310517 : Blo 135790 310517 := bbase (se 5 (by rfl) ⟨14555, by rfl⟩ : syracuseStep 310517 = 29111) (by norm_num)
theorem B310589 : Blo 135790 310589 := bbase (se 3 (by rfl) ⟨58235, by rfl⟩ : syracuseStep 310589 = 116471) (by norm_num)
theorem B310613 : Blo 135790 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B146777 : Blo 135790 146777 := bbase (se 2 (by rfl) ⟨55041, by rfl⟩ : syracuseStep 146777 = 110083) (by norm_num)
theorem B310661 : Blo 135790 310661 := bbase (se 4 (by rfl) ⟨29124, by rfl⟩ : syracuseStep 310661 = 58249) (by norm_num)
theorem B245149 : Blo 135790 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B310733 : Blo 135790 310733 := bbase (se 3 (by rfl) ⟨58262, by rfl⟩ : syracuseStep 310733 = 116525) (by norm_num)
theorem B310805 : Blo 135790 310805 := bbase (se 6 (by rfl) ⟨7284, by rfl⟩ : syracuseStep 310805 = 14569) (by norm_num)
theorem B212501 : Blo 135790 212501 := bbase (se 6 (by rfl) ⟨4980, by rfl⟩ : syracuseStep 212501 = 9961) (by norm_num)
theorem B147025 : Blo 135790 147025 := bbase (se 2 (by rfl) ⟨55134, by rfl⟩ : syracuseStep 147025 = 110269) (by norm_num)
theorem B310877 : Blo 135790 310877 := bbase (se 3 (by rfl) ⟨58289, by rfl⟩ : syracuseStep 310877 = 116579) (by norm_num)
theorem B310949 : Blo 135790 310949 := bbase (se 4 (by rfl) ⟨29151, by rfl⟩ : syracuseStep 310949 = 58303) (by norm_num)
theorem B442037 : Blo 135790 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B704213 : Blo 135790 704213 := bbase (se 7 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 704213 = 16505) (by norm_num)
theorem B311021 : Blo 135790 311021 := bbase (se 3 (by rfl) ⟨58316, by rfl⟩ : syracuseStep 311021 = 116633) (by norm_num)
theorem B376613 : Blo 135790 376613 := bbase (se 4 (by rfl) ⟨35307, by rfl⟩ : syracuseStep 376613 = 70615) (by norm_num)
theorem B311093 : Blo 135790 311093 := bbase (se 5 (by rfl) ⟨14582, by rfl⟩ : syracuseStep 311093 = 29165) (by norm_num)
theorem B343885 : Blo 135790 343885 := bbase (se 3 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 343885 = 128957) (by norm_num)
theorem B311165 : Blo 135790 311165 := bbase (se 3 (by rfl) ⟨58343, by rfl⟩ : syracuseStep 311165 = 116687) (by norm_num)
theorem B278437 : Blo 135790 278437 := bbase (se 4 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 278437 = 52207) (by norm_num)
theorem B376741 : Blo 135790 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B343997 : Blo 135790 343997 := bbase (se 3 (by rfl) ⟨64499, by rfl⟩ : syracuseStep 343997 = 128999) (by norm_num)
theorem B311237 : Blo 135790 311237 := bbase (se 4 (by rfl) ⟨29178, by rfl⟩ : syracuseStep 311237 = 58357) (by norm_num)
theorem B147469 : Blo 135790 147469 := bbase (se 3 (by rfl) ⟨27650, by rfl⟩ : syracuseStep 147469 = 55301) (by norm_num)
theorem B311309 : Blo 135790 311309 := bbase (se 3 (by rfl) ⟨58370, by rfl⟩ : syracuseStep 311309 = 116741) (by norm_num)
theorem B147529 : Blo 135790 147529 := bbase (se 2 (by rfl) ⟨55323, by rfl⟩ : syracuseStep 147529 = 110647) (by norm_num)
theorem B311381 : Blo 135790 311381 := bbase (se 8 (by rfl) ⟨1824, by rfl⟩ : syracuseStep 311381 = 3649) (by norm_num)
theorem B344189 : Blo 135790 344189 := bbase (se 3 (by rfl) ⟨64535, by rfl⟩ : syracuseStep 344189 = 129071) (by norm_num)
theorem B311453 : Blo 135790 311453 := bbase (se 3 (by rfl) ⟨58397, by rfl⟩ : syracuseStep 311453 = 116795) (by norm_num)
theorem B377045 : Blo 135790 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B311525 : Blo 135790 311525 := bbase (se 4 (by rfl) ⟨29205, by rfl⟩ : syracuseStep 311525 = 58411) (by norm_num)
theorem B737525 : Blo 135790 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B311597 : Blo 135790 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B311669 : Blo 135790 311669 := bbase (se 5 (by rfl) ⟨14609, by rfl⟩ : syracuseStep 311669 = 29219) (by norm_num)
theorem B147845 : Blo 135790 147845 := bbase (se 4 (by rfl) ⟨13860, by rfl⟩ : syracuseStep 147845 = 27721) (by norm_num)
theorem B278957 : Blo 135790 278957 := bbase (se 3 (by rfl) ⟨52304, by rfl⟩ : syracuseStep 278957 = 104609) (by norm_num)
theorem B311741 : Blo 135790 311741 := bbase (se 3 (by rfl) ⟨58451, by rfl⟩ : syracuseStep 311741 = 116903) (by norm_num)
theorem B344533 : Blo 135790 344533 := bbase (se 7 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 344533 = 8075) (by norm_num)
theorem B311813 : Blo 135790 311813 := bbase (se 4 (by rfl) ⟨29232, by rfl⟩ : syracuseStep 311813 = 58465) (by norm_num)
theorem B344645 : Blo 135790 344645 := bbase (se 4 (by rfl) ⟨32310, by rfl⟩ : syracuseStep 344645 = 64621) (by norm_num)
theorem B311885 : Blo 135790 311885 := bbase (se 3 (by rfl) ⟨58478, by rfl⟩ : syracuseStep 311885 = 116957) (by norm_num)
theorem B246397 : Blo 135790 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B311957 : Blo 135790 311957 := bbase (se 6 (by rfl) ⟨7311, by rfl⟩ : syracuseStep 311957 = 14623) (by norm_num)
theorem B705205 : Blo 135790 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B312029 : Blo 135790 312029 := bbase (se 3 (by rfl) ⟨58505, by rfl⟩ : syracuseStep 312029 = 117011) (by norm_num)
theorem B344837 : Blo 135790 344837 := bbase (se 4 (by rfl) ⟨32328, by rfl⟩ : syracuseStep 344837 = 64657) (by norm_num)
theorem B312101 : Blo 135790 312101 := bbase (se 4 (by rfl) ⟨29259, by rfl⟩ : syracuseStep 312101 = 58519) (by norm_num)
theorem B148289 : Blo 135790 148289 := bbase (se 2 (by rfl) ⟨55608, by rfl⟩ : syracuseStep 148289 = 111217) (by norm_num)
theorem B312173 : Blo 135790 312173 := bbase (se 3 (by rfl) ⟨58532, by rfl⟩ : syracuseStep 312173 = 117065) (by norm_num)
theorem B148349 : Blo 135790 148349 := bbase (se 3 (by rfl) ⟨27815, by rfl⟩ : syracuseStep 148349 = 55631) (by norm_num)
theorem B574373 : Blo 135790 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B312245 : Blo 135790 312245 := bbase (se 5 (by rfl) ⟨14636, by rfl⟩ : syracuseStep 312245 = 29273) (by norm_num)
theorem B705509 : Blo 135790 705509 := bbase (se 4 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 705509 = 132283) (by norm_num)
theorem B312317 : Blo 135790 312317 := bbase (se 3 (by rfl) ⟨58559, by rfl⟩ : syracuseStep 312317 = 117119) (by norm_num)
theorem B148477 : Blo 135790 148477 := bbase (se 3 (by rfl) ⟨27839, by rfl⟩ : syracuseStep 148477 = 55679) (by norm_num)
theorem B312365 : Blo 135790 312365 := bbase (se 3 (by rfl) ⟨58568, by rfl⟩ : syracuseStep 312365 = 117137) (by norm_num)
theorem B279605 : Blo 135790 279605 := bbase (se 5 (by rfl) ⟨13106, by rfl⟩ : syracuseStep 279605 = 26213) (by norm_num)
theorem B312389 : Blo 135790 312389 := bbase (se 4 (by rfl) ⟨29286, by rfl⟩ : syracuseStep 312389 = 58573) (by norm_num)
theorem B345181 : Blo 135790 345181 := bbase (se 3 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 345181 = 129443) (by norm_num)
theorem B312461 : Blo 135790 312461 := bbase (se 3 (by rfl) ⟨58586, by rfl⟩ : syracuseStep 312461 = 117173) (by norm_num)
theorem B345293 : Blo 135790 345293 := bbase (se 3 (by rfl) ⟨64742, by rfl⟩ : syracuseStep 345293 = 129485) (by norm_num)
theorem B312533 : Blo 135790 312533 := bbase (se 7 (by rfl) ⟨3662, by rfl⟩ : syracuseStep 312533 = 7325) (by norm_num)
theorem B312605 : Blo 135790 312605 := bbase (se 3 (by rfl) ⟨58613, by rfl⟩ : syracuseStep 312605 = 117227) (by norm_num)
theorem B312677 : Blo 135790 312677 := bbase (se 4 (by rfl) ⟨29313, by rfl⟩ : syracuseStep 312677 = 58627) (by norm_num)
theorem B345485 : Blo 135790 345485 := bbase (se 3 (by rfl) ⟨64778, by rfl⟩ : syracuseStep 345485 = 129557) (by norm_num)
theorem B1590677 : Blo 135790 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B312749 : Blo 135790 312749 := bbase (se 3 (by rfl) ⟨58640, by rfl⟩ : syracuseStep 312749 = 117281) (by norm_num)
theorem B148921 : Blo 135790 148921 := bbase (se 2 (by rfl) ⟨55845, by rfl⟩ : syracuseStep 148921 = 111691) (by norm_num)
theorem B443893 : Blo 135790 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B312821 : Blo 135790 312821 := bbase (se 5 (by rfl) ⟨14663, by rfl⟩ : syracuseStep 312821 = 29327) (by norm_num)
theorem B149041 : Blo 135790 149041 := bbase (se 2 (by rfl) ⟨55890, by rfl⟩ : syracuseStep 149041 = 111781) (by norm_num)
theorem B312893 : Blo 135790 312893 := bbase (se 3 (by rfl) ⟨58667, by rfl⟩ : syracuseStep 312893 = 117335) (by norm_num)
theorem B280189 : Blo 135790 280189 := bbase (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) (by norm_num)
theorem B312965 : Blo 135790 312965 := bbase (se 4 (by rfl) ⟨29340, by rfl⟩ : syracuseStep 312965 = 58681) (by norm_num)
theorem B476869 : Blo 135790 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B313037 : Blo 135790 313037 := bbase (se 3 (by rfl) ⟨58694, by rfl⟩ : syracuseStep 313037 = 117389) (by norm_num)
theorem B345829 : Blo 135790 345829 := bbase (se 4 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 345829 = 64843) (by norm_num)
theorem B313109 : Blo 135790 313109 := bbase (se 6 (by rfl) ⟨7338, by rfl⟩ : syracuseStep 313109 = 14677) (by norm_num)
theorem B1787669 : Blo 135790 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B345941 : Blo 135790 345941 := bbase (se 9 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 345941 = 2027) (by norm_num)
theorem B313181 : Blo 135790 313181 := bbase (se 3 (by rfl) ⟨58721, by rfl⟩ : syracuseStep 313181 = 117443) (by norm_num)
theorem B313253 : Blo 135790 313253 := bbase (se 4 (by rfl) ⟨29367, by rfl⟩ : syracuseStep 313253 = 58735) (by norm_num)
theorem B247781 : Blo 135790 247781 := bbase (se 4 (by rfl) ⟨23229, by rfl⟩ : syracuseStep 247781 = 46459) (by norm_num)
theorem B313325 : Blo 135790 313325 := bbase (se 3 (by rfl) ⟨58748, by rfl⟩ : syracuseStep 313325 = 117497) (by norm_num)
theorem B346133 : Blo 135790 346133 := bbase (se 6 (by rfl) ⟨8112, by rfl⟩ : syracuseStep 346133 = 16225) (by norm_num)
theorem B313397 : Blo 135790 313397 := bbase (se 5 (by rfl) ⟨14690, by rfl⟩ : syracuseStep 313397 = 29381) (by norm_num)
theorem B313469 : Blo 135790 313469 := bbase (se 3 (by rfl) ⟨58775, by rfl⟩ : syracuseStep 313469 = 117551) (by norm_num)
theorem B1230997 : Blo 135790 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B313541 : Blo 135790 313541 := bbase (se 4 (by rfl) ⟨29394, by rfl⟩ : syracuseStep 313541 = 58789) (by norm_num)
theorem B706805 : Blo 135790 706805 := bbase (se 5 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 706805 = 66263) (by norm_num)
theorem B313613 : Blo 135790 313613 := bbase (se 3 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 313613 = 117605) (by norm_num)
theorem B313685 : Blo 135790 313685 := bbase (se 10 (by rfl) ⟨459, by rfl⟩ : syracuseStep 313685 = 919) (by norm_num)
theorem B346477 : Blo 135790 346477 := bbase (se 3 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 346477 = 129929) (by norm_num)
theorem B313757 : Blo 135790 313757 := bbase (se 3 (by rfl) ⟨58829, by rfl⟩ : syracuseStep 313757 = 117659) (by norm_num)
theorem B346589 : Blo 135790 346589 := bbase (se 3 (by rfl) ⟨64985, by rfl⟩ : syracuseStep 346589 = 129971) (by norm_num)
theorem B313829 : Blo 135790 313829 := bbase (se 4 (by rfl) ⟨29421, by rfl⟩ : syracuseStep 313829 = 58843) (by norm_num)
theorem B313901 : Blo 135790 313901 := bbase (se 3 (by rfl) ⟨58856, by rfl⟩ : syracuseStep 313901 = 117713) (by norm_num)
theorem B313973 : Blo 135790 313973 := bbase (se 5 (by rfl) ⟨14717, by rfl⟩ : syracuseStep 313973 = 29435) (by norm_num)
theorem B1493653 : Blo 135790 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B477845 : Blo 135790 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B346781 : Blo 135790 346781 := bbase (se 3 (by rfl) ⟨65021, by rfl⟩ : syracuseStep 346781 = 130043) (by norm_num)
theorem B314045 : Blo 135790 314045 := bbase (se 3 (by rfl) ⟨58883, by rfl⟩ : syracuseStep 314045 = 117767) (by norm_num)
theorem B314117 : Blo 135790 314117 := bbase (se 4 (by rfl) ⟨29448, by rfl⟩ : syracuseStep 314117 = 58897) (by norm_num)
theorem B281389 : Blo 135790 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B314189 : Blo 135790 314189 := bbase (se 3 (by rfl) ⟨58910, by rfl⟩ : syracuseStep 314189 = 117821) (by norm_num)
theorem B314261 : Blo 135790 314261 := bbase (se 6 (by rfl) ⟨7365, by rfl⟩ : syracuseStep 314261 = 14731) (by norm_num)
theorem B576437 : Blo 135790 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B314333 : Blo 135790 314333 := bbase (se 3 (by rfl) ⟨58937, by rfl⟩ : syracuseStep 314333 = 117875) (by norm_num)
theorem B347125 : Blo 135790 347125 := bbase (se 5 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 347125 = 32543) (by norm_num)
theorem B248845 : Blo 135790 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B314405 : Blo 135790 314405 := bbase (se 4 (by rfl) ⟨29475, by rfl⟩ : syracuseStep 314405 = 58951) (by norm_num)
theorem B347237 : Blo 135790 347237 := bbase (se 4 (by rfl) ⟨32553, by rfl⟩ : syracuseStep 347237 = 65107) (by norm_num)
theorem B314477 : Blo 135790 314477 := bbase (se 3 (by rfl) ⟨58964, by rfl⟩ : syracuseStep 314477 = 117929) (by norm_num)
theorem B314501 : Blo 135790 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B150745 : Blo 135790 150745 := bbase (se 2 (by rfl) ⟨56529, by rfl⟩ : syracuseStep 150745 = 113059) (by norm_num)
theorem B249085 : Blo 135790 249085 := bbase (se 3 (by rfl) ⟨46703, by rfl⟩ : syracuseStep 249085 = 93407) (by norm_num)
theorem B347429 : Blo 135790 347429 := bbase (se 4 (by rfl) ⟨32571, by rfl⟩ : syracuseStep 347429 = 65143) (by norm_num)
theorem B249293 : Blo 135790 249293 := bbase (se 3 (by rfl) ⟨46742, by rfl⟩ : syracuseStep 249293 = 93485) (by norm_num)
theorem B249301 : Blo 135790 249301 := bbase (se 7 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 249301 = 5843) (by norm_num)
theorem B151093 : Blo 135790 151093 := bbase (se 5 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 151093 = 14165) (by norm_num)
theorem B347773 : Blo 135790 347773 := bbase (se 3 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 347773 = 130415) (by norm_num)
theorem B347885 : Blo 135790 347885 := bbase (se 3 (by rfl) ⟨65228, by rfl⟩ : syracuseStep 347885 = 130457) (by norm_num)
theorem B184133 : Blo 135790 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B5820245 : Blo 135790 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B282533 : Blo 135790 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B348077 : Blo 135790 348077 := bbase (se 3 (by rfl) ⟨65264, by rfl⟩ : syracuseStep 348077 = 130529) (by norm_num)
theorem B282541 : Blo 135790 282541 := bbase (se 3 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 282541 = 105953) (by norm_num)
theorem B937973 : Blo 135790 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B413957 : Blo 135790 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B348421 : Blo 135790 348421 := bbase (se 4 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 348421 = 65329) (by norm_num)
theorem B348533 : Blo 135790 348533 := bbase (se 5 (by rfl) ⟨16337, by rfl⟩ : syracuseStep 348533 = 32675) (by norm_num)
theorem B348725 : Blo 135790 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B250469 : Blo 135790 250469 := bbase (se 4 (by rfl) ⟨23481, by rfl⟩ : syracuseStep 250469 = 46963) (by norm_num)
theorem B217829 : Blo 135790 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B349069 : Blo 135790 349069 := bbase (se 3 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 349069 = 130901) (by norm_num)
theorem B1004501 : Blo 135790 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B316381 : Blo 135790 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B185333 : Blo 135790 185333 := bbase (se 5 (by rfl) ⟨8687, by rfl⟩ : syracuseStep 185333 = 17375) (by norm_num)
theorem B349181 : Blo 135790 349181 := bbase (se 3 (by rfl) ⟨65471, by rfl⟩ : syracuseStep 349181 = 130943) (by norm_num)
theorem B185365 : Blo 135790 185365 := bbase (se 6 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 185365 = 8689) (by norm_num)
theorem B349373 : Blo 135790 349373 := bbase (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) (by norm_num)
theorem B152797 : Blo 135790 152797 := bbase (se 3 (by rfl) ⟨28649, by rfl⟩ : syracuseStep 152797 = 57299) (by norm_num)
theorem B218333 : Blo 135790 218333 := bbase (se 3 (by rfl) ⟨40937, by rfl⟩ : syracuseStep 218333 = 81875) (by norm_num)
theorem B152833 : Blo 135790 152833 := bbase (se 2 (by rfl) ⟨57312, by rfl⟩ : syracuseStep 152833 = 114625) (by norm_num)
theorem B152869 : Blo 135790 152869 := bbase (se 4 (by rfl) ⟨14331, by rfl⟩ : syracuseStep 152869 = 28663) (by norm_num)
theorem B152905 : Blo 135790 152905 := bbase (se 2 (by rfl) ⟨57339, by rfl⟩ : syracuseStep 152905 = 114679) (by norm_num)
theorem B218461 : Blo 135790 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B152941 : Blo 135790 152941 := bbase (se 3 (by rfl) ⟨28676, by rfl⟩ : syracuseStep 152941 = 57353) (by norm_num)
theorem B152977 : Blo 135790 152977 := bbase (se 2 (by rfl) ⟨57366, by rfl⟩ : syracuseStep 152977 = 114733) (by norm_num)
theorem B284077 : Blo 135790 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B153013 : Blo 135790 153013 := bbase (se 5 (by rfl) ⟨7172, by rfl⟩ : syracuseStep 153013 = 14345) (by norm_num)
theorem B185797 : Blo 135790 185797 := bbase (se 4 (by rfl) ⟨17418, by rfl⟩ : syracuseStep 185797 = 34837) (by norm_num)
theorem B153049 : Blo 135790 153049 := bbase (se 2 (by rfl) ⟨57393, by rfl⟩ : syracuseStep 153049 = 114787) (by norm_num)
theorem B153085 : Blo 135790 153085 := bbase (se 3 (by rfl) ⟨28703, by rfl⟩ : syracuseStep 153085 = 57407) (by norm_num)
theorem B349717 : Blo 135790 349717 := bbase (se 6 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 349717 = 16393) (by norm_num)
theorem B153121 : Blo 135790 153121 := bbase (se 2 (by rfl) ⟨57420, by rfl⟩ : syracuseStep 153121 = 114841) (by norm_num)
theorem B153157 : Blo 135790 153157 := bbase (se 4 (by rfl) ⟨14358, by rfl⟩ : syracuseStep 153157 = 28717) (by norm_num)
theorem B153193 : Blo 135790 153193 := bbase (se 2 (by rfl) ⟨57447, by rfl⟩ : syracuseStep 153193 = 114895) (by norm_num)
theorem B349829 : Blo 135790 349829 := bbase (se 4 (by rfl) ⟨32796, by rfl⟩ : syracuseStep 349829 = 65593) (by norm_num)
theorem B153229 : Blo 135790 153229 := bbase (se 3 (by rfl) ⟨28730, by rfl⟩ : syracuseStep 153229 = 57461) (by norm_num)
theorem B153265 : Blo 135790 153265 := bbase (se 2 (by rfl) ⟨57474, by rfl⟩ : syracuseStep 153265 = 114949) (by norm_num)
theorem B153301 : Blo 135790 153301 := bbase (se 7 (by rfl) ⟨1796, by rfl⟩ : syracuseStep 153301 = 3593) (by norm_num)
theorem B153337 : Blo 135790 153337 := bbase (se 2 (by rfl) ⟨57501, by rfl⟩ : syracuseStep 153337 = 115003) (by norm_num)
theorem B153373 : Blo 135790 153373 := bbase (se 3 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 153373 = 57515) (by norm_num)
theorem B153409 : Blo 135790 153409 := bbase (se 2 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 153409 = 115057) (by norm_num)
theorem B350021 : Blo 135790 350021 := bbase (se 4 (by rfl) ⟨32814, by rfl⟩ : syracuseStep 350021 = 65629) (by norm_num)
theorem B153445 : Blo 135790 153445 := bbase (se 4 (by rfl) ⟨14385, by rfl⟩ : syracuseStep 153445 = 28771) (by norm_num)
theorem B153481 : Blo 135790 153481 := bbase (se 2 (by rfl) ⟨57555, by rfl⟩ : syracuseStep 153481 = 115111) (by norm_num)
theorem B153517 : Blo 135790 153517 := bbase (se 3 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 153517 = 57569) (by norm_num)
theorem B153553 : Blo 135790 153553 := bbase (se 2 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 153553 = 115165) (by norm_num)
theorem B153589 : Blo 135790 153589 := bbase (se 5 (by rfl) ⟨7199, by rfl⟩ : syracuseStep 153589 = 14399) (by norm_num)
theorem B153625 : Blo 135790 153625 := bbase (se 2 (by rfl) ⟨57609, by rfl⟩ : syracuseStep 153625 = 115219) (by norm_num)
theorem B710693 : Blo 135790 710693 := bbase (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) (by norm_num)
theorem B153661 : Blo 135790 153661 := bbase (se 3 (by rfl) ⟨28811, by rfl⟩ : syracuseStep 153661 = 57623) (by norm_num)
theorem B153697 : Blo 135790 153697 := bbase (se 2 (by rfl) ⟨57636, by rfl⟩ : syracuseStep 153697 = 115273) (by norm_num)
theorem B153733 : Blo 135790 153733 := bbase (se 4 (by rfl) ⟨14412, by rfl⟩ : syracuseStep 153733 = 28825) (by norm_num)
theorem B350365 : Blo 135790 350365 := bbase (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) (by norm_num)
theorem B153769 : Blo 135790 153769 := bbase (se 2 (by rfl) ⟨57663, by rfl⟩ : syracuseStep 153769 = 115327) (by norm_num)
theorem B153805 : Blo 135790 153805 := bbase (se 3 (by rfl) ⟨28838, by rfl⟩ : syracuseStep 153805 = 57677) (by norm_num)
theorem B153841 : Blo 135790 153841 := bbase (se 2 (by rfl) ⟨57690, by rfl⟩ : syracuseStep 153841 = 115381) (by norm_num)
theorem B1038581 : Blo 135790 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B350477 : Blo 135790 350477 := bbase (se 3 (by rfl) ⟨65714, by rfl⟩ : syracuseStep 350477 = 131429) (by norm_num)
theorem B153877 : Blo 135790 153877 := bbase (se 6 (by rfl) ⟨3606, by rfl⟩ : syracuseStep 153877 = 7213) (by norm_num)
theorem B153913 : Blo 135790 153913 := bbase (se 2 (by rfl) ⟨57717, by rfl⟩ : syracuseStep 153913 = 115435) (by norm_num)
theorem B153949 : Blo 135790 153949 := bbase (se 3 (by rfl) ⟨28865, by rfl⟩ : syracuseStep 153949 = 57731) (by norm_num)
theorem B153985 : Blo 135790 153985 := bbase (se 2 (by rfl) ⟨57744, by rfl⟩ : syracuseStep 153985 = 115489) (by norm_num)
theorem B154021 : Blo 135790 154021 := bbase (se 4 (by rfl) ⟨14439, by rfl⟩ : syracuseStep 154021 = 28879) (by norm_num)
theorem B154057 : Blo 135790 154057 := bbase (se 2 (by rfl) ⟨57771, by rfl⟩ : syracuseStep 154057 = 115543) (by norm_num)
theorem B350669 : Blo 135790 350669 := bbase (se 3 (by rfl) ⟨65750, by rfl⟩ : syracuseStep 350669 = 131501) (by norm_num)
theorem B154093 : Blo 135790 154093 := bbase (se 3 (by rfl) ⟨28892, by rfl⟩ : syracuseStep 154093 = 57785) (by norm_num)
theorem B1169909 : Blo 135790 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B154129 : Blo 135790 154129 := bbase (se 2 (by rfl) ⟨57798, by rfl⟩ : syracuseStep 154129 = 115597) (by norm_num)
theorem B154165 : Blo 135790 154165 := bbase (se 5 (by rfl) ⟨7226, by rfl⟩ : syracuseStep 154165 = 14453) (by norm_num)
theorem B154201 : Blo 135790 154201 := bbase (se 2 (by rfl) ⟨57825, by rfl⟩ : syracuseStep 154201 = 115651) (by norm_num)
theorem B154237 : Blo 135790 154237 := bbase (se 3 (by rfl) ⟨28919, by rfl⟩ : syracuseStep 154237 = 57839) (by norm_num)
theorem B154273 : Blo 135790 154273 := bbase (se 2 (by rfl) ⟨57852, by rfl⟩ : syracuseStep 154273 = 115705) (by norm_num)
theorem B154309 : Blo 135790 154309 := bbase (se 4 (by rfl) ⟨14466, by rfl⟩ : syracuseStep 154309 = 28933) (by norm_num)
theorem B219845 : Blo 135790 219845 := bbase (se 4 (by rfl) ⟨20610, by rfl⟩ : syracuseStep 219845 = 41221) (by norm_num)
theorem B154345 : Blo 135790 154345 := bbase (se 2 (by rfl) ⟨57879, by rfl⟩ : syracuseStep 154345 = 115759) (by norm_num)
theorem B154381 : Blo 135790 154381 := bbase (se 3 (by rfl) ⟨28946, by rfl⟩ : syracuseStep 154381 = 57893) (by norm_num)
theorem B351013 : Blo 135790 351013 := bbase (se 4 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 351013 = 65815) (by norm_num)
theorem B154417 : Blo 135790 154417 := bbase (se 2 (by rfl) ⟨57906, by rfl⟩ : syracuseStep 154417 = 115813) (by norm_num)
theorem B318269 : Blo 135790 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B154453 : Blo 135790 154453 := bbase (se 9 (by rfl) ⟨452, by rfl⟩ : syracuseStep 154453 = 905) (by norm_num)
theorem B154489 : Blo 135790 154489 := bbase (se 2 (by rfl) ⟨57933, by rfl⟩ : syracuseStep 154489 = 115867) (by norm_num)
theorem B351125 : Blo 135790 351125 := bbase (se 6 (by rfl) ⟨8229, by rfl⟩ : syracuseStep 351125 = 16459) (by norm_num)
theorem B154525 : Blo 135790 154525 := bbase (se 3 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 154525 = 57947) (by norm_num)
theorem B154561 : Blo 135790 154561 := bbase (se 2 (by rfl) ⟨57960, by rfl⟩ : syracuseStep 154561 = 115921) (by norm_num)
theorem B154597 : Blo 135790 154597 := bbase (se 4 (by rfl) ⟨14493, by rfl⟩ : syracuseStep 154597 = 28987) (by norm_num)
theorem B154633 : Blo 135790 154633 := bbase (se 2 (by rfl) ⟨57987, by rfl⟩ : syracuseStep 154633 = 115975) (by norm_num)
theorem B154669 : Blo 135790 154669 := bbase (se 3 (by rfl) ⟨29000, by rfl⟩ : syracuseStep 154669 = 58001) (by norm_num)
theorem B154705 : Blo 135790 154705 := bbase (se 2 (by rfl) ⟨58014, by rfl⟩ : syracuseStep 154705 = 116029) (by norm_num)
theorem B351317 : Blo 135790 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B154741 : Blo 135790 154741 := bbase (se 5 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 154741 = 14507) (by norm_num)
theorem B154777 : Blo 135790 154777 := bbase (se 2 (by rfl) ⟨58041, by rfl⟩ : syracuseStep 154777 = 116083) (by norm_num)
theorem B154813 : Blo 135790 154813 := bbase (se 3 (by rfl) ⟨29027, by rfl⟩ : syracuseStep 154813 = 58055) (by norm_num)
theorem B154849 : Blo 135790 154849 := bbase (se 2 (by rfl) ⟨58068, by rfl⟩ : syracuseStep 154849 = 116137) (by norm_num)
theorem B154885 : Blo 135790 154885 := bbase (se 4 (by rfl) ⟨14520, by rfl⟩ : syracuseStep 154885 = 29041) (by norm_num)
theorem B154921 : Blo 135790 154921 := bbase (se 2 (by rfl) ⟨58095, by rfl⟩ : syracuseStep 154921 = 116191) (by norm_num)
theorem B843061 : Blo 135790 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B154957 : Blo 135790 154957 := bbase (se 3 (by rfl) ⟨29054, by rfl⟩ : syracuseStep 154957 = 58109) (by norm_num)
theorem B15621461 : Blo 135790 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B154993 : Blo 135790 154993 := bbase (se 2 (by rfl) ⟨58122, by rfl⟩ : syracuseStep 154993 = 116245) (by norm_num)
theorem B155029 : Blo 135790 155029 := bbase (se 6 (by rfl) ⟨3633, by rfl⟩ : syracuseStep 155029 = 7267) (by norm_num)
theorem B351661 : Blo 135790 351661 := bbase (se 3 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 351661 = 131873) (by norm_num)
theorem B155065 : Blo 135790 155065 := bbase (se 2 (by rfl) ⟨58149, by rfl⟩ : syracuseStep 155065 = 116299) (by norm_num)
theorem B155101 : Blo 135790 155101 := bbase (se 3 (by rfl) ⟨29081, by rfl⟩ : syracuseStep 155101 = 58163) (by norm_num)
theorem B712165 : Blo 135790 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B155137 : Blo 135790 155137 := bbase (se 2 (by rfl) ⟨58176, by rfl⟩ : syracuseStep 155137 = 116353) (by norm_num)
theorem B351773 : Blo 135790 351773 := bbase (se 3 (by rfl) ⟨65957, by rfl⟩ : syracuseStep 351773 = 131915) (by norm_num)
theorem B155173 : Blo 135790 155173 := bbase (se 4 (by rfl) ⟨14547, by rfl⟩ : syracuseStep 155173 = 29095) (by norm_num)
theorem B155209 : Blo 135790 155209 := bbase (se 2 (by rfl) ⟨58203, by rfl⟩ : syracuseStep 155209 = 116407) (by norm_num)
theorem B220781 : Blo 135790 220781 := bbase (se 3 (by rfl) ⟨41396, by rfl⟩ : syracuseStep 220781 = 82793) (by norm_num)
theorem B155245 : Blo 135790 155245 := bbase (se 3 (by rfl) ⟨29108, by rfl⟩ : syracuseStep 155245 = 58217) (by norm_num)
theorem B417413 : Blo 135790 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B155281 : Blo 135790 155281 := bbase (se 2 (by rfl) ⟨58230, by rfl⟩ : syracuseStep 155281 = 116461) (by norm_num)
theorem B155317 : Blo 135790 155317 := bbase (se 5 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 155317 = 14561) (by norm_num)
theorem B155353 : Blo 135790 155353 := bbase (se 2 (by rfl) ⟨58257, by rfl⟩ : syracuseStep 155353 = 116515) (by norm_num)
theorem B351965 : Blo 135790 351965 := bbase (se 3 (by rfl) ⟨65993, by rfl⟩ : syracuseStep 351965 = 131987) (by norm_num)
theorem B351989 : Blo 135790 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B155389 : Blo 135790 155389 := bbase (se 3 (by rfl) ⟨29135, by rfl⟩ : syracuseStep 155389 = 58271) (by norm_num)
theorem B155425 : Blo 135790 155425 := bbase (se 2 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 155425 = 116569) (by norm_num)
theorem B155461 : Blo 135790 155461 := bbase (se 4 (by rfl) ⟨14574, by rfl⟩ : syracuseStep 155461 = 29149) (by norm_num)
theorem B155497 : Blo 135790 155497 := bbase (se 2 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 155497 = 116623) (by norm_num)
theorem B155533 : Blo 135790 155533 := bbase (se 3 (by rfl) ⟨29162, by rfl⟩ : syracuseStep 155533 = 58325) (by norm_num)
theorem B155569 : Blo 135790 155569 := bbase (se 2 (by rfl) ⟨58338, by rfl⟩ : syracuseStep 155569 = 116677) (by norm_num)
theorem B155605 : Blo 135790 155605 := bbase (se 7 (by rfl) ⟨1823, by rfl⟩ : syracuseStep 155605 = 3647) (by norm_num)
theorem B2383829 : Blo 135790 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B155641 : Blo 135790 155641 := bbase (se 2 (by rfl) ⟨58365, by rfl⟩ : syracuseStep 155641 = 116731) (by norm_num)
theorem B155677 : Blo 135790 155677 := bbase (se 3 (by rfl) ⟨29189, by rfl⟩ : syracuseStep 155677 = 58379) (by norm_num)
theorem B352309 : Blo 135790 352309 := bbase (se 5 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 352309 = 33029) (by norm_num)
theorem B155713 : Blo 135790 155713 := bbase (se 2 (by rfl) ⟨58392, by rfl⟩ : syracuseStep 155713 = 116785) (by norm_num)
theorem B155749 : Blo 135790 155749 := bbase (se 4 (by rfl) ⟨14601, by rfl⟩ : syracuseStep 155749 = 29203) (by norm_num)
theorem B155785 : Blo 135790 155785 := bbase (se 2 (by rfl) ⟨58419, by rfl⟩ : syracuseStep 155785 = 116839) (by norm_num)
theorem B352421 : Blo 135790 352421 := bbase (se 4 (by rfl) ⟨33039, by rfl⟩ : syracuseStep 352421 = 66079) (by norm_num)
theorem B155821 : Blo 135790 155821 := bbase (se 3 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 155821 = 58433) (by norm_num)
theorem B155857 : Blo 135790 155857 := bbase (se 2 (by rfl) ⟨58446, by rfl⟩ : syracuseStep 155857 = 116893) (by norm_num)
theorem B221429 : Blo 135790 221429 := bbase (se 5 (by rfl) ⟨10379, by rfl⟩ : syracuseStep 221429 = 20759) (by norm_num)
theorem B155893 : Blo 135790 155893 := bbase (se 5 (by rfl) ⟨7307, by rfl⟩ : syracuseStep 155893 = 14615) (by norm_num)
theorem B155929 : Blo 135790 155929 := bbase (se 2 (by rfl) ⟨58473, by rfl⟩ : syracuseStep 155929 = 116947) (by norm_num)
theorem B155965 : Blo 135790 155965 := bbase (se 3 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 155965 = 58487) (by norm_num)
theorem B156001 : Blo 135790 156001 := bbase (se 2 (by rfl) ⟨58500, by rfl⟩ : syracuseStep 156001 = 117001) (by norm_num)
theorem B352613 : Blo 135790 352613 := bbase (se 4 (by rfl) ⟨33057, by rfl⟩ : syracuseStep 352613 = 66115) (by norm_num)
theorem B156037 : Blo 135790 156037 := bbase (se 4 (by rfl) ⟨14628, by rfl⟩ : syracuseStep 156037 = 29257) (by norm_num)
theorem B156073 : Blo 135790 156073 := bbase (se 2 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 156073 = 117055) (by norm_num)
theorem B156109 : Blo 135790 156109 := bbase (se 3 (by rfl) ⟨29270, by rfl⟩ : syracuseStep 156109 = 58541) (by norm_num)
theorem B156145 : Blo 135790 156145 := bbase (se 2 (by rfl) ⟨58554, by rfl⟩ : syracuseStep 156145 = 117109) (by norm_num)
theorem B156181 : Blo 135790 156181 := bbase (se 6 (by rfl) ⟨3660, by rfl⟩ : syracuseStep 156181 = 7321) (by norm_num)
theorem B156217 : Blo 135790 156217 := bbase (se 2 (by rfl) ⟨58581, by rfl⟩ : syracuseStep 156217 = 117163) (by norm_num)
theorem B156253 : Blo 135790 156253 := bbase (se 3 (by rfl) ⟨29297, by rfl⟩ : syracuseStep 156253 = 58595) (by norm_num)
theorem B516725 : Blo 135790 516725 := bbase (se 5 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 516725 = 48443) (by norm_num)
theorem B156289 : Blo 135790 156289 := bbase (se 2 (by rfl) ⟨58608, by rfl⟩ : syracuseStep 156289 = 117217) (by norm_num)
theorem B156325 : Blo 135790 156325 := bbase (se 4 (by rfl) ⟨14655, by rfl⟩ : syracuseStep 156325 = 29311) (by norm_num)
theorem B352957 : Blo 135790 352957 := bbase (se 3 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 352957 = 132359) (by norm_num)
theorem B156361 : Blo 135790 156361 := bbase (se 2 (by rfl) ⟨58635, by rfl⟩ : syracuseStep 156361 = 117271) (by norm_num)
theorem B156397 : Blo 135790 156397 := bbase (se 3 (by rfl) ⟨29324, by rfl⟩ : syracuseStep 156397 = 58649) (by norm_num)
theorem B156433 : Blo 135790 156433 := bbase (se 2 (by rfl) ⟨58662, by rfl⟩ : syracuseStep 156433 = 117325) (by norm_num)
theorem B353069 : Blo 135790 353069 := bbase (se 3 (by rfl) ⟨66200, by rfl⟩ : syracuseStep 353069 = 132401) (by norm_num)
theorem B156469 : Blo 135790 156469 := bbase (se 5 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 156469 = 14669) (by norm_num)
theorem B156505 : Blo 135790 156505 := bbase (se 2 (by rfl) ⟨58689, by rfl⟩ : syracuseStep 156505 = 117379) (by norm_num)
theorem B156541 : Blo 135790 156541 := bbase (se 3 (by rfl) ⟨29351, by rfl⟩ : syracuseStep 156541 = 58703) (by norm_num)
theorem B517013 : Blo 135790 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B156577 : Blo 135790 156577 := bbase (se 2 (by rfl) ⟨58716, by rfl⟩ : syracuseStep 156577 = 117433) (by norm_num)
theorem B156613 : Blo 135790 156613 := bbase (se 4 (by rfl) ⟨14682, by rfl⟩ : syracuseStep 156613 = 29365) (by norm_num)
theorem B156649 : Blo 135790 156649 := bbase (se 2 (by rfl) ⟨58743, by rfl⟩ : syracuseStep 156649 = 117487) (by norm_num)
theorem B353261 : Blo 135790 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B156685 : Blo 135790 156685 := bbase (se 3 (by rfl) ⟨29378, by rfl⟩ : syracuseStep 156685 = 58757) (by norm_num)
theorem B156721 : Blo 135790 156721 := bbase (se 2 (by rfl) ⟨58770, by rfl⟩ : syracuseStep 156721 = 117541) (by norm_num)
theorem B156757 : Blo 135790 156757 := bbase (se 8 (by rfl) ⟨918, by rfl⟩ : syracuseStep 156757 = 1837) (by norm_num)
theorem B353381 : Blo 135790 353381 := bbase (se 4 (by rfl) ⟨33129, by rfl⟩ : syracuseStep 353381 = 66259) (by norm_num)
theorem B156793 : Blo 135790 156793 := bbase (se 2 (by rfl) ⟨58797, by rfl⟩ : syracuseStep 156793 = 117595) (by norm_num)
theorem B156829 : Blo 135790 156829 := bbase (se 3 (by rfl) ⟨29405, by rfl⟩ : syracuseStep 156829 = 58811) (by norm_num)
theorem B582821 : Blo 135790 582821 := bbase (se 4 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 582821 = 109279) (by norm_num)
theorem B156865 : Blo 135790 156865 := bbase (se 2 (by rfl) ⟨58824, by rfl⟩ : syracuseStep 156865 = 117649) (by norm_num)
theorem B222421 : Blo 135790 222421 := bbase (se 7 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 222421 = 5213) (by norm_num)
theorem B156901 : Blo 135790 156901 := bbase (se 4 (by rfl) ⟨14709, by rfl⟩ : syracuseStep 156901 = 29419) (by norm_num)
theorem B156937 : Blo 135790 156937 := bbase (se 2 (by rfl) ⟨58851, by rfl⟩ : syracuseStep 156937 = 117703) (by norm_num)
theorem B156973 : Blo 135790 156973 := bbase (se 3 (by rfl) ⟨29432, by rfl⟩ : syracuseStep 156973 = 58865) (by norm_num)
theorem B353605 : Blo 135790 353605 := bbase (se 4 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 353605 = 66301) (by norm_num)
theorem B157009 : Blo 135790 157009 := bbase (se 2 (by rfl) ⟨58878, by rfl⟩ : syracuseStep 157009 = 117757) (by norm_num)
theorem B157045 : Blo 135790 157045 := bbase (se 5 (by rfl) ⟨7361, by rfl⟩ : syracuseStep 157045 = 14723) (by norm_num)
theorem B157081 : Blo 135790 157081 := bbase (se 2 (by rfl) ⟨58905, by rfl⟩ : syracuseStep 157081 = 117811) (by norm_num)
theorem B353717 : Blo 135790 353717 := bbase (se 5 (by rfl) ⟨16580, by rfl⟩ : syracuseStep 353717 = 33161) (by norm_num)
theorem B157117 : Blo 135790 157117 := bbase (se 3 (by rfl) ⟨29459, by rfl⟩ : syracuseStep 157117 = 58919) (by norm_num)
theorem B583109 : Blo 135790 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B157153 : Blo 135790 157153 := bbase (se 2 (by rfl) ⟨58932, by rfl⟩ : syracuseStep 157153 = 117865) (by norm_num)
theorem B157189 : Blo 135790 157189 := bbase (se 4 (by rfl) ⟨14736, by rfl⟩ : syracuseStep 157189 = 29473) (by norm_num)
theorem B157225 : Blo 135790 157225 := bbase (se 2 (by rfl) ⟨58959, by rfl⟩ : syracuseStep 157225 = 117919) (by norm_num)
theorem B157261 : Blo 135790 157261 := bbase (se 3 (by rfl) ⟨29486, by rfl⟩ : syracuseStep 157261 = 58973) (by norm_num)
theorem B222869 : Blo 135790 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B223069 : Blo 135790 223069 := bbase (se 3 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 223069 = 83651) (by norm_num)
theorem B518197 : Blo 135790 518197 := bbase (se 5 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 518197 = 48581) (by norm_num)
theorem B223325 : Blo 135790 223325 := bbase (se 3 (by rfl) ⟨41873, by rfl⟩ : syracuseStep 223325 = 83747) (by norm_num)
theorem B157825 : Blo 135790 157825 := bbase (se 2 (by rfl) ⟨59184, by rfl⟩ : syracuseStep 157825 = 118369) (by norm_num)
theorem B583861 : Blo 135790 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B157945 : Blo 135790 157945 := bbase (se 2 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 157945 = 118459) (by norm_num)
theorem B518501 : Blo 135790 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B158117 : Blo 135790 158117 := bbase (se 4 (by rfl) ⟨14823, by rfl⟩ : syracuseStep 158117 = 29647) (by norm_num)
theorem B158153 : Blo 135790 158153 := bbase (se 2 (by rfl) ⟨59307, by rfl⟩ : syracuseStep 158153 = 118615) (by norm_num)
theorem B584597 : Blo 135790 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B781397 : Blo 135790 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B1305845 : Blo 135790 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B879893 : Blo 135790 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B421157 : Blo 135790 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B388421 : Blo 135790 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B159185 : Blo 135790 159185 := bbase (se 2 (by rfl) ⟨59694, by rfl⟩ : syracuseStep 159185 = 119389) (by norm_num)
theorem B290317 : Blo 135790 290317 := bbase (se 3 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 290317 = 108869) (by norm_num)
theorem B290461 : Blo 135790 290461 := bbase (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) (by norm_num)
theorem B258005 : Blo 135790 258005 := bbase (se 7 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 258005 = 6047) (by norm_num)
theorem B290837 : Blo 135790 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B2093141 : Blo 135790 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B258157 : Blo 135790 258157 := bbase (se 3 (by rfl) ⟨48404, by rfl⟩ : syracuseStep 258157 = 96809) (by norm_num)
theorem B782581 : Blo 135790 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B291205 : Blo 135790 291205 := bbase (se 4 (by rfl) ⟨27300, by rfl⟩ : syracuseStep 291205 = 54601) (by norm_num)
theorem B258461 : Blo 135790 258461 := bbase (se 3 (by rfl) ⟨48461, by rfl⟩ : syracuseStep 258461 = 96923) (by norm_num)
theorem B520613 : Blo 135790 520613 := bbase (se 4 (by rfl) ⟨48807, by rfl⟩ : syracuseStep 520613 = 97615) (by norm_num)
theorem B389605 : Blo 135790 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B356933 : Blo 135790 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B389765 : Blo 135790 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B520901 : Blo 135790 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B390005 : Blo 135790 390005 := bbase (se 5 (by rfl) ⟨18281, by rfl⟩ : syracuseStep 390005 = 36563) (by norm_num)
theorem B390197 : Blo 135790 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B226373 : Blo 135790 226373 := bbase (se 4 (by rfl) ⟨21222, by rfl⟩ : syracuseStep 226373 = 42445) (by norm_num)
theorem B259213 : Blo 135790 259213 := bbase (se 3 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 259213 = 97205) (by norm_num)
theorem B1766549 : Blo 135790 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B193709 : Blo 135790 193709 := bbase (se 3 (by rfl) ⟨36320, by rfl⟩ : syracuseStep 193709 = 72641) (by norm_num)
theorem B193789 : Blo 135790 193789 := bbase (se 3 (by rfl) ⟨36335, by rfl⟩ : syracuseStep 193789 = 72671) (by norm_num)
theorem B259357 : Blo 135790 259357 := bbase (se 3 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 259357 = 97259) (by norm_num)
theorem B357733 : Blo 135790 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B193909 : Blo 135790 193909 := bbase (se 5 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 193909 = 18179) (by norm_num)
theorem B259517 : Blo 135790 259517 := bbase (se 3 (by rfl) ⟨48659, by rfl⟩ : syracuseStep 259517 = 97319) (by norm_num)
theorem B194005 : Blo 135790 194005 := bbase (se 7 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 194005 = 4547) (by norm_num)
theorem B3503573 : Blo 135790 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B259661 : Blo 135790 259661 := bbase (se 3 (by rfl) ⟨48686, by rfl⟩ : syracuseStep 259661 = 97373) (by norm_num)
theorem B1046357 : Blo 135790 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B292709 : Blo 135790 292709 := bbase (se 4 (by rfl) ⟨27441, by rfl⟩ : syracuseStep 292709 = 54883) (by norm_num)
theorem B522085 : Blo 135790 522085 := bbase (se 4 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 522085 = 97891) (by norm_num)
theorem B259949 : Blo 135790 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B194501 : Blo 135790 194501 := bbase (se 4 (by rfl) ⟨18234, by rfl⟩ : syracuseStep 194501 = 36469) (by norm_num)
theorem B489461 : Blo 135790 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B292853 : Blo 135790 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B260101 : Blo 135790 260101 := bbase (se 4 (by rfl) ⟨24384, by rfl⟩ : syracuseStep 260101 = 48769) (by norm_num)
theorem B391189 : Blo 135790 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B587893 : Blo 135790 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B522389 : Blo 135790 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B784565 : Blo 135790 784565 := bbase (se 5 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 784565 = 73553) (by norm_num)
theorem B260405 : Blo 135790 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B424261 : Blo 135790 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B293213 : Blo 135790 293213 := bbase (se 3 (by rfl) ⟨54977, by rfl⟩ : syracuseStep 293213 = 109955) (by norm_num)
theorem B1177973 : Blo 135790 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B2259413 : Blo 135790 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B195053 : Blo 135790 195053 := bbase (se 3 (by rfl) ⟨36572, by rfl⟩ : syracuseStep 195053 = 73145) (by norm_num)
theorem B653845 : Blo 135790 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B326405 : Blo 135790 326405 := bbase (se 4 (by rfl) ⟨30600, by rfl⟩ : syracuseStep 326405 = 61201) (by norm_num)
theorem B326501 : Blo 135790 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B326693 : Blo 135790 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B261157 : Blo 135790 261157 := bbase (se 4 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 261157 = 48967) (by norm_num)
theorem B392293 : Blo 135790 392293 := bbase (se 4 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 392293 = 73555) (by norm_num)
theorem B261301 : Blo 135790 261301 := bbase (se 5 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 261301 = 24497) (by norm_num)
theorem B294101 : Blo 135790 294101 := bbase (se 7 (by rfl) ⟨3446, by rfl⟩ : syracuseStep 294101 = 6893) (by norm_num)
theorem B195805 : Blo 135790 195805 := bbase (se 3 (by rfl) ⟨36713, by rfl⟩ : syracuseStep 195805 = 73427) (by norm_num)
theorem B261461 : Blo 135790 261461 := bbase (se 11 (by rfl) ⟨191, by rfl⟩ : syracuseStep 261461 = 383) (by norm_num)
theorem B294349 : Blo 135790 294349 := bbase (se 3 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 294349 = 110381) (by norm_num)
theorem B261605 : Blo 135790 261605 := bbase (se 4 (by rfl) ⟨24525, by rfl⟩ : syracuseStep 261605 = 49051) (by norm_num)
theorem B1408565 : Blo 135790 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B982613 : Blo 135790 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B458405 : Blo 135790 458405 := bbase (se 4 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 458405 = 85951) (by norm_num)
theorem B491221 : Blo 135790 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B163577 : Blo 135790 163577 := bbase (se 2 (by rfl) ⟨61341, by rfl⟩ : syracuseStep 163577 = 122683) (by norm_num)
theorem B261893 : Blo 135790 261893 := bbase (se 4 (by rfl) ⟨24552, by rfl⟩ : syracuseStep 261893 = 49105) (by norm_num)
theorem B229189 : Blo 135790 229189 := bbase (se 4 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 229189 = 42973) (by norm_num)
theorem B229277 : Blo 135790 229277 := bbase (se 3 (by rfl) ⟨42989, by rfl⟩ : syracuseStep 229277 = 85979) (by norm_num)
theorem B262045 : Blo 135790 262045 := bbase (se 3 (by rfl) ⟨49133, by rfl⟩ : syracuseStep 262045 = 98267) (by norm_num)
theorem B294853 : Blo 135790 294853 := bbase (se 4 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 294853 = 55285) (by norm_num)
theorem B196597 : Blo 135790 196597 := bbase (se 5 (by rfl) ⟨9215, by rfl⟩ : syracuseStep 196597 = 18431) (by norm_num)
theorem B196625 : Blo 135790 196625 := bstep (se 2 (by rfl) ⟨73734, by rfl⟩ : syracuseStep 196625 = 147469) B147469
theorem B1769525 : Blo 135790 1769525 := bstep (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) B165893
theorem B229459 : Blo 135790 229459 := bstep (se 1 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 229459 = 344189) B344189
theorem B196705 : Blo 135790 196705 := bstep (se 2 (by rfl) ⟨73764, by rfl⟩ : syracuseStep 196705 = 147529) B147529
theorem B491683 : Blo 135790 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B229601 : Blo 135790 229601 := bstep (se 2 (by rfl) ⟨86100, by rfl⟩ : syracuseStep 229601 = 172201) B172201
theorem B524515 : Blo 135790 524515 := bstep (se 1 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 524515 = 786773) B786773
theorem B459053 : Blo 135790 459053 := bstep (se 3 (by rfl) ⟨86072, by rfl⟩ : syracuseStep 459053 = 172145) B172145
theorem B229729 : Blo 135790 229729 := bstep (se 2 (by rfl) ⟨86148, by rfl⟩ : syracuseStep 229729 = 172297) B172297
theorem B459107 : Blo 135790 459107 := bstep (se 1 (by rfl) ⟨344330, by rfl⟩ : syracuseStep 459107 = 688661) B688661
theorem B229763 : Blo 135790 229763 := bstep (se 1 (by rfl) ⟨172322, by rfl⟩ : syracuseStep 229763 = 344645) B344645
theorem B262531 : Blo 135790 262531 := bstep (se 1 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 262531 = 393797) B393797
theorem B262577 : Blo 135790 262577 := bstep (se 2 (by rfl) ⟨98466, by rfl⟩ : syracuseStep 262577 = 196933) B196933
theorem B229891 : Blo 135790 229891 := bstep (se 1 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 229891 = 344837) B344837
theorem B885325 : Blo 135790 885325 := bstep (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) B331997
theorem B459377 : Blo 135790 459377 := bstep (se 2 (by rfl) ⟨172266, by rfl⟩ : syracuseStep 459377 = 344533) B344533
theorem B230033 : Blo 135790 230033 := bstep (se 2 (by rfl) ⟨86262, by rfl⟩ : syracuseStep 230033 = 172525) B172525
theorem B393923 : Blo 135790 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B262865 : Blo 135790 262865 := bstep (se 2 (by rfl) ⟨98574, by rfl⟩ : syracuseStep 262865 = 197149) B197149
theorem B230161 : Blo 135790 230161 := bstep (se 2 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 230161 = 172621) B172621
theorem B590627 : Blo 135790 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B230195 : Blo 135790 230195 := bstep (se 1 (by rfl) ⟨172646, by rfl⟩ : syracuseStep 230195 = 345293) B345293
theorem B328529 : Blo 135790 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B197491 : Blo 135790 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B230323 : Blo 135790 230323 := bstep (se 1 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 230323 = 345485) B345485
theorem B951301 : Blo 135790 951301 := bstep (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) B178369
theorem B394253 : Blo 135790 394253 := bstep (se 3 (by rfl) ⟨73922, by rfl⟩ : syracuseStep 394253 = 147845) B147845
theorem B230465 : Blo 135790 230465 := bstep (se 2 (by rfl) ⟨86424, by rfl⟩ : syracuseStep 230465 = 172849) B172849
theorem B394321 : Blo 135790 394321 := bstep (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) B295741
theorem B525425 : Blo 135790 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B459917 : Blo 135790 459917 := bstep (se 3 (by rfl) ⟨86234, by rfl⟩ : syracuseStep 459917 = 172469) B172469
theorem B230593 : Blo 135790 230593 := bstep (se 2 (by rfl) ⟨86472, by rfl⟩ : syracuseStep 230593 = 172945) B172945
theorem B459971 : Blo 135790 459971 := bstep (se 1 (by rfl) ⟨344978, by rfl⟩ : syracuseStep 459971 = 689957) B689957
theorem B230627 : Blo 135790 230627 := bstep (se 1 (by rfl) ⟨172970, by rfl⟩ : syracuseStep 230627 = 345941) B345941
theorem B165187 : Blo 135790 165187 := bstep (se 1 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 165187 = 247781) B247781
theorem B197969 : Blo 135790 197969 := bstep (se 2 (by rfl) ⟨74238, by rfl⟩ : syracuseStep 197969 = 148477) B148477
theorem B230755 : Blo 135790 230755 := bstep (se 1 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 230755 = 346133) B346133
theorem B394595 : Blo 135790 394595 := bstep (se 1 (by rfl) ⟨295946, by rfl⟩ : syracuseStep 394595 = 591893) B591893
theorem B755077 : Blo 135790 755077 := bstep (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) B141577
theorem B263587 : Blo 135790 263587 := bstep (se 1 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 263587 = 395381) B395381
theorem B198083 : Blo 135790 198083 := bstep (se 1 (by rfl) ⟨148562, by rfl⟩ : syracuseStep 198083 = 297125) B297125
theorem B460241 : Blo 135790 460241 := bstep (se 2 (by rfl) ⟨172590, by rfl⟩ : syracuseStep 460241 = 345181) B345181
theorem B230897 : Blo 135790 230897 := bstep (se 2 (by rfl) ⟨86586, by rfl⟩ : syracuseStep 230897 = 173173) B173173
theorem B951821 : Blo 135790 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B198163 : Blo 135790 198163 := bstep (se 1 (by rfl) ⟨148622, by rfl⟩ : syracuseStep 198163 = 297245) B297245
theorem B231025 : Blo 135790 231025 := bstep (se 2 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 231025 = 173269) B173269
theorem B296561 : Blo 135790 296561 := bstep (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) B222421
theorem B231059 : Blo 135790 231059 := bstep (se 1 (by rfl) ⟨173294, by rfl⟩ : syracuseStep 231059 = 346589) B346589
theorem B2262725 : Blo 135790 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B231187 : Blo 135790 231187 := bstep (se 1 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 231187 = 346781) B346781
theorem B264035 : Blo 135790 264035 := bstep (se 1 (by rfl) ⟨198026, by rfl⟩ : syracuseStep 264035 = 396053) B396053
theorem B231329 : Blo 135790 231329 := bstep (se 2 (by rfl) ⟨86748, by rfl⟩ : syracuseStep 231329 = 173497) B173497
theorem B460781 : Blo 135790 460781 := bstep (se 3 (by rfl) ⟨86396, by rfl⟩ : syracuseStep 460781 = 172793) B172793
theorem B591857 : Blo 135790 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B231457 : Blo 135790 231457 := bstep (se 2 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 231457 = 173593) B173593
theorem B460835 : Blo 135790 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B198721 : Blo 135790 198721 := bstep (se 2 (by rfl) ⟨74520, by rfl⟩ : syracuseStep 198721 = 149041) B149041
theorem B231491 : Blo 135790 231491 := bstep (se 1 (by rfl) ⟨173618, by rfl⟩ : syracuseStep 231491 = 347237) B347237
theorem B264323 : Blo 135790 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B395437 : Blo 135790 395437 := bstep (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) B148289
theorem B231619 : Blo 135790 231619 := bstep (se 1 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 231619 = 347429) B347429
theorem B461105 : Blo 135790 461105 := bstep (se 2 (by rfl) ⟨172914, by rfl⟩ : syracuseStep 461105 = 345829) B345829
theorem B166195 : Blo 135790 166195 := bstep (se 1 (by rfl) ⟨124646, by rfl⟩ : syracuseStep 166195 = 249293) B249293
theorem B395597 : Blo 135790 395597 := bstep (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) B148349
theorem B231761 : Blo 135790 231761 := bstep (se 2 (by rfl) ⟨86910, by rfl⟩ : syracuseStep 231761 = 173821) B173821
theorem B526733 : Blo 135790 526733 := bstep (se 3 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 526733 = 197525) B197525
theorem B231889 : Blo 135790 231889 := bstep (se 2 (by rfl) ⟨86958, by rfl⟩ : syracuseStep 231889 = 173917) B173917
theorem B297425 : Blo 135790 297425 := bstep (se 2 (by rfl) ⟨111534, by rfl⟩ : syracuseStep 297425 = 223069) B223069
theorem B231923 : Blo 135790 231923 := bstep (se 1 (by rfl) ⟨173942, by rfl⟩ : syracuseStep 231923 = 347885) B347885
theorem B395779 : Blo 135790 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B232051 : Blo 135790 232051 := bstep (se 1 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 232051 = 348077) B348077
theorem B494221 : Blo 135790 494221 := bstep (se 3 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 494221 = 185333) B185333
theorem B625315 : Blo 135790 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B690929 : Blo 135790 690929 := bstep (se 2 (by rfl) ⟨259098, by rfl⟩ : syracuseStep 690929 = 518197) B518197
theorem B232193 : Blo 135790 232193 := bstep (se 2 (by rfl) ⟨87072, by rfl⟩ : syracuseStep 232193 = 174145) B174145
theorem B887557 : Blo 135790 887557 := bstep (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) B166417
theorem B1084229 : Blo 135790 1084229 := bstep (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) B203293
theorem B461645 : Blo 135790 461645 := bstep (se 3 (by rfl) ⟨86558, by rfl⟩ : syracuseStep 461645 = 173117) B173117
theorem B1641329 : Blo 135790 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B232321 : Blo 135790 232321 := bstep (se 2 (by rfl) ⟨87120, by rfl⟩ : syracuseStep 232321 = 174241) B174241
theorem B461699 : Blo 135790 461699 := bstep (se 1 (by rfl) ⟨346274, by rfl⟩ : syracuseStep 461699 = 692549) B692549
theorem B232355 : Blo 135790 232355 := bstep (se 1 (by rfl) ⟨174266, by rfl⟩ : syracuseStep 232355 = 348533) B348533
theorem B232483 : Blo 135790 232483 := bstep (se 1 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 232483 = 348725) B348725
theorem B265265 : Blo 135790 265265 := bstep (se 2 (by rfl) ⟨99474, by rfl⟩ : syracuseStep 265265 = 198949) B198949
theorem B166979 : Blo 135790 166979 := bstep (se 1 (by rfl) ⟨125234, by rfl⟩ : syracuseStep 166979 = 250469) B250469
theorem B461969 : Blo 135790 461969 := bstep (se 2 (by rfl) ⟨173238, by rfl⟩ : syracuseStep 461969 = 346477) B346477
theorem B232625 : Blo 135790 232625 := bstep (se 2 (by rfl) ⟨87234, by rfl⟩ : syracuseStep 232625 = 174469) B174469
theorem B1969379 : Blo 135790 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B232753 : Blo 135790 232753 := bstep (se 2 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 232753 = 174565) B174565
theorem B232787 : Blo 135790 232787 := bstep (se 1 (by rfl) ⟨174590, by rfl⟩ : syracuseStep 232787 = 349181) B349181
theorem B232915 : Blo 135790 232915 := bstep (se 1 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 232915 = 349373) B349373
theorem B200179 : Blo 135790 200179 := bstep (se 1 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 200179 = 300269) B300269
theorem B233009 : Blo 135790 233009 := bstep (se 2 (by rfl) ⟨87378, by rfl⟩ : syracuseStep 233009 = 174757) B174757
theorem B233057 : Blo 135790 233057 := bstep (se 2 (by rfl) ⟨87396, by rfl⟩ : syracuseStep 233057 = 174793) B174793
theorem B462509 : Blo 135790 462509 := bstep (se 3 (by rfl) ⟨86720, by rfl⟩ : syracuseStep 462509 = 173441) B173441
theorem B233185 : Blo 135790 233185 := bstep (se 2 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 233185 = 174889) B174889
theorem B462563 : Blo 135790 462563 := bstep (se 1 (by rfl) ⟨346922, by rfl⟩ : syracuseStep 462563 = 693845) B693845
theorem B233219 : Blo 135790 233219 := bstep (se 1 (by rfl) ⟨174914, by rfl⟩ : syracuseStep 233219 = 349829) B349829
theorem B397169 : Blo 135790 397169 := bstep (se 2 (by rfl) ⟨148938, by rfl⟩ : syracuseStep 397169 = 297877) B297877
theorem B233347 : Blo 135790 233347 := bstep (se 1 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 233347 = 350021) B350021
theorem B462833 : Blo 135790 462833 := bstep (se 2 (by rfl) ⟨173562, by rfl⟩ : syracuseStep 462833 = 347125) B347125
theorem B233489 : Blo 135790 233489 := bstep (se 2 (by rfl) ⟨87558, by rfl⟩ : syracuseStep 233489 = 175117) B175117
theorem B331793 : Blo 135790 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B233617 : Blo 135790 233617 := bstep (se 2 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 233617 = 175213) B175213
theorem B692387 : Blo 135790 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B233651 : Blo 135790 233651 := bstep (se 1 (by rfl) ⟨175238, by rfl⟩ : syracuseStep 233651 = 350477) B350477
theorem B233779 : Blo 135790 233779 := bstep (se 1 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 233779 = 350669) B350669
theorem B332113 : Blo 135790 332113 := bstep (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) B249085
theorem B594317 : Blo 135790 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B233921 : Blo 135790 233921 := bstep (se 2 (by rfl) ⟨87720, by rfl⟩ : syracuseStep 233921 = 175441) B175441
theorem B463373 : Blo 135790 463373 := bstep (se 3 (by rfl) ⟨86882, by rfl⟩ : syracuseStep 463373 = 173765) B173765
theorem B234049 : Blo 135790 234049 := bstep (se 2 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 234049 = 175537) B175537
theorem B463427 : Blo 135790 463427 := bstep (se 1 (by rfl) ⟨347570, by rfl⟩ : syracuseStep 463427 = 695141) B695141
theorem B234083 : Blo 135790 234083 := bstep (se 1 (by rfl) ⟨175562, by rfl⟩ : syracuseStep 234083 = 351125) B351125
theorem B135795 : Blo 135790 135795 := bstep (se 1 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 135795 = 203693) B203693
theorem B135811 : Blo 135790 135811 := bstep (se 1 (by rfl) ⟨101858, by rfl⟩ : syracuseStep 135811 = 203717) B203717
theorem B135827 : Blo 135790 135827 := bstep (se 1 (by rfl) ⟨101870, by rfl⟩ : syracuseStep 135827 = 203741) B203741
theorem B135843 : Blo 135790 135843 := bstep (se 1 (by rfl) ⟨101882, by rfl⟩ : syracuseStep 135843 = 203765) B203765
theorem B135859 : Blo 135790 135859 := bstep (se 1 (by rfl) ⟨101894, by rfl⟩ : syracuseStep 135859 = 203789) B203789
theorem B135875 : Blo 135790 135875 := bstep (se 1 (by rfl) ⟨101906, by rfl⟩ : syracuseStep 135875 = 203813) B203813
theorem B135891 : Blo 135790 135891 := bstep (se 1 (by rfl) ⟨101918, by rfl⟩ : syracuseStep 135891 = 203837) B203837
theorem B135907 : Blo 135790 135907 := bstep (se 1 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 135907 = 203861) B203861
theorem B234211 : Blo 135790 234211 := bstep (se 1 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 234211 = 351317) B351317
theorem B201457 : Blo 135790 201457 := bstep (se 2 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 201457 = 151093) B151093
theorem B135923 : Blo 135790 135923 := bstep (se 1 (by rfl) ⟨101942, by rfl⟩ : syracuseStep 135923 = 203885) B203885
theorem B135939 : Blo 135790 135939 := bstep (se 1 (by rfl) ⟨101954, by rfl⟩ : syracuseStep 135939 = 203909) B203909
theorem B135955 : Blo 135790 135955 := bstep (se 1 (by rfl) ⟨101966, by rfl⟩ : syracuseStep 135955 = 203933) B203933
theorem B135971 : Blo 135790 135971 := bstep (se 1 (by rfl) ⟨101978, by rfl⟩ : syracuseStep 135971 = 203957) B203957
theorem B135987 : Blo 135790 135987 := bstep (se 1 (by rfl) ⟨101990, by rfl⟩ : syracuseStep 135987 = 203981) B203981
theorem B136003 : Blo 135790 136003 := bstep (se 1 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 136003 = 204005) B204005
theorem B463697 : Blo 135790 463697 := bstep (se 2 (by rfl) ⟨173886, by rfl⟩ : syracuseStep 463697 = 347773) B347773
theorem B136019 : Blo 135790 136019 := bstep (se 1 (by rfl) ⟨102014, by rfl⟩ : syracuseStep 136019 = 204029) B204029
theorem B136035 : Blo 135790 136035 := bstep (se 1 (by rfl) ⟨102026, by rfl⟩ : syracuseStep 136035 = 204053) B204053
theorem B234353 : Blo 135790 234353 := bstep (se 2 (by rfl) ⟨87882, by rfl⟩ : syracuseStep 234353 = 175765) B175765
theorem B136051 : Blo 135790 136051 := bstep (se 1 (by rfl) ⟨102038, by rfl⟩ : syracuseStep 136051 = 204077) B204077
theorem B136067 : Blo 135790 136067 := bstep (se 1 (by rfl) ⟨102050, by rfl⟩ : syracuseStep 136067 = 204101) B204101
theorem B398225 : Blo 135790 398225 := bstep (se 2 (by rfl) ⟨149334, by rfl⟩ : syracuseStep 398225 = 298669) B298669
theorem B136083 : Blo 135790 136083 := bstep (se 1 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 136083 = 204125) B204125
theorem B136099 : Blo 135790 136099 := bstep (se 1 (by rfl) ⟨102074, by rfl⟩ : syracuseStep 136099 = 204149) B204149
theorem B136115 : Blo 135790 136115 := bstep (se 1 (by rfl) ⟨102086, by rfl⟩ : syracuseStep 136115 = 204173) B204173
theorem B136131 : Blo 135790 136131 := bstep (se 1 (by rfl) ⟨102098, by rfl⟩ : syracuseStep 136131 = 204197) B204197
theorem B693197 : Blo 135790 693197 := bstep (se 3 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 693197 = 259949) B259949
theorem B136147 : Blo 135790 136147 := bstep (se 1 (by rfl) ⟨102110, by rfl⟩ : syracuseStep 136147 = 204221) B204221
theorem B136163 : Blo 135790 136163 := bstep (se 1 (by rfl) ⟨102122, by rfl⟩ : syracuseStep 136163 = 204245) B204245
theorem B234481 : Blo 135790 234481 := bstep (se 2 (by rfl) ⟨87930, by rfl⟩ : syracuseStep 234481 = 175861) B175861
theorem B136179 : Blo 135790 136179 := bstep (se 1 (by rfl) ⟨102134, by rfl⟩ : syracuseStep 136179 = 204269) B204269
theorem B136195 : Blo 135790 136195 := bstep (se 1 (by rfl) ⟨102146, by rfl⟩ : syracuseStep 136195 = 204293) B204293
theorem B136211 : Blo 135790 136211 := bstep (se 1 (by rfl) ⟨102158, by rfl⟩ : syracuseStep 136211 = 204317) B204317
theorem B234515 : Blo 135790 234515 := bstep (se 1 (by rfl) ⟨175886, by rfl⟩ : syracuseStep 234515 = 351773) B351773
theorem B136227 : Blo 135790 136227 := bstep (se 1 (by rfl) ⟨102170, by rfl⟩ : syracuseStep 136227 = 204341) B204341
theorem B136243 : Blo 135790 136243 := bstep (se 1 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 136243 = 204365) B204365
theorem B136259 : Blo 135790 136259 := bstep (se 1 (by rfl) ⟨102194, by rfl⟩ : syracuseStep 136259 = 204389) B204389
theorem B136275 : Blo 135790 136275 := bstep (se 1 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 136275 = 204413) B204413
theorem B136291 : Blo 135790 136291 := bstep (se 1 (by rfl) ⟨102218, by rfl⟩ : syracuseStep 136291 = 204437) B204437
theorem B136307 : Blo 135790 136307 := bstep (se 1 (by rfl) ⟨102230, by rfl⟩ : syracuseStep 136307 = 204461) B204461
theorem B136323 : Blo 135790 136323 := bstep (se 1 (by rfl) ⟨102242, by rfl⟩ : syracuseStep 136323 = 204485) B204485
theorem B136339 : Blo 135790 136339 := bstep (se 1 (by rfl) ⟨102254, by rfl⟩ : syracuseStep 136339 = 204509) B204509
theorem B234643 : Blo 135790 234643 := bstep (se 1 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 234643 = 351965) B351965
theorem B136355 : Blo 135790 136355 := bstep (se 1 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 136355 = 204533) B204533
theorem B234659 : Blo 135790 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B136371 : Blo 135790 136371 := bstep (se 1 (by rfl) ⟨102278, by rfl⟩ : syracuseStep 136371 = 204557) B204557
theorem B136387 : Blo 135790 136387 := bstep (se 1 (by rfl) ⟨102290, by rfl⟩ : syracuseStep 136387 = 204581) B204581
theorem B136403 : Blo 135790 136403 := bstep (se 1 (by rfl) ⟨102302, by rfl⟩ : syracuseStep 136403 = 204605) B204605
theorem B136419 : Blo 135790 136419 := bstep (se 1 (by rfl) ⟨102314, by rfl⟩ : syracuseStep 136419 = 204629) B204629
theorem B529649 : Blo 135790 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B136435 : Blo 135790 136435 := bstep (se 1 (by rfl) ⟨102326, by rfl⟩ : syracuseStep 136435 = 204653) B204653
theorem B136451 : Blo 135790 136451 := bstep (se 1 (by rfl) ⟨102338, by rfl⟩ : syracuseStep 136451 = 204677) B204677
theorem B136467 : Blo 135790 136467 := bstep (se 1 (by rfl) ⟨102350, by rfl⟩ : syracuseStep 136467 = 204701) B204701
theorem B234785 : Blo 135790 234785 := bstep (se 2 (by rfl) ⟨88044, by rfl⟩ : syracuseStep 234785 = 176089) B176089
theorem B136483 : Blo 135790 136483 := bstep (se 1 (by rfl) ⟨102362, by rfl⟩ : syracuseStep 136483 = 204725) B204725
theorem B496945 : Blo 135790 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B136499 : Blo 135790 136499 := bstep (se 1 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 136499 = 204749) B204749
theorem B136515 : Blo 135790 136515 := bstep (se 1 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 136515 = 204773) B204773
theorem B136531 : Blo 135790 136531 := bstep (se 1 (by rfl) ⟨102398, by rfl⟩ : syracuseStep 136531 = 204797) B204797
theorem B136547 : Blo 135790 136547 := bstep (se 1 (by rfl) ⟨102410, by rfl⟩ : syracuseStep 136547 = 204821) B204821
theorem B464237 : Blo 135790 464237 := bstep (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) B174089
theorem B136563 : Blo 135790 136563 := bstep (se 1 (by rfl) ⟨102422, by rfl⟩ : syracuseStep 136563 = 204845) B204845
theorem B136579 : Blo 135790 136579 := bstep (se 1 (by rfl) ⟨102434, by rfl⟩ : syracuseStep 136579 = 204869) B204869
theorem B136595 : Blo 135790 136595 := bstep (se 1 (by rfl) ⟨102446, by rfl⟩ : syracuseStep 136595 = 204893) B204893
theorem B234913 : Blo 135790 234913 := bstep (se 2 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 234913 = 176185) B176185
theorem B136611 : Blo 135790 136611 := bstep (se 1 (by rfl) ⟨102458, by rfl⟩ : syracuseStep 136611 = 204917) B204917
theorem B464291 : Blo 135790 464291 := bstep (se 1 (by rfl) ⟨348218, by rfl⟩ : syracuseStep 464291 = 696437) B696437
theorem B136627 : Blo 135790 136627 := bstep (se 1 (by rfl) ⟨102470, by rfl⟩ : syracuseStep 136627 = 204941) B204941
theorem B136643 : Blo 135790 136643 := bstep (se 1 (by rfl) ⟨102482, by rfl⟩ : syracuseStep 136643 = 204965) B204965
theorem B234947 : Blo 135790 234947 := bstep (se 1 (by rfl) ⟨176210, by rfl⟩ : syracuseStep 234947 = 352421) B352421
theorem B136659 : Blo 135790 136659 := bstep (se 1 (by rfl) ⟨102494, by rfl⟩ : syracuseStep 136659 = 204989) B204989
theorem B136675 : Blo 135790 136675 := bstep (se 1 (by rfl) ⟨102506, by rfl⟩ : syracuseStep 136675 = 205013) B205013
theorem B136691 : Blo 135790 136691 := bstep (se 1 (by rfl) ⟨102518, by rfl⟩ : syracuseStep 136691 = 205037) B205037
theorem B136707 : Blo 135790 136707 := bstep (se 1 (by rfl) ⟨102530, by rfl⟩ : syracuseStep 136707 = 205061) B205061
theorem B136723 : Blo 135790 136723 := bstep (se 1 (by rfl) ⟨102542, by rfl⟩ : syracuseStep 136723 = 205085) B205085
theorem B136739 : Blo 135790 136739 := bstep (se 1 (by rfl) ⟨102554, by rfl⟩ : syracuseStep 136739 = 205109) B205109
theorem B136755 : Blo 135790 136755 := bstep (se 1 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 136755 = 205133) B205133
theorem B136771 : Blo 135790 136771 := bstep (se 1 (by rfl) ⟨102578, by rfl⟩ : syracuseStep 136771 = 205157) B205157
theorem B235075 : Blo 135790 235075 := bstep (se 1 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 235075 = 352613) B352613
theorem B136787 : Blo 135790 136787 := bstep (se 1 (by rfl) ⟨102590, by rfl⟩ : syracuseStep 136787 = 205181) B205181
theorem B136803 : Blo 135790 136803 := bstep (se 1 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 136803 = 205205) B205205
theorem B136819 : Blo 135790 136819 := bstep (se 1 (by rfl) ⟨102614, by rfl⟩ : syracuseStep 136819 = 205229) B205229
theorem B136835 : Blo 135790 136835 := bstep (se 1 (by rfl) ⟨102626, by rfl⟩ : syracuseStep 136835 = 205253) B205253
theorem B136851 : Blo 135790 136851 := bstep (se 1 (by rfl) ⟨102638, by rfl⟩ : syracuseStep 136851 = 205277) B205277
theorem B136867 : Blo 135790 136867 := bstep (se 1 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 136867 = 205301) B205301
theorem B464561 : Blo 135790 464561 := bstep (se 2 (by rfl) ⟨174210, by rfl⟩ : syracuseStep 464561 = 348421) B348421
theorem B136883 : Blo 135790 136883 := bstep (se 1 (by rfl) ⟨102662, by rfl⟩ : syracuseStep 136883 = 205325) B205325
theorem B136899 : Blo 135790 136899 := bstep (se 1 (by rfl) ⟨102674, by rfl⟩ : syracuseStep 136899 = 205349) B205349
theorem B235217 : Blo 135790 235217 := bstep (se 2 (by rfl) ⟨88206, by rfl⟩ : syracuseStep 235217 = 176413) B176413
theorem B136915 : Blo 135790 136915 := bstep (se 1 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 136915 = 205373) B205373
theorem B136931 : Blo 135790 136931 := bstep (se 1 (by rfl) ⟨102698, by rfl⟩ : syracuseStep 136931 = 205397) B205397
theorem B136947 : Blo 135790 136947 := bstep (se 1 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 136947 = 205421) B205421
theorem B136963 : Blo 135790 136963 := bstep (se 1 (by rfl) ⟨102722, by rfl⟩ : syracuseStep 136963 = 205445) B205445
theorem B136979 : Blo 135790 136979 := bstep (se 1 (by rfl) ⟨102734, by rfl⟩ : syracuseStep 136979 = 205469) B205469
theorem B136995 : Blo 135790 136995 := bstep (se 1 (by rfl) ⟨102746, by rfl⟩ : syracuseStep 136995 = 205493) B205493
theorem B137011 : Blo 135790 137011 := bstep (se 1 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 137011 = 205517) B205517
theorem B137027 : Blo 135790 137027 := bstep (se 1 (by rfl) ⟨102770, by rfl⟩ : syracuseStep 137027 = 205541) B205541
theorem B464717 : Blo 135790 464717 := bstep (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) B174269
theorem B235345 : Blo 135790 235345 := bstep (se 2 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 235345 = 176509) B176509
theorem B137043 : Blo 135790 137043 := bstep (se 1 (by rfl) ⟨102782, by rfl⟩ : syracuseStep 137043 = 205565) B205565
theorem B137059 : Blo 135790 137059 := bstep (se 1 (by rfl) ⟨102794, by rfl⟩ : syracuseStep 137059 = 205589) B205589
theorem B137075 : Blo 135790 137075 := bstep (se 1 (by rfl) ⟨102806, by rfl⟩ : syracuseStep 137075 = 205613) B205613
theorem B235379 : Blo 135790 235379 := bstep (se 1 (by rfl) ⟨176534, by rfl⟩ : syracuseStep 235379 = 353069) B353069
theorem B137091 : Blo 135790 137091 := bstep (se 1 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 137091 = 205637) B205637
theorem B137107 : Blo 135790 137107 := bstep (se 1 (by rfl) ⟨102830, by rfl⟩ : syracuseStep 137107 = 205661) B205661
theorem B137123 : Blo 135790 137123 := bstep (se 1 (by rfl) ⟨102842, by rfl⟩ : syracuseStep 137123 = 205685) B205685
theorem B137139 : Blo 135790 137139 := bstep (se 1 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 137139 = 205709) B205709
theorem B137155 : Blo 135790 137155 := bstep (se 1 (by rfl) ⟨102866, by rfl⟩ : syracuseStep 137155 = 205733) B205733
theorem B137171 : Blo 135790 137171 := bstep (se 1 (by rfl) ⟨102878, by rfl⟩ : syracuseStep 137171 = 205757) B205757
theorem B137187 : Blo 135790 137187 := bstep (se 1 (by rfl) ⟨102890, by rfl⟩ : syracuseStep 137187 = 205781) B205781
theorem B137203 : Blo 135790 137203 := bstep (se 1 (by rfl) ⟨102902, by rfl⟩ : syracuseStep 137203 = 205805) B205805
theorem B235507 : Blo 135790 235507 := bstep (se 1 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 235507 = 353261) B353261
theorem B137219 : Blo 135790 137219 := bstep (se 1 (by rfl) ⟨102914, by rfl⟩ : syracuseStep 137219 = 205829) B205829
theorem B137235 : Blo 135790 137235 := bstep (se 1 (by rfl) ⟨102926, by rfl⟩ : syracuseStep 137235 = 205853) B205853
theorem B137251 : Blo 135790 137251 := bstep (se 1 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 137251 = 205877) B205877
theorem B137267 : Blo 135790 137267 := bstep (se 1 (by rfl) ⟨102950, by rfl⟩ : syracuseStep 137267 = 205901) B205901
theorem B137283 : Blo 135790 137283 := bstep (se 1 (by rfl) ⟨102962, by rfl⟩ : syracuseStep 137283 = 205925) B205925
theorem B137299 : Blo 135790 137299 := bstep (se 1 (by rfl) ⟨102974, by rfl⟩ : syracuseStep 137299 = 205949) B205949
theorem B137315 : Blo 135790 137315 := bstep (se 1 (by rfl) ⟨102986, by rfl⟩ : syracuseStep 137315 = 205973) B205973
theorem B137331 : Blo 135790 137331 := bstep (se 1 (by rfl) ⟨102998, by rfl⟩ : syracuseStep 137331 = 205997) B205997
theorem B235649 : Blo 135790 235649 := bstep (se 2 (by rfl) ⟨88368, by rfl⟩ : syracuseStep 235649 = 176737) B176737
theorem B137347 : Blo 135790 137347 := bstep (se 1 (by rfl) ⟨103010, by rfl⟩ : syracuseStep 137347 = 206021) B206021
theorem B2398349 : Blo 135790 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B137363 : Blo 135790 137363 := bstep (se 1 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 137363 = 206045) B206045
theorem B137379 : Blo 135790 137379 := bstep (se 1 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 137379 = 206069) B206069
theorem B137395 : Blo 135790 137395 := bstep (se 1 (by rfl) ⟨103046, by rfl⟩ : syracuseStep 137395 = 206093) B206093
theorem B137411 : Blo 135790 137411 := bstep (se 1 (by rfl) ⟨103058, by rfl⟩ : syracuseStep 137411 = 206117) B206117
theorem B465101 : Blo 135790 465101 := bstep (se 3 (by rfl) ⟨87206, by rfl⟩ : syracuseStep 465101 = 174413) B174413
theorem B137427 : Blo 135790 137427 := bstep (se 1 (by rfl) ⟨103070, by rfl⟩ : syracuseStep 137427 = 206141) B206141
theorem B137443 : Blo 135790 137443 := bstep (se 1 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 137443 = 206165) B206165
theorem B399587 : Blo 135790 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B137459 : Blo 135790 137459 := bstep (se 1 (by rfl) ⟨103094, by rfl⟩ : syracuseStep 137459 = 206189) B206189
theorem B235777 : Blo 135790 235777 := bstep (se 2 (by rfl) ⟨88416, by rfl⟩ : syracuseStep 235777 = 176833) B176833
theorem B137475 : Blo 135790 137475 := bstep (se 1 (by rfl) ⟨103106, by rfl⟩ : syracuseStep 137475 = 206213) B206213
theorem B465155 : Blo 135790 465155 := bstep (se 1 (by rfl) ⟨348866, by rfl⟩ : syracuseStep 465155 = 697733) B697733
theorem B137491 : Blo 135790 137491 := bstep (se 1 (by rfl) ⟨103118, by rfl⟩ : syracuseStep 137491 = 206237) B206237
theorem B137507 : Blo 135790 137507 := bstep (se 1 (by rfl) ⟨103130, by rfl⟩ : syracuseStep 137507 = 206261) B206261
theorem B235811 : Blo 135790 235811 := bstep (se 1 (by rfl) ⟨176858, by rfl⟩ : syracuseStep 235811 = 353717) B353717
theorem B137523 : Blo 135790 137523 := bstep (se 1 (by rfl) ⟨103142, by rfl⟩ : syracuseStep 137523 = 206285) B206285
theorem B137539 : Blo 135790 137539 := bstep (se 1 (by rfl) ⟨103154, by rfl⟩ : syracuseStep 137539 = 206309) B206309
theorem B137555 : Blo 135790 137555 := bstep (se 1 (by rfl) ⟨103166, by rfl⟩ : syracuseStep 137555 = 206333) B206333
theorem B137571 : Blo 135790 137571 := bstep (se 1 (by rfl) ⟨103178, by rfl⟩ : syracuseStep 137571 = 206357) B206357
theorem B137587 : Blo 135790 137587 := bstep (se 1 (by rfl) ⟨103190, by rfl⟩ : syracuseStep 137587 = 206381) B206381
theorem B137603 : Blo 135790 137603 := bstep (se 1 (by rfl) ⟨103202, by rfl⟩ : syracuseStep 137603 = 206405) B206405
theorem B137619 : Blo 135790 137619 := bstep (se 1 (by rfl) ⟨103214, by rfl⟩ : syracuseStep 137619 = 206429) B206429
theorem B137635 : Blo 135790 137635 := bstep (se 1 (by rfl) ⟨103226, by rfl⟩ : syracuseStep 137635 = 206453) B206453
theorem B137651 : Blo 135790 137651 := bstep (se 1 (by rfl) ⟨103238, by rfl⟩ : syracuseStep 137651 = 206477) B206477
theorem B137667 : Blo 135790 137667 := bstep (se 1 (by rfl) ⟨103250, by rfl⟩ : syracuseStep 137667 = 206501) B206501
theorem B137683 : Blo 135790 137683 := bstep (se 1 (by rfl) ⟨103262, by rfl⟩ : syracuseStep 137683 = 206525) B206525
theorem B137699 : Blo 135790 137699 := bstep (se 1 (by rfl) ⟨103274, by rfl⟩ : syracuseStep 137699 = 206549) B206549
theorem B137715 : Blo 135790 137715 := bstep (se 1 (by rfl) ⟨103286, by rfl⟩ : syracuseStep 137715 = 206573) B206573
theorem B137731 : Blo 135790 137731 := bstep (se 1 (by rfl) ⟨103298, by rfl⟩ : syracuseStep 137731 = 206597) B206597
theorem B465425 : Blo 135790 465425 := bstep (se 2 (by rfl) ⟨174534, by rfl⟩ : syracuseStep 465425 = 349069) B349069
theorem B137747 : Blo 135790 137747 := bstep (se 1 (by rfl) ⟨103310, by rfl⟩ : syracuseStep 137747 = 206621) B206621
theorem B137763 : Blo 135790 137763 := bstep (se 1 (by rfl) ⟨103322, by rfl⟩ : syracuseStep 137763 = 206645) B206645
theorem B236081 : Blo 135790 236081 := bstep (se 2 (by rfl) ⟨88530, by rfl⟩ : syracuseStep 236081 = 177061) B177061
theorem B137779 : Blo 135790 137779 := bstep (se 1 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 137779 = 206669) B206669
theorem B137795 : Blo 135790 137795 := bstep (se 1 (by rfl) ⟨103346, by rfl⟩ : syracuseStep 137795 = 206693) B206693
theorem B137811 : Blo 135790 137811 := bstep (se 1 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 137811 = 206717) B206717
theorem B137827 : Blo 135790 137827 := bstep (se 1 (by rfl) ⟨103370, by rfl⟩ : syracuseStep 137827 = 206741) B206741
theorem B137843 : Blo 135790 137843 := bstep (se 1 (by rfl) ⟨103382, by rfl⟩ : syracuseStep 137843 = 206765) B206765
theorem B137859 : Blo 135790 137859 := bstep (se 1 (by rfl) ⟨103394, by rfl⟩ : syracuseStep 137859 = 206789) B206789
theorem B137875 : Blo 135790 137875 := bstep (se 1 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 137875 = 206813) B206813
theorem B137891 : Blo 135790 137891 := bstep (se 1 (by rfl) ⟨103418, by rfl⟩ : syracuseStep 137891 = 206837) B206837
theorem B137907 : Blo 135790 137907 := bstep (se 1 (by rfl) ⟨103430, by rfl⟩ : syracuseStep 137907 = 206861) B206861
theorem B137923 : Blo 135790 137923 := bstep (se 1 (by rfl) ⟨103442, by rfl⟩ : syracuseStep 137923 = 206885) B206885
theorem B137939 : Blo 135790 137939 := bstep (se 1 (by rfl) ⟨103454, by rfl⟩ : syracuseStep 137939 = 206909) B206909
theorem B137955 : Blo 135790 137955 := bstep (se 1 (by rfl) ⟨103466, by rfl⟩ : syracuseStep 137955 = 206933) B206933
theorem B137971 : Blo 135790 137971 := bstep (se 1 (by rfl) ⟨103478, by rfl⟩ : syracuseStep 137971 = 206957) B206957
theorem B137987 : Blo 135790 137987 := bstep (se 1 (by rfl) ⟨103490, by rfl⟩ : syracuseStep 137987 = 206981) B206981
theorem B138003 : Blo 135790 138003 := bstep (se 1 (by rfl) ⟨103502, by rfl⟩ : syracuseStep 138003 = 207005) B207005
theorem B138019 : Blo 135790 138019 := bstep (se 1 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 138019 = 207029) B207029
theorem B138035 : Blo 135790 138035 := bstep (se 1 (by rfl) ⟨103526, by rfl⟩ : syracuseStep 138035 = 207053) B207053
theorem B269123 : Blo 135790 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B138051 : Blo 135790 138051 := bstep (se 1 (by rfl) ⟨103538, by rfl⟩ : syracuseStep 138051 = 207077) B207077
theorem B138067 : Blo 135790 138067 := bstep (se 1 (by rfl) ⟨103550, by rfl⟩ : syracuseStep 138067 = 207101) B207101
theorem B138083 : Blo 135790 138083 := bstep (se 1 (by rfl) ⟨103562, by rfl⟩ : syracuseStep 138083 = 207125) B207125
theorem B138099 : Blo 135790 138099 := bstep (se 1 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 138099 = 207149) B207149
theorem B138115 : Blo 135790 138115 := bstep (se 1 (by rfl) ⟨103586, by rfl⟩ : syracuseStep 138115 = 207173) B207173
theorem B138131 : Blo 135790 138131 := bstep (se 1 (by rfl) ⟨103598, by rfl⟩ : syracuseStep 138131 = 207197) B207197
theorem B138147 : Blo 135790 138147 := bstep (se 1 (by rfl) ⟨103610, by rfl⟩ : syracuseStep 138147 = 207221) B207221
theorem B203699 : Blo 135790 203699 := bstep (se 1 (by rfl) ⟨152774, by rfl⟩ : syracuseStep 203699 = 305549) B305549
theorem B138163 : Blo 135790 138163 := bstep (se 1 (by rfl) ⟨103622, by rfl⟩ : syracuseStep 138163 = 207245) B207245
theorem B138179 : Blo 135790 138179 := bstep (se 1 (by rfl) ⟨103634, by rfl⟩ : syracuseStep 138179 = 207269) B207269
theorem B203729 : Blo 135790 203729 := bstep (se 2 (by rfl) ⟨76398, by rfl⟩ : syracuseStep 203729 = 152797) B152797
theorem B138195 : Blo 135790 138195 := bstep (se 1 (by rfl) ⟨103646, by rfl⟩ : syracuseStep 138195 = 207293) B207293
theorem B236513 : Blo 135790 236513 := bstep (se 2 (by rfl) ⟨88692, by rfl⟩ : syracuseStep 236513 = 177385) B177385
theorem B203747 : Blo 135790 203747 := bstep (se 1 (by rfl) ⟨152810, by rfl⟩ : syracuseStep 203747 = 305621) B305621
theorem B138211 : Blo 135790 138211 := bstep (se 1 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 138211 = 207317) B207317
theorem B138227 : Blo 135790 138227 := bstep (se 1 (by rfl) ⟨103670, by rfl⟩ : syracuseStep 138227 = 207341) B207341
theorem B203777 : Blo 135790 203777 := bstep (se 2 (by rfl) ⟨76416, by rfl⟩ : syracuseStep 203777 = 152833) B152833
theorem B138243 : Blo 135790 138243 := bstep (se 1 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 138243 = 207365) B207365
theorem B203779 : Blo 135790 203779 := bstep (se 1 (by rfl) ⟨152834, by rfl⟩ : syracuseStep 203779 = 305669) B305669
theorem B203795 : Blo 135790 203795 := bstep (se 1 (by rfl) ⟨152846, by rfl⟩ : syracuseStep 203795 = 305693) B305693
theorem B138259 : Blo 135790 138259 := bstep (se 1 (by rfl) ⟨103694, by rfl⟩ : syracuseStep 138259 = 207389) B207389
theorem B138275 : Blo 135790 138275 := bstep (se 1 (by rfl) ⟨103706, by rfl⟩ : syracuseStep 138275 = 207413) B207413
theorem B465965 : Blo 135790 465965 := bstep (se 3 (by rfl) ⟨87368, by rfl⟩ : syracuseStep 465965 = 174737) B174737
theorem B203825 : Blo 135790 203825 := bstep (se 2 (by rfl) ⟨76434, by rfl⟩ : syracuseStep 203825 = 152869) B152869
theorem B138291 : Blo 135790 138291 := bstep (se 1 (by rfl) ⟨103718, by rfl⟩ : syracuseStep 138291 = 207437) B207437
theorem B203843 : Blo 135790 203843 := bstep (se 1 (by rfl) ⟨152882, by rfl⟩ : syracuseStep 203843 = 305765) B305765
theorem B138307 : Blo 135790 138307 := bstep (se 1 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 138307 = 207461) B207461
theorem B400465 : Blo 135790 400465 := bstep (se 2 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 400465 = 300349) B300349
theorem B138323 : Blo 135790 138323 := bstep (se 1 (by rfl) ⟨103742, by rfl⟩ : syracuseStep 138323 = 207485) B207485
theorem B203873 : Blo 135790 203873 := bstep (se 2 (by rfl) ⟨76452, by rfl⟩ : syracuseStep 203873 = 152905) B152905
theorem B466019 : Blo 135790 466019 := bstep (se 1 (by rfl) ⟨349514, by rfl⟩ : syracuseStep 466019 = 699029) B699029
theorem B138339 : Blo 135790 138339 := bstep (se 1 (by rfl) ⟨103754, by rfl⟩ : syracuseStep 138339 = 207509) B207509
theorem B203891 : Blo 135790 203891 := bstep (se 1 (by rfl) ⟨152918, by rfl⟩ : syracuseStep 203891 = 305837) B305837
theorem B138355 : Blo 135790 138355 := bstep (se 1 (by rfl) ⟨103766, by rfl⟩ : syracuseStep 138355 = 207533) B207533
theorem B138371 : Blo 135790 138371 := bstep (se 1 (by rfl) ⟨103778, by rfl⟩ : syracuseStep 138371 = 207557) B207557
theorem B203921 : Blo 135790 203921 := bstep (se 2 (by rfl) ⟨76470, by rfl⟩ : syracuseStep 203921 = 152941) B152941
theorem B138387 : Blo 135790 138387 := bstep (se 1 (by rfl) ⟨103790, by rfl⟩ : syracuseStep 138387 = 207581) B207581
theorem B203939 : Blo 135790 203939 := bstep (se 1 (by rfl) ⟨152954, by rfl⟩ : syracuseStep 203939 = 305909) B305909
theorem B138403 : Blo 135790 138403 := bstep (se 1 (by rfl) ⟨103802, by rfl⟩ : syracuseStep 138403 = 207605) B207605
theorem B138419 : Blo 135790 138419 := bstep (se 1 (by rfl) ⟨103814, by rfl⟩ : syracuseStep 138419 = 207629) B207629
theorem B203969 : Blo 135790 203969 := bstep (se 2 (by rfl) ⟨76488, by rfl⟩ : syracuseStep 203969 = 152977) B152977
theorem B138435 : Blo 135790 138435 := bstep (se 1 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 138435 = 207653) B207653
theorem B203987 : Blo 135790 203987 := bstep (se 1 (by rfl) ⟨152990, by rfl⟩ : syracuseStep 203987 = 305981) B305981
theorem B138451 : Blo 135790 138451 := bstep (se 1 (by rfl) ⟨103838, by rfl⟩ : syracuseStep 138451 = 207677) B207677
theorem B138467 : Blo 135790 138467 := bstep (se 1 (by rfl) ⟨103850, by rfl⟩ : syracuseStep 138467 = 207701) B207701
theorem B204017 : Blo 135790 204017 := bstep (se 2 (by rfl) ⟨76506, by rfl⟩ : syracuseStep 204017 = 153013) B153013
theorem B138483 : Blo 135790 138483 := bstep (se 1 (by rfl) ⟨103862, by rfl⟩ : syracuseStep 138483 = 207725) B207725
theorem B204035 : Blo 135790 204035 := bstep (se 1 (by rfl) ⟨153026, by rfl⟩ : syracuseStep 204035 = 306053) B306053
theorem B138499 : Blo 135790 138499 := bstep (se 1 (by rfl) ⟨103874, by rfl⟩ : syracuseStep 138499 = 207749) B207749
theorem B138515 : Blo 135790 138515 := bstep (se 1 (by rfl) ⟨103886, by rfl⟩ : syracuseStep 138515 = 207773) B207773
theorem B204065 : Blo 135790 204065 := bstep (se 2 (by rfl) ⟨76524, by rfl⟩ : syracuseStep 204065 = 153049) B153049
theorem B138531 : Blo 135790 138531 := bstep (se 1 (by rfl) ⟨103898, by rfl⟩ : syracuseStep 138531 = 207797) B207797
theorem B204083 : Blo 135790 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B138547 : Blo 135790 138547 := bstep (se 1 (by rfl) ⟨103910, by rfl⟩ : syracuseStep 138547 = 207821) B207821
theorem B138563 : Blo 135790 138563 := bstep (se 1 (by rfl) ⟨103922, by rfl⟩ : syracuseStep 138563 = 207845) B207845
theorem B204113 : Blo 135790 204113 := bstep (se 2 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 204113 = 153085) B153085
theorem B138579 : Blo 135790 138579 := bstep (se 1 (by rfl) ⟨103934, by rfl⟩ : syracuseStep 138579 = 207869) B207869
theorem B204131 : Blo 135790 204131 := bstep (se 1 (by rfl) ⟨153098, by rfl⟩ : syracuseStep 204131 = 306197) B306197
theorem B138595 : Blo 135790 138595 := bstep (se 1 (by rfl) ⟨103946, by rfl⟩ : syracuseStep 138595 = 207893) B207893
theorem B466289 : Blo 135790 466289 := bstep (se 2 (by rfl) ⟨174858, by rfl⟩ : syracuseStep 466289 = 349717) B349717
theorem B138611 : Blo 135790 138611 := bstep (se 1 (by rfl) ⟨103958, by rfl⟩ : syracuseStep 138611 = 207917) B207917
theorem B204161 : Blo 135790 204161 := bstep (se 2 (by rfl) ⟨76560, by rfl⟩ : syracuseStep 204161 = 153121) B153121
theorem B138627 : Blo 135790 138627 := bstep (se 1 (by rfl) ⟨103970, by rfl⟩ : syracuseStep 138627 = 207941) B207941
theorem B204179 : Blo 135790 204179 := bstep (se 1 (by rfl) ⟨153134, by rfl⟩ : syracuseStep 204179 = 306269) B306269
theorem B138643 : Blo 135790 138643 := bstep (se 1 (by rfl) ⟨103982, by rfl⟩ : syracuseStep 138643 = 207965) B207965
theorem B138659 : Blo 135790 138659 := bstep (se 1 (by rfl) ⟨103994, by rfl⟩ : syracuseStep 138659 = 207989) B207989
theorem B204209 : Blo 135790 204209 := bstep (se 2 (by rfl) ⟨76578, by rfl⟩ : syracuseStep 204209 = 153157) B153157
theorem B138675 : Blo 135790 138675 := bstep (se 1 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 138675 = 208013) B208013
theorem B204227 : Blo 135790 204227 := bstep (se 1 (by rfl) ⟨153170, by rfl⟩ : syracuseStep 204227 = 306341) B306341
theorem B138691 : Blo 135790 138691 := bstep (se 1 (by rfl) ⟨104018, by rfl⟩ : syracuseStep 138691 = 208037) B208037
theorem B138707 : Blo 135790 138707 := bstep (se 1 (by rfl) ⟨104030, by rfl⟩ : syracuseStep 138707 = 208061) B208061
theorem B204257 : Blo 135790 204257 := bstep (se 2 (by rfl) ⟨76596, by rfl⟩ : syracuseStep 204257 = 153193) B153193
theorem B138723 : Blo 135790 138723 := bstep (se 1 (by rfl) ⟨104042, by rfl⟩ : syracuseStep 138723 = 208085) B208085
theorem B204275 : Blo 135790 204275 := bstep (se 1 (by rfl) ⟨153206, by rfl⟩ : syracuseStep 204275 = 306413) B306413
theorem B138739 : Blo 135790 138739 := bstep (se 1 (by rfl) ⟨104054, by rfl⟩ : syracuseStep 138739 = 208109) B208109
theorem B138755 : Blo 135790 138755 := bstep (se 1 (by rfl) ⟨104066, by rfl⟩ : syracuseStep 138755 = 208133) B208133
theorem B204305 : Blo 135790 204305 := bstep (se 2 (by rfl) ⟨76614, by rfl⟩ : syracuseStep 204305 = 153229) B153229
theorem B138771 : Blo 135790 138771 := bstep (se 1 (by rfl) ⟨104078, by rfl⟩ : syracuseStep 138771 = 208157) B208157
theorem B204323 : Blo 135790 204323 := bstep (se 1 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 204323 = 306485) B306485
theorem B138787 : Blo 135790 138787 := bstep (se 1 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 138787 = 208181) B208181
theorem B138803 : Blo 135790 138803 := bstep (se 1 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 138803 = 208205) B208205
theorem B204353 : Blo 135790 204353 := bstep (se 2 (by rfl) ⟨76632, by rfl⟩ : syracuseStep 204353 = 153265) B153265
theorem B466499 : Blo 135790 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B138819 : Blo 135790 138819 := bstep (se 1 (by rfl) ⟨104114, by rfl⟩ : syracuseStep 138819 = 208229) B208229
theorem B204371 : Blo 135790 204371 := bstep (se 1 (by rfl) ⟨153278, by rfl⟩ : syracuseStep 204371 = 306557) B306557
theorem B138835 : Blo 135790 138835 := bstep (se 1 (by rfl) ⟨104126, by rfl⟩ : syracuseStep 138835 = 208253) B208253
theorem B138851 : Blo 135790 138851 := bstep (se 1 (by rfl) ⟨104138, by rfl⟩ : syracuseStep 138851 = 208277) B208277
theorem B204401 : Blo 135790 204401 := bstep (se 2 (by rfl) ⟨76650, by rfl⟩ : syracuseStep 204401 = 153301) B153301
theorem B138867 : Blo 135790 138867 := bstep (se 1 (by rfl) ⟨104150, by rfl⟩ : syracuseStep 138867 = 208301) B208301
theorem B204419 : Blo 135790 204419 := bstep (se 1 (by rfl) ⟨153314, by rfl⟩ : syracuseStep 204419 = 306629) B306629
theorem B138883 : Blo 135790 138883 := bstep (se 1 (by rfl) ⟨104162, by rfl⟩ : syracuseStep 138883 = 208325) B208325
theorem B794245 : Blo 135790 794245 := bstep (se 4 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 794245 = 148921) B148921
theorem B138899 : Blo 135790 138899 := bstep (se 1 (by rfl) ⟨104174, by rfl⟩ : syracuseStep 138899 = 208349) B208349
theorem B204449 : Blo 135790 204449 := bstep (se 2 (by rfl) ⟨76668, by rfl⟩ : syracuseStep 204449 = 153337) B153337
theorem B138915 : Blo 135790 138915 := bstep (se 1 (by rfl) ⟨104186, by rfl⟩ : syracuseStep 138915 = 208373) B208373
theorem B138931 : Blo 135790 138931 := bstep (se 1 (by rfl) ⟨104198, by rfl⟩ : syracuseStep 138931 = 208397) B208397
theorem B204467 : Blo 135790 204467 := bstep (se 1 (by rfl) ⟨153350, by rfl⟩ : syracuseStep 204467 = 306701) B306701
theorem B138947 : Blo 135790 138947 := bstep (se 1 (by rfl) ⟨104210, by rfl⟩ : syracuseStep 138947 = 208421) B208421
theorem B990917 : Blo 135790 990917 := bstep (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) B185797
theorem B204497 : Blo 135790 204497 := bstep (se 2 (by rfl) ⟨76686, by rfl⟩ : syracuseStep 204497 = 153373) B153373
theorem B138963 : Blo 135790 138963 := bstep (se 1 (by rfl) ⟨104222, by rfl⟩ : syracuseStep 138963 = 208445) B208445
theorem B204515 : Blo 135790 204515 := bstep (se 1 (by rfl) ⟨153386, by rfl⟩ : syracuseStep 204515 = 306773) B306773
theorem B138979 : Blo 135790 138979 := bstep (se 1 (by rfl) ⟨104234, by rfl⟩ : syracuseStep 138979 = 208469) B208469
theorem B138995 : Blo 135790 138995 := bstep (se 1 (by rfl) ⟨104246, by rfl⟩ : syracuseStep 138995 = 208493) B208493
theorem B204545 : Blo 135790 204545 := bstep (se 2 (by rfl) ⟨76704, by rfl⟩ : syracuseStep 204545 = 153409) B153409
theorem B139011 : Blo 135790 139011 := bstep (se 1 (by rfl) ⟨104258, by rfl⟩ : syracuseStep 139011 = 208517) B208517
theorem B204563 : Blo 135790 204563 := bstep (se 1 (by rfl) ⟨153422, by rfl⟩ : syracuseStep 204563 = 306845) B306845
theorem B139027 : Blo 135790 139027 := bstep (se 1 (by rfl) ⟨104270, by rfl⟩ : syracuseStep 139027 = 208541) B208541
theorem B139043 : Blo 135790 139043 := bstep (se 1 (by rfl) ⟨104282, by rfl⟩ : syracuseStep 139043 = 208565) B208565
theorem B204593 : Blo 135790 204593 := bstep (se 2 (by rfl) ⟨76722, by rfl⟩ : syracuseStep 204593 = 153445) B153445
theorem B696113 : Blo 135790 696113 := bstep (se 2 (by rfl) ⟨261042, by rfl⟩ : syracuseStep 696113 = 522085) B522085
theorem B139059 : Blo 135790 139059 := bstep (se 1 (by rfl) ⟨104294, by rfl⟩ : syracuseStep 139059 = 208589) B208589
theorem B204611 : Blo 135790 204611 := bstep (se 1 (by rfl) ⟨153458, by rfl⟩ : syracuseStep 204611 = 306917) B306917
theorem B139075 : Blo 135790 139075 := bstep (se 1 (by rfl) ⟨104306, by rfl⟩ : syracuseStep 139075 = 208613) B208613
theorem B139091 : Blo 135790 139091 := bstep (se 1 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 139091 = 208637) B208637
theorem B204641 : Blo 135790 204641 := bstep (se 2 (by rfl) ⟨76740, by rfl⟩ : syracuseStep 204641 = 153481) B153481
theorem B139107 : Blo 135790 139107 := bstep (se 1 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 139107 = 208661) B208661
theorem B204659 : Blo 135790 204659 := bstep (se 1 (by rfl) ⟨153494, by rfl⟩ : syracuseStep 204659 = 306989) B306989
theorem B139123 : Blo 135790 139123 := bstep (se 1 (by rfl) ⟨104342, by rfl⟩ : syracuseStep 139123 = 208685) B208685
theorem B139139 : Blo 135790 139139 := bstep (se 1 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 139139 = 208709) B208709
theorem B466829 : Blo 135790 466829 := bstep (se 3 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 466829 = 175061) B175061
theorem B204689 : Blo 135790 204689 := bstep (se 2 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 204689 = 153517) B153517
theorem B139155 : Blo 135790 139155 := bstep (se 1 (by rfl) ⟨104366, by rfl⟩ : syracuseStep 139155 = 208733) B208733
theorem B204707 : Blo 135790 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B139171 : Blo 135790 139171 := bstep (se 1 (by rfl) ⟨104378, by rfl⟩ : syracuseStep 139171 = 208757) B208757
theorem B139187 : Blo 135790 139187 := bstep (se 1 (by rfl) ⟨104390, by rfl⟩ : syracuseStep 139187 = 208781) B208781
theorem B204737 : Blo 135790 204737 := bstep (se 2 (by rfl) ⟨76776, by rfl⟩ : syracuseStep 204737 = 153553) B153553
theorem B466883 : Blo 135790 466883 := bstep (se 1 (by rfl) ⟨350162, by rfl⟩ : syracuseStep 466883 = 700325) B700325
theorem B139203 : Blo 135790 139203 := bstep (se 1 (by rfl) ⟨104402, by rfl⟩ : syracuseStep 139203 = 208805) B208805
theorem B204755 : Blo 135790 204755 := bstep (se 1 (by rfl) ⟨153566, by rfl⟩ : syracuseStep 204755 = 307133) B307133
theorem B139219 : Blo 135790 139219 := bstep (se 1 (by rfl) ⟨104414, by rfl⟩ : syracuseStep 139219 = 208829) B208829
theorem B139235 : Blo 135790 139235 := bstep (se 1 (by rfl) ⟨104426, by rfl⟩ : syracuseStep 139235 = 208853) B208853
theorem B204785 : Blo 135790 204785 := bstep (se 2 (by rfl) ⟨76794, by rfl⟩ : syracuseStep 204785 = 153589) B153589
theorem B139251 : Blo 135790 139251 := bstep (se 1 (by rfl) ⟨104438, by rfl⟩ : syracuseStep 139251 = 208877) B208877
theorem B204803 : Blo 135790 204803 := bstep (se 1 (by rfl) ⟨153602, by rfl⟩ : syracuseStep 204803 = 307205) B307205
theorem B139267 : Blo 135790 139267 := bstep (se 1 (by rfl) ⟨104450, by rfl⟩ : syracuseStep 139267 = 208901) B208901
theorem B139283 : Blo 135790 139283 := bstep (se 1 (by rfl) ⟨104462, by rfl⟩ : syracuseStep 139283 = 208925) B208925
theorem B204833 : Blo 135790 204833 := bstep (se 2 (by rfl) ⟨76812, by rfl⟩ : syracuseStep 204833 = 153625) B153625
theorem B139299 : Blo 135790 139299 := bstep (se 1 (by rfl) ⟨104474, by rfl⟩ : syracuseStep 139299 = 208949) B208949
theorem B204851 : Blo 135790 204851 := bstep (se 1 (by rfl) ⟨153638, by rfl⟩ : syracuseStep 204851 = 307277) B307277
theorem B139315 : Blo 135790 139315 := bstep (se 1 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 139315 = 208973) B208973
theorem B139331 : Blo 135790 139331 := bstep (se 1 (by rfl) ⟨104498, by rfl⟩ : syracuseStep 139331 = 208997) B208997
theorem B204881 : Blo 135790 204881 := bstep (se 2 (by rfl) ⟨76830, by rfl⟩ : syracuseStep 204881 = 153661) B153661
theorem B139347 : Blo 135790 139347 := bstep (se 1 (by rfl) ⟨104510, by rfl⟩ : syracuseStep 139347 = 209021) B209021
theorem B204899 : Blo 135790 204899 := bstep (se 1 (by rfl) ⟨153674, by rfl⟩ : syracuseStep 204899 = 307349) B307349
theorem B139363 : Blo 135790 139363 := bstep (se 1 (by rfl) ⟨104522, by rfl⟩ : syracuseStep 139363 = 209045) B209045
theorem B139379 : Blo 135790 139379 := bstep (se 1 (by rfl) ⟨104534, by rfl⟩ : syracuseStep 139379 = 209069) B209069
theorem B204929 : Blo 135790 204929 := bstep (se 2 (by rfl) ⟨76848, by rfl⟩ : syracuseStep 204929 = 153697) B153697
theorem B139395 : Blo 135790 139395 := bstep (se 1 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 139395 = 209093) B209093
theorem B204947 : Blo 135790 204947 := bstep (se 1 (by rfl) ⟨153710, by rfl⟩ : syracuseStep 204947 = 307421) B307421
theorem B139411 : Blo 135790 139411 := bstep (se 1 (by rfl) ⟨104558, by rfl⟩ : syracuseStep 139411 = 209117) B209117
theorem B139427 : Blo 135790 139427 := bstep (se 1 (by rfl) ⟨104570, by rfl⟩ : syracuseStep 139427 = 209141) B209141
theorem B204977 : Blo 135790 204977 := bstep (se 2 (by rfl) ⟨76866, by rfl⟩ : syracuseStep 204977 = 153733) B153733
theorem B139443 : Blo 135790 139443 := bstep (se 1 (by rfl) ⟨104582, by rfl⟩ : syracuseStep 139443 = 209165) B209165
theorem B204995 : Blo 135790 204995 := bstep (se 1 (by rfl) ⟨153746, by rfl⟩ : syracuseStep 204995 = 307493) B307493
theorem B139459 : Blo 135790 139459 := bstep (se 1 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 139459 = 209189) B209189
theorem B467153 : Blo 135790 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B139475 : Blo 135790 139475 := bstep (se 1 (by rfl) ⟨104606, by rfl⟩ : syracuseStep 139475 = 209213) B209213
theorem B205025 : Blo 135790 205025 := bstep (se 2 (by rfl) ⟨76884, by rfl⟩ : syracuseStep 205025 = 153769) B153769
theorem B139491 : Blo 135790 139491 := bstep (se 1 (by rfl) ⟨104618, by rfl⟩ : syracuseStep 139491 = 209237) B209237
theorem B205043 : Blo 135790 205043 := bstep (se 1 (by rfl) ⟨153782, by rfl⟩ : syracuseStep 205043 = 307565) B307565
theorem B139507 : Blo 135790 139507 := bstep (se 1 (by rfl) ⟨104630, by rfl⟩ : syracuseStep 139507 = 209261) B209261
theorem B139523 : Blo 135790 139523 := bstep (se 1 (by rfl) ⟨104642, by rfl⟩ : syracuseStep 139523 = 209285) B209285
theorem B205073 : Blo 135790 205073 := bstep (se 2 (by rfl) ⟨76902, by rfl⟩ : syracuseStep 205073 = 153805) B153805
theorem B172307 : Blo 135790 172307 := bstep (se 1 (by rfl) ⟨129230, by rfl⟩ : syracuseStep 172307 = 258461) B258461
theorem B139539 : Blo 135790 139539 := bstep (se 1 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 139539 = 209309) B209309
theorem B205091 : Blo 135790 205091 := bstep (se 1 (by rfl) ⟨153818, by rfl⟩ : syracuseStep 205091 = 307637) B307637
theorem B139555 : Blo 135790 139555 := bstep (se 1 (by rfl) ⟨104666, by rfl⟩ : syracuseStep 139555 = 209333) B209333
theorem B139571 : Blo 135790 139571 := bstep (se 1 (by rfl) ⟨104678, by rfl⟩ : syracuseStep 139571 = 209357) B209357
theorem B205121 : Blo 135790 205121 := bstep (se 2 (by rfl) ⟨76920, by rfl⟩ : syracuseStep 205121 = 153841) B153841
theorem B139587 : Blo 135790 139587 := bstep (se 1 (by rfl) ⟨104690, by rfl⟩ : syracuseStep 139587 = 209381) B209381
theorem B205139 : Blo 135790 205139 := bstep (se 1 (by rfl) ⟨153854, by rfl⟩ : syracuseStep 205139 = 307709) B307709
theorem B139603 : Blo 135790 139603 := bstep (se 1 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 139603 = 209405) B209405
theorem B139619 : Blo 135790 139619 := bstep (se 1 (by rfl) ⟨104714, by rfl⟩ : syracuseStep 139619 = 209429) B209429
theorem B205169 : Blo 135790 205169 := bstep (se 2 (by rfl) ⟨76938, by rfl⟩ : syracuseStep 205169 = 153877) B153877
theorem B1188209 : Blo 135790 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B237937 : Blo 135790 237937 := bstep (se 2 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 237937 = 178453) B178453
theorem B139635 : Blo 135790 139635 := bstep (se 1 (by rfl) ⟨104726, by rfl⟩ : syracuseStep 139635 = 209453) B209453
theorem B205187 : Blo 135790 205187 := bstep (se 1 (by rfl) ⟨153890, by rfl⟩ : syracuseStep 205187 = 307781) B307781
theorem B139651 : Blo 135790 139651 := bstep (se 1 (by rfl) ⟨104738, by rfl⟩ : syracuseStep 139651 = 209477) B209477
theorem B139667 : Blo 135790 139667 := bstep (se 1 (by rfl) ⟨104750, by rfl⟩ : syracuseStep 139667 = 209501) B209501
theorem B205217 : Blo 135790 205217 := bstep (se 2 (by rfl) ⟨76956, by rfl⟩ : syracuseStep 205217 = 153913) B153913
theorem B139683 : Blo 135790 139683 := bstep (se 1 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 139683 = 209525) B209525
theorem B205235 : Blo 135790 205235 := bstep (se 1 (by rfl) ⟨153926, by rfl⟩ : syracuseStep 205235 = 307853) B307853
theorem B139699 : Blo 135790 139699 := bstep (se 1 (by rfl) ⟨104774, by rfl⟩ : syracuseStep 139699 = 209549) B209549
theorem B139715 : Blo 135790 139715 := bstep (se 1 (by rfl) ⟨104786, by rfl⟩ : syracuseStep 139715 = 209573) B209573
theorem B205265 : Blo 135790 205265 := bstep (se 2 (by rfl) ⟨76974, by rfl⟩ : syracuseStep 205265 = 153949) B153949
theorem B139731 : Blo 135790 139731 := bstep (se 1 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 139731 = 209597) B209597
theorem B205283 : Blo 135790 205283 := bstep (se 1 (by rfl) ⟨153962, by rfl⟩ : syracuseStep 205283 = 307925) B307925
theorem B139747 : Blo 135790 139747 := bstep (se 1 (by rfl) ⟨104810, by rfl⟩ : syracuseStep 139747 = 209621) B209621
theorem B139763 : Blo 135790 139763 := bstep (se 1 (by rfl) ⟨104822, by rfl⟩ : syracuseStep 139763 = 209645) B209645
theorem B205313 : Blo 135790 205313 := bstep (se 2 (by rfl) ⟨76992, by rfl⟩ : syracuseStep 205313 = 153985) B153985
theorem B139779 : Blo 135790 139779 := bstep (se 1 (by rfl) ⟨104834, by rfl⟩ : syracuseStep 139779 = 209669) B209669
theorem B205331 : Blo 135790 205331 := bstep (se 1 (by rfl) ⟨153998, by rfl⟩ : syracuseStep 205331 = 307997) B307997
theorem B205361 : Blo 135790 205361 := bstep (se 2 (by rfl) ⟨77010, by rfl⟩ : syracuseStep 205361 = 154021) B154021
theorem B205379 : Blo 135790 205379 := bstep (se 1 (by rfl) ⟨154034, by rfl⟩ : syracuseStep 205379 = 308069) B308069
theorem B205409 : Blo 135790 205409 := bstep (se 2 (by rfl) ⟨77028, by rfl⟩ : syracuseStep 205409 = 154057) B154057
theorem B1253987 : Blo 135790 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B205427 : Blo 135790 205427 := bstep (se 1 (by rfl) ⟨154070, by rfl⟩ : syracuseStep 205427 = 308141) B308141
theorem B205457 : Blo 135790 205457 := bstep (se 2 (by rfl) ⟨77046, by rfl⟩ : syracuseStep 205457 = 154093) B154093
theorem B205475 : Blo 135790 205475 := bstep (se 1 (by rfl) ⟨154106, by rfl⟩ : syracuseStep 205475 = 308213) B308213
theorem B205505 : Blo 135790 205505 := bstep (se 2 (by rfl) ⟨77064, by rfl⟩ : syracuseStep 205505 = 154129) B154129
theorem B205523 : Blo 135790 205523 := bstep (se 1 (by rfl) ⟨154142, by rfl⟩ : syracuseStep 205523 = 308285) B308285
theorem B1319651 : Blo 135790 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B467693 : Blo 135790 467693 := bstep (se 3 (by rfl) ⟨87692, by rfl⟩ : syracuseStep 467693 = 175385) B175385
theorem B205553 : Blo 135790 205553 := bstep (se 2 (by rfl) ⟨77082, by rfl⟩ : syracuseStep 205553 = 154165) B154165
theorem B205571 : Blo 135790 205571 := bstep (se 1 (by rfl) ⟨154178, by rfl⟩ : syracuseStep 205571 = 308357) B308357
theorem B1123085 : Blo 135790 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B205601 : Blo 135790 205601 := bstep (se 2 (by rfl) ⟨77100, by rfl⟩ : syracuseStep 205601 = 154201) B154201
theorem B467747 : Blo 135790 467747 := bstep (se 1 (by rfl) ⟨350810, by rfl⟩ : syracuseStep 467747 = 701621) B701621
theorem B205619 : Blo 135790 205619 := bstep (se 1 (by rfl) ⟨154214, by rfl⟩ : syracuseStep 205619 = 308429) B308429
theorem B205649 : Blo 135790 205649 := bstep (se 2 (by rfl) ⟨77118, by rfl⟩ : syracuseStep 205649 = 154237) B154237
theorem B205667 : Blo 135790 205667 := bstep (se 1 (by rfl) ⟨154250, by rfl⟩ : syracuseStep 205667 = 308501) B308501
theorem B205697 : Blo 135790 205697 := bstep (se 2 (by rfl) ⟨77136, by rfl⟩ : syracuseStep 205697 = 154273) B154273
theorem B828301 : Blo 135790 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B205715 : Blo 135790 205715 := bstep (se 1 (by rfl) ⟨154286, by rfl⟩ : syracuseStep 205715 = 308573) B308573
theorem B205745 : Blo 135790 205745 := bstep (se 2 (by rfl) ⟨77154, by rfl⟩ : syracuseStep 205745 = 154309) B154309
theorem B205763 : Blo 135790 205763 := bstep (se 1 (by rfl) ⟨154322, by rfl⟩ : syracuseStep 205763 = 308645) B308645
theorem B173011 : Blo 135790 173011 := bstep (se 1 (by rfl) ⟨129758, by rfl⟩ : syracuseStep 173011 = 259517) B259517
theorem B205793 : Blo 135790 205793 := bstep (se 2 (by rfl) ⟨77172, by rfl⟩ : syracuseStep 205793 = 154345) B154345
theorem B2335715 : Blo 135790 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B205811 : Blo 135790 205811 := bstep (se 1 (by rfl) ⟨154358, by rfl⟩ : syracuseStep 205811 = 308717) B308717
theorem B205841 : Blo 135790 205841 := bstep (se 2 (by rfl) ⟨77190, by rfl⟩ : syracuseStep 205841 = 154381) B154381
theorem B205859 : Blo 135790 205859 := bstep (se 1 (by rfl) ⟨154394, by rfl⟩ : syracuseStep 205859 = 308789) B308789
theorem B468017 : Blo 135790 468017 := bstep (se 2 (by rfl) ⟨175506, by rfl⟩ : syracuseStep 468017 = 351013) B351013
theorem B173107 : Blo 135790 173107 := bstep (se 1 (by rfl) ⟨129830, by rfl⟩ : syracuseStep 173107 = 259661) B259661
theorem B205889 : Blo 135790 205889 := bstep (se 2 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 205889 = 154417) B154417
theorem B205907 : Blo 135790 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B205937 : Blo 135790 205937 := bstep (se 2 (by rfl) ⟨77226, by rfl⟩ : syracuseStep 205937 = 154453) B154453
theorem B205955 : Blo 135790 205955 := bstep (se 1 (by rfl) ⟨154466, by rfl⟩ : syracuseStep 205955 = 308933) B308933
theorem B205985 : Blo 135790 205985 := bstep (se 2 (by rfl) ⟨77244, by rfl⟩ : syracuseStep 205985 = 154489) B154489
theorem B206003 : Blo 135790 206003 := bstep (se 1 (by rfl) ⟨154502, by rfl⟩ : syracuseStep 206003 = 309005) B309005
theorem B206033 : Blo 135790 206033 := bstep (se 2 (by rfl) ⟨77262, by rfl⟩ : syracuseStep 206033 = 154525) B154525
theorem B206051 : Blo 135790 206051 := bstep (se 1 (by rfl) ⟨154538, by rfl⟩ : syracuseStep 206051 = 309077) B309077
theorem B697571 : Blo 135790 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B206081 : Blo 135790 206081 := bstep (se 2 (by rfl) ⟨77280, by rfl⟩ : syracuseStep 206081 = 154561) B154561
theorem B206099 : Blo 135790 206099 := bstep (se 1 (by rfl) ⟨154574, by rfl⟩ : syracuseStep 206099 = 309149) B309149
theorem B206129 : Blo 135790 206129 := bstep (se 2 (by rfl) ⟨77298, by rfl⟩ : syracuseStep 206129 = 154597) B154597
theorem B206147 : Blo 135790 206147 := bstep (se 1 (by rfl) ⟨154610, by rfl⟩ : syracuseStep 206147 = 309221) B309221
theorem B206177 : Blo 135790 206177 := bstep (se 2 (by rfl) ⟨77316, by rfl⟩ : syracuseStep 206177 = 154633) B154633
theorem B206195 : Blo 135790 206195 := bstep (se 1 (by rfl) ⟨154646, by rfl⟩ : syracuseStep 206195 = 309293) B309293
theorem B566669 : Blo 135790 566669 := bstep (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) B212501
theorem B206225 : Blo 135790 206225 := bstep (se 2 (by rfl) ⟨77334, by rfl⟩ : syracuseStep 206225 = 154669) B154669
theorem B206243 : Blo 135790 206243 := bstep (se 1 (by rfl) ⟨154682, by rfl⟩ : syracuseStep 206243 = 309365) B309365
theorem B206273 : Blo 135790 206273 := bstep (se 2 (by rfl) ⟨77352, by rfl⟩ : syracuseStep 206273 = 154705) B154705
theorem B206291 : Blo 135790 206291 := bstep (se 1 (by rfl) ⟨154718, by rfl⟩ : syracuseStep 206291 = 309437) B309437
theorem B206321 : Blo 135790 206321 := bstep (se 2 (by rfl) ⟨77370, by rfl⟩ : syracuseStep 206321 = 154741) B154741
theorem B206339 : Blo 135790 206339 := bstep (se 1 (by rfl) ⟨154754, by rfl⟩ : syracuseStep 206339 = 309509) B309509
theorem B206369 : Blo 135790 206369 := bstep (se 2 (by rfl) ⟨77388, by rfl⟩ : syracuseStep 206369 = 154777) B154777
theorem B173603 : Blo 135790 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B206387 : Blo 135790 206387 := bstep (se 1 (by rfl) ⟨154790, by rfl⟩ : syracuseStep 206387 = 309581) B309581
theorem B468557 : Blo 135790 468557 := bstep (se 3 (by rfl) ⟨87854, by rfl⟩ : syracuseStep 468557 = 175709) B175709
theorem B206417 : Blo 135790 206417 := bstep (se 2 (by rfl) ⟨77406, by rfl⟩ : syracuseStep 206417 = 154813) B154813
theorem B206435 : Blo 135790 206435 := bstep (se 1 (by rfl) ⟨154826, by rfl⟩ : syracuseStep 206435 = 309653) B309653
theorem B206465 : Blo 135790 206465 := bstep (se 2 (by rfl) ⟨77424, by rfl⟩ : syracuseStep 206465 = 154849) B154849
theorem B468611 : Blo 135790 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B206483 : Blo 135790 206483 := bstep (se 1 (by rfl) ⟨154862, by rfl⟩ : syracuseStep 206483 = 309725) B309725
theorem B206513 : Blo 135790 206513 := bstep (se 2 (by rfl) ⟨77442, by rfl⟩ : syracuseStep 206513 = 154885) B154885
theorem B206531 : Blo 135790 206531 := bstep (se 1 (by rfl) ⟨154898, by rfl⟩ : syracuseStep 206531 = 309797) B309797
theorem B206561 : Blo 135790 206561 := bstep (se 2 (by rfl) ⟨77460, by rfl⟩ : syracuseStep 206561 = 154921) B154921
theorem B1124081 : Blo 135790 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B206579 : Blo 135790 206579 := bstep (se 1 (by rfl) ⟨154934, by rfl⟩ : syracuseStep 206579 = 309869) B309869
theorem B206609 : Blo 135790 206609 := bstep (se 2 (by rfl) ⟨77478, by rfl⟩ : syracuseStep 206609 = 154957) B154957
theorem B206627 : Blo 135790 206627 := bstep (se 1 (by rfl) ⟨154970, by rfl⟩ : syracuseStep 206627 = 309941) B309941
theorem B206657 : Blo 135790 206657 := bstep (se 2 (by rfl) ⟨77496, by rfl⟩ : syracuseStep 206657 = 154993) B154993
theorem B206675 : Blo 135790 206675 := bstep (se 1 (by rfl) ⟨155006, by rfl⟩ : syracuseStep 206675 = 310013) B310013
theorem B206705 : Blo 135790 206705 := bstep (se 2 (by rfl) ⟨77514, by rfl⟩ : syracuseStep 206705 = 155029) B155029
theorem B206723 : Blo 135790 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B468881 : Blo 135790 468881 := bstep (se 2 (by rfl) ⟨175830, by rfl⟩ : syracuseStep 468881 = 351661) B351661
theorem B206753 : Blo 135790 206753 := bstep (se 2 (by rfl) ⟨77532, by rfl⟩ : syracuseStep 206753 = 155065) B155065
theorem B206771 : Blo 135790 206771 := bstep (se 1 (by rfl) ⟨155078, by rfl⟩ : syracuseStep 206771 = 310157) B310157
theorem B206801 : Blo 135790 206801 := bstep (se 2 (by rfl) ⟨77550, by rfl⟩ : syracuseStep 206801 = 155101) B155101
theorem B206819 : Blo 135790 206819 := bstep (se 1 (by rfl) ⟨155114, by rfl⟩ : syracuseStep 206819 = 310229) B310229
theorem B436205 : Blo 135790 436205 := bstep (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) B163577
theorem B206849 : Blo 135790 206849 := bstep (se 2 (by rfl) ⟨77568, by rfl⟩ : syracuseStep 206849 = 155137) B155137
theorem B698381 : Blo 135790 698381 := bstep (se 3 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 698381 = 261893) B261893
theorem B206867 : Blo 135790 206867 := bstep (se 1 (by rfl) ⟨155150, by rfl⟩ : syracuseStep 206867 = 310301) B310301
theorem B206897 : Blo 135790 206897 := bstep (se 2 (by rfl) ⟨77586, by rfl⟩ : syracuseStep 206897 = 155173) B155173
theorem B206915 : Blo 135790 206915 := bstep (se 1 (by rfl) ⟨155186, by rfl⟩ : syracuseStep 206915 = 310373) B310373
theorem B206945 : Blo 135790 206945 := bstep (se 2 (by rfl) ⟨77604, by rfl⟩ : syracuseStep 206945 = 155209) B155209
theorem B206963 : Blo 135790 206963 := bstep (se 1 (by rfl) ⟨155222, by rfl⟩ : syracuseStep 206963 = 310445) B310445
theorem B206993 : Blo 135790 206993 := bstep (se 2 (by rfl) ⟨77622, by rfl⟩ : syracuseStep 206993 = 155245) B155245
theorem B207011 : Blo 135790 207011 := bstep (se 1 (by rfl) ⟨155258, by rfl⟩ : syracuseStep 207011 = 310517) B310517
theorem B207041 : Blo 135790 207041 := bstep (se 2 (by rfl) ⟨77640, by rfl⟩ : syracuseStep 207041 = 155281) B155281
theorem B2009285 : Blo 135790 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B207059 : Blo 135790 207059 := bstep (se 1 (by rfl) ⟨155294, by rfl⟩ : syracuseStep 207059 = 310589) B310589
theorem B174307 : Blo 135790 174307 := bstep (se 1 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 174307 = 261461) B261461
theorem B207089 : Blo 135790 207089 := bstep (se 2 (by rfl) ⟨77658, by rfl⟩ : syracuseStep 207089 = 155317) B155317
theorem B207107 : Blo 135790 207107 := bstep (se 1 (by rfl) ⟨155330, by rfl⟩ : syracuseStep 207107 = 310661) B310661
theorem B207137 : Blo 135790 207137 := bstep (se 2 (by rfl) ⟨77676, by rfl⟩ : syracuseStep 207137 = 155353) B155353
theorem B207155 : Blo 135790 207155 := bstep (se 1 (by rfl) ⟨155366, by rfl⟩ : syracuseStep 207155 = 310733) B310733
theorem B174403 : Blo 135790 174403 := bstep (se 1 (by rfl) ⟨130802, by rfl⟩ : syracuseStep 174403 = 261605) B261605
theorem B207185 : Blo 135790 207185 := bstep (se 2 (by rfl) ⟨77694, by rfl⟩ : syracuseStep 207185 = 155389) B155389
theorem B207203 : Blo 135790 207203 := bstep (se 1 (by rfl) ⟨155402, by rfl⟩ : syracuseStep 207203 = 310805) B310805
theorem B207233 : Blo 135790 207233 := bstep (se 2 (by rfl) ⟨77712, by rfl⟩ : syracuseStep 207233 = 155425) B155425
theorem B895373 : Blo 135790 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B207251 : Blo 135790 207251 := bstep (se 1 (by rfl) ⟨155438, by rfl⟩ : syracuseStep 207251 = 310877) B310877
theorem B469421 : Blo 135790 469421 := bstep (se 3 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 469421 = 176033) B176033
theorem B305585 : Blo 135790 305585 := bstep (se 2 (by rfl) ⟨114594, by rfl⟩ : syracuseStep 305585 = 229189) B229189
theorem B207281 : Blo 135790 207281 := bstep (se 2 (by rfl) ⟨77730, by rfl⟩ : syracuseStep 207281 = 155461) B155461
theorem B305603 : Blo 135790 305603 := bstep (se 1 (by rfl) ⟨229202, by rfl⟩ : syracuseStep 305603 = 458405) B458405
theorem B207299 : Blo 135790 207299 := bstep (se 1 (by rfl) ⟨155474, by rfl⟩ : syracuseStep 207299 = 310949) B310949
theorem B207329 : Blo 135790 207329 := bstep (se 2 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 207329 = 155497) B155497
theorem B469475 : Blo 135790 469475 := bstep (se 1 (by rfl) ⟨352106, by rfl⟩ : syracuseStep 469475 = 704213) B704213
theorem B207347 : Blo 135790 207347 := bstep (se 1 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 207347 = 311021) B311021
theorem B207377 : Blo 135790 207377 := bstep (se 2 (by rfl) ⟨77766, by rfl⟩ : syracuseStep 207377 = 155533) B155533
theorem B207395 : Blo 135790 207395 := bstep (se 1 (by rfl) ⟨155546, by rfl⟩ : syracuseStep 207395 = 311093) B311093
theorem B371249 : Blo 135790 371249 := bstep (se 2 (by rfl) ⟨139218, by rfl⟩ : syracuseStep 371249 = 278437) B278437
theorem B207425 : Blo 135790 207425 := bstep (se 2 (by rfl) ⟨77784, by rfl⟩ : syracuseStep 207425 = 155569) B155569
theorem B207443 : Blo 135790 207443 := bstep (se 1 (by rfl) ⟨155582, by rfl⟩ : syracuseStep 207443 = 311165) B311165
theorem B207473 : Blo 135790 207473 := bstep (se 2 (by rfl) ⟨77802, by rfl⟩ : syracuseStep 207473 = 155605) B155605
theorem B207491 : Blo 135790 207491 := bstep (se 1 (by rfl) ⟨155618, by rfl⟩ : syracuseStep 207491 = 311237) B311237
theorem B207521 : Blo 135790 207521 := bstep (se 2 (by rfl) ⟨77820, by rfl⟩ : syracuseStep 207521 = 155641) B155641
theorem B207539 : Blo 135790 207539 := bstep (se 1 (by rfl) ⟨155654, by rfl⟩ : syracuseStep 207539 = 311309) B311309
theorem B305873 : Blo 135790 305873 := bstep (se 2 (by rfl) ⟨114702, by rfl⟩ : syracuseStep 305873 = 229405) B229405
theorem B207569 : Blo 135790 207569 := bstep (se 2 (by rfl) ⟨77838, by rfl⟩ : syracuseStep 207569 = 155677) B155677
theorem B305891 : Blo 135790 305891 := bstep (se 1 (by rfl) ⟨229418, by rfl⟩ : syracuseStep 305891 = 458837) B458837
theorem B207587 : Blo 135790 207587 := bstep (se 1 (by rfl) ⟨155690, by rfl⟩ : syracuseStep 207587 = 311381) B311381
theorem B469745 : Blo 135790 469745 := bstep (se 2 (by rfl) ⟨176154, by rfl⟩ : syracuseStep 469745 = 352309) B352309
theorem B207617 : Blo 135790 207617 := bstep (se 2 (by rfl) ⟨77856, by rfl⟩ : syracuseStep 207617 = 155713) B155713
theorem B207635 : Blo 135790 207635 := bstep (se 1 (by rfl) ⟨155726, by rfl⟩ : syracuseStep 207635 = 311453) B311453
theorem B633635 : Blo 135790 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B207665 : Blo 135790 207665 := bstep (se 2 (by rfl) ⟨77874, by rfl⟩ : syracuseStep 207665 = 155749) B155749
theorem B174899 : Blo 135790 174899 := bstep (se 1 (by rfl) ⟨131174, by rfl⟩ : syracuseStep 174899 = 262349) B262349
theorem B207683 : Blo 135790 207683 := bstep (se 1 (by rfl) ⟨155762, by rfl⟩ : syracuseStep 207683 = 311525) B311525
theorem B207713 : Blo 135790 207713 := bstep (se 2 (by rfl) ⟨77892, by rfl⟩ : syracuseStep 207713 = 155785) B155785
theorem B207731 : Blo 135790 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B207761 : Blo 135790 207761 := bstep (se 2 (by rfl) ⟨77910, by rfl⟩ : syracuseStep 207761 = 155821) B155821
theorem B207779 : Blo 135790 207779 := bstep (se 1 (by rfl) ⟨155834, by rfl⟩ : syracuseStep 207779 = 311669) B311669
theorem B207809 : Blo 135790 207809 := bstep (se 2 (by rfl) ⟨77928, by rfl⟩ : syracuseStep 207809 = 155857) B155857
theorem B207827 : Blo 135790 207827 := bstep (se 1 (by rfl) ⟨155870, by rfl⟩ : syracuseStep 207827 = 311741) B311741
theorem B306161 : Blo 135790 306161 := bstep (se 2 (by rfl) ⟨114810, by rfl⟩ : syracuseStep 306161 = 229621) B229621
theorem B207857 : Blo 135790 207857 := bstep (se 2 (by rfl) ⟨77946, by rfl⟩ : syracuseStep 207857 = 155893) B155893
theorem B306179 : Blo 135790 306179 := bstep (se 1 (by rfl) ⟨229634, by rfl⟩ : syracuseStep 306179 = 459269) B459269
theorem B207875 : Blo 135790 207875 := bstep (se 1 (by rfl) ⟨155906, by rfl⟩ : syracuseStep 207875 = 311813) B311813
theorem B207905 : Blo 135790 207905 := bstep (se 2 (by rfl) ⟨77964, by rfl⟩ : syracuseStep 207905 = 155929) B155929
theorem B207923 : Blo 135790 207923 := bstep (se 1 (by rfl) ⟨155942, by rfl⟩ : syracuseStep 207923 = 311885) B311885
theorem B207953 : Blo 135790 207953 := bstep (se 2 (by rfl) ⟨77982, by rfl⟩ : syracuseStep 207953 = 155965) B155965
theorem B207971 : Blo 135790 207971 := bstep (se 1 (by rfl) ⟨155978, by rfl⟩ : syracuseStep 207971 = 311957) B311957
theorem B208001 : Blo 135790 208001 := bstep (se 2 (by rfl) ⟨78000, by rfl⟩ : syracuseStep 208001 = 156001) B156001
theorem B208019 : Blo 135790 208019 := bstep (se 1 (by rfl) ⟨156014, by rfl⟩ : syracuseStep 208019 = 312029) B312029
theorem B208049 : Blo 135790 208049 := bstep (se 2 (by rfl) ⟨78018, by rfl⟩ : syracuseStep 208049 = 156037) B156037
theorem B208067 : Blo 135790 208067 := bstep (se 1 (by rfl) ⟨156050, by rfl⟩ : syracuseStep 208067 = 312101) B312101
theorem B208097 : Blo 135790 208097 := bstep (se 2 (by rfl) ⟨78036, by rfl⟩ : syracuseStep 208097 = 156073) B156073
theorem B208115 : Blo 135790 208115 := bstep (se 1 (by rfl) ⟨156086, by rfl⟩ : syracuseStep 208115 = 312173) B312173
theorem B470285 : Blo 135790 470285 := bstep (se 3 (by rfl) ⟨88178, by rfl⟩ : syracuseStep 470285 = 176357) B176357
theorem B306449 : Blo 135790 306449 := bstep (se 2 (by rfl) ⟨114918, by rfl⟩ : syracuseStep 306449 = 229837) B229837
theorem B208145 : Blo 135790 208145 := bstep (se 2 (by rfl) ⟨78054, by rfl⟩ : syracuseStep 208145 = 156109) B156109
theorem B306467 : Blo 135790 306467 := bstep (se 1 (by rfl) ⟨229850, by rfl⟩ : syracuseStep 306467 = 459701) B459701
theorem B208163 : Blo 135790 208163 := bstep (se 1 (by rfl) ⟨156122, by rfl⟩ : syracuseStep 208163 = 312245) B312245
theorem B208193 : Blo 135790 208193 := bstep (se 2 (by rfl) ⟨78072, by rfl⟩ : syracuseStep 208193 = 156145) B156145
theorem B470339 : Blo 135790 470339 := bstep (se 1 (by rfl) ⟨352754, by rfl⟩ : syracuseStep 470339 = 705509) B705509
theorem B208211 : Blo 135790 208211 := bstep (se 1 (by rfl) ⟨156158, by rfl⟩ : syracuseStep 208211 = 312317) B312317
theorem B208241 : Blo 135790 208241 := bstep (se 2 (by rfl) ⟨78090, by rfl⟩ : syracuseStep 208241 = 156181) B156181
theorem B208243 : Blo 135790 208243 := bstep (se 1 (by rfl) ⟨156182, by rfl⟩ : syracuseStep 208243 = 312365) B312365
theorem B208259 : Blo 135790 208259 := bstep (se 1 (by rfl) ⟨156194, by rfl⟩ : syracuseStep 208259 = 312389) B312389
theorem B208289 : Blo 135790 208289 := bstep (se 2 (by rfl) ⟨78108, by rfl⟩ : syracuseStep 208289 = 156217) B156217
theorem B208307 : Blo 135790 208307 := bstep (se 1 (by rfl) ⟨156230, by rfl⟩ : syracuseStep 208307 = 312461) B312461
theorem B208337 : Blo 135790 208337 := bstep (se 2 (by rfl) ⟨78126, by rfl⟩ : syracuseStep 208337 = 156253) B156253
theorem B208355 : Blo 135790 208355 := bstep (se 1 (by rfl) ⟨156266, by rfl⟩ : syracuseStep 208355 = 312533) B312533
theorem B175603 : Blo 135790 175603 := bstep (se 1 (by rfl) ⟨131702, by rfl⟩ : syracuseStep 175603 = 263405) B263405
theorem B208385 : Blo 135790 208385 := bstep (se 2 (by rfl) ⟨78144, by rfl⟩ : syracuseStep 208385 = 156289) B156289
theorem B208403 : Blo 135790 208403 := bstep (se 1 (by rfl) ⟨156302, by rfl⟩ : syracuseStep 208403 = 312605) B312605
theorem B437795 : Blo 135790 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B306737 : Blo 135790 306737 := bstep (se 2 (by rfl) ⟨115026, by rfl⟩ : syracuseStep 306737 = 230053) B230053
theorem B208433 : Blo 135790 208433 := bstep (se 2 (by rfl) ⟨78162, by rfl⟩ : syracuseStep 208433 = 156325) B156325
theorem B306755 : Blo 135790 306755 := bstep (se 1 (by rfl) ⟨230066, by rfl⟩ : syracuseStep 306755 = 460133) B460133
theorem B208451 : Blo 135790 208451 := bstep (se 1 (by rfl) ⟨156338, by rfl⟩ : syracuseStep 208451 = 312677) B312677
theorem B470609 : Blo 135790 470609 := bstep (se 2 (by rfl) ⟨176478, by rfl⟩ : syracuseStep 470609 = 352957) B352957
theorem B175699 : Blo 135790 175699 := bstep (se 1 (by rfl) ⟨131774, by rfl⟩ : syracuseStep 175699 = 263549) B263549
theorem B208481 : Blo 135790 208481 := bstep (se 2 (by rfl) ⟨78180, by rfl⟩ : syracuseStep 208481 = 156361) B156361
theorem B1060451 : Blo 135790 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B208499 : Blo 135790 208499 := bstep (se 1 (by rfl) ⟨156374, by rfl⟩ : syracuseStep 208499 = 312749) B312749
theorem B208529 : Blo 135790 208529 := bstep (se 2 (by rfl) ⟨78198, by rfl⟩ : syracuseStep 208529 = 156397) B156397
theorem B208547 : Blo 135790 208547 := bstep (se 1 (by rfl) ⟨156410, by rfl⟩ : syracuseStep 208547 = 312821) B312821
theorem B208577 : Blo 135790 208577 := bstep (se 2 (by rfl) ⟨78216, by rfl⟩ : syracuseStep 208577 = 156433) B156433
theorem B208595 : Blo 135790 208595 := bstep (se 1 (by rfl) ⟨156446, by rfl⟩ : syracuseStep 208595 = 312893) B312893
theorem B208625 : Blo 135790 208625 := bstep (se 2 (by rfl) ⟨78234, by rfl⟩ : syracuseStep 208625 = 156469) B156469
theorem B208643 : Blo 135790 208643 := bstep (se 1 (by rfl) ⟨156482, by rfl⟩ : syracuseStep 208643 = 312965) B312965
theorem B208673 : Blo 135790 208673 := bstep (se 2 (by rfl) ⟨78252, by rfl⟩ : syracuseStep 208673 = 156505) B156505
theorem B208691 : Blo 135790 208691 := bstep (se 1 (by rfl) ⟨156518, by rfl⟩ : syracuseStep 208691 = 313037) B313037
theorem B307025 : Blo 135790 307025 := bstep (se 2 (by rfl) ⟨115134, by rfl⟩ : syracuseStep 307025 = 230269) B230269
theorem B208721 : Blo 135790 208721 := bstep (se 2 (by rfl) ⟨78270, by rfl⟩ : syracuseStep 208721 = 156541) B156541
theorem B307043 : Blo 135790 307043 := bstep (se 1 (by rfl) ⟨230282, by rfl⟩ : syracuseStep 307043 = 460565) B460565
theorem B208739 : Blo 135790 208739 := bstep (se 1 (by rfl) ⟨156554, by rfl⟩ : syracuseStep 208739 = 313109) B313109
theorem B1191779 : Blo 135790 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B208769 : Blo 135790 208769 := bstep (se 2 (by rfl) ⟨78288, by rfl⟩ : syracuseStep 208769 = 156577) B156577
theorem B208787 : Blo 135790 208787 := bstep (se 1 (by rfl) ⟨156590, by rfl⟩ : syracuseStep 208787 = 313181) B313181
theorem B208817 : Blo 135790 208817 := bstep (se 2 (by rfl) ⟨78306, by rfl⟩ : syracuseStep 208817 = 156613) B156613
theorem B208835 : Blo 135790 208835 := bstep (se 1 (by rfl) ⟨156626, by rfl⟩ : syracuseStep 208835 = 313253) B313253
theorem B208865 : Blo 135790 208865 := bstep (se 2 (by rfl) ⟨78324, by rfl⟩ : syracuseStep 208865 = 156649) B156649
theorem B208883 : Blo 135790 208883 := bstep (se 1 (by rfl) ⟨156662, by rfl⟩ : syracuseStep 208883 = 313325) B313325
theorem B208913 : Blo 135790 208913 := bstep (se 2 (by rfl) ⟨78342, by rfl⟩ : syracuseStep 208913 = 156685) B156685
theorem B208931 : Blo 135790 208931 := bstep (se 1 (by rfl) ⟨156698, by rfl⟩ : syracuseStep 208931 = 313397) B313397
theorem B208961 : Blo 135790 208961 := bstep (se 2 (by rfl) ⟨78360, by rfl⟩ : syracuseStep 208961 = 156721) B156721
theorem B176195 : Blo 135790 176195 := bstep (se 1 (by rfl) ⟨132146, by rfl⟩ : syracuseStep 176195 = 264293) B264293
theorem B208979 : Blo 135790 208979 := bstep (se 1 (by rfl) ⟨156734, by rfl⟩ : syracuseStep 208979 = 313469) B313469
theorem B471149 : Blo 135790 471149 := bstep (se 3 (by rfl) ⟨88340, by rfl⟩ : syracuseStep 471149 = 176681) B176681
theorem B307313 : Blo 135790 307313 := bstep (se 2 (by rfl) ⟨115242, by rfl⟩ : syracuseStep 307313 = 230485) B230485
theorem B209009 : Blo 135790 209009 := bstep (se 2 (by rfl) ⟨78378, by rfl⟩ : syracuseStep 209009 = 156757) B156757
theorem B307331 : Blo 135790 307331 := bstep (se 1 (by rfl) ⟨230498, by rfl⟩ : syracuseStep 307331 = 460997) B460997
theorem B209027 : Blo 135790 209027 := bstep (se 1 (by rfl) ⟨156770, by rfl⟩ : syracuseStep 209027 = 313541) B313541
theorem B209057 : Blo 135790 209057 := bstep (se 2 (by rfl) ⟨78396, by rfl⟩ : syracuseStep 209057 = 156793) B156793
theorem B471203 : Blo 135790 471203 := bstep (se 1 (by rfl) ⟨353402, by rfl⟩ : syracuseStep 471203 = 706805) B706805
theorem B209075 : Blo 135790 209075 := bstep (se 1 (by rfl) ⟨156806, by rfl⟩ : syracuseStep 209075 = 313613) B313613
theorem B209105 : Blo 135790 209105 := bstep (se 2 (by rfl) ⟨78414, by rfl⟩ : syracuseStep 209105 = 156829) B156829
theorem B209123 : Blo 135790 209123 := bstep (se 1 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 209123 = 313685) B313685
theorem B209153 : Blo 135790 209153 := bstep (se 2 (by rfl) ⟨78432, by rfl⟩ : syracuseStep 209153 = 156865) B156865
theorem B209171 : Blo 135790 209171 := bstep (se 1 (by rfl) ⟨156878, by rfl⟩ : syracuseStep 209171 = 313757) B313757
theorem B209201 : Blo 135790 209201 := bstep (se 2 (by rfl) ⟨78450, by rfl⟩ : syracuseStep 209201 = 156901) B156901
theorem B209219 : Blo 135790 209219 := bstep (se 1 (by rfl) ⟨156914, by rfl⟩ : syracuseStep 209219 = 313829) B313829
theorem B209249 : Blo 135790 209249 := bstep (se 2 (by rfl) ⟨78468, by rfl⟩ : syracuseStep 209249 = 156937) B156937
theorem B1323377 : Blo 135790 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B209267 : Blo 135790 209267 := bstep (se 1 (by rfl) ⟨156950, by rfl⟩ : syracuseStep 209267 = 313901) B313901
theorem B307601 : Blo 135790 307601 := bstep (se 2 (by rfl) ⟨115350, by rfl⟩ : syracuseStep 307601 = 230701) B230701
theorem B209297 : Blo 135790 209297 := bstep (se 2 (by rfl) ⟨78486, by rfl⟩ : syracuseStep 209297 = 156973) B156973
theorem B307619 : Blo 135790 307619 := bstep (se 1 (by rfl) ⟨230714, by rfl⟩ : syracuseStep 307619 = 461429) B461429
theorem B438691 : Blo 135790 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B209315 : Blo 135790 209315 := bstep (se 1 (by rfl) ⟨156986, by rfl⟩ : syracuseStep 209315 = 313973) B313973
theorem B471473 : Blo 135790 471473 := bstep (se 2 (by rfl) ⟨176802, by rfl⟩ : syracuseStep 471473 = 353605) B353605
theorem B209345 : Blo 135790 209345 := bstep (se 2 (by rfl) ⟨78504, by rfl⟩ : syracuseStep 209345 = 157009) B157009
theorem B209363 : Blo 135790 209363 := bstep (se 1 (by rfl) ⟨157022, by rfl⟩ : syracuseStep 209363 = 314045) B314045
theorem B209393 : Blo 135790 209393 := bstep (se 2 (by rfl) ⟨78522, by rfl⟩ : syracuseStep 209393 = 157045) B157045
theorem B209411 : Blo 135790 209411 := bstep (se 1 (by rfl) ⟨157058, by rfl⟩ : syracuseStep 209411 = 314117) B314117
theorem B209441 : Blo 135790 209441 := bstep (se 2 (by rfl) ⟨78540, by rfl⟩ : syracuseStep 209441 = 157081) B157081
theorem B209459 : Blo 135790 209459 := bstep (se 1 (by rfl) ⟨157094, by rfl⟩ : syracuseStep 209459 = 314189) B314189
theorem B209489 : Blo 135790 209489 := bstep (se 2 (by rfl) ⟨78558, by rfl⟩ : syracuseStep 209489 = 157117) B157117
theorem B209507 : Blo 135790 209507 := bstep (se 1 (by rfl) ⟨157130, by rfl⟩ : syracuseStep 209507 = 314261) B314261
theorem B209537 : Blo 135790 209537 := bstep (se 2 (by rfl) ⟨78576, by rfl⟩ : syracuseStep 209537 = 157153) B157153
theorem B209555 : Blo 135790 209555 := bstep (se 1 (by rfl) ⟨157166, by rfl⟩ : syracuseStep 209555 = 314333) B314333
theorem B307889 : Blo 135790 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B209585 : Blo 135790 209585 := bstep (se 2 (by rfl) ⟨78594, by rfl⟩ : syracuseStep 209585 = 157189) B157189
theorem B307907 : Blo 135790 307907 := bstep (se 1 (by rfl) ⟨230930, by rfl⟩ : syracuseStep 307907 = 461861) B461861
theorem B209603 : Blo 135790 209603 := bstep (se 1 (by rfl) ⟨157202, by rfl⟩ : syracuseStep 209603 = 314405) B314405
theorem B209633 : Blo 135790 209633 := bstep (se 2 (by rfl) ⟨78612, by rfl⟩ : syracuseStep 209633 = 157225) B157225
theorem B209651 : Blo 135790 209651 := bstep (se 1 (by rfl) ⟨157238, by rfl⟩ : syracuseStep 209651 = 314477) B314477
theorem B176899 : Blo 135790 176899 := bstep (se 1 (by rfl) ⟨132674, by rfl⟩ : syracuseStep 176899 = 265349) B265349
theorem B209681 : Blo 135790 209681 := bstep (se 2 (by rfl) ⟨78630, by rfl⟩ : syracuseStep 209681 = 157261) B157261
theorem B373585 : Blo 135790 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B701297 : Blo 135790 701297 := bstep (se 2 (by rfl) ⟨262986, by rfl⟩ : syracuseStep 701297 = 525973) B525973
theorem B635825 : Blo 135790 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B308177 : Blo 135790 308177 := bstep (se 2 (by rfl) ⟨115566, by rfl⟩ : syracuseStep 308177 = 231133) B231133
theorem B308195 : Blo 135790 308195 := bstep (se 1 (by rfl) ⟨231146, by rfl⟩ : syracuseStep 308195 = 462293) B462293
theorem B2700485 : Blo 135790 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B3880163 : Blo 135790 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B308465 : Blo 135790 308465 := bstep (se 2 (by rfl) ⟨115674, by rfl⟩ : syracuseStep 308465 = 231349) B231349
theorem B308483 : Blo 135790 308483 := bstep (se 1 (by rfl) ⟨231362, by rfl⟩ : syracuseStep 308483 = 462725) B462725
theorem B275729 : Blo 135790 275729 := bstep (se 2 (by rfl) ⟨103398, by rfl⟩ : syracuseStep 275729 = 206797) B206797
theorem B439793 : Blo 135790 439793 := bstep (se 2 (by rfl) ⟨164922, by rfl⟩ : syracuseStep 439793 = 329845) B329845
theorem B210433 : Blo 135790 210433 := bstep (se 2 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 210433 = 157825) B157825
theorem B275971 : Blo 135790 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B308753 : Blo 135790 308753 := bstep (se 2 (by rfl) ⟨115782, by rfl⟩ : syracuseStep 308753 = 231565) B231565
theorem B308771 : Blo 135790 308771 := bstep (se 1 (by rfl) ⟨231578, by rfl⟩ : syracuseStep 308771 = 463157) B463157
theorem B439921 : Blo 135790 439921 := bstep (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) B329941
theorem B210593 : Blo 135790 210593 := bstep (se 2 (by rfl) ⟨78972, by rfl⟩ : syracuseStep 210593 = 157945) B157945
theorem B309041 : Blo 135790 309041 := bstep (se 2 (by rfl) ⟨115890, by rfl⟩ : syracuseStep 309041 = 231781) B231781
theorem B309059 : Blo 135790 309059 := bstep (se 1 (by rfl) ⟨231794, by rfl⟩ : syracuseStep 309059 = 463589) B463589
theorem B669617 : Blo 135790 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B571313 : Blo 135790 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B669667 : Blo 135790 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B309329 : Blo 135790 309329 := bstep (se 2 (by rfl) ⟨115998, by rfl⟩ : syracuseStep 309329 = 231997) B231997
theorem B309347 : Blo 135790 309347 := bstep (se 1 (by rfl) ⟨232010, by rfl⟩ : syracuseStep 309347 = 464021) B464021
theorem B702755 : Blo 135790 702755 := bstep (se 1 (by rfl) ⟨527066, by rfl⟩ : syracuseStep 702755 = 1054133) B1054133
theorem B637283 : Blo 135790 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B309617 : Blo 135790 309617 := bstep (se 2 (by rfl) ⟨116106, by rfl⟩ : syracuseStep 309617 = 232213) B232213
theorem B309635 : Blo 135790 309635 := bstep (se 1 (by rfl) ⟨232226, by rfl⟩ : syracuseStep 309635 = 464453) B464453
theorem B375185 : Blo 135790 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B440909 : Blo 135790 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B309905 : Blo 135790 309905 := bstep (se 2 (by rfl) ⟨116214, by rfl⟩ : syracuseStep 309905 = 232429) B232429
theorem B309923 : Blo 135790 309923 := bstep (se 1 (by rfl) ⟨232442, by rfl⟩ : syracuseStep 309923 = 464885) B464885
theorem B473795 : Blo 135790 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B310193 : Blo 135790 310193 := bstep (se 2 (by rfl) ⟨116322, by rfl⟩ : syracuseStep 310193 = 232645) B232645
theorem B310211 : Blo 135790 310211 := bstep (se 1 (by rfl) ⟨232658, by rfl⟩ : syracuseStep 310211 = 465317) B465317
theorem B441379 : Blo 135790 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B703565 : Blo 135790 703565 := bstep (se 3 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 703565 = 263837) B263837
theorem B965773 : Blo 135790 965773 := bstep (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) B362165
theorem B310481 : Blo 135790 310481 := bstep (se 2 (by rfl) ⟨116430, by rfl⟩ : syracuseStep 310481 = 232861) B232861
theorem B310499 : Blo 135790 310499 := bstep (se 1 (by rfl) ⟨232874, by rfl⟩ : syracuseStep 310499 = 465749) B465749
theorem B703907 : Blo 135790 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B310769 : Blo 135790 310769 := bstep (se 2 (by rfl) ⟨116538, by rfl⟩ : syracuseStep 310769 = 233077) B233077
theorem B310787 : Blo 135790 310787 := bstep (se 1 (by rfl) ⟨233090, by rfl⟩ : syracuseStep 310787 = 466181) B466181
theorem B376397 : Blo 135790 376397 := bstep (se 3 (by rfl) ⟨70574, by rfl⟩ : syracuseStep 376397 = 141149) B141149
theorem B310979 : Blo 135790 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B376525 : Blo 135790 376525 := bstep (se 3 (by rfl) ⟨70598, by rfl⟩ : syracuseStep 376525 = 141197) B141197
theorem B147187 : Blo 135790 147187 := bstep (se 1 (by rfl) ⟨110390, by rfl⟩ : syracuseStep 147187 = 220781) B220781
theorem B311057 : Blo 135790 311057 := bstep (se 2 (by rfl) ⟨116646, by rfl⟩ : syracuseStep 311057 = 233293) B233293
theorem B311075 : Blo 135790 311075 := bstep (se 1 (by rfl) ⟨233306, by rfl⟩ : syracuseStep 311075 = 466613) B466613
theorem B442253 : Blo 135790 442253 := bstep (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) B165845
theorem B376721 : Blo 135790 376721 := bstep (se 2 (by rfl) ⟨141270, by rfl⟩ : syracuseStep 376721 = 282541) B282541
theorem B835555 : Blo 135790 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B1589219 : Blo 135790 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B311345 : Blo 135790 311345 := bstep (se 2 (by rfl) ⟨116754, by rfl⟩ : syracuseStep 311345 = 233509) B233509
theorem B311363 : Blo 135790 311363 := bstep (se 1 (by rfl) ⟨233522, by rfl⟩ : syracuseStep 311363 = 467045) B467045
theorem B344209 : Blo 135790 344209 := bstep (se 2 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 344209 = 258157) B258157
theorem B147619 : Blo 135790 147619 := bstep (se 1 (by rfl) ⟨110714, by rfl⟩ : syracuseStep 147619 = 221429) B221429
theorem B1327373 : Blo 135790 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B311633 : Blo 135790 311633 := bstep (se 2 (by rfl) ⟨116862, by rfl⟩ : syracuseStep 311633 = 233725) B233725
theorem B246115 : Blo 135790 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B311651 : Blo 135790 311651 := bstep (se 1 (by rfl) ⟨233738, by rfl⟩ : syracuseStep 311651 = 467477) B467477
theorem B344483 : Blo 135790 344483 := bstep (se 1 (by rfl) ⟨258362, by rfl⟩ : syracuseStep 344483 = 516725) B516725
theorem B344675 : Blo 135790 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B311921 : Blo 135790 311921 := bstep (se 2 (by rfl) ⟨116970, by rfl⟩ : syracuseStep 311921 = 233941) B233941
theorem B311939 : Blo 135790 311939 := bstep (se 1 (by rfl) ⟨233954, by rfl⟩ : syracuseStep 311939 = 467909) B467909
theorem B705293 : Blo 135790 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B312209 : Blo 135790 312209 := bstep (se 2 (by rfl) ⟨117078, by rfl⟩ : syracuseStep 312209 = 234157) B234157
theorem B312227 : Blo 135790 312227 := bstep (se 1 (by rfl) ⟨234170, by rfl⟩ : syracuseStep 312227 = 468341) B468341
theorem B3195875 : Blo 135790 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B312497 : Blo 135790 312497 := bstep (se 2 (by rfl) ⟨117186, by rfl⟩ : syracuseStep 312497 = 234373) B234373
theorem B312515 : Blo 135790 312515 := bstep (se 1 (by rfl) ⟨234386, by rfl⟩ : syracuseStep 312515 = 468773) B468773
theorem B247153 : Blo 135790 247153 := bstep (se 2 (by rfl) ⟨92682, by rfl⟩ : syracuseStep 247153 = 185365) B185365
theorem B148883 : Blo 135790 148883 := bstep (se 1 (by rfl) ⟨111662, by rfl⟩ : syracuseStep 148883 = 223325) B223325
theorem B443843 : Blo 135790 443843 := bstep (se 1 (by rfl) ⟨332882, by rfl⟩ : syracuseStep 443843 = 665765) B665765
theorem B312785 : Blo 135790 312785 := bstep (se 2 (by rfl) ⟨117294, by rfl⟩ : syracuseStep 312785 = 234589) B234589
theorem B312803 : Blo 135790 312803 := bstep (se 1 (by rfl) ⟨234602, by rfl⟩ : syracuseStep 312803 = 469205) B469205
theorem B345617 : Blo 135790 345617 := bstep (se 2 (by rfl) ⟨129606, by rfl⟩ : syracuseStep 345617 = 259213) B259213
theorem B345667 : Blo 135790 345667 := bstep (se 1 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 345667 = 518501) B518501
theorem B345809 : Blo 135790 345809 := bstep (se 2 (by rfl) ⟨129678, by rfl⟩ : syracuseStep 345809 = 259357) B259357
theorem B313073 : Blo 135790 313073 := bstep (se 2 (by rfl) ⟨117402, by rfl⟩ : syracuseStep 313073 = 234805) B234805
theorem B313091 : Blo 135790 313091 := bstep (se 1 (by rfl) ⟨234818, by rfl⟩ : syracuseStep 313091 = 469637) B469637
theorem B476977 : Blo 135790 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B378769 : Blo 135790 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B706481 : Blo 135790 706481 := bstep (se 2 (by rfl) ⟨264930, by rfl⟩ : syracuseStep 706481 = 529861) B529861
theorem B313361 : Blo 135790 313361 := bstep (se 2 (by rfl) ⟨117510, by rfl⟩ : syracuseStep 313361 = 235021) B235021
theorem B313379 : Blo 135790 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B12863573 : Blo 135790 12863573 := bstep (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) B150745
theorem B870563 : Blo 135790 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B444611 : Blo 135790 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B313649 : Blo 135790 313649 := bstep (se 2 (by rfl) ⟨117618, by rfl⟩ : syracuseStep 313649 = 235237) B235237
theorem B313667 : Blo 135790 313667 := bstep (se 1 (by rfl) ⟨235250, by rfl⟩ : syracuseStep 313667 = 470501) B470501
theorem B1034693 : Blo 135790 1034693 := bstep (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) B194005
theorem B1329605 : Blo 135790 1329605 := bstep (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) B249301
theorem B445009 : Blo 135790 445009 := bstep (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) B333757
theorem B313937 : Blo 135790 313937 := bstep (se 2 (by rfl) ⟨117726, by rfl⟩ : syracuseStep 313937 = 235453) B235453
theorem B313955 : Blo 135790 313955 := bstep (se 1 (by rfl) ⟨235466, by rfl⟩ : syracuseStep 313955 = 470933) B470933
theorem B346801 : Blo 135790 346801 := bstep (se 2 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 346801 = 260101) B260101
theorem B445123 : Blo 135790 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B1395427 : Blo 135790 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B314225 : Blo 135790 314225 := bstep (se 2 (by rfl) ⟨117834, by rfl⟩ : syracuseStep 314225 = 235669) B235669
theorem B314243 : Blo 135790 314243 := bstep (se 1 (by rfl) ⟨235682, by rfl⟩ : syracuseStep 314243 = 471365) B471365
theorem B347075 : Blo 135790 347075 := bstep (se 1 (by rfl) ⟨260306, by rfl⟩ : syracuseStep 347075 = 520613) B520613
theorem B838669 : Blo 135790 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B347267 : Blo 135790 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B314513 : Blo 135790 314513 := bstep (se 2 (by rfl) ⟨117942, by rfl⟩ : syracuseStep 314513 = 235885) B235885
theorem B871793 : Blo 135790 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B445841 : Blo 135790 445841 := bstep (se 2 (by rfl) ⟨167190, by rfl⟩ : syracuseStep 445841 = 334381) B334381
theorem B446381 : Blo 135790 446381 := bstep (se 3 (by rfl) ⟨83696, by rfl⟩ : syracuseStep 446381 = 167393) B167393
theorem B348209 : Blo 135790 348209 := bstep (se 2 (by rfl) ⟨130578, by rfl⟩ : syracuseStep 348209 = 261157) B261157
theorem B348259 : Blo 135790 348259 := bstep (se 1 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 348259 = 522389) B522389
theorem B446627 : Blo 135790 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B348401 : Blo 135790 348401 := bstep (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) B261301
theorem B217603 : Blo 135790 217603 := bstep (se 1 (by rfl) ⟨163202, by rfl⟩ : syracuseStep 217603 = 326405) B326405
theorem B217667 : Blo 135790 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B217795 : Blo 135790 217795 := bstep (se 1 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 217795 = 326693) B326693
theorem B185041 : Blo 135790 185041 := bstep (se 2 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 185041 = 138781) B138781
theorem B775109 : Blo 135790 775109 := bstep (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) B145333
theorem B939043 : Blo 135790 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B251075 : Blo 135790 251075 := bstep (se 1 (by rfl) ⟨188306, by rfl⟩ : syracuseStep 251075 = 376613) B376613
theorem B349393 : Blo 135790 349393 := bstep (se 2 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 349393 = 262045) B262045
theorem B152851 : Blo 135790 152851 := bstep (se 1 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 152851 = 229277) B229277
theorem B775565 : Blo 135790 775565 := bstep (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) B290837
theorem B218513 : Blo 135790 218513 := bstep (se 2 (by rfl) ⟨81942, by rfl⟩ : syracuseStep 218513 = 163885) B163885
theorem B152995 : Blo 135790 152995 := bstep (se 1 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 152995 = 229493) B229493
theorem B1496501 : Blo 135790 1496501 := bstep (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) B140297
theorem B349667 : Blo 135790 349667 := bstep (se 1 (by rfl) ⟨262250, by rfl⟩ : syracuseStep 349667 = 524501) B524501
theorem B251363 : Blo 135790 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B218641 : Blo 135790 218641 := bstep (se 2 (by rfl) ⟨81990, by rfl⟩ : syracuseStep 218641 = 163981) B163981
theorem B153139 : Blo 135790 153139 := bstep (se 1 (by rfl) ⟨114854, by rfl⟩ : syracuseStep 153139 = 229709) B229709
theorem B185971 : Blo 135790 185971 := bstep (se 1 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 185971 = 278957) B278957
theorem B349859 : Blo 135790 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B153283 : Blo 135790 153283 := bstep (se 1 (by rfl) ⟨114962, by rfl⟩ : syracuseStep 153283 = 229925) B229925
theorem B874253 : Blo 135790 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B153427 : Blo 135790 153427 := bstep (se 1 (by rfl) ⟨115070, by rfl⟩ : syracuseStep 153427 = 230141) B230141
theorem B219025 : Blo 135790 219025 := bstep (se 2 (by rfl) ⟨82134, by rfl⟩ : syracuseStep 219025 = 164269) B164269
theorem B382915 : Blo 135790 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B153571 : Blo 135790 153571 := bstep (se 1 (by rfl) ⟨115178, by rfl⟩ : syracuseStep 153571 = 230357) B230357
theorem B186403 : Blo 135790 186403 := bstep (se 1 (by rfl) ⟨139802, by rfl⟩ : syracuseStep 186403 = 279605) B279605
theorem B2414645 : Blo 135790 2414645 := bstep (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) B226373
theorem B153715 : Blo 135790 153715 := bstep (se 1 (by rfl) ⟨115286, by rfl⟩ : syracuseStep 153715 = 230573) B230573
theorem B3528845 : Blo 135790 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B219281 : Blo 135790 219281 := bstep (se 2 (by rfl) ⟨82230, by rfl⟩ : syracuseStep 219281 = 164461) B164461
theorem B153859 : Blo 135790 153859 := bstep (se 1 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 153859 = 230789) B230789
theorem B154003 : Blo 135790 154003 := bstep (se 1 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 154003 = 231005) B231005
theorem B416195 : Blo 135790 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B154147 : Blo 135790 154147 := bstep (se 1 (by rfl) ⟨115610, by rfl⟩ : syracuseStep 154147 = 231221) B231221
theorem B350801 : Blo 135790 350801 := bstep (se 2 (by rfl) ⟨131550, by rfl⟩ : syracuseStep 350801 = 263101) B263101
theorem B350851 : Blo 135790 350851 := bstep (se 1 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 350851 = 526277) B526277
theorem B154291 : Blo 135790 154291 := bstep (se 1 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 154291 = 231437) B231437
theorem B350993 : Blo 135790 350993 := bstep (se 2 (by rfl) ⟨131622, by rfl⟩ : syracuseStep 350993 = 263245) B263245
theorem B154435 : Blo 135790 154435 := bstep (se 1 (by rfl) ⟨115826, by rfl⟩ : syracuseStep 154435 = 231653) B231653
theorem B154579 : Blo 135790 154579 := bstep (se 1 (by rfl) ⟨115934, by rfl⟩ : syracuseStep 154579 = 231869) B231869
theorem B154723 : Blo 135790 154723 := bstep (se 1 (by rfl) ⟨116042, by rfl⟩ : syracuseStep 154723 = 232085) B232085
theorem B318563 : Blo 135790 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B154867 : Blo 135790 154867 := bstep (se 1 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 154867 = 232301) B232301
theorem B580877 : Blo 135790 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B220483 : Blo 135790 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B155011 : Blo 135790 155011 := bstep (se 1 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 155011 = 232517) B232517
theorem B220691 : Blo 135790 220691 := bstep (se 1 (by rfl) ⟨165518, by rfl⟩ : syracuseStep 220691 = 331037) B331037
theorem B155155 : Blo 135790 155155 := bstep (se 1 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 155155 = 232733) B232733
theorem B155299 : Blo 135790 155299 := bstep (se 1 (by rfl) ⟨116474, by rfl⟩ : syracuseStep 155299 = 232949) B232949
theorem B351985 : Blo 135790 351985 := bstep (se 2 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 351985 = 263989) B263989
theorem B155443 : Blo 135790 155443 := bstep (se 1 (by rfl) ⟨116582, by rfl⟩ : syracuseStep 155443 = 233165) B233165
theorem B155587 : Blo 135790 155587 := bstep (se 1 (by rfl) ⟨116690, by rfl⟩ : syracuseStep 155587 = 233381) B233381
theorem B352259 : Blo 135790 352259 := bstep (se 1 (by rfl) ⟨264194, by rfl⟩ : syracuseStep 352259 = 528389) B528389
theorem B155731 : Blo 135790 155731 := bstep (se 1 (by rfl) ⟨116798, by rfl⟩ : syracuseStep 155731 = 233597) B233597
theorem B1040525 : Blo 135790 1040525 := bstep (se 3 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 1040525 = 390197) B390197
theorem B352451 : Blo 135790 352451 := bstep (se 1 (by rfl) ⟨264338, by rfl⟩ : syracuseStep 352451 = 528677) B528677
theorem B745699 : Blo 135790 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B155875 : Blo 135790 155875 := bstep (se 1 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 155875 = 233813) B233813
theorem B778481 : Blo 135790 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B942349 : Blo 135790 942349 := bstep (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) B353381
theorem B221537 : Blo 135790 221537 := bstep (se 2 (by rfl) ⟨83076, by rfl⟩ : syracuseStep 221537 = 166153) B166153
theorem B156019 : Blo 135790 156019 := bstep (se 1 (by rfl) ⟨117014, by rfl⟩ : syracuseStep 156019 = 234029) B234029
theorem B516557 : Blo 135790 516557 := bstep (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) B193709
theorem B156163 : Blo 135790 156163 := bstep (se 1 (by rfl) ⟨117122, by rfl⟩ : syracuseStep 156163 = 234245) B234245
theorem B582221 : Blo 135790 582221 := bstep (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) B218333
theorem B1401457 : Blo 135790 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B189073 : Blo 135790 189073 := bstep (se 2 (by rfl) ⟨70902, by rfl⟩ : syracuseStep 189073 = 141805) B141805
theorem B156307 : Blo 135790 156307 := bstep (se 1 (by rfl) ⟨117230, by rfl⟩ : syracuseStep 156307 = 234461) B234461
theorem B156451 : Blo 135790 156451 := bstep (se 1 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 156451 = 234677) B234677
theorem B418627 : Blo 135790 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B222049 : Blo 135790 222049 := bstep (se 2 (by rfl) ⟨83268, by rfl⟩ : syracuseStep 222049 = 166537) B166537
theorem B1991537 : Blo 135790 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B156595 : Blo 135790 156595 := bstep (se 1 (by rfl) ⟨117446, by rfl⟩ : syracuseStep 156595 = 234893) B234893
theorem B3761093 : Blo 135790 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B156739 : Blo 135790 156739 := bstep (se 1 (by rfl) ⟨117554, by rfl⟩ : syracuseStep 156739 = 235109) B235109
theorem B353393 : Blo 135790 353393 := bstep (se 2 (by rfl) ⟨132522, by rfl⟩ : syracuseStep 353393 = 265045) B265045
theorem B353443 : Blo 135790 353443 := bstep (se 1 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 353443 = 530165) B530165
theorem B156883 : Blo 135790 156883 := bstep (se 1 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 156883 = 235325) B235325
theorem B353585 : Blo 135790 353585 := bstep (se 2 (by rfl) ⟨132594, by rfl⟩ : syracuseStep 353585 = 265189) B265189
theorem B157027 : Blo 135790 157027 := bstep (se 1 (by rfl) ⟨117770, by rfl⟩ : syracuseStep 157027 = 235541) B235541
theorem B222659 : Blo 135790 222659 := bstep (se 1 (by rfl) ⟨166994, by rfl⟩ : syracuseStep 222659 = 333989) B333989
theorem B157171 : Blo 135790 157171 := bstep (se 1 (by rfl) ⟨117878, by rfl⟩ : syracuseStep 157171 = 235757) B235757
theorem B157187 : Blo 135790 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B779939 : Blo 135790 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B387089 : Blo 135790 387089 := bstep (se 2 (by rfl) ⟨145158, by rfl⟩ : syracuseStep 387089 = 290317) B290317
theorem B583793 : Blo 135790 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B387281 : Blo 135790 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B10414307 : Blo 135790 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B223651 : Blo 135790 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B518669 : Blo 135790 518669 := bstep (se 3 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 518669 = 194501) B194501
theorem B1305229 : Blo 135790 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B780941 : Blo 135790 780941 := bstep (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) B292853
theorem B158611 : Blo 135790 158611 := bstep (se 1 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 158611 = 237917) B237917
theorem B1043441 : Blo 135790 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B191489 : Blo 135790 191489 := bstep (se 2 (by rfl) ⟨71808, by rfl⟩ : syracuseStep 191489 = 143617) B143617
theorem B388273 : Blo 135790 388273 := bstep (se 2 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 388273 = 291205) B291205
theorem B1666289 : Blo 135790 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B519473 : Blo 135790 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B388547 : Blo 135790 388547 := bstep (se 1 (by rfl) ⟨291410, by rfl⟩ : syracuseStep 388547 = 582821) B582821
theorem B388739 : Blo 135790 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B1175309 : Blo 135790 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B421645 : Blo 135790 421645 := bstep (se 3 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 421645 = 158117) B158117
theorem B421741 : Blo 135790 421741 := bstep (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) B158153
theorem B520141 : Blo 135790 520141 := bstep (se 3 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 520141 = 195053) B195053
theorem B421841 : Blo 135790 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B749573 : Blo 135790 749573 := bstep (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) B140545
theorem B1667213 : Blo 135790 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B258385 : Blo 135790 258385 := bstep (se 2 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 258385 = 193789) B193789
theorem B389549 : Blo 135790 389549 := bstep (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) B146081
theorem B291281 : Blo 135790 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B258545 : Blo 135790 258545 := bstep (se 2 (by rfl) ⟨96954, by rfl⟩ : syracuseStep 258545 = 193909) B193909
theorem B586253 : Blo 135790 586253 := bstep (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) B219845
theorem B389731 : Blo 135790 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B520931 : Blo 135790 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B1307461 : Blo 135790 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B848717 : Blo 135790 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B586595 : Blo 135790 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B258947 : Blo 135790 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B390221 : Blo 135790 390221 := bstep (se 3 (by rfl) ⟨73166, by rfl⟩ : syracuseStep 390221 = 146333) B146333
theorem B1537165 : Blo 135790 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B193681 : Blo 135790 193681 := bstep (se 2 (by rfl) ⟨72630, by rfl⟩ : syracuseStep 193681 = 145261) B145261
theorem B521585 : Blo 135790 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B423299 : Blo 135790 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B194017 : Blo 135790 194017 := bstep (se 2 (by rfl) ⟨72756, by rfl⟩ : syracuseStep 194017 = 145513) B145513
theorem B783857 : Blo 135790 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B882353 : Blo 135790 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B554701 : Blo 135790 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B259843 : Blo 135790 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B260003 : Blo 135790 260003 := bstep (se 1 (by rfl) ⟨195002, by rfl⟩ : syracuseStep 260003 = 390005) B390005
theorem B194609 : Blo 135790 194609 := bstep (se 2 (by rfl) ⟨72978, by rfl⟩ : syracuseStep 194609 = 145957) B145957
theorem B1177699 : Blo 135790 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B391405 : Blo 135790 391405 := bstep (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) B146777
theorem B424493 : Blo 135790 424493 := bstep (se 3 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 424493 = 159185) B159185
theorem B195139 : Blo 135790 195139 := bstep (se 1 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 195139 = 292709) B292709
theorem B523043 : Blo 135790 523043 := bstep (se 1 (by rfl) ⟨392282, by rfl⟩ : syracuseStep 523043 = 784565) B784565
theorem B523057 : Blo 135790 523057 := bstep (se 2 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 523057 = 392293) B392293
theorem B195475 : Blo 135790 195475 := bstep (se 1 (by rfl) ⟨146606, by rfl⟩ : syracuseStep 195475 = 293213) B293213
theorem B785315 : Blo 135790 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B2489285 : Blo 135790 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B261073 : Blo 135790 261073 := bstep (se 2 (by rfl) ⟨97902, by rfl⟩ : syracuseStep 261073 = 195805) B195805
theorem B1506275 : Blo 135790 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B1113101 : Blo 135790 1113101 := bstep (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) B417413
theorem B3013685 : Blo 135790 3013685 := bstep (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) B282533
theorem B392465 : Blo 135790 392465 := bstep (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) B294349
theorem B949553 : Blo 135790 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B196033 : Blo 135790 196033 := bstep (se 2 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 196033 = 147025) B147025
theorem B196067 : Blo 135790 196067 := bstep (se 1 (by rfl) ⟨147050, by rfl⟩ : syracuseStep 196067 = 294101) B294101
theorem B491021 : Blo 135790 491021 := bstep (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) B184133
theorem B654961 : Blo 135790 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B655075 : Blo 135790 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B458513 : Blo 135790 458513 := bstep (se 2 (by rfl) ⟨171942, by rfl⟩ : syracuseStep 458513 = 343885) B343885
theorem B294691 : Blo 135790 294691 := bstep (se 1 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 294691 = 442037) B442037
theorem B229169 : Blo 135790 229169 := bstep (se 2 (by rfl) ⟨85938, by rfl⟩ : syracuseStep 229169 = 171877) B171877
theorem B688013 : Blo 135790 688013 := bstep (se 3 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 688013 = 258005) B258005
theorem B229297 : Blo 135790 229297 := bstep (se 2 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 229297 = 171973) B171973
theorem B393137 : Blo 135790 393137 := bstep (se 2 (by rfl) ⟨147426, by rfl⟩ : syracuseStep 393137 = 294853) B294853
theorem B229331 : Blo 135790 229331 := bstep (se 1 (by rfl) ⟨171998, by rfl⟩ : syracuseStep 229331 = 343997) B343997
theorem B262129 : Blo 135790 262129 := bstep (se 2 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 262129 = 196597) B196597
theorem B1179683 : Blo 135790 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B524333 : Blo 135790 524333 := bstep (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) B196625
theorem B262273 : Blo 135790 262273 := bstep (se 2 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 262273 = 196705) B196705
theorem B884915 : Blo 135790 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B458945 : Blo 135790 458945 := bstep (se 2 (by rfl) ⟨172104, by rfl⟩ : syracuseStep 458945 = 344209) B344209
theorem B655577 : Blo 135790 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B196825 : Blo 135790 196825 := bstep (se 2 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 196825 = 147619) B147619
theorem B229655 : Blo 135790 229655 := bstep (se 1 (by rfl) ⟨172241, by rfl⟩ : syracuseStep 229655 = 344483) B344483
theorem B229783 : Blo 135790 229783 := bstep (se 1 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 229783 = 344675) B344675
theorem B262615 : Blo 135790 262615 := bstep (se 1 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 262615 = 393923) B393923
theorem B328153 : Blo 135790 328153 := bstep (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) B246115
theorem B393751 : Blo 135790 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B2130583 : Blo 135790 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B262835 : Blo 135790 262835 := bstep (se 1 (by rfl) ⟨197126, by rfl⟩ : syracuseStep 262835 = 394253) B394253
theorem B459485 : Blo 135790 459485 := bstep (se 3 (by rfl) ⟨86153, by rfl⟩ : syracuseStep 459485 = 172307) B172307
theorem B1180433 : Blo 135790 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1868609 : Blo 135790 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B263063 : Blo 135790 263063 := bstep (se 1 (by rfl) ⟨197297, by rfl⟩ : syracuseStep 263063 = 394595) B394595
theorem B295895 : Blo 135790 295895 := bstep (se 1 (by rfl) ⟨221921, by rfl⟩ : syracuseStep 295895 = 443843) B443843
theorem B230411 : Blo 135790 230411 := bstep (se 1 (by rfl) ⟨172808, by rfl⟩ : syracuseStep 230411 = 345617) B345617
theorem B296065 : Blo 135790 296065 := bstep (se 2 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 296065 = 222049) B222049
theorem B1508483 : Blo 135790 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B230539 : Blo 135790 230539 := bstep (se 1 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 230539 = 345809) B345809
theorem B263321 : Blo 135790 263321 := bstep (se 2 (by rfl) ⟨98745, by rfl⟩ : syracuseStep 263321 = 197491) B197491
theorem B230681 : Blo 135790 230681 := bstep (se 2 (by rfl) ⟨86505, by rfl⟩ : syracuseStep 230681 = 173011) B173011
theorem B394571 : Blo 135790 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B230809 : Blo 135790 230809 := bstep (se 2 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 230809 = 173107) B173107
theorem B525761 : Blo 135790 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B296407 : Blo 135790 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B263731 : Blo 135790 263731 := bstep (se 1 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 263731 = 395597) B395597
theorem B886373 : Blo 135790 886373 := bstep (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) B166195
theorem B689795 : Blo 135790 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B886403 : Blo 135790 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B198283 : Blo 135790 198283 := bstep (se 1 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 198283 = 297425) B297425
theorem B329537 : Blo 135790 329537 := bstep (se 2 (by rfl) ⟨123576, by rfl⟩ : syracuseStep 329537 = 247153) B247153
theorem B460619 : Blo 135790 460619 := bstep (se 1 (by rfl) ⟨345464, by rfl⟩ : syracuseStep 460619 = 690929) B690929
theorem B722819 : Blo 135790 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B231383 : Blo 135790 231383 := bstep (se 1 (by rfl) ⟨173537, by rfl⟩ : syracuseStep 231383 = 347075) B347075
theorem B264217 : Blo 135790 264217 := bstep (se 2 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 264217 = 198163) B198163
theorem B231511 : Blo 135790 231511 := bstep (se 1 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 231511 = 347267) B347267
theorem B460889 : Blo 135790 460889 := bstep (se 2 (by rfl) ⟨172833, by rfl⟩ : syracuseStep 460889 = 345667) B345667
theorem B1312919 : Blo 135790 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B297227 : Blo 135790 297227 := bstep (se 1 (by rfl) ⟨222920, by rfl⟩ : syracuseStep 297227 = 445841) B445841
theorem B264779 : Blo 135790 264779 := bstep (se 1 (by rfl) ⟨198584, by rfl⟩ : syracuseStep 264779 = 397169) B397169
theorem B297587 : Blo 135790 297587 := bstep (se 1 (by rfl) ⟨223190, by rfl⟩ : syracuseStep 297587 = 446381) B446381
theorem B232139 : Blo 135790 232139 := bstep (se 1 (by rfl) ⟨174104, by rfl⟩ : syracuseStep 232139 = 348209) B348209
theorem B264961 : Blo 135790 264961 := bstep (se 2 (by rfl) ⟨99360, by rfl⟩ : syracuseStep 264961 = 198721) B198721
theorem B461591 : Blo 135790 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B297751 : Blo 135790 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B232267 : Blo 135790 232267 := bstep (se 1 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 232267 = 348401) B348401
theorem B527249 : Blo 135790 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B232409 : Blo 135790 232409 := bstep (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) B174307
theorem B232537 : Blo 135790 232537 := bstep (se 2 (by rfl) ⟨87201, by rfl⟩ : syracuseStep 232537 = 174403) B174403
theorem B265483 : Blo 135790 265483 := bstep (se 1 (by rfl) ⟨199112, by rfl⟩ : syracuseStep 265483 = 398225) B398225
theorem B462131 : Blo 135790 462131 := bstep (se 1 (by rfl) ⟨346598, by rfl⟩ : syracuseStep 462131 = 693197) B693197
theorem B527705 : Blo 135790 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B593345 : Blo 135790 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B167383 : Blo 135790 167383 := bstep (se 1 (by rfl) ⟨125537, by rfl⟩ : syracuseStep 167383 = 251075) B251075
theorem B1740305 : Blo 135790 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B658961 : Blo 135790 658961 := bstep (se 2 (by rfl) ⟨247110, by rfl⟩ : syracuseStep 658961 = 494221) B494221
theorem B527917 : Blo 135790 527917 := bstep (se 3 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 527917 = 197969) B197969
theorem B462401 : Blo 135790 462401 := bstep (se 2 (by rfl) ⟨173400, by rfl⟩ : syracuseStep 462401 = 346801) B346801
theorem B593497 : Blo 135790 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B233111 : Blo 135790 233111 := bstep (se 1 (by rfl) ⟨174833, by rfl⟩ : syracuseStep 233111 = 349667) B349667
theorem B1183409 : Blo 135790 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B397021 : Blo 135790 397021 := bstep (se 3 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 397021 = 148883) B148883
theorem B233239 : Blo 135790 233239 := bstep (se 1 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 233239 = 349859) B349859
theorem B528221 : Blo 135790 528221 := bstep (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) B198083
theorem B1118225 : Blo 135790 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B1609763 : Blo 135790 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B462941 : Blo 135790 462941 := bstep (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) B173603
theorem B790829 : Blo 135790 790829 := bstep (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) B296561
theorem B2232677 : Blo 135790 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B233867 : Blo 135790 233867 := bstep (se 1 (by rfl) ⟨175400, by rfl⟩ : syracuseStep 233867 = 350801) B350801
theorem B561581 : Blo 135790 561581 := bstep (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) B210593
theorem B233995 : Blo 135790 233995 := bstep (se 1 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 233995 = 350993) B350993
theorem B135799 : Blo 135790 135799 := bstep (se 1 (by rfl) ⟨101849, by rfl⟩ : syracuseStep 135799 = 203699) B203699
theorem B135819 : Blo 135790 135819 := bstep (se 1 (by rfl) ⟨101864, by rfl⟩ : syracuseStep 135819 = 203729) B203729
theorem B135831 : Blo 135790 135831 := bstep (se 1 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 135831 = 203747) B203747
theorem B266905 : Blo 135790 266905 := bstep (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) B200179
theorem B234137 : Blo 135790 234137 := bstep (se 2 (by rfl) ⟨87801, by rfl⟩ : syracuseStep 234137 = 175603) B175603
theorem B135851 : Blo 135790 135851 := bstep (se 1 (by rfl) ⟨101888, by rfl⟩ : syracuseStep 135851 = 203777) B203777
theorem B135863 : Blo 135790 135863 := bstep (se 1 (by rfl) ⟨101897, by rfl⟩ : syracuseStep 135863 = 203795) B203795
theorem B135883 : Blo 135790 135883 := bstep (se 1 (by rfl) ⟨101912, by rfl⟩ : syracuseStep 135883 = 203825) B203825
theorem B2331341 : Blo 135790 2331341 := bstep (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) B874253
theorem B135895 : Blo 135790 135895 := bstep (se 1 (by rfl) ⟨101921, by rfl⟩ : syracuseStep 135895 = 203843) B203843
theorem B135915 : Blo 135790 135915 := bstep (se 1 (by rfl) ⟨101936, by rfl⟩ : syracuseStep 135915 = 203873) B203873
theorem B135927 : Blo 135790 135927 := bstep (se 1 (by rfl) ⟨101945, by rfl⟩ : syracuseStep 135927 = 203891) B203891
theorem B135947 : Blo 135790 135947 := bstep (se 1 (by rfl) ⟨101960, by rfl⟩ : syracuseStep 135947 = 203921) B203921
theorem B135959 : Blo 135790 135959 := bstep (se 1 (by rfl) ⟨101969, by rfl⟩ : syracuseStep 135959 = 203939) B203939
theorem B234265 : Blo 135790 234265 := bstep (se 2 (by rfl) ⟨87849, by rfl⟩ : syracuseStep 234265 = 175699) B175699
theorem B135979 : Blo 135790 135979 := bstep (se 1 (by rfl) ⟨101984, by rfl⟩ : syracuseStep 135979 = 203969) B203969
theorem B135991 : Blo 135790 135991 := bstep (se 1 (by rfl) ⟨101993, by rfl⟩ : syracuseStep 135991 = 203987) B203987
theorem B136011 : Blo 135790 136011 := bstep (se 1 (by rfl) ⟨102008, by rfl⟩ : syracuseStep 136011 = 204017) B204017
theorem B136023 : Blo 135790 136023 := bstep (se 1 (by rfl) ⟨102017, by rfl⟩ : syracuseStep 136023 = 204035) B204035
theorem B136043 : Blo 135790 136043 := bstep (se 1 (by rfl) ⟨102032, by rfl⟩ : syracuseStep 136043 = 204065) B204065
theorem B136055 : Blo 135790 136055 := bstep (se 1 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 136055 = 204083) B204083
theorem B136075 : Blo 135790 136075 := bstep (se 1 (by rfl) ⟨102056, by rfl⟩ : syracuseStep 136075 = 204113) B204113
theorem B136087 : Blo 135790 136087 := bstep (se 1 (by rfl) ⟨102065, by rfl⟩ : syracuseStep 136087 = 204131) B204131
theorem B136107 : Blo 135790 136107 := bstep (se 1 (by rfl) ⟨102080, by rfl⟩ : syracuseStep 136107 = 204161) B204161
theorem B136119 : Blo 135790 136119 := bstep (se 1 (by rfl) ⟨102089, by rfl⟩ : syracuseStep 136119 = 204179) B204179
theorem B136139 : Blo 135790 136139 := bstep (se 1 (by rfl) ⟨102104, by rfl⟩ : syracuseStep 136139 = 204209) B204209
theorem B136151 : Blo 135790 136151 := bstep (se 1 (by rfl) ⟨102113, by rfl⟩ : syracuseStep 136151 = 204227) B204227
theorem B136171 : Blo 135790 136171 := bstep (se 1 (by rfl) ⟨102128, by rfl⟩ : syracuseStep 136171 = 204257) B204257
theorem B136183 : Blo 135790 136183 := bstep (se 1 (by rfl) ⟨102137, by rfl⟩ : syracuseStep 136183 = 204275) B204275
theorem B136203 : Blo 135790 136203 := bstep (se 1 (by rfl) ⟨102152, by rfl⟩ : syracuseStep 136203 = 204305) B204305
theorem B562193 : Blo 135790 562193 := bstep (se 2 (by rfl) ⟨210822, by rfl⟩ : syracuseStep 562193 = 421645) B421645
theorem B136215 : Blo 135790 136215 := bstep (se 1 (by rfl) ⟨102161, by rfl⟩ : syracuseStep 136215 = 204323) B204323
theorem B136235 : Blo 135790 136235 := bstep (se 1 (by rfl) ⟨102176, by rfl⟩ : syracuseStep 136235 = 204353) B204353
theorem B136247 : Blo 135790 136247 := bstep (se 1 (by rfl) ⟨102185, by rfl⟩ : syracuseStep 136247 = 204371) B204371
theorem B136267 : Blo 135790 136267 := bstep (se 1 (by rfl) ⟨102200, by rfl⟩ : syracuseStep 136267 = 204401) B204401
theorem B136279 : Blo 135790 136279 := bstep (se 1 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 136279 = 204419) B204419
theorem B136299 : Blo 135790 136299 := bstep (se 1 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 136299 = 204449) B204449
theorem B136311 : Blo 135790 136311 := bstep (se 1 (by rfl) ⟨102233, by rfl⟩ : syracuseStep 136311 = 204467) B204467
theorem B660611 : Blo 135790 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B136331 : Blo 135790 136331 := bstep (se 1 (by rfl) ⟨102248, by rfl⟩ : syracuseStep 136331 = 204497) B204497
theorem B562321 : Blo 135790 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B136343 : Blo 135790 136343 := bstep (se 1 (by rfl) ⟨102257, by rfl⟩ : syracuseStep 136343 = 204515) B204515
theorem B136363 : Blo 135790 136363 := bstep (se 1 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 136363 = 204545) B204545
theorem B136375 : Blo 135790 136375 := bstep (se 1 (by rfl) ⟨102281, by rfl⟩ : syracuseStep 136375 = 204563) B204563
theorem B136395 : Blo 135790 136395 := bstep (se 1 (by rfl) ⟨102296, by rfl⟩ : syracuseStep 136395 = 204593) B204593
theorem B464075 : Blo 135790 464075 := bstep (se 1 (by rfl) ⟨348056, by rfl⟩ : syracuseStep 464075 = 696113) B696113
theorem B136407 : Blo 135790 136407 := bstep (se 1 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 136407 = 204611) B204611
theorem B136427 : Blo 135790 136427 := bstep (se 1 (by rfl) ⟨102320, by rfl⟩ : syracuseStep 136427 = 204641) B204641
theorem B136439 : Blo 135790 136439 := bstep (se 1 (by rfl) ⟨102329, by rfl⟩ : syracuseStep 136439 = 204659) B204659
theorem B136459 : Blo 135790 136459 := bstep (se 1 (by rfl) ⟨102344, by rfl⟩ : syracuseStep 136459 = 204689) B204689
theorem B693521 : Blo 135790 693521 := bstep (se 2 (by rfl) ⟨260070, by rfl⟩ : syracuseStep 693521 = 520141) B520141
theorem B136471 : Blo 135790 136471 := bstep (se 1 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 136471 = 204707) B204707
theorem B136491 : Blo 135790 136491 := bstep (se 1 (by rfl) ⟨102368, by rfl⟩ : syracuseStep 136491 = 204737) B204737
theorem B136503 : Blo 135790 136503 := bstep (se 1 (by rfl) ⟨102377, by rfl⟩ : syracuseStep 136503 = 204755) B204755
theorem B136523 : Blo 135790 136523 := bstep (se 1 (by rfl) ⟨102392, by rfl⟩ : syracuseStep 136523 = 204785) B204785
theorem B136535 : Blo 135790 136535 := bstep (se 1 (by rfl) ⟨102401, by rfl⟩ : syracuseStep 136535 = 204803) B204803
theorem B234839 : Blo 135790 234839 := bstep (se 1 (by rfl) ⟨176129, by rfl⟩ : syracuseStep 234839 = 352259) B352259
theorem B1086821 : Blo 135790 1086821 := bstep (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) B203779
theorem B136555 : Blo 135790 136555 := bstep (se 1 (by rfl) ⟨102416, by rfl⟩ : syracuseStep 136555 = 204833) B204833
theorem B136567 : Blo 135790 136567 := bstep (se 1 (by rfl) ⟨102425, by rfl⟩ : syracuseStep 136567 = 204851) B204851
theorem B136587 : Blo 135790 136587 := bstep (se 1 (by rfl) ⟨102440, by rfl⟩ : syracuseStep 136587 = 204881) B204881
theorem B136599 : Blo 135790 136599 := bstep (se 1 (by rfl) ⟨102449, by rfl⟩ : syracuseStep 136599 = 204899) B204899
theorem B136619 : Blo 135790 136619 := bstep (se 1 (by rfl) ⟨102464, by rfl⟩ : syracuseStep 136619 = 204929) B204929
theorem B693683 : Blo 135790 693683 := bstep (se 1 (by rfl) ⟨520262, by rfl⟩ : syracuseStep 693683 = 1040525) B1040525
theorem B136631 : Blo 135790 136631 := bstep (se 1 (by rfl) ⟨102473, by rfl⟩ : syracuseStep 136631 = 204947) B204947
theorem B136651 : Blo 135790 136651 := bstep (se 1 (by rfl) ⟨102488, by rfl⟩ : syracuseStep 136651 = 204977) B204977
theorem B136663 : Blo 135790 136663 := bstep (se 1 (by rfl) ⟨102497, by rfl⟩ : syracuseStep 136663 = 204995) B204995
theorem B234967 : Blo 135790 234967 := bstep (se 1 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 234967 = 352451) B352451
theorem B464345 : Blo 135790 464345 := bstep (se 2 (by rfl) ⟨174129, by rfl⟩ : syracuseStep 464345 = 348259) B348259
theorem B136683 : Blo 135790 136683 := bstep (se 1 (by rfl) ⟨102512, by rfl⟩ : syracuseStep 136683 = 205025) B205025
theorem B136695 : Blo 135790 136695 := bstep (se 1 (by rfl) ⟨102521, by rfl⟩ : syracuseStep 136695 = 205043) B205043
theorem B136715 : Blo 135790 136715 := bstep (se 1 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 136715 = 205073) B205073
theorem B136727 : Blo 135790 136727 := bstep (se 1 (by rfl) ⟨102545, by rfl⟩ : syracuseStep 136727 = 205091) B205091
theorem B136747 : Blo 135790 136747 := bstep (se 1 (by rfl) ⟨102560, by rfl⟩ : syracuseStep 136747 = 205121) B205121
theorem B136759 : Blo 135790 136759 := bstep (se 1 (by rfl) ⟨102569, by rfl⟩ : syracuseStep 136759 = 205139) B205139
theorem B136779 : Blo 135790 136779 := bstep (se 1 (by rfl) ⟨102584, by rfl⟩ : syracuseStep 136779 = 205169) B205169
theorem B792139 : Blo 135790 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B136791 : Blo 135790 136791 := bstep (se 1 (by rfl) ⟨102593, by rfl⟩ : syracuseStep 136791 = 205187) B205187
theorem B136811 : Blo 135790 136811 := bstep (se 1 (by rfl) ⟨102608, by rfl⟩ : syracuseStep 136811 = 205217) B205217
theorem B136823 : Blo 135790 136823 := bstep (se 1 (by rfl) ⟨102617, by rfl⟩ : syracuseStep 136823 = 205235) B205235
theorem B136843 : Blo 135790 136843 := bstep (se 1 (by rfl) ⟨102632, by rfl⟩ : syracuseStep 136843 = 205265) B205265
theorem B136855 : Blo 135790 136855 := bstep (se 1 (by rfl) ⟨102641, by rfl⟩ : syracuseStep 136855 = 205283) B205283
theorem B136875 : Blo 135790 136875 := bstep (se 1 (by rfl) ⟨102656, by rfl⟩ : syracuseStep 136875 = 205313) B205313
theorem B136887 : Blo 135790 136887 := bstep (se 1 (by rfl) ⟨102665, by rfl⟩ : syracuseStep 136887 = 205331) B205331
theorem B136907 : Blo 135790 136907 := bstep (se 1 (by rfl) ⟨102680, by rfl⟩ : syracuseStep 136907 = 205361) B205361
theorem B136919 : Blo 135790 136919 := bstep (se 1 (by rfl) ⟨102689, by rfl⟩ : syracuseStep 136919 = 205379) B205379
theorem B136939 : Blo 135790 136939 := bstep (se 1 (by rfl) ⟨102704, by rfl⟩ : syracuseStep 136939 = 205409) B205409
theorem B136951 : Blo 135790 136951 := bstep (se 1 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 136951 = 205427) B205427
theorem B136971 : Blo 135790 136971 := bstep (se 1 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 136971 = 205457) B205457
theorem B136983 : Blo 135790 136983 := bstep (se 1 (by rfl) ⟨102737, by rfl⟩ : syracuseStep 136983 = 205475) B205475
theorem B137003 : Blo 135790 137003 := bstep (se 1 (by rfl) ⟨102752, by rfl⟩ : syracuseStep 137003 = 205505) B205505
theorem B137015 : Blo 135790 137015 := bstep (se 1 (by rfl) ⟨102761, by rfl⟩ : syracuseStep 137015 = 205523) B205523
theorem B137035 : Blo 135790 137035 := bstep (se 1 (by rfl) ⟨102776, by rfl⟩ : syracuseStep 137035 = 205553) B205553
theorem B137047 : Blo 135790 137047 := bstep (se 1 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 137047 = 205571) B205571
theorem B137067 : Blo 135790 137067 := bstep (se 1 (by rfl) ⟨102800, by rfl⟩ : syracuseStep 137067 = 205601) B205601
theorem B137079 : Blo 135790 137079 := bstep (se 1 (by rfl) ⟨102809, by rfl⟩ : syracuseStep 137079 = 205619) B205619
theorem B137099 : Blo 135790 137099 := bstep (se 1 (by rfl) ⟨102824, by rfl⟩ : syracuseStep 137099 = 205649) B205649
theorem B137111 : Blo 135790 137111 := bstep (se 1 (by rfl) ⟨102833, by rfl⟩ : syracuseStep 137111 = 205667) B205667
theorem B137131 : Blo 135790 137131 := bstep (se 1 (by rfl) ⟨102848, by rfl⟩ : syracuseStep 137131 = 205697) B205697
theorem B137143 : Blo 135790 137143 := bstep (se 1 (by rfl) ⟨102857, by rfl⟩ : syracuseStep 137143 = 205715) B205715
theorem B137163 : Blo 135790 137163 := bstep (se 1 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 137163 = 205745) B205745
theorem B137175 : Blo 135790 137175 := bstep (se 1 (by rfl) ⟨102881, by rfl⟩ : syracuseStep 137175 = 205763) B205763
theorem B137195 : Blo 135790 137195 := bstep (se 1 (by rfl) ⟨102896, by rfl⟩ : syracuseStep 137195 = 205793) B205793
theorem B137207 : Blo 135790 137207 := bstep (se 1 (by rfl) ⟨102905, by rfl⟩ : syracuseStep 137207 = 205811) B205811
theorem B137227 : Blo 135790 137227 := bstep (se 1 (by rfl) ⟨102920, by rfl⟩ : syracuseStep 137227 = 205841) B205841
theorem B137239 : Blo 135790 137239 := bstep (se 1 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 137239 = 205859) B205859
theorem B137259 : Blo 135790 137259 := bstep (se 1 (by rfl) ⟨102944, by rfl⟩ : syracuseStep 137259 = 205889) B205889
theorem B137271 : Blo 135790 137271 := bstep (se 1 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 137271 = 205907) B205907
theorem B5150789 : Blo 135790 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B8198213 : Blo 135790 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B137291 : Blo 135790 137291 := bstep (se 1 (by rfl) ⟨102968, by rfl⟩ : syracuseStep 137291 = 205937) B205937
theorem B235595 : Blo 135790 235595 := bstep (se 1 (by rfl) ⟨176696, by rfl⟩ : syracuseStep 235595 = 353393) B353393
theorem B137303 : Blo 135790 137303 := bstep (se 1 (by rfl) ⟨102977, by rfl⟩ : syracuseStep 137303 = 205955) B205955
theorem B137323 : Blo 135790 137323 := bstep (se 1 (by rfl) ⟨102992, by rfl⟩ : syracuseStep 137323 = 205985) B205985
theorem B137335 : Blo 135790 137335 := bstep (se 1 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 137335 = 206003) B206003
theorem B137355 : Blo 135790 137355 := bstep (se 1 (by rfl) ⟨103016, by rfl⟩ : syracuseStep 137355 = 206033) B206033
theorem B137367 : Blo 135790 137367 := bstep (se 1 (by rfl) ⟨103025, by rfl⟩ : syracuseStep 137367 = 206051) B206051
theorem B465047 : Blo 135790 465047 := bstep (se 1 (by rfl) ⟨348785, by rfl⟩ : syracuseStep 465047 = 697571) B697571
theorem B137387 : Blo 135790 137387 := bstep (se 1 (by rfl) ⟨103040, by rfl⟩ : syracuseStep 137387 = 206081) B206081
theorem B137399 : Blo 135790 137399 := bstep (se 1 (by rfl) ⟨103049, by rfl⟩ : syracuseStep 137399 = 206099) B206099
theorem B137419 : Blo 135790 137419 := bstep (se 1 (by rfl) ⟨103064, by rfl⟩ : syracuseStep 137419 = 206129) B206129
theorem B235723 : Blo 135790 235723 := bstep (se 1 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 235723 = 353585) B353585
theorem B137431 : Blo 135790 137431 := bstep (se 1 (by rfl) ⟨103073, by rfl⟩ : syracuseStep 137431 = 206147) B206147
theorem B137451 : Blo 135790 137451 := bstep (se 1 (by rfl) ⟨103088, by rfl⟩ : syracuseStep 137451 = 206177) B206177
theorem B137463 : Blo 135790 137463 := bstep (se 1 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 137463 = 206195) B206195
theorem B137483 : Blo 135790 137483 := bstep (se 1 (by rfl) ⟨103112, by rfl⟩ : syracuseStep 137483 = 206225) B206225
theorem B137495 : Blo 135790 137495 := bstep (se 1 (by rfl) ⟨103121, by rfl⟩ : syracuseStep 137495 = 206243) B206243
theorem B137515 : Blo 135790 137515 := bstep (se 1 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 137515 = 206273) B206273
theorem B137527 : Blo 135790 137527 := bstep (se 1 (by rfl) ⟨103145, by rfl⟩ : syracuseStep 137527 = 206291) B206291
theorem B268609 : Blo 135790 268609 := bstep (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) B201457
theorem B137547 : Blo 135790 137547 := bstep (se 1 (by rfl) ⟨103160, by rfl⟩ : syracuseStep 137547 = 206321) B206321
theorem B137559 : Blo 135790 137559 := bstep (se 1 (by rfl) ⟨103169, by rfl⟩ : syracuseStep 137559 = 206339) B206339
theorem B235865 : Blo 135790 235865 := bstep (se 2 (by rfl) ⟨88449, by rfl⟩ : syracuseStep 235865 = 176899) B176899
theorem B137579 : Blo 135790 137579 := bstep (se 1 (by rfl) ⟨103184, by rfl⟩ : syracuseStep 137579 = 206369) B206369
theorem B137591 : Blo 135790 137591 := bstep (se 1 (by rfl) ⟨103193, by rfl⟩ : syracuseStep 137591 = 206387) B206387
theorem B137611 : Blo 135790 137611 := bstep (se 1 (by rfl) ⟨103208, by rfl⟩ : syracuseStep 137611 = 206417) B206417
theorem B137623 : Blo 135790 137623 := bstep (se 1 (by rfl) ⟨103217, by rfl⟩ : syracuseStep 137623 = 206435) B206435
theorem B137643 : Blo 135790 137643 := bstep (se 1 (by rfl) ⟨103232, by rfl⟩ : syracuseStep 137643 = 206465) B206465
theorem B1743281 : Blo 135790 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B137655 : Blo 135790 137655 := bstep (se 1 (by rfl) ⟨103241, by rfl⟩ : syracuseStep 137655 = 206483) B206483
theorem B498113 : Blo 135790 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B137675 : Blo 135790 137675 := bstep (se 1 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 137675 = 206513) B206513
theorem B137687 : Blo 135790 137687 := bstep (se 1 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 137687 = 206531) B206531
theorem B137707 : Blo 135790 137707 := bstep (se 1 (by rfl) ⟨103280, by rfl⟩ : syracuseStep 137707 = 206561) B206561
theorem B137719 : Blo 135790 137719 := bstep (se 1 (by rfl) ⟨103289, by rfl⟩ : syracuseStep 137719 = 206579) B206579
theorem B137739 : Blo 135790 137739 := bstep (se 1 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 137739 = 206609) B206609
theorem B137751 : Blo 135790 137751 := bstep (se 1 (by rfl) ⟨103313, by rfl⟩ : syracuseStep 137751 = 206627) B206627
theorem B137771 : Blo 135790 137771 := bstep (se 1 (by rfl) ⟨103328, by rfl⟩ : syracuseStep 137771 = 206657) B206657
theorem B137783 : Blo 135790 137783 := bstep (se 1 (by rfl) ⟨103337, by rfl⟩ : syracuseStep 137783 = 206675) B206675
theorem B137803 : Blo 135790 137803 := bstep (se 1 (by rfl) ⟨103352, by rfl⟩ : syracuseStep 137803 = 206705) B206705
theorem B137815 : Blo 135790 137815 := bstep (se 1 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 137815 = 206723) B206723
theorem B137835 : Blo 135790 137835 := bstep (se 1 (by rfl) ⟨103376, by rfl⟩ : syracuseStep 137835 = 206753) B206753
theorem B137847 : Blo 135790 137847 := bstep (se 1 (by rfl) ⟨103385, by rfl⟩ : syracuseStep 137847 = 206771) B206771
theorem B137867 : Blo 135790 137867 := bstep (se 1 (by rfl) ⟨103400, by rfl⟩ : syracuseStep 137867 = 206801) B206801
theorem B137879 : Blo 135790 137879 := bstep (se 1 (by rfl) ⟨103409, by rfl⟩ : syracuseStep 137879 = 206819) B206819
theorem B137899 : Blo 135790 137899 := bstep (se 1 (by rfl) ⟨103424, by rfl⟩ : syracuseStep 137899 = 206849) B206849
theorem B465587 : Blo 135790 465587 := bstep (se 1 (by rfl) ⟨349190, by rfl⟩ : syracuseStep 465587 = 698381) B698381
theorem B137911 : Blo 135790 137911 := bstep (se 1 (by rfl) ⟨103433, by rfl⟩ : syracuseStep 137911 = 206867) B206867
theorem B137931 : Blo 135790 137931 := bstep (se 1 (by rfl) ⟨103448, by rfl⟩ : syracuseStep 137931 = 206897) B206897
theorem B137943 : Blo 135790 137943 := bstep (se 1 (by rfl) ⟨103457, by rfl⟩ : syracuseStep 137943 = 206915) B206915
theorem B1252057 : Blo 135790 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B137963 : Blo 135790 137963 := bstep (se 1 (by rfl) ⟨103472, by rfl⟩ : syracuseStep 137963 = 206945) B206945
theorem B137975 : Blo 135790 137975 := bstep (se 1 (by rfl) ⟨103481, by rfl⟩ : syracuseStep 137975 = 206963) B206963
theorem B137995 : Blo 135790 137995 := bstep (se 1 (by rfl) ⟨103496, by rfl⟩ : syracuseStep 137995 = 206993) B206993
theorem B138007 : Blo 135790 138007 := bstep (se 1 (by rfl) ⟨103505, by rfl⟩ : syracuseStep 138007 = 207011) B207011
theorem B138027 : Blo 135790 138027 := bstep (se 1 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 138027 = 207041) B207041
theorem B629549 : Blo 135790 629549 := bstep (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) B236081
theorem B138039 : Blo 135790 138039 := bstep (se 1 (by rfl) ⟨103529, by rfl⟩ : syracuseStep 138039 = 207059) B207059
theorem B138059 : Blo 135790 138059 := bstep (se 1 (by rfl) ⟨103544, by rfl⟩ : syracuseStep 138059 = 207089) B207089
theorem B138071 : Blo 135790 138071 := bstep (se 1 (by rfl) ⟨103553, by rfl⟩ : syracuseStep 138071 = 207107) B207107
theorem B138091 : Blo 135790 138091 := bstep (se 1 (by rfl) ⟨103568, by rfl⟩ : syracuseStep 138091 = 207137) B207137
theorem B138103 : Blo 135790 138103 := bstep (se 1 (by rfl) ⟨103577, by rfl⟩ : syracuseStep 138103 = 207155) B207155
theorem B138123 : Blo 135790 138123 := bstep (se 1 (by rfl) ⟨103592, by rfl⟩ : syracuseStep 138123 = 207185) B207185
theorem B138135 : Blo 135790 138135 := bstep (se 1 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 138135 = 207203) B207203
theorem B138155 : Blo 135790 138155 := bstep (se 1 (by rfl) ⟨103616, by rfl⟩ : syracuseStep 138155 = 207233) B207233
theorem B596915 : Blo 135790 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B138167 : Blo 135790 138167 := bstep (se 1 (by rfl) ⟨103625, by rfl⟩ : syracuseStep 138167 = 207251) B207251
theorem B465857 : Blo 135790 465857 := bstep (se 2 (by rfl) ⟨174696, by rfl⟩ : syracuseStep 465857 = 349393) B349393
theorem B203723 : Blo 135790 203723 := bstep (se 1 (by rfl) ⟨152792, by rfl⟩ : syracuseStep 203723 = 305585) B305585
theorem B138187 : Blo 135790 138187 := bstep (se 1 (by rfl) ⟨103640, by rfl⟩ : syracuseStep 138187 = 207281) B207281
theorem B203735 : Blo 135790 203735 := bstep (se 1 (by rfl) ⟨152801, by rfl⟩ : syracuseStep 203735 = 305603) B305603
theorem B138199 : Blo 135790 138199 := bstep (se 1 (by rfl) ⟨103649, by rfl⟩ : syracuseStep 138199 = 207299) B207299
theorem B138219 : Blo 135790 138219 := bstep (se 1 (by rfl) ⟨103664, by rfl⟩ : syracuseStep 138219 = 207329) B207329
theorem B138231 : Blo 135790 138231 := bstep (se 1 (by rfl) ⟨103673, by rfl⟩ : syracuseStep 138231 = 207347) B207347
theorem B138251 : Blo 135790 138251 := bstep (se 1 (by rfl) ⟨103688, by rfl⟩ : syracuseStep 138251 = 207377) B207377
theorem B138263 : Blo 135790 138263 := bstep (se 1 (by rfl) ⟨103697, by rfl⟩ : syracuseStep 138263 = 207395) B207395
theorem B203801 : Blo 135790 203801 := bstep (se 2 (by rfl) ⟨76425, by rfl⟩ : syracuseStep 203801 = 152851) B152851
theorem B138283 : Blo 135790 138283 := bstep (se 1 (by rfl) ⟨103712, by rfl⟩ : syracuseStep 138283 = 207425) B207425
theorem B138295 : Blo 135790 138295 := bstep (se 1 (by rfl) ⟨103721, by rfl⟩ : syracuseStep 138295 = 207443) B207443
theorem B662593 : Blo 135790 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B138315 : Blo 135790 138315 := bstep (se 1 (by rfl) ⟨103736, by rfl⟩ : syracuseStep 138315 = 207473) B207473
theorem B138327 : Blo 135790 138327 := bstep (se 1 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 138327 = 207491) B207491
theorem B138347 : Blo 135790 138347 := bstep (se 1 (by rfl) ⟨103760, by rfl⟩ : syracuseStep 138347 = 207521) B207521
theorem B138359 : Blo 135790 138359 := bstep (se 1 (by rfl) ⟨103769, by rfl⟩ : syracuseStep 138359 = 207539) B207539
theorem B203915 : Blo 135790 203915 := bstep (se 1 (by rfl) ⟨152936, by rfl⟩ : syracuseStep 203915 = 305873) B305873
theorem B138379 : Blo 135790 138379 := bstep (se 1 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 138379 = 207569) B207569
theorem B203927 : Blo 135790 203927 := bstep (se 1 (by rfl) ⟨152945, by rfl⟩ : syracuseStep 203927 = 305891) B305891
theorem B138391 : Blo 135790 138391 := bstep (se 1 (by rfl) ⟨103793, by rfl⟩ : syracuseStep 138391 = 207587) B207587
theorem B138411 : Blo 135790 138411 := bstep (se 1 (by rfl) ⟨103808, by rfl⟩ : syracuseStep 138411 = 207617) B207617
theorem B138423 : Blo 135790 138423 := bstep (se 1 (by rfl) ⟨103817, by rfl⟩ : syracuseStep 138423 = 207635) B207635
theorem B138443 : Blo 135790 138443 := bstep (se 1 (by rfl) ⟨103832, by rfl⟩ : syracuseStep 138443 = 207665) B207665
theorem B138455 : Blo 135790 138455 := bstep (se 1 (by rfl) ⟨103841, by rfl⟩ : syracuseStep 138455 = 207683) B207683
theorem B203993 : Blo 135790 203993 := bstep (se 2 (by rfl) ⟨76497, by rfl⟩ : syracuseStep 203993 = 152995) B152995
theorem B138475 : Blo 135790 138475 := bstep (se 1 (by rfl) ⟨103856, by rfl⟩ : syracuseStep 138475 = 207713) B207713
theorem B138487 : Blo 135790 138487 := bstep (se 1 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 138487 = 207731) B207731
theorem B138507 : Blo 135790 138507 := bstep (se 1 (by rfl) ⟨103880, by rfl⟩ : syracuseStep 138507 = 207761) B207761
theorem B138519 : Blo 135790 138519 := bstep (se 1 (by rfl) ⟨103889, by rfl⟩ : syracuseStep 138519 = 207779) B207779
theorem B138539 : Blo 135790 138539 := bstep (se 1 (by rfl) ⟨103904, by rfl⟩ : syracuseStep 138539 = 207809) B207809
theorem B138551 : Blo 135790 138551 := bstep (se 1 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 138551 = 207827) B207827
theorem B204107 : Blo 135790 204107 := bstep (se 1 (by rfl) ⟨153080, by rfl⟩ : syracuseStep 204107 = 306161) B306161
theorem B695627 : Blo 135790 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B138571 : Blo 135790 138571 := bstep (se 1 (by rfl) ⟨103928, by rfl⟩ : syracuseStep 138571 = 207857) B207857
theorem B204119 : Blo 135790 204119 := bstep (se 1 (by rfl) ⟨153089, by rfl⟩ : syracuseStep 204119 = 306179) B306179
theorem B138583 : Blo 135790 138583 := bstep (se 1 (by rfl) ⟨103937, by rfl⟩ : syracuseStep 138583 = 207875) B207875
theorem B367961 : Blo 135790 367961 := bstep (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) B275971
theorem B138603 : Blo 135790 138603 := bstep (se 1 (by rfl) ⟨103952, by rfl⟩ : syracuseStep 138603 = 207905) B207905
theorem B138615 : Blo 135790 138615 := bstep (se 1 (by rfl) ⟨103961, by rfl⟩ : syracuseStep 138615 = 207923) B207923
theorem B138635 : Blo 135790 138635 := bstep (se 1 (by rfl) ⟨103976, by rfl⟩ : syracuseStep 138635 = 207953) B207953
theorem B138647 : Blo 135790 138647 := bstep (se 1 (by rfl) ⟨103985, by rfl⟩ : syracuseStep 138647 = 207971) B207971
theorem B204185 : Blo 135790 204185 := bstep (se 2 (by rfl) ⟨76569, by rfl⟩ : syracuseStep 204185 = 153139) B153139
theorem B138667 : Blo 135790 138667 := bstep (se 1 (by rfl) ⟨104000, by rfl⟩ : syracuseStep 138667 = 208001) B208001
theorem B138679 : Blo 135790 138679 := bstep (se 1 (by rfl) ⟨104009, by rfl⟩ : syracuseStep 138679 = 208019) B208019
theorem B138699 : Blo 135790 138699 := bstep (se 1 (by rfl) ⟨104024, by rfl⟩ : syracuseStep 138699 = 208049) B208049
theorem B138711 : Blo 135790 138711 := bstep (se 1 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 138711 = 208067) B208067
theorem B466397 : Blo 135790 466397 := bstep (se 3 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 466397 = 174899) B174899
theorem B138731 : Blo 135790 138731 := bstep (se 1 (by rfl) ⟨104048, by rfl⟩ : syracuseStep 138731 = 208097) B208097
theorem B138743 : Blo 135790 138743 := bstep (se 1 (by rfl) ⟨104057, by rfl⟩ : syracuseStep 138743 = 208115) B208115
theorem B204299 : Blo 135790 204299 := bstep (se 1 (by rfl) ⟨153224, by rfl⟩ : syracuseStep 204299 = 306449) B306449
theorem B138763 : Blo 135790 138763 := bstep (se 1 (by rfl) ⟨104072, by rfl⟩ : syracuseStep 138763 = 208145) B208145
theorem B204311 : Blo 135790 204311 := bstep (se 1 (by rfl) ⟨153233, by rfl⟩ : syracuseStep 204311 = 306467) B306467
theorem B138775 : Blo 135790 138775 := bstep (se 1 (by rfl) ⟨104081, by rfl⟩ : syracuseStep 138775 = 208163) B208163
theorem B138795 : Blo 135790 138795 := bstep (se 1 (by rfl) ⟨104096, by rfl⟩ : syracuseStep 138795 = 208193) B208193
theorem B138807 : Blo 135790 138807 := bstep (se 1 (by rfl) ⟨104105, by rfl⟩ : syracuseStep 138807 = 208211) B208211
theorem B138827 : Blo 135790 138827 := bstep (se 1 (by rfl) ⟨104120, by rfl⟩ : syracuseStep 138827 = 208241) B208241
theorem B138839 : Blo 135790 138839 := bstep (se 1 (by rfl) ⟨104129, by rfl⟩ : syracuseStep 138839 = 208259) B208259
theorem B204377 : Blo 135790 204377 := bstep (se 2 (by rfl) ⟨76641, by rfl⟩ : syracuseStep 204377 = 153283) B153283
theorem B368221 : Blo 135790 368221 := bstep (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) B138083
theorem B138859 : Blo 135790 138859 := bstep (se 1 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 138859 = 208289) B208289
theorem B138871 : Blo 135790 138871 := bstep (se 1 (by rfl) ⟨104153, by rfl⟩ : syracuseStep 138871 = 208307) B208307
theorem B138891 : Blo 135790 138891 := bstep (se 1 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 138891 = 208337) B208337
theorem B138903 : Blo 135790 138903 := bstep (se 1 (by rfl) ⟨104177, by rfl⟩ : syracuseStep 138903 = 208355) B208355
theorem B138923 : Blo 135790 138923 := bstep (se 1 (by rfl) ⟨104192, by rfl⟩ : syracuseStep 138923 = 208385) B208385
theorem B138935 : Blo 135790 138935 := bstep (se 1 (by rfl) ⟨104201, by rfl⟩ : syracuseStep 138935 = 208403) B208403
theorem B204491 : Blo 135790 204491 := bstep (se 1 (by rfl) ⟨153368, by rfl⟩ : syracuseStep 204491 = 306737) B306737
theorem B138955 : Blo 135790 138955 := bstep (se 1 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 138955 = 208433) B208433
theorem B204503 : Blo 135790 204503 := bstep (se 1 (by rfl) ⟨153377, by rfl⟩ : syracuseStep 204503 = 306755) B306755
theorem B138967 : Blo 135790 138967 := bstep (se 1 (by rfl) ⟨104225, by rfl⟩ : syracuseStep 138967 = 208451) B208451
theorem B138987 : Blo 135790 138987 := bstep (se 1 (by rfl) ⟨104240, by rfl⟩ : syracuseStep 138987 = 208481) B208481
theorem B138999 : Blo 135790 138999 := bstep (se 1 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 138999 = 208499) B208499
theorem B139019 : Blo 135790 139019 := bstep (se 1 (by rfl) ⟨104264, by rfl⟩ : syracuseStep 139019 = 208529) B208529
theorem B139031 : Blo 135790 139031 := bstep (se 1 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 139031 = 208547) B208547
theorem B204569 : Blo 135790 204569 := bstep (se 2 (by rfl) ⟨76713, by rfl⟩ : syracuseStep 204569 = 153427) B153427
theorem B139051 : Blo 135790 139051 := bstep (se 1 (by rfl) ⟨104288, by rfl⟩ : syracuseStep 139051 = 208577) B208577
theorem B139063 : Blo 135790 139063 := bstep (se 1 (by rfl) ⟨104297, by rfl⟩ : syracuseStep 139063 = 208595) B208595
theorem B139083 : Blo 135790 139083 := bstep (se 1 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 139083 = 208625) B208625
theorem B139095 : Blo 135790 139095 := bstep (se 1 (by rfl) ⟨104321, by rfl⟩ : syracuseStep 139095 = 208643) B208643
theorem B139115 : Blo 135790 139115 := bstep (se 1 (by rfl) ⟨104336, by rfl⟩ : syracuseStep 139115 = 208673) B208673
theorem B139127 : Blo 135790 139127 := bstep (se 1 (by rfl) ⟨104345, by rfl⟩ : syracuseStep 139127 = 208691) B208691
theorem B204683 : Blo 135790 204683 := bstep (se 1 (by rfl) ⟨153512, by rfl⟩ : syracuseStep 204683 = 307025) B307025
theorem B139147 : Blo 135790 139147 := bstep (se 1 (by rfl) ⟨104360, by rfl⟩ : syracuseStep 139147 = 208721) B208721
theorem B204695 : Blo 135790 204695 := bstep (se 1 (by rfl) ⟨153521, by rfl⟩ : syracuseStep 204695 = 307043) B307043
theorem B139159 : Blo 135790 139159 := bstep (se 1 (by rfl) ⟨104369, by rfl⟩ : syracuseStep 139159 = 208739) B208739
theorem B794519 : Blo 135790 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B139179 : Blo 135790 139179 := bstep (se 1 (by rfl) ⟨104384, by rfl⟩ : syracuseStep 139179 = 208769) B208769
theorem B139191 : Blo 135790 139191 := bstep (se 1 (by rfl) ⟨104393, by rfl⟩ : syracuseStep 139191 = 208787) B208787
theorem B139211 : Blo 135790 139211 := bstep (se 1 (by rfl) ⟨104408, by rfl⟩ : syracuseStep 139211 = 208817) B208817
theorem B139223 : Blo 135790 139223 := bstep (se 1 (by rfl) ⟨104417, by rfl⟩ : syracuseStep 139223 = 208835) B208835
theorem B204761 : Blo 135790 204761 := bstep (se 2 (by rfl) ⟨76785, by rfl⟩ : syracuseStep 204761 = 153571) B153571
theorem B892889 : Blo 135790 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B139243 : Blo 135790 139243 := bstep (se 1 (by rfl) ⟨104432, by rfl⟩ : syracuseStep 139243 = 208865) B208865
theorem B139255 : Blo 135790 139255 := bstep (se 1 (by rfl) ⟨104441, by rfl⟩ : syracuseStep 139255 = 208883) B208883
theorem B499715 : Blo 135790 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B139275 : Blo 135790 139275 := bstep (se 1 (by rfl) ⟨104456, by rfl⟩ : syracuseStep 139275 = 208913) B208913
theorem B139287 : Blo 135790 139287 := bstep (se 1 (by rfl) ⟨104465, by rfl⟩ : syracuseStep 139287 = 208931) B208931
theorem B139307 : Blo 135790 139307 := bstep (se 1 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 139307 = 208961) B208961
theorem B139319 : Blo 135790 139319 := bstep (se 1 (by rfl) ⟨104489, by rfl⟩ : syracuseStep 139319 = 208979) B208979
theorem B204875 : Blo 135790 204875 := bstep (se 1 (by rfl) ⟨153656, by rfl⟩ : syracuseStep 204875 = 307313) B307313
theorem B139339 : Blo 135790 139339 := bstep (se 1 (by rfl) ⟨104504, by rfl⟩ : syracuseStep 139339 = 209009) B209009
theorem B204887 : Blo 135790 204887 := bstep (se 1 (by rfl) ⟨153665, by rfl⟩ : syracuseStep 204887 = 307331) B307331
theorem B139351 : Blo 135790 139351 := bstep (se 1 (by rfl) ⟨104513, by rfl⟩ : syracuseStep 139351 = 209027) B209027
theorem B139371 : Blo 135790 139371 := bstep (se 1 (by rfl) ⟨104528, by rfl⟩ : syracuseStep 139371 = 209057) B209057
theorem B139383 : Blo 135790 139383 := bstep (se 1 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 139383 = 209075) B209075
theorem B139403 : Blo 135790 139403 := bstep (se 1 (by rfl) ⟨104552, by rfl⟩ : syracuseStep 139403 = 209105) B209105
theorem B139415 : Blo 135790 139415 := bstep (se 1 (by rfl) ⟨104561, by rfl⟩ : syracuseStep 139415 = 209123) B209123
theorem B204953 : Blo 135790 204953 := bstep (se 2 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 204953 = 153715) B153715
theorem B139435 : Blo 135790 139435 := bstep (se 1 (by rfl) ⟨104576, by rfl⟩ : syracuseStep 139435 = 209153) B209153
theorem B139447 : Blo 135790 139447 := bstep (se 1 (by rfl) ⟨104585, by rfl⟩ : syracuseStep 139447 = 209171) B209171
theorem B139467 : Blo 135790 139467 := bstep (se 1 (by rfl) ⟨104600, by rfl⟩ : syracuseStep 139467 = 209201) B209201
theorem B139479 : Blo 135790 139479 := bstep (se 1 (by rfl) ⟨104609, by rfl⟩ : syracuseStep 139479 = 209219) B209219
theorem B139499 : Blo 135790 139499 := bstep (se 1 (by rfl) ⟨104624, by rfl⟩ : syracuseStep 139499 = 209249) B209249
theorem B139511 : Blo 135790 139511 := bstep (se 1 (by rfl) ⟨104633, by rfl⟩ : syracuseStep 139511 = 209267) B209267
theorem B205067 : Blo 135790 205067 := bstep (se 1 (by rfl) ⟨153800, by rfl⟩ : syracuseStep 205067 = 307601) B307601
theorem B139531 : Blo 135790 139531 := bstep (se 1 (by rfl) ⟨104648, by rfl⟩ : syracuseStep 139531 = 209297) B209297
theorem B205079 : Blo 135790 205079 := bstep (se 1 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 205079 = 307619) B307619
theorem B139543 : Blo 135790 139543 := bstep (se 1 (by rfl) ⟨104657, by rfl⟩ : syracuseStep 139543 = 209315) B209315
theorem B139563 : Blo 135790 139563 := bstep (se 1 (by rfl) ⟨104672, by rfl⟩ : syracuseStep 139563 = 209345) B209345
theorem B139575 : Blo 135790 139575 := bstep (se 1 (by rfl) ⟨104681, by rfl⟩ : syracuseStep 139575 = 209363) B209363
theorem B172363 : Blo 135790 172363 := bstep (se 1 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 172363 = 258545) B258545
theorem B139595 : Blo 135790 139595 := bstep (se 1 (by rfl) ⟨104696, by rfl⟩ : syracuseStep 139595 = 209393) B209393
theorem B139607 : Blo 135790 139607 := bstep (se 1 (by rfl) ⟨104705, by rfl⟩ : syracuseStep 139607 = 209411) B209411
theorem B205145 : Blo 135790 205145 := bstep (se 2 (by rfl) ⟨76929, by rfl⟩ : syracuseStep 205145 = 153859) B153859
theorem B139627 : Blo 135790 139627 := bstep (se 1 (by rfl) ⟨104720, by rfl⟩ : syracuseStep 139627 = 209441) B209441
theorem B139639 : Blo 135790 139639 := bstep (se 1 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 139639 = 209459) B209459
theorem B139659 : Blo 135790 139659 := bstep (se 1 (by rfl) ⟨104744, by rfl⟩ : syracuseStep 139659 = 209489) B209489
theorem B139671 : Blo 135790 139671 := bstep (se 1 (by rfl) ⟨104753, by rfl⟩ : syracuseStep 139671 = 209507) B209507
theorem B139691 : Blo 135790 139691 := bstep (se 1 (by rfl) ⟨104768, by rfl⟩ : syracuseStep 139691 = 209537) B209537
theorem B139703 : Blo 135790 139703 := bstep (se 1 (by rfl) ⟨104777, by rfl⟩ : syracuseStep 139703 = 209555) B209555
theorem B205259 : Blo 135790 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B139723 : Blo 135790 139723 := bstep (se 1 (by rfl) ⟨104792, by rfl⟩ : syracuseStep 139723 = 209585) B209585
theorem B205271 : Blo 135790 205271 := bstep (se 1 (by rfl) ⟨153953, by rfl⟩ : syracuseStep 205271 = 307907) B307907
theorem B139735 : Blo 135790 139735 := bstep (se 1 (by rfl) ⟨104801, by rfl⟩ : syracuseStep 139735 = 209603) B209603
theorem B139755 : Blo 135790 139755 := bstep (se 1 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 139755 = 209633) B209633
theorem B139767 : Blo 135790 139767 := bstep (se 1 (by rfl) ⟨104825, by rfl⟩ : syracuseStep 139767 = 209651) B209651
theorem B139787 : Blo 135790 139787 := bstep (se 1 (by rfl) ⟨104840, by rfl⟩ : syracuseStep 139787 = 209681) B209681
theorem B205337 : Blo 135790 205337 := bstep (se 2 (by rfl) ⟨77001, by rfl⟩ : syracuseStep 205337 = 154003) B154003
theorem B565811 : Blo 135790 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B467531 : Blo 135790 467531 := bstep (se 1 (by rfl) ⟨350648, by rfl⟩ : syracuseStep 467531 = 701297) B701297
theorem B172631 : Blo 135790 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B205451 : Blo 135790 205451 := bstep (se 1 (by rfl) ⟨154088, by rfl⟩ : syracuseStep 205451 = 308177) B308177
theorem B205463 : Blo 135790 205463 := bstep (se 1 (by rfl) ⟨154097, by rfl⟩ : syracuseStep 205463 = 308195) B308195
theorem B205529 : Blo 135790 205529 := bstep (se 2 (by rfl) ⟨77073, by rfl⟩ : syracuseStep 205529 = 154147) B154147
theorem B205643 : Blo 135790 205643 := bstep (se 1 (by rfl) ⟨154232, by rfl⟩ : syracuseStep 205643 = 308465) B308465
theorem B205655 : Blo 135790 205655 := bstep (se 1 (by rfl) ⟨154241, by rfl⟩ : syracuseStep 205655 = 308483) B308483
theorem B467801 : Blo 135790 467801 := bstep (se 2 (by rfl) ⟨175425, by rfl⟩ : syracuseStep 467801 = 350851) B350851
theorem B205721 : Blo 135790 205721 := bstep (se 2 (by rfl) ⟨77145, by rfl⟩ : syracuseStep 205721 = 154291) B154291
theorem B205835 : Blo 135790 205835 := bstep (se 1 (by rfl) ⟨154376, by rfl⟩ : syracuseStep 205835 = 308753) B308753
theorem B205847 : Blo 135790 205847 := bstep (se 1 (by rfl) ⟨154385, by rfl⟩ : syracuseStep 205847 = 308771) B308771
theorem B697409 : Blo 135790 697409 := bstep (se 2 (by rfl) ⟨261528, by rfl⟩ : syracuseStep 697409 = 523057) B523057
theorem B205913 : Blo 135790 205913 := bstep (se 2 (by rfl) ⟨77217, by rfl⟩ : syracuseStep 205913 = 154435) B154435
theorem B206027 : Blo 135790 206027 := bstep (se 1 (by rfl) ⟨154520, by rfl⟩ : syracuseStep 206027 = 309041) B309041
theorem B206039 : Blo 135790 206039 := bstep (se 1 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 206039 = 309059) B309059
theorem B173335 : Blo 135790 173335 := bstep (se 1 (by rfl) ⟨130001, by rfl⟩ : syracuseStep 173335 = 260003) B260003
theorem B206105 : Blo 135790 206105 := bstep (se 2 (by rfl) ⟨77289, by rfl⟩ : syracuseStep 206105 = 154579) B154579
theorem B206219 : Blo 135790 206219 := bstep (se 1 (by rfl) ⟨154664, by rfl⟩ : syracuseStep 206219 = 309329) B309329
theorem B206231 : Blo 135790 206231 := bstep (se 1 (by rfl) ⟨154673, by rfl⟩ : syracuseStep 206231 = 309347) B309347
theorem B533953 : Blo 135790 533953 := bstep (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) B400465
theorem B206297 : Blo 135790 206297 := bstep (se 2 (by rfl) ⟨77361, by rfl⟩ : syracuseStep 206297 = 154723) B154723
theorem B468503 : Blo 135790 468503 := bstep (se 1 (by rfl) ⟨351377, by rfl⟩ : syracuseStep 468503 = 702755) B702755
theorem B206411 : Blo 135790 206411 := bstep (se 1 (by rfl) ⟨154808, by rfl⟩ : syracuseStep 206411 = 309617) B309617
theorem B206423 : Blo 135790 206423 := bstep (se 1 (by rfl) ⟨154817, by rfl⟩ : syracuseStep 206423 = 309635) B309635
theorem B206489 : Blo 135790 206489 := bstep (se 2 (by rfl) ⟨77433, by rfl⟩ : syracuseStep 206489 = 154867) B154867
theorem B206603 : Blo 135790 206603 := bstep (se 1 (by rfl) ⟨154952, by rfl⟩ : syracuseStep 206603 = 309905) B309905
theorem B206615 : Blo 135790 206615 := bstep (se 1 (by rfl) ⟨154961, by rfl⟩ : syracuseStep 206615 = 309923) B309923
theorem B206681 : Blo 135790 206681 := bstep (se 2 (by rfl) ⟨77505, by rfl⟩ : syracuseStep 206681 = 155011) B155011
theorem B829277 : Blo 135790 829277 := bstep (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) B310979
theorem B206795 : Blo 135790 206795 := bstep (se 1 (by rfl) ⟨155096, by rfl⟩ : syracuseStep 206795 = 310193) B310193
theorem B206807 : Blo 135790 206807 := bstep (se 1 (by rfl) ⟨155105, by rfl⟩ : syracuseStep 206807 = 310211) B310211
theorem B206873 : Blo 135790 206873 := bstep (se 2 (by rfl) ⟨77577, by rfl⟩ : syracuseStep 206873 = 155155) B155155
theorem B2009123 : Blo 135790 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B469043 : Blo 135790 469043 := bstep (se 1 (by rfl) ⟨351782, by rfl⟩ : syracuseStep 469043 = 703565) B703565
theorem B206987 : Blo 135790 206987 := bstep (se 1 (by rfl) ⟨155240, by rfl⟩ : syracuseStep 206987 = 310481) B310481
theorem B206999 : Blo 135790 206999 := bstep (se 1 (by rfl) ⟨155249, by rfl⟩ : syracuseStep 206999 = 310499) B310499
theorem B1058993 : Blo 135790 1058993 := bstep (se 2 (by rfl) ⟨397122, by rfl⟩ : syracuseStep 1058993 = 794245) B794245
theorem B633035 : Blo 135790 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B207065 : Blo 135790 207065 := bstep (se 2 (by rfl) ⟨77649, by rfl⟩ : syracuseStep 207065 = 155299) B155299
theorem B502033 : Blo 135790 502033 := bstep (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) B376525
theorem B469271 : Blo 135790 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B469313 : Blo 135790 469313 := bstep (se 2 (by rfl) ⟨175992, by rfl⟩ : syracuseStep 469313 = 351985) B351985
theorem B207179 : Blo 135790 207179 := bstep (se 1 (by rfl) ⟨155384, by rfl⟩ : syracuseStep 207179 = 310769) B310769
theorem B207191 : Blo 135790 207191 := bstep (se 1 (by rfl) ⟨155393, by rfl⟩ : syracuseStep 207191 = 310787) B310787
theorem B207257 : Blo 135790 207257 := bstep (se 2 (by rfl) ⟨77721, by rfl⟩ : syracuseStep 207257 = 155443) B155443
theorem B305675 : Blo 135790 305675 := bstep (se 1 (by rfl) ⟨229256, by rfl⟩ : syracuseStep 305675 = 458513) B458513
theorem B207371 : Blo 135790 207371 := bstep (se 1 (by rfl) ⟨155528, by rfl⟩ : syracuseStep 207371 = 311057) B311057
theorem B207383 : Blo 135790 207383 := bstep (se 1 (by rfl) ⟨155537, by rfl⟩ : syracuseStep 207383 = 311075) B311075
theorem B305729 : Blo 135790 305729 := bstep (se 2 (by rfl) ⟨114648, by rfl⟩ : syracuseStep 305729 = 229297) B229297
theorem B207449 : Blo 135790 207449 := bstep (se 2 (by rfl) ⟨77793, by rfl⟩ : syracuseStep 207449 = 155587) B155587
theorem B1059479 : Blo 135790 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B207563 : Blo 135790 207563 := bstep (se 1 (by rfl) ⟨155672, by rfl⟩ : syracuseStep 207563 = 311345) B311345
theorem B207575 : Blo 135790 207575 := bstep (se 1 (by rfl) ⟨155681, by rfl⟩ : syracuseStep 207575 = 311363) B311363
theorem B305945 : Blo 135790 305945 := bstep (se 2 (by rfl) ⟨114729, by rfl⟩ : syracuseStep 305945 = 229459) B229459
theorem B207641 : Blo 135790 207641 := bstep (se 2 (by rfl) ⟨77865, by rfl⟩ : syracuseStep 207641 = 155731) B155731
theorem B469853 : Blo 135790 469853 := bstep (se 3 (by rfl) ⟨88097, by rfl⟩ : syracuseStep 469853 = 176195) B176195
theorem B306035 : Blo 135790 306035 := bstep (se 1 (by rfl) ⟨229526, by rfl⟩ : syracuseStep 306035 = 459053) B459053
theorem B207755 : Blo 135790 207755 := bstep (se 1 (by rfl) ⟨155816, by rfl⟩ : syracuseStep 207755 = 311633) B311633
theorem B306071 : Blo 135790 306071 := bstep (se 1 (by rfl) ⟨229553, by rfl⟩ : syracuseStep 306071 = 459107) B459107
theorem B207767 : Blo 135790 207767 := bstep (se 1 (by rfl) ⟨155825, by rfl⟩ : syracuseStep 207767 = 311651) B311651
theorem B175051 : Blo 135790 175051 := bstep (se 1 (by rfl) ⟨131288, by rfl⟩ : syracuseStep 175051 = 262577) B262577
theorem B994265 : Blo 135790 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B699353 : Blo 135790 699353 := bstep (se 2 (by rfl) ⟨262257, by rfl⟩ : syracuseStep 699353 = 524515) B524515
theorem B207833 : Blo 135790 207833 := bstep (se 2 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 207833 = 155875) B155875
theorem B1256465 : Blo 135790 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B306251 : Blo 135790 306251 := bstep (se 1 (by rfl) ⟨229688, by rfl⟩ : syracuseStep 306251 = 459377) B459377
theorem B207947 : Blo 135790 207947 := bstep (se 1 (by rfl) ⟨155960, by rfl⟩ : syracuseStep 207947 = 311921) B311921
theorem B207959 : Blo 135790 207959 := bstep (se 1 (by rfl) ⟨155969, by rfl⟩ : syracuseStep 207959 = 311939) B311939
theorem B306305 : Blo 135790 306305 := bstep (se 2 (by rfl) ⟨114864, by rfl⟩ : syracuseStep 306305 = 229729) B229729
theorem B208025 : Blo 135790 208025 := bstep (se 2 (by rfl) ⟨78009, by rfl⟩ : syracuseStep 208025 = 156019) B156019
theorem B470195 : Blo 135790 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B208139 : Blo 135790 208139 := bstep (se 1 (by rfl) ⟨156104, by rfl⟩ : syracuseStep 208139 = 312209) B312209
theorem B208151 : Blo 135790 208151 := bstep (se 1 (by rfl) ⟨156113, by rfl⟩ : syracuseStep 208151 = 312227) B312227
theorem B306521 : Blo 135790 306521 := bstep (se 2 (by rfl) ⟨114945, by rfl⟩ : syracuseStep 306521 = 229891) B229891
theorem B208217 : Blo 135790 208217 := bstep (se 2 (by rfl) ⟨78081, by rfl⟩ : syracuseStep 208217 = 156163) B156163
theorem B306611 : Blo 135790 306611 := bstep (se 1 (by rfl) ⟨229958, by rfl⟩ : syracuseStep 306611 = 459917) B459917
theorem B208331 : Blo 135790 208331 := bstep (se 1 (by rfl) ⟨156248, by rfl⟩ : syracuseStep 208331 = 312497) B312497
theorem B306647 : Blo 135790 306647 := bstep (se 1 (by rfl) ⟨229985, by rfl⟩ : syracuseStep 306647 = 459971) B459971
theorem B208343 : Blo 135790 208343 := bstep (se 1 (by rfl) ⟨156257, by rfl⟩ : syracuseStep 208343 = 312515) B312515
theorem B208409 : Blo 135790 208409 := bstep (se 2 (by rfl) ⟨78153, by rfl⟩ : syracuseStep 208409 = 156307) B156307
theorem B306827 : Blo 135790 306827 := bstep (se 1 (by rfl) ⟨230120, by rfl⟩ : syracuseStep 306827 = 460241) B460241
theorem B208523 : Blo 135790 208523 := bstep (se 1 (by rfl) ⟨156392, by rfl⟩ : syracuseStep 208523 = 312785) B312785
theorem B208535 : Blo 135790 208535 := bstep (se 1 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 208535 = 312803) B312803
theorem B634547 : Blo 135790 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B306881 : Blo 135790 306881 := bstep (se 2 (by rfl) ⟨115080, by rfl⟩ : syracuseStep 306881 = 230161) B230161
theorem B1584845 : Blo 135790 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B208601 : Blo 135790 208601 := bstep (se 2 (by rfl) ⟨78225, by rfl⟩ : syracuseStep 208601 = 156451) B156451
theorem B208715 : Blo 135790 208715 := bstep (se 1 (by rfl) ⟨156536, by rfl⟩ : syracuseStep 208715 = 313073) B313073
theorem B208727 : Blo 135790 208727 := bstep (se 1 (by rfl) ⟨156545, by rfl⟩ : syracuseStep 208727 = 313091) B313091
theorem B176023 : Blo 135790 176023 := bstep (se 1 (by rfl) ⟨132017, by rfl⟩ : syracuseStep 176023 = 264035) B264035
theorem B307097 : Blo 135790 307097 := bstep (se 2 (by rfl) ⟨115161, by rfl⟩ : syracuseStep 307097 = 230323) B230323
theorem B208793 : Blo 135790 208793 := bstep (se 2 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 208793 = 156595) B156595
theorem B470987 : Blo 135790 470987 := bstep (se 1 (by rfl) ⟨353240, by rfl⟩ : syracuseStep 470987 = 706481) B706481
theorem B307187 : Blo 135790 307187 := bstep (se 1 (by rfl) ⟨230390, by rfl⟩ : syracuseStep 307187 = 460781) B460781
theorem B208907 : Blo 135790 208907 := bstep (se 1 (by rfl) ⟨156680, by rfl⟩ : syracuseStep 208907 = 313361) B313361
theorem B307223 : Blo 135790 307223 := bstep (se 1 (by rfl) ⟨230417, by rfl⟩ : syracuseStep 307223 = 460835) B460835
theorem B208919 : Blo 135790 208919 := bstep (se 1 (by rfl) ⟨156689, by rfl⟩ : syracuseStep 208919 = 313379) B313379
theorem B208985 : Blo 135790 208985 := bstep (se 2 (by rfl) ⟨78369, by rfl⟩ : syracuseStep 208985 = 156739) B156739
theorem B307403 : Blo 135790 307403 := bstep (se 1 (by rfl) ⟨230552, by rfl⟩ : syracuseStep 307403 = 461105) B461105
theorem B209099 : Blo 135790 209099 := bstep (se 1 (by rfl) ⟨156824, by rfl⟩ : syracuseStep 209099 = 313649) B313649
theorem B209111 : Blo 135790 209111 := bstep (se 1 (by rfl) ⟨156833, by rfl⟩ : syracuseStep 209111 = 313667) B313667
theorem B471257 : Blo 135790 471257 := bstep (se 2 (by rfl) ⟨176721, by rfl⟩ : syracuseStep 471257 = 353443) B353443
theorem B307457 : Blo 135790 307457 := bstep (se 2 (by rfl) ⟨115296, by rfl⟩ : syracuseStep 307457 = 230593) B230593
theorem B209177 : Blo 135790 209177 := bstep (se 2 (by rfl) ⟨78441, by rfl⟩ : syracuseStep 209177 = 156883) B156883
theorem B209291 : Blo 135790 209291 := bstep (se 1 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 209291 = 313937) B313937
theorem B209303 : Blo 135790 209303 := bstep (se 1 (by rfl) ⟨156977, by rfl⟩ : syracuseStep 209303 = 313955) B313955
theorem B307673 : Blo 135790 307673 := bstep (se 2 (by rfl) ⟨115377, by rfl⟩ : syracuseStep 307673 = 230755) B230755
theorem B209369 : Blo 135790 209369 := bstep (se 2 (by rfl) ⟨78513, by rfl⟩ : syracuseStep 209369 = 157027) B157027
theorem B700973 : Blo 135790 700973 := bstep (se 3 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 700973 = 262865) B262865
theorem B307763 : Blo 135790 307763 := bstep (se 1 (by rfl) ⟨230822, by rfl⟩ : syracuseStep 307763 = 461645) B461645
theorem B1094219 : Blo 135790 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B209483 : Blo 135790 209483 := bstep (se 1 (by rfl) ⟨157112, by rfl⟩ : syracuseStep 209483 = 314225) B314225
theorem B307799 : Blo 135790 307799 := bstep (se 1 (by rfl) ⟨230849, by rfl⟩ : syracuseStep 307799 = 461699) B461699
theorem B209495 : Blo 135790 209495 := bstep (se 1 (by rfl) ⟨157121, by rfl⟩ : syracuseStep 209495 = 314243) B314243
theorem B209561 : Blo 135790 209561 := bstep (se 2 (by rfl) ⟨78585, by rfl⟩ : syracuseStep 209561 = 157171) B157171
theorem B176843 : Blo 135790 176843 := bstep (se 1 (by rfl) ⟨132632, by rfl⟩ : syracuseStep 176843 = 265265) B265265
theorem B2994893 : Blo 135790 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B307979 : Blo 135790 307979 := bstep (se 1 (by rfl) ⟨230984, by rfl⟩ : syracuseStep 307979 = 461969) B461969
theorem B209675 : Blo 135790 209675 := bstep (se 1 (by rfl) ⟨157256, by rfl⟩ : syracuseStep 209675 = 314513) B314513
theorem B308033 : Blo 135790 308033 := bstep (se 2 (by rfl) ⟨115512, by rfl⟩ : syracuseStep 308033 = 231025) B231025
theorem B1192805 : Blo 135790 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B308249 : Blo 135790 308249 := bstep (se 2 (by rfl) ⟨115593, by rfl⟩ : syracuseStep 308249 = 231187) B231187
theorem B635969 : Blo 135790 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B308339 : Blo 135790 308339 := bstep (se 1 (by rfl) ⟨231254, by rfl⟩ : syracuseStep 308339 = 462509) B462509
theorem B308375 : Blo 135790 308375 := bstep (se 1 (by rfl) ⟨231281, by rfl⟩ : syracuseStep 308375 = 462563) B462563
theorem B505025 : Blo 135790 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B308555 : Blo 135790 308555 := bstep (se 1 (by rfl) ⟨231416, by rfl⟩ : syracuseStep 308555 = 462833) B462833
theorem B308609 : Blo 135790 308609 := bstep (se 2 (by rfl) ⟨115728, by rfl⟩ : syracuseStep 308609 = 231457) B231457
theorem B308825 : Blo 135790 308825 := bstep (se 2 (by rfl) ⟨115809, by rfl⟩ : syracuseStep 308825 = 231619) B231619
theorem B308915 : Blo 135790 308915 := bstep (se 1 (by rfl) ⟨231686, by rfl⟩ : syracuseStep 308915 = 463373) B463373
theorem B308951 : Blo 135790 308951 := bstep (se 1 (by rfl) ⟨231713, by rfl⟩ : syracuseStep 308951 = 463427) B463427
theorem B309131 : Blo 135790 309131 := bstep (se 1 (by rfl) ⟨231848, by rfl⟩ : syracuseStep 309131 = 463697) B463697
theorem B309185 : Blo 135790 309185 := bstep (se 2 (by rfl) ⟨115944, by rfl⟩ : syracuseStep 309185 = 231889) B231889
theorem B735277 : Blo 135790 735277 := bstep (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) B275729
theorem B309401 : Blo 135790 309401 := bstep (se 2 (by rfl) ⟨116025, by rfl⟩ : syracuseStep 309401 = 232051) B232051
theorem B833753 : Blo 135790 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B309491 : Blo 135790 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B145675 : Blo 135790 145675 := bstep (se 1 (by rfl) ⟨109256, by rfl⟩ : syracuseStep 145675 = 218513) B218513
theorem B309527 : Blo 135790 309527 := bstep (se 1 (by rfl) ⟨232145, by rfl⟩ : syracuseStep 309527 = 464291) B464291
theorem B997667 : Blo 135790 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B309707 : Blo 135790 309707 := bstep (se 1 (by rfl) ⟨232280, by rfl⟩ : syracuseStep 309707 = 464561) B464561
theorem B309761 : Blo 135790 309761 := bstep (se 2 (by rfl) ⟨116160, by rfl⟩ : syracuseStep 309761 = 232321) B232321
theorem B211481 : Blo 135790 211481 := bstep (se 2 (by rfl) ⟨79305, by rfl⟩ : syracuseStep 211481 = 158611) B158611
theorem B670301 : Blo 135790 670301 := bstep (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) B251363
theorem B309977 : Blo 135790 309977 := bstep (se 2 (by rfl) ⟨116241, by rfl⟩ : syracuseStep 309977 = 232483) B232483
theorem B310067 : Blo 135790 310067 := bstep (se 1 (by rfl) ⟨232550, by rfl⟩ : syracuseStep 310067 = 465101) B465101
theorem B310103 : Blo 135790 310103 := bstep (se 1 (by rfl) ⟨232577, by rfl⟩ : syracuseStep 310103 = 465155) B465155
theorem B277463 : Blo 135790 277463 := bstep (se 1 (by rfl) ⟨208097, by rfl⟩ : syracuseStep 277463 = 416195) B416195
theorem B310283 : Blo 135790 310283 := bstep (se 1 (by rfl) ⟨232712, by rfl⟩ : syracuseStep 310283 = 465425) B465425
theorem B310337 : Blo 135790 310337 := bstep (se 2 (by rfl) ⟨116376, by rfl⟩ : syracuseStep 310337 = 232753) B232753
theorem B310553 : Blo 135790 310553 := bstep (se 2 (by rfl) ⟨116457, by rfl⟩ : syracuseStep 310553 = 232915) B232915
theorem B310643 : Blo 135790 310643 := bstep (se 1 (by rfl) ⟨232982, by rfl⟩ : syracuseStep 310643 = 465965) B465965
theorem B310679 : Blo 135790 310679 := bstep (se 1 (by rfl) ⟨233009, by rfl⟩ : syracuseStep 310679 = 466019) B466019
theorem B212375 : Blo 135790 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B310859 : Blo 135790 310859 := bstep (se 1 (by rfl) ⟨233144, by rfl⟩ : syracuseStep 310859 = 466289) B466289
theorem B310913 : Blo 135790 310913 := bstep (se 2 (by rfl) ⟨116592, by rfl⟩ : syracuseStep 310913 = 233185) B233185
theorem B310999 : Blo 135790 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B311129 : Blo 135790 311129 := bstep (se 2 (by rfl) ⟨116673, by rfl⟩ : syracuseStep 311129 = 233347) B233347
theorem B311219 : Blo 135790 311219 := bstep (se 1 (by rfl) ⟨233414, by rfl⟩ : syracuseStep 311219 = 466829) B466829
theorem B311255 : Blo 135790 311255 := bstep (se 1 (by rfl) ⟨233441, by rfl⟩ : syracuseStep 311255 = 466883) B466883
theorem B311435 : Blo 135790 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B311489 : Blo 135790 311489 := bstep (se 2 (by rfl) ⟨116808, by rfl⟩ : syracuseStep 311489 = 233617) B233617
theorem B147691 : Blo 135790 147691 := bstep (se 1 (by rfl) ⟨110768, by rfl⟩ : syracuseStep 147691 = 221537) B221537
theorem B344371 : Blo 135790 344371 := bstep (se 1 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 344371 = 516557) B516557
theorem B704861 : Blo 135790 704861 := bstep (se 3 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 704861 = 264323) B264323
theorem B835991 : Blo 135790 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B311705 : Blo 135790 311705 := bstep (se 2 (by rfl) ⟨116889, by rfl⟩ : syracuseStep 311705 = 233779) B233779
theorem B344513 : Blo 135790 344513 := bstep (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) B258385
theorem B442817 : Blo 135790 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B311795 : Blo 135790 311795 := bstep (se 1 (by rfl) ⟨233846, by rfl⟩ : syracuseStep 311795 = 467693) B467693
theorem B311831 : Blo 135790 311831 := bstep (se 1 (by rfl) ⟨233873, by rfl⟩ : syracuseStep 311831 = 467747) B467747
theorem B1032749 : Blo 135790 1032749 := bstep (se 3 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 1032749 = 387281) B387281
theorem B1327691 : Blo 135790 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B1065565 : Blo 135790 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B2507395 : Blo 135790 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B1557143 : Blo 135790 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B312011 : Blo 135790 312011 := bstep (se 1 (by rfl) ⟨234008, by rfl⟩ : syracuseStep 312011 = 468017) B468017
theorem B312065 : Blo 135790 312065 := bstep (se 2 (by rfl) ⟨117024, by rfl⟩ : syracuseStep 312065 = 234049) B234049
theorem B377779 : Blo 135790 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B246721 : Blo 135790 246721 := bstep (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) B185041
theorem B148439 : Blo 135790 148439 := bstep (se 1 (by rfl) ⟨111329, by rfl⟩ : syracuseStep 148439 = 222659) B222659
theorem B312281 : Blo 135790 312281 := bstep (se 2 (by rfl) ⟨117105, by rfl⟩ : syracuseStep 312281 = 234211) B234211
theorem B312371 : Blo 135790 312371 := bstep (se 1 (by rfl) ⟨234278, by rfl⟩ : syracuseStep 312371 = 468557) B468557
theorem B312407 : Blo 135790 312407 := bstep (se 1 (by rfl) ⟨234305, by rfl⟩ : syracuseStep 312407 = 468611) B468611
theorem B312587 : Blo 135790 312587 := bstep (se 1 (by rfl) ⟨234440, by rfl⟩ : syracuseStep 312587 = 468881) B468881
theorem B312641 : Blo 135790 312641 := bstep (se 2 (by rfl) ⟨117240, by rfl⟩ : syracuseStep 312641 = 234481) B234481
theorem B312857 : Blo 135790 312857 := bstep (se 2 (by rfl) ⟨117321, by rfl⟩ : syracuseStep 312857 = 234643) B234643
theorem B312947 : Blo 135790 312947 := bstep (se 1 (by rfl) ⟨234710, by rfl⟩ : syracuseStep 312947 = 469421) B469421
theorem B312983 : Blo 135790 312983 := bstep (se 1 (by rfl) ⟨234737, by rfl⟩ : syracuseStep 312983 = 469475) B469475
theorem B345779 : Blo 135790 345779 := bstep (se 1 (by rfl) ⟨259334, by rfl⟩ : syracuseStep 345779 = 518669) B518669
theorem B247499 : Blo 135790 247499 := bstep (se 1 (by rfl) ⟨185624, by rfl⟩ : syracuseStep 247499 = 371249) B371249
theorem B313163 : Blo 135790 313163 := bstep (se 1 (by rfl) ⟨234872, by rfl⟩ : syracuseStep 313163 = 469745) B469745
theorem B313217 : Blo 135790 313217 := bstep (se 2 (by rfl) ⟨117456, by rfl⟩ : syracuseStep 313217 = 234913) B234913
theorem B280577 : Blo 135790 280577 := bstep (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) B210433
theorem B313433 : Blo 135790 313433 := bstep (se 2 (by rfl) ⟨117537, by rfl⟩ : syracuseStep 313433 = 235075) B235075
theorem B247961 : Blo 135790 247961 := bstep (se 2 (by rfl) ⟨92985, by rfl⟩ : syracuseStep 247961 = 185971) B185971
theorem B313523 : Blo 135790 313523 := bstep (se 1 (by rfl) ⟨235142, by rfl⟩ : syracuseStep 313523 = 470285) B470285
theorem B346315 : Blo 135790 346315 := bstep (se 1 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 346315 = 519473) B519473
theorem B313559 : Blo 135790 313559 := bstep (se 1 (by rfl) ⟨235169, by rfl⟩ : syracuseStep 313559 = 470339) B470339
theorem B739601 : Blo 135790 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B346457 : Blo 135790 346457 := bstep (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) B259843
theorem B313739 : Blo 135790 313739 := bstep (se 1 (by rfl) ⟨235304, by rfl⟩ : syracuseStep 313739 = 470609) B470609
theorem B706967 : Blo 135790 706967 := bstep (se 1 (by rfl) ⟨530225, by rfl⟩ : syracuseStep 706967 = 1060451) B1060451
theorem B313793 : Blo 135790 313793 := bstep (se 2 (by rfl) ⟨117672, by rfl⟩ : syracuseStep 313793 = 235345) B235345
theorem B510553 : Blo 135790 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B281227 : Blo 135790 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B314009 : Blo 135790 314009 := bstep (se 2 (by rfl) ⟨117753, by rfl⟩ : syracuseStep 314009 = 235507) B235507
theorem B510637 : Blo 135790 510637 := bstep (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) B191489
theorem B248537 : Blo 135790 248537 := bstep (se 2 (by rfl) ⟨93201, by rfl⟩ : syracuseStep 248537 = 186403) B186403
theorem B314099 : Blo 135790 314099 := bstep (se 1 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 314099 = 471149) B471149
theorem B314135 : Blo 135790 314135 := bstep (se 1 (by rfl) ⟨235601, by rfl⟩ : syracuseStep 314135 = 471203) B471203
theorem B445277 : Blo 135790 445277 := bstep (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) B166979
theorem B314315 : Blo 135790 314315 := bstep (se 1 (by rfl) ⟨235736, by rfl⟩ : syracuseStep 314315 = 471473) B471473
theorem B314369 : Blo 135790 314369 := bstep (se 2 (by rfl) ⟨117888, by rfl⟩ : syracuseStep 314369 = 235777) B235777
theorem B347287 : Blo 135790 347287 := bstep (se 1 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 347287 = 520931) B520931
theorem B4443437 : Blo 135790 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B347723 : Blo 135790 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B282199 : Blo 135790 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B348097 : Blo 135790 348097 := bstep (se 2 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 348097 = 261073) B261073
theorem B446411 : Blo 135790 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B380875 : Blo 135790 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B250123 : Blo 135790 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B1036637 : Blo 135790 1036637 := bstep (se 3 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 1036637 = 388739) B388739
theorem B282995 : Blo 135790 282995 := bstep (se 1 (by rfl) ⟨212246, by rfl⟩ : syracuseStep 282995 = 424493) B424493
theorem B315863 : Blo 135790 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B348695 : Blo 135790 348695 := bstep (se 1 (by rfl) ⟨261521, by rfl⟩ : syracuseStep 348695 = 523043) B523043
theorem B1659523 : Blo 135790 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B1004183 : Blo 135790 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B742067 : Blo 135790 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B873281 : Blo 135790 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B873433 : Blo 135790 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B250931 : Blo 135790 250931 := bstep (se 1 (by rfl) ⟨188198, by rfl⟩ : syracuseStep 250931 = 376397) B376397
theorem B152779 : Blo 135790 152779 := bstep (se 1 (by rfl) ⟨114584, by rfl⟩ : syracuseStep 152779 = 229169) B229169
theorem B251147 : Blo 135790 251147 := bstep (se 1 (by rfl) ⟨188360, by rfl⟩ : syracuseStep 251147 = 376721) B376721
theorem B152887 : Blo 135790 152887 := bstep (se 1 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 152887 = 229331) B229331
theorem B349505 : Blo 135790 349505 := bstep (se 2 (by rfl) ⟨131064, by rfl⟩ : syracuseStep 349505 = 262129) B262129
theorem B153067 : Blo 135790 153067 := bstep (se 1 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 153067 = 229601) B229601
theorem B153175 : Blo 135790 153175 := bstep (se 1 (by rfl) ⟨114881, by rfl⟩ : syracuseStep 153175 = 229763) B229763
theorem B153355 : Blo 135790 153355 := bstep (se 1 (by rfl) ⟨115016, by rfl⟩ : syracuseStep 153355 = 230033) B230033
theorem B317249 : Blo 135790 317249 := bstep (se 2 (by rfl) ⟨118968, by rfl⟩ : syracuseStep 317249 = 237937) B237937
theorem B350041 : Blo 135790 350041 := bstep (se 2 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 350041 = 262531) B262531
theorem B153463 : Blo 135790 153463 := bstep (se 1 (by rfl) ⟨115097, by rfl⟩ : syracuseStep 153463 = 230195) B230195
theorem B219019 : Blo 135790 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B153643 : Blo 135790 153643 := bstep (se 1 (by rfl) ⟨115232, by rfl⟩ : syracuseStep 153643 = 230465) B230465
theorem B153751 : Blo 135790 153751 := bstep (se 1 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 153751 = 230627) B230627
theorem B153931 : Blo 135790 153931 := bstep (se 1 (by rfl) ⟨115448, by rfl⟩ : syracuseStep 153931 = 230897) B230897
theorem B154039 : Blo 135790 154039 := bstep (se 1 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 154039 = 231059) B231059
theorem B1104401 : Blo 135790 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B776749 : Blo 135790 776749 := bstep (se 3 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 776749 = 291281) B291281
theorem B154219 : Blo 135790 154219 := bstep (se 1 (by rfl) ⟨115664, by rfl⟩ : syracuseStep 154219 = 231329) B231329
theorem B1268401 : Blo 135790 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B154327 : Blo 135790 154327 := bstep (se 1 (by rfl) ⟨115745, by rfl⟩ : syracuseStep 154327 = 231491) B231491
theorem B8575715 : Blo 135790 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B580375 : Blo 135790 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B580445 : Blo 135790 580445 := bstep (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) B217667
theorem B154507 : Blo 135790 154507 := bstep (se 1 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 154507 = 231761) B231761
theorem B351155 : Blo 135790 351155 := bstep (se 1 (by rfl) ⟨263366, by rfl⟩ : syracuseStep 351155 = 526733) B526733
theorem B154615 : Blo 135790 154615 := bstep (se 1 (by rfl) ⟨115961, by rfl⟩ : syracuseStep 154615 = 231923) B231923
theorem B220249 : Blo 135790 220249 := bstep (se 2 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 220249 = 165187) B165187
theorem B154795 : Blo 135790 154795 := bstep (se 1 (by rfl) ⟨116096, by rfl⟩ : syracuseStep 154795 = 232193) B232193
theorem B1006769 : Blo 135790 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B351449 : Blo 135790 351449 := bstep (se 2 (by rfl) ⟨131793, by rfl⟩ : syracuseStep 351449 = 263587) B263587
theorem B154903 : Blo 135790 154903 := bstep (se 1 (by rfl) ⟨116177, by rfl⟩ : syracuseStep 154903 = 232355) B232355
theorem B155083 : Blo 135790 155083 := bstep (se 1 (by rfl) ⟨116312, by rfl⟩ : syracuseStep 155083 = 232625) B232625
theorem B155191 : Blo 135790 155191 := bstep (se 1 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 155191 = 232787) B232787
theorem B581195 : Blo 135790 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B155339 : Blo 135790 155339 := bstep (se 1 (by rfl) ⟨116504, by rfl⟩ : syracuseStep 155339 = 233009) B233009
theorem B155371 : Blo 135790 155371 := bstep (se 1 (by rfl) ⟨116528, by rfl⟩ : syracuseStep 155371 = 233057) B233057
theorem B155479 : Blo 135790 155479 := bstep (se 1 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 155479 = 233219) B233219
theorem B155659 : Blo 135790 155659 := bstep (se 1 (by rfl) ⟨116744, by rfl⟩ : syracuseStep 155659 = 233489) B233489
theorem B221195 : Blo 135790 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B155767 : Blo 135790 155767 := bstep (se 1 (by rfl) ⟨116825, by rfl⟩ : syracuseStep 155767 = 233651) B233651
theorem B155947 : Blo 135790 155947 := bstep (se 1 (by rfl) ⟨116960, by rfl⟩ : syracuseStep 155947 = 233921) B233921
theorem B1401133 : Blo 135790 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B156055 : Blo 135790 156055 := bstep (se 1 (by rfl) ⟨117041, by rfl⟩ : syracuseStep 156055 = 234083) B234083
theorem B156235 : Blo 135790 156235 := bstep (se 1 (by rfl) ⟨117176, by rfl⟩ : syracuseStep 156235 = 234353) B234353
theorem B516739 : Blo 135790 516739 := bstep (se 1 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 516739 = 775109) B775109
theorem B156343 : Blo 135790 156343 := bstep (se 1 (by rfl) ⟨117257, by rfl⟩ : syracuseStep 156343 = 234515) B234515
theorem B1008389 : Blo 135790 1008389 := bstep (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) B189073
theorem B156439 : Blo 135790 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B353099 : Blo 135790 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B156523 : Blo 135790 156523 := bstep (se 1 (by rfl) ⟨117392, by rfl⟩ : syracuseStep 156523 = 234785) B234785
theorem B517043 : Blo 135790 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B156631 : Blo 135790 156631 := bstep (se 1 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 156631 = 234947) B234947
theorem B1860569 : Blo 135790 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B156811 : Blo 135790 156811 := bstep (se 1 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 156811 = 235217) B235217
theorem B156919 : Blo 135790 156919 := bstep (se 1 (by rfl) ⟨117689, by rfl⟩ : syracuseStep 156919 = 235379) B235379
theorem B419165 : Blo 135790 419165 := bstep (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) B157187
theorem B157099 : Blo 135790 157099 := bstep (se 1 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 157099 = 235649) B235649
theorem B2352563 : Blo 135790 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B1598899 : Blo 135790 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B157207 : Blo 135790 157207 := bstep (se 1 (by rfl) ⟨117905, by rfl⟩ : syracuseStep 157207 = 235811) B235811
theorem B517697 : Blo 135790 517697 := bstep (se 2 (by rfl) ⟨194136, by rfl⟩ : syracuseStep 517697 = 388273) B388273
theorem B157675 : Blo 135790 157675 := bstep (se 1 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 157675 = 236513) B236513
theorem B387251 : Blo 135790 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B1239245 : Blo 135790 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B518957 : Blo 135790 518957 := bstep (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) B194609
theorem B518987 : Blo 135790 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B584749 : Blo 135790 584749 := bstep (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) B219281
theorem B388147 : Blo 135790 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B879767 : Blo 135790 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B584921 : Blo 135790 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B290137 : Blo 135790 290137 := bstep (se 2 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 290137 = 217603) B217603
theorem B519641 : Blo 135790 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B290393 : Blo 135790 290393 := bstep (se 2 (by rfl) ⟨108897, by rfl⟩ : syracuseStep 290393 = 217795) B217795
theorem B519959 : Blo 135790 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B749387 : Blo 135790 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B290803 : Blo 135790 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B258059 : Blo 135790 258059 := bstep (se 1 (by rfl) ⟨193544, by rfl⟩ : syracuseStep 258059 = 387089) B387089
theorem B389195 : Blo 135790 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B1339523 : Blo 135790 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B6942871 : Blo 135790 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B258241 : Blo 135790 258241 := bstep (se 2 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 258241 = 193681) B193681
theorem B520627 : Blo 135790 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B422423 : Blo 135790 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B1110629 : Blo 135790 1110629 := bstep (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) B208243
theorem B258689 : Blo 135790 258689 := bstep (se 2 (by rfl) ⟨97008, by rfl⟩ : syracuseStep 258689 = 194017) B194017
theorem B291521 : Blo 135790 291521 := bstep (se 2 (by rfl) ⟨109320, by rfl⟩ : syracuseStep 291521 = 218641) B218641
theorem B586561 : Blo 135790 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B717661 : Blo 135790 717661 := bstep (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) B269123
theorem B259031 : Blo 135790 259031 := bstep (se 1 (by rfl) ⟨194273, by rfl⟩ : syracuseStep 259031 = 388547) B388547
theorem B291863 : Blo 135790 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B783539 : Blo 135790 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B292033 : Blo 135790 292033 := bstep (se 2 (by rfl) ⟨109512, by rfl⟩ : syracuseStep 292033 = 219025) B219025
theorem B1111475 : Blo 135790 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B1570265 : Blo 135790 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B882251 : Blo 135790 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B259699 : Blo 135790 259699 := bstep (se 1 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 259699 = 389549) B389549
theorem B521873 : Blo 135790 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B390835 : Blo 135790 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B391063 : Blo 135790 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B423883 : Blo 135790 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B260147 : Blo 135790 260147 := bstep (se 1 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 260147 = 390221) B390221
theorem B260185 : Blo 135790 260185 := bstep (se 2 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 260185 = 195139) B195139
theorem B1800323 : Blo 135790 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B2586775 : Blo 135790 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B293195 : Blo 135790 293195 := bstep (se 1 (by rfl) ⟨219896, by rfl⟩ : syracuseStep 293195 = 439793) B439793
theorem B522571 : Blo 135790 522571 := bstep (se 1 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 522571 = 783857) B783857
theorem B588235 : Blo 135790 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B260633 : Blo 135790 260633 := bstep (se 2 (by rfl) ⟨97737, by rfl⟩ : syracuseStep 260633 = 195475) B195475
theorem B522845 : Blo 135790 522845 := bstep (se 3 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 522845 = 196067) B196067
theorem B784997 : Blo 135790 784997 := bstep (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) B147187
theorem B588505 : Blo 135790 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B588509 : Blo 135790 588509 := bstep (se 3 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 588509 = 220691) B220691
theorem B424855 : Blo 135790 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B293939 : Blo 135790 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B293977 : Blo 135790 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B261377 : Blo 135790 261377 := bstep (se 2 (by rfl) ⟨98016, by rfl⟩ : syracuseStep 261377 = 196033) B196033
theorem B523543 : Blo 135790 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B261643 : Blo 135790 261643 := bstep (se 1 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 261643 = 392465) B392465
theorem B327347 : Blo 135790 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B392921 : Blo 135790 392921 := bstep (se 2 (by rfl) ⟨147345, by rfl⟩ : syracuseStep 392921 = 294691) B294691
theorem B458675 : Blo 135790 458675 := bstep (se 1 (by rfl) ⟨344006, by rfl⟩ : syracuseStep 458675 = 688013) B688013
theorem B294835 : Blo 135790 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B262091 : Blo 135790 262091 := bstep (se 1 (by rfl) ⟨196568, by rfl⟩ : syracuseStep 262091 = 393137) B393137
theorem B1114073 : Blo 135790 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B786455 : Blo 135790 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B589853 : Blo 135790 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B589943 : Blo 135790 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B557327 : Blo 135790 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B262433 : Blo 135790 262433 := bstep (se 2 (by rfl) ⟨98412, by rfl⟩ : syracuseStep 262433 = 196825) B196825
theorem B229675 : Blo 135790 229675 := bstep (se 1 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 229675 = 344513) B344513
theorem B295211 : Blo 135790 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B196921 : Blo 135790 196921 := bstep (se 2 (by rfl) ⟨73845, by rfl⟩ : syracuseStep 196921 = 147691) B147691
theorem B688499 : Blo 135790 688499 := bstep (se 1 (by rfl) ⟨516374, by rfl⟩ : syracuseStep 688499 = 1032749) B1032749
theorem B17170805 : Blo 135790 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B885127 : Blo 135790 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B1868177 : Blo 135790 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B459161 : Blo 135790 459161 := bstep (se 2 (by rfl) ⟨172185, by rfl⟩ : syracuseStep 459161 = 344371) B344371
theorem B229817 : Blo 135790 229817 := bstep (se 2 (by rfl) ⟨86181, by rfl⟩ : syracuseStep 229817 = 172363) B172363
theorem B786955 : Blo 135790 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B197263 : Blo 135790 197263 := bstep (se 1 (by rfl) ⟨147947, by rfl⟩ : syracuseStep 197263 = 295895) B295895
theorem B525001 : Blo 135790 525001 := bstep (se 2 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 525001 = 393751) B393751
theorem B688985 : Blo 135790 688985 := bstep (se 2 (by rfl) ⟨258369, by rfl⟩ : syracuseStep 688985 = 516739) B516739
theorem B3343193 : Blo 135790 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B590915 : Blo 135790 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B459863 : Blo 135790 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B590935 : Blo 135790 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B230519 : Blo 135790 230519 := bstep (se 1 (by rfl) ⟨172889, by rfl⟩ : syracuseStep 230519 = 345779) B345779
theorem B164999 : Blo 135790 164999 := bstep (se 1 (by rfl) ⟨123749, by rfl⟩ : syracuseStep 164999 = 247499) B247499
theorem B328961 : Blo 135790 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B165307 : Blo 135790 165307 := bstep (se 1 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 165307 = 247961) B247961
theorem B493067 : Blo 135790 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B230971 : Blo 135790 230971 := bstep (se 1 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 230971 = 346457) B346457
theorem B460349 : Blo 135790 460349 := bstep (se 3 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 460349 = 172631) B172631
theorem B231113 : Blo 135790 231113 := bstep (se 2 (by rfl) ⟨86667, by rfl⟩ : syracuseStep 231113 = 173335) B173335
theorem B198391 : Blo 135790 198391 := bstep (se 1 (by rfl) ⟨148793, by rfl⟩ : syracuseStep 198391 = 297587) B297587
theorem B165691 : Blo 135790 165691 := bstep (se 1 (by rfl) ⟨124268, by rfl⟩ : syracuseStep 165691 = 248537) B248537
theorem B2131865 : Blo 135790 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B395209 : Blo 135790 395209 := bstep (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) B296407
theorem B4982957 : Blo 135790 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B264377 : Blo 135790 264377 := bstep (se 2 (by rfl) ⟨99141, by rfl⟩ : syracuseStep 264377 = 198283) B198283
theorem B395563 : Blo 135790 395563 := bstep (se 1 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 395563 = 593345) B593345
theorem B231815 : Blo 135790 231815 := bstep (se 1 (by rfl) ⟨173861, by rfl⟩ : syracuseStep 231815 = 347723) B347723
theorem B788939 : Blo 135790 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B395837 : Blo 135790 395837 := bstep (se 3 (by rfl) ⟨74219, by rfl⟩ : syracuseStep 395837 = 148439) B148439
theorem B297607 : Blo 135790 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B527219 : Blo 135790 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B691091 : Blo 135790 691091 := bstep (se 1 (by rfl) ⟨518318, by rfl⟩ : syracuseStep 691091 = 1036637) B1036637
theorem B461753 : Blo 135790 461753 := bstep (se 2 (by rfl) ⟨173157, by rfl⟩ : syracuseStep 461753 = 346315) B346315
theorem B232463 : Blo 135790 232463 := bstep (se 1 (by rfl) ⟨174347, by rfl⟩ : syracuseStep 232463 = 348695) B348695
theorem B494711 : Blo 135790 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B167287 : Blo 135790 167287 := bstep (se 1 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 167287 = 250931) B250931
theorem B167431 : Blo 135790 167431 := bstep (se 1 (by rfl) ⟨125573, by rfl⟩ : syracuseStep 167431 = 251147) B251147
theorem B462347 : Blo 135790 462347 := bstep (se 1 (by rfl) ⟨346760, by rfl⟩ : syracuseStep 462347 = 693521) B693521
theorem B1052189 : Blo 135790 1052189 := bstep (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) B394571
theorem B233003 : Blo 135790 233003 := bstep (se 1 (by rfl) ⟨174752, by rfl⟩ : syracuseStep 233003 = 349505) B349505
theorem B724547 : Blo 135790 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B462455 : Blo 135790 462455 := bstep (se 1 (by rfl) ⟨346841, by rfl⟩ : syracuseStep 462455 = 693683) B693683
theorem B397001 : Blo 135790 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B233401 : Blo 135790 233401 := bstep (se 2 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 233401 = 175051) B175051
theorem B463049 : Blo 135790 463049 := bstep (se 2 (by rfl) ⟨173643, by rfl⟩ : syracuseStep 463049 = 347287) B347287
theorem B332075 : Blo 135790 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B234103 : Blo 135790 234103 := bstep (se 1 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 234103 = 351155) B351155
theorem B397943 : Blo 135790 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B135815 : Blo 135790 135815 := bstep (se 1 (by rfl) ⟨101861, by rfl⟩ : syracuseStep 135815 = 203723) B203723
theorem B135823 : Blo 135790 135823 := bstep (se 1 (by rfl) ⟨101867, by rfl⟩ : syracuseStep 135823 = 203735) B203735
theorem B135867 : Blo 135790 135867 := bstep (se 1 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 135867 = 203801) B203801
theorem B135943 : Blo 135790 135943 := bstep (se 1 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 135943 = 203915) B203915
theorem B135951 : Blo 135790 135951 := bstep (se 1 (by rfl) ⟨101963, by rfl⟩ : syracuseStep 135951 = 203927) B203927
theorem B791329 : Blo 135790 791329 := bstep (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) B593497
theorem B2265893 : Blo 135790 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B135995 : Blo 135790 135995 := bstep (se 1 (by rfl) ⟨101996, by rfl⟩ : syracuseStep 135995 = 203993) B203993
theorem B234299 : Blo 135790 234299 := bstep (se 1 (by rfl) ⟨175724, by rfl⟩ : syracuseStep 234299 = 351449) B351449
theorem B136071 : Blo 135790 136071 := bstep (se 1 (by rfl) ⟨102053, by rfl⟩ : syracuseStep 136071 = 204107) B204107
theorem B463751 : Blo 135790 463751 := bstep (se 1 (by rfl) ⟨347813, by rfl⟩ : syracuseStep 463751 = 695627) B695627
theorem B136079 : Blo 135790 136079 := bstep (se 1 (by rfl) ⟨102059, by rfl⟩ : syracuseStep 136079 = 204119) B204119
theorem B136123 : Blo 135790 136123 := bstep (se 1 (by rfl) ⟨102092, by rfl⟩ : syracuseStep 136123 = 204185) B204185
theorem B529361 : Blo 135790 529361 := bstep (se 2 (by rfl) ⟨198510, by rfl⟩ : syracuseStep 529361 = 397021) B397021
theorem B136199 : Blo 135790 136199 := bstep (se 1 (by rfl) ⟨102149, by rfl⟩ : syracuseStep 136199 = 204299) B204299
theorem B136207 : Blo 135790 136207 := bstep (se 1 (by rfl) ⟨102155, by rfl⟩ : syracuseStep 136207 = 204311) B204311
theorem B136251 : Blo 135790 136251 := bstep (se 1 (by rfl) ⟨102188, by rfl⟩ : syracuseStep 136251 = 204377) B204377
theorem B136327 : Blo 135790 136327 := bstep (se 1 (by rfl) ⟨102245, by rfl⟩ : syracuseStep 136327 = 204491) B204491
theorem B136335 : Blo 135790 136335 := bstep (se 1 (by rfl) ⟨102251, by rfl⟩ : syracuseStep 136335 = 204503) B204503
theorem B136379 : Blo 135790 136379 := bstep (se 1 (by rfl) ⟨102284, by rfl⟩ : syracuseStep 136379 = 204569) B204569
theorem B234697 : Blo 135790 234697 := bstep (se 2 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 234697 = 176023) B176023
theorem B464129 : Blo 135790 464129 := bstep (se 2 (by rfl) ⟨174048, by rfl⟩ : syracuseStep 464129 = 348097) B348097
theorem B136455 : Blo 135790 136455 := bstep (se 1 (by rfl) ⟨102341, by rfl⟩ : syracuseStep 136455 = 204683) B204683
theorem B136463 : Blo 135790 136463 := bstep (se 1 (by rfl) ⟨102347, by rfl⟩ : syracuseStep 136463 = 204695) B204695
theorem B529679 : Blo 135790 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B136507 : Blo 135790 136507 := bstep (se 1 (by rfl) ⟨102380, by rfl⟩ : syracuseStep 136507 = 204761) B204761
theorem B595259 : Blo 135790 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B333143 : Blo 135790 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B136583 : Blo 135790 136583 := bstep (se 1 (by rfl) ⟨102437, by rfl⟩ : syracuseStep 136583 = 204875) B204875
theorem B136591 : Blo 135790 136591 := bstep (se 1 (by rfl) ⟨102443, by rfl⟩ : syracuseStep 136591 = 204887) B204887
theorem B136635 : Blo 135790 136635 := bstep (se 1 (by rfl) ⟨102476, by rfl⟩ : syracuseStep 136635 = 204953) B204953
theorem B136711 : Blo 135790 136711 := bstep (se 1 (by rfl) ⟨102533, by rfl⟩ : syracuseStep 136711 = 205067) B205067
theorem B136719 : Blo 135790 136719 := bstep (se 1 (by rfl) ⟨102539, by rfl⟩ : syracuseStep 136719 = 205079) B205079
theorem B136763 : Blo 135790 136763 := bstep (se 1 (by rfl) ⟨102572, by rfl⟩ : syracuseStep 136763 = 205145) B205145
theorem B136839 : Blo 135790 136839 := bstep (se 1 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 136839 = 205259) B205259
theorem B136847 : Blo 135790 136847 := bstep (se 1 (by rfl) ⟨102635, by rfl⟩ : syracuseStep 136847 = 205271) B205271
theorem B333497 : Blo 135790 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B136891 : Blo 135790 136891 := bstep (se 1 (by rfl) ⟨102668, by rfl⟩ : syracuseStep 136891 = 205337) B205337
theorem B136967 : Blo 135790 136967 := bstep (se 1 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 136967 = 205451) B205451
theorem B136975 : Blo 135790 136975 := bstep (se 1 (by rfl) ⟨102731, by rfl⟩ : syracuseStep 136975 = 205463) B205463
theorem B137019 : Blo 135790 137019 := bstep (se 1 (by rfl) ⟨102764, by rfl⟩ : syracuseStep 137019 = 205529) B205529
theorem B137095 : Blo 135790 137095 := bstep (se 1 (by rfl) ⟨102821, by rfl⟩ : syracuseStep 137095 = 205643) B205643
theorem B235399 : Blo 135790 235399 := bstep (se 1 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 235399 = 353099) B353099
theorem B137103 : Blo 135790 137103 := bstep (se 1 (by rfl) ⟨102827, by rfl⟩ : syracuseStep 137103 = 205655) B205655
theorem B694169 : Blo 135790 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B137147 : Blo 135790 137147 := bstep (se 1 (by rfl) ⟨102860, by rfl⟩ : syracuseStep 137147 = 205721) B205721
theorem B1579013 : Blo 135790 1579013 := bstep (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) B296065
theorem B137223 : Blo 135790 137223 := bstep (se 1 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 137223 = 205835) B205835
theorem B137231 : Blo 135790 137231 := bstep (se 1 (by rfl) ⟨102923, by rfl⟩ : syracuseStep 137231 = 205847) B205847
theorem B792605 : Blo 135790 792605 := bstep (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) B297227
theorem B464939 : Blo 135790 464939 := bstep (se 1 (by rfl) ⟨348704, by rfl⟩ : syracuseStep 464939 = 697409) B697409
theorem B137275 : Blo 135790 137275 := bstep (se 1 (by rfl) ⟨102956, by rfl⟩ : syracuseStep 137275 = 205913) B205913
theorem B1251389 : Blo 135790 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B137351 : Blo 135790 137351 := bstep (se 1 (by rfl) ⟨103013, by rfl⟩ : syracuseStep 137351 = 206027) B206027
theorem B137359 : Blo 135790 137359 := bstep (se 1 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 137359 = 206039) B206039
theorem B137403 : Blo 135790 137403 := bstep (se 1 (by rfl) ⟨103052, by rfl⟩ : syracuseStep 137403 = 206105) B206105
theorem B137479 : Blo 135790 137479 := bstep (se 1 (by rfl) ⟨103109, by rfl⟩ : syracuseStep 137479 = 206219) B206219
theorem B137487 : Blo 135790 137487 := bstep (se 1 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 137487 = 206231) B206231
theorem B137531 : Blo 135790 137531 := bstep (se 1 (by rfl) ⟨103148, by rfl⟩ : syracuseStep 137531 = 206297) B206297
theorem B137607 : Blo 135790 137607 := bstep (se 1 (by rfl) ⟨103205, by rfl⟩ : syracuseStep 137607 = 206411) B206411
theorem B137615 : Blo 135790 137615 := bstep (se 1 (by rfl) ⟨103211, by rfl⟩ : syracuseStep 137615 = 206423) B206423
theorem B137659 : Blo 135790 137659 := bstep (se 1 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 137659 = 206489) B206489
theorem B956881 : Blo 135790 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B137735 : Blo 135790 137735 := bstep (se 1 (by rfl) ⟨103301, by rfl⟩ : syracuseStep 137735 = 206603) B206603
theorem B137743 : Blo 135790 137743 := bstep (se 1 (by rfl) ⟨103307, by rfl⟩ : syracuseStep 137743 = 206615) B206615
theorem B137787 : Blo 135790 137787 := bstep (se 1 (by rfl) ⟨103340, by rfl⟩ : syracuseStep 137787 = 206681) B206681
theorem B137863 : Blo 135790 137863 := bstep (se 1 (by rfl) ⟨103397, by rfl⟩ : syracuseStep 137863 = 206795) B206795
theorem B137871 : Blo 135790 137871 := bstep (se 1 (by rfl) ⟨103403, by rfl⟩ : syracuseStep 137871 = 206807) B206807
theorem B137915 : Blo 135790 137915 := bstep (se 1 (by rfl) ⟨103436, by rfl⟩ : syracuseStep 137915 = 206873) B206873
theorem B137991 : Blo 135790 137991 := bstep (se 1 (by rfl) ⟨103493, by rfl⟩ : syracuseStep 137991 = 206987) B206987
theorem B137999 : Blo 135790 137999 := bstep (se 1 (by rfl) ⟨103499, by rfl⟩ : syracuseStep 137999 = 206999) B206999
theorem B826163 : Blo 135790 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B138043 : Blo 135790 138043 := bstep (se 1 (by rfl) ⟨103532, by rfl⟩ : syracuseStep 138043 = 207065) B207065
theorem B138119 : Blo 135790 138119 := bstep (se 1 (by rfl) ⟨103589, by rfl⟩ : syracuseStep 138119 = 207179) B207179
theorem B138127 : Blo 135790 138127 := bstep (se 1 (by rfl) ⟨103595, by rfl⟩ : syracuseStep 138127 = 207191) B207191
theorem B203705 : Blo 135790 203705 := bstep (se 2 (by rfl) ⟨76389, by rfl⟩ : syracuseStep 203705 = 152779) B152779
theorem B138171 : Blo 135790 138171 := bstep (se 1 (by rfl) ⟨103628, by rfl⟩ : syracuseStep 138171 = 207257) B207257
theorem B203783 : Blo 135790 203783 := bstep (se 1 (by rfl) ⟨152837, by rfl⟩ : syracuseStep 203783 = 305675) B305675
theorem B138247 : Blo 135790 138247 := bstep (se 1 (by rfl) ⟨103685, by rfl⟩ : syracuseStep 138247 = 207371) B207371
theorem B138255 : Blo 135790 138255 := bstep (se 1 (by rfl) ⟨103691, by rfl⟩ : syracuseStep 138255 = 207383) B207383
theorem B203819 : Blo 135790 203819 := bstep (se 1 (by rfl) ⟨152864, by rfl⟩ : syracuseStep 203819 = 305729) B305729
theorem B138299 : Blo 135790 138299 := bstep (se 1 (by rfl) ⟨103724, by rfl⟩ : syracuseStep 138299 = 207449) B207449
theorem B203849 : Blo 135790 203849 := bstep (se 2 (by rfl) ⟨76443, by rfl⟩ : syracuseStep 203849 = 152887) B152887
theorem B138375 : Blo 135790 138375 := bstep (se 1 (by rfl) ⟨103781, by rfl⟩ : syracuseStep 138375 = 207563) B207563
theorem B138383 : Blo 135790 138383 := bstep (se 1 (by rfl) ⟨103787, by rfl⟩ : syracuseStep 138383 = 207575) B207575
theorem B203963 : Blo 135790 203963 := bstep (se 1 (by rfl) ⟨152972, by rfl⟩ : syracuseStep 203963 = 305945) B305945
theorem B138427 : Blo 135790 138427 := bstep (se 1 (by rfl) ⟨103820, by rfl⟩ : syracuseStep 138427 = 207641) B207641
theorem B204023 : Blo 135790 204023 := bstep (se 1 (by rfl) ⟨153017, by rfl⟩ : syracuseStep 204023 = 306035) B306035
theorem B138503 : Blo 135790 138503 := bstep (se 1 (by rfl) ⟨103877, by rfl⟩ : syracuseStep 138503 = 207755) B207755
theorem B204047 : Blo 135790 204047 := bstep (se 1 (by rfl) ⟨153035, by rfl⟩ : syracuseStep 204047 = 306071) B306071
theorem B138511 : Blo 135790 138511 := bstep (se 1 (by rfl) ⟨103883, by rfl⟩ : syracuseStep 138511 = 207767) B207767
theorem B204089 : Blo 135790 204089 := bstep (se 2 (by rfl) ⟨76533, by rfl⟩ : syracuseStep 204089 = 153067) B153067
theorem B662843 : Blo 135790 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B466235 : Blo 135790 466235 := bstep (se 1 (by rfl) ⟨349676, by rfl⟩ : syracuseStep 466235 = 699353) B699353
theorem B138555 : Blo 135790 138555 := bstep (se 1 (by rfl) ⟨103916, by rfl⟩ : syracuseStep 138555 = 207833) B207833
theorem B204167 : Blo 135790 204167 := bstep (se 1 (by rfl) ⟨153125, by rfl⟩ : syracuseStep 204167 = 306251) B306251
theorem B138631 : Blo 135790 138631 := bstep (se 1 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 138631 = 207947) B207947
theorem B138639 : Blo 135790 138639 := bstep (se 1 (by rfl) ⟨103979, by rfl⟩ : syracuseStep 138639 = 207959) B207959
theorem B204203 : Blo 135790 204203 := bstep (se 1 (by rfl) ⟨153152, by rfl⟩ : syracuseStep 204203 = 306305) B306305
theorem B1056185 : Blo 135790 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B138683 : Blo 135790 138683 := bstep (se 1 (by rfl) ⟨104012, by rfl⟩ : syracuseStep 138683 = 208025) B208025
theorem B204233 : Blo 135790 204233 := bstep (se 2 (by rfl) ⟨76587, by rfl⟩ : syracuseStep 204233 = 153175) B153175
theorem B138759 : Blo 135790 138759 := bstep (se 1 (by rfl) ⟨104069, by rfl⟩ : syracuseStep 138759 = 208139) B208139
theorem B138767 : Blo 135790 138767 := bstep (se 1 (by rfl) ⟨104075, by rfl⟩ : syracuseStep 138767 = 208151) B208151
theorem B204347 : Blo 135790 204347 := bstep (se 1 (by rfl) ⟨153260, by rfl⟩ : syracuseStep 204347 = 306521) B306521
theorem B138811 : Blo 135790 138811 := bstep (se 1 (by rfl) ⟨104108, by rfl⟩ : syracuseStep 138811 = 208217) B208217
theorem B1187405 : Blo 135790 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B204407 : Blo 135790 204407 := bstep (se 1 (by rfl) ⟨153305, by rfl⟩ : syracuseStep 204407 = 306611) B306611
theorem B138887 : Blo 135790 138887 := bstep (se 1 (by rfl) ⟨104165, by rfl⟩ : syracuseStep 138887 = 208331) B208331
theorem B204431 : Blo 135790 204431 := bstep (se 1 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 204431 = 306647) B306647
theorem B138895 : Blo 135790 138895 := bstep (se 1 (by rfl) ⟨104171, by rfl⟩ : syracuseStep 138895 = 208343) B208343
theorem B204473 : Blo 135790 204473 := bstep (se 2 (by rfl) ⟨76677, by rfl⟩ : syracuseStep 204473 = 153355) B153355
theorem B138939 : Blo 135790 138939 := bstep (se 1 (by rfl) ⟨104204, by rfl⟩ : syracuseStep 138939 = 208409) B208409
theorem B204551 : Blo 135790 204551 := bstep (se 1 (by rfl) ⟨153413, by rfl⟩ : syracuseStep 204551 = 306827) B306827
theorem B139015 : Blo 135790 139015 := bstep (se 1 (by rfl) ⟨104261, by rfl⟩ : syracuseStep 139015 = 208523) B208523
theorem B139023 : Blo 135790 139023 := bstep (se 1 (by rfl) ⟨104267, by rfl⟩ : syracuseStep 139023 = 208535) B208535
theorem B466721 : Blo 135790 466721 := bstep (se 2 (by rfl) ⟨175020, by rfl⟩ : syracuseStep 466721 = 350041) B350041
theorem B204587 : Blo 135790 204587 := bstep (se 1 (by rfl) ⟨153440, by rfl⟩ : syracuseStep 204587 = 306881) B306881
theorem B1056563 : Blo 135790 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B139067 : Blo 135790 139067 := bstep (se 1 (by rfl) ⟨104300, by rfl⟩ : syracuseStep 139067 = 208601) B208601
theorem B204617 : Blo 135790 204617 := bstep (se 2 (by rfl) ⟨76731, by rfl⟩ : syracuseStep 204617 = 153463) B153463
theorem B499591 : Blo 135790 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B139143 : Blo 135790 139143 := bstep (se 1 (by rfl) ⟨104357, by rfl⟩ : syracuseStep 139143 = 208715) B208715
theorem B139151 : Blo 135790 139151 := bstep (se 1 (by rfl) ⟨104363, by rfl⟩ : syracuseStep 139151 = 208727) B208727
theorem B565177 : Blo 135790 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B204731 : Blo 135790 204731 := bstep (se 1 (by rfl) ⟨153548, by rfl⟩ : syracuseStep 204731 = 307097) B307097
theorem B139195 : Blo 135790 139195 := bstep (se 1 (by rfl) ⟨104396, by rfl⟩ : syracuseStep 139195 = 208793) B208793
theorem B204791 : Blo 135790 204791 := bstep (se 1 (by rfl) ⟨153593, by rfl⟩ : syracuseStep 204791 = 307187) B307187
theorem B172039 : Blo 135790 172039 := bstep (se 1 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 172039 = 258059) B258059
theorem B139271 : Blo 135790 139271 := bstep (se 1 (by rfl) ⟨104453, by rfl⟩ : syracuseStep 139271 = 208907) B208907
theorem B204815 : Blo 135790 204815 := bstep (se 1 (by rfl) ⟨153611, by rfl⟩ : syracuseStep 204815 = 307223) B307223
theorem B139279 : Blo 135790 139279 := bstep (se 1 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 139279 = 208919) B208919
theorem B204857 : Blo 135790 204857 := bstep (se 2 (by rfl) ⟨76821, by rfl⟩ : syracuseStep 204857 = 153643) B153643
theorem B139323 : Blo 135790 139323 := bstep (se 1 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 139323 = 208985) B208985
theorem B893015 : Blo 135790 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B204935 : Blo 135790 204935 := bstep (se 1 (by rfl) ⟨153701, by rfl⟩ : syracuseStep 204935 = 307403) B307403
theorem B139399 : Blo 135790 139399 := bstep (se 1 (by rfl) ⟨104549, by rfl⟩ : syracuseStep 139399 = 209099) B209099
theorem B139407 : Blo 135790 139407 := bstep (se 1 (by rfl) ⟨104555, by rfl⟩ : syracuseStep 139407 = 209111) B209111
theorem B204971 : Blo 135790 204971 := bstep (se 1 (by rfl) ⟨153728, by rfl⟩ : syracuseStep 204971 = 307457) B307457
theorem B139451 : Blo 135790 139451 := bstep (se 1 (by rfl) ⟨104588, by rfl⟩ : syracuseStep 139451 = 209177) B209177
theorem B205001 : Blo 135790 205001 := bstep (se 2 (by rfl) ⟨76875, by rfl⟩ : syracuseStep 205001 = 153751) B153751
theorem B3449033 : Blo 135790 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B139527 : Blo 135790 139527 := bstep (se 1 (by rfl) ⟨104645, by rfl⟩ : syracuseStep 139527 = 209291) B209291
theorem B139535 : Blo 135790 139535 := bstep (se 1 (by rfl) ⟨104651, by rfl⟩ : syracuseStep 139535 = 209303) B209303
theorem B205115 : Blo 135790 205115 := bstep (se 1 (by rfl) ⟨153836, by rfl⟩ : syracuseStep 205115 = 307673) B307673
theorem B139579 : Blo 135790 139579 := bstep (se 1 (by rfl) ⟨104684, by rfl⟩ : syracuseStep 139579 = 209369) B209369
theorem B467315 : Blo 135790 467315 := bstep (se 1 (by rfl) ⟨350486, by rfl⟩ : syracuseStep 467315 = 700973) B700973
theorem B205175 : Blo 135790 205175 := bstep (se 1 (by rfl) ⟨153881, by rfl⟩ : syracuseStep 205175 = 307763) B307763
theorem B729479 : Blo 135790 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B139655 : Blo 135790 139655 := bstep (se 1 (by rfl) ⟨104741, by rfl⟩ : syracuseStep 139655 = 209483) B209483
theorem B205199 : Blo 135790 205199 := bstep (se 1 (by rfl) ⟨153899, by rfl⟩ : syracuseStep 205199 = 307799) B307799
theorem B139663 : Blo 135790 139663 := bstep (se 1 (by rfl) ⟨104747, by rfl⟩ : syracuseStep 139663 = 209495) B209495
theorem B172459 : Blo 135790 172459 := bstep (se 1 (by rfl) ⟨129344, by rfl⟩ : syracuseStep 172459 = 258689) B258689
theorem B205241 : Blo 135790 205241 := bstep (se 2 (by rfl) ⟨76965, by rfl⟩ : syracuseStep 205241 = 153931) B153931
theorem B696761 : Blo 135790 696761 := bstep (se 2 (by rfl) ⟨261285, by rfl⟩ : syracuseStep 696761 = 522571) B522571
theorem B139707 : Blo 135790 139707 := bstep (se 1 (by rfl) ⟨104780, by rfl⟩ : syracuseStep 139707 = 209561) B209561
theorem B205319 : Blo 135790 205319 := bstep (se 1 (by rfl) ⟨153989, by rfl⟩ : syracuseStep 205319 = 307979) B307979
theorem B139783 : Blo 135790 139783 := bstep (se 1 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 139783 = 209675) B209675
theorem B205355 : Blo 135790 205355 := bstep (se 1 (by rfl) ⟨154016, by rfl⟩ : syracuseStep 205355 = 308033) B308033
theorem B795203 : Blo 135790 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B205385 : Blo 135790 205385 := bstep (se 2 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 205385 = 154039) B154039
theorem B172687 : Blo 135790 172687 := bstep (se 1 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 172687 = 259031) B259031
theorem B205499 : Blo 135790 205499 := bstep (se 1 (by rfl) ⟨154124, by rfl⟩ : syracuseStep 205499 = 308249) B308249
theorem B205559 : Blo 135790 205559 := bstep (se 1 (by rfl) ⟨154169, by rfl⟩ : syracuseStep 205559 = 308339) B308339
theorem B205583 : Blo 135790 205583 := bstep (se 1 (by rfl) ⟨154187, by rfl⟩ : syracuseStep 205583 = 308375) B308375
theorem B336683 : Blo 135790 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B205625 : Blo 135790 205625 := bstep (se 2 (by rfl) ⟨77109, by rfl⟩ : syracuseStep 205625 = 154219) B154219
theorem B205703 : Blo 135790 205703 := bstep (se 1 (by rfl) ⟨154277, by rfl⟩ : syracuseStep 205703 = 308555) B308555
theorem B205739 : Blo 135790 205739 := bstep (se 1 (by rfl) ⟨154304, by rfl⟩ : syracuseStep 205739 = 308609) B308609
theorem B205769 : Blo 135790 205769 := bstep (se 2 (by rfl) ⟨77163, by rfl⟩ : syracuseStep 205769 = 154327) B154327
theorem B205883 : Blo 135790 205883 := bstep (se 1 (by rfl) ⟨154412, by rfl⟩ : syracuseStep 205883 = 308825) B308825
theorem B205943 : Blo 135790 205943 := bstep (se 1 (by rfl) ⟨154457, by rfl⟩ : syracuseStep 205943 = 308915) B308915
theorem B205967 : Blo 135790 205967 := bstep (se 1 (by rfl) ⟨154475, by rfl⟩ : syracuseStep 205967 = 308951) B308951
theorem B206009 : Blo 135790 206009 := bstep (se 2 (by rfl) ⟨77253, by rfl⟩ : syracuseStep 206009 = 154507) B154507
theorem B206087 : Blo 135790 206087 := bstep (se 1 (by rfl) ⟨154565, by rfl⟩ : syracuseStep 206087 = 309131) B309131
theorem B206123 : Blo 135790 206123 := bstep (se 1 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 206123 = 309185) B309185
theorem B206153 : Blo 135790 206153 := bstep (se 2 (by rfl) ⟨77307, by rfl⟩ : syracuseStep 206153 = 154615) B154615
theorem B173431 : Blo 135790 173431 := bstep (se 1 (by rfl) ⟨130073, by rfl⟩ : syracuseStep 173431 = 260147) B260147
theorem B206267 : Blo 135790 206267 := bstep (se 1 (by rfl) ⟨154700, by rfl⟩ : syracuseStep 206267 = 309401) B309401
theorem B206327 : Blo 135790 206327 := bstep (se 1 (by rfl) ⟨154745, by rfl⟩ : syracuseStep 206327 = 309491) B309491
theorem B206351 : Blo 135790 206351 := bstep (se 1 (by rfl) ⟨154763, by rfl⟩ : syracuseStep 206351 = 309527) B309527
theorem B665111 : Blo 135790 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B1549853 : Blo 135790 1549853 := bstep (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) B581195
theorem B206393 : Blo 135790 206393 := bstep (se 2 (by rfl) ⟨77397, by rfl⟩ : syracuseStep 206393 = 154795) B154795
theorem B206471 : Blo 135790 206471 := bstep (se 1 (by rfl) ⟨154853, by rfl⟩ : syracuseStep 206471 = 309707) B309707
theorem B206507 : Blo 135790 206507 := bstep (se 1 (by rfl) ⟨154880, by rfl⟩ : syracuseStep 206507 = 309761) B309761
theorem B140987 : Blo 135790 140987 := bstep (se 1 (by rfl) ⟨105740, by rfl⟩ : syracuseStep 140987 = 211481) B211481
theorem B173755 : Blo 135790 173755 := bstep (se 1 (by rfl) ⟨130316, by rfl⟩ : syracuseStep 173755 = 260633) B260633
theorem B206537 : Blo 135790 206537 := bstep (se 2 (by rfl) ⟨77451, by rfl⟩ : syracuseStep 206537 = 154903) B154903
theorem B698057 : Blo 135790 698057 := bstep (se 2 (by rfl) ⟨261771, by rfl⟩ : syracuseStep 698057 = 523543) B523543
theorem B206651 : Blo 135790 206651 := bstep (se 1 (by rfl) ⟨154988, by rfl⟩ : syracuseStep 206651 = 309977) B309977
theorem B206711 : Blo 135790 206711 := bstep (se 1 (by rfl) ⟨155033, by rfl⟩ : syracuseStep 206711 = 310067) B310067
theorem B206735 : Blo 135790 206735 := bstep (se 1 (by rfl) ⟨155051, by rfl⟩ : syracuseStep 206735 = 310103) B310103
theorem B206777 : Blo 135790 206777 := bstep (se 2 (by rfl) ⟨77541, by rfl⟩ : syracuseStep 206777 = 155083) B155083
theorem B206855 : Blo 135790 206855 := bstep (se 1 (by rfl) ⟨155141, by rfl⟩ : syracuseStep 206855 = 310283) B310283
theorem B206891 : Blo 135790 206891 := bstep (se 1 (by rfl) ⟨155168, by rfl⟩ : syracuseStep 206891 = 310337) B310337
theorem B206921 : Blo 135790 206921 := bstep (se 2 (by rfl) ⟨77595, by rfl⟩ : syracuseStep 206921 = 155191) B155191
theorem B174251 : Blo 135790 174251 := bstep (se 1 (by rfl) ⟨130688, by rfl⟩ : syracuseStep 174251 = 261377) B261377
theorem B207035 : Blo 135790 207035 := bstep (se 1 (by rfl) ⟨155276, by rfl⟩ : syracuseStep 207035 = 310553) B310553
theorem B207095 : Blo 135790 207095 := bstep (se 1 (by rfl) ⟨155321, by rfl⟩ : syracuseStep 207095 = 310643) B310643
theorem B207119 : Blo 135790 207119 := bstep (se 1 (by rfl) ⟨155339, by rfl⟩ : syracuseStep 207119 = 310679) B310679
theorem B141583 : Blo 135790 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B207161 : Blo 135790 207161 := bstep (se 2 (by rfl) ⟨77685, by rfl⟩ : syracuseStep 207161 = 155371) B155371
theorem B207239 : Blo 135790 207239 := bstep (se 1 (by rfl) ⟨155429, by rfl⟩ : syracuseStep 207239 = 310859) B310859
theorem B207275 : Blo 135790 207275 := bstep (se 1 (by rfl) ⟨155456, by rfl⟩ : syracuseStep 207275 = 310913) B310913
theorem B207305 : Blo 135790 207305 := bstep (se 2 (by rfl) ⟨77739, by rfl⟩ : syracuseStep 207305 = 155479) B155479
theorem B207419 : Blo 135790 207419 := bstep (se 1 (by rfl) ⟨155564, by rfl⟩ : syracuseStep 207419 = 311129) B311129
theorem B305783 : Blo 135790 305783 := bstep (se 1 (by rfl) ⟨229337, by rfl⟩ : syracuseStep 305783 = 458675) B458675
theorem B207479 : Blo 135790 207479 := bstep (se 1 (by rfl) ⟨155609, by rfl⟩ : syracuseStep 207479 = 311219) B311219
theorem B174727 : Blo 135790 174727 := bstep (se 1 (by rfl) ⟨131045, by rfl⟩ : syracuseStep 174727 = 262091) B262091
theorem B207503 : Blo 135790 207503 := bstep (se 1 (by rfl) ⟨155627, by rfl⟩ : syracuseStep 207503 = 311255) B311255
theorem B207545 : Blo 135790 207545 := bstep (se 2 (by rfl) ⟨77829, by rfl⟩ : syracuseStep 207545 = 155659) B155659
theorem B207623 : Blo 135790 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B305963 : Blo 135790 305963 := bstep (se 1 (by rfl) ⟨229472, by rfl⟩ : syracuseStep 305963 = 458945) B458945
theorem B207659 : Blo 135790 207659 := bstep (se 1 (by rfl) ⟨155744, by rfl⟩ : syracuseStep 207659 = 311489) B311489
theorem B437051 : Blo 135790 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B207689 : Blo 135790 207689 := bstep (se 2 (by rfl) ⟨77883, by rfl⟩ : syracuseStep 207689 = 155767) B155767
theorem B469907 : Blo 135790 469907 := bstep (se 1 (by rfl) ⟨352430, by rfl⟩ : syracuseStep 469907 = 704861) B704861
theorem B207803 : Blo 135790 207803 := bstep (se 1 (by rfl) ⟨155852, by rfl⟩ : syracuseStep 207803 = 311705) B311705
theorem B207863 : Blo 135790 207863 := bstep (se 1 (by rfl) ⟨155897, by rfl⟩ : syracuseStep 207863 = 311795) B311795
theorem B207887 : Blo 135790 207887 := bstep (se 1 (by rfl) ⟨155915, by rfl⟩ : syracuseStep 207887 = 311831) B311831
theorem B207929 : Blo 135790 207929 := bstep (se 2 (by rfl) ⟨77973, by rfl⟩ : syracuseStep 207929 = 155947) B155947
theorem B175223 : Blo 135790 175223 := bstep (se 1 (by rfl) ⟨131417, by rfl⟩ : syracuseStep 175223 = 262835) B262835
theorem B208007 : Blo 135790 208007 := bstep (se 1 (by rfl) ⟨156005, by rfl⟩ : syracuseStep 208007 = 312011) B312011
theorem B306323 : Blo 135790 306323 := bstep (se 1 (by rfl) ⟨229742, by rfl⟩ : syracuseStep 306323 = 459485) B459485
theorem B208043 : Blo 135790 208043 := bstep (se 1 (by rfl) ⟨156032, by rfl⟩ : syracuseStep 208043 = 312065) B312065
theorem B306377 : Blo 135790 306377 := bstep (se 2 (by rfl) ⟨114891, by rfl⟩ : syracuseStep 306377 = 229783) B229783
theorem B208073 : Blo 135790 208073 := bstep (se 2 (by rfl) ⟨78027, by rfl⟩ : syracuseStep 208073 = 156055) B156055
theorem B175375 : Blo 135790 175375 := bstep (se 1 (by rfl) ⟨131531, by rfl⟩ : syracuseStep 175375 = 263063) B263063
theorem B437537 : Blo 135790 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B208187 : Blo 135790 208187 := bstep (se 1 (by rfl) ⟨156140, by rfl⟩ : syracuseStep 208187 = 312281) B312281
theorem B208247 : Blo 135790 208247 := bstep (se 1 (by rfl) ⟨156185, by rfl⟩ : syracuseStep 208247 = 312371) B312371
theorem B208271 : Blo 135790 208271 := bstep (se 1 (by rfl) ⟨156203, by rfl⟩ : syracuseStep 208271 = 312407) B312407
theorem B208313 : Blo 135790 208313 := bstep (se 2 (by rfl) ⟨78117, by rfl⟩ : syracuseStep 208313 = 156235) B156235
theorem B175547 : Blo 135790 175547 := bstep (se 1 (by rfl) ⟨131660, by rfl⟩ : syracuseStep 175547 = 263321) B263321
theorem B1420753 : Blo 135790 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B208391 : Blo 135790 208391 := bstep (se 1 (by rfl) ⟨156293, by rfl⟩ : syracuseStep 208391 = 312587) B312587
theorem B208427 : Blo 135790 208427 := bstep (se 1 (by rfl) ⟨156320, by rfl⟩ : syracuseStep 208427 = 312641) B312641
theorem B208457 : Blo 135790 208457 := bstep (se 2 (by rfl) ⟨78171, by rfl⟩ : syracuseStep 208457 = 156343) B156343
theorem B208571 : Blo 135790 208571 := bstep (se 1 (by rfl) ⟨156428, by rfl⟩ : syracuseStep 208571 = 312857) B312857
theorem B208585 : Blo 135790 208585 := bstep (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) B156439
theorem B208631 : Blo 135790 208631 := bstep (se 1 (by rfl) ⟨156473, by rfl⟩ : syracuseStep 208631 = 312947) B312947
theorem B208655 : Blo 135790 208655 := bstep (se 1 (by rfl) ⟨156491, by rfl⟩ : syracuseStep 208655 = 312983) B312983
theorem B208697 : Blo 135790 208697 := bstep (se 2 (by rfl) ⟨78261, by rfl⟩ : syracuseStep 208697 = 156523) B156523
theorem B307079 : Blo 135790 307079 := bstep (se 1 (by rfl) ⟨230309, by rfl⟩ : syracuseStep 307079 = 460619) B460619
theorem B208775 : Blo 135790 208775 := bstep (se 1 (by rfl) ⟨156581, by rfl⟩ : syracuseStep 208775 = 313163) B313163
theorem B503705 : Blo 135790 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B208811 : Blo 135790 208811 := bstep (se 1 (by rfl) ⟨156608, by rfl⟩ : syracuseStep 208811 = 313217) B313217
theorem B208841 : Blo 135790 208841 := bstep (se 2 (by rfl) ⟨78315, by rfl⟩ : syracuseStep 208841 = 156631) B156631
theorem B307259 : Blo 135790 307259 := bstep (se 1 (by rfl) ⟨230444, by rfl⟩ : syracuseStep 307259 = 460889) B460889
theorem B208955 : Blo 135790 208955 := bstep (se 1 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 208955 = 313433) B313433
theorem B209015 : Blo 135790 209015 := bstep (se 1 (by rfl) ⟨156761, by rfl⟩ : syracuseStep 209015 = 313523) B313523
theorem B209039 : Blo 135790 209039 := bstep (se 1 (by rfl) ⟨156779, by rfl⟩ : syracuseStep 209039 = 313559) B313559
theorem B307385 : Blo 135790 307385 := bstep (se 2 (by rfl) ⟨115269, by rfl⟩ : syracuseStep 307385 = 230539) B230539
theorem B209081 : Blo 135790 209081 := bstep (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) B156811
theorem B209159 : Blo 135790 209159 := bstep (se 1 (by rfl) ⟨156869, by rfl⟩ : syracuseStep 209159 = 313739) B313739
theorem B2961677 : Blo 135790 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B471311 : Blo 135790 471311 := bstep (se 1 (by rfl) ⟨353483, by rfl⟩ : syracuseStep 471311 = 706967) B706967
theorem B209195 : Blo 135790 209195 := bstep (se 1 (by rfl) ⟨156896, by rfl⟩ : syracuseStep 209195 = 313793) B313793
theorem B209225 : Blo 135790 209225 := bstep (se 2 (by rfl) ⟨78459, by rfl⟩ : syracuseStep 209225 = 156919) B156919
theorem B176519 : Blo 135790 176519 := bstep (se 1 (by rfl) ⟨132389, by rfl⟩ : syracuseStep 176519 = 264779) B264779
theorem B209339 : Blo 135790 209339 := bstep (se 1 (by rfl) ⟨157004, by rfl⟩ : syracuseStep 209339 = 314009) B314009
theorem B209399 : Blo 135790 209399 := bstep (se 1 (by rfl) ⟨157049, by rfl⟩ : syracuseStep 209399 = 314099) B314099
theorem B307727 : Blo 135790 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B209423 : Blo 135790 209423 := bstep (se 1 (by rfl) ⟨157067, by rfl⟩ : syracuseStep 209423 = 314135) B314135
theorem B471581 : Blo 135790 471581 := bstep (se 3 (by rfl) ⟨88421, by rfl⟩ : syracuseStep 471581 = 176843) B176843
theorem B307745 : Blo 135790 307745 := bstep (se 2 (by rfl) ⟨115404, by rfl⟩ : syracuseStep 307745 = 230809) B230809
theorem B209465 : Blo 135790 209465 := bstep (se 2 (by rfl) ⟨78549, by rfl⟩ : syracuseStep 209465 = 157099) B157099
theorem B209543 : Blo 135790 209543 := bstep (se 1 (by rfl) ⟨157157, by rfl⟩ : syracuseStep 209543 = 314315) B314315
theorem B209579 : Blo 135790 209579 := bstep (se 1 (by rfl) ⟨157184, by rfl⟩ : syracuseStep 209579 = 314369) B314369
theorem B209609 : Blo 135790 209609 := bstep (se 2 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 209609 = 157207) B157207
theorem B2962291 : Blo 135790 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B308087 : Blo 135790 308087 := bstep (se 1 (by rfl) ⟨231065, by rfl⟩ : syracuseStep 308087 = 462131) B462131
theorem B1160203 : Blo 135790 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B439307 : Blo 135790 439307 := bstep (se 1 (by rfl) ⟨329480, by rfl⟩ : syracuseStep 439307 = 658961) B658961
theorem B308267 : Blo 135790 308267 := bstep (se 1 (by rfl) ⟨231200, by rfl⟩ : syracuseStep 308267 = 462401) B462401
theorem B210233 : Blo 135790 210233 := bstep (se 2 (by rfl) ⟨78837, by rfl⟩ : syracuseStep 210233 = 157675) B157675
theorem B308627 : Blo 135790 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B308681 : Blo 135790 308681 := bstep (se 2 (by rfl) ⟨115755, by rfl⟩ : syracuseStep 308681 = 231511) B231511
theorem B1488451 : Blo 135790 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B374387 : Blo 135790 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B210575 : Blo 135790 210575 := bstep (se 1 (by rfl) ⟨157931, by rfl⟩ : syracuseStep 210575 = 315863) B315863
theorem B669377 : Blo 135790 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B669455 : Blo 135790 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B1554227 : Blo 135790 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B374795 : Blo 135790 374795 := bstep (se 1 (by rfl) ⟨281096, by rfl⟩ : syracuseStep 374795 = 562193) B562193
theorem B440407 : Blo 135790 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B1423493 : Blo 135790 1423493 := bstep (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) B266905
theorem B309383 : Blo 135790 309383 := bstep (se 1 (by rfl) ⟨232037, by rfl⟩ : syracuseStep 309383 = 464075) B464075
theorem B374969 : Blo 135790 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B309563 : Blo 135790 309563 := bstep (se 1 (by rfl) ⟨232172, by rfl⟩ : syracuseStep 309563 = 464345) B464345
theorem B309689 : Blo 135790 309689 := bstep (se 2 (by rfl) ⟨116133, by rfl⟩ : syracuseStep 309689 = 232267) B232267
theorem B211499 : Blo 135790 211499 := bstep (se 1 (by rfl) ⟨158624, by rfl⟩ : syracuseStep 211499 = 317249) B317249
theorem B310031 : Blo 135790 310031 := bstep (se 1 (by rfl) ⟨232523, by rfl⟩ : syracuseStep 310031 = 465047) B465047
theorem B310049 : Blo 135790 310049 := bstep (se 2 (by rfl) ⟨116268, by rfl⟩ : syracuseStep 310049 = 232537) B232537
theorem B1162187 : Blo 135790 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B310391 : Blo 135790 310391 := bstep (se 1 (by rfl) ⟨232793, by rfl⟩ : syracuseStep 310391 = 465587) B465587
theorem B5717143 : Blo 135790 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B310571 : Blo 135790 310571 := bstep (se 1 (by rfl) ⟨232928, by rfl⟩ : syracuseStep 310571 = 465857) B465857
theorem B703889 : Blo 135790 703889 := bstep (se 2 (by rfl) ⟨263958, by rfl⟩ : syracuseStep 703889 = 527917) B527917
theorem B376265 : Blo 135790 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B671179 : Blo 135790 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B310931 : Blo 135790 310931 := bstep (se 1 (by rfl) ⟨233198, by rfl⟩ : syracuseStep 310931 = 466397) B466397
theorem B310985 : Blo 135790 310985 := bstep (se 2 (by rfl) ⟨116619, by rfl⟩ : syracuseStep 310985 = 233239) B233239
theorem B507833 : Blo 135790 507833 := bstep (se 2 (by rfl) ⟨190437, by rfl⟩ : syracuseStep 507833 = 380875) B380875
theorem B9257161 : Blo 135790 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B344321 : Blo 135790 344321 := bstep (se 2 (by rfl) ⟨129120, by rfl⟩ : syracuseStep 344321 = 258241) B258241
theorem B377207 : Blo 135790 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B311687 : Blo 135790 311687 := bstep (se 1 (by rfl) ⟨233765, by rfl⟩ : syracuseStep 311687 = 467531) B467531
theorem B672259 : Blo 135790 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B311867 : Blo 135790 311867 := bstep (se 1 (by rfl) ⟨233900, by rfl⟩ : syracuseStep 311867 = 467801) B467801
theorem B344695 : Blo 135790 344695 := bstep (se 1 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 344695 = 517043) B517043
theorem B311993 : Blo 135790 311993 := bstep (se 2 (by rfl) ⟨116997, by rfl⟩ : syracuseStep 311993 = 233995) B233995
theorem B2999045 : Blo 135790 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B2212697 : Blo 135790 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B279443 : Blo 135790 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B312335 : Blo 135790 312335 := bstep (se 1 (by rfl) ⟨234251, by rfl⟩ : syracuseStep 312335 = 468503) B468503
theorem B312353 : Blo 135790 312353 := bstep (se 2 (by rfl) ⟨117132, by rfl⟩ : syracuseStep 312353 = 234265) B234265
theorem B345131 : Blo 135790 345131 := bstep (se 1 (by rfl) ⟨258848, by rfl⟩ : syracuseStep 345131 = 517697) B517697
theorem B1164577 : Blo 135790 1164577 := bstep (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) B873433
theorem B312695 : Blo 135790 312695 := bstep (se 1 (by rfl) ⟨234521, by rfl⟩ : syracuseStep 312695 = 469043) B469043
theorem B705995 : Blo 135790 705995 := bstep (se 1 (by rfl) ⟨529496, by rfl⟩ : syracuseStep 705995 = 1058993) B1058993
theorem B312875 : Blo 135790 312875 := bstep (se 1 (by rfl) ⟨234656, by rfl⟩ : syracuseStep 312875 = 469313) B469313
theorem B706319 : Blo 135790 706319 := bstep (se 1 (by rfl) ⟨529739, by rfl⟩ : syracuseStep 706319 = 1059479) B1059479
theorem B345971 : Blo 135790 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B345991 : Blo 135790 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B313235 : Blo 135790 313235 := bstep (se 1 (by rfl) ⟨234926, by rfl⟩ : syracuseStep 313235 = 469853) B469853
theorem B313289 : Blo 135790 313289 := bstep (se 2 (by rfl) ⟨117483, by rfl⟩ : syracuseStep 313289 = 234967) B234967
theorem B837643 : Blo 135790 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B1656949 : Blo 135790 1656949 := bstep (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) B155339
theorem B313463 : Blo 135790 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B346265 : Blo 135790 346265 := bstep (se 2 (by rfl) ⟨129849, by rfl⟩ : syracuseStep 346265 = 259699) B259699
theorem B346427 : Blo 135790 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B346639 : Blo 135790 346639 := bstep (se 1 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 346639 = 519959) B519959
theorem B739901 : Blo 135790 739901 := bstep (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) B277463
theorem B313991 : Blo 135790 313991 := bstep (se 1 (by rfl) ⟨235493, by rfl⟩ : syracuseStep 313991 = 470987) B470987
theorem B346913 : Blo 135790 346913 := bstep (se 2 (by rfl) ⟨130092, by rfl⟩ : syracuseStep 346913 = 260185) B260185
theorem B314171 : Blo 135790 314171 := bstep (se 1 (by rfl) ⟨235628, by rfl⟩ : syracuseStep 314171 = 471257) B471257
theorem B314297 : Blo 135790 314297 := bstep (se 2 (by rfl) ⟨117861, by rfl⟩ : syracuseStep 314297 = 235723) B235723
theorem B281615 : Blo 135790 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B1035665 : Blo 135790 1035665 := bstep (se 2 (by rfl) ⟨388374, by rfl⟩ : syracuseStep 1035665 = 776749) B776749
theorem B1691201 : Blo 135790 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B740983 : Blo 135790 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B773833 : Blo 135790 773833 := bstep (se 2 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 773833 = 580375) B580375
theorem B347915 : Blo 135790 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B1200215 : Blo 135790 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B348563 : Blo 135790 348563 := bstep (se 1 (by rfl) ⟨261422, by rfl⟩ : syracuseStep 348563 = 522845) B522845
theorem B446867 : Blo 135790 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B348857 : Blo 135790 348857 := bstep (se 2 (by rfl) ⟨130821, by rfl⟩ : syracuseStep 348857 = 261643) B261643
theorem B414665 : Blo 135790 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B218231 : Blo 135790 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B742715 : Blo 135790 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B349555 : Blo 135790 349555 := bstep (se 1 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 349555 = 524333) B524333
theorem B349697 : Blo 135790 349697 := bstep (se 2 (by rfl) ⟨131136, by rfl⟩ : syracuseStep 349697 = 262273) B262273
theorem B153103 : Blo 135790 153103 := bstep (se 1 (by rfl) ⟨114827, by rfl⟩ : syracuseStep 153103 = 229655) B229655
theorem B1038095 : Blo 135790 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B350153 : Blo 135790 350153 := bstep (se 2 (by rfl) ⟨131307, by rfl⟩ : syracuseStep 350153 = 262615) B262615
theorem B153607 : Blo 135790 153607 := bstep (se 1 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 153607 = 230411) B230411
theorem B87447605 : Blo 135790 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1005655 : Blo 135790 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B153787 : Blo 135790 153787 := bstep (se 1 (by rfl) ⟨115340, by rfl⟩ : syracuseStep 153787 = 230681) B230681
theorem B2840777 : Blo 135790 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B350507 : Blo 135790 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B219691 : Blo 135790 219691 := bstep (se 1 (by rfl) ⟨164768, by rfl⟩ : syracuseStep 219691 = 329537) B329537
theorem B481879 : Blo 135790 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B154255 : Blo 135790 154255 := bstep (se 1 (by rfl) ⟨115691, by rfl⟩ : syracuseStep 154255 = 231383) B231383
theorem B875279 : Blo 135790 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B154759 : Blo 135790 154759 := bstep (se 1 (by rfl) ⟨116069, by rfl⟩ : syracuseStep 154759 = 232139) B232139
theorem B711937 : Blo 135790 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B351499 : Blo 135790 351499 := bstep (se 1 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 351499 = 527249) B527249
theorem B154939 : Blo 135790 154939 := bstep (se 1 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 154939 = 232409) B232409
theorem B351641 : Blo 135790 351641 := bstep (se 2 (by rfl) ⟨131865, by rfl⟩ : syracuseStep 351641 = 263731) B263731
theorem B351803 : Blo 135790 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B155407 : Blo 135790 155407 := bstep (se 1 (by rfl) ⟨116555, by rfl⟩ : syracuseStep 155407 = 233111) B233111
theorem B352147 : Blo 135790 352147 := bstep (se 1 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 352147 = 528221) B528221
theorem B745483 : Blo 135790 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B352289 : Blo 135790 352289 := bstep (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) B264217
theorem B1695917 : Blo 135790 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B188663 : Blo 135790 188663 := bstep (se 1 (by rfl) ⟨141497, by rfl⟩ : syracuseStep 188663 = 282995) B282995
theorem B155911 : Blo 135790 155911 := bstep (se 1 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 155911 = 233867) B233867
theorem B156091 : Blo 135790 156091 := bstep (se 1 (by rfl) ⟨117068, by rfl⟩ : syracuseStep 156091 = 234137) B234137
theorem B582187 : Blo 135790 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B680737 : Blo 135790 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B156559 : Blo 135790 156559 := bstep (se 1 (by rfl) ⟨117419, by rfl⟩ : syracuseStep 156559 = 234839) B234839
theorem B680849 : Blo 135790 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B353281 : Blo 135790 353281 := bstep (se 2 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 353281 = 264961) B264961
theorem B3433859 : Blo 135790 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B157063 : Blo 135790 157063 := bstep (se 1 (by rfl) ⟨117797, by rfl⟩ : syracuseStep 157063 = 235595) B235595
theorem B779665 : Blo 135790 779665 := bstep (se 2 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 779665 = 584749) B584749
theorem B517529 : Blo 135790 517529 := bstep (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) B388147
theorem B157243 : Blo 135790 157243 := bstep (se 1 (by rfl) ⟨117932, by rfl⟩ : syracuseStep 157243 = 235865) B235865
theorem B353977 : Blo 135790 353977 := bstep (se 2 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 353977 = 265483) B265483
theorem B386849 : Blo 135790 386849 := bstep (se 2 (by rfl) ⟨145068, by rfl⟩ : syracuseStep 386849 = 290137) B290137
theorem B419699 : Blo 135790 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B386963 : Blo 135790 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B223177 : Blo 135790 223177 := bstep (se 2 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 223177 = 167383) B167383
theorem B387737 : Blo 135790 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B748205 : Blo 135790 748205 := bstep (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) B280577
theorem B1174661 : Blo 135790 1174661 := bstep (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) B220249
theorem B1240379 : Blo 135790 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B1568375 : Blo 135790 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B782081 : Blo 135790 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B552851 : Blo 135790 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B1339415 : Blo 135790 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B2945069 : Blo 135790 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B258167 : Blo 135790 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B422023 : Blo 135790 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B389377 : Blo 135790 389377 := bstep (se 2 (by rfl) ⟨146016, by rfl⟩ : syracuseStep 389377 = 292033) B292033
theorem B586511 : Blo 135790 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B389947 : Blo 135790 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B521113 : Blo 135790 521113 := bstep (se 2 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 521113 = 390835) B390835
theorem B193595 : Blo 135790 193595 := bstep (se 1 (by rfl) ⟨145196, by rfl⟩ : syracuseStep 193595 = 290393) B290393
theorem B423031 : Blo 135790 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B292025 : Blo 135790 292025 := bstep (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) B219019
theorem B521417 : Blo 135790 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B259463 : Blo 135790 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B980369 : Blo 135790 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B194233 : Blo 135790 194233 := bstep (se 2 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 194233 = 145675) B145675
theorem B358145 : Blo 135790 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B194347 : Blo 135790 194347 := bstep (se 1 (by rfl) ⟨145760, by rfl⟩ : syracuseStep 194347 = 291521) B291521
theorem B1996595 : Blo 135790 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B784313 : Blo 135790 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B194575 : Blo 135790 194575 := bstep (se 1 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 194575 = 291863) B291863
theorem B522359 : Blo 135790 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B981229 : Blo 135790 981229 := bstep (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) B367961
theorem B784673 : Blo 135790 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B1669409 : Blo 135790 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B1046843 : Blo 135790 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B588167 : Blo 135790 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B883457 : Blo 135790 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B391969 : Blo 135790 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B555835 : Blo 135790 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B195463 : Blo 135790 195463 := bstep (se 1 (by rfl) ⟨146597, by rfl⟩ : syracuseStep 195463 = 293195) B293195
theorem B523331 : Blo 135790 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B392339 : Blo 135790 392339 := bstep (se 1 (by rfl) ⟨294254, by rfl⟩ : syracuseStep 392339 = 588509) B588509
theorem B195959 : Blo 135790 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B490961 : Blo 135790 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B261947 : Blo 135790 261947 := bstep (se 1 (by rfl) ⟨196460, by rfl⟩ : syracuseStep 261947 = 392921) B392921
theorem B393113 : Blo 135790 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B229385 : Blo 135790 229385 := bstep (se 2 (by rfl) ⟨86019, by rfl⟩ : syracuseStep 229385 = 172039) B172039
theorem B524303 : Blo 135790 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B1572941 : Blo 135790 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B229547 : Blo 135790 229547 := bstep (se 1 (by rfl) ⟨172160, by rfl⟩ : syracuseStep 229547 = 344321) B344321
theorem B458999 : Blo 135790 458999 := bstep (se 1 (by rfl) ⟨344249, by rfl⟩ : syracuseStep 458999 = 688499) B688499
theorem B1245451 : Blo 135790 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1573181 : Blo 135790 1573181 := bstep (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) B589943
theorem B688445 : Blo 135790 688445 := bstep (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) B258167
theorem B1999363 : Blo 135790 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1180169 : Blo 135790 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B932774453 : Blo 135790 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B229945 : Blo 135790 229945 := bstep (se 2 (by rfl) ⟨86229, by rfl⟩ : syracuseStep 229945 = 172459) B172459
theorem B459323 : Blo 135790 459323 := bstep (se 1 (by rfl) ⟨344492, by rfl⟩ : syracuseStep 459323 = 688985) B688985
theorem B2228795 : Blo 135790 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B1049273 : Blo 135790 1049273 := bstep (se 2 (by rfl) ⟨393477, by rfl⟩ : syracuseStep 1049273 = 786955) B786955
theorem B230087 : Blo 135790 230087 := bstep (se 1 (by rfl) ⟨172565, by rfl⟩ : syracuseStep 230087 = 345131) B345131
theorem B393943 : Blo 135790 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B787229 : Blo 135790 787229 := bstep (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) B295211
theorem B459593 : Blo 135790 459593 := bstep (se 2 (by rfl) ⟨172347, by rfl⟩ : syracuseStep 459593 = 344695) B344695
theorem B230249 : Blo 135790 230249 := bstep (se 2 (by rfl) ⟨86343, by rfl⟩ : syracuseStep 230249 = 172687) B172687
theorem B263017 : Blo 135790 263017 := bstep (se 2 (by rfl) ⟨98631, by rfl⟩ : syracuseStep 263017 = 197263) B197263
theorem B328711 : Blo 135790 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B230647 : Blo 135790 230647 := bstep (se 1 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 230647 = 345971) B345971
theorem B230843 : Blo 135790 230843 := bstep (se 1 (by rfl) ⟨173132, by rfl⟩ : syracuseStep 230843 = 346265) B346265
theorem B787913 : Blo 135790 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B230951 : Blo 135790 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B1050245 : Blo 135790 1050245 := bstep (se 4 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 1050245 = 196921) B196921
theorem B525959 : Blo 135790 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B263891 : Blo 135790 263891 := bstep (se 1 (by rfl) ⟨197918, by rfl⟩ : syracuseStep 263891 = 395837) B395837
theorem B231241 : Blo 135790 231241 := bstep (se 2 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 231241 = 173431) B173431
theorem B231275 : Blo 135790 231275 := bstep (se 1 (by rfl) ⟨173456, by rfl⟩ : syracuseStep 231275 = 346913) B346913
theorem B460727 : Blo 135790 460727 := bstep (se 1 (by rfl) ⟨345545, by rfl⟩ : syracuseStep 460727 = 691091) B691091
theorem B329807 : Blo 135790 329807 := bstep (se 1 (by rfl) ⟨247355, by rfl⟩ : syracuseStep 329807 = 494711) B494711
theorem B5900525 : Blo 135790 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B231673 : Blo 135790 231673 := bstep (se 2 (by rfl) ⟨86877, by rfl⟩ : syracuseStep 231673 = 173755) B173755
theorem B690443 : Blo 135790 690443 := bstep (se 1 (by rfl) ⟨517832, by rfl⟩ : syracuseStep 690443 = 1035665) B1035665
theorem B264521 : Blo 135790 264521 := bstep (se 2 (by rfl) ⟨99195, by rfl⟩ : syracuseStep 264521 = 198391) B198391
theorem B231943 : Blo 135790 231943 := bstep (se 1 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 231943 = 347915) B347915
theorem B461321 : Blo 135790 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B526945 : Blo 135790 526945 := bstep (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) B395209
theorem B297569 : Blo 135790 297569 := bstep (se 2 (by rfl) ⟨111588, by rfl⟩ : syracuseStep 297569 = 223177) B223177
theorem B1116857 : Blo 135790 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B232375 : Blo 135790 232375 := bstep (se 1 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 232375 = 348563) B348563
theorem B297911 : Blo 135790 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B527417 : Blo 135790 527417 := bstep (se 2 (by rfl) ⟨197781, by rfl⟩ : syracuseStep 527417 = 395563) B395563
theorem B265295 : Blo 135790 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B232571 : Blo 135790 232571 := bstep (se 1 (by rfl) ⟨174428, by rfl⟩ : syracuseStep 232571 = 348857) B348857
theorem B1510595 : Blo 135790 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B462185 : Blo 135790 462185 := bstep (se 2 (by rfl) ⟨173319, by rfl⟩ : syracuseStep 462185 = 346639) B346639
theorem B560621 : Blo 135790 560621 := bstep (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) B210233
theorem B396809 : Blo 135790 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B232969 : Blo 135790 232969 := bstep (se 2 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 232969 = 174727) B174727
theorem B495143 : Blo 135790 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B396839 : Blo 135790 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B233131 : Blo 135790 233131 := bstep (se 1 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 233131 = 349697) B349697
theorem B691901 : Blo 135790 691901 := bstep (se 3 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 691901 = 259463) B259463
theorem B692063 : Blo 135790 692063 := bstep (se 1 (by rfl) ⟨519047, by rfl⟩ : syracuseStep 692063 = 1038095) B1038095
theorem B462779 : Blo 135790 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B233435 : Blo 135790 233435 := bstep (se 1 (by rfl) ⟨175076, by rfl⟩ : syracuseStep 233435 = 350153) B350153
theorem B1052675 : Blo 135790 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B528403 : Blo 135790 528403 := bstep (se 1 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 528403 = 792605) B792605
theorem B233671 : Blo 135790 233671 := bstep (se 1 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 233671 = 350507) B350507
theorem B233833 : Blo 135790 233833 := bstep (se 2 (by rfl) ⟨87687, by rfl⟩ : syracuseStep 233833 = 175375) B175375
theorem B889325 : Blo 135790 889325 := bstep (se 3 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 889325 = 333497) B333497
theorem B135803 : Blo 135790 135803 := bstep (se 1 (by rfl) ⟨101852, by rfl⟩ : syracuseStep 135803 = 203705) B203705
theorem B135855 : Blo 135790 135855 := bstep (se 1 (by rfl) ⟨101891, by rfl⟩ : syracuseStep 135855 = 203783) B203783
theorem B135879 : Blo 135790 135879 := bstep (se 1 (by rfl) ⟨101909, by rfl⟩ : syracuseStep 135879 = 203819) B203819
theorem B135899 : Blo 135790 135899 := bstep (se 1 (by rfl) ⟨101924, by rfl⟩ : syracuseStep 135899 = 203849) B203849
theorem B135975 : Blo 135790 135975 := bstep (se 1 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 135975 = 203963) B203963
theorem B987977 : Blo 135790 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B136015 : Blo 135790 136015 := bstep (se 1 (by rfl) ⟨102011, by rfl⟩ : syracuseStep 136015 = 204023) B204023
theorem B136031 : Blo 135790 136031 := bstep (se 1 (by rfl) ⟨102023, by rfl⟩ : syracuseStep 136031 = 204047) B204047
theorem B136059 : Blo 135790 136059 := bstep (se 1 (by rfl) ⟨102044, by rfl⟩ : syracuseStep 136059 = 204089) B204089
theorem B136111 : Blo 135790 136111 := bstep (se 1 (by rfl) ⟨102083, by rfl⟩ : syracuseStep 136111 = 204167) B204167
theorem B234427 : Blo 135790 234427 := bstep (se 1 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 234427 = 351641) B351641
theorem B136135 : Blo 135790 136135 := bstep (se 1 (by rfl) ⟨102101, by rfl⟩ : syracuseStep 136135 = 204203) B204203
theorem B136155 : Blo 135790 136155 := bstep (se 1 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 136155 = 204233) B204233
theorem B1119197 : Blo 135790 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B136231 : Blo 135790 136231 := bstep (se 1 (by rfl) ⟨102173, by rfl⟩ : syracuseStep 136231 = 204347) B204347
theorem B234535 : Blo 135790 234535 := bstep (se 1 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 234535 = 351803) B351803
theorem B791603 : Blo 135790 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B136271 : Blo 135790 136271 := bstep (se 1 (by rfl) ⟨102203, by rfl⟩ : syracuseStep 136271 = 204407) B204407
theorem B136287 : Blo 135790 136287 := bstep (se 1 (by rfl) ⟨102215, by rfl⟩ : syracuseStep 136287 = 204431) B204431
theorem B136315 : Blo 135790 136315 := bstep (se 1 (by rfl) ⟨102236, by rfl⟩ : syracuseStep 136315 = 204473) B204473
theorem B136367 : Blo 135790 136367 := bstep (se 1 (by rfl) ⟨102275, by rfl⟩ : syracuseStep 136367 = 204551) B204551
theorem B136391 : Blo 135790 136391 := bstep (se 1 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 136391 = 204587) B204587
theorem B136411 : Blo 135790 136411 := bstep (se 1 (by rfl) ⟨102308, by rfl⟩ : syracuseStep 136411 = 204617) B204617
theorem B136487 : Blo 135790 136487 := bstep (se 1 (by rfl) ⟨102365, by rfl⟩ : syracuseStep 136487 = 204731) B204731
theorem B136527 : Blo 135790 136527 := bstep (se 1 (by rfl) ⟨102395, by rfl⟩ : syracuseStep 136527 = 204791) B204791
theorem B136543 : Blo 135790 136543 := bstep (se 1 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 136543 = 204815) B204815
theorem B234859 : Blo 135790 234859 := bstep (se 1 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 234859 = 352289) B352289
theorem B136571 : Blo 135790 136571 := bstep (se 1 (by rfl) ⟨102428, by rfl⟩ : syracuseStep 136571 = 204857) B204857
theorem B595343 : Blo 135790 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B136623 : Blo 135790 136623 := bstep (se 1 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 136623 = 204935) B204935
theorem B136647 : Blo 135790 136647 := bstep (se 1 (by rfl) ⟨102485, by rfl⟩ : syracuseStep 136647 = 204971) B204971
theorem B136667 : Blo 135790 136667 := bstep (se 1 (by rfl) ⟨102500, by rfl⟩ : syracuseStep 136667 = 205001) B205001
theorem B2299355 : Blo 135790 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B562697 : Blo 135790 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B136743 : Blo 135790 136743 := bstep (se 1 (by rfl) ⟨102557, by rfl⟩ : syracuseStep 136743 = 205115) B205115
theorem B136783 : Blo 135790 136783 := bstep (se 1 (by rfl) ⟨102587, by rfl⟩ : syracuseStep 136783 = 205175) B205175
theorem B136799 : Blo 135790 136799 := bstep (se 1 (by rfl) ⟨102599, by rfl⟩ : syracuseStep 136799 = 205199) B205199
theorem B136827 : Blo 135790 136827 := bstep (se 1 (by rfl) ⟨102620, by rfl⟩ : syracuseStep 136827 = 205241) B205241
theorem B464507 : Blo 135790 464507 := bstep (se 1 (by rfl) ⟨348380, by rfl⟩ : syracuseStep 464507 = 696761) B696761
theorem B136879 : Blo 135790 136879 := bstep (se 1 (by rfl) ⟨102659, by rfl⟩ : syracuseStep 136879 = 205319) B205319
theorem B136903 : Blo 135790 136903 := bstep (se 1 (by rfl) ⟨102677, by rfl⟩ : syracuseStep 136903 = 205355) B205355
theorem B530135 : Blo 135790 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B136923 : Blo 135790 136923 := bstep (se 1 (by rfl) ⟨102692, by rfl⟩ : syracuseStep 136923 = 205385) B205385
theorem B464669 : Blo 135790 464669 := bstep (se 3 (by rfl) ⟨87125, by rfl⟩ : syracuseStep 464669 = 174251) B174251
theorem B136999 : Blo 135790 136999 := bstep (se 1 (by rfl) ⟨102749, by rfl⟩ : syracuseStep 136999 = 205499) B205499
theorem B137039 : Blo 135790 137039 := bstep (se 1 (by rfl) ⟨102779, by rfl⟩ : syracuseStep 137039 = 205559) B205559
theorem B137055 : Blo 135790 137055 := bstep (se 1 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 137055 = 205583) B205583
theorem B137083 : Blo 135790 137083 := bstep (se 1 (by rfl) ⟨102812, by rfl⟩ : syracuseStep 137083 = 205625) B205625
theorem B137135 : Blo 135790 137135 := bstep (se 1 (by rfl) ⟨102851, by rfl⟩ : syracuseStep 137135 = 205703) B205703
theorem B137159 : Blo 135790 137159 := bstep (se 1 (by rfl) ⟨102869, by rfl⟩ : syracuseStep 137159 = 205739) B205739
theorem B137179 : Blo 135790 137179 := bstep (se 1 (by rfl) ⟨102884, by rfl⟩ : syracuseStep 137179 = 205769) B205769
theorem B137255 : Blo 135790 137255 := bstep (se 1 (by rfl) ⟨102941, by rfl⟩ : syracuseStep 137255 = 205883) B205883
theorem B137295 : Blo 135790 137295 := bstep (se 1 (by rfl) ⟨102971, by rfl⟩ : syracuseStep 137295 = 205943) B205943
theorem B137311 : Blo 135790 137311 := bstep (se 1 (by rfl) ⟨102983, by rfl⟩ : syracuseStep 137311 = 205967) B205967
theorem B137339 : Blo 135790 137339 := bstep (se 1 (by rfl) ⟨103004, by rfl⟩ : syracuseStep 137339 = 206009) B206009
theorem B137391 : Blo 135790 137391 := bstep (se 1 (by rfl) ⟨103043, by rfl⟩ : syracuseStep 137391 = 206087) B206087
theorem B137415 : Blo 135790 137415 := bstep (se 1 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 137415 = 206123) B206123
theorem B137435 : Blo 135790 137435 := bstep (se 1 (by rfl) ⟨103076, by rfl⟩ : syracuseStep 137435 = 206153) B206153
theorem B137511 : Blo 135790 137511 := bstep (se 1 (by rfl) ⟨103133, by rfl⟩ : syracuseStep 137511 = 206267) B206267
theorem B137551 : Blo 135790 137551 := bstep (se 1 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 137551 = 206327) B206327
theorem B137567 : Blo 135790 137567 := bstep (se 1 (by rfl) ⟨103175, by rfl⟩ : syracuseStep 137567 = 206351) B206351
theorem B137595 : Blo 135790 137595 := bstep (se 1 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 137595 = 206393) B206393
theorem B1055105 : Blo 135790 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B137647 : Blo 135790 137647 := bstep (se 1 (by rfl) ⟨103235, by rfl⟩ : syracuseStep 137647 = 206471) B206471
theorem B137671 : Blo 135790 137671 := bstep (se 1 (by rfl) ⟨103253, by rfl⟩ : syracuseStep 137671 = 206507) B206507
theorem B137691 : Blo 135790 137691 := bstep (se 1 (by rfl) ⟨103268, by rfl⟩ : syracuseStep 137691 = 206537) B206537
theorem B465371 : Blo 135790 465371 := bstep (se 1 (by rfl) ⟨349028, by rfl⟩ : syracuseStep 465371 = 698057) B698057
theorem B694817 : Blo 135790 694817 := bstep (se 2 (by rfl) ⟨260556, by rfl⟩ : syracuseStep 694817 = 521113) B521113
theorem B137767 : Blo 135790 137767 := bstep (se 1 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 137767 = 206651) B206651
theorem B137807 : Blo 135790 137807 := bstep (se 1 (by rfl) ⟨103355, by rfl⟩ : syracuseStep 137807 = 206711) B206711
theorem B137823 : Blo 135790 137823 := bstep (se 1 (by rfl) ⟨103367, by rfl⟩ : syracuseStep 137823 = 206735) B206735
theorem B137851 : Blo 135790 137851 := bstep (se 1 (by rfl) ⟨103388, by rfl⟩ : syracuseStep 137851 = 206777) B206777
theorem B137903 : Blo 135790 137903 := bstep (se 1 (by rfl) ⟨103427, by rfl⟩ : syracuseStep 137903 = 206855) B206855
theorem B1546937 : Blo 135790 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B137927 : Blo 135790 137927 := bstep (se 1 (by rfl) ⟨103445, by rfl⟩ : syracuseStep 137927 = 206891) B206891
theorem B137947 : Blo 135790 137947 := bstep (se 1 (by rfl) ⟨103460, by rfl⟩ : syracuseStep 137947 = 206921) B206921
theorem B138023 : Blo 135790 138023 := bstep (se 1 (by rfl) ⟨103517, by rfl⟩ : syracuseStep 138023 = 207035) B207035
theorem B564041 : Blo 135790 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B1973069 : Blo 135790 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B138063 : Blo 135790 138063 := bstep (se 1 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 138063 = 207095) B207095
theorem B138079 : Blo 135790 138079 := bstep (se 1 (by rfl) ⟨103559, by rfl⟩ : syracuseStep 138079 = 207119) B207119
theorem B138107 : Blo 135790 138107 := bstep (se 1 (by rfl) ⟨103580, by rfl⟩ : syracuseStep 138107 = 207161) B207161
theorem B138159 : Blo 135790 138159 := bstep (se 1 (by rfl) ⟨103619, by rfl⟩ : syracuseStep 138159 = 207239) B207239
theorem B138183 : Blo 135790 138183 := bstep (se 1 (by rfl) ⟨103637, by rfl⟩ : syracuseStep 138183 = 207275) B207275
theorem B138203 : Blo 135790 138203 := bstep (se 1 (by rfl) ⟨103652, by rfl⟩ : syracuseStep 138203 = 207305) B207305
theorem B138279 : Blo 135790 138279 := bstep (se 1 (by rfl) ⟨103709, by rfl⟩ : syracuseStep 138279 = 207419) B207419
theorem B203855 : Blo 135790 203855 := bstep (se 1 (by rfl) ⟨152891, by rfl⟩ : syracuseStep 203855 = 305783) B305783
theorem B138319 : Blo 135790 138319 := bstep (se 1 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 138319 = 207479) B207479
theorem B138335 : Blo 135790 138335 := bstep (se 1 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 138335 = 207503) B207503
theorem B498803 : Blo 135790 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B138363 : Blo 135790 138363 := bstep (se 1 (by rfl) ⟨103772, by rfl⟩ : syracuseStep 138363 = 207545) B207545
theorem B466073 : Blo 135790 466073 := bstep (se 2 (by rfl) ⟨174777, by rfl⟩ : syracuseStep 466073 = 349555) B349555
theorem B138415 : Blo 135790 138415 := bstep (se 1 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 138415 = 207623) B207623
theorem B203975 : Blo 135790 203975 := bstep (se 1 (by rfl) ⟨152981, by rfl⟩ : syracuseStep 203975 = 305963) B305963
theorem B138439 : Blo 135790 138439 := bstep (se 1 (by rfl) ⟨103829, by rfl⟩ : syracuseStep 138439 = 207659) B207659
theorem B138459 : Blo 135790 138459 := bstep (se 1 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 138459 = 207689) B207689
theorem B138535 : Blo 135790 138535 := bstep (se 1 (by rfl) ⟨103901, by rfl⟩ : syracuseStep 138535 = 207803) B207803
theorem B138575 : Blo 135790 138575 := bstep (se 1 (by rfl) ⟨103931, by rfl⟩ : syracuseStep 138575 = 207863) B207863
theorem B138591 : Blo 135790 138591 := bstep (se 1 (by rfl) ⟨103943, by rfl⟩ : syracuseStep 138591 = 207887) B207887
theorem B204137 : Blo 135790 204137 := bstep (se 2 (by rfl) ⟨76551, by rfl⟩ : syracuseStep 204137 = 153103) B153103
theorem B138619 : Blo 135790 138619 := bstep (se 1 (by rfl) ⟨103964, by rfl⟩ : syracuseStep 138619 = 207929) B207929
theorem B138671 : Blo 135790 138671 := bstep (se 1 (by rfl) ⟨104003, by rfl⟩ : syracuseStep 138671 = 208007) B208007
theorem B204215 : Blo 135790 204215 := bstep (se 1 (by rfl) ⟨153161, by rfl⟩ : syracuseStep 204215 = 306323) B306323
theorem B138695 : Blo 135790 138695 := bstep (se 1 (by rfl) ⟨104021, by rfl⟩ : syracuseStep 138695 = 208043) B208043
theorem B204251 : Blo 135790 204251 := bstep (se 1 (by rfl) ⟨153188, by rfl⟩ : syracuseStep 204251 = 306377) B306377
theorem B138715 : Blo 135790 138715 := bstep (se 1 (by rfl) ⟨104036, by rfl⟩ : syracuseStep 138715 = 208073) B208073
theorem B826919 : Blo 135790 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B138791 : Blo 135790 138791 := bstep (se 1 (by rfl) ⟨104093, by rfl⟩ : syracuseStep 138791 = 208187) B208187
theorem B138831 : Blo 135790 138831 := bstep (se 1 (by rfl) ⟨104123, by rfl⟩ : syracuseStep 138831 = 208247) B208247
theorem B138847 : Blo 135790 138847 := bstep (se 1 (by rfl) ⟨104135, by rfl⟩ : syracuseStep 138847 = 208271) B208271
theorem B138875 : Blo 135790 138875 := bstep (se 1 (by rfl) ⟨104156, by rfl⟩ : syracuseStep 138875 = 208313) B208313
theorem B138927 : Blo 135790 138927 := bstep (se 1 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 138927 = 208391) B208391
theorem B138951 : Blo 135790 138951 := bstep (se 1 (by rfl) ⟨104213, by rfl⟩ : syracuseStep 138951 = 208427) B208427
theorem B138971 : Blo 135790 138971 := bstep (se 1 (by rfl) ⟨104228, by rfl⟩ : syracuseStep 138971 = 208457) B208457
theorem B139047 : Blo 135790 139047 := bstep (se 1 (by rfl) ⟨104285, by rfl⟩ : syracuseStep 139047 = 208571) B208571
theorem B139087 : Blo 135790 139087 := bstep (se 1 (by rfl) ⟨104315, by rfl⟩ : syracuseStep 139087 = 208631) B208631
theorem B139103 : Blo 135790 139103 := bstep (se 1 (by rfl) ⟨104327, by rfl⟩ : syracuseStep 139103 = 208655) B208655
theorem B139131 : Blo 135790 139131 := bstep (se 1 (by rfl) ⟨104348, by rfl⟩ : syracuseStep 139131 = 208697) B208697
theorem B204719 : Blo 135790 204719 := bstep (se 1 (by rfl) ⟨153539, by rfl⟩ : syracuseStep 204719 = 307079) B307079
theorem B139183 : Blo 135790 139183 := bstep (se 1 (by rfl) ⟨104387, by rfl⟩ : syracuseStep 139183 = 208775) B208775
theorem B368567 : Blo 135790 368567 := bstep (se 1 (by rfl) ⟨276425, by rfl⟩ : syracuseStep 368567 = 552851) B552851
theorem B139207 : Blo 135790 139207 := bstep (se 1 (by rfl) ⟨104405, by rfl⟩ : syracuseStep 139207 = 208811) B208811
theorem B139227 : Blo 135790 139227 := bstep (se 1 (by rfl) ⟨104420, by rfl⟩ : syracuseStep 139227 = 208841) B208841
theorem B204809 : Blo 135790 204809 := bstep (se 2 (by rfl) ⟨76803, by rfl⟩ : syracuseStep 204809 = 153607) B153607
theorem B892943 : Blo 135790 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B204839 : Blo 135790 204839 := bstep (se 1 (by rfl) ⟨153629, by rfl⟩ : syracuseStep 204839 = 307259) B307259
theorem B139303 : Blo 135790 139303 := bstep (se 1 (by rfl) ⟨104477, by rfl⟩ : syracuseStep 139303 = 208955) B208955
theorem B139343 : Blo 135790 139343 := bstep (se 1 (by rfl) ⟨104507, by rfl⟩ : syracuseStep 139343 = 209015) B209015
theorem B139359 : Blo 135790 139359 := bstep (se 1 (by rfl) ⟨104519, by rfl⟩ : syracuseStep 139359 = 209039) B209039
theorem B204923 : Blo 135790 204923 := bstep (se 1 (by rfl) ⟨153692, by rfl⟩ : syracuseStep 204923 = 307385) B307385
theorem B139387 : Blo 135790 139387 := bstep (se 1 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 139387 = 209081) B209081
theorem B139439 : Blo 135790 139439 := bstep (se 1 (by rfl) ⟨104579, by rfl⟩ : syracuseStep 139439 = 209159) B209159
theorem B1974451 : Blo 135790 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B139463 : Blo 135790 139463 := bstep (se 1 (by rfl) ⟨104597, by rfl⟩ : syracuseStep 139463 = 209195) B209195
theorem B139483 : Blo 135790 139483 := bstep (se 1 (by rfl) ⟨104612, by rfl⟩ : syracuseStep 139483 = 209225) B209225
theorem B205049 : Blo 135790 205049 := bstep (se 2 (by rfl) ⟨76893, by rfl⟩ : syracuseStep 205049 = 153787) B153787
theorem B139559 : Blo 135790 139559 := bstep (se 1 (by rfl) ⟨104669, by rfl⟩ : syracuseStep 139559 = 209339) B209339
theorem B467261 : Blo 135790 467261 := bstep (se 3 (by rfl) ⟨87611, by rfl⟩ : syracuseStep 467261 = 175223) B175223
theorem B139599 : Blo 135790 139599 := bstep (se 1 (by rfl) ⟨104699, by rfl⟩ : syracuseStep 139599 = 209399) B209399
theorem B205151 : Blo 135790 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B139615 : Blo 135790 139615 := bstep (se 1 (by rfl) ⟨104711, by rfl⟩ : syracuseStep 139615 = 209423) B209423
theorem B205163 : Blo 135790 205163 := bstep (se 1 (by rfl) ⟨153872, by rfl⟩ : syracuseStep 205163 = 307745) B307745
theorem B139643 : Blo 135790 139643 := bstep (se 1 (by rfl) ⟨104732, by rfl⟩ : syracuseStep 139643 = 209465) B209465
theorem B139695 : Blo 135790 139695 := bstep (se 1 (by rfl) ⟨104771, by rfl⟩ : syracuseStep 139695 = 209543) B209543
theorem B139719 : Blo 135790 139719 := bstep (se 1 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 139719 = 209579) B209579
theorem B139739 : Blo 135790 139739 := bstep (se 1 (by rfl) ⟨104804, by rfl⟩ : syracuseStep 139739 = 209609) B209609
theorem B205391 : Blo 135790 205391 := bstep (se 1 (by rfl) ⟨154043, by rfl⟩ : syracuseStep 205391 = 308087) B308087
theorem B205511 : Blo 135790 205511 := bstep (se 1 (by rfl) ⟨154133, by rfl⟩ : syracuseStep 205511 = 308267) B308267
theorem B205673 : Blo 135790 205673 := bstep (se 2 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 205673 = 154255) B154255
theorem B205751 : Blo 135790 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B205787 : Blo 135790 205787 := bstep (se 1 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 205787 = 308681) B308681
theorem B140383 : Blo 135790 140383 := bstep (se 1 (by rfl) ⟨105287, by rfl⟩ : syracuseStep 140383 = 210575) B210575
theorem B468125 : Blo 135790 468125 := bstep (se 3 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 468125 = 175547) B175547
theorem B238763 : Blo 135790 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B206255 : Blo 135790 206255 := bstep (se 1 (by rfl) ⟨154691, by rfl⟩ : syracuseStep 206255 = 309383) B309383
theorem B206345 : Blo 135790 206345 := bstep (se 2 (by rfl) ⟨77379, by rfl⟩ : syracuseStep 206345 = 154759) B154759
theorem B206375 : Blo 135790 206375 := bstep (se 1 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 206375 = 309563) B309563
theorem B697895 : Blo 135790 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B206459 : Blo 135790 206459 := bstep (se 1 (by rfl) ⟨154844, by rfl⟩ : syracuseStep 206459 = 309689) B309689
theorem B468665 : Blo 135790 468665 := bstep (se 2 (by rfl) ⟨175749, by rfl⟩ : syracuseStep 468665 = 351499) B351499
theorem B140999 : Blo 135790 140999 := bstep (se 1 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 140999 = 211499) B211499
theorem B206585 : Blo 135790 206585 := bstep (se 2 (by rfl) ⟨77469, by rfl⟩ : syracuseStep 206585 = 154939) B154939
theorem B206687 : Blo 135790 206687 := bstep (se 1 (by rfl) ⟨155015, by rfl⟩ : syracuseStep 206687 = 310031) B310031
theorem B206699 : Blo 135790 206699 := bstep (se 1 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 206699 = 310049) B310049
theorem B1058669 : Blo 135790 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B894905 : Blo 135790 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B2664485 : Blo 135790 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B206927 : Blo 135790 206927 := bstep (se 1 (by rfl) ⟨155195, by rfl⟩ : syracuseStep 206927 = 310391) B310391
theorem B207047 : Blo 135790 207047 := bstep (se 1 (by rfl) ⟨155285, by rfl⟩ : syracuseStep 207047 = 310571) B310571
theorem B469259 : Blo 135790 469259 := bstep (se 1 (by rfl) ⟨351944, by rfl⟩ : syracuseStep 469259 = 703889) B703889
theorem B207209 : Blo 135790 207209 := bstep (se 2 (by rfl) ⟨77703, by rfl⟩ : syracuseStep 207209 = 155407) B155407
theorem B207287 : Blo 135790 207287 := bstep (se 1 (by rfl) ⟨155465, by rfl⟩ : syracuseStep 207287 = 310931) B310931
theorem B207323 : Blo 135790 207323 := bstep (se 1 (by rfl) ⟨155492, by rfl⟩ : syracuseStep 207323 = 310985) B310985
theorem B469529 : Blo 135790 469529 := bstep (se 2 (by rfl) ⟨176073, by rfl⟩ : syracuseStep 469529 = 352147) B352147
theorem B174631 : Blo 135790 174631 := bstep (se 1 (by rfl) ⟨130973, by rfl⟩ : syracuseStep 174631 = 261947) B261947
theorem B338555 : Blo 135790 338555 := bstep (se 1 (by rfl) ⟨253916, by rfl⟩ : syracuseStep 338555 = 507833) B507833
theorem B993977 : Blo 135790 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B371551 : Blo 135790 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B174955 : Blo 135790 174955 := bstep (se 1 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 174955 = 262433) B262433
theorem B11447203 : Blo 135790 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B207791 : Blo 135790 207791 := bstep (se 1 (by rfl) ⟨155843, by rfl⟩ : syracuseStep 207791 = 311687) B311687
theorem B306107 : Blo 135790 306107 := bstep (se 1 (by rfl) ⟨229580, by rfl⟩ : syracuseStep 306107 = 459161) B459161
theorem B207881 : Blo 135790 207881 := bstep (se 2 (by rfl) ⟨77955, by rfl⟩ : syracuseStep 207881 = 155911) B155911
theorem B207911 : Blo 135790 207911 := bstep (se 1 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 207911 = 311867) B311867
theorem B306233 : Blo 135790 306233 := bstep (se 2 (by rfl) ⟨114837, by rfl⟩ : syracuseStep 306233 = 229675) B229675
theorem B207995 : Blo 135790 207995 := bstep (se 1 (by rfl) ⟨155996, by rfl⟩ : syracuseStep 207995 = 311993) B311993
theorem B208121 : Blo 135790 208121 := bstep (se 2 (by rfl) ⟨78045, by rfl⟩ : syracuseStep 208121 = 156091) B156091
theorem B503101 : Blo 135790 503101 := bstep (se 3 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 503101 = 188663) B188663
theorem B896345 : Blo 135790 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B208223 : Blo 135790 208223 := bstep (se 1 (by rfl) ⟨156167, by rfl⟩ : syracuseStep 208223 = 312335) B312335
theorem B208235 : Blo 135790 208235 := bstep (se 1 (by rfl) ⟨156176, by rfl⟩ : syracuseStep 208235 = 312353) B312353
theorem B306575 : Blo 135790 306575 := bstep (se 1 (by rfl) ⟨229931, by rfl⟩ : syracuseStep 306575 = 459863) B459863
theorem B208463 : Blo 135790 208463 := bstep (se 1 (by rfl) ⟨156347, by rfl⟩ : syracuseStep 208463 = 312695) B312695
theorem B700001 : Blo 135790 700001 := bstep (se 2 (by rfl) ⟨262500, by rfl⟩ : syracuseStep 700001 = 525001) B525001
theorem B470663 : Blo 135790 470663 := bstep (se 1 (by rfl) ⟨352997, by rfl⟩ : syracuseStep 470663 = 705995) B705995
theorem B470717 : Blo 135790 470717 := bstep (se 3 (by rfl) ⟨88259, by rfl⟩ : syracuseStep 470717 = 176519) B176519
theorem B208583 : Blo 135790 208583 := bstep (se 1 (by rfl) ⟨156437, by rfl⟩ : syracuseStep 208583 = 312875) B312875
theorem B306899 : Blo 135790 306899 := bstep (se 1 (by rfl) ⟨230174, by rfl⟩ : syracuseStep 306899 = 460349) B460349
theorem B470879 : Blo 135790 470879 := bstep (se 1 (by rfl) ⟨353159, by rfl⟩ : syracuseStep 470879 = 706319) B706319
theorem B208745 : Blo 135790 208745 := bstep (se 2 (by rfl) ⟨78279, by rfl⟩ : syracuseStep 208745 = 156559) B156559
theorem B208823 : Blo 135790 208823 := bstep (se 1 (by rfl) ⟨156617, by rfl⟩ : syracuseStep 208823 = 313235) B313235
theorem B1421243 : Blo 135790 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B208859 : Blo 135790 208859 := bstep (se 1 (by rfl) ⟨156644, by rfl⟩ : syracuseStep 208859 = 313289) B313289
theorem B471041 : Blo 135790 471041 := bstep (se 2 (by rfl) ⟨176640, by rfl⟩ : syracuseStep 471041 = 353281) B353281
theorem B208975 : Blo 135790 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B3321971 : Blo 135790 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B176251 : Blo 135790 176251 := bstep (se 1 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 176251 = 264377) B264377
theorem B1552769 : Blo 135790 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B209327 : Blo 135790 209327 := bstep (se 1 (by rfl) ⟨156995, by rfl⟩ : syracuseStep 209327 = 313991) B313991
theorem B209417 : Blo 135790 209417 := bstep (se 2 (by rfl) ⟨78531, by rfl⟩ : syracuseStep 209417 = 157063) B157063
theorem B209447 : Blo 135790 209447 := bstep (se 1 (by rfl) ⟨157085, by rfl⟩ : syracuseStep 209447 = 314171) B314171
theorem B307835 : Blo 135790 307835 := bstep (se 1 (by rfl) ⟨230876, by rfl⟩ : syracuseStep 307835 = 461753) B461753
theorem B209531 : Blo 135790 209531 := bstep (se 1 (by rfl) ⟨157148, by rfl⟩ : syracuseStep 209531 = 314297) B314297
theorem B307961 : Blo 135790 307961 := bstep (se 2 (by rfl) ⟨115485, by rfl⟩ : syracuseStep 307961 = 230971) B230971
theorem B209657 : Blo 135790 209657 := bstep (se 2 (by rfl) ⟨78621, by rfl⟩ : syracuseStep 209657 = 157243) B157243
theorem B897821 : Blo 135790 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B308231 : Blo 135790 308231 := bstep (se 1 (by rfl) ⟨231173, by rfl⟩ : syracuseStep 308231 = 462347) B462347
theorem B701459 : Blo 135790 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B1127467 : Blo 135790 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B308303 : Blo 135790 308303 := bstep (se 1 (by rfl) ⟨231227, by rfl⟩ : syracuseStep 308303 = 462455) B462455
theorem B308699 : Blo 135790 308699 := bstep (se 1 (by rfl) ⟨231524, by rfl⟩ : syracuseStep 308699 = 463049) B463049
theorem B2209265 : Blo 135790 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B439997 : Blo 135790 439997 := bstep (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) B164999
theorem B309167 : Blo 135790 309167 := bstep (se 1 (by rfl) ⟨231875, by rfl⟩ : syracuseStep 309167 = 463751) B463751
theorem B276443 : Blo 135790 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B145487 : Blo 135790 145487 := bstep (se 1 (by rfl) ⟨109115, by rfl⟩ : syracuseStep 145487 = 218231) B218231
theorem B309419 : Blo 135790 309419 := bstep (se 1 (by rfl) ⟨232064, by rfl⟩ : syracuseStep 309419 = 464129) B464129
theorem B309959 : Blo 135790 309959 := bstep (se 1 (by rfl) ⟨232469, by rfl⟩ : syracuseStep 309959 = 464939) B464939
theorem B998365 : Blo 135790 998365 := bstep (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) B374387
theorem B375965 : Blo 135790 375965 := bstep (se 3 (by rfl) ⟨70493, by rfl⟩ : syracuseStep 375965 = 140987) B140987
theorem B441895 : Blo 135790 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B310823 : Blo 135790 310823 := bstep (se 1 (by rfl) ⟨233117, by rfl⟩ : syracuseStep 310823 = 466235) B466235
theorem B1031777 : Blo 135790 1031777 := bstep (se 2 (by rfl) ⟨386916, by rfl⟩ : syracuseStep 1031777 = 773833) B773833
theorem B704123 : Blo 135790 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B311147 : Blo 135790 311147 := bstep (se 1 (by rfl) ⟨233360, by rfl⟩ : syracuseStep 311147 = 466721) B466721
theorem B704375 : Blo 135790 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B311201 : Blo 135790 311201 := bstep (se 2 (by rfl) ⟨116700, by rfl⟩ : syracuseStep 311201 = 233401) B233401
theorem B1130611 : Blo 135790 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B311543 : Blo 135790 311543 := bstep (se 1 (by rfl) ⟨233657, by rfl⟩ : syracuseStep 311543 = 467315) B467315
theorem B312137 : Blo 135790 312137 := bstep (se 2 (by rfl) ⟨117051, by rfl⟩ : syracuseStep 312137 = 234103) B234103
theorem B345019 : Blo 135790 345019 := bstep (se 1 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 345019 = 517529) B517529
theorem B443407 : Blo 135790 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B1033235 : Blo 135790 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B3949721 : Blo 135790 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B312929 : Blo 135790 312929 := bstep (se 2 (by rfl) ⟨117348, by rfl⟩ : syracuseStep 312929 = 234697) B234697
theorem B313271 : Blo 135790 313271 := bstep (se 1 (by rfl) ⟨234953, by rfl⟩ : syracuseStep 313271 = 469907) B469907
theorem B1984601 : Blo 135790 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B313865 : Blo 135790 313865 := bstep (se 2 (by rfl) ⟨117699, by rfl⟩ : syracuseStep 313865 = 235399) B235399
theorem B314207 : Blo 135790 314207 := bstep (se 1 (by rfl) ⟨235655, by rfl⟩ : syracuseStep 314207 = 471311) B471311
theorem B314387 : Blo 135790 314387 := bstep (se 1 (by rfl) ⟨235790, by rfl⟩ : syracuseStep 314387 = 471581) B471581
theorem B642505 : Blo 135790 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B347611 : Blo 135790 347611 := bstep (se 1 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 347611 = 521417) B521417
theorem B1887877 : Blo 135790 1887877 := bstep (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) B353977
theorem B741113 : Blo 135790 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B446251 : Blo 135790 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B446303 : Blo 135790 446303 := bstep (se 1 (by rfl) ⟨334727, by rfl⟩ : syracuseStep 446303 = 669455) B669455
theorem B1003373 : Blo 135790 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B1036151 : Blo 135790 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B1331063 : Blo 135790 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B249863 : Blo 135790 249863 := bstep (se 1 (by rfl) ⟨187397, by rfl⟩ : syracuseStep 249863 = 374795) B374795
theorem B348239 : Blo 135790 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B249979 : Blo 135790 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B7622857 : Blo 135790 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B774791 : Blo 135790 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B348887 : Blo 135790 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B3200573 : Blo 135790 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B251471 : Blo 135790 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B12342881 : Blo 135790 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B153211 : Blo 135790 153211 := bstep (se 1 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 153211 = 229817) B229817
theorem B2348837 : Blo 135790 2348837 := bstep (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) B440407
theorem B186295 : Blo 135790 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B776249 : Blo 135790 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B153679 : Blo 135790 153679 := bstep (se 1 (by rfl) ⟨115259, by rfl⟩ : syracuseStep 153679 = 230519) B230519
theorem B907649 : Blo 135790 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B154075 : Blo 135790 154075 := bstep (se 1 (by rfl) ⟨115556, by rfl⟩ : syracuseStep 154075 = 231113) B231113
theorem B154543 : Blo 135790 154543 := bstep (se 1 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 154543 = 231815) B231815
theorem B1039553 : Blo 135790 1039553 := bstep (se 2 (by rfl) ⟨389832, by rfl⟩ : syracuseStep 1039553 = 779665) B779665
theorem B351479 : Blo 135790 351479 := bstep (se 1 (by rfl) ⟨263609, by rfl⟩ : syracuseStep 351479 = 527219) B527219
theorem B220409 : Blo 135790 220409 := bstep (se 2 (by rfl) ⟨82653, by rfl⟩ : syracuseStep 220409 = 165307) B165307
theorem B154975 : Blo 135790 154975 := bstep (se 1 (by rfl) ⟨116231, by rfl⟩ : syracuseStep 154975 = 232463) B232463
theorem B155335 : Blo 135790 155335 := bstep (se 1 (by rfl) ⟨116501, by rfl⟩ : syracuseStep 155335 = 233003) B233003
theorem B483031 : Blo 135790 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B516253 : Blo 135790 516253 := bstep (se 3 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 516253 = 193595) B193595
theorem B221383 : Blo 135790 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B1171685 : Blo 135790 1171685 := bstep (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) B219691
theorem B188777 : Blo 135790 188777 := bstep (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) B141583
theorem B778733 : Blo 135790 778733 := bstep (se 3 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 778733 = 292025) B292025
theorem B156199 : Blo 135790 156199 := bstep (se 1 (by rfl) ⟨117149, by rfl⟩ : syracuseStep 156199 = 234299) B234299
theorem B352907 : Blo 135790 352907 := bstep (se 1 (by rfl) ⟨264680, by rfl⟩ : syracuseStep 352907 = 529361) B529361
theorem B877229 : Blo 135790 877229 := bstep (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) B328961
theorem B353119 : Blo 135790 353119 := bstep (se 1 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 353119 = 529679) B529679
theorem B222095 : Blo 135790 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B1893851 : Blo 135790 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B223049 : Blo 135790 223049 := bstep (se 2 (by rfl) ⟨83643, by rfl⟩ : syracuseStep 223049 = 167287) B167287
theorem B583519 : Blo 135790 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B550775 : Blo 135790 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B1894337 : Blo 135790 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B223241 : Blo 135790 223241 := bstep (se 2 (by rfl) ⟨83715, by rfl⟩ : syracuseStep 223241 = 167431) B167431
theorem B1042469 : Blo 135790 1042469 := bstep (se 4 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 1042469 = 195463) B195463
theorem B551069 : Blo 135790 551069 := bstep (se 3 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 551069 = 206651) B206651
theorem B3337037 : Blo 135790 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B486319 : Blo 135790 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B519169 : Blo 135790 519169 := bstep (se 2 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 519169 = 389377) B389377
theorem B453899 : Blo 135790 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B2289239 : Blo 135790 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B519929 : Blo 135790 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B257899 : Blo 135790 257899 := bstep (se 1 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 257899 = 386849) B386849
theorem B257975 : Blo 135790 257975 := bstep (se 1 (by rfl) ⟨193481, by rfl⟩ : syracuseStep 257975 = 386963) B386963
theorem B258491 : Blo 135790 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B291367 : Blo 135790 291367 := bstep (se 1 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 291367 = 437051) B437051
theorem B783107 : Blo 135790 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B291691 : Blo 135790 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B258977 : Blo 135790 258977 := bstep (se 2 (by rfl) ⟨97116, by rfl⟩ : syracuseStep 258977 = 194233) B194233
theorem B259129 : Blo 135790 259129 := bstep (se 2 (by rfl) ⟨97173, by rfl⟩ : syracuseStep 259129 = 194347) B194347
theorem B1045583 : Blo 135790 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B521387 : Blo 135790 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B259433 : Blo 135790 259433 := bstep (se 2 (by rfl) ⟨97287, by rfl⟩ : syracuseStep 259433 = 194575) B194575
theorem B1963379 : Blo 135790 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B750973 : Blo 135790 750973 := bstep (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) B281615
theorem B1340873 : Blo 135790 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B1308305 : Blo 135790 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B391007 : Blo 135790 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B1275841 : Blo 135790 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B292871 : Blo 135790 292871 := bstep (se 1 (by rfl) ⟨219653, by rfl⟩ : syracuseStep 292871 = 439307) B439307
theorem B653579 : Blo 135790 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B522557 : Blo 135790 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B522625 : Blo 135790 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B1112453 : Blo 135790 1112453 := bstep (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) B208585
theorem B1309229 : Blo 135790 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B522875 : Blo 135790 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B948995 : Blo 135790 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B523115 : Blo 135790 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B1112939 : Blo 135790 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B392111 : Blo 135790 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B883685 : Blo 135790 883685 := bstep (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) B165691
theorem B949249 : Blo 135790 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B588971 : Blo 135790 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B261559 : Blo 135790 261559 := bstep (se 1 (by rfl) ⟨196169, by rfl⟩ : syracuseStep 261559 = 392339) B392339
theorem B1048301 : Blo 135790 1048301 := bstep (se 3 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 1048301 = 393113) B393113
theorem B1343213 : Blo 135790 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B753569 : Blo 135790 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B1048627 : Blo 135790 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B1507481 : Blo 135790 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B688337 : Blo 135790 688337 := bstep (se 2 (by rfl) ⟨258126, by rfl⟩ : syracuseStep 688337 = 516253) B516253
theorem B1048787 : Blo 135790 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B458963 : Blo 135790 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B295177 : Blo 135790 295177 := bstep (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) B221383
theorem B786779 : Blo 135790 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B524819 : Blo 135790 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B688823 : Blo 135790 688823 := bstep (se 1 (by rfl) ⟨516617, by rfl⟩ : syracuseStep 688823 = 1033235) B1033235
theorem B525257 : Blo 135790 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B525275 : Blo 135790 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B689309 : Blo 135790 689309 := bstep (se 3 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 689309 = 258491) B258491
theorem B460025 : Blo 135790 460025 := bstep (se 2 (by rfl) ⟨172509, by rfl⟩ : syracuseStep 460025 = 345019) B345019
theorem B591209 : Blo 135790 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B3933683 : Blo 135790 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B460295 : Blo 135790 460295 := bstep (se 1 (by rfl) ⟨345221, by rfl⟩ : syracuseStep 460295 = 690443) B690443
theorem B198379 : Blo 135790 198379 := bstep (se 1 (by rfl) ⟨148784, by rfl⟩ : syracuseStep 198379 = 297569) B297569
theorem B198607 : Blo 135790 198607 := bstep (se 1 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 198607 = 297911) B297911
theorem B264539 : Blo 135790 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B330095 : Blo 135790 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B264559 : Blo 135790 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B690605 : Blo 135790 690605 := bstep (se 3 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 690605 = 258977) B258977
theorem B461267 : Blo 135790 461267 := bstep (se 1 (by rfl) ⟨345950, by rfl⟩ : syracuseStep 461267 = 691901) B691901
theorem B494075 : Blo 135790 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B461375 : Blo 135790 461375 := bstep (se 1 (by rfl) ⟨346031, by rfl⟩ : syracuseStep 461375 = 692063) B692063
theorem B297535 : Blo 135790 297535 := bstep (se 1 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 297535 = 446303) B446303
theorem B690767 : Blo 135790 690767 := bstep (se 1 (by rfl) ⟨518075, by rfl⟩ : syracuseStep 690767 = 1036151) B1036151
theorem B887375 : Blo 135790 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B232159 : Blo 135790 232159 := bstep (se 1 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 232159 = 348239) B348239
theorem B592883 : Blo 135790 592883 := bstep (se 1 (by rfl) ⟨444662, by rfl⟩ : syracuseStep 592883 = 889325) B889325
theorem B232591 : Blo 135790 232591 := bstep (se 1 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 232591 = 348887) B348887
theorem B527735 : Blo 135790 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B232841 : Blo 135790 232841 := bstep (se 2 (by rfl) ⟨87315, by rfl⟩ : syracuseStep 232841 = 174631) B174631
theorem B396895 : Blo 135790 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B2133715 : Blo 135790 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B8228587 : Blo 135790 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B495401 : Blo 135790 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B233273 : Blo 135790 233273 := bstep (se 2 (by rfl) ⟨87477, by rfl⟩ : syracuseStep 233273 = 174955) B174955
theorem B692225 : Blo 135790 692225 := bstep (se 2 (by rfl) ⟨259584, by rfl⟩ : syracuseStep 692225 = 519169) B519169
theorem B463211 : Blo 135790 463211 := bstep (se 1 (by rfl) ⟨347408, by rfl⟩ : syracuseStep 463211 = 694817) B694817
theorem B1315379 : Blo 135790 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B856673 : Blo 135790 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B463481 : Blo 135790 463481 := bstep (se 2 (by rfl) ⟨173805, by rfl⟩ : syracuseStep 463481 = 347611) B347611
theorem B135903 : Blo 135790 135903 := bstep (se 1 (by rfl) ⟨101927, by rfl⟩ : syracuseStep 135903 = 203855) B203855
theorem B693035 : Blo 135790 693035 := bstep (se 1 (by rfl) ⟨519776, by rfl⟩ : syracuseStep 693035 = 1039553) B1039553
theorem B135983 : Blo 135790 135983 := bstep (se 1 (by rfl) ⟨101987, by rfl⟩ : syracuseStep 135983 = 203975) B203975
theorem B234319 : Blo 135790 234319 := bstep (se 1 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 234319 = 351479) B351479
theorem B136091 : Blo 135790 136091 := bstep (se 1 (by rfl) ⟨102068, by rfl⟩ : syracuseStep 136091 = 204137) B204137
theorem B136143 : Blo 135790 136143 := bstep (se 1 (by rfl) ⟨102107, by rfl⟩ : syracuseStep 136143 = 204215) B204215
theorem B136167 : Blo 135790 136167 := bstep (se 1 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 136167 = 204251) B204251
theorem B595001 : Blo 135790 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B136479 : Blo 135790 136479 := bstep (se 1 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 136479 = 204719) B204719
theorem B136539 : Blo 135790 136539 := bstep (se 1 (by rfl) ⟨102404, by rfl⟩ : syracuseStep 136539 = 204809) B204809
theorem B595295 : Blo 135790 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B595309 : Blo 135790 595309 := bstep (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) B223241
theorem B136559 : Blo 135790 136559 := bstep (se 1 (by rfl) ⟨102419, by rfl⟩ : syracuseStep 136559 = 204839) B204839
theorem B136615 : Blo 135790 136615 := bstep (se 1 (by rfl) ⟨102461, by rfl⟩ : syracuseStep 136615 = 204923) B204923
theorem B333305 : Blo 135790 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B235001 : Blo 135790 235001 := bstep (se 2 (by rfl) ⟨88125, by rfl⟩ : syracuseStep 235001 = 176251) B176251
theorem B136699 : Blo 135790 136699 := bstep (se 1 (by rfl) ⟨102524, by rfl⟩ : syracuseStep 136699 = 205049) B205049
theorem B136767 : Blo 135790 136767 := bstep (se 1 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 136767 = 205151) B205151
theorem B136775 : Blo 135790 136775 := bstep (se 1 (by rfl) ⟨102581, by rfl⟩ : syracuseStep 136775 = 205163) B205163
theorem B10163809 : Blo 135790 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B136927 : Blo 135790 136927 := bstep (se 1 (by rfl) ⟨102695, by rfl⟩ : syracuseStep 136927 = 205391) B205391
theorem B235271 : Blo 135790 235271 := bstep (se 1 (by rfl) ⟨176453, by rfl⟩ : syracuseStep 235271 = 352907) B352907
theorem B137007 : Blo 135790 137007 := bstep (se 1 (by rfl) ⟨102755, by rfl⟩ : syracuseStep 137007 = 205511) B205511
theorem B137115 : Blo 135790 137115 := bstep (se 1 (by rfl) ⟨102836, by rfl⟩ : syracuseStep 137115 = 205673) B205673
theorem B137167 : Blo 135790 137167 := bstep (se 1 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 137167 = 205751) B205751
theorem B137191 : Blo 135790 137191 := bstep (se 1 (by rfl) ⟨102893, by rfl⟩ : syracuseStep 137191 = 205787) B205787
theorem B137503 : Blo 135790 137503 := bstep (se 1 (by rfl) ⟨103127, by rfl⟩ : syracuseStep 137503 = 206255) B206255
theorem B137563 : Blo 135790 137563 := bstep (se 1 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 137563 = 206345) B206345
theorem B137583 : Blo 135790 137583 := bstep (se 1 (by rfl) ⟨103187, by rfl⟩ : syracuseStep 137583 = 206375) B206375
theorem B465263 : Blo 135790 465263 := bstep (se 1 (by rfl) ⟨348947, by rfl⟩ : syracuseStep 465263 = 697895) B697895
theorem B137639 : Blo 135790 137639 := bstep (se 1 (by rfl) ⟨103229, by rfl⟩ : syracuseStep 137639 = 206459) B206459
theorem B137723 : Blo 135790 137723 := bstep (se 1 (by rfl) ⟨103292, by rfl⟩ : syracuseStep 137723 = 206585) B206585
theorem B137791 : Blo 135790 137791 := bstep (se 1 (by rfl) ⟨103343, by rfl⟩ : syracuseStep 137791 = 206687) B206687
theorem B137799 : Blo 135790 137799 := bstep (se 1 (by rfl) ⟨103349, by rfl⟩ : syracuseStep 137799 = 206699) B206699
theorem B367183 : Blo 135790 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B596603 : Blo 135790 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B1776323 : Blo 135790 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B694979 : Blo 135790 694979 := bstep (se 1 (by rfl) ⟨521234, by rfl⟩ : syracuseStep 694979 = 1042469) B1042469
theorem B137951 : Blo 135790 137951 := bstep (se 1 (by rfl) ⟨103463, by rfl⟩ : syracuseStep 137951 = 206927) B206927
theorem B367379 : Blo 135790 367379 := bstep (se 1 (by rfl) ⟨275534, by rfl⟩ : syracuseStep 367379 = 551069) B551069
theorem B138031 : Blo 135790 138031 := bstep (se 1 (by rfl) ⟨103523, by rfl⟩ : syracuseStep 138031 = 207047) B207047
theorem B138139 : Blo 135790 138139 := bstep (se 1 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 138139 = 207209) B207209
theorem B138191 : Blo 135790 138191 := bstep (se 1 (by rfl) ⟨103643, by rfl⟩ : syracuseStep 138191 = 207287) B207287
theorem B138215 : Blo 135790 138215 := bstep (se 1 (by rfl) ⟨103661, by rfl⟩ : syracuseStep 138215 = 207323) B207323
theorem B662651 : Blo 135790 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B138527 : Blo 135790 138527 := bstep (se 1 (by rfl) ⟨103895, by rfl⟩ : syracuseStep 138527 = 207791) B207791
theorem B204071 : Blo 135790 204071 := bstep (se 1 (by rfl) ⟨153053, by rfl⟩ : syracuseStep 204071 = 306107) B306107
theorem B138587 : Blo 135790 138587 := bstep (se 1 (by rfl) ⟨103940, by rfl⟩ : syracuseStep 138587 = 207881) B207881
theorem B138607 : Blo 135790 138607 := bstep (se 1 (by rfl) ⟨103955, by rfl⟩ : syracuseStep 138607 = 207911) B207911
theorem B204155 : Blo 135790 204155 := bstep (se 1 (by rfl) ⟨153116, by rfl⟩ : syracuseStep 204155 = 306233) B306233
theorem B138663 : Blo 135790 138663 := bstep (se 1 (by rfl) ⟨103997, by rfl⟩ : syracuseStep 138663 = 207995) B207995
theorem B204281 : Blo 135790 204281 := bstep (se 2 (by rfl) ⟨76605, by rfl⟩ : syracuseStep 204281 = 153211) B153211
theorem B138747 : Blo 135790 138747 := bstep (se 1 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 138747 = 208121) B208121
theorem B302599 : Blo 135790 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B597563 : Blo 135790 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B138815 : Blo 135790 138815 := bstep (se 1 (by rfl) ⟨104111, by rfl⟩ : syracuseStep 138815 = 208223) B208223
theorem B138823 : Blo 135790 138823 := bstep (se 1 (by rfl) ⟨104117, by rfl⟩ : syracuseStep 138823 = 208235) B208235
theorem B204383 : Blo 135790 204383 := bstep (se 1 (by rfl) ⟨153287, by rfl⟩ : syracuseStep 204383 = 306575) B306575
theorem B138975 : Blo 135790 138975 := bstep (se 1 (by rfl) ⟨104231, by rfl⟩ : syracuseStep 138975 = 208463) B208463
theorem B466667 : Blo 135790 466667 := bstep (se 1 (by rfl) ⟨350000, by rfl⟩ : syracuseStep 466667 = 700001) B700001
theorem B139055 : Blo 135790 139055 := bstep (se 1 (by rfl) ⟨104291, by rfl⟩ : syracuseStep 139055 = 208583) B208583
theorem B204599 : Blo 135790 204599 := bstep (se 1 (by rfl) ⟨153449, by rfl⟩ : syracuseStep 204599 = 306899) B306899
theorem B139163 : Blo 135790 139163 := bstep (se 1 (by rfl) ⟨104372, by rfl⟩ : syracuseStep 139163 = 208745) B208745
theorem B171983 : Blo 135790 171983 := bstep (se 1 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 171983 = 257975) B257975
theorem B139215 : Blo 135790 139215 := bstep (se 1 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 139215 = 208823) B208823
theorem B139239 : Blo 135790 139239 := bstep (se 1 (by rfl) ⟨104429, by rfl⟩ : syracuseStep 139239 = 208859) B208859
theorem B204905 : Blo 135790 204905 := bstep (se 2 (by rfl) ⟨76839, by rfl⟩ : syracuseStep 204905 = 153679) B153679
theorem B139551 : Blo 135790 139551 := bstep (se 1 (by rfl) ⟨104663, by rfl⟩ : syracuseStep 139551 = 209327) B209327
theorem B139611 : Blo 135790 139611 := bstep (se 1 (by rfl) ⟨104708, by rfl⟩ : syracuseStep 139611 = 209417) B209417
theorem B139631 : Blo 135790 139631 := bstep (se 1 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 139631 = 209447) B209447
theorem B205223 : Blo 135790 205223 := bstep (se 1 (by rfl) ⟨153917, by rfl⟩ : syracuseStep 205223 = 307835) B307835
theorem B139687 : Blo 135790 139687 := bstep (se 1 (by rfl) ⟨104765, by rfl⟩ : syracuseStep 139687 = 209531) B209531
theorem B205307 : Blo 135790 205307 := bstep (se 1 (by rfl) ⟨153980, by rfl⟩ : syracuseStep 205307 = 307961) B307961
theorem B139771 : Blo 135790 139771 := bstep (se 1 (by rfl) ⟨104828, by rfl⟩ : syracuseStep 139771 = 209657) B209657
theorem B696833 : Blo 135790 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B598547 : Blo 135790 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B205433 : Blo 135790 205433 := bstep (se 2 (by rfl) ⟨77037, by rfl⟩ : syracuseStep 205433 = 154075) B154075
theorem B205487 : Blo 135790 205487 := bstep (se 1 (by rfl) ⟨154115, by rfl⟩ : syracuseStep 205487 = 308231) B308231
theorem B467639 : Blo 135790 467639 := bstep (se 1 (by rfl) ⟨350729, by rfl⟩ : syracuseStep 467639 = 701459) B701459
theorem B697055 : Blo 135790 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B205535 : Blo 135790 205535 := bstep (se 1 (by rfl) ⟨154151, by rfl⟩ : syracuseStep 205535 = 308303) B308303
theorem B172955 : Blo 135790 172955 := bstep (se 1 (by rfl) ⟨129716, by rfl⟩ : syracuseStep 172955 = 259433) B259433
theorem B893915 : Blo 135790 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B205799 : Blo 135790 205799 := bstep (se 1 (by rfl) ⟨154349, by rfl⟩ : syracuseStep 205799 = 308699) B308699
theorem B206057 : Blo 135790 206057 := bstep (se 2 (by rfl) ⟨77271, by rfl⟩ : syracuseStep 206057 = 154543) B154543
theorem B206111 : Blo 135790 206111 := bstep (se 1 (by rfl) ⟨154583, by rfl⟩ : syracuseStep 206111 = 309167) B309167
theorem B206279 : Blo 135790 206279 := bstep (se 1 (by rfl) ⟨154709, by rfl⟩ : syracuseStep 206279 = 309419) B309419
theorem B435719 : Blo 135790 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B206633 : Blo 135790 206633 := bstep (se 2 (by rfl) ⟨77487, by rfl⟩ : syracuseStep 206633 = 154975) B154975
theorem B206639 : Blo 135790 206639 := bstep (se 1 (by rfl) ⟨154979, by rfl⟩ : syracuseStep 206639 = 309959) B309959
theorem B632663 : Blo 135790 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B207113 : Blo 135790 207113 := bstep (se 2 (by rfl) ⟨77667, by rfl⟩ : syracuseStep 207113 = 155335) B155335
theorem B207215 : Blo 135790 207215 := bstep (se 1 (by rfl) ⟨155411, by rfl⟩ : syracuseStep 207215 = 310823) B310823
theorem B469415 : Blo 135790 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B698867 : Blo 135790 698867 := bstep (se 1 (by rfl) ⟨524150, by rfl⟩ : syracuseStep 698867 = 1048301) B1048301
theorem B895475 : Blo 135790 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B207431 : Blo 135790 207431 := bstep (se 1 (by rfl) ⟨155573, by rfl⟩ : syracuseStep 207431 = 311147) B311147
theorem B469583 : Blo 135790 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B207467 : Blo 135790 207467 := bstep (se 1 (by rfl) ⟨155600, by rfl⟩ : syracuseStep 207467 = 311201) B311201
theorem B502379 : Blo 135790 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B666301 : Blo 135790 666301 := bstep (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) B249863
theorem B305999 : Blo 135790 305999 := bstep (se 1 (by rfl) ⟨229499, by rfl⟩ : syracuseStep 305999 = 458999) B458999
theorem B207695 : Blo 135790 207695 := bstep (se 1 (by rfl) ⟨155771, by rfl⟩ : syracuseStep 207695 = 311543) B311543
theorem B2632601 : Blo 135790 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B621849635 : Blo 135790 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B306215 : Blo 135790 306215 := bstep (se 1 (by rfl) ⟨229661, by rfl⟩ : syracuseStep 306215 = 459323) B459323
theorem B1485863 : Blo 135790 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B699515 : Blo 135790 699515 := bstep (se 1 (by rfl) ⟨524636, by rfl⟩ : syracuseStep 699515 = 1049273) B1049273
theorem B306395 : Blo 135790 306395 := bstep (se 1 (by rfl) ⟨229796, by rfl⟩ : syracuseStep 306395 = 459593) B459593
theorem B208091 : Blo 135790 208091 := bstep (se 1 (by rfl) ⟨156068, by rfl⟩ : syracuseStep 208091 = 312137) B312137
theorem B2665817 : Blo 135790 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B208265 : Blo 135790 208265 := bstep (se 2 (by rfl) ⟨78099, by rfl⟩ : syracuseStep 208265 = 156199) B156199
theorem B306593 : Blo 135790 306593 := bstep (se 2 (by rfl) ⟨114972, by rfl⟩ : syracuseStep 306593 = 229945) B229945
theorem B2633147 : Blo 135790 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B503405 : Blo 135790 503405 := bstep (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) B188777
theorem B208619 : Blo 135790 208619 := bstep (se 1 (by rfl) ⟨156464, by rfl⟩ : syracuseStep 208619 = 312929) B312929
theorem B700163 : Blo 135790 700163 := bstep (se 1 (by rfl) ⟨525122, by rfl⟩ : syracuseStep 700163 = 1050245) B1050245
theorem B470825 : Blo 135790 470825 := bstep (se 2 (by rfl) ⟨176559, by rfl⟩ : syracuseStep 470825 = 353119) B353119
theorem B175927 : Blo 135790 175927 := bstep (se 1 (by rfl) ⟨131945, by rfl⟩ : syracuseStep 175927 = 263891) B263891
theorem B307151 : Blo 135790 307151 := bstep (se 1 (by rfl) ⟨230363, by rfl⟩ : syracuseStep 307151 = 460727) B460727
theorem B208847 : Blo 135790 208847 := bstep (se 1 (by rfl) ⟨156635, by rfl⟩ : syracuseStep 208847 = 313271) B313271
theorem B438281 : Blo 135790 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B1323067 : Blo 135790 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B176347 : Blo 135790 176347 := bstep (se 1 (by rfl) ⟨132260, by rfl⟩ : syracuseStep 176347 = 264521) B264521
theorem B307529 : Blo 135790 307529 := bstep (se 2 (by rfl) ⟨115323, by rfl⟩ : syracuseStep 307529 = 230647) B230647
theorem B307547 : Blo 135790 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B209243 : Blo 135790 209243 := bstep (se 1 (by rfl) ⟨156932, by rfl⟩ : syracuseStep 209243 = 313865) B313865
theorem B209471 : Blo 135790 209471 := bstep (se 1 (by rfl) ⟨157103, by rfl⟩ : syracuseStep 209471 = 314207) B314207
theorem B209591 : Blo 135790 209591 := bstep (se 1 (by rfl) ⟨157193, by rfl⟩ : syracuseStep 209591 = 314387) B314387
theorem B2634605 : Blo 135790 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B308123 : Blo 135790 308123 := bstep (se 1 (by rfl) ⟨231092, by rfl⟩ : syracuseStep 308123 = 462185) B462185
theorem B373747 : Blo 135790 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B308321 : Blo 135790 308321 := bstep (se 2 (by rfl) ⟨115620, by rfl⟩ : syracuseStep 308321 = 231241) B231241
theorem B668915 : Blo 135790 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B308519 : Blo 135790 308519 := bstep (se 1 (by rfl) ⟨231389, by rfl⟩ : syracuseStep 308519 = 462779) B462779
theorem B701783 : Blo 135790 701783 := bstep (se 1 (by rfl) ⟨526337, by rfl⟩ : syracuseStep 701783 = 1052675) B1052675
theorem B308897 : Blo 135790 308897 := bstep (se 2 (by rfl) ⟨115836, by rfl⟩ : syracuseStep 308897 = 231673) B231673
theorem B309257 : Blo 135790 309257 := bstep (se 2 (by rfl) ⟨115971, by rfl⟩ : syracuseStep 309257 = 231943) B231943
theorem B702593 : Blo 135790 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B375131 : Blo 135790 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B309671 : Blo 135790 309671 := bstep (se 1 (by rfl) ⟨232253, by rfl⟩ : syracuseStep 309671 = 464507) B464507
theorem B309779 : Blo 135790 309779 := bstep (se 1 (by rfl) ⟨232334, by rfl⟩ : syracuseStep 309779 = 464669) B464669
theorem B309833 : Blo 135790 309833 := bstep (se 2 (by rfl) ⟨116187, by rfl⟩ : syracuseStep 309833 = 232375) B232375
theorem B670589 : Blo 135790 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B703403 : Blo 135790 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B605099 : Blo 135790 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B310247 : Blo 135790 310247 := bstep (se 1 (by rfl) ⟨232685, by rfl⟩ : syracuseStep 310247 = 465371) B465371
theorem B670801 : Blo 135790 670801 := bstep (se 2 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 670801 = 503101) B503101
theorem B1031291 : Blo 135790 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B375997 : Blo 135790 375997 := bstep (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) B140999
theorem B1555685 : Blo 135790 1555685 := bstep (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) B291691
theorem B310625 : Blo 135790 310625 := bstep (se 2 (by rfl) ⟨116484, by rfl⟩ : syracuseStep 310625 = 232969) B232969
theorem B310715 : Blo 135790 310715 := bstep (se 1 (by rfl) ⟨233036, by rfl⟩ : syracuseStep 310715 = 466073) B466073
theorem B146939 : Blo 135790 146939 := bstep (se 1 (by rfl) ⟨110204, by rfl⟩ : syracuseStep 146939 = 220409) B220409
theorem B310841 : Blo 135790 310841 := bstep (se 2 (by rfl) ⟨116565, by rfl⟩ : syracuseStep 310841 = 233131) B233131
theorem B343865 : Blo 135790 343865 := bstep (se 2 (by rfl) ⟨128949, by rfl⟩ : syracuseStep 343865 = 257899) B257899
theorem B245711 : Blo 135790 245711 := bstep (se 1 (by rfl) ⟨184283, by rfl⟩ : syracuseStep 245711 = 368567) B368567
theorem B704537 : Blo 135790 704537 := bstep (se 2 (by rfl) ⟨264201, by rfl⟩ : syracuseStep 704537 = 528403) B528403
theorem B278633 : Blo 135790 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B311507 : Blo 135790 311507 := bstep (se 1 (by rfl) ⟨233630, by rfl⟩ : syracuseStep 311507 = 467261) B467261
theorem B311561 : Blo 135790 311561 := bstep (se 2 (by rfl) ⟨116835, by rfl⟩ : syracuseStep 311561 = 233671) B233671
theorem B311777 : Blo 135790 311777 := bstep (se 2 (by rfl) ⟨116916, by rfl⟩ : syracuseStep 311777 = 233833) B233833
theorem B148063 : Blo 135790 148063 := bstep (se 1 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 148063 = 222095) B222095
theorem B312083 : Blo 135790 312083 := bstep (se 1 (by rfl) ⟨234062, by rfl⟩ : syracuseStep 312083 = 468125) B468125
theorem B1262567 : Blo 135790 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B312443 : Blo 135790 312443 := bstep (se 1 (by rfl) ⟨234332, by rfl⟩ : syracuseStep 312443 = 468665) B468665
theorem B148699 : Blo 135790 148699 := bstep (se 1 (by rfl) ⟨111524, by rfl⟩ : syracuseStep 148699 = 223049) B223049
theorem B705779 : Blo 135790 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B312569 : Blo 135790 312569 := bstep (se 2 (by rfl) ⟨117213, by rfl⟩ : syracuseStep 312569 = 234427) B234427
theorem B1262891 : Blo 135790 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B312713 : Blo 135790 312713 := bstep (se 2 (by rfl) ⟨117267, by rfl⟩ : syracuseStep 312713 = 234535) B234535
theorem B345505 : Blo 135790 345505 := bstep (se 2 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 345505 = 259129) B259129
theorem B312839 : Blo 135790 312839 := bstep (se 1 (by rfl) ⟨234629, by rfl⟩ : syracuseStep 312839 = 469259) B469259
theorem B313019 : Blo 135790 313019 := bstep (se 1 (by rfl) ⟨234764, by rfl⟩ : syracuseStep 313019 = 469529) B469529
theorem B313145 : Blo 135790 313145 := bstep (se 2 (by rfl) ⟨117429, by rfl⟩ : syracuseStep 313145 = 234859) B234859
theorem B1001297 : Blo 135790 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B1526159 : Blo 135790 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B313775 : Blo 135790 313775 := bstep (se 1 (by rfl) ⟨235331, by rfl⟩ : syracuseStep 313775 = 470663) B470663
theorem B313811 : Blo 135790 313811 := bstep (se 1 (by rfl) ⟨235358, by rfl⟩ : syracuseStep 313811 = 470717) B470717
theorem B346619 : Blo 135790 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B313919 : Blo 135790 313919 := bstep (se 1 (by rfl) ⟨235439, by rfl⟩ : syracuseStep 313919 = 470879) B470879
theorem B248393 : Blo 135790 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B314027 : Blo 135790 314027 := bstep (se 1 (by rfl) ⟨235520, by rfl⟩ : syracuseStep 314027 = 471041) B471041
theorem B2214647 : Blo 135790 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B707453 : Blo 135790 707453 := bstep (se 3 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 707453 = 265295) B265295
theorem B1035179 : Blo 135790 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B1330141 : Blo 135790 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B347591 : Blo 135790 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B872203 : Blo 135790 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B1331153 : Blo 135790 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B184295 : Blo 135790 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B1265665 : Blo 135790 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B348371 : Blo 135790 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B741635 : Blo 135790 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B872819 : Blo 135790 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B348583 : Blo 135790 348583 := bstep (se 1 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 348583 = 522875) B522875
theorem B348743 : Blo 135790 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B741959 : Blo 135790 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B348745 : Blo 135790 348745 := bstep (se 2 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 348745 = 261559) B261559
theorem B250643 : Blo 135790 250643 := bstep (se 1 (by rfl) ⟨187982, by rfl⟩ : syracuseStep 250643 = 375965) B375965
theorem B644041 : Blo 135790 644041 := bstep (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) B483031
theorem B152923 : Blo 135790 152923 := bstep (se 1 (by rfl) ⟨114692, by rfl⟩ : syracuseStep 152923 = 229385) B229385
theorem B349535 : Blo 135790 349535 := bstep (se 1 (by rfl) ⟨262151, by rfl⟩ : syracuseStep 349535 = 524303) B524303
theorem B153031 : Blo 135790 153031 := bstep (se 1 (by rfl) ⟨114773, by rfl⟩ : syracuseStep 153031 = 229547) B229547
theorem B1660601 : Blo 135790 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B153391 : Blo 135790 153391 := bstep (se 1 (by rfl) ⟨115043, by rfl⟩ : syracuseStep 153391 = 230087) B230087
theorem B153499 : Blo 135790 153499 := bstep (se 1 (by rfl) ⟨115124, by rfl⟩ : syracuseStep 153499 = 230249) B230249
theorem B153895 : Blo 135790 153895 := bstep (se 1 (by rfl) ⟨115421, by rfl⟩ : syracuseStep 153895 = 230843) B230843
theorem B153967 : Blo 135790 153967 := bstep (se 1 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 153967 = 230951) B230951
theorem B350639 : Blo 135790 350639 := bstep (se 1 (by rfl) ⟨262979, by rfl⟩ : syracuseStep 350639 = 525959) B525959
theorem B350689 : Blo 135790 350689 := bstep (se 2 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 350689 = 263017) B263017
theorem B154183 : Blo 135790 154183 := bstep (se 1 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 154183 = 231275) B231275
theorem B219871 : Blo 135790 219871 := bstep (se 1 (by rfl) ⟨164903, by rfl⟩ : syracuseStep 219871 = 329807) B329807
theorem B187177 : Blo 135790 187177 := bstep (se 2 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 187177 = 140383) B140383
theorem B744571 : Blo 135790 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B351611 : Blo 135790 351611 := bstep (se 1 (by rfl) ⟨263708, by rfl⟩ : syracuseStep 351611 = 527417) B527417
theorem B155047 : Blo 135790 155047 := bstep (se 1 (by rfl) ⟨116285, by rfl⟩ : syracuseStep 155047 = 232571) B232571
theorem B1007063 : Blo 135790 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B778025 : Blo 135790 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B155623 : Blo 135790 155623 := bstep (se 1 (by rfl) ⟨116717, by rfl⟩ : syracuseStep 155623 = 233435) B233435
theorem B516527 : Blo 135790 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B746131 : Blo 135790 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B5235677 : Blo 135790 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B1532903 : Blo 135790 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B353423 : Blo 135790 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B1565891 : Blo 135790 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B15262937 : Blo 135790 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B648425 : Blo 135790 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B517499 : Blo 135790 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B1173325 : Blo 135790 1173325 := bstep (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) B439997
theorem B2517169 : Blo 135790 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B551279 : Blo 135790 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B781123 : Blo 135790 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B387965 : Blo 135790 387965 := bstep (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) B145487
theorem B519155 : Blo 135790 519155 := bstep (se 1 (by rfl) ⟨389366, by rfl⟩ : syracuseStep 519155 = 778733) B778733
theorem B584819 : Blo 135790 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B388489 : Blo 135790 388489 := bstep (se 2 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 388489 = 291367) B291367
theorem B159175 : Blo 135790 159175 := bstep (se 1 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 159175 = 238763) B238763
theorem B1503289 : Blo 135790 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B225703 : Blo 135790 225703 := bstep (se 1 (by rfl) ⟨169277, by rfl⟩ : syracuseStep 225703 = 338555) B338555
theorem B2224691 : Blo 135790 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B1504109 : Blo 135790 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1701121 : Blo 135790 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B947495 : Blo 135790 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B522071 : Blo 135790 522071 := bstep (se 1 (by rfl) ⟨391553, by rfl⟩ : syracuseStep 522071 = 783107) B783107
theorem B1472843 : Blo 135790 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B260671 : Blo 135790 260671 := bstep (se 1 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 260671 = 391007) B391007
theorem B195247 : Blo 135790 195247 := bstep (se 1 (by rfl) ⟨146435, by rfl⟩ : syracuseStep 195247 = 292871) B292871
theorem B261407 : Blo 135790 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B589123 : Blo 135790 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B589193 : Blo 135790 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B392647 : Blo 135790 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B687851 : Blo 135790 687851 := bstep (se 1 (by rfl) ⟨515888, by rfl⟩ : syracuseStep 687851 = 1031777) B1031777
theorem B458891 : Blo 135790 458891 := bstep (se 1 (by rfl) ⟨344168, by rfl⟩ : syracuseStep 458891 = 688337) B688337
theorem B524519 : Blo 135790 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B393569 : Blo 135790 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B459215 : Blo 135790 459215 := bstep (se 1 (by rfl) ⟨344411, by rfl⟩ : syracuseStep 459215 = 688823) B688823
theorem B459539 : Blo 135790 459539 := bstep (se 1 (by rfl) ⟨344654, by rfl⟩ : syracuseStep 459539 = 689309) B689309
theorem B197417 : Blo 135790 197417 := bstep (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) B148063
theorem B394139 : Blo 135790 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B2622455 : Blo 135790 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B460403 : Blo 135790 460403 := bstep (se 1 (by rfl) ⟨345302, by rfl⟩ : syracuseStep 460403 = 690605) B690605
theorem B231079 : Blo 135790 231079 := bstep (se 1 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 231079 = 346619) B346619
theorem B329383 : Blo 135790 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B460511 : Blo 135790 460511 := bstep (se 1 (by rfl) ⟨345383, by rfl⟩ : syracuseStep 460511 = 690767) B690767
theorem B1476431 : Blo 135790 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B460673 : Blo 135790 460673 := bstep (se 2 (by rfl) ⟨172752, by rfl⟩ : syracuseStep 460673 = 345505) B345505
theorem B690119 : Blo 135790 690119 := bstep (se 1 (by rfl) ⟨517589, by rfl⟩ : syracuseStep 690119 = 1035179) B1035179
theorem B395255 : Blo 135790 395255 := bstep (se 1 (by rfl) ⟨296441, by rfl⟩ : syracuseStep 395255 = 592883) B592883
theorem B231727 : Blo 135790 231727 := bstep (se 1 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 231727 = 347591) B347591
theorem B461213 : Blo 135790 461213 := bstep (se 3 (by rfl) ⟨86477, by rfl⟩ : syracuseStep 461213 = 172955) B172955
theorem B264809 : Blo 135790 264809 := bstep (se 2 (by rfl) ⟨99303, by rfl⟩ : syracuseStep 264809 = 198607) B198607
theorem B887435 : Blo 135790 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B461483 : Blo 135790 461483 := bstep (se 1 (by rfl) ⟨346112, by rfl⟩ : syracuseStep 461483 = 692225) B692225
theorem B232247 : Blo 135790 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B494423 : Blo 135790 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B494639 : Blo 135790 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B167095 : Blo 135790 167095 := bstep (se 1 (by rfl) ⟨125321, by rfl⟩ : syracuseStep 167095 = 250643) B250643
theorem B462023 : Blo 135790 462023 := bstep (se 1 (by rfl) ⟨346517, by rfl⟩ : syracuseStep 462023 = 693035) B693035
theorem B396667 : Blo 135790 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B396713 : Blo 135790 396713 := bstep (se 2 (by rfl) ⟨148767, by rfl⟩ : syracuseStep 396713 = 297535) B297535
theorem B2526653 : Blo 135790 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B233023 : Blo 135790 233023 := bstep (se 1 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 233023 = 349535) B349535
theorem B396863 : Blo 135790 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B888401 : Blo 135790 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B1773521 : Blo 135790 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B233759 : Blo 135790 233759 := bstep (se 1 (by rfl) ⟨175319, by rfl⟩ : syracuseStep 233759 = 350639) B350639
theorem B397735 : Blo 135790 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B1184215 : Blo 135790 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B463319 : Blo 135790 463319 := bstep (se 1 (by rfl) ⟨347489, by rfl⟩ : syracuseStep 463319 = 694979) B694979
theorem B529193 : Blo 135790 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B136047 : Blo 135790 136047 := bstep (se 1 (by rfl) ⟨102035, by rfl⟩ : syracuseStep 136047 = 204071) B204071
theorem B136103 : Blo 135790 136103 := bstep (se 1 (by rfl) ⟨102077, by rfl⟩ : syracuseStep 136103 = 204155) B204155
theorem B234407 : Blo 135790 234407 := bstep (se 1 (by rfl) ⟨175805, by rfl⟩ : syracuseStep 234407 = 351611) B351611
theorem B136187 : Blo 135790 136187 := bstep (se 1 (by rfl) ⟨102140, by rfl⟩ : syracuseStep 136187 = 204281) B204281
theorem B398375 : Blo 135790 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B136255 : Blo 135790 136255 := bstep (se 1 (by rfl) ⟨102191, by rfl⟩ : syracuseStep 136255 = 204383) B204383
theorem B234569 : Blo 135790 234569 := bstep (se 2 (by rfl) ⟨87963, by rfl⟩ : syracuseStep 234569 = 175927) B175927
theorem B136399 : Blo 135790 136399 := bstep (se 1 (by rfl) ⟨102299, by rfl⟩ : syracuseStep 136399 = 204599) B204599
theorem B136603 : Blo 135790 136603 := bstep (se 1 (by rfl) ⟨102452, by rfl⟩ : syracuseStep 136603 = 204905) B204905
theorem B2004385 : Blo 135790 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B136815 : Blo 135790 136815 := bstep (se 1 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 136815 = 205223) B205223
theorem B235129 : Blo 135790 235129 := bstep (se 2 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 235129 = 176347) B176347
theorem B136871 : Blo 135790 136871 := bstep (se 1 (by rfl) ⟨102653, by rfl⟩ : syracuseStep 136871 = 205307) B205307
theorem B464555 : Blo 135790 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B136955 : Blo 135790 136955 := bstep (se 1 (by rfl) ⟨102716, by rfl⟩ : syracuseStep 136955 = 205433) B205433
theorem B136991 : Blo 135790 136991 := bstep (se 1 (by rfl) ⟨102743, by rfl⟩ : syracuseStep 136991 = 205487) B205487
theorem B137023 : Blo 135790 137023 := bstep (se 1 (by rfl) ⟨102767, by rfl⟩ : syracuseStep 137023 = 205535) B205535
theorem B464777 : Blo 135790 464777 := bstep (se 2 (by rfl) ⟨174291, by rfl⟩ : syracuseStep 464777 = 348583) B348583
theorem B300937 : Blo 135790 300937 := bstep (se 2 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 300937 = 225703) B225703
theorem B3971045 : Blo 135790 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B595943 : Blo 135790 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B137199 : Blo 135790 137199 := bstep (se 1 (by rfl) ⟨102899, by rfl⟩ : syracuseStep 137199 = 205799) B205799
theorem B235615 : Blo 135790 235615 := bstep (se 1 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 235615 = 353423) B353423
theorem B464993 : Blo 135790 464993 := bstep (se 2 (by rfl) ⟨174372, by rfl⟩ : syracuseStep 464993 = 348745) B348745
theorem B137371 : Blo 135790 137371 := bstep (se 1 (by rfl) ⟨103028, by rfl⟩ : syracuseStep 137371 = 206057) B206057
theorem B137407 : Blo 135790 137407 := bstep (se 1 (by rfl) ⟨103055, by rfl⟩ : syracuseStep 137407 = 206111) B206111
theorem B137519 : Blo 135790 137519 := bstep (se 1 (by rfl) ⟨103139, by rfl⟩ : syracuseStep 137519 = 206279) B206279
theorem B4069757 : Blo 135790 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B793061 : Blo 135790 793061 := bstep (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) B148699
theorem B137755 : Blo 135790 137755 := bstep (se 1 (by rfl) ⟨103316, by rfl⟩ : syracuseStep 137755 = 206633) B206633
theorem B137759 : Blo 135790 137759 := bstep (se 1 (by rfl) ⟨103319, by rfl⟩ : syracuseStep 137759 = 206639) B206639
theorem B858721 : Blo 135790 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B498329 : Blo 135790 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B138075 : Blo 135790 138075 := bstep (se 1 (by rfl) ⟨103556, by rfl⟩ : syracuseStep 138075 = 207113) B207113
theorem B662381 : Blo 135790 662381 := bstep (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) B248393
theorem B2366333 : Blo 135790 2366333 := bstep (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) B887375
theorem B367519 : Blo 135790 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B138143 : Blo 135790 138143 := bstep (se 1 (by rfl) ⟨103607, by rfl⟩ : syracuseStep 138143 = 207215) B207215
theorem B465911 : Blo 135790 465911 := bstep (se 1 (by rfl) ⟨349433, by rfl⟩ : syracuseStep 465911 = 698867) B698867
theorem B596983 : Blo 135790 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B2268161 : Blo 135790 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B138287 : Blo 135790 138287 := bstep (se 1 (by rfl) ⟨103715, by rfl⟩ : syracuseStep 138287 = 207431) B207431
theorem B138311 : Blo 135790 138311 := bstep (se 1 (by rfl) ⟨103733, by rfl⟩ : syracuseStep 138311 = 207467) B207467
theorem B334919 : Blo 135790 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B203897 : Blo 135790 203897 := bstep (se 2 (by rfl) ⟨76461, by rfl⟩ : syracuseStep 203897 = 152923) B152923
theorem B793745 : Blo 135790 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B203999 : Blo 135790 203999 := bstep (se 1 (by rfl) ⟨152999, by rfl⟩ : syracuseStep 203999 = 305999) B305999
theorem B138463 : Blo 135790 138463 := bstep (se 1 (by rfl) ⟨103847, by rfl⟩ : syracuseStep 138463 = 207695) B207695
theorem B204041 : Blo 135790 204041 := bstep (se 2 (by rfl) ⟨76515, by rfl⟩ : syracuseStep 204041 = 153031) B153031
theorem B204143 : Blo 135790 204143 := bstep (se 1 (by rfl) ⟨153107, by rfl⟩ : syracuseStep 204143 = 306215) B306215
theorem B990575 : Blo 135790 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B466343 : Blo 135790 466343 := bstep (se 1 (by rfl) ⟨349757, by rfl⟩ : syracuseStep 466343 = 699515) B699515
theorem B204263 : Blo 135790 204263 := bstep (se 1 (by rfl) ⟨153197, by rfl⟩ : syracuseStep 204263 = 306395) B306395
theorem B138727 : Blo 135790 138727 := bstep (se 1 (by rfl) ⟨104045, by rfl⟩ : syracuseStep 138727 = 208091) B208091
theorem B1777211 : Blo 135790 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B138843 : Blo 135790 138843 := bstep (se 1 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 138843 = 208265) B208265
theorem B204395 : Blo 135790 204395 := bstep (se 1 (by rfl) ⟨153296, by rfl⟩ : syracuseStep 204395 = 306593) B306593
theorem B204521 : Blo 135790 204521 := bstep (se 2 (by rfl) ⟨76695, by rfl⟩ : syracuseStep 204521 = 153391) B153391
theorem B335603 : Blo 135790 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B139079 : Blo 135790 139079 := bstep (se 1 (by rfl) ⟨104309, by rfl⟩ : syracuseStep 139079 = 208619) B208619
theorem B466775 : Blo 135790 466775 := bstep (se 1 (by rfl) ⟨350081, by rfl⟩ : syracuseStep 466775 = 700163) B700163
theorem B204665 : Blo 135790 204665 := bstep (se 2 (by rfl) ⟨76749, by rfl⟩ : syracuseStep 204665 = 153499) B153499
theorem B204767 : Blo 135790 204767 := bstep (se 1 (by rfl) ⟨153575, by rfl⟩ : syracuseStep 204767 = 307151) B307151
theorem B139231 : Blo 135790 139231 := bstep (se 1 (by rfl) ⟨104423, by rfl⟩ : syracuseStep 139231 = 208847) B208847
theorem B205019 : Blo 135790 205019 := bstep (se 1 (by rfl) ⟨153764, by rfl⟩ : syracuseStep 205019 = 307529) B307529
theorem B205031 : Blo 135790 205031 := bstep (se 1 (by rfl) ⟨153773, by rfl⟩ : syracuseStep 205031 = 307547) B307547
theorem B139495 : Blo 135790 139495 := bstep (se 1 (by rfl) ⟨104621, by rfl⟩ : syracuseStep 139495 = 209243) B209243
theorem B1483127 : Blo 135790 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B139647 : Blo 135790 139647 := bstep (se 1 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 139647 = 209471) B209471
theorem B205193 : Blo 135790 205193 := bstep (se 2 (by rfl) ⟨76947, by rfl⟩ : syracuseStep 205193 = 153895) B153895
theorem B139727 : Blo 135790 139727 := bstep (se 1 (by rfl) ⟨104795, by rfl⟩ : syracuseStep 139727 = 209591) B209591
theorem B205289 : Blo 135790 205289 := bstep (se 2 (by rfl) ⟨76983, by rfl⟩ : syracuseStep 205289 = 153967) B153967
theorem B205415 : Blo 135790 205415 := bstep (se 1 (by rfl) ⟨154061, by rfl⟩ : syracuseStep 205415 = 308123) B308123
theorem B467585 : Blo 135790 467585 := bstep (se 2 (by rfl) ⟨175344, by rfl⟩ : syracuseStep 467585 = 350689) B350689
theorem B205547 : Blo 135790 205547 := bstep (se 1 (by rfl) ⟨154160, by rfl⟩ : syracuseStep 205547 = 308321) B308321
theorem B697085 : Blo 135790 697085 := bstep (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) B261407
theorem B205577 : Blo 135790 205577 := bstep (se 2 (by rfl) ⟨77091, by rfl⟩ : syracuseStep 205577 = 154183) B154183
theorem B205679 : Blo 135790 205679 := bstep (se 1 (by rfl) ⟨154259, by rfl⟩ : syracuseStep 205679 = 308519) B308519
theorem B467855 : Blo 135790 467855 := bstep (se 1 (by rfl) ⟨350891, by rfl⟩ : syracuseStep 467855 = 701783) B701783
theorem B205931 : Blo 135790 205931 := bstep (se 1 (by rfl) ⟨154448, by rfl⟩ : syracuseStep 205931 = 308897) B308897
theorem B1058021 : Blo 135790 1058021 := bstep (se 4 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 1058021 = 198379) B198379
theorem B206171 : Blo 135790 206171 := bstep (se 1 (by rfl) ⟨154628, by rfl⟩ : syracuseStep 206171 = 309257) B309257
theorem B468395 : Blo 135790 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B894401 : Blo 135790 894401 := bstep (se 2 (by rfl) ⟨335400, by rfl⟩ : syracuseStep 894401 = 670801) B670801
theorem B501329 : Blo 135790 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B206447 : Blo 135790 206447 := bstep (se 1 (by rfl) ⟨154835, by rfl⟩ : syracuseStep 206447 = 309671) B309671
theorem B206519 : Blo 135790 206519 := bstep (se 1 (by rfl) ⟨154889, by rfl⟩ : syracuseStep 206519 = 309779) B309779
theorem B206555 : Blo 135790 206555 := bstep (se 1 (by rfl) ⟨154916, by rfl⟩ : syracuseStep 206555 = 309833) B309833
theorem B206729 : Blo 135790 206729 := bstep (se 2 (by rfl) ⟨77523, by rfl⟩ : syracuseStep 206729 = 155047) B155047
theorem B468935 : Blo 135790 468935 := bstep (se 1 (by rfl) ⟨351701, by rfl⟩ : syracuseStep 468935 = 703403) B703403
theorem B403399 : Blo 135790 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B206831 : Blo 135790 206831 := bstep (se 1 (by rfl) ⟨155123, by rfl⟩ : syracuseStep 206831 = 310247) B310247
theorem B403465 : Blo 135790 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B1321069 : Blo 135790 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B207083 : Blo 135790 207083 := bstep (se 1 (by rfl) ⟨155312, by rfl⟩ : syracuseStep 207083 = 310625) B310625
theorem B207143 : Blo 135790 207143 := bstep (se 1 (by rfl) ⟨155357, by rfl⟩ : syracuseStep 207143 = 310715) B310715
theorem B207227 : Blo 135790 207227 := bstep (se 1 (by rfl) ⟨155420, by rfl⟩ : syracuseStep 207227 = 310841) B310841
theorem B207497 : Blo 135790 207497 := bstep (se 2 (by rfl) ⟨77811, by rfl⟩ : syracuseStep 207497 = 155623) B155623
theorem B469691 : Blo 135790 469691 := bstep (se 1 (by rfl) ⟨352268, by rfl⟩ : syracuseStep 469691 = 704537) B704537
theorem B699191 : Blo 135790 699191 := bstep (se 1 (by rfl) ⟨524393, by rfl⟩ : syracuseStep 699191 = 1048787) B1048787
theorem B207671 : Blo 135790 207671 := bstep (se 1 (by rfl) ⟨155753, by rfl⟩ : syracuseStep 207671 = 311507) B311507
theorem B305975 : Blo 135790 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B207707 : Blo 135790 207707 := bstep (se 1 (by rfl) ⟨155780, by rfl⟩ : syracuseStep 207707 = 311561) B311561
theorem B207851 : Blo 135790 207851 := bstep (se 1 (by rfl) ⟨155888, by rfl⟩ : syracuseStep 207851 = 311777) B311777
theorem B208055 : Blo 135790 208055 := bstep (se 1 (by rfl) ⟨156041, by rfl⟩ : syracuseStep 208055 = 312083) B312083
theorem B208295 : Blo 135790 208295 := bstep (se 1 (by rfl) ⟨156221, by rfl⟩ : syracuseStep 208295 = 312443) B312443
theorem B470519 : Blo 135790 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B306683 : Blo 135790 306683 := bstep (se 1 (by rfl) ⟨230012, by rfl⟩ : syracuseStep 306683 = 460025) B460025
theorem B208379 : Blo 135790 208379 := bstep (se 1 (by rfl) ⟨156284, by rfl⟩ : syracuseStep 208379 = 312569) B312569
theorem B994841 : Blo 135790 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B208475 : Blo 135790 208475 := bstep (se 1 (by rfl) ⟨156356, by rfl⟩ : syracuseStep 208475 = 312713) B312713
theorem B306863 : Blo 135790 306863 := bstep (se 1 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 306863 = 460295) B460295
theorem B208559 : Blo 135790 208559 := bstep (se 1 (by rfl) ⟨156419, by rfl⟩ : syracuseStep 208559 = 312839) B312839
theorem B208679 : Blo 135790 208679 := bstep (se 1 (by rfl) ⟨156509, by rfl⟩ : syracuseStep 208679 = 313019) B313019
theorem B208763 : Blo 135790 208763 := bstep (se 1 (by rfl) ⟨156572, by rfl⟩ : syracuseStep 208763 = 313145) B313145
theorem B667531 : Blo 135790 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B929981 : Blo 135790 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B176359 : Blo 135790 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B209183 : Blo 135790 209183 := bstep (se 1 (by rfl) ⟨156887, by rfl⟩ : syracuseStep 209183 = 313775) B313775
theorem B307511 : Blo 135790 307511 := bstep (se 1 (by rfl) ⟨230633, by rfl⟩ : syracuseStep 307511 = 461267) B461267
theorem B209207 : Blo 135790 209207 := bstep (se 1 (by rfl) ⟨156905, by rfl⟩ : syracuseStep 209207 = 313811) B313811
theorem B307583 : Blo 135790 307583 := bstep (se 1 (by rfl) ⟨230687, by rfl⟩ : syracuseStep 307583 = 461375) B461375
theorem B209279 : Blo 135790 209279 := bstep (se 1 (by rfl) ⟨156959, by rfl⟩ : syracuseStep 209279 = 313919) B313919
theorem B209351 : Blo 135790 209351 := bstep (se 1 (by rfl) ⟨157013, by rfl⟩ : syracuseStep 209351 = 314027) B314027
theorem B471635 : Blo 135790 471635 := bstep (se 1 (by rfl) ⟨353726, by rfl⟩ : syracuseStep 471635 = 707453) B707453
theorem B4010957 : Blo 135790 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B3356225 : Blo 135790 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B308807 : Blo 135790 308807 := bstep (se 1 (by rfl) ⟨231605, by rfl⟩ : syracuseStep 308807 = 463211) B463211
theorem B571115 : Blo 135790 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B308987 : Blo 135790 308987 := bstep (se 1 (by rfl) ⟨231740, by rfl⟩ : syracuseStep 308987 = 463481) B463481
theorem B309545 : Blo 135790 309545 := bstep (se 2 (by rfl) ⟨116079, by rfl⟩ : syracuseStep 309545 = 232159) B232159
theorem B310121 : Blo 135790 310121 := bstep (se 2 (by rfl) ⟨116295, by rfl⟩ : syracuseStep 310121 = 232591) B232591
theorem B310175 : Blo 135790 310175 := bstep (se 1 (by rfl) ⟨232631, by rfl⟩ : syracuseStep 310175 = 465263) B465263
theorem B244919 : Blo 135790 244919 := bstep (se 1 (by rfl) ⟨183689, by rfl⟩ : syracuseStep 244919 = 367379) B367379
theorem B441767 : Blo 135790 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B671375 : Blo 135790 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B1162937 : Blo 135790 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B311111 : Blo 135790 311111 := bstep (se 1 (by rfl) ⟨233333, by rfl⟩ : syracuseStep 311111 = 466667) B466667
theorem B1687553 : Blo 135790 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B344351 : Blo 135790 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B311759 : Blo 135790 311759 := bstep (se 1 (by rfl) ⟨233819, by rfl⟩ : syracuseStep 311759 = 467639) B467639
theorem B3490451 : Blo 135790 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B10175291 : Blo 135790 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1000349 : Blo 135790 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B344999 : Blo 135790 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B312425 : Blo 135790 312425 := bstep (se 2 (by rfl) ⟨117159, by rfl⟩ : syracuseStep 312425 = 234319) B234319
theorem B312943 : Blo 135790 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B313055 : Blo 135790 313055 := bstep (se 1 (by rfl) ⟨234791, by rfl⟩ : syracuseStep 313055 = 469583) B469583
theorem B1755067 : Blo 135790 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B346103 : Blo 135790 346103 := bstep (se 1 (by rfl) ⟨259577, by rfl⟩ : syracuseStep 346103 = 519155) B519155
theorem B414566423 : Blo 135790 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B13551745 : Blo 135790 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B1755431 : Blo 135790 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B313883 : Blo 135790 313883 := bstep (se 1 (by rfl) ⟨235412, by rfl⟩ : syracuseStep 313883 = 470825) B470825
theorem B1756403 : Blo 135790 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B347561 : Blo 135790 347561 := bstep (se 2 (by rfl) ⟨130335, by rfl⟩ : syracuseStep 347561 = 260671) B260671
theorem B445943 : Blo 135790 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B249569 : Blo 135790 249569 := bstep (se 2 (by rfl) ⟨93588, by rfl⟩ : syracuseStep 249569 = 187177) B187177
theorem B348047 : Blo 135790 348047 := bstep (se 1 (by rfl) ⟨261035, by rfl⟩ : syracuseStep 348047 = 522071) B522071
theorem B447059 : Blo 135790 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B1037123 : Blo 135790 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B1398169 : Blo 135790 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B185755 : Blo 135790 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B1004987 : Blo 135790 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B349879 : Blo 135790 349879 := bstep (se 1 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 349879 = 524819) B524819
theorem B350171 : Blo 135790 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B350183 : Blo 135790 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B841711 : Blo 135790 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B841927 : Blo 135790 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1596125 : Blo 135790 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B351823 : Blo 135790 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B155227 : Blo 135790 155227 := bstep (se 1 (by rfl) ⟨116420, by rfl⟩ : syracuseStep 155227 = 232841) B232841
theorem B1564433 : Blo 135790 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B155515 : Blo 135790 155515 := bstep (se 1 (by rfl) ⟨116636, by rfl⟩ : syracuseStep 155515 = 233273) B233273
theorem B4087741 : Blo 135790 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B581879 : Blo 135790 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B876919 : Blo 135790 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B352745 : Blo 135790 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B1729133 : Blo 135790 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B222203 : Blo 135790 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B156667 : Blo 135790 156667 := bstep (se 1 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 156667 = 235001) B235001
theorem B1041497 : Blo 135790 1041497 := bstep (se 2 (by rfl) ⟨390561, by rfl⟩ : syracuseStep 1041497 = 781123) B781123
theorem B1107067 : Blo 135790 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B156847 : Blo 135790 156847 := bstep (se 1 (by rfl) ⟨117635, by rfl⟩ : syracuseStep 156847 = 235271) B235271
theorem B517985 : Blo 135790 517985 := bstep (se 2 (by rfl) ⟨194244, by rfl⟩ : syracuseStep 517985 = 388489) B388489
theorem B2844953 : Blo 135790 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B10971449 : Blo 135790 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B518683 : Blo 135790 518683 := bstep (se 1 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 518683 = 778025) B778025
theorem B1567349 : Blo 135790 1567349 := bstep (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) B146939
theorem B1764089 : Blo 135790 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B1043927 : Blo 135790 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B880253 : Blo 135790 880253 := bstep (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) B330095
theorem B290479 : Blo 135790 290479 := bstep (se 1 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 290479 = 435719) B435719
theorem B421775 : Blo 135790 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B258643 : Blo 135790 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B389879 : Blo 135790 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B7435253 : Blo 135790 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B848933 : Blo 135790 848933 := bstep (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) B159175
theorem B292187 : Blo 135790 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B489577 : Blo 135790 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B260329 : Blo 135790 260329 := bstep (se 2 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 260329 = 195247) B195247
theorem B293161 : Blo 135790 293161 := bstep (se 2 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 293161 = 219871) B219871
theorem B981895 : Blo 135790 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B785497 : Blo 135790 785497 := bstep (se 2 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 785497 = 589123) B589123
theorem B523529 : Blo 135790 523529 := bstep (se 2 (by rfl) ⟨196323, by rfl⟩ : syracuseStep 523529 = 392647) B392647
theorem B687527 : Blo 135790 687527 := bstep (se 1 (by rfl) ⟨515645, by rfl⟩ : syracuseStep 687527 = 1031291) B1031291
theorem B392795 : Blo 135790 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B458567 : Blo 135790 458567 := bstep (se 1 (by rfl) ⟨343925, by rfl⟩ : syracuseStep 458567 = 687851) B687851
theorem B229243 : Blo 135790 229243 := bstep (se 1 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 229243 = 343865) B343865
theorem B458621 : Blo 135790 458621 := bstep (se 3 (by rfl) ⟨85991, by rfl⟩ : syracuseStep 458621 = 171983) B171983
theorem B655229 : Blo 135790 655229 := bstep (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) B245711
theorem B491453 : Blo 135790 491453 := bstep (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) B184295
theorem B229567 : Blo 135790 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B262379 : Blo 135790 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B2326967 : Blo 135790 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B6783527 : Blo 135790 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B262759 : Blo 135790 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B229999 : Blo 135790 229999 := bstep (se 1 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 229999 = 344999) B344999
theorem B984287 : Blo 135790 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B460079 : Blo 135790 460079 := bstep (se 1 (by rfl) ⟨345059, by rfl⟩ : syracuseStep 460079 = 690119) B690119
theorem B230735 : Blo 135790 230735 := bstep (se 1 (by rfl) ⟨173051, by rfl⟩ : syracuseStep 230735 = 346103) B346103
theorem B263503 : Blo 135790 263503 := bstep (se 1 (by rfl) ⟨197627, by rfl⟩ : syracuseStep 263503 = 395255) B395255
theorem B1476089 : Blo 135790 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B591623 : Blo 135790 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B329615 : Blo 135790 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B329759 : Blo 135790 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B526445 : Blo 135790 526445 := bstep (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) B197417
theorem B231707 : Blo 135790 231707 := bstep (se 1 (by rfl) ⟨173780, by rfl⟩ : syracuseStep 231707 = 347561) B347561
theorem B264475 : Blo 135790 264475 := bstep (se 1 (by rfl) ⟨198356, by rfl⟩ : syracuseStep 264475 = 396713) B396713
theorem B264575 : Blo 135790 264575 := bstep (se 1 (by rfl) ⟨198431, by rfl⟩ : syracuseStep 264575 = 396863) B396863
theorem B592267 : Blo 135790 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B166379 : Blo 135790 166379 := bstep (se 1 (by rfl) ⟨124784, by rfl⟩ : syracuseStep 166379 = 249569) B249569
theorem B232031 : Blo 135790 232031 := bstep (se 1 (by rfl) ⟨174023, by rfl⟩ : syracuseStep 232031 = 348047) B348047
theorem B1182347 : Blo 135790 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B592541 : Blo 135790 592541 := bstep (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) B222203
theorem B691415 : Blo 135790 691415 := bstep (se 1 (by rfl) ⟨518561, by rfl⟩ : syracuseStep 691415 = 1037123) B1037123
theorem B265583 : Blo 135790 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B691577 : Blo 135790 691577 := bstep (se 2 (by rfl) ⟨259341, by rfl⟩ : syracuseStep 691577 = 518683) B518683
theorem B233447 : Blo 135790 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B233455 : Blo 135790 233455 := bstep (se 1 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 233455 = 350183) B350183
theorem B397295 : Blo 135790 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B528707 : Blo 135790 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B332219 : Blo 135790 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B528889 : Blo 135790 528889 := bstep (se 2 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 528889 = 396667) B396667
theorem B1577555 : Blo 135790 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B1512107 : Blo 135790 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B135931 : Blo 135790 135931 := bstep (se 1 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 135931 = 203897) B203897
theorem B529163 : Blo 135790 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B135999 : Blo 135790 135999 := bstep (se 1 (by rfl) ⟨101999, by rfl⟩ : syracuseStep 135999 = 203999) B203999
theorem B136027 : Blo 135790 136027 := bstep (se 1 (by rfl) ⟨102020, by rfl⟩ : syracuseStep 136027 = 204041) B204041
theorem B136095 : Blo 135790 136095 := bstep (se 1 (by rfl) ⟨102071, by rfl⟩ : syracuseStep 136095 = 204143) B204143
theorem B660383 : Blo 135790 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B136175 : Blo 135790 136175 := bstep (se 1 (by rfl) ⟨102131, by rfl⟩ : syracuseStep 136175 = 204263) B204263
theorem B1184807 : Blo 135790 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B136263 : Blo 135790 136263 := bstep (se 1 (by rfl) ⟨102197, by rfl⟩ : syracuseStep 136263 = 204395) B204395
theorem B136347 : Blo 135790 136347 := bstep (se 1 (by rfl) ⟨102260, by rfl⟩ : syracuseStep 136347 = 204521) B204521
theorem B890041 : Blo 135790 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B136443 : Blo 135790 136443 := bstep (se 1 (by rfl) ⟨102332, by rfl⟩ : syracuseStep 136443 = 204665) B204665
theorem B136511 : Blo 135790 136511 := bstep (se 1 (by rfl) ⟨102383, by rfl⟩ : syracuseStep 136511 = 204767) B204767
theorem B136679 : Blo 135790 136679 := bstep (se 1 (by rfl) ⟨102509, by rfl⟩ : syracuseStep 136679 = 205019) B205019
theorem B136687 : Blo 135790 136687 := bstep (se 1 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 136687 = 205031) B205031
theorem B988751 : Blo 135790 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B136795 : Blo 135790 136795 := bstep (se 1 (by rfl) ⟨102596, by rfl⟩ : syracuseStep 136795 = 205193) B205193
theorem B235145 : Blo 135790 235145 := bstep (se 2 (by rfl) ⟨88179, by rfl⟩ : syracuseStep 235145 = 176359) B176359
theorem B136859 : Blo 135790 136859 := bstep (se 1 (by rfl) ⟨102644, by rfl⟩ : syracuseStep 136859 = 205289) B205289
theorem B235163 : Blo 135790 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B136943 : Blo 135790 136943 := bstep (se 1 (by rfl) ⟨102707, by rfl⟩ : syracuseStep 136943 = 205415) B205415
theorem B1152755 : Blo 135790 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B137031 : Blo 135790 137031 := bstep (se 1 (by rfl) ⟨102773, by rfl⟩ : syracuseStep 137031 = 205547) B205547
theorem B464723 : Blo 135790 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B137051 : Blo 135790 137051 := bstep (se 1 (by rfl) ⟨102788, by rfl⟩ : syracuseStep 137051 = 205577) B205577
theorem B137119 : Blo 135790 137119 := bstep (se 1 (by rfl) ⟨102839, by rfl⟩ : syracuseStep 137119 = 205679) B205679
theorem B1578953 : Blo 135790 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B694331 : Blo 135790 694331 := bstep (se 1 (by rfl) ⟨520748, by rfl⟩ : syracuseStep 694331 = 1041497) B1041497
theorem B137287 : Blo 135790 137287 := bstep (se 1 (by rfl) ⟨102965, by rfl⟩ : syracuseStep 137287 = 205931) B205931
theorem B137447 : Blo 135790 137447 := bstep (se 1 (by rfl) ⟨103085, by rfl⟩ : syracuseStep 137447 = 206171) B206171
theorem B596267 : Blo 135790 596267 := bstep (se 1 (by rfl) ⟨447200, by rfl⟩ : syracuseStep 596267 = 894401) B894401
theorem B334219 : Blo 135790 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B137631 : Blo 135790 137631 := bstep (se 1 (by rfl) ⟨103223, by rfl⟩ : syracuseStep 137631 = 206447) B206447
theorem B137679 : Blo 135790 137679 := bstep (se 1 (by rfl) ⟨103259, by rfl⟩ : syracuseStep 137679 = 206519) B206519
theorem B137703 : Blo 135790 137703 := bstep (se 1 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 137703 = 206555) B206555
theorem B137819 : Blo 135790 137819 := bstep (se 1 (by rfl) ⟨103364, by rfl⟩ : syracuseStep 137819 = 206729) B206729
theorem B137887 : Blo 135790 137887 := bstep (se 1 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 137887 = 206831) B206831
theorem B138055 : Blo 135790 138055 := bstep (se 1 (by rfl) ⟨103541, by rfl⟩ : syracuseStep 138055 = 207083) B207083
theorem B138095 : Blo 135790 138095 := bstep (se 1 (by rfl) ⟨103571, by rfl⟩ : syracuseStep 138095 = 207143) B207143
theorem B7314299 : Blo 135790 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B138151 : Blo 135790 138151 := bstep (se 1 (by rfl) ⟨103613, by rfl⟩ : syracuseStep 138151 = 207227) B207227
theorem B138331 : Blo 135790 138331 := bstep (se 1 (by rfl) ⟨103748, by rfl⟩ : syracuseStep 138331 = 207497) B207497
theorem B466127 : Blo 135790 466127 := bstep (se 1 (by rfl) ⟨349595, by rfl⟩ : syracuseStep 466127 = 699191) B699191
theorem B138447 : Blo 135790 138447 := bstep (se 1 (by rfl) ⟨103835, by rfl⟩ : syracuseStep 138447 = 207671) B207671
theorem B138471 : Blo 135790 138471 := bstep (se 1 (by rfl) ⟨103853, by rfl⟩ : syracuseStep 138471 = 207707) B207707
theorem B138567 : Blo 135790 138567 := bstep (se 1 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 138567 = 207851) B207851
theorem B138703 : Blo 135790 138703 := bstep (se 1 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 138703 = 208055) B208055
theorem B466505 : Blo 135790 466505 := bstep (se 2 (by rfl) ⟨174939, by rfl⟩ : syracuseStep 466505 = 349879) B349879
theorem B138863 : Blo 135790 138863 := bstep (se 1 (by rfl) ⟨104147, by rfl⟩ : syracuseStep 138863 = 208295) B208295
theorem B695951 : Blo 135790 695951 := bstep (se 1 (by rfl) ⟨521963, by rfl⟩ : syracuseStep 695951 = 1043927) B1043927
theorem B204455 : Blo 135790 204455 := bstep (se 1 (by rfl) ⟨153341, by rfl⟩ : syracuseStep 204455 = 306683) B306683
theorem B138919 : Blo 135790 138919 := bstep (se 1 (by rfl) ⟨104189, by rfl⟩ : syracuseStep 138919 = 208379) B208379
theorem B663227 : Blo 135790 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B138983 : Blo 135790 138983 := bstep (se 1 (by rfl) ⟨104237, by rfl⟩ : syracuseStep 138983 = 208475) B208475
theorem B204575 : Blo 135790 204575 := bstep (se 1 (by rfl) ⟨153431, by rfl⟩ : syracuseStep 204575 = 306863) B306863
theorem B139039 : Blo 135790 139039 := bstep (se 1 (by rfl) ⟨104279, by rfl⟩ : syracuseStep 139039 = 208559) B208559
theorem B401249 : Blo 135790 401249 := bstep (se 2 (by rfl) ⟨150468, by rfl⟩ : syracuseStep 401249 = 300937) B300937
theorem B139119 : Blo 135790 139119 := bstep (se 1 (by rfl) ⟨104339, by rfl⟩ : syracuseStep 139119 = 208679) B208679
theorem B139175 : Blo 135790 139175 := bstep (se 1 (by rfl) ⟨104381, by rfl⟩ : syracuseStep 139175 = 208763) B208763
theorem B1122281 : Blo 135790 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B139455 : Blo 135790 139455 := bstep (se 1 (by rfl) ⟨104591, by rfl⟩ : syracuseStep 139455 = 209183) B209183
theorem B205007 : Blo 135790 205007 := bstep (se 1 (by rfl) ⟨153755, by rfl⟩ : syracuseStep 205007 = 307511) B307511
theorem B139471 : Blo 135790 139471 := bstep (se 1 (by rfl) ⟨104603, by rfl⟩ : syracuseStep 139471 = 209207) B209207
theorem B205055 : Blo 135790 205055 := bstep (se 1 (by rfl) ⟨153791, by rfl⟩ : syracuseStep 205055 = 307583) B307583
theorem B139519 : Blo 135790 139519 := bstep (se 1 (by rfl) ⟨104639, by rfl⟩ : syracuseStep 139519 = 209279) B209279
theorem B1122569 : Blo 135790 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B139567 : Blo 135790 139567 := bstep (se 1 (by rfl) ⟨104675, by rfl⟩ : syracuseStep 139567 = 209351) B209351
theorem B4956835 : Blo 135790 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B565955 : Blo 135790 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B2237483 : Blo 135790 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B205871 : Blo 135790 205871 := bstep (se 1 (by rfl) ⟨154403, by rfl⟩ : syracuseStep 205871 = 308807) B308807
theorem B205991 : Blo 135790 205991 := bstep (se 1 (by rfl) ⟨154493, by rfl⟩ : syracuseStep 205991 = 308987) B308987
theorem B1189181 : Blo 135790 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B795977 : Blo 135790 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B206363 : Blo 135790 206363 := bstep (se 1 (by rfl) ⟨154772, by rfl⟩ : syracuseStep 206363 = 309545) B309545
theorem B206747 : Blo 135790 206747 := bstep (se 1 (by rfl) ⟨155060, by rfl⟩ : syracuseStep 206747 = 310121) B310121
theorem B206783 : Blo 135790 206783 := bstep (se 1 (by rfl) ⟨155087, by rfl⟩ : syracuseStep 206783 = 310175) B310175
theorem B469097 : Blo 135790 469097 := bstep (se 2 (by rfl) ⟨175911, by rfl⟩ : syracuseStep 469097 = 351823) B351823
theorem B206969 : Blo 135790 206969 := bstep (se 2 (by rfl) ⟨77613, by rfl⟩ : syracuseStep 206969 = 155227) B155227
theorem B1747277 : Blo 135790 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B305657 : Blo 135790 305657 := bstep (se 2 (by rfl) ⟨114621, by rfl⟩ : syracuseStep 305657 = 229243) B229243
theorem B207353 : Blo 135790 207353 := bstep (se 2 (by rfl) ⟨77757, by rfl⟩ : syracuseStep 207353 = 155515) B155515
theorem B305711 : Blo 135790 305711 := bstep (se 1 (by rfl) ⟨229283, by rfl⟩ : syracuseStep 305711 = 458567) B458567
theorem B207407 : Blo 135790 207407 := bstep (se 1 (by rfl) ⟨155555, by rfl⟩ : syracuseStep 207407 = 311111) B311111
theorem B5450321 : Blo 135790 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B305747 : Blo 135790 305747 := bstep (se 1 (by rfl) ⟨229310, by rfl⟩ : syracuseStep 305747 = 458621) B458621
theorem B1125035 : Blo 135790 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B305927 : Blo 135790 305927 := bstep (se 1 (by rfl) ⟨229445, by rfl⟩ : syracuseStep 305927 = 458891) B458891
theorem B306143 : Blo 135790 306143 := bstep (se 1 (by rfl) ⟨229607, by rfl⟩ : syracuseStep 306143 = 459215) B459215
theorem B207839 : Blo 135790 207839 := bstep (se 1 (by rfl) ⟨155879, by rfl⟩ : syracuseStep 207839 = 311759) B311759
theorem B306359 : Blo 135790 306359 := bstep (se 1 (by rfl) ⟨229769, by rfl⟩ : syracuseStep 306359 = 459539) B459539
theorem B666899 : Blo 135790 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B1748303 : Blo 135790 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B208283 : Blo 135790 208283 := bstep (se 1 (by rfl) ⟨156212, by rfl⟩ : syracuseStep 208283 = 312425) B312425
theorem B306935 : Blo 135790 306935 := bstep (se 1 (by rfl) ⟨230201, by rfl⟩ : syracuseStep 306935 = 460403) B460403
theorem B307007 : Blo 135790 307007 := bstep (se 1 (by rfl) ⟨230255, by rfl⟩ : syracuseStep 307007 = 460511) B460511
theorem B208703 : Blo 135790 208703 := bstep (se 1 (by rfl) ⟨156527, by rfl⟩ : syracuseStep 208703 = 313055) B313055
theorem B307115 : Blo 135790 307115 := bstep (se 1 (by rfl) ⟨230336, by rfl⟩ : syracuseStep 307115 = 460673) B460673
theorem B208889 : Blo 135790 208889 := bstep (se 2 (by rfl) ⟨78333, by rfl⟩ : syracuseStep 208889 = 156667) B156667
theorem B276377615 : Blo 135790 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B1192157 : Blo 135790 1192157 := bstep (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) B447059
theorem B209129 : Blo 135790 209129 := bstep (se 2 (by rfl) ⟨78423, by rfl⟩ : syracuseStep 209129 = 156847) B156847
theorem B307475 : Blo 135790 307475 := bstep (se 1 (by rfl) ⟨230606, by rfl⟩ : syracuseStep 307475 = 461213) B461213
theorem B209255 : Blo 135790 209255 := bstep (se 1 (by rfl) ⟨156941, by rfl⟩ : syracuseStep 209255 = 313883) B313883
theorem B307655 : Blo 135790 307655 := bstep (se 1 (by rfl) ⟨230741, by rfl⟩ : syracuseStep 307655 = 461483) B461483
theorem B308015 : Blo 135790 308015 := bstep (se 1 (by rfl) ⟨231011, by rfl⟩ : syracuseStep 308015 = 462023) B462023
theorem B308105 : Blo 135790 308105 := bstep (se 2 (by rfl) ⟨115539, by rfl⟩ : syracuseStep 308105 = 231079) B231079
theorem B439177 : Blo 135790 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B1684435 : Blo 135790 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2340089 : Blo 135790 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B537953 : Blo 135790 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B18068993 : Blo 135790 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B308879 : Blo 135790 308879 := bstep (se 1 (by rfl) ⟨231659, by rfl⟩ : syracuseStep 308879 = 463319) B463319
theorem B308969 : Blo 135790 308969 := bstep (se 2 (by rfl) ⟨115863, by rfl⟩ : syracuseStep 308969 = 231727) B231727
theorem B309851 : Blo 135790 309851 := bstep (se 1 (by rfl) ⟨232388, by rfl⟩ : syracuseStep 309851 = 464777) B464777
theorem B309995 : Blo 135790 309995 := bstep (se 1 (by rfl) ⟨232496, by rfl⟩ : syracuseStep 309995 = 464993) B464993
theorem B1064083 : Blo 135790 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B441587 : Blo 135790 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B310607 : Blo 135790 310607 := bstep (se 1 (by rfl) ⟨232955, by rfl⟩ : syracuseStep 310607 = 465911) B465911
theorem B310697 : Blo 135790 310697 := bstep (se 2 (by rfl) ⟨116511, by rfl⟩ : syracuseStep 310697 = 233023) B233023
theorem B310895 : Blo 135790 310895 := bstep (se 1 (by rfl) ⟨233171, by rfl⟩ : syracuseStep 310895 = 466343) B466343
theorem B311183 : Blo 135790 311183 := bstep (se 1 (by rfl) ⟨233387, by rfl⟩ : syracuseStep 311183 = 466775) B466775
theorem B311723 : Blo 135790 311723 := bstep (se 1 (by rfl) ⟨233792, by rfl⟩ : syracuseStep 311723 = 467585) B467585
theorem B311903 : Blo 135790 311903 := bstep (se 1 (by rfl) ⟨233927, by rfl⟩ : syracuseStep 311903 = 467855) B467855
theorem B344857 : Blo 135790 344857 := bstep (se 2 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 344857 = 258643) B258643
theorem B705347 : Blo 135790 705347 := bstep (se 1 (by rfl) ⟨529010, by rfl⟩ : syracuseStep 705347 = 1058021) B1058021
theorem B312263 : Blo 135790 312263 := bstep (se 1 (by rfl) ⟨234197, by rfl⟩ : syracuseStep 312263 = 468395) B468395
theorem B345323 : Blo 135790 345323 := bstep (se 1 (by rfl) ⟨258992, by rfl⟩ : syracuseStep 345323 = 517985) B517985
theorem B312623 : Blo 135790 312623 := bstep (se 1 (by rfl) ⟨234467, by rfl⟩ : syracuseStep 312623 = 468935) B468935
theorem B706157 : Blo 135790 706157 := bstep (se 3 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 706157 = 264809) B264809
theorem B313127 : Blo 135790 313127 := bstep (se 1 (by rfl) ⟨234845, by rfl⟩ : syracuseStep 313127 = 469691) B469691
theorem B247673 : Blo 135790 247673 := bstep (se 2 (by rfl) ⟨92877, by rfl⟩ : syracuseStep 247673 = 185755) B185755
theorem B2672513 : Blo 135790 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B313505 : Blo 135790 313505 := bstep (se 2 (by rfl) ⟨117564, by rfl⟩ : syracuseStep 313505 = 235129) B235129
theorem B313679 : Blo 135790 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B281183 : Blo 135790 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B314153 : Blo 135790 314153 := bstep (se 2 (by rfl) ⟨117807, by rfl⟩ : syracuseStep 314153 = 235615) B235615
theorem B347105 : Blo 135790 347105 := bstep (se 2 (by rfl) ⟨130164, by rfl⟩ : syracuseStep 347105 = 260329) B260329
theorem B314423 : Blo 135790 314423 := bstep (se 1 (by rfl) ⟨235817, by rfl⟩ : syracuseStep 314423 = 471635) B471635
theorem B2673971 : Blo 135790 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B380743 : Blo 135790 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B1790333 : Blo 135790 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B349019 : Blo 135790 349019 := bstep (se 1 (by rfl) ⟨261764, by rfl⟩ : syracuseStep 349019 = 523529) B523529
theorem B2151461 : Blo 135790 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B775291 : Blo 135790 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B349679 : Blo 135790 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B1169225 : Blo 135790 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B1170287 : Blo 135790 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B154831 : Blo 135790 154831 := bstep (se 1 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 154831 = 232247) B232247
theorem B417257 : Blo 135790 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B1170935 : Blo 135790 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B1761425 : Blo 135790 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B155839 : Blo 135790 155839 := bstep (se 1 (by rfl) ⟨116879, by rfl⟩ : syracuseStep 155839 = 233759) B233759
theorem B352795 : Blo 135790 352795 := bstep (se 1 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 352795 = 529193) B529193
theorem B156271 : Blo 135790 156271 := bstep (se 1 (by rfl) ⟨117203, by rfl⟩ : syracuseStep 156271 = 234407) B234407
theorem B156379 : Blo 135790 156379 := bstep (se 1 (by rfl) ⟨117284, by rfl⟩ : syracuseStep 156379 = 234569) B234569
theorem B779165 : Blo 135790 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B2679965 : Blo 135790 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B2647363 : Blo 135790 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B222793 : Blo 135790 222793 := bstep (se 2 (by rfl) ⟨83547, by rfl⟩ : syracuseStep 222793 = 167095) B167095
theorem B2713171 : Blo 135790 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1238813 : Blo 135790 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B223279 : Blo 135790 223279 := bstep (se 1 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 223279 = 334919) B334919
theorem B387305 : Blo 135790 387305 := bstep (se 2 (by rfl) ⟨145239, by rfl⟩ : syracuseStep 387305 = 290479) B290479
theorem B223735 : Blo 135790 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B1042955 : Blo 135790 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B387919 : Blo 135790 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B1896635 : Blo 135790 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B1044899 : Blo 135790 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B1176059 : Blo 135790 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B1864225 : Blo 135790 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B815933 : Blo 135790 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B586835 : Blo 135790 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B619987 : Blo 135790 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B652769 : Blo 135790 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B390881 : Blo 135790 390881 := bstep (se 2 (by rfl) ⟨146580, by rfl⟩ : syracuseStep 390881 = 293161) B293161
theorem B259919 : Blo 135790 259919 := bstep (se 1 (by rfl) ⟨194939, by rfl⟩ : syracuseStep 259919 = 389879) B389879
theorem B1144961 : Blo 135790 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B8485013 : Blo 135790 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B1309193 : Blo 135790 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B490025 : Blo 135790 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B1047329 : Blo 135790 1047329 := bstep (se 2 (by rfl) ⟨392748, by rfl⟩ : syracuseStep 1047329 = 785497) B785497
theorem B163279 : Blo 135790 163279 := bstep (se 1 (by rfl) ⟨122459, by rfl⟩ : syracuseStep 163279 = 244919) B244919
theorem B458351 : Blo 135790 458351 := bstep (se 1 (by rfl) ⟨343763, by rfl⟩ : syracuseStep 458351 = 687527) B687527
theorem B294511 : Blo 135790 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B261863 : Blo 135790 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B327635 : Blo 135790 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B656191 : Blo 135790 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B230215 : Blo 135790 230215 := bstep (se 1 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 230215 = 345323) B345323
theorem B984059 : Blo 135790 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B459809 : Blo 135790 459809 := bstep (se 2 (by rfl) ⟨172428, by rfl⟩ : syracuseStep 459809 = 344857) B344857
theorem B885917 : Blo 135790 885917 := bstep (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) B332219
theorem B394415 : Blo 135790 394415 := bstep (se 1 (by rfl) ⟨295811, by rfl⟩ : syracuseStep 394415 = 591623) B591623
theorem B165115 : Blo 135790 165115 := bstep (se 1 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 165115 = 247673) B247673
theorem B18089405 : Blo 135790 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B788231 : Blo 135790 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B395027 : Blo 135790 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B231403 : Blo 135790 231403 := bstep (se 1 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 231403 = 347105) B347105
theorem B460943 : Blo 135790 460943 := bstep (se 1 (by rfl) ⟨345707, by rfl⟩ : syracuseStep 460943 = 691415) B691415
theorem B461051 : Blo 135790 461051 := bstep (se 1 (by rfl) ⟨345788, by rfl⟩ : syracuseStep 461051 = 691577) B691577
theorem B264863 : Blo 135790 264863 := bstep (se 1 (by rfl) ⟨198647, by rfl⟩ : syracuseStep 264863 = 397295) B397295
theorem B1051703 : Blo 135790 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B789689 : Blo 135790 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B232679 : Blo 135790 232679 := bstep (se 1 (by rfl) ⟨174509, by rfl⟩ : syracuseStep 232679 = 349019) B349019
theorem B298313 : Blo 135790 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B789871 : Blo 135790 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B233119 : Blo 135790 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B5738165 : Blo 135790 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B659167 : Blo 135790 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B1052635 : Blo 135790 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B462887 : Blo 135790 462887 := bstep (se 1 (by rfl) ⟨347165, by rfl⟩ : syracuseStep 462887 = 694331) B694331
theorem B397511 : Blo 135790 397511 := bstep (se 1 (by rfl) ⟨298133, by rfl⟩ : syracuseStep 397511 = 596267) B596267
theorem B463967 : Blo 135790 463967 := bstep (se 1 (by rfl) ⟨347975, by rfl⟩ : syracuseStep 463967 = 695951) B695951
theorem B136303 : Blo 135790 136303 := bstep (se 1 (by rfl) ⟨102227, by rfl⟩ : syracuseStep 136303 = 204455) B204455
theorem B136383 : Blo 135790 136383 := bstep (se 1 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 136383 = 204575) B204575
theorem B267499 : Blo 135790 267499 := bstep (se 1 (by rfl) ⟨200624, by rfl⟩ : syracuseStep 267499 = 401249) B401249
theorem B136671 : Blo 135790 136671 := bstep (se 1 (by rfl) ⟨102503, by rfl⟩ : syracuseStep 136671 = 205007) B205007
theorem B136703 : Blo 135790 136703 := bstep (se 1 (by rfl) ⟨102527, by rfl⟩ : syracuseStep 136703 = 205055) B205055
theorem B137247 : Blo 135790 137247 := bstep (se 1 (by rfl) ⟨102935, by rfl⟩ : syracuseStep 137247 = 205871) B205871
theorem B137327 : Blo 135790 137327 := bstep (se 1 (by rfl) ⟨102995, by rfl⟩ : syracuseStep 137327 = 205991) B205991
theorem B792787 : Blo 135790 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B530651 : Blo 135790 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B137575 : Blo 135790 137575 := bstep (se 1 (by rfl) ⟨103181, by rfl⟩ : syracuseStep 137575 = 206363) B206363
theorem B825875 : Blo 135790 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B137831 : Blo 135790 137831 := bstep (se 1 (by rfl) ⟨103373, by rfl⟩ : syracuseStep 137831 = 206747) B206747
theorem B137855 : Blo 135790 137855 := bstep (se 1 (by rfl) ⟨103391, by rfl⟩ : syracuseStep 137855 = 206783) B206783
theorem B137979 : Blo 135790 137979 := bstep (se 1 (by rfl) ⟨103484, by rfl⟩ : syracuseStep 137979 = 206969) B206969
theorem B1186721 : Blo 135790 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B203771 : Blo 135790 203771 := bstep (se 1 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 203771 = 305657) B305657
theorem B138235 : Blo 135790 138235 := bstep (se 1 (by rfl) ⟨103676, by rfl⟩ : syracuseStep 138235 = 207353) B207353
theorem B695303 : Blo 135790 695303 := bstep (se 1 (by rfl) ⟨521477, by rfl⟩ : syracuseStep 695303 = 1042955) B1042955
theorem B203807 : Blo 135790 203807 := bstep (se 1 (by rfl) ⟨152855, by rfl⟩ : syracuseStep 203807 = 305711) B305711
theorem B138271 : Blo 135790 138271 := bstep (se 1 (by rfl) ⟨103703, by rfl⟩ : syracuseStep 138271 = 207407) B207407
theorem B203831 : Blo 135790 203831 := bstep (se 1 (by rfl) ⟨152873, by rfl⟩ : syracuseStep 203831 = 305747) B305747
theorem B203951 : Blo 135790 203951 := bstep (se 1 (by rfl) ⟨152963, by rfl⟩ : syracuseStep 203951 = 305927) B305927
theorem B826649 : Blo 135790 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B204095 : Blo 135790 204095 := bstep (se 1 (by rfl) ⟨153071, by rfl⟩ : syracuseStep 204095 = 306143) B306143
theorem B138559 : Blo 135790 138559 := bstep (se 1 (by rfl) ⟨103919, by rfl⟩ : syracuseStep 138559 = 207839) B207839
theorem B204239 : Blo 135790 204239 := bstep (se 1 (by rfl) ⟨153179, by rfl⟩ : syracuseStep 204239 = 306359) B306359
theorem B138855 : Blo 135790 138855 := bstep (se 1 (by rfl) ⟨104141, by rfl⟩ : syracuseStep 138855 = 208283) B208283
theorem B204623 : Blo 135790 204623 := bstep (se 1 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 204623 = 306935) B306935
theorem B204671 : Blo 135790 204671 := bstep (se 1 (by rfl) ⟨153503, by rfl⟩ : syracuseStep 204671 = 307007) B307007
theorem B139135 : Blo 135790 139135 := bstep (se 1 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 139135 = 208703) B208703
theorem B204743 : Blo 135790 204743 := bstep (se 1 (by rfl) ⟨153557, by rfl⟩ : syracuseStep 204743 = 307115) B307115
theorem B139259 : Blo 135790 139259 := bstep (se 1 (by rfl) ⟨104444, by rfl⟩ : syracuseStep 139259 = 208889) B208889
theorem B794771 : Blo 135790 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B139419 : Blo 135790 139419 := bstep (se 1 (by rfl) ⟨104564, by rfl⟩ : syracuseStep 139419 = 209129) B209129
theorem B204983 : Blo 135790 204983 := bstep (se 1 (by rfl) ⟨153737, by rfl⟩ : syracuseStep 204983 = 307475) B307475
theorem B139503 : Blo 135790 139503 := bstep (se 1 (by rfl) ⟨104627, by rfl⟩ : syracuseStep 139503 = 209255) B209255
theorem B696599 : Blo 135790 696599 := bstep (se 1 (by rfl) ⟨522449, by rfl⟩ : syracuseStep 696599 = 1044899) B1044899
theorem B205103 : Blo 135790 205103 := bstep (se 1 (by rfl) ⟨153827, by rfl⟩ : syracuseStep 205103 = 307655) B307655
theorem B1188229 : Blo 135790 1188229 := bstep (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) B222793
theorem B205343 : Blo 135790 205343 := bstep (se 1 (by rfl) ⟨154007, by rfl⟩ : syracuseStep 205343 = 308015) B308015
theorem B205403 : Blo 135790 205403 := bstep (se 1 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 205403 = 308105) B308105
theorem B435179 : Blo 135790 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B205919 : Blo 135790 205919 := bstep (se 1 (by rfl) ⟨154439, by rfl⟩ : syracuseStep 205919 = 308879) B308879
theorem B205979 : Blo 135790 205979 := bstep (se 1 (by rfl) ⟨154484, by rfl⟩ : syracuseStep 205979 = 308969) B308969
theorem B173279 : Blo 135790 173279 := bstep (se 1 (by rfl) ⟨129959, by rfl⟩ : syracuseStep 173279 = 259919) B259919
theorem B763307 : Blo 135790 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B1418777 : Blo 135790 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B206441 : Blo 135790 206441 := bstep (se 2 (by rfl) ⟨77415, by rfl⟩ : syracuseStep 206441 = 154831) B154831
theorem B206567 : Blo 135790 206567 := bstep (se 1 (by rfl) ⟨154925, by rfl⟩ : syracuseStep 206567 = 309851) B309851
theorem B206663 : Blo 135790 206663 := bstep (se 1 (by rfl) ⟨154997, by rfl⟩ : syracuseStep 206663 = 309995) B309995
theorem B698219 : Blo 135790 698219 := bstep (se 1 (by rfl) ⟨523664, by rfl⟩ : syracuseStep 698219 = 1047329) B1047329
theorem B207071 : Blo 135790 207071 := bstep (se 1 (by rfl) ⟨155303, by rfl⟩ : syracuseStep 207071 = 310607) B310607
theorem B207131 : Blo 135790 207131 := bstep (se 1 (by rfl) ⟨155348, by rfl⟩ : syracuseStep 207131 = 310697) B310697
theorem B305567 : Blo 135790 305567 := bstep (se 1 (by rfl) ⟨229175, by rfl⟩ : syracuseStep 305567 = 458351) B458351
theorem B207263 : Blo 135790 207263 := bstep (se 1 (by rfl) ⟨155447, by rfl⟩ : syracuseStep 207263 = 310895) B310895
theorem B174575 : Blo 135790 174575 := bstep (se 1 (by rfl) ⟨130931, by rfl⟩ : syracuseStep 174575 = 261863) B261863
theorem B207455 : Blo 135790 207455 := bstep (se 1 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 207455 = 311183) B311183
theorem B1190821 : Blo 135790 1190821 := bstep (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) B223279
theorem B306089 : Blo 135790 306089 := bstep (se 2 (by rfl) ⟨114783, by rfl⟩ : syracuseStep 306089 = 229567) B229567
theorem B207785 : Blo 135790 207785 := bstep (se 2 (by rfl) ⟨77919, by rfl⟩ : syracuseStep 207785 = 155839) B155839
theorem B207815 : Blo 135790 207815 := bstep (se 1 (by rfl) ⟨155861, by rfl⟩ : syracuseStep 207815 = 311723) B311723
theorem B1551311 : Blo 135790 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B207935 : Blo 135790 207935 := bstep (se 1 (by rfl) ⟨155951, by rfl⟩ : syracuseStep 207935 = 311903) B311903
theorem B470231 : Blo 135790 470231 := bstep (se 1 (by rfl) ⟨352673, by rfl⟩ : syracuseStep 470231 = 705347) B705347
theorem B699677 : Blo 135790 699677 := bstep (se 3 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 699677 = 262379) B262379
theorem B208175 : Blo 135790 208175 := bstep (se 1 (by rfl) ⟨156131, by rfl⟩ : syracuseStep 208175 = 312263) B312263
theorem B470393 : Blo 135790 470393 := bstep (se 2 (by rfl) ⟨176397, by rfl⟩ : syracuseStep 470393 = 352795) B352795
theorem B306665 : Blo 135790 306665 := bstep (se 2 (by rfl) ⟨114999, by rfl⟩ : syracuseStep 306665 = 229999) B229999
theorem B208361 : Blo 135790 208361 := bstep (se 2 (by rfl) ⟨78135, by rfl⟩ : syracuseStep 208361 = 156271) B156271
theorem B306719 : Blo 135790 306719 := bstep (se 1 (by rfl) ⟨230039, by rfl⟩ : syracuseStep 306719 = 460079) B460079
theorem B208415 : Blo 135790 208415 := bstep (se 1 (by rfl) ⟨156311, by rfl⟩ : syracuseStep 208415 = 312623) B312623
theorem B208505 : Blo 135790 208505 := bstep (se 2 (by rfl) ⟨78189, by rfl⟩ : syracuseStep 208505 = 156379) B156379
theorem B470771 : Blo 135790 470771 := bstep (se 1 (by rfl) ⟨353078, by rfl⟩ : syracuseStep 470771 = 706157) B706157
theorem B208751 : Blo 135790 208751 := bstep (se 1 (by rfl) ⟨156563, by rfl⟩ : syracuseStep 208751 = 313127) B313127
theorem B1781675 : Blo 135790 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B209003 : Blo 135790 209003 := bstep (se 1 (by rfl) ⟨156752, by rfl⟩ : syracuseStep 209003 = 313505) B313505
theorem B176383 : Blo 135790 176383 := bstep (se 1 (by rfl) ⟨132287, by rfl⟩ : syracuseStep 176383 = 264575) B264575
theorem B209435 : Blo 135790 209435 := bstep (se 1 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 209435 = 314153) B314153
theorem B209615 : Blo 135790 209615 := bstep (se 1 (by rfl) ⟨157211, by rfl⟩ : syracuseStep 209615 = 314423) B314423
theorem B3617561 : Blo 135790 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1782647 : Blo 135790 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B1193555 : Blo 135790 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B440255 : Blo 135790 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B768503 : Blo 135790 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B309815 : Blo 135790 309815 := bstep (se 1 (by rfl) ⟨232361, by rfl⟩ : syracuseStep 309815 = 464723) B464723
theorem B310751 : Blo 135790 310751 := bstep (se 1 (by rfl) ⟨233063, by rfl⟩ : syracuseStep 310751 = 466127) B466127
theorem B278171 : Blo 135790 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B311003 : Blo 135790 311003 := bstep (se 1 (by rfl) ⟨233252, by rfl⟩ : syracuseStep 311003 = 466505) B466505
theorem B442151 : Blo 135790 442151 := bstep (se 1 (by rfl) ⟨331613, by rfl⟩ : syracuseStep 442151 = 663227) B663227
theorem B311273 : Blo 135790 311273 := bstep (se 2 (by rfl) ⟨116727, by rfl⟩ : syracuseStep 311273 = 233455) B233455
theorem B377303 : Blo 135790 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B705185 : Blo 135790 705185 := bstep (se 2 (by rfl) ⟨264444, by rfl⟩ : syracuseStep 705185 = 528889) B528889
theorem B1491655 : Blo 135790 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B1786643 : Blo 135790 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B836477 : Blo 135790 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B2245913 : Blo 135790 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B443677 : Blo 135790 443677 := bstep (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) B166379
theorem B312731 : Blo 135790 312731 := bstep (se 1 (by rfl) ⟨234548, by rfl⟩ : syracuseStep 312731 = 469097) B469097
theorem B1033721 : Blo 135790 1033721 := bstep (se 2 (by rfl) ⟨387645, by rfl⟩ : syracuseStep 1033721 = 775291) B775291
theorem B1164851 : Blo 135790 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B444599 : Blo 135790 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B1165535 : Blo 135790 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B870821 : Blo 135790 870821 := bstep (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) B163279
theorem B1264423 : Blo 135790 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B445625 : Blo 135790 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B543955 : Blo 135790 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B1560059 : Blo 135790 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B708221 : Blo 135790 708221 := bstep (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) B265583
theorem B12045995 : Blo 135790 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B5656675 : Blo 135790 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B872795 : Blo 135790 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B218423 : Blo 135790 218423 := bstep (se 1 (by rfl) ⟨163817, by rfl⟩ : syracuseStep 218423 = 327635) B327635
theorem B350345 : Blo 135790 350345 := bstep (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) B262759
theorem B6609113 : Blo 135790 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B153823 : Blo 135790 153823 := bstep (se 1 (by rfl) ⟨115367, by rfl⟩ : syracuseStep 153823 = 230735) B230735
theorem B219743 : Blo 135790 219743 := bstep (se 1 (by rfl) ⟨164807, by rfl⟩ : syracuseStep 219743 = 329615) B329615
theorem B219839 : Blo 135790 219839 := bstep (se 1 (by rfl) ⟨164879, by rfl⟩ : syracuseStep 219839 = 329759) B329759
theorem B350963 : Blo 135790 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B154471 : Blo 135790 154471 := bstep (se 1 (by rfl) ⟨115853, by rfl⟩ : syracuseStep 154471 = 231707) B231707
theorem B154687 : Blo 135790 154687 := bstep (se 1 (by rfl) ⟨116015, by rfl⟩ : syracuseStep 154687 = 232031) B232031
theorem B3529817 : Blo 135790 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B351337 : Blo 135790 351337 := bstep (se 2 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 351337 = 263503) B263503
theorem B352471 : Blo 135790 352471 := bstep (se 1 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 352471 = 528707) B528707
theorem B352633 : Blo 135790 352633 := bstep (se 2 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 352633 = 264475) B264475
theorem B1008071 : Blo 135790 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B352775 : Blo 135790 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B1434307 : Blo 135790 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B156763 : Blo 135790 156763 := bstep (se 1 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 156763 = 235145) B235145
theorem B156775 : Blo 135790 156775 := bstep (se 1 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 156775 = 235163) B235163
theorem B517225 : Blo 135790 517225 := bstep (se 2 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 517225 = 387919) B387919
theorem B779483 : Blo 135790 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B780191 : Blo 135790 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B4876199 : Blo 135790 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B780623 : Blo 135790 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B748187 : Blo 135790 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B1174283 : Blo 135790 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B748379 : Blo 135790 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B519443 : Blo 135790 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B2485633 : Blo 135790 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B585569 : Blo 135790 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B258203 : Blo 135790 258203 := bstep (se 1 (by rfl) ⟨193652, by rfl⟩ : syracuseStep 258203 = 387305) B387305
theorem B749821 : Blo 135790 749821 := bstep (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) B281183
theorem B3633547 : Blo 135790 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B750023 : Blo 135790 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B184251743 : Blo 135790 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B784039 : Blo 135790 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B391223 : Blo 135790 391223 := bstep (se 1 (by rfl) ⟨293417, by rfl⟩ : syracuseStep 391223 = 586835) B586835
theorem B260587 : Blo 135790 260587 := bstep (se 1 (by rfl) ⟨195440, by rfl⟩ : syracuseStep 260587 = 390881) B390881
theorem B326683 : Blo 135790 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B2030629 : Blo 135790 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B392681 : Blo 135790 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B294391 : Blo 135790 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B622525 : Blo 135790 622525 := bstep (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) B233447
theorem B557651 : Blo 135790 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B656039 : Blo 135790 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B590611 : Blo 135790 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B262943 : Blo 135790 262943 := bstep (se 1 (by rfl) ⟨197207, by rfl⟩ : syracuseStep 262943 = 394415) B394415
theorem B12059603 : Blo 135790 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B689147 : Blo 135790 689147 := bstep (se 1 (by rfl) ⟨516860, by rfl⟩ : syracuseStep 689147 = 1033721) B1033721
theorem B525487 : Blo 135790 525487 := bstep (se 1 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 525487 = 788231) B788231
theorem B263351 : Blo 135790 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B296399 : Blo 135790 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B689633 : Blo 135790 689633 := bstep (se 2 (by rfl) ⟨258612, by rfl⟩ : syracuseStep 689633 = 517225) B517225
theorem B591569 : Blo 135790 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B526459 : Blo 135790 526459 := bstep (se 1 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 526459 = 789689) B789689
theorem B297083 : Blo 135790 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B198875 : Blo 135790 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B8030663 : Blo 135790 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B265007 : Blo 135790 265007 := bstep (se 1 (by rfl) ⟨198755, by rfl⟩ : syracuseStep 265007 = 397511) B397511
theorem B462077 : Blo 135790 462077 := bstep (se 3 (by rfl) ⟨86639, by rfl⟩ : syracuseStep 462077 = 173279) B173279
theorem B233563 : Blo 135790 233563 := bstep (se 1 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 233563 = 350345) B350345
theorem B725273 : Blo 135790 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B1053161 : Blo 135790 1053161 := bstep (se 2 (by rfl) ⟨394935, by rfl⟩ : syracuseStep 1053161 = 789871) B789871
theorem B233975 : Blo 135790 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B3314177 : Blo 135790 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B791147 : Blo 135790 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B135847 : Blo 135790 135847 := bstep (se 1 (by rfl) ⟨101885, by rfl⟩ : syracuseStep 135847 = 203771) B203771
theorem B463535 : Blo 135790 463535 := bstep (se 1 (by rfl) ⟨347651, by rfl⟩ : syracuseStep 463535 = 695303) B695303
theorem B135871 : Blo 135790 135871 := bstep (se 1 (by rfl) ⟨101903, by rfl⟩ : syracuseStep 135871 = 203807) B203807
theorem B135887 : Blo 135790 135887 := bstep (se 1 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 135887 = 203831) B203831
theorem B135967 : Blo 135790 135967 := bstep (se 1 (by rfl) ⟨101975, by rfl⟩ : syracuseStep 135967 = 203951) B203951
theorem B136063 : Blo 135790 136063 := bstep (se 1 (by rfl) ⟨102047, by rfl⟩ : syracuseStep 136063 = 204095) B204095
theorem B136159 : Blo 135790 136159 := bstep (se 1 (by rfl) ⟨102119, by rfl⟩ : syracuseStep 136159 = 204239) B204239
theorem B136415 : Blo 135790 136415 := bstep (se 1 (by rfl) ⟨102311, by rfl⟩ : syracuseStep 136415 = 204623) B204623
theorem B136447 : Blo 135790 136447 := bstep (se 1 (by rfl) ⟨102335, by rfl⟩ : syracuseStep 136447 = 204671) B204671
theorem B136495 : Blo 135790 136495 := bstep (se 1 (by rfl) ⟨102371, by rfl⟩ : syracuseStep 136495 = 204743) B204743
theorem B529847 : Blo 135790 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B136655 : Blo 135790 136655 := bstep (se 1 (by rfl) ⟨102491, by rfl⟩ : syracuseStep 136655 = 204983) B204983
theorem B7542233 : Blo 135790 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B1742309 : Blo 135790 1742309 := bstep (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) B326683
theorem B464399 : Blo 135790 464399 := bstep (se 1 (by rfl) ⟨348299, by rfl⟩ : syracuseStep 464399 = 696599) B696599
theorem B136735 : Blo 135790 136735 := bstep (se 1 (by rfl) ⟨102551, by rfl⟩ : syracuseStep 136735 = 205103) B205103
theorem B235183 : Blo 135790 235183 := bstep (se 1 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 235183 = 352775) B352775
theorem B136895 : Blo 135790 136895 := bstep (se 1 (by rfl) ⟨102671, by rfl⟩ : syracuseStep 136895 = 205343) B205343
theorem B136935 : Blo 135790 136935 := bstep (se 1 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 136935 = 205403) B205403
theorem B137279 : Blo 135790 137279 := bstep (se 1 (by rfl) ⟨102959, by rfl⟩ : syracuseStep 137279 = 205919) B205919
theorem B137319 : Blo 135790 137319 := bstep (se 1 (by rfl) ⟨102989, by rfl⟩ : syracuseStep 137319 = 205979) B205979
theorem B137627 : Blo 135790 137627 := bstep (se 1 (by rfl) ⟨103220, by rfl⟩ : syracuseStep 137627 = 206441) B206441
theorem B137711 : Blo 135790 137711 := bstep (se 1 (by rfl) ⟨103283, by rfl⟩ : syracuseStep 137711 = 206567) B206567
theorem B137775 : Blo 135790 137775 := bstep (se 1 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 137775 = 206663) B206663
theorem B465479 : Blo 135790 465479 := bstep (se 1 (by rfl) ⟨349109, by rfl⟩ : syracuseStep 465479 = 698219) B698219
theorem B3250799 : Blo 135790 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B465533 : Blo 135790 465533 := bstep (se 3 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 465533 = 174575) B174575
theorem B138047 : Blo 135790 138047 := bstep (se 1 (by rfl) ⟨103535, by rfl⟩ : syracuseStep 138047 = 207071) B207071
theorem B138087 : Blo 135790 138087 := bstep (se 1 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 138087 = 207131) B207131
theorem B203711 : Blo 135790 203711 := bstep (se 1 (by rfl) ⟨152783, by rfl⟩ : syracuseStep 203711 = 305567) B305567
theorem B138175 : Blo 135790 138175 := bstep (se 1 (by rfl) ⟨103631, by rfl⟩ : syracuseStep 138175 = 207263) B207263
theorem B138303 : Blo 135790 138303 := bstep (se 1 (by rfl) ⟨103727, by rfl⟩ : syracuseStep 138303 = 207455) B207455
theorem B498791 : Blo 135790 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B498919 : Blo 135790 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B204059 : Blo 135790 204059 := bstep (se 1 (by rfl) ⟨153044, by rfl⟩ : syracuseStep 204059 = 306089) B306089
theorem B138523 : Blo 135790 138523 := bstep (se 1 (by rfl) ⟨103892, by rfl⟩ : syracuseStep 138523 = 207785) B207785
theorem B138543 : Blo 135790 138543 := bstep (se 1 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 138543 = 207815) B207815
theorem B138623 : Blo 135790 138623 := bstep (se 1 (by rfl) ⟨103967, by rfl⟩ : syracuseStep 138623 = 207935) B207935
theorem B466451 : Blo 135790 466451 := bstep (se 1 (by rfl) ⟨349838, by rfl⟩ : syracuseStep 466451 = 699677) B699677
theorem B138783 : Blo 135790 138783 := bstep (se 1 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 138783 = 208175) B208175
theorem B204443 : Blo 135790 204443 := bstep (se 1 (by rfl) ⟨153332, by rfl⟩ : syracuseStep 204443 = 306665) B306665
theorem B138907 : Blo 135790 138907 := bstep (se 1 (by rfl) ⟨104180, by rfl⟩ : syracuseStep 138907 = 208361) B208361
theorem B204479 : Blo 135790 204479 := bstep (se 1 (by rfl) ⟨153359, by rfl⟩ : syracuseStep 204479 = 306719) B306719
theorem B138943 : Blo 135790 138943 := bstep (se 1 (by rfl) ⟨104207, by rfl⟩ : syracuseStep 138943 = 208415) B208415
theorem B139003 : Blo 135790 139003 := bstep (se 1 (by rfl) ⟨104252, by rfl⟩ : syracuseStep 139003 = 208505) B208505
theorem B139167 : Blo 135790 139167 := bstep (se 1 (by rfl) ⟨104375, by rfl⟩ : syracuseStep 139167 = 208751) B208751
theorem B1187783 : Blo 135790 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B139335 : Blo 135790 139335 := bstep (se 1 (by rfl) ⟨104501, by rfl⟩ : syracuseStep 139335 = 209003) B209003
theorem B172135 : Blo 135790 172135 := bstep (se 1 (by rfl) ⟨129101, by rfl⟩ : syracuseStep 172135 = 258203) B258203
theorem B1057049 : Blo 135790 1057049 := bstep (se 2 (by rfl) ⟨396393, by rfl⟩ : syracuseStep 1057049 = 792787) B792787
theorem B205097 : Blo 135790 205097 := bstep (se 2 (by rfl) ⟨76911, by rfl⟩ : syracuseStep 205097 = 153823) B153823
theorem B500015 : Blo 135790 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B139623 : Blo 135790 139623 := bstep (se 1 (by rfl) ⟨104717, by rfl⟩ : syracuseStep 139623 = 209435) B209435
theorem B139743 : Blo 135790 139743 := bstep (se 1 (by rfl) ⟨104807, by rfl⟩ : syracuseStep 139743 = 209615) B209615
theorem B1188431 : Blo 135790 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B795703 : Blo 135790 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B205961 : Blo 135790 205961 := bstep (se 2 (by rfl) ⟨77235, by rfl⟩ : syracuseStep 205961 = 154471) B154471
theorem B3515557 : Blo 135790 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B206249 : Blo 135790 206249 := bstep (se 2 (by rfl) ⟨77343, by rfl⟩ : syracuseStep 206249 = 154687) B154687
theorem B468449 : Blo 135790 468449 := bstep (se 2 (by rfl) ⟨175668, by rfl⟩ : syracuseStep 468449 = 351337) B351337
theorem B206543 : Blo 135790 206543 := bstep (se 1 (by rfl) ⟨154907, by rfl⟩ : syracuseStep 206543 = 309815) B309815
theorem B207167 : Blo 135790 207167 := bstep (se 1 (by rfl) ⟨155375, by rfl⟩ : syracuseStep 207167 = 310751) B310751
theorem B207335 : Blo 135790 207335 := bstep (se 1 (by rfl) ⟨155501, by rfl⟩ : syracuseStep 207335 = 311003) B311003
theorem B830033 : Blo 135790 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B207515 : Blo 135790 207515 := bstep (se 1 (by rfl) ⟨155636, by rfl⟩ : syracuseStep 207515 = 311273) B311273
theorem B469961 : Blo 135790 469961 := bstep (se 2 (by rfl) ⟨176235, by rfl⟩ : syracuseStep 469961 = 352471) B352471
theorem B470123 : Blo 135790 470123 := bstep (se 1 (by rfl) ⟨352592, by rfl⟩ : syracuseStep 470123 = 705185) B705185
theorem B470177 : Blo 135790 470177 := bstep (se 2 (by rfl) ⟨176316, by rfl⟩ : syracuseStep 470177 = 352633) B352633
theorem B1584305 : Blo 135790 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B1191095 : Blo 135790 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B306539 : Blo 135790 306539 := bstep (se 1 (by rfl) ⟨229904, by rfl⟩ : syracuseStep 306539 = 459809) B459809
theorem B1912409 : Blo 135790 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B208487 : Blo 135790 208487 := bstep (se 1 (by rfl) ⟨156365, by rfl⟩ : syracuseStep 208487 = 312731) B312731
theorem B306953 : Blo 135790 306953 := bstep (se 2 (by rfl) ⟨115107, by rfl⟩ : syracuseStep 306953 = 230215) B230215
theorem B307295 : Blo 135790 307295 := bstep (se 1 (by rfl) ⟨230471, by rfl⟩ : syracuseStep 307295 = 460943) B460943
theorem B209017 : Blo 135790 209017 := bstep (se 2 (by rfl) ⟨78381, by rfl⟩ : syracuseStep 209017 = 156763) B156763
theorem B209033 : Blo 135790 209033 := bstep (se 2 (by rfl) ⟨78387, by rfl⟩ : syracuseStep 209033 = 156775) B156775
theorem B307367 : Blo 135790 307367 := bstep (se 1 (by rfl) ⟨230525, by rfl⟩ : syracuseStep 307367 = 461051) B461051
theorem B176575 : Blo 135790 176575 := bstep (se 1 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 176575 = 264863) B264863
theorem B701135 : Blo 135790 701135 := bstep (se 1 (by rfl) ⟨525851, by rfl⟩ : syracuseStep 701135 = 1051703) B1051703
theorem B1160477 : Blo 135790 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B308537 : Blo 135790 308537 := bstep (se 2 (by rfl) ⟨115701, by rfl⟩ : syracuseStep 308537 = 231403) B231403
theorem B308591 : Blo 135790 308591 := bstep (se 1 (by rfl) ⟨231443, by rfl⟩ : syracuseStep 308591 = 462887) B462887
theorem B309311 : Blo 135790 309311 := bstep (se 1 (by rfl) ⟨231983, by rfl⟩ : syracuseStep 309311 = 463967) B463967
theorem B1685897 : Blo 135790 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B1587761 : Blo 135790 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B4406075 : Blo 135790 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B146495 : Blo 135790 146495 := bstep (se 1 (by rfl) ⟨109871, by rfl⟩ : syracuseStep 146495 = 219743) B219743
theorem B310825 : Blo 135790 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B672047 : Blo 135790 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B999761 : Blo 135790 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B508871 : Blo 135790 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B1034207 : Blo 135790 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B313487 : Blo 135790 313487 := bstep (se 1 (by rfl) ⟨235115, by rfl⟩ : syracuseStep 313487 = 470231) B470231
theorem B346295 : Blo 135790 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B313595 : Blo 135790 313595 := bstep (se 1 (by rfl) ⟨235196, by rfl⟩ : syracuseStep 313595 = 470393) B470393
theorem B313847 : Blo 135790 313847 := bstep (se 1 (by rfl) ⟨235385, by rfl⟩ : syracuseStep 313847 = 470771) B470771
theorem B2411707 : Blo 135790 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B347449 : Blo 135790 347449 := bstep (se 2 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 347449 = 260587) B260587
theorem B122834495 : Blo 135790 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B2707505 : Blo 135790 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B1888589 : Blo 135790 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B512335 : Blo 135790 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B1561517 : Blo 135790 1561517 := bstep (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) B585569
theorem B185447 : Blo 135790 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B1497275 : Blo 135790 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B1988873 : Blo 135790 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B776567 : Blo 135790 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B874921 : Blo 135790 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B1006141 : Blo 135790 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B940709 : Blo 135790 940709 := bstep (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) B176383
theorem B777023 : Blo 135790 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B580547 : Blo 135790 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B220153 : Blo 135790 220153 := bstep (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) B165115
theorem B155119 : Blo 135790 155119 := bstep (se 1 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 155119 = 232679) B232679
theorem B1040039 : Blo 135790 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B3825443 : Blo 135790 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B581863 : Blo 135790 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B582461 : Blo 135790 582461 := bstep (se 3 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 582461 = 218423) B218423
theorem B353767 : Blo 135790 353767 := bstep (se 1 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 353767 = 530651) B530651
theorem B550583 : Blo 135790 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B2353211 : Blo 135790 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B551099 : Blo 135790 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B1403513 : Blo 135790 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B4844729 : Blo 135790 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B519655 : Blo 135790 519655 := bstep (se 1 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 519655 = 779483) B779483
theorem B945851 : Blo 135790 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B520127 : Blo 135790 520127 := bstep (se 1 (by rfl) ⟨390095, by rfl⟩ : syracuseStep 520127 = 780191) B780191
theorem B520415 : Blo 135790 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B356665 : Blo 135790 356665 := bstep (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) B267499
theorem B586237 : Blo 135790 586237 := bstep (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) B219839
theorem B782855 : Blo 135790 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B1045385 : Blo 135790 1045385 := bstep (se 2 (by rfl) ⟨392019, by rfl⟩ : syracuseStep 1045385 = 784039) B784039
theorem B293503 : Blo 135790 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B260815 : Blo 135790 260815 := bstep (se 1 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 260815 = 391223) B391223
theorem B392521 : Blo 135790 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B261787 : Blo 135790 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B294767 : Blo 135790 294767 := bstep (se 1 (by rfl) ⟨221075, by rfl⟩ : syracuseStep 294767 = 442151) B442151
theorem B229513 : Blo 135790 229513 := bstep (se 2 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 229513 = 172135) B172135
theorem B459431 : Blo 135790 459431 := bstep (se 1 (by rfl) ⟨344573, by rfl⟩ : syracuseStep 459431 = 689147) B689147
theorem B459755 : Blo 135790 459755 := bstep (se 1 (by rfl) ⟨344816, by rfl⟩ : syracuseStep 459755 = 689633) B689633
theorem B787481 : Blo 135790 787481 := bstep (se 2 (by rfl) ⟨295305, by rfl⟩ : syracuseStep 787481 = 590611) B590611
theorem B394379 : Blo 135790 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B689471 : Blo 135790 689471 := bstep (se 1 (by rfl) ⟨517103, by rfl⟩ : syracuseStep 689471 = 1034207) B1034207
theorem B198055 : Blo 135790 198055 := bstep (se 1 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 198055 = 297083) B297083
theorem B230863 : Blo 135790 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B4687409 : Blo 135790 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B81889663 : Blo 135790 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B1805003 : Blo 135790 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B494525 : Blo 135790 494525 := bstep (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) B185447
theorem B527431 : Blo 135790 527431 := bstep (se 1 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 527431 = 791147) B791147
theorem B790397 : Blo 135790 790397 := bstep (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) B296399
theorem B3215609 : Blo 135790 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B2167199 : Blo 135790 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B463265 : Blo 135790 463265 := bstep (se 2 (by rfl) ⟨173724, by rfl⟩ : syracuseStep 463265 = 347449) B347449
theorem B627139 : Blo 135790 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B135807 : Blo 135790 135807 := bstep (se 1 (by rfl) ⟨101855, by rfl⟩ : syracuseStep 135807 = 203711) B203711
theorem B692873 : Blo 135790 692873 := bstep (se 2 (by rfl) ⟨259827, by rfl⟩ : syracuseStep 692873 = 519655) B519655
theorem B332527 : Blo 135790 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B136039 : Blo 135790 136039 := bstep (se 1 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 136039 = 204059) B204059
theorem B136295 : Blo 135790 136295 := bstep (se 1 (by rfl) ⟨102221, by rfl⟩ : syracuseStep 136295 = 204443) B204443
theorem B693359 : Blo 135790 693359 := bstep (se 1 (by rfl) ⟨520019, by rfl⟩ : syracuseStep 693359 = 1040039) B1040039
theorem B136319 : Blo 135790 136319 := bstep (se 1 (by rfl) ⟨102239, by rfl⟩ : syracuseStep 136319 = 204479) B204479
theorem B791855 : Blo 135790 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B136731 : Blo 135790 136731 := bstep (se 1 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 136731 = 205097) B205097
theorem B333343 : Blo 135790 333343 := bstep (se 1 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 333343 = 500015) B500015
theorem B792287 : Blo 135790 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B530333 : Blo 135790 530333 := bstep (se 3 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 530333 = 198875) B198875
theorem B235433 : Blo 135790 235433 := bstep (se 2 (by rfl) ⟨88287, by rfl⟩ : syracuseStep 235433 = 176575) B176575
theorem B137307 : Blo 135790 137307 := bstep (se 1 (by rfl) ⟨102980, by rfl⟩ : syracuseStep 137307 = 205961) B205961
theorem B137499 : Blo 135790 137499 := bstep (se 1 (by rfl) ⟨103124, by rfl⟩ : syracuseStep 137499 = 206249) B206249
theorem B367055 : Blo 135790 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B137695 : Blo 135790 137695 := bstep (se 1 (by rfl) ⟨103271, by rfl⟩ : syracuseStep 137695 = 206543) B206543
theorem B367399 : Blo 135790 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B138111 : Blo 135790 138111 := bstep (se 1 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 138111 = 207167) B207167
theorem B138223 : Blo 135790 138223 := bstep (se 1 (by rfl) ⟨103667, by rfl⟩ : syracuseStep 138223 = 207335) B207335
theorem B138343 : Blo 135790 138343 := bstep (se 1 (by rfl) ⟨103757, by rfl⟩ : syracuseStep 138343 = 207515) B207515
theorem B1056203 : Blo 135790 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B794063 : Blo 135790 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B204359 : Blo 135790 204359 := bstep (se 1 (by rfl) ⟨153269, by rfl⟩ : syracuseStep 204359 = 306539) B306539
theorem B138991 : Blo 135790 138991 := bstep (se 1 (by rfl) ⟨104243, by rfl⟩ : syracuseStep 138991 = 208487) B208487
theorem B204635 : Blo 135790 204635 := bstep (se 1 (by rfl) ⟨153476, by rfl⟩ : syracuseStep 204635 = 306953) B306953
theorem B204863 : Blo 135790 204863 := bstep (se 1 (by rfl) ⟨153647, by rfl⟩ : syracuseStep 204863 = 307295) B307295
theorem B139355 : Blo 135790 139355 := bstep (se 1 (by rfl) ⟨104516, by rfl⟩ : syracuseStep 139355 = 209033) B209033
theorem B204911 : Blo 135790 204911 := bstep (se 1 (by rfl) ⟨153683, by rfl⟩ : syracuseStep 204911 = 307367) B307367
theorem B467423 : Blo 135790 467423 := bstep (se 1 (by rfl) ⟨350567, by rfl⟩ : syracuseStep 467423 = 701135) B701135
theorem B12919277 : Blo 135790 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B696923 : Blo 135790 696923 := bstep (se 1 (by rfl) ⟨522692, by rfl⟩ : syracuseStep 696923 = 1045385) B1045385
theorem B205691 : Blo 135790 205691 := bstep (se 1 (by rfl) ⟨154268, by rfl⟩ : syracuseStep 205691 = 308537) B308537
theorem B205727 : Blo 135790 205727 := bstep (se 1 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 205727 = 308591) B308591
theorem B206207 : Blo 135790 206207 := bstep (se 1 (by rfl) ⟨154655, by rfl⟩ : syracuseStep 206207 = 309311) B309311
theorem B1123931 : Blo 135790 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B665225 : Blo 135790 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B1058507 : Blo 135790 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B206825 : Blo 135790 206825 := bstep (se 2 (by rfl) ⟨77559, by rfl⟩ : syracuseStep 206825 = 155119) B155119
theorem B437359 : Blo 135790 437359 := bstep (se 1 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 437359 = 656039) B656039
theorem B175295 : Blo 135790 175295 := bstep (se 1 (by rfl) ⟨131471, by rfl⟩ : syracuseStep 175295 = 262943) B262943
theorem B339247 : Blo 135790 339247 := bstep (se 1 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 339247 = 508871) B508871
theorem B8039735 : Blo 135790 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B2666029 : Blo 135790 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B1060937 : Blo 135790 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B208991 : Blo 135790 208991 := bstep (se 1 (by rfl) ⟨156743, by rfl⟩ : syracuseStep 208991 = 313487) B313487
theorem B209063 : Blo 135790 209063 := bstep (se 1 (by rfl) ⟨156797, by rfl⟩ : syracuseStep 209063 = 313595) B313595
theorem B1487069 : Blo 135790 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B700649 : Blo 135790 700649 := bstep (se 2 (by rfl) ⟨262743, by rfl⟩ : syracuseStep 700649 = 525487) B525487
theorem B5353775 : Blo 135790 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B209231 : Blo 135790 209231 := bstep (se 1 (by rfl) ⟨156923, by rfl⟩ : syracuseStep 209231 = 313847) B313847
theorem B2732453 : Blo 135790 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B176671 : Blo 135790 176671 := bstep (se 1 (by rfl) ⟨132503, by rfl⟩ : syracuseStep 176671 = 265007) B265007
theorem B471689 : Blo 135790 471689 := bstep (se 2 (by rfl) ⟨176883, by rfl⟩ : syracuseStep 471689 = 353767) B353767
theorem B308051 : Blo 135790 308051 := bstep (se 1 (by rfl) ⟨231038, by rfl⟩ : syracuseStep 308051 = 462077) B462077
theorem B701945 : Blo 135790 701945 := bstep (se 2 (by rfl) ⟨263229, by rfl⟩ : syracuseStep 701945 = 526459) B526459
theorem B1259059 : Blo 135790 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B702107 : Blo 135790 702107 := bstep (se 1 (by rfl) ⟨526580, by rfl⟩ : syracuseStep 702107 = 1053161) B1053161
theorem B2209451 : Blo 135790 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B309023 : Blo 135790 309023 := bstep (se 1 (by rfl) ⟨231767, by rfl⟩ : syracuseStep 309023 = 463535) B463535
theorem B702269 : Blo 135790 702269 := bstep (se 3 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 702269 = 263351) B263351
theorem B5028155 : Blo 135790 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B1161539 : Blo 135790 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B309599 : Blo 135790 309599 := bstep (se 1 (by rfl) ⟨232199, by rfl⟩ : syracuseStep 309599 = 464399) B464399
theorem B998183 : Blo 135790 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B1325915 : Blo 135790 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B310319 : Blo 135790 310319 := bstep (se 1 (by rfl) ⟨232739, by rfl⟩ : syracuseStep 310319 = 465479) B465479
theorem B310355 : Blo 135790 310355 := bstep (se 1 (by rfl) ⟨232766, by rfl⟩ : syracuseStep 310355 = 465533) B465533
theorem B310967 : Blo 135790 310967 := bstep (se 1 (by rfl) ⟨233225, by rfl⟩ : syracuseStep 310967 = 466451) B466451
theorem B311417 : Blo 135790 311417 := bstep (se 2 (by rfl) ⟨116781, by rfl⟩ : syracuseStep 311417 = 233563) B233563
theorem B278689 : Blo 135790 278689 := bstep (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) B209017
theorem B704699 : Blo 135790 704699 := bstep (se 1 (by rfl) ⟨528524, by rfl⟩ : syracuseStep 704699 = 1057049) B1057049
theorem B475553 : Blo 135790 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B312299 : Blo 135790 312299 := bstep (se 1 (by rfl) ⟨234224, by rfl⟩ : syracuseStep 312299 = 468449) B468449
theorem B935675 : Blo 135790 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B313307 : Blo 135790 313307 := bstep (se 1 (by rfl) ⟨234980, by rfl⟩ : syracuseStep 313307 = 469961) B469961
theorem B313415 : Blo 135790 313415 := bstep (se 1 (by rfl) ⟨235061, by rfl⟩ : syracuseStep 313415 = 470123) B470123
theorem B313451 : Blo 135790 313451 := bstep (se 1 (by rfl) ⟨235088, by rfl⟩ : syracuseStep 313451 = 470177) B470177
theorem B313577 : Blo 135790 313577 := bstep (se 2 (by rfl) ⟨117591, by rfl⟩ : syracuseStep 313577 = 235183) B235183
theorem B346751 : Blo 135790 346751 := bstep (se 1 (by rfl) ⟨260063, by rfl⟩ : syracuseStep 346751 = 520127) B520127
theorem B346943 : Blo 135790 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B1166561 : Blo 135790 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B773651 : Blo 135790 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B347753 : Blo 135790 347753 := bstep (se 2 (by rfl) ⟨130407, by rfl⟩ : syracuseStep 347753 = 260815) B260815
theorem B2937383 : Blo 135790 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B414433 : Blo 135790 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B349049 : Blo 135790 349049 := bstep (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) B261787
theorem B185257 : Blo 135790 185257 := bstep (se 2 (by rfl) ⟨69471, by rfl⟩ : syracuseStep 185257 = 138943) B138943
theorem B448031 : Blo 135790 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B775817 : Blo 135790 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B483515 : Blo 135790 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B155983 : Blo 135790 155983 := bstep (se 1 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 155983 = 233975) B233975
theorem B1041011 : Blo 135790 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B353231 : Blo 135790 353231 := bstep (se 1 (by rfl) ⟨264923, by rfl⟩ : syracuseStep 353231 = 529847) B529847
theorem B517711 : Blo 135790 517711 := bstep (se 1 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 517711 = 776567) B776567
theorem B518015 : Blo 135790 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B387031 : Blo 135790 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B2550295 : Blo 135790 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B388307 : Blo 135790 388307 := bstep (se 1 (by rfl) ⟨291230, by rfl⟩ : syracuseStep 388307 = 582461) B582461
theorem B781649 : Blo 135790 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B1568807 : Blo 135790 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B553355 : Blo 135790 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B1274939 : Blo 135790 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B390653 : Blo 135790 390653 := bstep (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) B146495
theorem B521903 : Blo 135790 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B1341521 : Blo 135790 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B391337 : Blo 135790 391337 := bstep (se 2 (by rfl) ⟨146751, by rfl⟩ : syracuseStep 391337 = 293503) B293503
theorem B293537 : Blo 135790 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B523361 : Blo 135790 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B2522269 : Blo 135790 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B196511 : Blo 135790 196511 := bstep (se 1 (by rfl) ⟨147383, by rfl⟩ : syracuseStep 196511 = 294767) B294767
theorem B524987 : Blo 135790 524987 := bstep (se 1 (by rfl) ⟨393740, by rfl⟩ : syracuseStep 524987 = 787481) B787481
theorem B262919 : Blo 135790 262919 := bstep (se 1 (by rfl) ⟨197189, by rfl⟩ : syracuseStep 262919 = 394379) B394379
theorem B459647 : Blo 135790 459647 := bstep (se 1 (by rfl) ⟨344735, by rfl⟩ : syracuseStep 459647 = 689471) B689471
theorem B623783 : Blo 135790 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B231167 : Blo 135790 231167 := bstep (se 1 (by rfl) ⟨173375, by rfl⟩ : syracuseStep 231167 = 346751) B346751
theorem B231295 : Blo 135790 231295 := bstep (se 1 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 231295 = 346943) B346943
theorem B264073 : Blo 135790 264073 := bstep (se 2 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 264073 = 198055) B198055
theorem B329683 : Blo 135790 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B690281 : Blo 135790 690281 := bstep (se 2 (by rfl) ⟨258855, by rfl⟩ : syracuseStep 690281 = 517711) B517711
theorem B231835 : Blo 135790 231835 := bstep (se 1 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 231835 = 347753) B347753
theorem B526931 : Blo 135790 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B1444799 : Blo 135790 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B461915 : Blo 135790 461915 := bstep (se 1 (by rfl) ⟨346436, by rfl⟩ : syracuseStep 461915 = 692873) B692873
theorem B109186217 : Blo 135790 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B232699 : Blo 135790 232699 := bstep (se 1 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 232699 = 349049) B349049
theorem B462239 : Blo 135790 462239 := bstep (se 1 (by rfl) ⟨346679, by rfl⟩ : syracuseStep 462239 = 693359) B693359
theorem B527903 : Blo 135790 527903 := bstep (se 1 (by rfl) ⟨395927, by rfl⟩ : syracuseStep 527903 = 791855) B791855
theorem B298687 : Blo 135790 298687 := bstep (se 1 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 298687 = 448031) B448031
theorem B528191 : Blo 135790 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B988037 : Blo 135790 988037 := bstep (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) B185257
theorem B529375 : Blo 135790 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B136239 : Blo 135790 136239 := bstep (se 1 (by rfl) ⟨102179, by rfl⟩ : syracuseStep 136239 = 204359) B204359
theorem B136423 : Blo 135790 136423 := bstep (se 1 (by rfl) ⟨102317, by rfl⟩ : syracuseStep 136423 = 204635) B204635
theorem B136575 : Blo 135790 136575 := bstep (se 1 (by rfl) ⟨102431, by rfl⟩ : syracuseStep 136575 = 204863) B204863
theorem B136607 : Blo 135790 136607 := bstep (se 1 (by rfl) ⟨102455, by rfl⟩ : syracuseStep 136607 = 204911) B204911
theorem B464615 : Blo 135790 464615 := bstep (se 1 (by rfl) ⟨348461, by rfl⟩ : syracuseStep 464615 = 696923) B696923
theorem B694007 : Blo 135790 694007 := bstep (se 1 (by rfl) ⟨520505, by rfl⟩ : syracuseStep 694007 = 1041011) B1041011
theorem B137127 : Blo 135790 137127 := bstep (se 1 (by rfl) ⟨102845, by rfl⟩ : syracuseStep 137127 = 205691) B205691
theorem B137151 : Blo 135790 137151 := bstep (se 1 (by rfl) ⟨102863, by rfl⟩ : syracuseStep 137151 = 205727) B205727
theorem B235487 : Blo 135790 235487 := bstep (se 1 (by rfl) ⟨176615, by rfl⟩ : syracuseStep 235487 = 353231) B353231
theorem B235561 : Blo 135790 235561 := bstep (se 2 (by rfl) ⟨88335, by rfl⟩ : syracuseStep 235561 = 176671) B176671
theorem B137471 : Blo 135790 137471 := bstep (se 1 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 137471 = 206207) B206207
theorem B137883 : Blo 135790 137883 := bstep (se 1 (by rfl) ⟨103412, by rfl⟩ : syracuseStep 137883 = 206825) B206825
theorem B1809317 : Blo 135790 1809317 := bstep (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) B339247
theorem B1678745 : Blo 135790 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B2661821 : Blo 135790 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B139327 : Blo 135790 139327 := bstep (se 1 (by rfl) ⟨104495, by rfl⟩ : syracuseStep 139327 = 208991) B208991
theorem B139375 : Blo 135790 139375 := bstep (se 1 (by rfl) ⟨104531, by rfl⟩ : syracuseStep 139375 = 209063) B209063
theorem B991379 : Blo 135790 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B467099 : Blo 135790 467099 := bstep (se 1 (by rfl) ⟨350324, by rfl⟩ : syracuseStep 467099 = 700649) B700649
theorem B139487 : Blo 135790 139487 := bstep (se 1 (by rfl) ⟨104615, by rfl⟩ : syracuseStep 139487 = 209231) B209231
theorem B368903 : Blo 135790 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B467453 : Blo 135790 467453 := bstep (se 3 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 467453 = 175295) B175295
theorem B205367 : Blo 135790 205367 := bstep (se 1 (by rfl) ⟨154025, by rfl⟩ : syracuseStep 205367 = 308051) B308051
theorem B467963 : Blo 135790 467963 := bstep (se 1 (by rfl) ⟨350972, by rfl⟩ : syracuseStep 467963 = 701945) B701945
theorem B468071 : Blo 135790 468071 := bstep (se 1 (by rfl) ⟨351053, by rfl⟩ : syracuseStep 468071 = 702107) B702107
theorem B206015 : Blo 135790 206015 := bstep (se 1 (by rfl) ⟨154511, by rfl⟩ : syracuseStep 206015 = 309023) B309023
theorem B468179 : Blo 135790 468179 := bstep (se 1 (by rfl) ⟨351134, by rfl⟩ : syracuseStep 468179 = 702269) B702269
theorem B894347 : Blo 135790 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B3352103 : Blo 135790 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B206399 : Blo 135790 206399 := bstep (se 1 (by rfl) ⟨154799, by rfl⟩ : syracuseStep 206399 = 309599) B309599
theorem B206879 : Blo 135790 206879 := bstep (se 1 (by rfl) ⟨155159, by rfl⟩ : syracuseStep 206879 = 310319) B310319
theorem B206903 : Blo 135790 206903 := bstep (se 1 (by rfl) ⟨155177, by rfl⟩ : syracuseStep 206903 = 310355) B310355
theorem B207311 : Blo 135790 207311 := bstep (se 1 (by rfl) ⟨155483, by rfl⟩ : syracuseStep 207311 = 310967) B310967
theorem B207611 : Blo 135790 207611 := bstep (se 1 (by rfl) ⟨155708, by rfl⟩ : syracuseStep 207611 = 311417) B311417
theorem B469799 : Blo 135790 469799 := bstep (se 1 (by rfl) ⟨352349, by rfl⟩ : syracuseStep 469799 = 704699) B704699
theorem B306017 : Blo 135790 306017 := bstep (se 2 (by rfl) ⟨114756, by rfl⟩ : syracuseStep 306017 = 229513) B229513
theorem B371585 : Blo 135790 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B207977 : Blo 135790 207977 := bstep (se 2 (by rfl) ⟨77991, by rfl⟩ : syracuseStep 207977 = 155983) B155983
theorem B306287 : Blo 135790 306287 := bstep (se 1 (by rfl) ⟨229715, by rfl⟩ : syracuseStep 306287 = 459431) B459431
theorem B306503 : Blo 135790 306503 := bstep (se 1 (by rfl) ⟨229877, by rfl⟩ : syracuseStep 306503 = 459755) B459755
theorem B208199 : Blo 135790 208199 := bstep (se 1 (by rfl) ⟨156149, by rfl⟩ : syracuseStep 208199 = 312299) B312299
theorem B3124939 : Blo 135790 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B208871 : Blo 135790 208871 := bstep (se 1 (by rfl) ⟨156653, by rfl⟩ : syracuseStep 208871 = 313307) B313307
theorem B208943 : Blo 135790 208943 := bstep (se 1 (by rfl) ⟨156707, by rfl⟩ : syracuseStep 208943 = 313415) B313415
theorem B208967 : Blo 135790 208967 := bstep (se 1 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 208967 = 313451) B313451
theorem B209051 : Blo 135790 209051 := bstep (se 1 (by rfl) ⟨156788, by rfl⟩ : syracuseStep 209051 = 313577) B313577
theorem B307817 : Blo 135790 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B2143739 : Blo 135790 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B308843 : Blo 135790 308843 := bstep (se 1 (by rfl) ⟨231632, by rfl⟩ : syracuseStep 308843 = 463265) B463265
theorem B703241 : Blo 135790 703241 := bstep (se 2 (by rfl) ⟨263715, by rfl⟩ : syracuseStep 703241 = 527431) B527431
theorem B244703 : Blo 135790 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B3554705 : Blo 135790 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B704135 : Blo 135790 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B311615 : Blo 135790 311615 := bstep (se 1 (by rfl) ⟨233711, by rfl⟩ : syracuseStep 311615 = 467423) B467423
theorem B836185 : Blo 135790 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B13452101 : Blo 135790 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B443369 : Blo 135790 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B443483 : Blo 135790 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B705671 : Blo 135790 705671 := bstep (se 1 (by rfl) ⟨529253, by rfl⟩ : syracuseStep 705671 = 1058507) B1058507
theorem B345343 : Blo 135790 345343 := bstep (se 1 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 345343 = 518015) B518015
theorem B444457 : Blo 135790 444457 := bstep (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) B333343
theorem B5359823 : Blo 135790 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B707291 : Blo 135790 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B1821635 : Blo 135790 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B314459 : Blo 135790 314459 := bstep (se 1 (by rfl) ⟨235844, by rfl⟩ : syracuseStep 314459 = 471689) B471689
theorem B347935 : Blo 135790 347935 := bstep (se 1 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 347935 = 521903) B521903
theorem B774359 : Blo 135790 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B348907 : Blo 135790 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B1268141 : Blo 135790 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B1203335 : Blo 135790 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B777707 : Blo 135790 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B515767 : Blo 135790 515767 := bstep (se 1 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 515767 = 773651) B773651
theorem B516041 : Blo 135790 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B1958255 : Blo 135790 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B3400393 : Blo 135790 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B517211 : Blo 135790 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B353555 : Blo 135790 353555 := bstep (se 1 (by rfl) ⟨265166, by rfl⟩ : syracuseStep 353555 = 530333) B530333
theorem B156955 : Blo 135790 156955 := bstep (se 1 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 156955 = 235433) B235433
theorem B583145 : Blo 135790 583145 := bstep (se 2 (by rfl) ⟨218679, by rfl⟩ : syracuseStep 583145 = 437359) B437359
theorem B1959461 : Blo 135790 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B5891869 : Blo 135790 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B322343 : Blo 135790 322343 := bstep (se 1 (by rfl) ⟨241757, by rfl⟩ : syracuseStep 322343 = 483515) B483515
theorem B8612851 : Blo 135790 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B552577 : Blo 135790 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B749287 : Blo 135790 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B258871 : Blo 135790 258871 := bstep (se 1 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 258871 = 388307) B388307
theorem B521099 : Blo 135790 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B1045871 : Blo 135790 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B3569183 : Blo 135790 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B849959 : Blo 135790 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B260435 : Blo 135790 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B260891 : Blo 135790 260891 := bstep (se 1 (by rfl) ⟨195668, by rfl⟩ : syracuseStep 260891 = 391337) B391337
theorem B195691 : Blo 135790 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B883943 : Blo 135790 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B524029 : Blo 135790 524029 := bstep (se 3 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 524029 = 196511) B196511
theorem B295579 : Blo 135790 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B295655 : Blo 135790 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B1114913 : Blo 135790 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B460187 : Blo 135790 460187 := bstep (se 1 (by rfl) ⟨345140, by rfl⟩ : syracuseStep 460187 = 690281) B690281
theorem B3573215 : Blo 135790 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B460457 : Blo 135790 460457 := bstep (se 2 (by rfl) ⟨172671, by rfl⟩ : syracuseStep 460457 = 345343) B345343
theorem B1214423 : Blo 135790 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B592609 : Blo 135790 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B658691 : Blo 135790 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B462671 : Blo 135790 462671 := bstep (se 1 (by rfl) ⟨347003, by rfl⟩ : syracuseStep 462671 = 694007) B694007
theorem B398249 : Blo 135790 398249 := bstep (se 2 (by rfl) ⟨149343, by rfl⟩ : syracuseStep 398249 = 298687) B298687
theorem B4166585 : Blo 135790 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1774547 : Blo 135790 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B463913 : Blo 135790 463913 := bstep (se 2 (by rfl) ⟨173967, by rfl⟩ : syracuseStep 463913 = 347935) B347935
theorem B660919 : Blo 135790 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B136911 : Blo 135790 136911 := bstep (se 1 (by rfl) ⟨102683, by rfl⟩ : syracuseStep 136911 = 205367) B205367
theorem B137343 : Blo 135790 137343 := bstep (se 1 (by rfl) ⟨103007, by rfl⟩ : syracuseStep 137343 = 206015) B206015
theorem B235703 : Blo 135790 235703 := bstep (se 1 (by rfl) ⟨176777, by rfl⟩ : syracuseStep 235703 = 353555) B353555
theorem B694493 : Blo 135790 694493 := bstep (se 3 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 694493 = 260435) B260435
theorem B596231 : Blo 135790 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B465209 : Blo 135790 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B2234735 : Blo 135790 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B137599 : Blo 135790 137599 := bstep (se 1 (by rfl) ⟨103199, by rfl⟩ : syracuseStep 137599 = 206399) B206399
theorem B137919 : Blo 135790 137919 := bstep (se 1 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 137919 = 206879) B206879
theorem B137935 : Blo 135790 137935 := bstep (se 1 (by rfl) ⟨103451, by rfl⟩ : syracuseStep 137935 = 206903) B206903
theorem B138207 : Blo 135790 138207 := bstep (se 1 (by rfl) ⟨103655, by rfl⟩ : syracuseStep 138207 = 207311) B207311
theorem B138407 : Blo 135790 138407 := bstep (se 1 (by rfl) ⟨103805, by rfl⟩ : syracuseStep 138407 = 207611) B207611
theorem B204011 : Blo 135790 204011 := bstep (se 1 (by rfl) ⟨153008, by rfl⟩ : syracuseStep 204011 = 306017) B306017
theorem B138651 : Blo 135790 138651 := bstep (se 1 (by rfl) ⟨103988, by rfl⟩ : syracuseStep 138651 = 207977) B207977
theorem B204191 : Blo 135790 204191 := bstep (se 1 (by rfl) ⟨153143, by rfl⟩ : syracuseStep 204191 = 306287) B306287
theorem B204335 : Blo 135790 204335 := bstep (se 1 (by rfl) ⟨153251, by rfl⟩ : syracuseStep 204335 = 306503) B306503
theorem B138799 : Blo 135790 138799 := bstep (se 1 (by rfl) ⟨104099, by rfl⟩ : syracuseStep 138799 = 208199) B208199
theorem B990893 : Blo 135790 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B139247 : Blo 135790 139247 := bstep (se 1 (by rfl) ⟨104435, by rfl⟩ : syracuseStep 139247 = 208871) B208871
theorem B139295 : Blo 135790 139295 := bstep (se 1 (by rfl) ⟨104471, by rfl⟩ : syracuseStep 139295 = 208943) B208943
theorem B139311 : Blo 135790 139311 := bstep (se 1 (by rfl) ⟨104483, by rfl⟩ : syracuseStep 139311 = 208967) B208967
theorem B139367 : Blo 135790 139367 := bstep (se 1 (by rfl) ⟨104525, by rfl⟩ : syracuseStep 139367 = 209051) B209051
theorem B205211 : Blo 135790 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B697247 : Blo 135790 697247 := bstep (se 1 (by rfl) ⟨522935, by rfl⟩ : syracuseStep 697247 = 1045871) B1045871
theorem B205895 : Blo 135790 205895 := bstep (se 1 (by rfl) ⟨154421, by rfl⟩ : syracuseStep 205895 = 308843) B308843
theorem B566639 : Blo 135790 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B468827 : Blo 135790 468827 := bstep (se 1 (by rfl) ⟨351620, by rfl⟩ : syracuseStep 468827 = 703241) B703241
theorem B173927 : Blo 135790 173927 := bstep (se 1 (by rfl) ⟨130445, by rfl⟩ : syracuseStep 173927 = 260891) B260891
theorem B2369803 : Blo 135790 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B698705 : Blo 135790 698705 := bstep (se 2 (by rfl) ⟨262014, by rfl⟩ : syracuseStep 698705 = 524029) B524029
theorem B469423 : Blo 135790 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B207743 : Blo 135790 207743 := bstep (se 1 (by rfl) ⟨155807, by rfl⟩ : syracuseStep 207743 = 311615) B311615
theorem B175279 : Blo 135790 175279 := bstep (se 1 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 175279 = 262919) B262919
theorem B306431 : Blo 135790 306431 := bstep (se 1 (by rfl) ⟨229823, by rfl⟩ : syracuseStep 306431 = 459647) B459647
theorem B470447 : Blo 135790 470447 := bstep (se 1 (by rfl) ⟨352835, by rfl⟩ : syracuseStep 470447 = 705671) B705671
theorem B4533857 : Blo 135790 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B209273 : Blo 135790 209273 := bstep (se 2 (by rfl) ⟨78477, by rfl⟩ : syracuseStep 209273 = 156955) B156955
theorem B471527 : Blo 135790 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B963199 : Blo 135790 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B307943 : Blo 135790 307943 := bstep (se 1 (by rfl) ⟨230957, by rfl⟩ : syracuseStep 307943 = 461915) B461915
theorem B209639 : Blo 135790 209639 := bstep (se 1 (by rfl) ⟨157229, by rfl⟩ : syracuseStep 209639 = 314459) B314459
theorem B72790811 : Blo 135790 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B308159 : Blo 135790 308159 := bstep (se 1 (by rfl) ⟨231119, by rfl⟩ : syracuseStep 308159 = 462239) B462239
theorem B308393 : Blo 135790 308393 := bstep (se 2 (by rfl) ⟨115647, by rfl⟩ : syracuseStep 308393 = 231295) B231295
theorem B439577 : Blo 135790 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B309113 : Blo 135790 309113 := bstep (se 2 (by rfl) ⟨115917, by rfl⟩ : syracuseStep 309113 = 231835) B231835
theorem B309743 : Blo 135790 309743 := bstep (se 1 (by rfl) ⟨232307, by rfl⟩ : syracuseStep 309743 = 464615) B464615
theorem B11483801 : Blo 135790 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B310265 : Blo 135790 310265 := bstep (se 2 (by rfl) ⟨116349, by rfl⟩ : syracuseStep 310265 = 232699) B232699
theorem B802223 : Blo 135790 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B736769 : Blo 135790 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B999049 : Blo 135790 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B344027 : Blo 135790 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B311399 : Blo 135790 311399 := bstep (se 1 (by rfl) ⟨233549, by rfl⟩ : syracuseStep 311399 = 467099) B467099
theorem B245935 : Blo 135790 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B311635 : Blo 135790 311635 := bstep (se 1 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 311635 = 467453) B467453
theorem B311975 : Blo 135790 311975 := bstep (se 1 (by rfl) ⟨233981, by rfl⟩ : syracuseStep 311975 = 467963) B467963
theorem B344807 : Blo 135790 344807 := bstep (se 1 (by rfl) ⟨258605, by rfl⟩ : syracuseStep 344807 = 517211) B517211
theorem B312047 : Blo 135790 312047 := bstep (se 1 (by rfl) ⟨234035, by rfl⟩ : syracuseStep 312047 = 468071) B468071
theorem B312119 : Blo 135790 312119 := bstep (se 1 (by rfl) ⟨234089, by rfl⟩ : syracuseStep 312119 = 468179) B468179
theorem B345161 : Blo 135790 345161 := bstep (se 2 (by rfl) ⟨129435, by rfl⟩ : syracuseStep 345161 = 258871) B258871
theorem B705833 : Blo 135790 705833 := bstep (se 2 (by rfl) ⟨264687, by rfl⟩ : syracuseStep 705833 = 529375) B529375
theorem B313199 : Blo 135790 313199 := bstep (se 1 (by rfl) ⟨234899, by rfl⟩ : syracuseStep 313199 = 469799) B469799
theorem B214895 : Blo 135790 214895 := bstep (se 1 (by rfl) ⟨161171, by rfl⟩ : syracuseStep 214895 = 322343) B322343
theorem B314081 : Blo 135790 314081 := bstep (se 2 (by rfl) ⟨117780, by rfl⟩ : syracuseStep 314081 = 235561) B235561
theorem B347399 : Blo 135790 347399 := bstep (se 1 (by rfl) ⟨260549, by rfl⟩ : syracuseStep 347399 = 521099) B521099
theorem B1429159 : Blo 135790 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B2379455 : Blo 135790 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B4476653 : Blo 135790 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B349991 : Blo 135790 349991 := bstep (se 1 (by rfl) ⟨262493, by rfl⟩ : syracuseStep 349991 = 524987) B524987
theorem B8968067 : Blo 135790 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B415855 : Blo 135790 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B154111 : Blo 135790 154111 := bstep (se 1 (by rfl) ⟨115583, by rfl⟩ : syracuseStep 154111 = 231167) B231167
theorem B351287 : Blo 135790 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B351935 : Blo 135790 351935 := bstep (se 1 (by rfl) ⟨263951, by rfl⟩ : syracuseStep 351935 = 527903) B527903
theorem B7855825 : Blo 135790 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B352097 : Blo 135790 352097 := bstep (se 2 (by rfl) ⟨132036, by rfl⟩ : syracuseStep 352097 = 264073) B264073
theorem B352127 : Blo 135790 352127 := bstep (se 1 (by rfl) ⟨264095, by rfl⟩ : syracuseStep 352127 = 528191) B528191
theorem B516239 : Blo 135790 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B156991 : Blo 135790 156991 := bstep (se 1 (by rfl) ⟨117743, by rfl⟩ : syracuseStep 156991 = 235487) B235487
theorem B13526837 : Blo 135790 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B1206211 : Blo 135790 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B518471 : Blo 135790 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B1305503 : Blo 135790 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B388763 : Blo 135790 388763 := bstep (se 1 (by rfl) ⟨291572, by rfl⟩ : syracuseStep 388763 = 583145) B583145
theorem B1306307 : Blo 135790 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B260921 : Blo 135790 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B163135 : Blo 135790 163135 := bstep (se 1 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 163135 = 244703) B244703
theorem B589295 : Blo 135790 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B687689 : Blo 135790 687689 := bstep (se 2 (by rfl) ⟨257883, by rfl⟩ : syracuseStep 687689 = 515767) B515767
theorem B229871 : Blo 135790 229871 := bstep (se 1 (by rfl) ⟨172403, by rfl⟩ : syracuseStep 229871 = 344807) B344807
theorem B230107 : Blo 135790 230107 := bstep (se 1 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 230107 = 345161) B345161
theorem B394105 : Blo 135790 394105 := bstep (se 2 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 394105 = 295579) B295579
theorem B1311653 : Blo 135790 1311653 := bstep (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) B245935
theorem B788413 : Blo 135790 788413 := bstep (se 3 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 788413 = 295655) B295655
theorem B231599 : Blo 135790 231599 := bstep (se 1 (by rfl) ⟨173699, by rfl⟩ : syracuseStep 231599 = 347399) B347399
theorem B2984435 : Blo 135790 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B1608281 : Blo 135790 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B625897 : Blo 135790 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B265499 : Blo 135790 265499 := bstep (se 1 (by rfl) ⟨199124, by rfl⟩ : syracuseStep 265499 = 398249) B398249
theorem B1183031 : Blo 135790 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B790145 : Blo 135790 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B233327 : Blo 135790 233327 := bstep (se 1 (by rfl) ⟨174995, by rfl⟩ : syracuseStep 233327 = 349991) B349991
theorem B462995 : Blo 135790 462995 := bstep (se 1 (by rfl) ⟨347246, by rfl⟩ : syracuseStep 462995 = 694493) B694493
theorem B397487 : Blo 135790 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B233705 : Blo 135790 233705 := bstep (se 2 (by rfl) ⟨87639, by rfl⟩ : syracuseStep 233705 = 175279) B175279
theorem B234191 : Blo 135790 234191 := bstep (se 1 (by rfl) ⟨175643, by rfl⟩ : syracuseStep 234191 = 351287) B351287
theorem B136007 : Blo 135790 136007 := bstep (se 1 (by rfl) ⟨102005, by rfl⟩ : syracuseStep 136007 = 204011) B204011
theorem B1905545 : Blo 135790 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B463805 : Blo 135790 463805 := bstep (se 3 (by rfl) ⟨86963, by rfl⟩ : syracuseStep 463805 = 173927) B173927
theorem B136127 : Blo 135790 136127 := bstep (se 1 (by rfl) ⟨102095, by rfl⟩ : syracuseStep 136127 = 204191) B204191
theorem B136223 : Blo 135790 136223 := bstep (se 1 (by rfl) ⟨102167, by rfl⟩ : syracuseStep 136223 = 204335) B204335
theorem B660595 : Blo 135790 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B234623 : Blo 135790 234623 := bstep (se 1 (by rfl) ⟨175967, by rfl⟩ : syracuseStep 234623 = 351935) B351935
theorem B234731 : Blo 135790 234731 := bstep (se 1 (by rfl) ⟨176048, by rfl⟩ : syracuseStep 234731 = 352097) B352097
theorem B234751 : Blo 135790 234751 := bstep (se 1 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 234751 = 352127) B352127
theorem B136807 : Blo 135790 136807 := bstep (se 1 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 136807 = 205211) B205211
theorem B464831 : Blo 135790 464831 := bstep (se 1 (by rfl) ⟨348623, by rfl⟩ : syracuseStep 464831 = 697247) B697247
theorem B137263 : Blo 135790 137263 := bstep (se 1 (by rfl) ⟨102947, by rfl⟩ : syracuseStep 137263 = 205895) B205895
theorem B1284265 : Blo 135790 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B9017891 : Blo 135790 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B465803 : Blo 135790 465803 := bstep (se 1 (by rfl) ⟨349352, by rfl⟩ : syracuseStep 465803 = 698705) B698705
theorem B138495 : Blo 135790 138495 := bstep (se 1 (by rfl) ⟨103871, by rfl⟩ : syracuseStep 138495 = 207743) B207743
theorem B695789 : Blo 135790 695789 := bstep (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) B260921
theorem B204287 : Blo 135790 204287 := bstep (se 1 (by rfl) ⟨153215, by rfl⟩ : syracuseStep 204287 = 306431) B306431
theorem B3022571 : Blo 135790 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B139515 : Blo 135790 139515 := bstep (se 1 (by rfl) ⟨104636, by rfl⟩ : syracuseStep 139515 = 209273) B209273
theorem B205295 : Blo 135790 205295 := bstep (se 1 (by rfl) ⟨153971, by rfl⟩ : syracuseStep 205295 = 307943) B307943
theorem B139759 : Blo 135790 139759 := bstep (se 1 (by rfl) ⟨104819, by rfl⟩ : syracuseStep 139759 = 209639) B209639
theorem B205439 : Blo 135790 205439 := bstep (se 1 (by rfl) ⟨154079, by rfl⟩ : syracuseStep 205439 = 308159) B308159
theorem B205481 : Blo 135790 205481 := bstep (se 2 (by rfl) ⟨77055, by rfl⟩ : syracuseStep 205481 = 154111) B154111
theorem B205595 : Blo 135790 205595 := bstep (se 1 (by rfl) ⟨154196, by rfl⟩ : syracuseStep 205595 = 308393) B308393
theorem B206075 : Blo 135790 206075 := bstep (se 1 (by rfl) ⟨154556, by rfl⟩ : syracuseStep 206075 = 309113) B309113
theorem B206495 : Blo 135790 206495 := bstep (se 1 (by rfl) ⟨154871, by rfl⟩ : syracuseStep 206495 = 309743) B309743
theorem B206843 : Blo 135790 206843 := bstep (se 1 (by rfl) ⟨155132, by rfl⟩ : syracuseStep 206843 = 310265) B310265
theorem B534815 : Blo 135790 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B207599 : Blo 135790 207599 := bstep (se 1 (by rfl) ⟨155699, by rfl⟩ : syracuseStep 207599 = 311399) B311399
theorem B207983 : Blo 135790 207983 := bstep (se 1 (by rfl) ⟨155987, by rfl⟩ : syracuseStep 207983 = 311975) B311975
theorem B208031 : Blo 135790 208031 := bstep (se 1 (by rfl) ⟨156023, by rfl⟩ : syracuseStep 208031 = 312047) B312047
theorem B208079 : Blo 135790 208079 := bstep (se 1 (by rfl) ⟨156059, by rfl⟩ : syracuseStep 208079 = 312119) B312119
theorem B470555 : Blo 135790 470555 := bstep (se 1 (by rfl) ⟨352916, by rfl⟩ : syracuseStep 470555 = 705833) B705833
theorem B306791 : Blo 135790 306791 := bstep (se 1 (by rfl) ⟨230093, by rfl⟩ : syracuseStep 306791 = 460187) B460187
theorem B306971 : Blo 135790 306971 := bstep (se 1 (by rfl) ⟨230228, by rfl⟩ : syracuseStep 306971 = 460457) B460457
theorem B208799 : Blo 135790 208799 := bstep (se 1 (by rfl) ⟨156599, by rfl⟩ : syracuseStep 208799 = 313199) B313199
theorem B209321 : Blo 135790 209321 := bstep (se 2 (by rfl) ⟨78495, by rfl⟩ : syracuseStep 209321 = 156991) B156991
theorem B209387 : Blo 135790 209387 := bstep (se 1 (by rfl) ⟨157040, by rfl⟩ : syracuseStep 209387 = 314081) B314081
theorem B439127 : Blo 135790 439127 := bstep (se 1 (by rfl) ⟨329345, by rfl⟩ : syracuseStep 439127 = 658691) B658691
theorem B1586303 : Blo 135790 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B308447 : Blo 135790 308447 := bstep (se 1 (by rfl) ⟨231335, by rfl⟩ : syracuseStep 308447 = 462671) B462671
theorem B3159737 : Blo 135790 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B309275 : Blo 135790 309275 := bstep (se 1 (by rfl) ⟨231956, by rfl⟩ : syracuseStep 309275 = 463913) B463913
theorem B5978711 : Blo 135790 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B310139 : Blo 135790 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B1489823 : Blo 135790 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B573053 : Blo 135790 573053 := bstep (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) B214895
theorem B344159 : Blo 135790 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B377759 : Blo 135790 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B312551 : Blo 135790 312551 := bstep (se 1 (by rfl) ⟨234413, by rfl⟩ : syracuseStep 312551 = 468827) B468827
theorem B345647 : Blo 135790 345647 := bstep (se 1 (by rfl) ⟨259235, by rfl⟩ : syracuseStep 345647 = 518471) B518471
theorem B870335 : Blo 135790 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B313631 : Blo 135790 313631 := bstep (se 1 (by rfl) ⟨235223, by rfl⟩ : syracuseStep 313631 = 470447) B470447
theorem B870871 : Blo 135790 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B314351 : Blo 135790 314351 := bstep (se 1 (by rfl) ⟨235763, by rfl⟩ : syracuseStep 314351 = 471527) B471527
theorem B217513 : Blo 135790 217513 := bstep (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) B163135
theorem B7655867 : Blo 135790 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B1332065 : Blo 135790 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B10474433 : Blo 135790 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B415513 : Blo 135790 415513 := bstep (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) B311635
theorem B743275 : Blo 135790 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B2382143 : Blo 135790 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B809615 : Blo 135790 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B2777723 : Blo 135790 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B157135 : Blo 135790 157135 := bstep (se 1 (by rfl) ⟨117851, by rfl⟩ : syracuseStep 157135 = 235703) B235703
theorem B881225 : Blo 135790 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B259175 : Blo 135790 259175 := bstep (se 1 (by rfl) ⟨194381, by rfl⟩ : syracuseStep 259175 = 388763) B388763
theorem B554473 : Blo 135790 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B48527207 : Blo 135790 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B293051 : Blo 135790 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B392863 : Blo 135790 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B491179 : Blo 135790 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B458459 : Blo 135790 458459 := bstep (se 1 (by rfl) ⟨343844, by rfl⟩ : syracuseStep 458459 = 687689) B687689
theorem B229351 : Blo 135790 229351 := bstep (se 1 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 229351 = 344027) B344027
theorem B229439 : Blo 135790 229439 := bstep (se 1 (by rfl) ⟨172079, by rfl⟩ : syracuseStep 229439 = 344159) B344159
theorem B230431 : Blo 135790 230431 := bstep (se 1 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 230431 = 345647) B345647
theorem B525473 : Blo 135790 525473 := bstep (se 2 (by rfl) ⟨197052, by rfl⟩ : syracuseStep 525473 = 394105) B394105
theorem B788687 : Blo 135790 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B526763 : Blo 135790 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B1051217 : Blo 135790 1051217 := bstep (se 2 (by rfl) ⟨394206, by rfl⟩ : syracuseStep 1051217 = 788413) B788413
theorem B888043 : Blo 135790 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B6982955 : Blo 135790 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B463859 : Blo 135790 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B136191 : Blo 135790 136191 := bstep (se 1 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 136191 = 204287) B204287
theorem B136863 : Blo 135790 136863 := bstep (se 1 (by rfl) ⟨102647, by rfl⟩ : syracuseStep 136863 = 205295) B205295
theorem B136959 : Blo 135790 136959 := bstep (se 1 (by rfl) ⟨102719, by rfl⟩ : syracuseStep 136959 = 205439) B205439
theorem B136987 : Blo 135790 136987 := bstep (se 1 (by rfl) ⟨102740, by rfl⟩ : syracuseStep 136987 = 205481) B205481
theorem B137063 : Blo 135790 137063 := bstep (se 1 (by rfl) ⟨102797, by rfl⟩ : syracuseStep 137063 = 205595) B205595
theorem B137383 : Blo 135790 137383 := bstep (se 1 (by rfl) ⟨103037, by rfl⟩ : syracuseStep 137383 = 206075) B206075
theorem B137663 : Blo 135790 137663 := bstep (se 1 (by rfl) ⟨103247, by rfl⟩ : syracuseStep 137663 = 206495) B206495
theorem B137895 : Blo 135790 137895 := bstep (se 1 (by rfl) ⟨103421, by rfl⟩ : syracuseStep 137895 = 206843) B206843
theorem B138399 : Blo 135790 138399 := bstep (se 1 (by rfl) ⟨103799, by rfl⟩ : syracuseStep 138399 = 207599) B207599
theorem B138655 : Blo 135790 138655 := bstep (se 1 (by rfl) ⟨103991, by rfl⟩ : syracuseStep 138655 = 207983) B207983
theorem B138687 : Blo 135790 138687 := bstep (se 1 (by rfl) ⟨104015, by rfl⟩ : syracuseStep 138687 = 208031) B208031
theorem B138719 : Blo 135790 138719 := bstep (se 1 (by rfl) ⟨104039, by rfl⟩ : syracuseStep 138719 = 208079) B208079
theorem B204527 : Blo 135790 204527 := bstep (se 1 (by rfl) ⟨153395, by rfl⟩ : syracuseStep 204527 = 306791) B306791
theorem B991033 : Blo 135790 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B204647 : Blo 135790 204647 := bstep (se 1 (by rfl) ⟨153485, by rfl⟩ : syracuseStep 204647 = 306971) B306971
theorem B139199 : Blo 135790 139199 := bstep (se 1 (by rfl) ⟨104399, by rfl⟩ : syracuseStep 139199 = 208799) B208799
theorem B1712353 : Blo 135790 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B139547 : Blo 135790 139547 := bstep (se 1 (by rfl) ⟨104660, by rfl⟩ : syracuseStep 139547 = 209321) B209321
theorem B139591 : Blo 135790 139591 := bstep (se 1 (by rfl) ⟨104693, by rfl⟩ : syracuseStep 139591 = 209387) B209387
theorem B172783 : Blo 135790 172783 := bstep (se 1 (by rfl) ⟨129587, by rfl⟩ : syracuseStep 172783 = 259175) B259175
theorem B1057535 : Blo 135790 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B205631 : Blo 135790 205631 := bstep (se 1 (by rfl) ⟨154223, by rfl⟩ : syracuseStep 205631 = 308447) B308447
theorem B2106491 : Blo 135790 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B32351471 : Blo 135790 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B206183 : Blo 135790 206183 := bstep (se 1 (by rfl) ⟨154637, by rfl⟩ : syracuseStep 206183 = 309275) B309275
theorem B206759 : Blo 135790 206759 := bstep (se 1 (by rfl) ⟨155069, by rfl⟩ : syracuseStep 206759 = 310139) B310139
theorem B993215 : Blo 135790 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B305639 : Blo 135790 305639 := bstep (se 1 (by rfl) ⟨229229, by rfl⟩ : syracuseStep 305639 = 458459) B458459
theorem B305801 : Blo 135790 305801 := bstep (se 2 (by rfl) ⟨114675, by rfl⟩ : syracuseStep 305801 = 229351) B229351
theorem B1059965 : Blo 135790 1059965 := bstep (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) B397487
theorem B208367 : Blo 135790 208367 := bstep (se 1 (by rfl) ⟨156275, by rfl⟩ : syracuseStep 208367 = 312551) B312551
theorem B306809 : Blo 135790 306809 := bstep (se 2 (by rfl) ⟨115053, by rfl⟩ : syracuseStep 306809 = 230107) B230107
theorem B209087 : Blo 135790 209087 := bstep (se 1 (by rfl) ⟨156815, by rfl⟩ : syracuseStep 209087 = 313631) B313631
theorem B209513 : Blo 135790 209513 := bstep (se 2 (by rfl) ⟨78567, by rfl⟩ : syracuseStep 209513 = 157135) B157135
theorem B209567 : Blo 135790 209567 := bstep (se 1 (by rfl) ⟨157175, by rfl⟩ : syracuseStep 209567 = 314351) B314351
theorem B176999 : Blo 135790 176999 := bstep (se 1 (by rfl) ⟨132749, by rfl⟩ : syracuseStep 176999 = 265499) B265499
theorem B308663 : Blo 135790 308663 := bstep (se 1 (by rfl) ⟨231497, by rfl⟩ : syracuseStep 308663 = 462995) B462995
theorem B1161161 : Blo 135790 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B309203 : Blo 135790 309203 := bstep (se 1 (by rfl) ⟨231902, by rfl⟩ : syracuseStep 309203 = 463805) B463805
theorem B309887 : Blo 135790 309887 := bstep (se 1 (by rfl) ⟨232415, by rfl⟩ : syracuseStep 309887 = 464831) B464831
theorem B834529 : Blo 135790 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B6011927 : Blo 135790 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B539743 : Blo 135790 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B310535 : Blo 135790 310535 := bstep (se 1 (by rfl) ⟨232901, by rfl⟩ : syracuseStep 310535 = 465803) B465803
theorem B2015047 : Blo 135790 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B1851815 : Blo 135790 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B313001 : Blo 135790 313001 := bstep (se 2 (by rfl) ⟨117375, by rfl⟩ : syracuseStep 313001 = 234751) B234751
theorem B739297 : Blo 135790 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B313703 : Blo 135790 313703 := bstep (se 1 (by rfl) ⟨235277, by rfl⟩ : syracuseStep 313703 = 470555) B470555
theorem B2216069 : Blo 135790 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B1528141 : Blo 135790 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B3985807 : Blo 135790 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B153247 : Blo 135790 153247 := bstep (se 1 (by rfl) ⟨114935, by rfl⟩ : syracuseStep 153247 = 229871) B229871
theorem B251839 : Blo 135790 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B874435 : Blo 135790 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B580223 : Blo 135790 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B154399 : Blo 135790 154399 := bstep (se 1 (by rfl) ⟨115799, by rfl⟩ : syracuseStep 154399 = 231599) B231599
theorem B1989623 : Blo 135790 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1072187 : Blo 135790 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B155551 : Blo 135790 155551 := bstep (se 1 (by rfl) ⟨116663, by rfl⟩ : syracuseStep 155551 = 233327) B233327
theorem B155803 : Blo 135790 155803 := bstep (se 1 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 155803 = 233705) B233705
theorem B5103911 : Blo 135790 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B156127 : Blo 135790 156127 := bstep (se 1 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 156127 = 234191) B234191
theorem B1270363 : Blo 135790 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B156415 : Blo 135790 156415 := bstep (se 1 (by rfl) ⟨117311, by rfl⟩ : syracuseStep 156415 = 234623) B234623
theorem B156487 : Blo 135790 156487 := bstep (se 1 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 156487 = 234731) B234731
theorem B290017 : Blo 135790 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B6352381 : Blo 135790 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B880793 : Blo 135790 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B356543 : Blo 135790 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B587483 : Blo 135790 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B292751 : Blo 135790 292751 := bstep (se 1 (by rfl) ⟨219563, by rfl⟩ : syracuseStep 292751 = 439127) B439127
theorem B195367 : Blo 135790 195367 := bstep (se 1 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 195367 = 293051) B293051
theorem B523817 : Blo 135790 523817 := bstep (se 2 (by rfl) ⟨196431, by rfl⟩ : syracuseStep 523817 = 392863) B392863
theorem B654905 : Blo 135790 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B230377 : Blo 135790 230377 := bstep (se 2 (by rfl) ⟨86391, by rfl⟩ : syracuseStep 230377 = 172783) B172783
theorem B525791 : Blo 135790 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B3803125 : Blo 135790 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B4655303 : Blo 135790 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B985729 : Blo 135790 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B1477379 : Blo 135790 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B1184057 : Blo 135790 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B136351 : Blo 135790 136351 := bstep (se 1 (by rfl) ⟨102263, by rfl⟩ : syracuseStep 136351 = 204527) B204527
theorem B136431 : Blo 135790 136431 := bstep (se 1 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 136431 = 204647) B204647
theorem B2037521 : Blo 135790 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B5314409 : Blo 135790 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B137087 : Blo 135790 137087 := bstep (se 1 (by rfl) ⟨102815, by rfl⟩ : syracuseStep 137087 = 205631) B205631
theorem B21567647 : Blo 135790 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B137455 : Blo 135790 137455 := bstep (se 1 (by rfl) ⟨103091, by rfl⟩ : syracuseStep 137455 = 206183) B206183
theorem B21142037 : Blo 135790 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B137839 : Blo 135790 137839 := bstep (se 1 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 137839 = 206759) B206759
theorem B662143 : Blo 135790 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B203759 : Blo 135790 203759 := bstep (se 1 (by rfl) ⟨152819, by rfl⟩ : syracuseStep 203759 = 305639) B305639
theorem B203867 : Blo 135790 203867 := bstep (se 1 (by rfl) ⟨152900, by rfl⟩ : syracuseStep 203867 = 305801) B305801
theorem B204329 : Blo 135790 204329 := bstep (se 2 (by rfl) ⟨76623, by rfl⟩ : syracuseStep 204329 = 153247) B153247
theorem B138911 : Blo 135790 138911 := bstep (se 1 (by rfl) ⟨104183, by rfl⟩ : syracuseStep 138911 = 208367) B208367
theorem B204539 : Blo 135790 204539 := bstep (se 1 (by rfl) ⟨153404, by rfl⟩ : syracuseStep 204539 = 306809) B306809
theorem B335785 : Blo 135790 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B139391 : Blo 135790 139391 := bstep (se 1 (by rfl) ⟨104543, by rfl⟩ : syracuseStep 139391 = 209087) B209087
theorem B139675 : Blo 135790 139675 := bstep (se 1 (by rfl) ⟨104756, by rfl⟩ : syracuseStep 139675 = 209513) B209513
theorem B139711 : Blo 135790 139711 := bstep (se 1 (by rfl) ⟨104783, by rfl⟩ : syracuseStep 139711 = 209567) B209567
theorem B205775 : Blo 135790 205775 := bstep (se 1 (by rfl) ⟨154331, by rfl⟩ : syracuseStep 205775 = 308663) B308663
theorem B205865 : Blo 135790 205865 := bstep (se 2 (by rfl) ⟨77199, by rfl⟩ : syracuseStep 205865 = 154399) B154399
theorem B206135 : Blo 135790 206135 := bstep (se 1 (by rfl) ⟨154601, by rfl⟩ : syracuseStep 206135 = 309203) B309203
theorem B206591 : Blo 135790 206591 := bstep (se 1 (by rfl) ⟨154943, by rfl⟩ : syracuseStep 206591 = 309887) B309887
theorem B4007951 : Blo 135790 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B207023 : Blo 135790 207023 := bstep (se 1 (by rfl) ⟨155267, by rfl⟩ : syracuseStep 207023 = 310535) B310535
theorem B436603 : Blo 135790 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B207401 : Blo 135790 207401 := bstep (se 2 (by rfl) ⟨77775, by rfl⟩ : syracuseStep 207401 = 155551) B155551
theorem B207737 : Blo 135790 207737 := bstep (se 2 (by rfl) ⟨77901, by rfl⟩ : syracuseStep 207737 = 155803) B155803
theorem B208169 : Blo 135790 208169 := bstep (se 2 (by rfl) ⟨78063, by rfl⟩ : syracuseStep 208169 = 156127) B156127
theorem B208553 : Blo 135790 208553 := bstep (se 2 (by rfl) ⟨78207, by rfl⟩ : syracuseStep 208553 = 156415) B156415
theorem B208649 : Blo 135790 208649 := bstep (se 2 (by rfl) ⟨78243, by rfl⟩ : syracuseStep 208649 = 156487) B156487
theorem B208667 : Blo 135790 208667 := bstep (se 1 (by rfl) ⟨156500, by rfl⟩ : syracuseStep 208667 = 313001) B313001
theorem B307241 : Blo 135790 307241 := bstep (se 2 (by rfl) ⟨115215, by rfl⟩ : syracuseStep 307241 = 230431) B230431
theorem B209135 : Blo 135790 209135 := bstep (se 1 (by rfl) ⟨156851, by rfl⟩ : syracuseStep 209135 = 313703) B313703
theorem B700811 : Blo 135790 700811 := bstep (se 1 (by rfl) ⟨525608, by rfl⟩ : syracuseStep 700811 = 1051217) B1051217
theorem B471997 : Blo 135790 471997 := bstep (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) B176999
theorem B5617309 : Blo 135790 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B309239 : Blo 135790 309239 := bstep (se 1 (by rfl) ⟨231929, by rfl⟩ : syracuseStep 309239 = 463859) B463859
theorem B1326415 : Blo 135790 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B8469841 : Blo 135790 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B705023 : Blo 135790 705023 := bstep (se 1 (by rfl) ⟨528767, by rfl⟩ : syracuseStep 705023 = 1057535) B1057535
theorem B706643 : Blo 135790 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B1165913 : Blo 135790 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B774107 : Blo 135790 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B349211 : Blo 135790 349211 := bstep (se 1 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 349211 = 523817) B523817
theorem B152959 : Blo 135790 152959 := bstep (se 1 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 152959 = 229439) B229439
theorem B1234543 : Blo 135790 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B2283137 : Blo 135790 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B350315 : Blo 135790 350315 := bstep (se 1 (by rfl) ⟨262736, by rfl⟩ : syracuseStep 350315 = 525473) B525473
theorem B1693817 : Blo 135790 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B351175 : Blo 135790 351175 := bstep (se 1 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 351175 = 526763) B526763
theorem B386689 : Blo 135790 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B386815 : Blo 135790 386815 := bstep (se 1 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 386815 = 580223) B580223
theorem B714791 : Blo 135790 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B3402607 : Blo 135790 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B587195 : Blo 135790 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B260489 : Blo 135790 260489 := bstep (se 2 (by rfl) ⟨97683, by rfl⟩ : syracuseStep 260489 = 195367) B195367
theorem B391655 : Blo 135790 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B195167 : Blo 135790 195167 := bstep (se 1 (by rfl) ⟨146375, by rfl⟩ : syracuseStep 195167 = 292751) B292751
theorem B1112705 : Blo 135790 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B719657 : Blo 135790 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B2686729 : Blo 135790 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B789371 : Blo 135790 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B232807 : Blo 135790 232807 := bstep (se 1 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 232807 = 349211) B349211
theorem B1314305 : Blo 135790 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B3542939 : Blo 135790 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B233543 : Blo 135790 233543 := bstep (se 1 (by rfl) ⟨175157, by rfl⟩ : syracuseStep 233543 = 350315) B350315
theorem B14094691 : Blo 135790 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B135839 : Blo 135790 135839 := bstep (se 1 (by rfl) ⟨101879, by rfl⟩ : syracuseStep 135839 = 203759) B203759
theorem B135911 : Blo 135790 135911 := bstep (se 1 (by rfl) ⟨101933, by rfl⟩ : syracuseStep 135911 = 203867) B203867
theorem B136219 : Blo 135790 136219 := bstep (se 1 (by rfl) ⟨102164, by rfl⟩ : syracuseStep 136219 = 204329) B204329
theorem B136359 : Blo 135790 136359 := bstep (se 1 (by rfl) ⟨102269, by rfl⟩ : syracuseStep 136359 = 204539) B204539
theorem B57513725 : Blo 135790 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B137183 : Blo 135790 137183 := bstep (se 1 (by rfl) ⟨102887, by rfl⟩ : syracuseStep 137183 = 205775) B205775
theorem B137243 : Blo 135790 137243 := bstep (se 1 (by rfl) ⟨102932, by rfl⟩ : syracuseStep 137243 = 205865) B205865
theorem B137423 : Blo 135790 137423 := bstep (se 1 (by rfl) ⟨103067, by rfl⟩ : syracuseStep 137423 = 206135) B206135
theorem B137727 : Blo 135790 137727 := bstep (se 1 (by rfl) ⟨103295, by rfl⟩ : syracuseStep 137727 = 206591) B206591
theorem B629329 : Blo 135790 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B138015 : Blo 135790 138015 := bstep (se 1 (by rfl) ⟨103511, by rfl⟩ : syracuseStep 138015 = 207023) B207023
theorem B138267 : Blo 135790 138267 := bstep (se 1 (by rfl) ⟨103700, by rfl⟩ : syracuseStep 138267 = 207401) B207401
theorem B203945 : Blo 135790 203945 := bstep (se 2 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 203945 = 152959) B152959
theorem B138491 : Blo 135790 138491 := bstep (se 1 (by rfl) ⟨103868, by rfl⟩ : syracuseStep 138491 = 207737) B207737
theorem B3939677 : Blo 135790 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B1646057 : Blo 135790 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B138779 : Blo 135790 138779 := bstep (se 1 (by rfl) ⟨104084, by rfl⟩ : syracuseStep 138779 = 208169) B208169
theorem B139035 : Blo 135790 139035 := bstep (se 1 (by rfl) ⟨104276, by rfl⟩ : syracuseStep 139035 = 208553) B208553
theorem B139099 : Blo 135790 139099 := bstep (se 1 (by rfl) ⟨104324, by rfl⟩ : syracuseStep 139099 = 208649) B208649
theorem B139111 : Blo 135790 139111 := bstep (se 1 (by rfl) ⟨104333, by rfl⟩ : syracuseStep 139111 = 208667) B208667
theorem B204827 : Blo 135790 204827 := bstep (se 1 (by rfl) ⟨153620, by rfl⟩ : syracuseStep 204827 = 307241) B307241
theorem B139423 : Blo 135790 139423 := bstep (se 1 (by rfl) ⟨104567, by rfl⟩ : syracuseStep 139423 = 209135) B209135
theorem B467207 : Blo 135790 467207 := bstep (se 1 (by rfl) ⟨350405, by rfl⟩ : syracuseStep 467207 = 700811) B700811
theorem B468233 : Blo 135790 468233 := bstep (se 2 (by rfl) ⟨175587, by rfl⟩ : syracuseStep 468233 = 351175) B351175
theorem B206159 : Blo 135790 206159 := bstep (se 1 (by rfl) ⟨154619, by rfl⟩ : syracuseStep 206159 = 309239) B309239
theorem B173659 : Blo 135790 173659 := bstep (se 1 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 173659 = 260489) B260489
theorem B3582305 : Blo 135790 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B470015 : Blo 135790 470015 := bstep (se 1 (by rfl) ⟨352511, by rfl⟩ : syracuseStep 470015 = 705023) B705023
theorem B307169 : Blo 135790 307169 := bstep (se 2 (by rfl) ⟨115188, by rfl⟩ : syracuseStep 307169 = 230377) B230377
theorem B471095 : Blo 135790 471095 := bstep (se 1 (by rfl) ⟨353321, by rfl⟩ : syracuseStep 471095 = 706643) B706643
theorem B1522091 : Blo 135790 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B4536809 : Blo 135790 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B1129211 : Blo 135790 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B2671967 : Blo 135790 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B476527 : Blo 135790 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B7489745 : Blo 135790 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B741803 : Blo 135790 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B11293121 : Blo 135790 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B479771 : Blo 135790 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B447713 : Blo 135790 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B350527 : Blo 135790 350527 := bstep (se 1 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 350527 = 525791) B525791
theorem B3103535 : Blo 135790 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B777275 : Blo 135790 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B515585 : Blo 135790 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B515753 : Blo 135790 515753 := bstep (se 2 (by rfl) ⟨193407, by rfl⟩ : syracuseStep 515753 = 386815) B386815
theorem B516071 : Blo 135790 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B5070833 : Blo 135790 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B582137 : Blo 135790 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B5433389 : Blo 135790 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B1044413 : Blo 135790 1044413 := bstep (se 3 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 1044413 = 391655) B391655
theorem B520445 : Blo 135790 520445 := bstep (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) B195167
theorem B882857 : Blo 135790 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B391463 : Blo 135790 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B1768553 : Blo 135790 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B75171685 : Blo 135790 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B526247 : Blo 135790 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B231545 : Blo 135790 231545 := bstep (se 2 (by rfl) ⟨86829, by rfl⟩ : syracuseStep 231545 = 173659) B173659
theorem B2361959 : Blo 135790 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B298475 : Blo 135790 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B38342483 : Blo 135790 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B2069023 : Blo 135790 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B135963 : Blo 135790 135963 := bstep (se 1 (by rfl) ⟨101972, by rfl⟩ : syracuseStep 135963 = 203945) B203945
theorem B2626451 : Blo 135790 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B3380555 : Blo 135790 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B136551 : Blo 135790 136551 := bstep (se 1 (by rfl) ⟨102413, by rfl⟩ : syracuseStep 136551 = 204827) B204827
theorem B137439 : Blo 135790 137439 := bstep (se 1 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 137439 = 206159) B206159
theorem B696275 : Blo 135790 696275 := bstep (se 1 (by rfl) ⟨522206, by rfl⟩ : syracuseStep 696275 = 1044413) B1044413
theorem B204779 : Blo 135790 204779 := bstep (se 1 (by rfl) ⟨153584, by rfl⟩ : syracuseStep 204779 = 307169) B307169
theorem B467369 : Blo 135790 467369 := bstep (se 2 (by rfl) ⟨175263, by rfl⟩ : syracuseStep 467369 = 350527) B350527
theorem B3024539 : Blo 135790 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B1781311 : Blo 135790 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B4993163 : Blo 135790 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B635369 : Blo 135790 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B7912565 : Blo 135790 7912565 := bstep (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) B741803
theorem B310409 : Blo 135790 310409 := bstep (se 2 (by rfl) ⟨116403, by rfl⟩ : syracuseStep 310409 = 232807) B232807
theorem B1097371 : Blo 135790 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B343723 : Blo 135790 343723 := bstep (se 1 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 343723 = 515585) B515585
theorem B343835 : Blo 135790 343835 := bstep (se 1 (by rfl) ⟨257876, by rfl⟩ : syracuseStep 343835 = 515753) B515753
theorem B344047 : Blo 135790 344047 := bstep (se 1 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 344047 = 516071) B516071
theorem B311471 : Blo 135790 311471 := bstep (se 1 (by rfl) ⟨233603, by rfl⟩ : syracuseStep 311471 = 467207) B467207
theorem B312155 : Blo 135790 312155 := bstep (se 1 (by rfl) ⟨234116, by rfl⟩ : syracuseStep 312155 = 468233) B468233
theorem B3622259 : Blo 135790 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B313343 : Blo 135790 313343 := bstep (se 1 (by rfl) ⟨235007, by rfl⟩ : syracuseStep 313343 = 470015) B470015
theorem B314063 : Blo 135790 314063 := bstep (se 1 (by rfl) ⟨235547, by rfl⟩ : syracuseStep 314063 = 471095) B471095
theorem B346963 : Blo 135790 346963 := bstep (se 1 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 346963 = 520445) B520445
theorem B839105 : Blo 135790 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B876203 : Blo 135790 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B155695 : Blo 135790 155695 := bstep (se 1 (by rfl) ⟨116771, by rfl⟩ : syracuseStep 155695 = 233543) B233543
theorem B7528747 : Blo 135790 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B319847 : Blo 135790 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B518183 : Blo 135790 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B388091 : Blo 135790 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B2354285 : Blo 135790 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B2388203 : Blo 135790 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B260975 : Blo 135790 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B1014727 : Blo 135790 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B752807 : Blo 135790 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B1179035 : Blo 135790 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B852925 : Blo 135790 852925 := bstep (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) B319847
theorem B1574639 : Blo 135790 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B559403 : Blo 135790 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B198983 : Blo 135790 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B25561655 : Blo 135790 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B462617 : Blo 135790 462617 := bstep (se 2 (by rfl) ⟨173481, by rfl⟩ : syracuseStep 462617 = 346963) B346963
theorem B464183 : Blo 135790 464183 := bstep (se 1 (by rfl) ⟨348137, by rfl⟩ : syracuseStep 464183 = 696275) B696275
theorem B136519 : Blo 135790 136519 := bstep (se 1 (by rfl) ⟨102389, by rfl⟩ : syracuseStep 136519 = 204779) B204779
theorem B2758697 : Blo 135790 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B1352969 : Blo 135790 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B173983 : Blo 135790 173983 := bstep (se 1 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 173983 = 260975) B260975
theorem B206939 : Blo 135790 206939 := bstep (se 1 (by rfl) ⟨155204, by rfl⟩ : syracuseStep 206939 = 310409) B310409
theorem B501871 : Blo 135790 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B207593 : Blo 135790 207593 := bstep (se 2 (by rfl) ⟨77847, by rfl⟩ : syracuseStep 207593 = 155695) B155695
theorem B207647 : Blo 135790 207647 := bstep (se 1 (by rfl) ⟨155735, by rfl⟩ : syracuseStep 207647 = 311471) B311471
theorem B10038329 : Blo 135790 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B208103 : Blo 135790 208103 := bstep (se 1 (by rfl) ⟨156077, by rfl⟩ : syracuseStep 208103 = 312155) B312155
theorem B208895 : Blo 135790 208895 := bstep (se 1 (by rfl) ⟨156671, by rfl⟩ : syracuseStep 208895 = 313343) B313343
theorem B209375 : Blo 135790 209375 := bstep (se 1 (by rfl) ⟨157031, by rfl⟩ : syracuseStep 209375 = 314063) B314063
theorem B1750967 : Blo 135790 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B2375081 : Blo 135790 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B311579 : Blo 135790 311579 := bstep (se 1 (by rfl) ⟨233684, by rfl⟩ : syracuseStep 311579 = 467369) B467369
theorem B2016359 : Blo 135790 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B345455 : Blo 135790 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B3328775 : Blo 135790 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B1592135 : Blo 135790 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B6278093 : Blo 135790 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B5852645 : Blo 135790 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B1694317 : Blo 135790 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B350831 : Blo 135790 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B154363 : Blo 135790 154363 := bstep (se 1 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 154363 = 231545) B231545
theorem B100228913 : Blo 135790 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B2253703 : Blo 135790 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B9659357 : Blo 135790 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B584135 : Blo 135790 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B258727 : Blo 135790 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B5275043 : Blo 135790 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B458297 : Blo 135790 458297 := bstep (se 2 (by rfl) ⟨171861, by rfl⟩ : syracuseStep 458297 = 343723) B343723
theorem B786023 : Blo 135790 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B229223 : Blo 135790 229223 := bstep (se 1 (by rfl) ⟨171917, by rfl⟩ : syracuseStep 229223 = 343835) B343835
theorem B458729 : Blo 135790 458729 := bstep (se 2 (by rfl) ⟨172023, by rfl⟩ : syracuseStep 458729 = 344047) B344047
theorem B1344239 : Blo 135790 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B230303 : Blo 135790 230303 := bstep (se 1 (by rfl) ⟨172727, by rfl⟩ : syracuseStep 230303 = 345455) B345455
theorem B1049759 : Blo 135790 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B17041103 : Blo 135790 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B3901763 : Blo 135790 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B231977 : Blo 135790 231977 := bstep (se 2 (by rfl) ⟨86991, by rfl⟩ : syracuseStep 231977 = 173983) B173983
theorem B1839131 : Blo 135790 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B233887 : Blo 135790 233887 := bstep (se 1 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 233887 = 350831) B350831
theorem B66819275 : Blo 135790 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B530621 : Blo 135790 530621 := bstep (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) B198983
theorem B137959 : Blo 135790 137959 := bstep (se 1 (by rfl) ⟨103469, by rfl⟩ : syracuseStep 137959 = 206939) B206939
theorem B138395 : Blo 135790 138395 := bstep (se 1 (by rfl) ⟨103796, by rfl⟩ : syracuseStep 138395 = 207593) B207593
theorem B138431 : Blo 135790 138431 := bstep (se 1 (by rfl) ⟨103823, by rfl⟩ : syracuseStep 138431 = 207647) B207647
theorem B6692219 : Blo 135790 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B138735 : Blo 135790 138735 := bstep (se 1 (by rfl) ⟨104051, by rfl⟩ : syracuseStep 138735 = 208103) B208103
theorem B139263 : Blo 135790 139263 := bstep (se 1 (by rfl) ⟨104447, by rfl⟩ : syracuseStep 139263 = 208895) B208895
theorem B139583 : Blo 135790 139583 := bstep (se 1 (by rfl) ⟨104687, by rfl⟩ : syracuseStep 139583 = 209375) B209375
theorem B205817 : Blo 135790 205817 := bstep (se 2 (by rfl) ⟨77181, by rfl⟩ : syracuseStep 205817 = 154363) B154363
theorem B3516695 : Blo 135790 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B1583387 : Blo 135790 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B305531 : Blo 135790 305531 := bstep (se 1 (by rfl) ⟨229148, by rfl⟩ : syracuseStep 305531 = 458297) B458297
theorem B305819 : Blo 135790 305819 := bstep (se 1 (by rfl) ⟨229364, by rfl⟩ : syracuseStep 305819 = 458729) B458729
theorem B207719 : Blo 135790 207719 := bstep (se 1 (by rfl) ⟨155789, by rfl⟩ : syracuseStep 207719 = 311579) B311579
theorem B372935 : Blo 135790 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B1061423 : Blo 135790 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B308411 : Blo 135790 308411 := bstep (se 1 (by rfl) ⟨231308, by rfl⟩ : syracuseStep 308411 = 462617) B462617
theorem B669161 : Blo 135790 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B309455 : Blo 135790 309455 := bstep (se 1 (by rfl) ⟨232091, by rfl⟩ : syracuseStep 309455 = 464183) B464183
theorem B6439571 : Blo 135790 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B901979 : Blo 135790 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B344969 : Blo 135790 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B1167311 : Blo 135790 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B152815 : Blo 135790 152815 := bstep (se 1 (by rfl) ⟨114611, by rfl⟩ : syracuseStep 152815 = 229223) B229223
theorem B3004937 : Blo 135790 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B1137233 : Blo 135790 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B2219183 : Blo 135790 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B4185395 : Blo 135790 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B389423 : Blo 135790 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B2259089 : Blo 135790 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B524015 : Blo 135790 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B4293047 : Blo 135790 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B229979 : Blo 135790 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B2003291 : Blo 135790 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B758155 : Blo 135790 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1479455 : Blo 135790 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B2790263 : Blo 135790 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B4461479 : Blo 135790 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B137211 : Blo 135790 137211 := bstep (se 1 (by rfl) ⟨102908, by rfl⟩ : syracuseStep 137211 = 205817) B205817
theorem B1055591 : Blo 135790 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B203687 : Blo 135790 203687 := bstep (se 1 (by rfl) ⟨152765, by rfl⟩ : syracuseStep 203687 = 305531) B305531
theorem B203753 : Blo 135790 203753 := bstep (se 2 (by rfl) ⟨76407, by rfl⟩ : syracuseStep 203753 = 152815) B152815
theorem B203879 : Blo 135790 203879 := bstep (se 1 (by rfl) ⟨152909, by rfl⟩ : syracuseStep 203879 = 305819) B305819
theorem B138479 : Blo 135790 138479 := bstep (se 1 (by rfl) ⟨103859, by rfl⟩ : syracuseStep 138479 = 207719) B207719
theorem B205607 : Blo 135790 205607 := bstep (se 1 (by rfl) ⟨154205, by rfl⟩ : syracuseStep 205607 = 308411) B308411
theorem B206303 : Blo 135790 206303 := bstep (se 1 (by rfl) ⟨154727, by rfl⟩ : syracuseStep 206303 = 309455) B309455
theorem B896159 : Blo 135790 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B994493 : Blo 135790 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B601319 : Blo 135790 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B699839 : Blo 135790 699839 := bstep (se 1 (by rfl) ⟨524879, by rfl⟩ : syracuseStep 699839 = 1049759) B1049759
theorem B2601175 : Blo 135790 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1226087 : Blo 135790 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B44546183 : Blo 135790 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B311849 : Blo 135790 311849 := bstep (se 2 (by rfl) ⟨116943, by rfl⟩ : syracuseStep 311849 = 233887) B233887
theorem B2344463 : Blo 135790 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B707615 : Blo 135790 707615 := bstep (se 1 (by rfl) ⟨530711, by rfl⟩ : syracuseStep 707615 = 1061423) B1061423
theorem B446107 : Blo 135790 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B349343 : Blo 135790 349343 := bstep (se 1 (by rfl) ⟨262007, by rfl⟩ : syracuseStep 349343 = 524015) B524015
theorem B153535 : Blo 135790 153535 := bstep (se 1 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 153535 = 230303) B230303
theorem B11360735 : Blo 135790 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B154651 : Blo 135790 154651 := bstep (se 1 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 154651 = 231977) B231977
theorem B778207 : Blo 135790 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B353747 : Blo 135790 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B259615 : Blo 135790 259615 := bstep (se 1 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 259615 = 389423) B389423
theorem B1506059 : Blo 135790 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B986303 : Blo 135790 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B232895 : Blo 135790 232895 := bstep (se 1 (by rfl) ⟨174671, by rfl⟩ : syracuseStep 232895 = 349343) B349343
theorem B7573823 : Blo 135790 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B135791 : Blo 135790 135791 := bstep (se 1 (by rfl) ⟨101843, by rfl⟩ : syracuseStep 135791 = 203687) B203687
theorem B135835 : Blo 135790 135835 := bstep (se 1 (by rfl) ⟨101876, by rfl⟩ : syracuseStep 135835 = 203753) B203753
theorem B135919 : Blo 135790 135919 := bstep (se 1 (by rfl) ⟨101939, by rfl⟩ : syracuseStep 135919 = 203879) B203879
theorem B594809 : Blo 135790 594809 := bstep (se 2 (by rfl) ⟨223053, by rfl⟩ : syracuseStep 594809 = 446107) B446107
theorem B137071 : Blo 135790 137071 := bstep (se 1 (by rfl) ⟨102803, by rfl⟩ : syracuseStep 137071 = 205607) B205607
theorem B235831 : Blo 135790 235831 := bstep (se 1 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 235831 = 353747) B353747
theorem B137535 : Blo 135790 137535 := bstep (se 1 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 137535 = 206303) B206303
theorem B597439 : Blo 135790 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B662995 : Blo 135790 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B400879 : Blo 135790 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B466559 : Blo 135790 466559 := bstep (se 1 (by rfl) ⟨349919, by rfl⟩ : syracuseStep 466559 = 699839) B699839
theorem B204713 : Blo 135790 204713 := bstep (se 2 (by rfl) ⟨76767, by rfl⟩ : syracuseStep 204713 = 153535) B153535
theorem B206201 : Blo 135790 206201 := bstep (se 2 (by rfl) ⟨77325, by rfl⟩ : syracuseStep 206201 = 154651) B154651
theorem B29697455 : Blo 135790 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B207899 : Blo 135790 207899 := bstep (se 1 (by rfl) ⟨155924, by rfl⟩ : syracuseStep 207899 = 311849) B311849
theorem B11448125 : Blo 135790 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B471743 : Blo 135790 471743 := bstep (se 1 (by rfl) ⟨353807, by rfl⟩ : syracuseStep 471743 = 707615) B707615
theorem B703727 : Blo 135790 703727 := bstep (se 1 (by rfl) ⟨527795, by rfl⟩ : syracuseStep 703727 = 1055591) B1055591
theorem B346153 : Blo 135790 346153 := bstep (se 2 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 346153 = 259615) B259615
theorem B1004039 : Blo 135790 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B1037609 : Blo 135790 1037609 := bstep (se 2 (by rfl) ⟨389103, by rfl⟩ : syracuseStep 1037609 = 778207) B778207
theorem B153319 : Blo 135790 153319 := bstep (se 1 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 153319 = 229979) B229979
theorem B1562975 : Blo 135790 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B1335527 : Blo 135790 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B1860175 : Blo 135790 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B2974319 : Blo 135790 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B3468233 : Blo 135790 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1010873 : Blo 135790 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B817391 : Blo 135790 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B461537 : Blo 135790 461537 := bstep (se 2 (by rfl) ⟨173076, by rfl⟩ : syracuseStep 461537 = 346153) B346153
theorem B5049215 : Blo 135790 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B396539 : Blo 135790 396539 := bstep (se 1 (by rfl) ⟨297404, by rfl⟩ : syracuseStep 396539 = 594809) B594809
theorem B691739 : Blo 135790 691739 := bstep (se 1 (by rfl) ⟨518804, by rfl⟩ : syracuseStep 691739 = 1037609) B1037609
theorem B136475 : Blo 135790 136475 := bstep (se 1 (by rfl) ⟨102356, by rfl⟩ : syracuseStep 136475 = 204713) B204713
theorem B890351 : Blo 135790 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B137467 : Blo 135790 137467 := bstep (se 1 (by rfl) ⟨103100, by rfl⟩ : syracuseStep 137467 = 206201) B206201
theorem B138599 : Blo 135790 138599 := bstep (se 1 (by rfl) ⟨103949, by rfl⟩ : syracuseStep 138599 = 207899) B207899
theorem B204425 : Blo 135790 204425 := bstep (se 2 (by rfl) ⟨76659, by rfl⟩ : syracuseStep 204425 = 153319) B153319
theorem B3186341 : Blo 135790 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B2138021 : Blo 135790 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B2630141 : Blo 135790 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B469151 : Blo 135790 469151 := bstep (se 1 (by rfl) ⟨351863, by rfl⟩ : syracuseStep 469151 = 703727) B703727
theorem B669359 : Blo 135790 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B311039 : Blo 135790 311039 := bstep (se 1 (by rfl) ⟨233279, by rfl⟩ : syracuseStep 311039 = 466559) B466559
theorem B1982879 : Blo 135790 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B2179709 : Blo 135790 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B2312155 : Blo 135790 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B673915 : Blo 135790 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B314441 : Blo 135790 314441 := bstep (se 2 (by rfl) ⟨117915, by rfl⟩ : syracuseStep 314441 = 235831) B235831
theorem B314495 : Blo 135790 314495 := bstep (se 1 (by rfl) ⟨235871, by rfl⟩ : syracuseStep 314495 = 471743) B471743
theorem B2480233 : Blo 135790 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B155263 : Blo 135790 155263 := bstep (se 1 (by rfl) ⟨116447, by rfl⟩ : syracuseStep 155263 = 232895) B232895
theorem B79193213 : Blo 135790 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B1041983 : Blo 135790 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B7632083 : Blo 135790 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B883993 : Blo 135790 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B264359 : Blo 135790 264359 := bstep (se 1 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 264359 = 396539) B396539
theorem B461159 : Blo 135790 461159 := bstep (se 1 (by rfl) ⟨345869, by rfl⟩ : syracuseStep 461159 = 691739) B691739
theorem B3082873 : Blo 135790 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B593567 : Blo 135790 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B136283 : Blo 135790 136283 := bstep (se 1 (by rfl) ⟨102212, by rfl⟩ : syracuseStep 136283 = 204425) B204425
theorem B52795475 : Blo 135790 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B694655 : Blo 135790 694655 := bstep (se 1 (by rfl) ⟨520991, by rfl⟩ : syracuseStep 694655 = 1041983) B1041983
theorem B5088055 : Blo 135790 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B207017 : Blo 135790 207017 := bstep (se 2 (by rfl) ⟨77631, by rfl⟩ : syracuseStep 207017 = 155263) B155263
theorem B207359 : Blo 135790 207359 := bstep (se 1 (by rfl) ⟨155519, by rfl⟩ : syracuseStep 207359 = 311039) B311039
theorem B1321919 : Blo 135790 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B1453139 : Blo 135790 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B307691 : Blo 135790 307691 := bstep (se 1 (by rfl) ⟨230768, by rfl⟩ : syracuseStep 307691 = 461537) B461537
theorem B209627 : Blo 135790 209627 := bstep (se 1 (by rfl) ⟨157220, by rfl⟩ : syracuseStep 209627 = 314441) B314441
theorem B209663 : Blo 135790 209663 := bstep (se 1 (by rfl) ⟨157247, by rfl⟩ : syracuseStep 209663 = 314495) B314495
theorem B898553 : Blo 135790 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B1425347 : Blo 135790 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B1753427 : Blo 135790 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B312767 : Blo 135790 312767 := bstep (se 1 (by rfl) ⟨234575, by rfl⟩ : syracuseStep 312767 = 469151) B469151
theorem B446239 : Blo 135790 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B3366143 : Blo 135790 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B2124227 : Blo 135790 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B3306977 : Blo 135790 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B1178657 : Blo 135790 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B6784073 : Blo 135790 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B395711 : Blo 135790 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B2396141 : Blo 135790 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B35196983 : Blo 135790 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B463103 : Blo 135790 463103 := bstep (se 1 (by rfl) ⟨347327, by rfl⟩ : syracuseStep 463103 = 694655) B694655
theorem B594985 : Blo 135790 594985 := bstep (se 2 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 594985 = 446239) B446239
theorem B138011 : Blo 135790 138011 := bstep (se 1 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 138011 = 207017) B207017
theorem B1416151 : Blo 135790 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B138239 : Blo 135790 138239 := bstep (se 1 (by rfl) ⟨103679, by rfl⟩ : syracuseStep 138239 = 207359) B207359
theorem B205127 : Blo 135790 205127 := bstep (se 1 (by rfl) ⟨153845, by rfl⟩ : syracuseStep 205127 = 307691) B307691
theorem B139751 : Blo 135790 139751 := bstep (se 1 (by rfl) ⟨104813, by rfl⟩ : syracuseStep 139751 = 209627) B209627
theorem B139775 : Blo 135790 139775 := bstep (se 1 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 139775 = 209663) B209663
theorem B2204651 : Blo 135790 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B208511 : Blo 135790 208511 := bstep (se 1 (by rfl) ⟨156383, by rfl⟩ : syracuseStep 208511 = 312767) B312767
theorem B176239 : Blo 135790 176239 := bstep (se 1 (by rfl) ⟨132179, by rfl⟩ : syracuseStep 176239 = 264359) B264359
theorem B307439 : Blo 135790 307439 := bstep (se 1 (by rfl) ⟨230579, by rfl⟩ : syracuseStep 307439 = 461159) B461159
theorem B4110497 : Blo 135790 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2244095 : Blo 135790 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B968759 : Blo 135790 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B1168951 : Blo 135790 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B881279 : Blo 135790 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B785771 : Blo 135790 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B950231 : Blo 135790 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B4522715 : Blo 135790 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B263807 : Blo 135790 263807 := bstep (se 1 (by rfl) ⟨197855, by rfl⟩ : syracuseStep 263807 = 395711) B395711
theorem B23464655 : Blo 135790 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B136751 : Blo 135790 136751 := bstep (se 1 (by rfl) ⟨102563, by rfl⟩ : syracuseStep 136751 = 205127) B205127
theorem B793313 : Blo 135790 793313 := bstep (se 2 (by rfl) ⟨297492, by rfl⟩ : syracuseStep 793313 = 594985) B594985
theorem B139007 : Blo 135790 139007 := bstep (se 1 (by rfl) ⟨104255, by rfl⟩ : syracuseStep 139007 = 208511) B208511
theorem B204959 : Blo 135790 204959 := bstep (se 1 (by rfl) ⟨153719, by rfl⟩ : syracuseStep 204959 = 307439) B307439
theorem B2533949 : Blo 135790 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B308735 : Blo 135790 308735 := bstep (se 1 (by rfl) ⟨231551, by rfl⟩ : syracuseStep 308735 = 463103) B463103
theorem B1558601 : Blo 135790 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B1888201 : Blo 135790 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B2740331 : Blo 135790 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1496063 : Blo 135790 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B939941 : Blo 135790 939941 := bstep (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) B176239
theorem B645839 : Blo 135790 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B1597427 : Blo 135790 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1469767 : Blo 135790 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B587519 : Blo 135790 587519 := bstep (se 1 (by rfl) ⟨440639, by rfl⟩ : syracuseStep 587519 = 881279) B881279
theorem B523847 : Blo 135790 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B3015143 : Blo 135790 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B626627 : Blo 135790 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B430559 : Blo 135790 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B528875 : Blo 135790 528875 := bstep (se 1 (by rfl) ⟨396656, by rfl⟩ : syracuseStep 528875 = 793313) B793313
theorem B136639 : Blo 135790 136639 := bstep (se 1 (by rfl) ⟨102479, by rfl⟩ : syracuseStep 136639 = 204959) B204959
theorem B205823 : Blo 135790 205823 := bstep (se 1 (by rfl) ⟨154367, by rfl⟩ : syracuseStep 205823 = 308735) B308735
theorem B175871 : Blo 135790 175871 := bstep (se 1 (by rfl) ⟨131903, by rfl⟩ : syracuseStep 175871 = 263807) B263807
theorem B15643103 : Blo 135790 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B997375 : Blo 135790 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B1064951 : Blo 135790 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B1689299 : Blo 135790 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B349231 : Blo 135790 349231 := bstep (se 1 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 349231 = 523847) B523847
theorem B1039067 : Blo 135790 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B1826887 : Blo 135790 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B1959689 : Blo 135790 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B2517601 : Blo 135790 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B391679 : Blo 135790 391679 := bstep (se 1 (by rfl) ⟨293759, by rfl⟩ : syracuseStep 391679 = 587519) B587519
theorem B41714941 : Blo 135790 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B692711 : Blo 135790 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B137215 : Blo 135790 137215 := bstep (se 1 (by rfl) ⟨102911, by rfl⟩ : syracuseStep 137215 = 205823) B205823
theorem B465641 : Blo 135790 465641 := bstep (se 2 (by rfl) ⟨174615, by rfl⟩ : syracuseStep 465641 = 349231) B349231
theorem B468989 : Blo 135790 468989 := bstep (se 3 (by rfl) ⟨87935, by rfl⟩ : syracuseStep 468989 = 175871) B175871
theorem B2435849 : Blo 135790 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B2010095 : Blo 135790 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B1126199 : Blo 135790 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B3356801 : Blo 135790 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B1329833 : Blo 135790 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B709967 : Blo 135790 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B287039 : Blo 135790 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B352583 : Blo 135790 352583 := bstep (se 1 (by rfl) ⟨264437, by rfl⟩ : syracuseStep 352583 = 528875) B528875
theorem B1306459 : Blo 135790 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B261119 : Blo 135790 261119 := bstep (se 1 (by rfl) ⟨195839, by rfl⟩ : syracuseStep 261119 = 391679) B391679
theorem B1671005 : Blo 135790 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B886555 : Blo 135790 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B461807 : Blo 135790 461807 := bstep (se 1 (by rfl) ⟨346355, by rfl⟩ : syracuseStep 461807 = 692711) B692711
theorem B1741945 : Blo 135790 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B235055 : Blo 135790 235055 := bstep (se 1 (by rfl) ⟨176291, by rfl⟩ : syracuseStep 235055 = 352583) B352583
theorem B2237867 : Blo 135790 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B174079 : Blo 135790 174079 := bstep (se 1 (by rfl) ⟨130559, by rfl⟩ : syracuseStep 174079 = 261119) B261119
theorem B55619921 : Blo 135790 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B473311 : Blo 135790 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B310427 : Blo 135790 310427 := bstep (se 1 (by rfl) ⟨232820, by rfl⟩ : syracuseStep 310427 = 465641) B465641
theorem B312659 : Blo 135790 312659 := bstep (se 1 (by rfl) ⟨234494, by rfl⟩ : syracuseStep 312659 = 468989) B468989
theorem B1623899 : Blo 135790 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B191359 : Blo 135790 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B1340063 : Blo 135790 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B750799 : Blo 135790 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B1114003 : Blo 135790 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1182073 : Blo 135790 1182073 := bstep (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) B886555
theorem B232105 : Blo 135790 232105 := bstep (se 2 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 232105 = 174079) B174079
theorem B4330397 : Blo 135790 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B4004261 : Blo 135790 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B631081 : Blo 135790 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B893375 : Blo 135790 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B5941349 : Blo 135790 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B206951 : Blo 135790 206951 := bstep (se 1 (by rfl) ⟨155213, by rfl⟩ : syracuseStep 206951 = 310427) B310427
theorem B208439 : Blo 135790 208439 := bstep (se 1 (by rfl) ⟨156329, by rfl⟩ : syracuseStep 208439 = 312659) B312659
theorem B307871 : Blo 135790 307871 := bstep (se 1 (by rfl) ⟨230903, by rfl⟩ : syracuseStep 307871 = 461807) B461807
theorem B1491911 : Blo 135790 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B37079947 : Blo 135790 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B156703 : Blo 135790 156703 := bstep (se 1 (by rfl) ⟨117527, by rfl⟩ : syracuseStep 156703 = 235055) B235055
theorem B255145 : Blo 135790 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B2322593 : Blo 135790 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B1576097 : Blo 135790 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B2886931 : Blo 135790 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B197759717 : Blo 135790 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B595583 : Blo 135790 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B137967 : Blo 135790 137967 := bstep (se 1 (by rfl) ⟨103475, by rfl⟩ : syracuseStep 137967 = 206951) B206951
theorem B138959 : Blo 135790 138959 := bstep (se 1 (by rfl) ⟨104219, by rfl⟩ : syracuseStep 138959 = 208439) B208439
theorem B1548395 : Blo 135790 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B205247 : Blo 135790 205247 := bstep (se 1 (by rfl) ⟨153935, by rfl⟩ : syracuseStep 205247 = 307871) B307871
theorem B994607 : Blo 135790 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B208937 : Blo 135790 208937 := bstep (se 2 (by rfl) ⟨78351, by rfl⟩ : syracuseStep 208937 = 156703) B156703
theorem B340193 : Blo 135790 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B309473 : Blo 135790 309473 := bstep (se 2 (by rfl) ⟨116052, by rfl⟩ : syracuseStep 309473 = 232105) B232105
theorem B2669507 : Blo 135790 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B841441 : Blo 135790 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B3960899 : Blo 135790 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B1050731 : Blo 135790 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B397055 : Blo 135790 397055 := bstep (se 1 (by rfl) ⟨297791, by rfl⟩ : syracuseStep 397055 = 595583) B595583
theorem B136831 : Blo 135790 136831 := bstep (se 1 (by rfl) ⟨102623, by rfl⟩ : syracuseStep 136831 = 205247) B205247
theorem B663071 : Blo 135790 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B1121921 : Blo 135790 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B139291 : Blo 135790 139291 := bstep (se 1 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 139291 = 208937) B208937
theorem B206315 : Blo 135790 206315 := bstep (se 1 (by rfl) ⟨154736, by rfl⟩ : syracuseStep 206315 = 309473) B309473
theorem B1779671 : Blo 135790 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B131839811 : Blo 135790 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B3849241 : Blo 135790 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1032263 : Blo 135790 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B2640599 : Blo 135790 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B226795 : Blo 135790 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B688175 : Blo 135790 688175 := bstep (se 1 (by rfl) ⟨516131, by rfl⟩ : syracuseStep 688175 = 1032263) B1032263
theorem B264703 : Blo 135790 264703 := bstep (se 1 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 264703 = 397055) B397055
theorem B137543 : Blo 135790 137543 := bstep (se 1 (by rfl) ⟨103157, by rfl⟩ : syracuseStep 137543 = 206315) B206315
theorem B1186447 : Blo 135790 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B302393 : Blo 135790 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B87893207 : Blo 135790 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B700487 : Blo 135790 700487 := bstep (se 1 (by rfl) ⟨525365, by rfl⟩ : syracuseStep 700487 = 1050731) B1050731
theorem B5132321 : Blo 135790 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B1760399 : Blo 135790 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B747947 : Blo 135790 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B1768189 : Blo 135790 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B458783 : Blo 135790 458783 := bstep (se 1 (by rfl) ⟨344087, by rfl⟩ : syracuseStep 458783 = 688175) B688175
theorem B58595471 : Blo 135790 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B498631 : Blo 135790 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B466991 : Blo 135790 466991 := bstep (se 1 (by rfl) ⟨350243, by rfl⟩ : syracuseStep 466991 = 700487) B700487
theorem B1581929 : Blo 135790 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B3421547 : Blo 135790 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B806381 : Blo 135790 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B352937 : Blo 135790 352937 := bstep (se 2 (by rfl) ⟨132351, by rfl⟩ : syracuseStep 352937 = 264703) B264703
theorem B1173599 : Blo 135790 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B2357585 : Blo 135790 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B39063647 : Blo 135790 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B235291 : Blo 135790 235291 := bstep (se 1 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 235291 = 352937) B352937
theorem B1054619 : Blo 135790 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B664841 : Blo 135790 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B305855 : Blo 135790 305855 := bstep (se 1 (by rfl) ⟨229391, by rfl⟩ : syracuseStep 305855 = 458783) B458783
theorem B537587 : Blo 135790 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B311327 : Blo 135790 311327 := bstep (se 1 (by rfl) ⟨233495, by rfl⟩ : syracuseStep 311327 = 466991) B466991
theorem B2281031 : Blo 135790 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B782399 : Blo 135790 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B1571723 : Blo 135790 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B203903 : Blo 135790 203903 := bstep (se 1 (by rfl) ⟨152927, by rfl⟩ : syracuseStep 203903 = 305855) B305855
theorem B207551 : Blo 135790 207551 := bstep (se 1 (by rfl) ⟨155663, by rfl⟩ : syracuseStep 207551 = 311327) B311327
theorem B1520687 : Blo 135790 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B703079 : Blo 135790 703079 := bstep (se 1 (by rfl) ⟨527309, by rfl⟩ : syracuseStep 703079 = 1054619) B1054619
theorem B443227 : Blo 135790 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B313721 : Blo 135790 313721 := bstep (se 2 (by rfl) ⟨117645, by rfl⟩ : syracuseStep 313721 = 235291) B235291
theorem B26042431 : Blo 135790 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B521599 : Blo 135790 521599 := bstep (se 1 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 521599 = 782399) B782399
theorem B358391 : Blo 135790 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B1047815 : Blo 135790 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B590969 : Blo 135790 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B135935 : Blo 135790 135935 := bstep (se 1 (by rfl) ⟨101951, by rfl⟩ : syracuseStep 135935 = 203903) B203903
theorem B955709 : Blo 135790 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B138367 : Blo 135790 138367 := bstep (se 1 (by rfl) ⟨103775, by rfl⟩ : syracuseStep 138367 = 207551) B207551
theorem B695465 : Blo 135790 695465 := bstep (se 2 (by rfl) ⟨260799, by rfl⟩ : syracuseStep 695465 = 521599) B521599
theorem B468719 : Blo 135790 468719 := bstep (se 1 (by rfl) ⟨351539, by rfl⟩ : syracuseStep 468719 = 703079) B703079
theorem B698543 : Blo 135790 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B209147 : Blo 135790 209147 := bstep (se 1 (by rfl) ⟨156860, by rfl⟩ : syracuseStep 209147 = 313721) B313721
theorem B34723241 : Blo 135790 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1013791 : Blo 135790 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B393979 : Blo 135790 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B463643 : Blo 135790 463643 := bstep (se 1 (by rfl) ⟨347732, by rfl⟩ : syracuseStep 463643 = 695465) B695465
theorem B465695 : Blo 135790 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B1351721 : Blo 135790 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B139431 : Blo 135790 139431 := bstep (se 1 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 139431 = 209147) B209147
theorem B637139 : Blo 135790 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B23148827 : Blo 135790 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B312479 : Blo 135790 312479 := bstep (se 1 (by rfl) ⟨234359, by rfl⟩ : syracuseStep 312479 = 468719) B468719
theorem B525305 : Blo 135790 525305 := bstep (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) B393979
theorem B208319 : Blo 135790 208319 := bstep (se 1 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 208319 = 312479) B312479
theorem B309095 : Blo 135790 309095 := bstep (se 1 (by rfl) ⟨231821, by rfl⟩ : syracuseStep 309095 = 463643) B463643
theorem B310463 : Blo 135790 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B901147 : Blo 135790 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B424759 : Blo 135790 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B15432551 : Blo 135790 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B138879 : Blo 135790 138879 := bstep (se 1 (by rfl) ⟨104159, by rfl⟩ : syracuseStep 138879 = 208319) B208319
theorem B566345 : Blo 135790 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B206063 : Blo 135790 206063 := bstep (se 1 (by rfl) ⟨154547, by rfl⟩ : syracuseStep 206063 = 309095) B309095
theorem B206975 : Blo 135790 206975 := bstep (se 1 (by rfl) ⟨155231, by rfl⟩ : syracuseStep 206975 = 310463) B310463
theorem B1201529 : Blo 135790 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B350203 : Blo 135790 350203 := bstep (se 1 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 350203 = 525305) B525305
theorem B10288367 : Blo 135790 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B137375 : Blo 135790 137375 := bstep (se 1 (by rfl) ⟨103031, by rfl⟩ : syracuseStep 137375 = 206063) B206063
theorem B137983 : Blo 135790 137983 := bstep (se 1 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 137983 = 206975) B206975
theorem B466937 : Blo 135790 466937 := bstep (se 2 (by rfl) ⟨175101, by rfl⟩ : syracuseStep 466937 = 350203) B350203
theorem B6858911 : Blo 135790 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B801019 : Blo 135790 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B377563 : Blo 135790 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B503417 : Blo 135790 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B4272101 : Blo 135790 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B311291 : Blo 135790 311291 := bstep (se 1 (by rfl) ⟨233468, by rfl⟩ : syracuseStep 311291 = 466937) B466937
theorem B4572607 : Blo 135790 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B6096809 : Blo 135790 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B335611 : Blo 135790 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B207527 : Blo 135790 207527 := bstep (se 1 (by rfl) ⟨155645, by rfl⟩ : syracuseStep 207527 = 311291) B311291
theorem B2848067 : Blo 135790 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B16258157 : Blo 135790 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B138351 : Blo 135790 138351 := bstep (se 1 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 138351 = 207527) B207527
theorem B447481 : Blo 135790 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B1898711 : Blo 135790 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B596641 : Blo 135790 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B1265807 : Blo 135790 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B10838771 : Blo 135790 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B795521 : Blo 135790 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B7225847 : Blo 135790 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B843871 : Blo 135790 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B4817231 : Blo 135790 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B530347 : Blo 135790 530347 := bstep (se 1 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 530347 = 795521) B795521
theorem B1125161 : Blo 135790 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B3211487 : Blo 135790 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B707129 : Blo 135790 707129 := bstep (se 2 (by rfl) ⟨265173, by rfl⟩ : syracuseStep 707129 = 530347) B530347
theorem B750107 : Blo 135790 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 135790 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B2140991 : Blo 135790 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B471419 : Blo 135790 471419 := bstep (se 1 (by rfl) ⟨353564, by rfl⟩ : syracuseStep 471419 = 707129) B707129
theorem B1427327 : Blo 135790 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B314279 : Blo 135790 314279 := bstep (se 1 (by rfl) ⟨235709, by rfl⟩ : syracuseStep 314279 = 471419) B471419
theorem B1333523 : Blo 135790 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B951551 : Blo 135790 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B209519 : Blo 135790 209519 := bstep (se 1 (by rfl) ⟨157139, by rfl⟩ : syracuseStep 209519 = 314279) B314279
theorem B3556061 : Blo 135790 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B139679 : Blo 135790 139679 := bstep (se 1 (by rfl) ⟨104759, by rfl⟩ : syracuseStep 139679 = 209519) B209519
theorem B2370707 : Blo 135790 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B634367 : Blo 135790 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B1580471 : Blo 135790 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B422911 : Blo 135790 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B1053647 : Blo 135790 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B563881 : Blo 135790 563881 := bstep (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) B422911
theorem B702431 : Blo 135790 702431 := bstep (se 1 (by rfl) ⟨526823, by rfl⟩ : syracuseStep 702431 = 1053647) B1053647
theorem B751841 : Blo 135790 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B468287 : Blo 135790 468287 := bstep (se 1 (by rfl) ⟨351215, by rfl⟩ : syracuseStep 468287 = 702431) B702431
theorem B501227 : Blo 135790 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B334151 : Blo 135790 334151 := bstep (se 1 (by rfl) ⟨250613, by rfl⟩ : syracuseStep 334151 = 501227) B501227
theorem B312191 : Blo 135790 312191 := bstep (se 1 (by rfl) ⟨234143, by rfl⟩ : syracuseStep 312191 = 468287) B468287
theorem B208127 : Blo 135790 208127 := bstep (se 1 (by rfl) ⟨156095, by rfl⟩ : syracuseStep 208127 = 312191) B312191
theorem B222767 : Blo 135790 222767 := bstep (se 1 (by rfl) ⟨167075, by rfl⟩ : syracuseStep 222767 = 334151) B334151
theorem B138751 : Blo 135790 138751 := bstep (se 1 (by rfl) ⟨104063, by rfl⟩ : syracuseStep 138751 = 208127) B208127
theorem B148511 : Blo 135790 148511 := bstep (se 1 (by rfl) ⟨111383, by rfl⟩ : syracuseStep 148511 = 222767) B222767
theorem B396029 : Blo 135790 396029 := bstep (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) B148511
theorem B1056077 : Blo 135790 1056077 := bstep (se 3 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 1056077 = 396029) B396029
theorem B704051 : Blo 135790 704051 := bstep (se 1 (by rfl) ⟨528038, by rfl⟩ : syracuseStep 704051 = 1056077) B1056077
theorem B469367 : Blo 135790 469367 := bstep (se 1 (by rfl) ⟨352025, by rfl⟩ : syracuseStep 469367 = 704051) B704051
theorem B312911 : Blo 135790 312911 := bstep (se 1 (by rfl) ⟨234683, by rfl⟩ : syracuseStep 312911 = 469367) B469367
theorem B208607 : Blo 135790 208607 := bstep (se 1 (by rfl) ⟨156455, by rfl⟩ : syracuseStep 208607 = 312911) B312911
theorem B139071 : Blo 135790 139071 := bstep (se 1 (by rfl) ⟨104303, by rfl⟩ : syracuseStep 139071 = 208607) B208607

theorem C0 (j : ℕ) (h1 : 33947 ≤ j) (h2 : j ≤ 34646) : Blo 135790 (4 * j + 3) := by
  interval_cases j
  · exact B135791
  · exact B135795
  · exact B135799
  · exact B135803
  · exact B135807
  · exact B135811
  · exact B135815
  · exact B135819
  · exact B135823
  · exact B135827
  · exact B135831
  · exact B135835
  · exact B135839
  · exact B135843
  · exact B135847
  · exact B135851
  · exact B135855
  · exact B135859
  · exact B135863
  · exact B135867
  · exact B135871
  · exact B135875
  · exact B135879
  · exact B135883
  · exact B135887
  · exact B135891
  · exact B135895
  · exact B135899
  · exact B135903
  · exact B135907
  · exact B135911
  · exact B135915
  · exact B135919
  · exact B135923
  · exact B135927
  · exact B135931
  · exact B135935
  · exact B135939
  · exact B135943
  · exact B135947
  · exact B135951
  · exact B135955
  · exact B135959
  · exact B135963
  · exact B135967
  · exact B135971
  · exact B135975
  · exact B135979
  · exact B135983
  · exact B135987
  · exact B135991
  · exact B135995
  · exact B135999
  · exact B136003
  · exact B136007
  · exact B136011
  · exact B136015
  · exact B136019
  · exact B136023
  · exact B136027
  · exact B136031
  · exact B136035
  · exact B136039
  · exact B136043
  · exact B136047
  · exact B136051
  · exact B136055
  · exact B136059
  · exact B136063
  · exact B136067
  · exact B136071
  · exact B136075
  · exact B136079
  · exact B136083
  · exact B136087
  · exact B136091
  · exact B136095
  · exact B136099
  · exact B136103
  · exact B136107
  · exact B136111
  · exact B136115
  · exact B136119
  · exact B136123
  · exact B136127
  · exact B136131
  · exact B136135
  · exact B136139
  · exact B136143
  · exact B136147
  · exact B136151
  · exact B136155
  · exact B136159
  · exact B136163
  · exact B136167
  · exact B136171
  · exact B136175
  · exact B136179
  · exact B136183
  · exact B136187
  · exact B136191
  · exact B136195
  · exact B136199
  · exact B136203
  · exact B136207
  · exact B136211
  · exact B136215
  · exact B136219
  · exact B136223
  · exact B136227
  · exact B136231
  · exact B136235
  · exact B136239
  · exact B136243
  · exact B136247
  · exact B136251
  · exact B136255
  · exact B136259
  · exact B136263
  · exact B136267
  · exact B136271
  · exact B136275
  · exact B136279
  · exact B136283
  · exact B136287
  · exact B136291
  · exact B136295
  · exact B136299
  · exact B136303
  · exact B136307
  · exact B136311
  · exact B136315
  · exact B136319
  · exact B136323
  · exact B136327
  · exact B136331
  · exact B136335
  · exact B136339
  · exact B136343
  · exact B136347
  · exact B136351
  · exact B136355
  · exact B136359
  · exact B136363
  · exact B136367
  · exact B136371
  · exact B136375
  · exact B136379
  · exact B136383
  · exact B136387
  · exact B136391
  · exact B136395
  · exact B136399
  · exact B136403
  · exact B136407
  · exact B136411
  · exact B136415
  · exact B136419
  · exact B136423
  · exact B136427
  · exact B136431
  · exact B136435
  · exact B136439
  · exact B136443
  · exact B136447
  · exact B136451
  · exact B136455
  · exact B136459
  · exact B136463
  · exact B136467
  · exact B136471
  · exact B136475
  · exact B136479
  · exact B136483
  · exact B136487
  · exact B136491
  · exact B136495
  · exact B136499
  · exact B136503
  · exact B136507
  · exact B136511
  · exact B136515
  · exact B136519
  · exact B136523
  · exact B136527
  · exact B136531
  · exact B136535
  · exact B136539
  · exact B136543
  · exact B136547
  · exact B136551
  · exact B136555
  · exact B136559
  · exact B136563
  · exact B136567
  · exact B136571
  · exact B136575
  · exact B136579
  · exact B136583
  · exact B136587
  · exact B136591
  · exact B136595
  · exact B136599
  · exact B136603
  · exact B136607
  · exact B136611
  · exact B136615
  · exact B136619
  · exact B136623
  · exact B136627
  · exact B136631
  · exact B136635
  · exact B136639
  · exact B136643
  · exact B136647
  · exact B136651
  · exact B136655
  · exact B136659
  · exact B136663
  · exact B136667
  · exact B136671
  · exact B136675
  · exact B136679
  · exact B136683
  · exact B136687
  · exact B136691
  · exact B136695
  · exact B136699
  · exact B136703
  · exact B136707
  · exact B136711
  · exact B136715
  · exact B136719
  · exact B136723
  · exact B136727
  · exact B136731
  · exact B136735
  · exact B136739
  · exact B136743
  · exact B136747
  · exact B136751
  · exact B136755
  · exact B136759
  · exact B136763
  · exact B136767
  · exact B136771
  · exact B136775
  · exact B136779
  · exact B136783
  · exact B136787
  · exact B136791
  · exact B136795
  · exact B136799
  · exact B136803
  · exact B136807
  · exact B136811
  · exact B136815
  · exact B136819
  · exact B136823
  · exact B136827
  · exact B136831
  · exact B136835
  · exact B136839
  · exact B136843
  · exact B136847
  · exact B136851
  · exact B136855
  · exact B136859
  · exact B136863
  · exact B136867
  · exact B136871
  · exact B136875
  · exact B136879
  · exact B136883
  · exact B136887
  · exact B136891
  · exact B136895
  · exact B136899
  · exact B136903
  · exact B136907
  · exact B136911
  · exact B136915
  · exact B136919
  · exact B136923
  · exact B136927
  · exact B136931
  · exact B136935
  · exact B136939
  · exact B136943
  · exact B136947
  · exact B136951
  · exact B136955
  · exact B136959
  · exact B136963
  · exact B136967
  · exact B136971
  · exact B136975
  · exact B136979
  · exact B136983
  · exact B136987
  · exact B136991
  · exact B136995
  · exact B136999
  · exact B137003
  · exact B137007
  · exact B137011
  · exact B137015
  · exact B137019
  · exact B137023
  · exact B137027
  · exact B137031
  · exact B137035
  · exact B137039
  · exact B137043
  · exact B137047
  · exact B137051
  · exact B137055
  · exact B137059
  · exact B137063
  · exact B137067
  · exact B137071
  · exact B137075
  · exact B137079
  · exact B137083
  · exact B137087
  · exact B137091
  · exact B137095
  · exact B137099
  · exact B137103
  · exact B137107
  · exact B137111
  · exact B137115
  · exact B137119
  · exact B137123
  · exact B137127
  · exact B137131
  · exact B137135
  · exact B137139
  · exact B137143
  · exact B137147
  · exact B137151
  · exact B137155
  · exact B137159
  · exact B137163
  · exact B137167
  · exact B137171
  · exact B137175
  · exact B137179
  · exact B137183
  · exact B137187
  · exact B137191
  · exact B137195
  · exact B137199
  · exact B137203
  · exact B137207
  · exact B137211
  · exact B137215
  · exact B137219
  · exact B137223
  · exact B137227
  · exact B137231
  · exact B137235
  · exact B137239
  · exact B137243
  · exact B137247
  · exact B137251
  · exact B137255
  · exact B137259
  · exact B137263
  · exact B137267
  · exact B137271
  · exact B137275
  · exact B137279
  · exact B137283
  · exact B137287
  · exact B137291
  · exact B137295
  · exact B137299
  · exact B137303
  · exact B137307
  · exact B137311
  · exact B137315
  · exact B137319
  · exact B137323
  · exact B137327
  · exact B137331
  · exact B137335
  · exact B137339
  · exact B137343
  · exact B137347
  · exact B137351
  · exact B137355
  · exact B137359
  · exact B137363
  · exact B137367
  · exact B137371
  · exact B137375
  · exact B137379
  · exact B137383
  · exact B137387
  · exact B137391
  · exact B137395
  · exact B137399
  · exact B137403
  · exact B137407
  · exact B137411
  · exact B137415
  · exact B137419
  · exact B137423
  · exact B137427
  · exact B137431
  · exact B137435
  · exact B137439
  · exact B137443
  · exact B137447
  · exact B137451
  · exact B137455
  · exact B137459
  · exact B137463
  · exact B137467
  · exact B137471
  · exact B137475
  · exact B137479
  · exact B137483
  · exact B137487
  · exact B137491
  · exact B137495
  · exact B137499
  · exact B137503
  · exact B137507
  · exact B137511
  · exact B137515
  · exact B137519
  · exact B137523
  · exact B137527
  · exact B137531
  · exact B137535
  · exact B137539
  · exact B137543
  · exact B137547
  · exact B137551
  · exact B137555
  · exact B137559
  · exact B137563
  · exact B137567
  · exact B137571
  · exact B137575
  · exact B137579
  · exact B137583
  · exact B137587
  · exact B137591
  · exact B137595
  · exact B137599
  · exact B137603
  · exact B137607
  · exact B137611
  · exact B137615
  · exact B137619
  · exact B137623
  · exact B137627
  · exact B137631
  · exact B137635
  · exact B137639
  · exact B137643
  · exact B137647
  · exact B137651
  · exact B137655
  · exact B137659
  · exact B137663
  · exact B137667
  · exact B137671
  · exact B137675
  · exact B137679
  · exact B137683
  · exact B137687
  · exact B137691
  · exact B137695
  · exact B137699
  · exact B137703
  · exact B137707
  · exact B137711
  · exact B137715
  · exact B137719
  · exact B137723
  · exact B137727
  · exact B137731
  · exact B137735
  · exact B137739
  · exact B137743
  · exact B137747
  · exact B137751
  · exact B137755
  · exact B137759
  · exact B137763
  · exact B137767
  · exact B137771
  · exact B137775
  · exact B137779
  · exact B137783
  · exact B137787
  · exact B137791
  · exact B137795
  · exact B137799
  · exact B137803
  · exact B137807
  · exact B137811
  · exact B137815
  · exact B137819
  · exact B137823
  · exact B137827
  · exact B137831
  · exact B137835
  · exact B137839
  · exact B137843
  · exact B137847
  · exact B137851
  · exact B137855
  · exact B137859
  · exact B137863
  · exact B137867
  · exact B137871
  · exact B137875
  · exact B137879
  · exact B137883
  · exact B137887
  · exact B137891
  · exact B137895
  · exact B137899
  · exact B137903
  · exact B137907
  · exact B137911
  · exact B137915
  · exact B137919
  · exact B137923
  · exact B137927
  · exact B137931
  · exact B137935
  · exact B137939
  · exact B137943
  · exact B137947
  · exact B137951
  · exact B137955
  · exact B137959
  · exact B137963
  · exact B137967
  · exact B137971
  · exact B137975
  · exact B137979
  · exact B137983
  · exact B137987
  · exact B137991
  · exact B137995
  · exact B137999
  · exact B138003
  · exact B138007
  · exact B138011
  · exact B138015
  · exact B138019
  · exact B138023
  · exact B138027
  · exact B138031
  · exact B138035
  · exact B138039
  · exact B138043
  · exact B138047
  · exact B138051
  · exact B138055
  · exact B138059
  · exact B138063
  · exact B138067
  · exact B138071
  · exact B138075
  · exact B138079
  · exact B138083
  · exact B138087
  · exact B138091
  · exact B138095
  · exact B138099
  · exact B138103
  · exact B138107
  · exact B138111
  · exact B138115
  · exact B138119
  · exact B138123
  · exact B138127
  · exact B138131
  · exact B138135
  · exact B138139
  · exact B138143
  · exact B138147
  · exact B138151
  · exact B138155
  · exact B138159
  · exact B138163
  · exact B138167
  · exact B138171
  · exact B138175
  · exact B138179
  · exact B138183
  · exact B138187
  · exact B138191
  · exact B138195
  · exact B138199
  · exact B138203
  · exact B138207
  · exact B138211
  · exact B138215
  · exact B138219
  · exact B138223
  · exact B138227
  · exact B138231
  · exact B138235
  · exact B138239
  · exact B138243
  · exact B138247
  · exact B138251
  · exact B138255
  · exact B138259
  · exact B138263
  · exact B138267
  · exact B138271
  · exact B138275
  · exact B138279
  · exact B138283
  · exact B138287
  · exact B138291
  · exact B138295
  · exact B138299
  · exact B138303
  · exact B138307
  · exact B138311
  · exact B138315
  · exact B138319
  · exact B138323
  · exact B138327
  · exact B138331
  · exact B138335
  · exact B138339
  · exact B138343
  · exact B138347
  · exact B138351
  · exact B138355
  · exact B138359
  · exact B138363
  · exact B138367
  · exact B138371
  · exact B138375
  · exact B138379
  · exact B138383
  · exact B138387
  · exact B138391
  · exact B138395
  · exact B138399
  · exact B138403
  · exact B138407
  · exact B138411
  · exact B138415
  · exact B138419
  · exact B138423
  · exact B138427
  · exact B138431
  · exact B138435
  · exact B138439
  · exact B138443
  · exact B138447
  · exact B138451
  · exact B138455
  · exact B138459
  · exact B138463
  · exact B138467
  · exact B138471
  · exact B138475
  · exact B138479
  · exact B138483
  · exact B138487
  · exact B138491
  · exact B138495
  · exact B138499
  · exact B138503
  · exact B138507
  · exact B138511
  · exact B138515
  · exact B138519
  · exact B138523
  · exact B138527
  · exact B138531
  · exact B138535
  · exact B138539
  · exact B138543
  · exact B138547
  · exact B138551
  · exact B138555
  · exact B138559
  · exact B138563
  · exact B138567
  · exact B138571
  · exact B138575
  · exact B138579
  · exact B138583
  · exact B138587

theorem C1 (j : ℕ) (h1 : 34647 ≤ j) (h2 : j ≤ 34946) : Blo 135790 (4 * j + 3) := by
  interval_cases j
  · exact B138591
  · exact B138595
  · exact B138599
  · exact B138603
  · exact B138607
  · exact B138611
  · exact B138615
  · exact B138619
  · exact B138623
  · exact B138627
  · exact B138631
  · exact B138635
  · exact B138639
  · exact B138643
  · exact B138647
  · exact B138651
  · exact B138655
  · exact B138659
  · exact B138663
  · exact B138667
  · exact B138671
  · exact B138675
  · exact B138679
  · exact B138683
  · exact B138687
  · exact B138691
  · exact B138695
  · exact B138699
  · exact B138703
  · exact B138707
  · exact B138711
  · exact B138715
  · exact B138719
  · exact B138723
  · exact B138727
  · exact B138731
  · exact B138735
  · exact B138739
  · exact B138743
  · exact B138747
  · exact B138751
  · exact B138755
  · exact B138759
  · exact B138763
  · exact B138767
  · exact B138771
  · exact B138775
  · exact B138779
  · exact B138783
  · exact B138787
  · exact B138791
  · exact B138795
  · exact B138799
  · exact B138803
  · exact B138807
  · exact B138811
  · exact B138815
  · exact B138819
  · exact B138823
  · exact B138827
  · exact B138831
  · exact B138835
  · exact B138839
  · exact B138843
  · exact B138847
  · exact B138851
  · exact B138855
  · exact B138859
  · exact B138863
  · exact B138867
  · exact B138871
  · exact B138875
  · exact B138879
  · exact B138883
  · exact B138887
  · exact B138891
  · exact B138895
  · exact B138899
  · exact B138903
  · exact B138907
  · exact B138911
  · exact B138915
  · exact B138919
  · exact B138923
  · exact B138927
  · exact B138931
  · exact B138935
  · exact B138939
  · exact B138943
  · exact B138947
  · exact B138951
  · exact B138955
  · exact B138959
  · exact B138963
  · exact B138967
  · exact B138971
  · exact B138975
  · exact B138979
  · exact B138983
  · exact B138987
  · exact B138991
  · exact B138995
  · exact B138999
  · exact B139003
  · exact B139007
  · exact B139011
  · exact B139015
  · exact B139019
  · exact B139023
  · exact B139027
  · exact B139031
  · exact B139035
  · exact B139039
  · exact B139043
  · exact B139047
  · exact B139051
  · exact B139055
  · exact B139059
  · exact B139063
  · exact B139067
  · exact B139071
  · exact B139075
  · exact B139079
  · exact B139083
  · exact B139087
  · exact B139091
  · exact B139095
  · exact B139099
  · exact B139103
  · exact B139107
  · exact B139111
  · exact B139115
  · exact B139119
  · exact B139123
  · exact B139127
  · exact B139131
  · exact B139135
  · exact B139139
  · exact B139143
  · exact B139147
  · exact B139151
  · exact B139155
  · exact B139159
  · exact B139163
  · exact B139167
  · exact B139171
  · exact B139175
  · exact B139179
  · exact B139183
  · exact B139187
  · exact B139191
  · exact B139195
  · exact B139199
  · exact B139203
  · exact B139207
  · exact B139211
  · exact B139215
  · exact B139219
  · exact B139223
  · exact B139227
  · exact B139231
  · exact B139235
  · exact B139239
  · exact B139243
  · exact B139247
  · exact B139251
  · exact B139255
  · exact B139259
  · exact B139263
  · exact B139267
  · exact B139271
  · exact B139275
  · exact B139279
  · exact B139283
  · exact B139287
  · exact B139291
  · exact B139295
  · exact B139299
  · exact B139303
  · exact B139307
  · exact B139311
  · exact B139315
  · exact B139319
  · exact B139323
  · exact B139327
  · exact B139331
  · exact B139335
  · exact B139339
  · exact B139343
  · exact B139347
  · exact B139351
  · exact B139355
  · exact B139359
  · exact B139363
  · exact B139367
  · exact B139371
  · exact B139375
  · exact B139379
  · exact B139383
  · exact B139387
  · exact B139391
  · exact B139395
  · exact B139399
  · exact B139403
  · exact B139407
  · exact B139411
  · exact B139415
  · exact B139419
  · exact B139423
  · exact B139427
  · exact B139431
  · exact B139435
  · exact B139439
  · exact B139443
  · exact B139447
  · exact B139451
  · exact B139455
  · exact B139459
  · exact B139463
  · exact B139467
  · exact B139471
  · exact B139475
  · exact B139479
  · exact B139483
  · exact B139487
  · exact B139491
  · exact B139495
  · exact B139499
  · exact B139503
  · exact B139507
  · exact B139511
  · exact B139515
  · exact B139519
  · exact B139523
  · exact B139527
  · exact B139531
  · exact B139535
  · exact B139539
  · exact B139543
  · exact B139547
  · exact B139551
  · exact B139555
  · exact B139559
  · exact B139563
  · exact B139567
  · exact B139571
  · exact B139575
  · exact B139579
  · exact B139583
  · exact B139587
  · exact B139591
  · exact B139595
  · exact B139599
  · exact B139603
  · exact B139607
  · exact B139611
  · exact B139615
  · exact B139619
  · exact B139623
  · exact B139627
  · exact B139631
  · exact B139635
  · exact B139639
  · exact B139643
  · exact B139647
  · exact B139651
  · exact B139655
  · exact B139659
  · exact B139663
  · exact B139667
  · exact B139671
  · exact B139675
  · exact B139679
  · exact B139683
  · exact B139687
  · exact B139691
  · exact B139695
  · exact B139699
  · exact B139703
  · exact B139707
  · exact B139711
  · exact B139715
  · exact B139719
  · exact B139723
  · exact B139727
  · exact B139731
  · exact B139735
  · exact B139739
  · exact B139743
  · exact B139747
  · exact B139751
  · exact B139755
  · exact B139759
  · exact B139763
  · exact B139767
  · exact B139771
  · exact B139775
  · exact B139779
  · exact B139783
  · exact B139787

theorem solution (m : ℕ) (hlo : 135790 ≤ m) (hhi : m ≤ 139790) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 33947 ≤ j := by omega
    have hj2 : j ≤ 34946 := by omega
    have hb : Blo 135790 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 34647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
