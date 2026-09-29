-- Prove2me | solution 1 for syracuse_descends_range_1313975_1315975
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:32.539403+00:00
-- url     : https://prove2.me/submissions/7b4a5251-deaf-4784-9a04-3aa4a6f01fc2

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


theorem B2220061 : Blo 1313975 2220061 := bbase (se 3 (by rfl) ⟨416261, by rfl⟩ : syracuseStep 2220061 = 832523) (by norm_num)
theorem B2809885 : Blo 1313975 2809885 := bbase (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) (by norm_num)
theorem B1663021 : Blo 1313975 1663021 := bbase (se 3 (by rfl) ⟨311816, by rfl⟩ : syracuseStep 1663021 = 623633) (by norm_num)
theorem B2957381 : Blo 1313975 2957381 := bbase (se 4 (by rfl) ⟨277254, by rfl⟩ : syracuseStep 2957381 = 554509) (by norm_num)
theorem B4440149 : Blo 1313975 4440149 := bbase (se 8 (by rfl) ⟨26016, by rfl⟩ : syracuseStep 4440149 = 52033) (by norm_num)
theorem B2220149 : Blo 1313975 2220149 := bbase (se 5 (by rfl) ⟨104069, by rfl⟩ : syracuseStep 2220149 = 208139) (by norm_num)
theorem B3997829 : Blo 1313975 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B3326093 : Blo 1313975 3326093 := bbase (se 3 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 3326093 = 1247285) (by norm_num)
theorem B2957453 : Blo 1313975 2957453 := bbase (se 3 (by rfl) ⟨554522, by rfl⟩ : syracuseStep 2957453 = 1109045) (by norm_num)
theorem B2433205 : Blo 1313975 2433205 := bbase (se 5 (by rfl) ⟨114056, by rfl⟩ : syracuseStep 2433205 = 228113) (by norm_num)
theorem B1851589 : Blo 1313975 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B2957525 : Blo 1313975 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B7798997 : Blo 1313975 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B1663193 : Blo 1313975 1663193 := bbase (se 2 (by rfl) ⟨623697, by rfl⟩ : syracuseStep 1663193 = 1247395) (by norm_num)
theorem B2220277 : Blo 1313975 2220277 := bbase (se 5 (by rfl) ⟨104075, by rfl⟩ : syracuseStep 2220277 = 208151) (by norm_num)
theorem B1663249 : Blo 1313975 1663249 := bbase (se 2 (by rfl) ⟨623718, by rfl⟩ : syracuseStep 1663249 = 1247437) (by norm_num)
theorem B3997973 : Blo 1313975 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B2957597 : Blo 1313975 2957597 := bbase (se 3 (by rfl) ⟨554549, by rfl⟩ : syracuseStep 2957597 = 1109099) (by norm_num)
theorem B3744053 : Blo 1313975 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B3326285 : Blo 1313975 3326285 := bbase (se 3 (by rfl) ⟨623678, by rfl⟩ : syracuseStep 3326285 = 1247357) (by norm_num)
theorem B2220365 : Blo 1313975 2220365 := bbase (se 3 (by rfl) ⟨416318, by rfl⟩ : syracuseStep 2220365 = 832637) (by norm_num)
theorem B1499477 : Blo 1313975 1499477 := bbase (se 10 (by rfl) ⟨2196, by rfl⟩ : syracuseStep 1499477 = 4393) (by norm_num)
theorem B47997269 : Blo 1313975 47997269 := bbase (se 10 (by rfl) ⟨70308, by rfl⟩ : syracuseStep 47997269 = 140617) (by norm_num)
theorem B2957669 : Blo 1313975 2957669 := bbase (se 4 (by rfl) ⟨277281, by rfl⟩ : syracuseStep 2957669 = 554563) (by norm_num)
theorem B1663345 : Blo 1313975 1663345 := bbase (se 2 (by rfl) ⟨623754, by rfl⟩ : syracuseStep 1663345 = 1247509) (by norm_num)
theorem B3555701 : Blo 1313975 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B2810261 : Blo 1313975 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B2957741 : Blo 1313975 2957741 := bbase (se 3 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 2957741 = 1109153) (by norm_num)
theorem B2220493 : Blo 1313975 2220493 := bbase (se 3 (by rfl) ⟨416342, by rfl⟩ : syracuseStep 2220493 = 832685) (by norm_num)
theorem B4989397 : Blo 1313975 4989397 := bbase (se 7 (by rfl) ⟨58469, by rfl⟩ : syracuseStep 4989397 = 116939) (by norm_num)
theorem B2163181 : Blo 1313975 2163181 := bbase (se 3 (by rfl) ⟨405596, by rfl⟩ : syracuseStep 2163181 = 811193) (by norm_num)
theorem B2957813 : Blo 1313975 2957813 := bbase (se 5 (by rfl) ⟨138647, by rfl⟩ : syracuseStep 2957813 = 277295) (by norm_num)
theorem B3555829 : Blo 1313975 3555829 := bbase (se 5 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 3555829 = 333359) (by norm_num)
theorem B4440581 : Blo 1313975 4440581 := bbase (se 4 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 4440581 = 832609) (by norm_num)
theorem B6660629 : Blo 1313975 6660629 := bbase (se 6 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 6660629 = 312217) (by norm_num)
theorem B1663517 : Blo 1313975 1663517 := bbase (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) (by norm_num)
theorem B2220581 : Blo 1313975 2220581 := bbase (se 4 (by rfl) ⟨208179, by rfl⟩ : syracuseStep 2220581 = 416359) (by norm_num)
theorem B2368045 : Blo 1313975 2368045 := bbase (se 3 (by rfl) ⟨444008, by rfl⟩ : syracuseStep 2368045 = 888017) (by norm_num)
theorem B2957885 : Blo 1313975 2957885 := bbase (se 3 (by rfl) ⟨554603, by rfl⟩ : syracuseStep 2957885 = 1109207) (by norm_num)
theorem B1663573 : Blo 1313975 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B2105941 : Blo 1313975 2105941 := bbase (se 8 (by rfl) ⟨12339, by rfl⟩ : syracuseStep 2105941 = 24679) (by norm_num)
theorem B2957957 : Blo 1313975 2957957 := bbase (se 4 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 2957957 = 554617) (by norm_num)
theorem B3326629 : Blo 1313975 3326629 := bbase (se 4 (by rfl) ⟨311871, by rfl⟩ : syracuseStep 3326629 = 623743) (by norm_num)
theorem B2220709 : Blo 1313975 2220709 := bbase (se 4 (by rfl) ⟨208191, by rfl⟩ : syracuseStep 2220709 = 416383) (by norm_num)
theorem B8422069 : Blo 1313975 8422069 := bbase (se 5 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 8422069 = 789569) (by norm_num)
theorem B1663669 : Blo 1313975 1663669 := bbase (se 5 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 1663669 = 155969) (by norm_num)
theorem B4735685 : Blo 1313975 4735685 := bbase (se 4 (by rfl) ⟨443970, by rfl⟩ : syracuseStep 4735685 = 887941) (by norm_num)
theorem B2958029 : Blo 1313975 2958029 := bbase (se 3 (by rfl) ⟨554630, by rfl⟩ : syracuseStep 2958029 = 1109261) (by norm_num)
theorem B4989701 : Blo 1313975 4989701 := bbase (se 4 (by rfl) ⟨467784, by rfl⟩ : syracuseStep 4989701 = 935569) (by norm_num)
theorem B3326741 : Blo 1313975 3326741 := bbase (se 6 (by rfl) ⟨77970, by rfl⟩ : syracuseStep 3326741 = 155941) (by norm_num)
theorem B2958101 : Blo 1313975 2958101 := bbase (se 6 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 2958101 = 138661) (by norm_num)
theorem B3556165 : Blo 1313975 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B2958173 : Blo 1313975 2958173 := bbase (se 3 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 2958173 = 1109315) (by norm_num)
theorem B1663841 : Blo 1313975 1663841 := bbase (se 2 (by rfl) ⟨623940, by rfl⟩ : syracuseStep 1663841 = 1247881) (by norm_num)
theorem B1999765 : Blo 1313975 1999765 := bbase (se 6 (by rfl) ⟨46869, by rfl⟩ : syracuseStep 1999765 = 93739) (by norm_num)
theorem B1663897 : Blo 1313975 1663897 := bbase (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) (by norm_num)
theorem B2958245 : Blo 1313975 2958245 := bbase (se 4 (by rfl) ⟨277335, by rfl⟩ : syracuseStep 2958245 = 554671) (by norm_num)
theorem B6652853 : Blo 1313975 6652853 := bbase (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) (by norm_num)
theorem B4441013 : Blo 1313975 4441013 := bbase (se 5 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 4441013 = 416345) (by norm_num)
theorem B3326933 : Blo 1313975 3326933 := bbase (se 7 (by rfl) ⟨38987, by rfl⟩ : syracuseStep 3326933 = 77975) (by norm_num)
theorem B21341141 : Blo 1313975 21341141 := bbase (se 7 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 21341141 = 500183) (by norm_num)
theorem B2368477 : Blo 1313975 2368477 := bbase (se 3 (by rfl) ⟨444089, by rfl⟩ : syracuseStep 2368477 = 888179) (by norm_num)
theorem B2958317 : Blo 1313975 2958317 := bbase (se 3 (by rfl) ⟨554684, by rfl⟩ : syracuseStep 2958317 = 1109369) (by norm_num)
theorem B1663993 : Blo 1313975 1663993 := bbase (se 2 (by rfl) ⟨623997, by rfl⟩ : syracuseStep 1663993 = 1247995) (by norm_num)
theorem B2106389 : Blo 1313975 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B3744805 : Blo 1313975 3744805 := bbase (se 4 (by rfl) ⟨351075, by rfl⟩ : syracuseStep 3744805 = 702151) (by norm_num)
theorem B2958389 : Blo 1313975 2958389 := bbase (se 5 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 2958389 = 277349) (by norm_num)
theorem B2958461 : Blo 1313975 2958461 := bbase (se 3 (by rfl) ⟨554711, by rfl⟩ : syracuseStep 2958461 = 1109423) (by norm_num)
theorem B2999429 : Blo 1313975 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B1664165 : Blo 1313975 1664165 := bbase (se 4 (by rfl) ⟨156015, by rfl⟩ : syracuseStep 1664165 = 312031) (by norm_num)
theorem B2958533 : Blo 1313975 2958533 := bbase (se 4 (by rfl) ⟨277362, by rfl⟩ : syracuseStep 2958533 = 554725) (by norm_num)
theorem B1664221 : Blo 1313975 1664221 := bbase (se 3 (by rfl) ⟨312041, by rfl⟩ : syracuseStep 1664221 = 624083) (by norm_num)
theorem B4211957 : Blo 1313975 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B2368765 : Blo 1313975 2368765 := bbase (se 3 (by rfl) ⟨444143, by rfl⟩ : syracuseStep 2368765 = 888287) (by norm_num)
theorem B2958605 : Blo 1313975 2958605 := bbase (se 3 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 2958605 = 1109477) (by norm_num)
theorem B3327277 : Blo 1313975 3327277 := bbase (se 3 (by rfl) ⟨623864, by rfl⟩ : syracuseStep 3327277 = 1247729) (by norm_num)
theorem B1664317 : Blo 1313975 1664317 := bbase (se 3 (by rfl) ⟨312059, by rfl⟩ : syracuseStep 1664317 = 624119) (by norm_num)
theorem B2958677 : Blo 1313975 2958677 := bbase (se 12 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2958677 = 2167) (by norm_num)
theorem B3327389 : Blo 1313975 3327389 := bbase (se 3 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 3327389 = 1247771) (by norm_num)
theorem B2958749 : Blo 1313975 2958749 := bbase (se 3 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 2958749 = 1109531) (by norm_num)
theorem B2958821 : Blo 1313975 2958821 := bbase (se 4 (by rfl) ⟨277389, by rfl⟩ : syracuseStep 2958821 = 554779) (by norm_num)
theorem B1664489 : Blo 1313975 1664489 := bbase (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) (by norm_num)
theorem B1664545 : Blo 1313975 1664545 := bbase (se 2 (by rfl) ⟨624204, by rfl⟩ : syracuseStep 1664545 = 1248409) (by norm_num)
theorem B2958893 : Blo 1313975 2958893 := bbase (se 3 (by rfl) ⟨554792, by rfl⟩ : syracuseStep 2958893 = 1109585) (by norm_num)
theorem B5064245 : Blo 1313975 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B3327581 : Blo 1313975 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B2958965 : Blo 1313975 2958965 := bbase (se 5 (by rfl) ⟨138701, by rfl⟩ : syracuseStep 2958965 = 277403) (by norm_num)
theorem B1664641 : Blo 1313975 1664641 := bbase (se 2 (by rfl) ⟨624240, by rfl⟩ : syracuseStep 1664641 = 1248481) (by norm_num)
theorem B2959037 : Blo 1313975 2959037 := bbase (se 3 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 2959037 = 1109639) (by norm_num)
theorem B2959109 : Blo 1313975 2959109 := bbase (se 4 (by rfl) ⟨277416, by rfl⟩ : syracuseStep 2959109 = 554833) (by norm_num)
theorem B6661925 : Blo 1313975 6661925 := bbase (se 4 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 6661925 = 1249111) (by norm_num)
theorem B1664813 : Blo 1313975 1664813 := bbase (se 3 (by rfl) ⟨312152, by rfl⟩ : syracuseStep 1664813 = 624305) (by norm_num)
theorem B4736837 : Blo 1313975 4736837 := bbase (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) (by norm_num)
theorem B2959181 : Blo 1313975 2959181 := bbase (se 3 (by rfl) ⟨554846, by rfl⟩ : syracuseStep 2959181 = 1109693) (by norm_num)
theorem B9471829 : Blo 1313975 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B1664869 : Blo 1313975 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B2369429 : Blo 1313975 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B2959253 : Blo 1313975 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B3327925 : Blo 1313975 3327925 := bbase (se 5 (by rfl) ⟨155996, by rfl⟩ : syracuseStep 3327925 = 311993) (by norm_num)
theorem B1664965 : Blo 1313975 1664965 := bbase (se 4 (by rfl) ⟨156090, by rfl⟩ : syracuseStep 1664965 = 312181) (by norm_num)
theorem B5998549 : Blo 1313975 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B2959325 : Blo 1313975 2959325 := bbase (se 3 (by rfl) ⟨554873, by rfl⟩ : syracuseStep 2959325 = 1109747) (by norm_num)
theorem B3328037 : Blo 1313975 3328037 := bbase (se 4 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 3328037 = 624007) (by norm_num)
theorem B2959397 : Blo 1313975 2959397 := bbase (se 4 (by rfl) ⟨277443, by rfl⟩ : syracuseStep 2959397 = 554887) (by norm_num)
theorem B3000397 : Blo 1313975 3000397 := bbase (se 3 (by rfl) ⟨562574, by rfl⟩ : syracuseStep 3000397 = 1125149) (by norm_num)
theorem B2959469 : Blo 1313975 2959469 := bbase (se 3 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 2959469 = 1109801) (by norm_num)
theorem B1665137 : Blo 1313975 1665137 := bbase (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) (by norm_num)
theorem B1665193 : Blo 1313975 1665193 := bbase (se 2 (by rfl) ⟨624447, by rfl⟩ : syracuseStep 1665193 = 1248895) (by norm_num)
theorem B2959541 : Blo 1313975 2959541 := bbase (se 5 (by rfl) ⟨138728, by rfl⟩ : syracuseStep 2959541 = 277457) (by norm_num)
theorem B6654149 : Blo 1313975 6654149 := bbase (se 4 (by rfl) ⟨623826, by rfl⟩ : syracuseStep 6654149 = 1247653) (by norm_num)
theorem B3328229 : Blo 1313975 3328229 := bbase (se 4 (by rfl) ⟨312021, by rfl⟩ : syracuseStep 3328229 = 624043) (by norm_num)
theorem B11233525 : Blo 1313975 11233525 := bbase (se 5 (by rfl) ⟨526571, by rfl⟩ : syracuseStep 11233525 = 1053143) (by norm_num)
theorem B2959613 : Blo 1313975 2959613 := bbase (se 3 (by rfl) ⟨554927, by rfl⟩ : syracuseStep 2959613 = 1109855) (by norm_num)
theorem B5335301 : Blo 1313975 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B1665289 : Blo 1313975 1665289 := bbase (se 2 (by rfl) ⟨624483, by rfl⟩ : syracuseStep 1665289 = 1248967) (by norm_num)
theorem B5613893 : Blo 1313975 5613893 := bbase (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) (by norm_num)
theorem B2959685 : Blo 1313975 2959685 := bbase (se 4 (by rfl) ⟨277470, by rfl⟩ : syracuseStep 2959685 = 554941) (by norm_num)
theorem B2959757 : Blo 1313975 2959757 := bbase (se 3 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 2959757 = 1109909) (by norm_num)
theorem B1665461 : Blo 1313975 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B2959829 : Blo 1313975 2959829 := bbase (se 7 (by rfl) ⟨34685, by rfl⟩ : syracuseStep 2959829 = 69371) (by norm_num)
theorem B1665517 : Blo 1313975 1665517 := bbase (se 3 (by rfl) ⟨312284, by rfl⟩ : syracuseStep 1665517 = 624569) (by norm_num)
theorem B2107901 : Blo 1313975 2107901 := bbase (se 3 (by rfl) ⟨395231, by rfl⟩ : syracuseStep 2107901 = 790463) (by norm_num)
theorem B1403401 : Blo 1313975 1403401 := bbase (se 2 (by rfl) ⟨526275, by rfl⟩ : syracuseStep 1403401 = 1052551) (by norm_num)
theorem B2959901 : Blo 1313975 2959901 := bbase (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) (by norm_num)
theorem B3328573 : Blo 1313975 3328573 := bbase (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) (by norm_num)
theorem B2370149 : Blo 1313975 2370149 := bbase (se 4 (by rfl) ⟨222201, by rfl⟩ : syracuseStep 2370149 = 444403) (by norm_num)
theorem B2959973 : Blo 1313975 2959973 := bbase (se 4 (by rfl) ⟨277497, by rfl⟩ : syracuseStep 2959973 = 554995) (by norm_num)
theorem B9988757 : Blo 1313975 9988757 := bbase (se 6 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 9988757 = 468223) (by norm_num)
theorem B3328685 : Blo 1313975 3328685 := bbase (se 3 (by rfl) ⟨624128, by rfl⟩ : syracuseStep 3328685 = 1248257) (by norm_num)
theorem B2960045 : Blo 1313975 2960045 := bbase (se 3 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 2960045 = 1110017) (by norm_num)
theorem B2960117 : Blo 1313975 2960117 := bbase (se 5 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 2960117 = 277511) (by norm_num)
theorem B2960189 : Blo 1313975 2960189 := bbase (se 3 (by rfl) ⟨555035, by rfl⟩ : syracuseStep 2960189 = 1110071) (by norm_num)
theorem B4991813 : Blo 1313975 4991813 := bbase (se 4 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 4991813 = 935965) (by norm_num)
theorem B3328877 : Blo 1313975 3328877 := bbase (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) (by norm_num)
theorem B1403777 : Blo 1313975 1403777 := bbase (se 2 (by rfl) ⟨526416, by rfl⟩ : syracuseStep 1403777 = 1052833) (by norm_num)
theorem B2960261 : Blo 1313975 2960261 := bbase (se 4 (by rfl) ⟨277524, by rfl⟩ : syracuseStep 2960261 = 555049) (by norm_num)
theorem B2845589 : Blo 1313975 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B12643253 : Blo 1313975 12643253 := bbase (se 5 (by rfl) ⟨592652, by rfl⟩ : syracuseStep 12643253 = 1185305) (by norm_num)
theorem B1403849 : Blo 1313975 1403849 := bbase (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) (by norm_num)
theorem B2960333 : Blo 1313975 2960333 := bbase (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) (by norm_num)
theorem B4434965 : Blo 1313975 4434965 := bbase (se 6 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 4434965 = 207889) (by norm_num)
theorem B2960405 : Blo 1313975 2960405 := bbase (se 6 (by rfl) ⟨69384, by rfl⟩ : syracuseStep 2960405 = 138769) (by norm_num)
theorem B9980981 : Blo 1313975 9980981 := bbase (se 5 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 9980981 = 935717) (by norm_num)
theorem B1870933 : Blo 1313975 1870933 := bbase (se 8 (by rfl) ⟨10962, by rfl⟩ : syracuseStep 1870933 = 21925) (by norm_num)
theorem B2960477 : Blo 1313975 2960477 := bbase (se 3 (by rfl) ⟨555089, by rfl⟩ : syracuseStep 2960477 = 1110179) (by norm_num)
theorem B4992101 : Blo 1313975 4992101 := bbase (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) (by norm_num)
theorem B1404037 : Blo 1313975 1404037 := bbase (se 4 (by rfl) ⟨131628, by rfl⟩ : syracuseStep 1404037 = 263257) (by norm_num)
theorem B2247821 : Blo 1313975 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B2960549 : Blo 1313975 2960549 := bbase (se 4 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 2960549 = 555103) (by norm_num)
theorem B3329221 : Blo 1313975 3329221 := bbase (se 4 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 3329221 = 624229) (by norm_num)
theorem B4213957 : Blo 1313975 4213957 := bbase (se 4 (by rfl) ⟨395058, by rfl⟩ : syracuseStep 4213957 = 790117) (by norm_num)
theorem B2960621 : Blo 1313975 2960621 := bbase (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) (by norm_num)
theorem B12807413 : Blo 1313975 12807413 := bbase (se 5 (by rfl) ⟨600347, by rfl⟩ : syracuseStep 12807413 = 1200695) (by norm_num)
theorem B1600781 : Blo 1313975 1600781 := bbase (se 3 (by rfl) ⟨300146, by rfl⟩ : syracuseStep 1600781 = 600293) (by norm_num)
theorem B6319397 : Blo 1313975 6319397 := bbase (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) (by norm_num)
theorem B3329333 : Blo 1313975 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B2960693 : Blo 1313975 2960693 := bbase (se 5 (by rfl) ⟨138782, by rfl⟩ : syracuseStep 2960693 = 277565) (by norm_num)
theorem B1404221 : Blo 1313975 1404221 := bbase (se 3 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 1404221 = 526583) (by norm_num)
theorem B2960765 : Blo 1313975 2960765 := bbase (se 3 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 2960765 = 1110287) (by norm_num)
theorem B4435397 : Blo 1313975 4435397 := bbase (se 4 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 4435397 = 831637) (by norm_num)
theorem B2960837 : Blo 1313975 2960837 := bbase (se 4 (by rfl) ⟨277578, by rfl⟩ : syracuseStep 2960837 = 555157) (by norm_num)
theorem B1871309 : Blo 1313975 1871309 := bbase (se 3 (by rfl) ⟨350870, by rfl⟩ : syracuseStep 1871309 = 701741) (by norm_num)
theorem B6655445 : Blo 1313975 6655445 := bbase (se 7 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 6655445 = 155987) (by norm_num)
theorem B8424917 : Blo 1313975 8424917 := bbase (se 7 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 8424917 = 197459) (by norm_num)
theorem B3329525 : Blo 1313975 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B2960909 : Blo 1313975 2960909 := bbase (se 3 (by rfl) ⟨555170, by rfl⟩ : syracuseStep 2960909 = 1110341) (by norm_num)
theorem B2666029 : Blo 1313975 2666029 := bbase (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) (by norm_num)
theorem B1478245 : Blo 1313975 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B1478281 : Blo 1313975 1478281 := bbase (se 2 (by rfl) ⟨554355, by rfl⟩ : syracuseStep 1478281 = 1108711) (by norm_num)
theorem B3157661 : Blo 1313975 3157661 := bbase (se 3 (by rfl) ⟨592061, by rfl⟩ : syracuseStep 3157661 = 1184123) (by norm_num)
theorem B1478317 : Blo 1313975 1478317 := bbase (se 3 (by rfl) ⟨277184, by rfl⟩ : syracuseStep 1478317 = 554369) (by norm_num)
theorem B1478353 : Blo 1313975 1478353 := bbase (se 2 (by rfl) ⟨554382, by rfl⟩ : syracuseStep 1478353 = 1108765) (by norm_num)
theorem B1478389 : Blo 1313975 1478389 := bbase (se 5 (by rfl) ⟨69299, by rfl⟩ : syracuseStep 1478389 = 138599) (by norm_num)
theorem B1462025 : Blo 1313975 1462025 := bbase (se 2 (by rfl) ⟨548259, by rfl⟩ : syracuseStep 1462025 = 1096519) (by norm_num)
theorem B1478425 : Blo 1313975 1478425 := bbase (se 2 (by rfl) ⟨554409, by rfl⟩ : syracuseStep 1478425 = 1108819) (by norm_num)
theorem B1478461 : Blo 1313975 1478461 := bbase (se 3 (by rfl) ⟨277211, by rfl⟩ : syracuseStep 1478461 = 554423) (by norm_num)
theorem B3329869 : Blo 1313975 3329869 := bbase (se 3 (by rfl) ⟨624350, by rfl⟩ : syracuseStep 3329869 = 1248701) (by norm_num)
theorem B1478497 : Blo 1313975 1478497 := bbase (se 2 (by rfl) ⟨554436, by rfl⟩ : syracuseStep 1478497 = 1108873) (by norm_num)
theorem B4435829 : Blo 1313975 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1478533 : Blo 1313975 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1478569 : Blo 1313975 1478569 := bbase (se 2 (by rfl) ⟨554463, by rfl⟩ : syracuseStep 1478569 = 1108927) (by norm_num)
theorem B3329981 : Blo 1313975 3329981 := bbase (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) (by norm_num)
theorem B1478605 : Blo 1313975 1478605 := bbase (se 3 (by rfl) ⟨277238, by rfl⟩ : syracuseStep 1478605 = 554477) (by norm_num)
theorem B1478641 : Blo 1313975 1478641 := bbase (se 2 (by rfl) ⟨554490, by rfl⟩ : syracuseStep 1478641 = 1108981) (by norm_num)
theorem B12816373 : Blo 1313975 12816373 := bbase (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) (by norm_num)
theorem B3600389 : Blo 1313975 3600389 := bbase (se 4 (by rfl) ⟨337536, by rfl⟩ : syracuseStep 3600389 = 675073) (by norm_num)
theorem B1478677 : Blo 1313975 1478677 := bbase (se 6 (by rfl) ⟨34656, by rfl⟩ : syracuseStep 1478677 = 69313) (by norm_num)
theorem B1404973 : Blo 1313975 1404973 := bbase (se 3 (by rfl) ⟨263432, by rfl⟩ : syracuseStep 1404973 = 526865) (by norm_num)
theorem B5615669 : Blo 1313975 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B1478713 : Blo 1313975 1478713 := bbase (se 2 (by rfl) ⟨554517, by rfl⟩ : syracuseStep 1478713 = 1109035) (by norm_num)
theorem B3797077 : Blo 1313975 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B1478749 : Blo 1313975 1478749 := bbase (se 3 (by rfl) ⟨277265, by rfl⟩ : syracuseStep 1478749 = 554531) (by norm_num)
theorem B1405045 : Blo 1313975 1405045 := bbase (se 5 (by rfl) ⟨65861, by rfl⟩ : syracuseStep 1405045 = 131723) (by norm_num)
theorem B3330173 : Blo 1313975 3330173 := bbase (se 3 (by rfl) ⟨624407, by rfl⟩ : syracuseStep 3330173 = 1248815) (by norm_num)
theorem B1478785 : Blo 1313975 1478785 := bbase (se 2 (by rfl) ⟨554544, by rfl⟩ : syracuseStep 1478785 = 1109089) (by norm_num)
theorem B1478821 : Blo 1313975 1478821 := bbase (se 4 (by rfl) ⟨138639, by rfl⟩ : syracuseStep 1478821 = 277279) (by norm_num)
theorem B11235509 : Blo 1313975 11235509 := bbase (se 5 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 11235509 = 1053329) (by norm_num)
theorem B1478857 : Blo 1313975 1478857 := bbase (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) (by norm_num)
theorem B7491797 : Blo 1313975 7491797 := bbase (se 7 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 7491797 = 175589) (by norm_num)
theorem B1478893 : Blo 1313975 1478893 := bbase (se 3 (by rfl) ⟨277292, by rfl⟩ : syracuseStep 1478893 = 554585) (by norm_num)
theorem B4993285 : Blo 1313975 4993285 := bbase (se 4 (by rfl) ⟨468120, by rfl⟩ : syracuseStep 4993285 = 936241) (by norm_num)
theorem B1478929 : Blo 1313975 1478929 := bbase (se 2 (by rfl) ⟨554598, by rfl⟩ : syracuseStep 1478929 = 1109197) (by norm_num)
theorem B4436261 : Blo 1313975 4436261 := bbase (se 4 (by rfl) ⟨415899, by rfl⟩ : syracuseStep 4436261 = 831799) (by norm_num)
theorem B1405225 : Blo 1313975 1405225 := bbase (se 2 (by rfl) ⟨526959, by rfl⟩ : syracuseStep 1405225 = 1053919) (by norm_num)
theorem B1478965 : Blo 1313975 1478965 := bbase (se 5 (by rfl) ⟨69326, by rfl⟩ : syracuseStep 1478965 = 138653) (by norm_num)
theorem B1479001 : Blo 1313975 1479001 := bbase (se 2 (by rfl) ⟨554625, by rfl⟩ : syracuseStep 1479001 = 1109251) (by norm_num)
theorem B2494813 : Blo 1313975 2494813 := bbase (se 3 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 2494813 = 935555) (by norm_num)
theorem B9613685 : Blo 1313975 9613685 := bbase (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) (by norm_num)
theorem B1479037 : Blo 1313975 1479037 := bbase (se 3 (by rfl) ⟨277319, by rfl⟩ : syracuseStep 1479037 = 554639) (by norm_num)
theorem B1896853 : Blo 1313975 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B1479073 : Blo 1313975 1479073 := bbase (se 2 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 1479073 = 1109305) (by norm_num)
theorem B2249149 : Blo 1313975 2249149 := bbase (se 3 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 2249149 = 843431) (by norm_num)
theorem B1479109 : Blo 1313975 1479109 := bbase (se 4 (by rfl) ⟨138666, by rfl⟩ : syracuseStep 1479109 = 277333) (by norm_num)
theorem B3330517 : Blo 1313975 3330517 := bbase (se 7 (by rfl) ⟨39029, by rfl⟩ : syracuseStep 3330517 = 78059) (by norm_num)
theorem B1479145 : Blo 1313975 1479145 := bbase (se 2 (by rfl) ⟨554679, by rfl⟩ : syracuseStep 1479145 = 1109359) (by norm_num)
theorem B2494957 : Blo 1313975 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B1479181 : Blo 1313975 1479181 := bbase (se 3 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 1479181 = 554693) (by norm_num)
theorem B1479217 : Blo 1313975 1479217 := bbase (se 2 (by rfl) ⟨554706, by rfl⟩ : syracuseStep 1479217 = 1109413) (by norm_num)
theorem B4993589 : Blo 1313975 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B3330629 : Blo 1313975 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B1479253 : Blo 1313975 1479253 := bbase (se 8 (by rfl) ⟨8667, by rfl⟩ : syracuseStep 1479253 = 17335) (by norm_num)
theorem B1479289 : Blo 1313975 1479289 := bbase (se 2 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 1479289 = 1109467) (by norm_num)
theorem B2495117 : Blo 1313975 2495117 := bbase (se 3 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 2495117 = 935669) (by norm_num)
theorem B3551893 : Blo 1313975 3551893 := bbase (se 6 (by rfl) ⟨83247, by rfl⟩ : syracuseStep 3551893 = 166495) (by norm_num)
theorem B1479325 : Blo 1313975 1479325 := bbase (se 3 (by rfl) ⟨277373, by rfl⟩ : syracuseStep 1479325 = 554747) (by norm_num)
theorem B2249381 : Blo 1313975 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B1479361 : Blo 1313975 1479361 := bbase (se 2 (by rfl) ⟨554760, by rfl⟩ : syracuseStep 1479361 = 1109521) (by norm_num)
theorem B4436693 : Blo 1313975 4436693 := bbase (se 7 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 4436693 = 103985) (by norm_num)
theorem B6656741 : Blo 1313975 6656741 := bbase (se 4 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 6656741 = 1248139) (by norm_num)
theorem B1479397 : Blo 1313975 1479397 := bbase (se 4 (by rfl) ⟨138693, by rfl⟩ : syracuseStep 1479397 = 277387) (by norm_num)
theorem B3330821 : Blo 1313975 3330821 := bbase (se 4 (by rfl) ⟨312264, by rfl⟩ : syracuseStep 3330821 = 624529) (by norm_num)
theorem B1479433 : Blo 1313975 1479433 := bbase (se 2 (by rfl) ⟨554787, by rfl⟩ : syracuseStep 1479433 = 1109575) (by norm_num)
theorem B2495261 : Blo 1313975 2495261 := bbase (se 3 (by rfl) ⟨467861, by rfl⟩ : syracuseStep 2495261 = 935723) (by norm_num)
theorem B1970981 : Blo 1313975 1970981 := bbase (se 4 (by rfl) ⟨184779, by rfl⟩ : syracuseStep 1970981 = 369559) (by norm_num)
theorem B1332005 : Blo 1313975 1332005 := bbase (se 4 (by rfl) ⟨124875, by rfl⟩ : syracuseStep 1332005 = 249751) (by norm_num)
theorem B1479469 : Blo 1313975 1479469 := bbase (se 3 (by rfl) ⟨277400, by rfl⟩ : syracuseStep 1479469 = 554801) (by norm_num)
theorem B1971005 : Blo 1313975 1971005 := bbase (se 3 (by rfl) ⟨369563, by rfl⟩ : syracuseStep 1971005 = 739127) (by norm_num)
theorem B1479505 : Blo 1313975 1479505 := bbase (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) (by norm_num)
theorem B1971029 : Blo 1313975 1971029 := bbase (se 9 (by rfl) ⟨5774, by rfl⟩ : syracuseStep 1971029 = 11549) (by norm_num)
theorem B1872733 : Blo 1313975 1872733 := bbase (se 3 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 1872733 = 702275) (by norm_num)
theorem B1971053 : Blo 1313975 1971053 := bbase (se 3 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 1971053 = 739145) (by norm_num)
theorem B1479541 : Blo 1313975 1479541 := bbase (se 5 (by rfl) ⟨69353, by rfl⟩ : syracuseStep 1479541 = 138707) (by norm_num)
theorem B1971077 : Blo 1313975 1971077 := bbase (se 4 (by rfl) ⟨184788, by rfl⟩ : syracuseStep 1971077 = 369577) (by norm_num)
theorem B3552133 : Blo 1313975 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B1479577 : Blo 1313975 1479577 := bbase (se 2 (by rfl) ⟨554841, by rfl⟩ : syracuseStep 1479577 = 1109683) (by norm_num)
theorem B1971101 : Blo 1313975 1971101 := bbase (se 3 (by rfl) ⟨369581, by rfl⟩ : syracuseStep 1971101 = 739163) (by norm_num)
theorem B1971125 : Blo 1313975 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B1479613 : Blo 1313975 1479613 := bbase (se 3 (by rfl) ⟨277427, by rfl⟩ : syracuseStep 1479613 = 554855) (by norm_num)
theorem B1971149 : Blo 1313975 1971149 := bbase (se 3 (by rfl) ⟨369590, by rfl⟩ : syracuseStep 1971149 = 739181) (by norm_num)
theorem B2806741 : Blo 1313975 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B1479649 : Blo 1313975 1479649 := bbase (se 2 (by rfl) ⟨554868, by rfl⟩ : syracuseStep 1479649 = 1109737) (by norm_num)
theorem B1971173 : Blo 1313975 1971173 := bbase (se 4 (by rfl) ⟨184797, by rfl⟩ : syracuseStep 1971173 = 369595) (by norm_num)
theorem B1971197 : Blo 1313975 1971197 := bbase (se 3 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 1971197 = 739199) (by norm_num)
theorem B1479685 : Blo 1313975 1479685 := bbase (se 4 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 1479685 = 277441) (by norm_num)
theorem B1971221 : Blo 1313975 1971221 := bbase (se 6 (by rfl) ⟨46200, by rfl⟩ : syracuseStep 1971221 = 92401) (by norm_num)
theorem B5616661 : Blo 1313975 5616661 := bbase (se 6 (by rfl) ⟨131640, by rfl⟩ : syracuseStep 5616661 = 263281) (by norm_num)
theorem B1479721 : Blo 1313975 1479721 := bbase (se 2 (by rfl) ⟨554895, by rfl⟩ : syracuseStep 1479721 = 1109791) (by norm_num)
theorem B1971245 : Blo 1313975 1971245 := bbase (se 3 (by rfl) ⟨369608, by rfl⟩ : syracuseStep 1971245 = 739217) (by norm_num)
theorem B2495549 : Blo 1313975 2495549 := bbase (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) (by norm_num)
theorem B1971269 : Blo 1313975 1971269 := bbase (se 4 (by rfl) ⟨184806, by rfl⟩ : syracuseStep 1971269 = 369613) (by norm_num)
theorem B1479757 : Blo 1313975 1479757 := bbase (se 3 (by rfl) ⟨277454, by rfl⟩ : syracuseStep 1479757 = 554909) (by norm_num)
theorem B1971293 : Blo 1313975 1971293 := bbase (se 3 (by rfl) ⟨369617, by rfl⟩ : syracuseStep 1971293 = 739235) (by norm_num)
theorem B1479793 : Blo 1313975 1479793 := bbase (se 2 (by rfl) ⟨554922, by rfl⟩ : syracuseStep 1479793 = 1109845) (by norm_num)
theorem B1971317 : Blo 1313975 1971317 := bbase (se 5 (by rfl) ⟨92405, by rfl⟩ : syracuseStep 1971317 = 184811) (by norm_num)
theorem B2249845 : Blo 1313975 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B4437125 : Blo 1313975 4437125 := bbase (se 4 (by rfl) ⟨415980, by rfl⟩ : syracuseStep 4437125 = 831961) (by norm_num)
theorem B1971341 : Blo 1313975 1971341 := bbase (se 3 (by rfl) ⟨369626, by rfl⟩ : syracuseStep 1971341 = 739253) (by norm_num)
theorem B1479829 : Blo 1313975 1479829 := bbase (se 6 (by rfl) ⟨34683, by rfl⟩ : syracuseStep 1479829 = 69367) (by norm_num)
theorem B1971365 : Blo 1313975 1971365 := bbase (se 4 (by rfl) ⟨184815, by rfl⟩ : syracuseStep 1971365 = 369631) (by norm_num)
theorem B1479865 : Blo 1313975 1479865 := bbase (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) (by norm_num)
theorem B1971389 : Blo 1313975 1971389 := bbase (se 3 (by rfl) ⟨369635, by rfl⟩ : syracuseStep 1971389 = 739271) (by norm_num)
theorem B1971413 : Blo 1313975 1971413 := bbase (se 7 (by rfl) ⟨23102, by rfl⟩ : syracuseStep 1971413 = 46205) (by norm_num)
theorem B2495701 : Blo 1313975 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B8541397 : Blo 1313975 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B1479901 : Blo 1313975 1479901 := bbase (se 3 (by rfl) ⟨277481, by rfl⟩ : syracuseStep 1479901 = 554963) (by norm_num)
theorem B2249957 : Blo 1313975 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B1971437 : Blo 1313975 1971437 := bbase (se 3 (by rfl) ⟨369644, by rfl⟩ : syracuseStep 1971437 = 739289) (by norm_num)
theorem B2667773 : Blo 1313975 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B1479937 : Blo 1313975 1479937 := bbase (se 2 (by rfl) ⟨554976, by rfl⟩ : syracuseStep 1479937 = 1109953) (by norm_num)
theorem B1971461 : Blo 1313975 1971461 := bbase (se 4 (by rfl) ⟨184824, by rfl⟩ : syracuseStep 1971461 = 369649) (by norm_num)
theorem B2667797 : Blo 1313975 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B1971485 : Blo 1313975 1971485 := bbase (se 3 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 1971485 = 739307) (by norm_num)
theorem B1479973 : Blo 1313975 1479973 := bbase (se 4 (by rfl) ⟨138747, by rfl⟩ : syracuseStep 1479973 = 277495) (by norm_num)
theorem B1971509 : Blo 1313975 1971509 := bbase (se 5 (by rfl) ⟨92414, by rfl⟩ : syracuseStep 1971509 = 184829) (by norm_num)
theorem B2667845 : Blo 1313975 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B1480009 : Blo 1313975 1480009 := bbase (se 2 (by rfl) ⟨555003, by rfl⟩ : syracuseStep 1480009 = 1110007) (by norm_num)
theorem B1971533 : Blo 1313975 1971533 := bbase (se 3 (by rfl) ⟨369662, by rfl⟩ : syracuseStep 1971533 = 739325) (by norm_num)
theorem B1971557 : Blo 1313975 1971557 := bbase (se 4 (by rfl) ⟨184833, by rfl⟩ : syracuseStep 1971557 = 369667) (by norm_num)
theorem B1480045 : Blo 1313975 1480045 := bbase (se 3 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 1480045 = 555017) (by norm_num)
theorem B2217341 : Blo 1313975 2217341 := bbase (se 3 (by rfl) ⟨415751, by rfl⟩ : syracuseStep 2217341 = 831503) (by norm_num)
theorem B1971581 : Blo 1313975 1971581 := bbase (se 3 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 1971581 = 739343) (by norm_num)
theorem B1480081 : Blo 1313975 1480081 := bbase (se 2 (by rfl) ⟨555030, by rfl⟩ : syracuseStep 1480081 = 1110061) (by norm_num)
theorem B1971605 : Blo 1313975 1971605 := bbase (se 6 (by rfl) ⟨46209, by rfl⟩ : syracuseStep 1971605 = 92419) (by norm_num)
theorem B1971629 : Blo 1313975 1971629 := bbase (se 3 (by rfl) ⟨369680, by rfl⟩ : syracuseStep 1971629 = 739361) (by norm_num)
theorem B1873325 : Blo 1313975 1873325 := bbase (se 3 (by rfl) ⟨351248, by rfl⟩ : syracuseStep 1873325 = 702497) (by norm_num)
theorem B5330357 : Blo 1313975 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B1480117 : Blo 1313975 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B2807237 : Blo 1313975 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B1971653 : Blo 1313975 1971653 := bbase (se 4 (by rfl) ⟨184842, by rfl⟩ : syracuseStep 1971653 = 369685) (by norm_num)
theorem B1480153 : Blo 1313975 1480153 := bbase (se 2 (by rfl) ⟨555057, by rfl⟩ : syracuseStep 1480153 = 1110115) (by norm_num)
theorem B1971677 : Blo 1313975 1971677 := bbase (se 3 (by rfl) ⟨369689, by rfl⟩ : syracuseStep 1971677 = 739379) (by norm_num)
theorem B1971701 : Blo 1313975 1971701 := bbase (se 5 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 1971701 = 184847) (by norm_num)
theorem B2217469 : Blo 1313975 2217469 := bbase (se 3 (by rfl) ⟨415775, by rfl⟩ : syracuseStep 2217469 = 831551) (by norm_num)
theorem B1480189 : Blo 1313975 1480189 := bbase (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) (by norm_num)
theorem B1873405 : Blo 1313975 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B2496005 : Blo 1313975 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B1971725 : Blo 1313975 1971725 := bbase (se 3 (by rfl) ⟨369698, by rfl⟩ : syracuseStep 1971725 = 739397) (by norm_num)
theorem B1480225 : Blo 1313975 1480225 := bbase (se 2 (by rfl) ⟨555084, by rfl⟩ : syracuseStep 1480225 = 1110169) (by norm_num)
theorem B1971749 : Blo 1313975 1971749 := bbase (se 4 (by rfl) ⟨184851, by rfl⟩ : syracuseStep 1971749 = 369703) (by norm_num)
theorem B4437557 : Blo 1313975 4437557 := bbase (se 5 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 4437557 = 416021) (by norm_num)
theorem B1971773 : Blo 1313975 1971773 := bbase (se 3 (by rfl) ⟨369707, by rfl⟩ : syracuseStep 1971773 = 739415) (by norm_num)
theorem B1480261 : Blo 1313975 1480261 := bbase (se 4 (by rfl) ⟨138774, by rfl⟩ : syracuseStep 1480261 = 277549) (by norm_num)
theorem B2217557 : Blo 1313975 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B1971797 : Blo 1313975 1971797 := bbase (se 8 (by rfl) ⟨11553, by rfl⟩ : syracuseStep 1971797 = 23107) (by norm_num)
theorem B1480297 : Blo 1313975 1480297 := bbase (se 2 (by rfl) ⟨555111, by rfl⟩ : syracuseStep 1480297 = 1110223) (by norm_num)
theorem B1971821 : Blo 1313975 1971821 := bbase (se 3 (by rfl) ⟨369716, by rfl⟩ : syracuseStep 1971821 = 739433) (by norm_num)
theorem B3159661 : Blo 1313975 3159661 := bbase (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) (by norm_num)
theorem B1873525 : Blo 1313975 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B1971845 : Blo 1313975 1971845 := bbase (se 4 (by rfl) ⟨184860, by rfl⟩ : syracuseStep 1971845 = 369721) (by norm_num)
theorem B1480333 : Blo 1313975 1480333 := bbase (se 3 (by rfl) ⟨277562, by rfl⟩ : syracuseStep 1480333 = 555125) (by norm_num)
theorem B1971869 : Blo 1313975 1971869 := bbase (se 3 (by rfl) ⟨369725, by rfl⟩ : syracuseStep 1971869 = 739451) (by norm_num)
theorem B1480369 : Blo 1313975 1480369 := bbase (se 2 (by rfl) ⟨555138, by rfl⟩ : syracuseStep 1480369 = 1110277) (by norm_num)
theorem B1971893 : Blo 1313975 1971893 := bbase (se 5 (by rfl) ⟨92432, by rfl⟩ : syracuseStep 1971893 = 184865) (by norm_num)
theorem B1971917 : Blo 1313975 1971917 := bbase (se 3 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 1971917 = 739469) (by norm_num)
theorem B2217685 : Blo 1313975 2217685 := bbase (se 7 (by rfl) ⟨25988, by rfl⟩ : syracuseStep 2217685 = 51977) (by norm_num)
theorem B1873621 : Blo 1313975 1873621 := bbase (se 7 (by rfl) ⟨21956, by rfl⟩ : syracuseStep 1873621 = 43913) (by norm_num)
theorem B1480405 : Blo 1313975 1480405 := bbase (se 7 (by rfl) ⟨17348, by rfl⟩ : syracuseStep 1480405 = 34697) (by norm_num)
theorem B1971941 : Blo 1313975 1971941 := bbase (se 4 (by rfl) ⟨184869, by rfl⟩ : syracuseStep 1971941 = 369739) (by norm_num)
theorem B6747893 : Blo 1313975 6747893 := bbase (se 5 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 6747893 = 632615) (by norm_num)
theorem B1480441 : Blo 1313975 1480441 := bbase (se 2 (by rfl) ⟨555165, by rfl⟩ : syracuseStep 1480441 = 1110331) (by norm_num)
theorem B1971965 : Blo 1313975 1971965 := bbase (se 3 (by rfl) ⟨369743, by rfl⟩ : syracuseStep 1971965 = 739487) (by norm_num)
theorem B3159805 : Blo 1313975 3159805 := bbase (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) (by norm_num)
theorem B1971989 : Blo 1313975 1971989 := bbase (se 6 (by rfl) ⟨46218, by rfl⟩ : syracuseStep 1971989 = 92437) (by norm_num)
theorem B2250517 : Blo 1313975 2250517 := bbase (se 6 (by rfl) ⟨52746, by rfl⟩ : syracuseStep 2250517 = 105493) (by norm_num)
theorem B2217773 : Blo 1313975 2217773 := bbase (se 3 (by rfl) ⟨415832, by rfl⟩ : syracuseStep 2217773 = 831665) (by norm_num)
theorem B1972013 : Blo 1313975 1972013 := bbase (se 3 (by rfl) ⟨369752, by rfl⟩ : syracuseStep 1972013 = 739505) (by norm_num)
theorem B1972037 : Blo 1313975 1972037 := bbase (se 4 (by rfl) ⟨184878, by rfl⟩ : syracuseStep 1972037 = 369757) (by norm_num)
theorem B14980949 : Blo 1313975 14980949 := bbase (se 9 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 14980949 = 87779) (by norm_num)
theorem B1972061 : Blo 1313975 1972061 := bbase (se 3 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 1972061 = 739523) (by norm_num)
theorem B1972085 : Blo 1313975 1972085 := bbase (se 5 (by rfl) ⟨92441, by rfl⟩ : syracuseStep 1972085 = 184883) (by norm_num)
theorem B1578889 : Blo 1313975 1578889 := bbase (se 2 (by rfl) ⟨592083, by rfl⟩ : syracuseStep 1578889 = 1184167) (by norm_num)
theorem B1972109 : Blo 1313975 1972109 := bbase (se 3 (by rfl) ⟨369770, by rfl⟩ : syracuseStep 1972109 = 739541) (by norm_num)
theorem B3372965 : Blo 1313975 3372965 := bbase (se 4 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 3372965 = 632431) (by norm_num)
theorem B1972133 : Blo 1313975 1972133 := bbase (se 4 (by rfl) ⟨184887, by rfl⟩ : syracuseStep 1972133 = 369775) (by norm_num)
theorem B2217901 : Blo 1313975 2217901 := bbase (se 3 (by rfl) ⟨415856, by rfl⟩ : syracuseStep 2217901 = 831713) (by norm_num)
theorem B1972157 : Blo 1313975 1972157 := bbase (se 3 (by rfl) ⟨369779, by rfl⟩ : syracuseStep 1972157 = 739559) (by norm_num)
theorem B2701253 : Blo 1313975 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B1972181 : Blo 1313975 1972181 := bbase (se 7 (by rfl) ⟨23111, by rfl⟩ : syracuseStep 1972181 = 46223) (by norm_num)
theorem B4437989 : Blo 1313975 4437989 := bbase (se 4 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 4437989 = 832123) (by norm_num)
theorem B1972205 : Blo 1313975 1972205 := bbase (se 3 (by rfl) ⟨369788, by rfl⟩ : syracuseStep 1972205 = 739577) (by norm_num)
theorem B6658037 : Blo 1313975 6658037 := bbase (se 5 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 6658037 = 624191) (by norm_num)
theorem B2217989 : Blo 1313975 2217989 := bbase (se 4 (by rfl) ⟨207936, by rfl⟩ : syracuseStep 2217989 = 415873) (by norm_num)
theorem B1972229 : Blo 1313975 1972229 := bbase (se 4 (by rfl) ⟨184896, by rfl⟩ : syracuseStep 1972229 = 369793) (by norm_num)
theorem B1972253 : Blo 1313975 1972253 := bbase (se 3 (by rfl) ⟨369797, by rfl⟩ : syracuseStep 1972253 = 739595) (by norm_num)
theorem B1972277 : Blo 1313975 1972277 := bbase (se 5 (by rfl) ⟨92450, by rfl⟩ : syracuseStep 1972277 = 184901) (by norm_num)
theorem B1579081 : Blo 1313975 1579081 := bbase (se 2 (by rfl) ⟨592155, by rfl⟩ : syracuseStep 1579081 = 1184311) (by norm_num)
theorem B1972301 : Blo 1313975 1972301 := bbase (se 3 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 1972301 = 739613) (by norm_num)
theorem B1972325 : Blo 1313975 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B3553397 : Blo 1313975 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B2136181 : Blo 1313975 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B1972349 : Blo 1313975 1972349 := bbase (se 3 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 1972349 = 739631) (by norm_num)
theorem B2218117 : Blo 1313975 2218117 := bbase (se 4 (by rfl) ⟨207948, by rfl⟩ : syracuseStep 2218117 = 415897) (by norm_num)
theorem B1972373 : Blo 1313975 1972373 := bbase (se 6 (by rfl) ⟨46227, by rfl⟩ : syracuseStep 1972373 = 92455) (by norm_num)
theorem B1972397 : Blo 1313975 1972397 := bbase (se 3 (by rfl) ⟨369824, by rfl⟩ : syracuseStep 1972397 = 739649) (by norm_num)
theorem B1972421 : Blo 1313975 1972421 := bbase (se 4 (by rfl) ⟨184914, by rfl⟩ : syracuseStep 1972421 = 369829) (by norm_num)
theorem B22771925 : Blo 1313975 22771925 := bbase (se 7 (by rfl) ⟨266858, by rfl⟩ : syracuseStep 22771925 = 533717) (by norm_num)
theorem B1579225 : Blo 1313975 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B2218205 : Blo 1313975 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B1972445 : Blo 1313975 1972445 := bbase (se 3 (by rfl) ⟨369833, by rfl⟩ : syracuseStep 1972445 = 739667) (by norm_num)
theorem B1972469 : Blo 1313975 1972469 := bbase (se 5 (by rfl) ⟨92459, by rfl⟩ : syracuseStep 1972469 = 184919) (by norm_num)
theorem B2496757 : Blo 1313975 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B1972493 : Blo 1313975 1972493 := bbase (se 3 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 1972493 = 739685) (by norm_num)
theorem B1333517 : Blo 1313975 1333517 := bbase (se 3 (by rfl) ⟨250034, by rfl⟩ : syracuseStep 1333517 = 500069) (by norm_num)
theorem B2808101 : Blo 1313975 2808101 := bbase (se 4 (by rfl) ⟨263259, by rfl⟩ : syracuseStep 2808101 = 526519) (by norm_num)
theorem B1972517 : Blo 1313975 1972517 := bbase (se 4 (by rfl) ⟨184923, by rfl⟩ : syracuseStep 1972517 = 369847) (by norm_num)
theorem B1972541 : Blo 1313975 1972541 := bbase (se 3 (by rfl) ⟨369851, by rfl⟩ : syracuseStep 1972541 = 739703) (by norm_num)
theorem B1972565 : Blo 1313975 1972565 := bbase (se 10 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 1972565 = 5779) (by norm_num)
theorem B2218333 : Blo 1313975 2218333 := bbase (se 3 (by rfl) ⟨415937, by rfl⟩ : syracuseStep 2218333 = 831875) (by norm_num)
theorem B3160421 : Blo 1313975 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B1972589 : Blo 1313975 1972589 := bbase (se 3 (by rfl) ⟨369860, by rfl⟩ : syracuseStep 1972589 = 739721) (by norm_num)
theorem B6322549 : Blo 1313975 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B1972613 : Blo 1313975 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B2496901 : Blo 1313975 2496901 := bbase (se 4 (by rfl) ⟨234084, by rfl⟩ : syracuseStep 2496901 = 468169) (by norm_num)
theorem B4438421 : Blo 1313975 4438421 := bbase (se 6 (by rfl) ⟨104025, by rfl⟩ : syracuseStep 4438421 = 208051) (by norm_num)
theorem B1423765 : Blo 1313975 1423765 := bbase (se 6 (by rfl) ⟨33369, by rfl⟩ : syracuseStep 1423765 = 66739) (by norm_num)
theorem B1972637 : Blo 1313975 1972637 := bbase (se 3 (by rfl) ⟨369869, by rfl⟩ : syracuseStep 1972637 = 739739) (by norm_num)
theorem B2218421 : Blo 1313975 2218421 := bbase (se 5 (by rfl) ⟨103988, by rfl⟩ : syracuseStep 2218421 = 207977) (by norm_num)
theorem B2808245 : Blo 1313975 2808245 := bbase (se 5 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 2808245 = 263273) (by norm_num)
theorem B1972661 : Blo 1313975 1972661 := bbase (se 5 (by rfl) ⟨92468, by rfl⟩ : syracuseStep 1972661 = 184937) (by norm_num)
theorem B1972685 : Blo 1313975 1972685 := bbase (se 3 (by rfl) ⟨369878, by rfl⟩ : syracuseStep 1972685 = 739757) (by norm_num)
theorem B1972709 : Blo 1313975 1972709 := bbase (se 4 (by rfl) ⟨184941, by rfl⟩ : syracuseStep 1972709 = 369883) (by norm_num)
theorem B1972733 : Blo 1313975 1972733 := bbase (se 3 (by rfl) ⟨369887, by rfl⟩ : syracuseStep 1972733 = 739775) (by norm_num)
theorem B1686029 : Blo 1313975 1686029 := bbase (se 3 (by rfl) ⟨316130, by rfl⟩ : syracuseStep 1686029 = 632261) (by norm_num)
theorem B1972757 : Blo 1313975 1972757 := bbase (se 6 (by rfl) ⟨46236, by rfl⟩ : syracuseStep 1972757 = 92473) (by norm_num)
theorem B2497061 : Blo 1313975 2497061 := bbase (se 4 (by rfl) ⟨234099, by rfl⟩ : syracuseStep 2497061 = 468199) (by norm_num)
theorem B1972781 : Blo 1313975 1972781 := bbase (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) (by norm_num)
theorem B2218549 : Blo 1313975 2218549 := bbase (se 5 (by rfl) ⟨103994, by rfl⟩ : syracuseStep 2218549 = 207989) (by norm_num)
theorem B1972805 : Blo 1313975 1972805 := bbase (se 4 (by rfl) ⟨184950, by rfl⟩ : syracuseStep 1972805 = 369901) (by norm_num)
theorem B1972829 : Blo 1313975 1972829 := bbase (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) (by norm_num)
theorem B1972853 : Blo 1313975 1972853 := bbase (se 5 (by rfl) ⟨92477, by rfl⟩ : syracuseStep 1972853 = 184955) (by norm_num)
theorem B4995701 : Blo 1313975 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B2218637 : Blo 1313975 2218637 := bbase (se 3 (by rfl) ⟨415994, by rfl⟩ : syracuseStep 2218637 = 831989) (by norm_num)
theorem B1972877 : Blo 1313975 1972877 := bbase (se 3 (by rfl) ⟨369914, by rfl⟩ : syracuseStep 1972877 = 739829) (by norm_num)
theorem B1972901 : Blo 1313975 1972901 := bbase (se 4 (by rfl) ⟨184959, by rfl⟩ : syracuseStep 1972901 = 369919) (by norm_num)
theorem B2497205 : Blo 1313975 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B3160757 : Blo 1313975 3160757 := bbase (se 5 (by rfl) ⟨148160, by rfl⟩ : syracuseStep 3160757 = 296321) (by norm_num)
theorem B1972925 : Blo 1313975 1972925 := bbase (se 3 (by rfl) ⟨369923, by rfl⟩ : syracuseStep 1972925 = 739847) (by norm_num)
theorem B1972949 : Blo 1313975 1972949 := bbase (se 7 (by rfl) ⟨23120, by rfl⟩ : syracuseStep 1972949 = 46241) (by norm_num)
theorem B1972973 : Blo 1313975 1972973 := bbase (se 3 (by rfl) ⟨369932, by rfl⟩ : syracuseStep 1972973 = 739865) (by norm_num)
theorem B5331701 : Blo 1313975 5331701 := bbase (se 5 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 5331701 = 499847) (by norm_num)
theorem B1972997 : Blo 1313975 1972997 := bbase (se 4 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 1972997 = 369937) (by norm_num)
theorem B2218765 : Blo 1313975 2218765 := bbase (se 3 (by rfl) ⟨416018, by rfl⟩ : syracuseStep 2218765 = 832037) (by norm_num)
theorem B3160853 : Blo 1313975 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B1973021 : Blo 1313975 1973021 := bbase (se 3 (by rfl) ⟨369941, by rfl⟩ : syracuseStep 1973021 = 739883) (by norm_num)
theorem B1973045 : Blo 1313975 1973045 := bbase (se 5 (by rfl) ⟨92486, by rfl⟩ : syracuseStep 1973045 = 184973) (by norm_num)
theorem B4438853 : Blo 1313975 4438853 := bbase (se 4 (by rfl) ⟨416142, by rfl⟩ : syracuseStep 4438853 = 832285) (by norm_num)
theorem B1973069 : Blo 1313975 1973069 := bbase (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) (by norm_num)
theorem B2218853 : Blo 1313975 2218853 := bbase (se 4 (by rfl) ⟨208017, by rfl⟩ : syracuseStep 2218853 = 416035) (by norm_num)
theorem B1973093 : Blo 1313975 1973093 := bbase (se 4 (by rfl) ⟨184977, by rfl⟩ : syracuseStep 1973093 = 369955) (by norm_num)
theorem B1973117 : Blo 1313975 1973117 := bbase (se 3 (by rfl) ⟨369959, by rfl⟩ : syracuseStep 1973117 = 739919) (by norm_num)
theorem B1973141 : Blo 1313975 1973141 := bbase (se 6 (by rfl) ⟨46245, by rfl⟩ : syracuseStep 1973141 = 92491) (by norm_num)
theorem B4995989 : Blo 1313975 4995989 := bbase (se 6 (by rfl) ⟨117093, by rfl⟩ : syracuseStep 4995989 = 234187) (by norm_num)
theorem B1973165 : Blo 1313975 1973165 := bbase (se 3 (by rfl) ⟨369968, by rfl⟩ : syracuseStep 1973165 = 739937) (by norm_num)
theorem B1973189 : Blo 1313975 1973189 := bbase (se 4 (by rfl) ⟨184986, by rfl⟩ : syracuseStep 1973189 = 369973) (by norm_num)
theorem B2497493 : Blo 1313975 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B3161045 : Blo 1313975 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B1973213 : Blo 1313975 1973213 := bbase (se 3 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 1973213 = 739955) (by norm_num)
theorem B2218981 : Blo 1313975 2218981 := bbase (se 4 (by rfl) ⟨208029, by rfl⟩ : syracuseStep 2218981 = 416059) (by norm_num)
theorem B1973237 : Blo 1313975 1973237 := bbase (se 5 (by rfl) ⟨92495, by rfl⟩ : syracuseStep 1973237 = 184991) (by norm_num)
theorem B1973261 : Blo 1313975 1973261 := bbase (se 3 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 1973261 = 739973) (by norm_num)
theorem B1973285 : Blo 1313975 1973285 := bbase (se 4 (by rfl) ⟨184995, by rfl⟩ : syracuseStep 1973285 = 369991) (by norm_num)
theorem B2219069 : Blo 1313975 2219069 := bbase (se 3 (by rfl) ⟨416075, by rfl⟩ : syracuseStep 2219069 = 832151) (by norm_num)
theorem B1973309 : Blo 1313975 1973309 := bbase (se 3 (by rfl) ⟨369995, by rfl⟩ : syracuseStep 1973309 = 739991) (by norm_num)
theorem B1997893 : Blo 1313975 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B1973333 : Blo 1313975 1973333 := bbase (se 8 (by rfl) ⟨11562, by rfl⟩ : syracuseStep 1973333 = 23125) (by norm_num)
theorem B1973357 : Blo 1313975 1973357 := bbase (se 3 (by rfl) ⟨370004, by rfl⟩ : syracuseStep 1973357 = 740009) (by norm_num)
theorem B2497645 : Blo 1313975 2497645 := bbase (se 3 (by rfl) ⟨468308, by rfl⟩ : syracuseStep 2497645 = 936617) (by norm_num)
theorem B1973381 : Blo 1313975 1973381 := bbase (se 4 (by rfl) ⟨185004, by rfl⟩ : syracuseStep 1973381 = 370009) (by norm_num)
theorem B2956445 : Blo 1313975 2956445 := bbase (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) (by norm_num)
theorem B2808989 : Blo 1313975 2808989 := bbase (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) (by norm_num)
theorem B1973405 : Blo 1313975 1973405 := bbase (se 3 (by rfl) ⟨370013, by rfl⟩ : syracuseStep 1973405 = 740027) (by norm_num)
theorem B1973429 : Blo 1313975 1973429 := bbase (se 5 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 1973429 = 185009) (by norm_num)
theorem B2219197 : Blo 1313975 2219197 := bbase (se 3 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 2219197 = 832199) (by norm_num)
theorem B1973453 : Blo 1313975 1973453 := bbase (se 3 (by rfl) ⟨370022, by rfl⟩ : syracuseStep 1973453 = 740045) (by norm_num)
theorem B2956517 : Blo 1313975 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B3742949 : Blo 1313975 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B1973477 : Blo 1313975 1973477 := bbase (se 4 (by rfl) ⟨185013, by rfl⟩ : syracuseStep 1973477 = 370027) (by norm_num)
theorem B4439285 : Blo 1313975 4439285 := bbase (se 5 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 4439285 = 416183) (by norm_num)
theorem B1973501 : Blo 1313975 1973501 := bbase (se 3 (by rfl) ⟨370031, by rfl⟩ : syracuseStep 1973501 = 740063) (by norm_num)
theorem B6659333 : Blo 1313975 6659333 := bbase (se 4 (by rfl) ⟨624312, by rfl⟩ : syracuseStep 6659333 = 1248625) (by norm_num)
theorem B2219285 : Blo 1313975 2219285 := bbase (se 6 (by rfl) ⟨52014, by rfl⟩ : syracuseStep 2219285 = 104029) (by norm_num)
theorem B1973525 : Blo 1313975 1973525 := bbase (se 6 (by rfl) ⟨46254, by rfl⟩ : syracuseStep 1973525 = 92509) (by norm_num)
theorem B2956589 : Blo 1313975 2956589 := bbase (se 3 (by rfl) ⟨554360, by rfl⟩ : syracuseStep 2956589 = 1108721) (by norm_num)
theorem B1973549 : Blo 1313975 1973549 := bbase (se 3 (by rfl) ⟨370040, by rfl⟩ : syracuseStep 1973549 = 740081) (by norm_num)
theorem B1973573 : Blo 1313975 1973573 := bbase (se 4 (by rfl) ⟨185022, by rfl⟩ : syracuseStep 1973573 = 370045) (by norm_num)
theorem B1973597 : Blo 1313975 1973597 := bbase (se 3 (by rfl) ⟨370049, by rfl⟩ : syracuseStep 1973597 = 740099) (by norm_num)
theorem B2956661 : Blo 1313975 2956661 := bbase (se 5 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 2956661 = 277187) (by norm_num)
theorem B1973621 : Blo 1313975 1973621 := bbase (se 5 (by rfl) ⟨92513, by rfl⟩ : syracuseStep 1973621 = 185027) (by norm_num)
theorem B1973645 : Blo 1313975 1973645 := bbase (se 3 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 1973645 = 740117) (by norm_num)
theorem B1777045 : Blo 1313975 1777045 := bbase (se 6 (by rfl) ⟨41649, by rfl⟩ : syracuseStep 1777045 = 83299) (by norm_num)
theorem B2219413 : Blo 1313975 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B4742549 : Blo 1313975 4742549 := bbase (se 6 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 4742549 = 222307) (by norm_num)
theorem B2497949 : Blo 1313975 2497949 := bbase (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) (by norm_num)
theorem B1973669 : Blo 1313975 1973669 := bbase (se 4 (by rfl) ⟨185031, by rfl⟩ : syracuseStep 1973669 = 370063) (by norm_num)
theorem B2956733 : Blo 1313975 2956733 := bbase (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) (by norm_num)
theorem B1973693 : Blo 1313975 1973693 := bbase (se 3 (by rfl) ⟨370067, by rfl⟩ : syracuseStep 1973693 = 740135) (by norm_num)
theorem B1973717 : Blo 1313975 1973717 := bbase (se 7 (by rfl) ⟨23129, by rfl⟩ : syracuseStep 1973717 = 46259) (by norm_num)
theorem B2104813 : Blo 1313975 2104813 := bbase (se 3 (by rfl) ⟨394652, by rfl⟩ : syracuseStep 2104813 = 789305) (by norm_num)
theorem B2219501 : Blo 1313975 2219501 := bbase (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) (by norm_num)
theorem B1973741 : Blo 1313975 1973741 := bbase (se 3 (by rfl) ⟨370076, by rfl⟩ : syracuseStep 1973741 = 740153) (by norm_num)
theorem B2956805 : Blo 1313975 2956805 := bbase (se 4 (by rfl) ⟨277200, by rfl⟩ : syracuseStep 2956805 = 554401) (by norm_num)
theorem B1973765 : Blo 1313975 1973765 := bbase (se 4 (by rfl) ⟨185040, by rfl⟩ : syracuseStep 1973765 = 370081) (by norm_num)
theorem B3554837 : Blo 1313975 3554837 := bbase (se 6 (by rfl) ⟨83316, by rfl⟩ : syracuseStep 3554837 = 166633) (by norm_num)
theorem B1973789 : Blo 1313975 1973789 := bbase (se 3 (by rfl) ⟨370085, by rfl⟩ : syracuseStep 1973789 = 740171) (by norm_num)
theorem B1949221 : Blo 1313975 1949221 := bbase (se 4 (by rfl) ⟨182739, by rfl⟩ : syracuseStep 1949221 = 365479) (by norm_num)
theorem B1973813 : Blo 1313975 1973813 := bbase (se 5 (by rfl) ⟨92522, by rfl⟩ : syracuseStep 1973813 = 185045) (by norm_num)
theorem B2956877 : Blo 1313975 2956877 := bbase (se 3 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 2956877 = 1108829) (by norm_num)
theorem B1973837 : Blo 1313975 1973837 := bbase (se 3 (by rfl) ⟨370094, by rfl⟩ : syracuseStep 1973837 = 740189) (by norm_num)
theorem B1973861 : Blo 1313975 1973861 := bbase (se 4 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 1973861 = 370099) (by norm_num)
theorem B2219629 : Blo 1313975 2219629 := bbase (se 3 (by rfl) ⟨416180, by rfl⟩ : syracuseStep 2219629 = 832361) (by norm_num)
theorem B1973885 : Blo 1313975 1973885 := bbase (se 3 (by rfl) ⟨370103, by rfl⟩ : syracuseStep 1973885 = 740207) (by norm_num)
theorem B2956949 : Blo 1313975 2956949 := bbase (se 6 (by rfl) ⟨69303, by rfl⟩ : syracuseStep 2956949 = 138607) (by norm_num)
theorem B1973909 : Blo 1313975 1973909 := bbase (se 6 (by rfl) ⟨46263, by rfl⟩ : syracuseStep 1973909 = 92527) (by norm_num)
theorem B2997917 : Blo 1313975 2997917 := bbase (se 3 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 2997917 = 1124219) (by norm_num)
theorem B4439717 : Blo 1313975 4439717 := bbase (se 4 (by rfl) ⟨416223, by rfl⟩ : syracuseStep 4439717 = 832447) (by norm_num)
theorem B1973933 : Blo 1313975 1973933 := bbase (se 3 (by rfl) ⟨370112, by rfl⟩ : syracuseStep 1973933 = 740225) (by norm_num)
theorem B3374789 : Blo 1313975 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B2219717 : Blo 1313975 2219717 := bbase (se 4 (by rfl) ⟨208098, by rfl⟩ : syracuseStep 2219717 = 416197) (by norm_num)
theorem B1973957 : Blo 1313975 1973957 := bbase (se 4 (by rfl) ⟨185058, by rfl⟩ : syracuseStep 1973957 = 370117) (by norm_num)
theorem B1580753 : Blo 1313975 1580753 := bbase (se 2 (by rfl) ⟨592782, by rfl⟩ : syracuseStep 1580753 = 1185565) (by norm_num)
theorem B2957021 : Blo 1313975 2957021 := bbase (se 3 (by rfl) ⟨554441, by rfl⟩ : syracuseStep 2957021 = 1108883) (by norm_num)
theorem B2957093 : Blo 1313975 2957093 := bbase (se 4 (by rfl) ⟨277227, by rfl⟩ : syracuseStep 2957093 = 554455) (by norm_num)
theorem B2219845 : Blo 1313975 2219845 := bbase (se 4 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 2219845 = 416221) (by norm_num)
theorem B2957165 : Blo 1313975 2957165 := bbase (se 3 (by rfl) ⟨554468, by rfl⟩ : syracuseStep 2957165 = 1108937) (by norm_num)
theorem B3743621 : Blo 1313975 3743621 := bbase (se 4 (by rfl) ⟨350964, by rfl⟩ : syracuseStep 3743621 = 701929) (by norm_num)
theorem B2809741 : Blo 1313975 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B2219933 : Blo 1313975 2219933 := bbase (se 3 (by rfl) ⟨416237, by rfl⟩ : syracuseStep 2219933 = 832475) (by norm_num)
theorem B2957237 : Blo 1313975 2957237 := bbase (se 5 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 2957237 = 277241) (by norm_num)
theorem B4210613 : Blo 1313975 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B1351625 : Blo 1313975 1351625 := bbase (se 2 (by rfl) ⟨506859, by rfl⟩ : syracuseStep 1351625 = 1013719) (by norm_num)
theorem B2957309 : Blo 1313975 2957309 := bbase (se 3 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 2957309 = 1108991) (by norm_num)
theorem B9601037 : Blo 1313975 9601037 := bstep (se 3 (by rfl) ⟨1800194, by rfl⟩ : syracuseStep 9601037 = 3600389) B3600389
theorem B2220115 : Blo 1313975 2220115 := bstep (se 1 (by rfl) ⟨1665086, by rfl⟩ : syracuseStep 2220115 = 3330173) B3330173
theorem B2105441 : Blo 1313975 2105441 := bstep (se 2 (by rfl) ⟨789540, by rfl⟩ : syracuseStep 2105441 = 1579081) B1579081
theorem B5062769 : Blo 1313975 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B14975117 : Blo 1313975 14975117 := bstep (se 3 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 14975117 = 5615669) B5615669
theorem B2957489 : Blo 1313975 2957489 := bstep (se 2 (by rfl) ⟨1109058, by rfl⟩ : syracuseStep 2957489 = 2218117) B2218117
theorem B2957507 : Blo 1313975 2957507 := bstep (se 1 (by rfl) ⟨2218130, by rfl⟩ : syracuseStep 2957507 = 4436261) B4436261
theorem B2220257 : Blo 1313975 2220257 := bstep (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) B1665193
theorem B31998179 : Blo 1313975 31998179 := bstep (se 1 (by rfl) ⟨23998634, by rfl⟩ : syracuseStep 31998179 = 47997269) B47997269
theorem B2105633 : Blo 1313975 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B4440365 : Blo 1313975 4440365 := bstep (se 3 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 4440365 = 1665137) B1665137
theorem B2220385 : Blo 1313975 2220385 := bstep (se 2 (by rfl) ⟨832644, by rfl⟩ : syracuseStep 2220385 = 1665289) B1665289
theorem B4440419 : Blo 1313975 4440419 := bstep (se 1 (by rfl) ⟨3330314, by rfl⟩ : syracuseStep 4440419 = 6660629) B6660629
theorem B2220419 : Blo 1313975 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B1663411 : Blo 1313975 1663411 := bstep (se 1 (by rfl) ⟨1247558, by rfl⟩ : syracuseStep 1663411 = 2495117) B2495117
theorem B3326417 : Blo 1313975 3326417 := bstep (se 2 (by rfl) ⟨1247406, by rfl⟩ : syracuseStep 3326417 = 2494813) B2494813
theorem B2957777 : Blo 1313975 2957777 := bstep (se 2 (by rfl) ⟨1109166, by rfl⟩ : syracuseStep 2957777 = 2218333) B2218333
theorem B2957795 : Blo 1313975 2957795 := bstep (se 1 (by rfl) ⟨2218346, by rfl⟩ : syracuseStep 2957795 = 4436693) B4436693
theorem B8430065 : Blo 1313975 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B3326467 : Blo 1313975 3326467 := bstep (se 1 (by rfl) ⟨2494850, by rfl⟩ : syracuseStep 3326467 = 4989701) B4989701
theorem B2220547 : Blo 1313975 2220547 := bstep (se 1 (by rfl) ⟨1665410, by rfl⟩ : syracuseStep 2220547 = 3330821) B3330821
theorem B1663507 : Blo 1313975 1663507 := bstep (se 1 (by rfl) ⟨1247630, by rfl⟩ : syracuseStep 1663507 = 2495261) B2495261
theorem B2998865 : Blo 1313975 2998865 := bstep (se 2 (by rfl) ⟨1124574, by rfl⟩ : syracuseStep 2998865 = 2249149) B2249149
theorem B6652529 : Blo 1313975 6652529 := bstep (se 2 (by rfl) ⟨2494698, by rfl⟩ : syracuseStep 6652529 = 4989397) B4989397
theorem B4440689 : Blo 1313975 4440689 := bstep (se 2 (by rfl) ⟨1665258, by rfl⟩ : syracuseStep 4440689 = 3330517) B3330517
theorem B11231885 : Blo 1313975 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B3326609 : Blo 1313975 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2884241 : Blo 1313975 2884241 := bstep (se 2 (by rfl) ⟨1081590, by rfl⟩ : syracuseStep 2884241 = 2163181) B2163181
theorem B2220689 : Blo 1313975 2220689 := bstep (se 2 (by rfl) ⟨832758, by rfl⟩ : syracuseStep 2220689 = 1665517) B1665517
theorem B7488197 : Blo 1313975 7488197 := bstep (se 4 (by rfl) ⟨702018, by rfl⟩ : syracuseStep 7488197 = 1404037) B1404037
theorem B4268749 : Blo 1313975 4268749 := bstep (se 3 (by rfl) ⟨800390, by rfl⟩ : syracuseStep 4268749 = 1600781) B1600781
theorem B3556045 : Blo 1313975 3556045 := bstep (se 3 (by rfl) ⟨666758, by rfl⟩ : syracuseStep 3556045 = 1333517) B1333517
theorem B2958065 : Blo 1313975 2958065 := bstep (se 2 (by rfl) ⟨1109274, by rfl⟩ : syracuseStep 2958065 = 2218549) B2218549
theorem B2958083 : Blo 1313975 2958083 := bstep (se 1 (by rfl) ⟨2218562, by rfl⟩ : syracuseStep 2958083 = 4437125) B4437125
theorem B1999619 : Blo 1313975 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B16851725 : Blo 1313975 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B1499971 : Blo 1313975 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B3744589 : Blo 1313975 3744589 := bstep (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) B1404221
theorem B1778531 : Blo 1313975 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B1778563 : Blo 1313975 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B12977093 : Blo 1313975 12977093 := bstep (se 4 (by rfl) ⟨1216602, by rfl⟩ : syracuseStep 12977093 = 2433205) B2433205
theorem B1664003 : Blo 1313975 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B2958353 : Blo 1313975 2958353 := bstep (se 2 (by rfl) ⟨1109382, by rfl⟩ : syracuseStep 2958353 = 2218765) B2218765
theorem B2958371 : Blo 1313975 2958371 := bstep (se 1 (by rfl) ⟨2218778, by rfl⟩ : syracuseStep 2958371 = 4437557) B4437557
theorem B3376163 : Blo 1313975 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B4441229 : Blo 1313975 4441229 := bstep (se 3 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 4441229 = 1665461) B1665461
theorem B4498595 : Blo 1313975 4498595 := bstep (se 1 (by rfl) ⟨3373946, by rfl⟩ : syracuseStep 4498595 = 6747893) B6747893
theorem B4736177 : Blo 1313975 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B4441283 : Blo 1313975 4441283 := bstep (se 1 (by rfl) ⟨3330962, by rfl⟩ : syracuseStep 4441283 = 6661925) B6661925
theorem B4990157 : Blo 1313975 4990157 := bstep (se 3 (by rfl) ⟨935654, by rfl⟩ : syracuseStep 4990157 = 1871309) B1871309
theorem B9987299 : Blo 1313975 9987299 := bstep (se 1 (by rfl) ⟨7490474, by rfl⟩ : syracuseStep 9987299 = 14980949) B14980949
theorem B2958641 : Blo 1313975 2958641 := bstep (se 2 (by rfl) ⟨1109490, by rfl⟩ : syracuseStep 2958641 = 2218981) B2218981
theorem B2958659 : Blo 1313975 2958659 := bstep (se 1 (by rfl) ⟨2218994, by rfl⟩ : syracuseStep 2958659 = 4437989) B4437989
theorem B5621069 : Blo 1313975 5621069 := bstep (se 3 (by rfl) ⟨1053950, by rfl⟩ : syracuseStep 5621069 = 2107901) B2107901
theorem B7488881 : Blo 1313975 7488881 := bstep (se 2 (by rfl) ⟨2808330, by rfl⟩ : syracuseStep 7488881 = 5616661) B5616661
theorem B2368931 : Blo 1313975 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B2663857 : Blo 1313975 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B15181283 : Blo 1313975 15181283 := bstep (se 1 (by rfl) ⟨11385962, by rfl⟩ : syracuseStep 15181283 = 22771925) B22771925
theorem B3556867 : Blo 1313975 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B2106947 : Blo 1313975 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B2958929 : Blo 1313975 2958929 := bstep (se 2 (by rfl) ⟨1109598, by rfl⟩ : syracuseStep 2958929 = 2219197) B2219197
theorem B2958947 : Blo 1313975 2958947 := bstep (se 1 (by rfl) ⟨2219210, by rfl⟩ : syracuseStep 2958947 = 4438421) B4438421
theorem B3327601 : Blo 1313975 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B11388529 : Blo 1313975 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B1664707 : Blo 1313975 1664707 := bstep (se 1 (by rfl) ⟨1248530, by rfl⟩ : syracuseStep 1664707 = 2497061) B2497061
theorem B5998349 : Blo 1313975 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B1664803 : Blo 1313975 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B2107171 : Blo 1313975 2107171 := bstep (se 1 (by rfl) ⟨1580378, by rfl⟩ : syracuseStep 2107171 = 3160757) B3160757
theorem B2107235 : Blo 1313975 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B2369393 : Blo 1313975 2369393 := bstep (se 2 (by rfl) ⟨888522, by rfl⟩ : syracuseStep 2369393 = 1777045) B1777045
theorem B2959217 : Blo 1313975 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B3327875 : Blo 1313975 3327875 := bstep (se 1 (by rfl) ⟨2495906, by rfl⟩ : syracuseStep 3327875 = 4991813) B4991813
theorem B2959235 : Blo 1313975 2959235 := bstep (se 1 (by rfl) ⟨2219426, by rfl⟩ : syracuseStep 2959235 = 4438853) B4438853
theorem B2107363 : Blo 1313975 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B6653987 : Blo 1313975 6653987 := bstep (se 1 (by rfl) ⟨4990490, by rfl⟩ : syracuseStep 6653987 = 9980981) B9980981
theorem B2598961 : Blo 1313975 2598961 := bstep (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) B1949221
theorem B3328067 : Blo 1313975 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B4212881 : Blo 1313975 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B2959505 : Blo 1313975 2959505 := bstep (se 2 (by rfl) ⟨1109814, by rfl⟩ : syracuseStep 2959505 = 2219629) B2219629
theorem B8538275 : Blo 1313975 8538275 := bstep (se 1 (by rfl) ⟨6403706, by rfl⟩ : syracuseStep 8538275 = 12807413) B12807413
theorem B2959523 : Blo 1313975 2959523 := bstep (se 1 (by rfl) ⟨2219642, by rfl⟩ : syracuseStep 2959523 = 4439285) B4439285
theorem B1665299 : Blo 1313975 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B4213073 : Blo 1313975 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B2369891 : Blo 1313975 2369891 := bstep (se 1 (by rfl) ⟨1777418, by rfl⟩ : syracuseStep 2369891 = 3554837) B3554837
theorem B3000689 : Blo 1313975 3000689 := bstep (se 2 (by rfl) ⟨1125258, by rfl⟩ : syracuseStep 3000689 = 2250517) B2250517
theorem B7588237 : Blo 1313975 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B2959793 : Blo 1313975 2959793 := bstep (se 2 (by rfl) ⟨1109922, by rfl⟩ : syracuseStep 2959793 = 2219845) B2219845
theorem B2959811 : Blo 1313975 2959811 := bstep (se 1 (by rfl) ⟨2219858, by rfl⟩ : syracuseStep 2959811 = 4439717) B4439717
theorem B14969285 : Blo 1313975 14969285 := bstep (se 4 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 14969285 = 2806741) B2806741
theorem B3746321 : Blo 1313975 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B7998065 : Blo 1313975 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B2960081 : Blo 1313975 2960081 := bstep (se 2 (by rfl) ⟨1110030, by rfl⟩ : syracuseStep 2960081 = 2220061) B2220061
theorem B3746513 : Blo 1313975 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B2960099 : Blo 1313975 2960099 := bstep (se 1 (by rfl) ⟨2220074, by rfl⟩ : syracuseStep 2960099 = 4440149) B4440149
theorem B2665219 : Blo 1313975 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B4000529 : Blo 1313975 4000529 := bstep (se 2 (by rfl) ⟨1500198, by rfl⟩ : syracuseStep 4000529 = 3000397) B3000397
theorem B7490339 : Blo 1313975 7490339 := bstep (se 1 (by rfl) ⟨5617754, by rfl⟩ : syracuseStep 7490339 = 11235509) B11235509
theorem B6654797 : Blo 1313975 6654797 := bstep (se 3 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 6654797 = 2495549) B2495549
theorem B2665315 : Blo 1313975 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B2370467 : Blo 1313975 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B14978033 : Blo 1313975 14978033 := bstep (se 2 (by rfl) ⟨5616762, by rfl⟩ : syracuseStep 14978033 = 11233525) B11233525
theorem B3329009 : Blo 1313975 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B2960369 : Blo 1313975 2960369 := bstep (se 2 (by rfl) ⟨1110138, by rfl⟩ : syracuseStep 2960369 = 2220277) B2220277
theorem B2960387 : Blo 1313975 2960387 := bstep (se 1 (by rfl) ⟨2220290, by rfl⟩ : syracuseStep 2960387 = 4440581) B4440581
theorem B3329059 : Blo 1313975 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B3157123 : Blo 1313975 3157123 := bstep (se 1 (by rfl) ⟨2367842, by rfl⟩ : syracuseStep 3157123 = 4735685) B4735685
theorem B3329201 : Blo 1313975 3329201 := bstep (se 2 (by rfl) ⟨1248450, by rfl⟩ : syracuseStep 3329201 = 2496901) B2496901
theorem B1313987 : Blo 1313975 1313987 := bstep (se 1 (by rfl) ⟨985490, by rfl⟩ : syracuseStep 1313987 = 1970981) B1970981
theorem B1314003 : Blo 1313975 1314003 := bstep (se 1 (by rfl) ⟨985502, by rfl⟩ : syracuseStep 1314003 = 1971005) B1971005
theorem B1314019 : Blo 1313975 1314019 := bstep (se 1 (by rfl) ⟨985514, by rfl⟩ : syracuseStep 1314019 = 1971029) B1971029
theorem B4435181 : Blo 1313975 4435181 := bstep (se 3 (by rfl) ⟨831596, by rfl⟩ : syracuseStep 4435181 = 1663193) B1663193
theorem B1314035 : Blo 1313975 1314035 := bstep (se 1 (by rfl) ⟨985526, by rfl⟩ : syracuseStep 1314035 = 1971053) B1971053
theorem B1314051 : Blo 1313975 1314051 := bstep (se 1 (by rfl) ⟨985538, by rfl⟩ : syracuseStep 1314051 = 1971077) B1971077
theorem B2960657 : Blo 1313975 2960657 := bstep (se 2 (by rfl) ⟨1110246, by rfl⟩ : syracuseStep 2960657 = 2220493) B2220493
theorem B1314067 : Blo 1313975 1314067 := bstep (se 1 (by rfl) ⟨985550, by rfl⟩ : syracuseStep 1314067 = 1971101) B1971101
theorem B1314083 : Blo 1313975 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B4435235 : Blo 1313975 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B2960675 : Blo 1313975 2960675 := bstep (se 1 (by rfl) ⟨2220506, by rfl⟩ : syracuseStep 2960675 = 4441013) B4441013
theorem B1314099 : Blo 1313975 1314099 := bstep (se 1 (by rfl) ⟨985574, by rfl⟩ : syracuseStep 1314099 = 1971149) B1971149
theorem B1314115 : Blo 1313975 1314115 := bstep (se 1 (by rfl) ⟨985586, by rfl⟩ : syracuseStep 1314115 = 1971173) B1971173
theorem B7114061 : Blo 1313975 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B1314131 : Blo 1313975 1314131 := bstep (se 1 (by rfl) ⟨985598, by rfl⟩ : syracuseStep 1314131 = 1971197) B1971197
theorem B1871201 : Blo 1313975 1871201 := bstep (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) B1403401
theorem B1314147 : Blo 1313975 1314147 := bstep (se 1 (by rfl) ⟨985610, by rfl⟩ : syracuseStep 1314147 = 1971221) B1971221
theorem B1404259 : Blo 1313975 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B1314163 : Blo 1313975 1314163 := bstep (se 1 (by rfl) ⟨985622, by rfl⟩ : syracuseStep 1314163 = 1971245) B1971245
theorem B1314179 : Blo 1313975 1314179 := bstep (se 1 (by rfl) ⟨985634, by rfl⟩ : syracuseStep 1314179 = 1971269) B1971269
theorem B3157393 : Blo 1313975 3157393 := bstep (se 2 (by rfl) ⟨1184022, by rfl⟩ : syracuseStep 3157393 = 2368045) B2368045
theorem B1314195 : Blo 1313975 1314195 := bstep (se 1 (by rfl) ⟨985646, by rfl⟩ : syracuseStep 1314195 = 1971293) B1971293
theorem B1314211 : Blo 1313975 1314211 := bstep (se 1 (by rfl) ⟨985658, by rfl⟩ : syracuseStep 1314211 = 1971317) B1971317
theorem B1314227 : Blo 1313975 1314227 := bstep (se 1 (by rfl) ⟨985670, by rfl⟩ : syracuseStep 1314227 = 1971341) B1971341
theorem B1314243 : Blo 1313975 1314243 := bstep (se 1 (by rfl) ⟨985682, by rfl⟩ : syracuseStep 1314243 = 1971365) B1971365
theorem B18943429 : Blo 1313975 18943429 := bstep (se 4 (by rfl) ⟨1775946, by rfl⟩ : syracuseStep 18943429 = 3551893) B3551893
theorem B1314259 : Blo 1313975 1314259 := bstep (se 1 (by rfl) ⟨985694, by rfl⟩ : syracuseStep 1314259 = 1971389) B1971389
theorem B1314275 : Blo 1313975 1314275 := bstep (se 1 (by rfl) ⟨985706, by rfl⟩ : syracuseStep 1314275 = 1971413) B1971413
theorem B1314291 : Blo 1313975 1314291 := bstep (se 1 (by rfl) ⟨985718, by rfl⟩ : syracuseStep 1314291 = 1971437) B1971437
theorem B1314307 : Blo 1313975 1314307 := bstep (se 1 (by rfl) ⟨985730, by rfl⟩ : syracuseStep 1314307 = 1971461) B1971461
theorem B1314323 : Blo 1313975 1314323 := bstep (se 1 (by rfl) ⟨985742, by rfl⟩ : syracuseStep 1314323 = 1971485) B1971485
theorem B1314339 : Blo 1313975 1314339 := bstep (se 1 (by rfl) ⟨985754, by rfl⟩ : syracuseStep 1314339 = 1971509) B1971509
theorem B4435505 : Blo 1313975 4435505 := bstep (se 2 (by rfl) ⟨1663314, by rfl⟩ : syracuseStep 4435505 = 3326629) B3326629
theorem B2960945 : Blo 1313975 2960945 := bstep (se 2 (by rfl) ⟨1110354, by rfl⟩ : syracuseStep 2960945 = 2220709) B2220709
theorem B1314355 : Blo 1313975 1314355 := bstep (se 1 (by rfl) ⟨985766, by rfl⟩ : syracuseStep 1314355 = 1971533) B1971533
theorem B15994421 : Blo 1313975 15994421 := bstep (se 5 (by rfl) ⟨749738, by rfl⟩ : syracuseStep 15994421 = 1499477) B1499477
theorem B1314371 : Blo 1313975 1314371 := bstep (se 1 (by rfl) ⟨985778, by rfl⟩ : syracuseStep 1314371 = 1971557) B1971557
theorem B1478227 : Blo 1313975 1478227 := bstep (se 1 (by rfl) ⟨1108670, by rfl⟩ : syracuseStep 1478227 = 2217341) B2217341
theorem B1314387 : Blo 1313975 1314387 := bstep (se 1 (by rfl) ⟨985790, by rfl⟩ : syracuseStep 1314387 = 1971581) B1971581
theorem B1314403 : Blo 1313975 1314403 := bstep (se 1 (by rfl) ⟨985802, by rfl⟩ : syracuseStep 1314403 = 1971605) B1971605
theorem B1314419 : Blo 1313975 1314419 := bstep (se 1 (by rfl) ⟨985814, by rfl⟩ : syracuseStep 1314419 = 1971629) B1971629
theorem B1314435 : Blo 1313975 1314435 := bstep (se 1 (by rfl) ⟨985826, by rfl⟩ : syracuseStep 1314435 = 1971653) B1971653
theorem B25636493 : Blo 1313975 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B1314451 : Blo 1313975 1314451 := bstep (se 1 (by rfl) ⟨985838, by rfl⟩ : syracuseStep 1314451 = 1971677) B1971677
theorem B1314467 : Blo 1313975 1314467 := bstep (se 1 (by rfl) ⟨985850, by rfl⟩ : syracuseStep 1314467 = 1971701) B1971701
theorem B1314483 : Blo 1313975 1314483 := bstep (se 1 (by rfl) ⟨985862, by rfl⟩ : syracuseStep 1314483 = 1971725) B1971725
theorem B1314499 : Blo 1313975 1314499 := bstep (se 1 (by rfl) ⟨985874, by rfl⟩ : syracuseStep 1314499 = 1971749) B1971749
theorem B9875141 : Blo 1313975 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B1314515 : Blo 1313975 1314515 := bstep (se 1 (by rfl) ⟨985886, by rfl⟩ : syracuseStep 1314515 = 1971773) B1971773
theorem B1478371 : Blo 1313975 1478371 := bstep (se 1 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 1478371 = 2217557) B2217557
theorem B1314531 : Blo 1313975 1314531 := bstep (se 1 (by rfl) ⟨985898, by rfl⟩ : syracuseStep 1314531 = 1971797) B1971797
theorem B1314547 : Blo 1313975 1314547 := bstep (se 1 (by rfl) ⟨985910, by rfl⟩ : syracuseStep 1314547 = 1971821) B1971821
theorem B1314563 : Blo 1313975 1314563 := bstep (se 1 (by rfl) ⟨985922, by rfl⟩ : syracuseStep 1314563 = 1971845) B1971845
theorem B1314579 : Blo 1313975 1314579 := bstep (se 1 (by rfl) ⟨985934, by rfl⟩ : syracuseStep 1314579 = 1971869) B1971869
theorem B1314595 : Blo 1313975 1314595 := bstep (se 1 (by rfl) ⟨985946, by rfl⟩ : syracuseStep 1314595 = 1971893) B1971893
theorem B1314611 : Blo 1313975 1314611 := bstep (se 1 (by rfl) ⟨985958, by rfl⟩ : syracuseStep 1314611 = 1971917) B1971917
theorem B1314627 : Blo 1313975 1314627 := bstep (se 1 (by rfl) ⟨985970, by rfl⟩ : syracuseStep 1314627 = 1971941) B1971941
theorem B1314643 : Blo 1313975 1314643 := bstep (se 1 (by rfl) ⟨985982, by rfl⟩ : syracuseStep 1314643 = 1971965) B1971965
theorem B1314659 : Blo 1313975 1314659 := bstep (se 1 (by rfl) ⟨985994, by rfl⟩ : syracuseStep 1314659 = 1971989) B1971989
theorem B2666353 : Blo 1313975 2666353 := bstep (se 2 (by rfl) ⟨999882, by rfl⟩ : syracuseStep 2666353 = 1999765) B1999765
theorem B1478515 : Blo 1313975 1478515 := bstep (se 1 (by rfl) ⟨1108886, by rfl⟩ : syracuseStep 1478515 = 2217773) B2217773
theorem B1314675 : Blo 1313975 1314675 := bstep (se 1 (by rfl) ⟨986006, by rfl⟩ : syracuseStep 1314675 = 1972013) B1972013
theorem B1314691 : Blo 1313975 1314691 := bstep (se 1 (by rfl) ⟨986018, by rfl⟩ : syracuseStep 1314691 = 1972037) B1972037
theorem B1314707 : Blo 1313975 1314707 := bstep (se 1 (by rfl) ⟨986030, by rfl⟩ : syracuseStep 1314707 = 1972061) B1972061
theorem B1314723 : Blo 1313975 1314723 := bstep (se 1 (by rfl) ⟨986042, by rfl⟩ : syracuseStep 1314723 = 1972085) B1972085
theorem B1314739 : Blo 1313975 1314739 := bstep (se 1 (by rfl) ⟨986054, by rfl⟩ : syracuseStep 1314739 = 1972109) B1972109
theorem B2248643 : Blo 1313975 2248643 := bstep (se 1 (by rfl) ⟨1686482, by rfl⟩ : syracuseStep 2248643 = 3372965) B3372965
theorem B1314755 : Blo 1313975 1314755 := bstep (se 1 (by rfl) ⟨986066, by rfl⟩ : syracuseStep 1314755 = 1972133) B1972133
theorem B3157969 : Blo 1313975 3157969 := bstep (se 2 (by rfl) ⟨1184238, by rfl⟩ : syracuseStep 3157969 = 2368477) B2368477
theorem B1314771 : Blo 1313975 1314771 := bstep (se 1 (by rfl) ⟨986078, by rfl⟩ : syracuseStep 1314771 = 1972157) B1972157
theorem B1314787 : Blo 1313975 1314787 := bstep (se 1 (by rfl) ⟨986090, by rfl⟩ : syracuseStep 1314787 = 1972181) B1972181
theorem B1314803 : Blo 1313975 1314803 := bstep (se 1 (by rfl) ⟨986102, by rfl⟩ : syracuseStep 1314803 = 1972205) B1972205
theorem B1478659 : Blo 1313975 1478659 := bstep (se 1 (by rfl) ⟨1108994, by rfl⟩ : syracuseStep 1478659 = 2217989) B2217989
theorem B1314819 : Blo 1313975 1314819 := bstep (se 1 (by rfl) ⟨986114, by rfl⟩ : syracuseStep 1314819 = 1972229) B1972229
theorem B1314835 : Blo 1313975 1314835 := bstep (se 1 (by rfl) ⟨986126, by rfl⟩ : syracuseStep 1314835 = 1972253) B1972253
theorem B1314851 : Blo 1313975 1314851 := bstep (se 1 (by rfl) ⟨986138, by rfl⟩ : syracuseStep 1314851 = 1972277) B1972277
theorem B4993073 : Blo 1313975 4993073 := bstep (se 2 (by rfl) ⟨1872402, by rfl⟩ : syracuseStep 4993073 = 3744805) B3744805
theorem B1314867 : Blo 1313975 1314867 := bstep (se 1 (by rfl) ⟨986150, by rfl⟩ : syracuseStep 1314867 = 1972301) B1972301
theorem B1314883 : Blo 1313975 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B4436045 : Blo 1313975 4436045 := bstep (se 3 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 4436045 = 1663517) B1663517
theorem B1314899 : Blo 1313975 1314899 := bstep (se 1 (by rfl) ⟨986174, by rfl⟩ : syracuseStep 1314899 = 1972349) B1972349
theorem B1314915 : Blo 1313975 1314915 := bstep (se 1 (by rfl) ⟨986186, by rfl⟩ : syracuseStep 1314915 = 1972373) B1972373
theorem B2494577 : Blo 1313975 2494577 := bstep (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) B1870933
theorem B1314931 : Blo 1313975 1314931 := bstep (se 1 (by rfl) ⟨986198, by rfl⟩ : syracuseStep 1314931 = 1972397) B1972397
theorem B4436099 : Blo 1313975 4436099 := bstep (se 1 (by rfl) ⟨3327074, by rfl⟩ : syracuseStep 4436099 = 6654149) B6654149
theorem B1314947 : Blo 1313975 1314947 := bstep (se 1 (by rfl) ⟨986210, by rfl⟩ : syracuseStep 1314947 = 1972421) B1972421
theorem B3330193 : Blo 1313975 3330193 := bstep (se 2 (by rfl) ⟨1248822, by rfl⟩ : syracuseStep 3330193 = 2497645) B2497645
theorem B1478803 : Blo 1313975 1478803 := bstep (se 1 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 1478803 = 2218205) B2218205
theorem B1314963 : Blo 1313975 1314963 := bstep (se 1 (by rfl) ⟨986222, by rfl⟩ : syracuseStep 1314963 = 1972445) B1972445
theorem B1314979 : Blo 1313975 1314979 := bstep (se 1 (by rfl) ⟨986234, by rfl⟩ : syracuseStep 1314979 = 1972469) B1972469
theorem B1314995 : Blo 1313975 1314995 := bstep (se 1 (by rfl) ⟨986246, by rfl⟩ : syracuseStep 1314995 = 1972493) B1972493
theorem B1872067 : Blo 1313975 1872067 := bstep (se 1 (by rfl) ⟨1404050, by rfl⟩ : syracuseStep 1872067 = 2808101) B2808101
theorem B1315011 : Blo 1313975 1315011 := bstep (se 1 (by rfl) ⟨986258, by rfl⟩ : syracuseStep 1315011 = 1972517) B1972517
theorem B1315027 : Blo 1313975 1315027 := bstep (se 1 (by rfl) ⟨986270, by rfl⟩ : syracuseStep 1315027 = 1972541) B1972541
theorem B1315043 : Blo 1313975 1315043 := bstep (se 1 (by rfl) ⟨986282, by rfl⟩ : syracuseStep 1315043 = 1972565) B1972565
theorem B1315059 : Blo 1313975 1315059 := bstep (se 1 (by rfl) ⟨986294, by rfl⟩ : syracuseStep 1315059 = 1972589) B1972589
theorem B1315075 : Blo 1313975 1315075 := bstep (se 1 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 1315075 = 1972613) B1972613
theorem B1315091 : Blo 1313975 1315091 := bstep (se 1 (by rfl) ⟨986318, by rfl⟩ : syracuseStep 1315091 = 1972637) B1972637
theorem B1478947 : Blo 1313975 1478947 := bstep (se 1 (by rfl) ⟨1109210, by rfl⟩ : syracuseStep 1478947 = 2218421) B2218421
theorem B1872163 : Blo 1313975 1872163 := bstep (se 1 (by rfl) ⟨1404122, by rfl⟩ : syracuseStep 1872163 = 2808245) B2808245
theorem B1315107 : Blo 1313975 1315107 := bstep (se 1 (by rfl) ⟨986330, by rfl⟩ : syracuseStep 1315107 = 1972661) B1972661
theorem B1315123 : Blo 1313975 1315123 := bstep (se 1 (by rfl) ⟨986342, by rfl⟩ : syracuseStep 1315123 = 1972685) B1972685
theorem B1315139 : Blo 1313975 1315139 := bstep (se 1 (by rfl) ⟨986354, by rfl⟩ : syracuseStep 1315139 = 1972709) B1972709
theorem B3158353 : Blo 1313975 3158353 := bstep (se 2 (by rfl) ⟨1184382, by rfl⟩ : syracuseStep 3158353 = 2368765) B2368765
theorem B1315155 : Blo 1313975 1315155 := bstep (se 1 (by rfl) ⟨986366, by rfl⟩ : syracuseStep 1315155 = 1972733) B1972733
theorem B1315171 : Blo 1313975 1315171 := bstep (se 1 (by rfl) ⟨986378, by rfl⟩ : syracuseStep 1315171 = 1972757) B1972757
theorem B1315187 : Blo 1313975 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B1315203 : Blo 1313975 1315203 := bstep (se 1 (by rfl) ⟨986402, by rfl⟩ : syracuseStep 1315203 = 1972805) B1972805
theorem B4436369 : Blo 1313975 4436369 := bstep (se 2 (by rfl) ⟨1663638, by rfl⟩ : syracuseStep 4436369 = 3327277) B3327277
theorem B1315219 : Blo 1313975 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B1315235 : Blo 1313975 1315235 := bstep (se 1 (by rfl) ⟨986426, by rfl⟩ : syracuseStep 1315235 = 1972853) B1972853
theorem B3330467 : Blo 1313975 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B1479091 : Blo 1313975 1479091 := bstep (se 1 (by rfl) ⟨1109318, by rfl⟩ : syracuseStep 1479091 = 2218637) B2218637
theorem B1315251 : Blo 1313975 1315251 := bstep (se 1 (by rfl) ⟨986438, by rfl⟩ : syracuseStep 1315251 = 1972877) B1972877
theorem B1315267 : Blo 1313975 1315267 := bstep (se 1 (by rfl) ⟨986450, by rfl⟩ : syracuseStep 1315267 = 1972901) B1972901
theorem B1315283 : Blo 1313975 1315283 := bstep (se 1 (by rfl) ⟨986462, by rfl⟩ : syracuseStep 1315283 = 1972925) B1972925
theorem B1315299 : Blo 1313975 1315299 := bstep (se 1 (by rfl) ⟨986474, by rfl⟩ : syracuseStep 1315299 = 1972949) B1972949
theorem B1315315 : Blo 1313975 1315315 := bstep (se 1 (by rfl) ⟨986486, by rfl⟩ : syracuseStep 1315315 = 1972973) B1972973
theorem B1315331 : Blo 1313975 1315331 := bstep (se 1 (by rfl) ⟨986498, by rfl⟩ : syracuseStep 1315331 = 1972997) B1972997
theorem B8999437 : Blo 1313975 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B1315347 : Blo 1313975 1315347 := bstep (se 1 (by rfl) ⟨986510, by rfl⟩ : syracuseStep 1315347 = 1973021) B1973021
theorem B1315363 : Blo 1313975 1315363 := bstep (se 1 (by rfl) ⟨986522, by rfl⟩ : syracuseStep 1315363 = 1973045) B1973045
theorem B4215341 : Blo 1313975 4215341 := bstep (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) B1580753
theorem B1315379 : Blo 1313975 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B1479235 : Blo 1313975 1479235 := bstep (se 1 (by rfl) ⟨1109426, by rfl⟩ : syracuseStep 1479235 = 2218853) B2218853
theorem B1315395 : Blo 1313975 1315395 := bstep (se 1 (by rfl) ⟨986546, by rfl⟩ : syracuseStep 1315395 = 1973093) B1973093
theorem B1315411 : Blo 1313975 1315411 := bstep (se 1 (by rfl) ⟨986558, by rfl⟩ : syracuseStep 1315411 = 1973117) B1973117
theorem B1315427 : Blo 1313975 1315427 := bstep (se 1 (by rfl) ⟨986570, by rfl⟩ : syracuseStep 1315427 = 1973141) B1973141
theorem B3330659 : Blo 1313975 3330659 := bstep (se 1 (by rfl) ⟨2497994, by rfl⟩ : syracuseStep 3330659 = 4995989) B4995989
theorem B1315443 : Blo 1313975 1315443 := bstep (se 1 (by rfl) ⟨986582, by rfl⟩ : syracuseStep 1315443 = 1973165) B1973165
theorem B1315459 : Blo 1313975 1315459 := bstep (se 1 (by rfl) ⟨986594, by rfl⟩ : syracuseStep 1315459 = 1973189) B1973189
theorem B14217869 : Blo 1313975 14217869 := bstep (se 3 (by rfl) ⟨2665850, by rfl⟩ : syracuseStep 14217869 = 5331701) B5331701
theorem B2806417 : Blo 1313975 2806417 := bstep (se 2 (by rfl) ⟨1052406, by rfl⟩ : syracuseStep 2806417 = 2104813) B2104813
theorem B1315475 : Blo 1313975 1315475 := bstep (se 1 (by rfl) ⟨986606, by rfl⟩ : syracuseStep 1315475 = 1973213) B1973213
theorem B1315491 : Blo 1313975 1315491 := bstep (se 1 (by rfl) ⟨986618, by rfl⟩ : syracuseStep 1315491 = 1973237) B1973237
theorem B1315507 : Blo 1313975 1315507 := bstep (se 1 (by rfl) ⟨986630, by rfl⟩ : syracuseStep 1315507 = 1973261) B1973261
theorem B1315523 : Blo 1313975 1315523 := bstep (se 1 (by rfl) ⟨986642, by rfl⟩ : syracuseStep 1315523 = 1973285) B1973285
theorem B1479379 : Blo 1313975 1479379 := bstep (se 1 (by rfl) ⟨1109534, by rfl⟩ : syracuseStep 1479379 = 2219069) B2219069
theorem B1315539 : Blo 1313975 1315539 := bstep (se 1 (by rfl) ⟨986654, by rfl⟩ : syracuseStep 1315539 = 1973309) B1973309
theorem B1315555 : Blo 1313975 1315555 := bstep (se 1 (by rfl) ⟨986666, by rfl⟩ : syracuseStep 1315555 = 1973333) B1973333
theorem B1315571 : Blo 1313975 1315571 := bstep (se 1 (by rfl) ⟨986678, by rfl⟩ : syracuseStep 1315571 = 1973357) B1973357
theorem B1315587 : Blo 1313975 1315587 := bstep (se 1 (by rfl) ⟨986690, by rfl⟩ : syracuseStep 1315587 = 1973381) B1973381
theorem B3552013 : Blo 1313975 3552013 := bstep (se 3 (by rfl) ⟨666002, by rfl⟩ : syracuseStep 3552013 = 1332005) B1332005
theorem B1970963 : Blo 1313975 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B1872659 : Blo 1313975 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B1315603 : Blo 1313975 1315603 := bstep (se 1 (by rfl) ⟨986702, by rfl⟩ : syracuseStep 1315603 = 1973405) B1973405
theorem B1315619 : Blo 1313975 1315619 := bstep (se 1 (by rfl) ⟨986714, by rfl⟩ : syracuseStep 1315619 = 1973429) B1973429
theorem B1970993 : Blo 1313975 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B1315635 : Blo 1313975 1315635 := bstep (se 1 (by rfl) ⟨986726, by rfl⟩ : syracuseStep 1315635 = 1973453) B1973453
theorem B1971011 : Blo 1313975 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B2495299 : Blo 1313975 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B1315651 : Blo 1313975 1315651 := bstep (se 1 (by rfl) ⟨986738, by rfl⟩ : syracuseStep 1315651 = 1973477) B1973477
theorem B1315667 : Blo 1313975 1315667 := bstep (se 1 (by rfl) ⟨986750, by rfl⟩ : syracuseStep 1315667 = 1973501) B1973501
theorem B1971041 : Blo 1313975 1971041 := bstep (se 2 (by rfl) ⟨739140, by rfl⟩ : syracuseStep 1971041 = 1478281) B1478281
theorem B1479523 : Blo 1313975 1479523 := bstep (se 1 (by rfl) ⟨1109642, by rfl⟩ : syracuseStep 1479523 = 2219285) B2219285
theorem B1315683 : Blo 1313975 1315683 := bstep (se 1 (by rfl) ⟨986762, by rfl⟩ : syracuseStep 1315683 = 1973525) B1973525
theorem B1971059 : Blo 1313975 1971059 := bstep (se 1 (by rfl) ⟨1478294, by rfl⟩ : syracuseStep 1971059 = 2956589) B2956589
theorem B1315699 : Blo 1313975 1315699 := bstep (se 1 (by rfl) ⟨986774, by rfl⟩ : syracuseStep 1315699 = 1973549) B1973549
theorem B1315715 : Blo 1313975 1315715 := bstep (se 1 (by rfl) ⟨986786, by rfl⟩ : syracuseStep 1315715 = 1973573) B1973573
theorem B1971089 : Blo 1313975 1971089 := bstep (se 2 (by rfl) ⟨739158, by rfl⟩ : syracuseStep 1971089 = 1478317) B1478317
theorem B1315731 : Blo 1313975 1315731 := bstep (se 1 (by rfl) ⟨986798, by rfl⟩ : syracuseStep 1315731 = 1973597) B1973597
theorem B1971107 : Blo 1313975 1971107 := bstep (se 1 (by rfl) ⟨1478330, by rfl⟩ : syracuseStep 1971107 = 2956661) B2956661
theorem B1315747 : Blo 1313975 1315747 := bstep (se 1 (by rfl) ⟨986810, by rfl⟩ : syracuseStep 1315747 = 1973621) B1973621
theorem B4436909 : Blo 1313975 4436909 := bstep (se 3 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 4436909 = 1663841) B1663841
theorem B1315763 : Blo 1313975 1315763 := bstep (se 1 (by rfl) ⟨986822, by rfl⟩ : syracuseStep 1315763 = 1973645) B1973645
theorem B1971137 : Blo 1313975 1971137 := bstep (se 2 (by rfl) ⟨739176, by rfl⟩ : syracuseStep 1971137 = 1478353) B1478353
theorem B1315779 : Blo 1313975 1315779 := bstep (se 1 (by rfl) ⟨986834, by rfl⟩ : syracuseStep 1315779 = 1973669) B1973669
theorem B1971155 : Blo 1313975 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B1315795 : Blo 1313975 1315795 := bstep (se 1 (by rfl) ⟨986846, by rfl⟩ : syracuseStep 1315795 = 1973693) B1973693
theorem B4436963 : Blo 1313975 4436963 := bstep (se 1 (by rfl) ⟨3327722, by rfl⟩ : syracuseStep 4436963 = 6655445) B6655445
theorem B5616611 : Blo 1313975 5616611 := bstep (se 1 (by rfl) ⟨4212458, by rfl⟩ : syracuseStep 5616611 = 8424917) B8424917
theorem B1315811 : Blo 1313975 1315811 := bstep (se 1 (by rfl) ⟨986858, by rfl⟩ : syracuseStep 1315811 = 1973717) B1973717
theorem B1971185 : Blo 1313975 1971185 := bstep (se 2 (by rfl) ⟨739194, by rfl⟩ : syracuseStep 1971185 = 1478389) B1478389
theorem B1479667 : Blo 1313975 1479667 := bstep (se 1 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 1479667 = 2219501) B2219501
theorem B1315827 : Blo 1313975 1315827 := bstep (se 1 (by rfl) ⟨986870, by rfl⟩ : syracuseStep 1315827 = 1973741) B1973741
theorem B1971203 : Blo 1313975 1971203 := bstep (se 1 (by rfl) ⟨1478402, by rfl⟩ : syracuseStep 1971203 = 2956805) B2956805
theorem B1315843 : Blo 1313975 1315843 := bstep (se 1 (by rfl) ⟨986882, by rfl⟩ : syracuseStep 1315843 = 1973765) B1973765
theorem B1315859 : Blo 1313975 1315859 := bstep (se 1 (by rfl) ⟨986894, by rfl⟩ : syracuseStep 1315859 = 1973789) B1973789
theorem B1971233 : Blo 1313975 1971233 := bstep (se 2 (by rfl) ⟨739212, by rfl⟩ : syracuseStep 1971233 = 1478425) B1478425
theorem B1315875 : Blo 1313975 1315875 := bstep (se 1 (by rfl) ⟨986906, by rfl⟩ : syracuseStep 1315875 = 1973813) B1973813
theorem B1971251 : Blo 1313975 1971251 := bstep (se 1 (by rfl) ⟨1478438, by rfl⟩ : syracuseStep 1971251 = 2956877) B2956877
theorem B1315891 : Blo 1313975 1315891 := bstep (se 1 (by rfl) ⟨986918, by rfl⟩ : syracuseStep 1315891 = 1973837) B1973837
theorem B1315907 : Blo 1313975 1315907 := bstep (se 1 (by rfl) ⟨986930, by rfl⟩ : syracuseStep 1315907 = 1973861) B1973861
theorem B1971281 : Blo 1313975 1971281 := bstep (se 2 (by rfl) ⟨739230, by rfl⟩ : syracuseStep 1971281 = 1478461) B1478461
theorem B1315923 : Blo 1313975 1315923 := bstep (se 1 (by rfl) ⟨986942, by rfl⟩ : syracuseStep 1315923 = 1973885) B1973885
theorem B1971299 : Blo 1313975 1971299 := bstep (se 1 (by rfl) ⟨1478474, by rfl⟩ : syracuseStep 1971299 = 2956949) B2956949
theorem B1315939 : Blo 1313975 1315939 := bstep (se 1 (by rfl) ⟨986954, by rfl⟩ : syracuseStep 1315939 = 1973909) B1973909
theorem B12629105 : Blo 1313975 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B1315955 : Blo 1313975 1315955 := bstep (se 1 (by rfl) ⟨986966, by rfl⟩ : syracuseStep 1315955 = 1973933) B1973933
theorem B1971329 : Blo 1313975 1971329 := bstep (se 2 (by rfl) ⟨739248, by rfl⟩ : syracuseStep 1971329 = 1478497) B1478497
theorem B1479811 : Blo 1313975 1479811 := bstep (se 1 (by rfl) ⟨1109858, by rfl⟩ : syracuseStep 1479811 = 2219717) B2219717
theorem B1315971 : Blo 1313975 1315971 := bstep (se 1 (by rfl) ⟨986978, by rfl⟩ : syracuseStep 1315971 = 1973957) B1973957
theorem B1971347 : Blo 1313975 1971347 := bstep (se 1 (by rfl) ⟨1478510, by rfl⟩ : syracuseStep 1971347 = 2957021) B2957021
theorem B1971377 : Blo 1313975 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B1971395 : Blo 1313975 1971395 := bstep (se 1 (by rfl) ⟨1478546, by rfl⟩ : syracuseStep 1971395 = 2957093) B2957093
theorem B1971425 : Blo 1313975 1971425 := bstep (se 2 (by rfl) ⟨739284, by rfl⟩ : syracuseStep 1971425 = 1478569) B1478569
theorem B4437233 : Blo 1313975 4437233 := bstep (se 2 (by rfl) ⟨1663962, by rfl⟩ : syracuseStep 4437233 = 3327925) B3327925
theorem B1971443 : Blo 1313975 1971443 := bstep (se 1 (by rfl) ⟨1478582, by rfl⟩ : syracuseStep 1971443 = 2957165) B2957165
theorem B2495747 : Blo 1313975 2495747 := bstep (se 1 (by rfl) ⟨1871810, by rfl⟩ : syracuseStep 2495747 = 3743621) B3743621
theorem B1971473 : Blo 1313975 1971473 := bstep (se 2 (by rfl) ⟨739302, by rfl⟩ : syracuseStep 1971473 = 1478605) B1478605
theorem B1479955 : Blo 1313975 1479955 := bstep (se 1 (by rfl) ⟨1109966, by rfl⟩ : syracuseStep 1479955 = 2219933) B2219933
theorem B1971491 : Blo 1313975 1971491 := bstep (se 1 (by rfl) ⟨1478618, by rfl⟩ : syracuseStep 1971491 = 2957237) B2957237
theorem B2807075 : Blo 1313975 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B1971521 : Blo 1313975 1971521 := bstep (se 2 (by rfl) ⟨739320, by rfl⟩ : syracuseStep 1971521 = 1478641) B1478641
theorem B1971539 : Blo 1313975 1971539 := bstep (se 1 (by rfl) ⟨1478654, by rfl⟩ : syracuseStep 1971539 = 2957309) B2957309
theorem B1971569 : Blo 1313975 1971569 := bstep (se 2 (by rfl) ⟨739338, by rfl⟩ : syracuseStep 1971569 = 1478677) B1478677
theorem B1971587 : Blo 1313975 1971587 := bstep (se 1 (by rfl) ⟨1478690, by rfl⟩ : syracuseStep 1971587 = 2957381) B2957381
theorem B2217361 : Blo 1313975 2217361 := bstep (se 2 (by rfl) ⟨831510, by rfl⟩ : syracuseStep 2217361 = 1663021) B1663021
theorem B1873297 : Blo 1313975 1873297 := bstep (se 2 (by rfl) ⟨702486, by rfl⟩ : syracuseStep 1873297 = 1404973) B1404973
theorem B1971617 : Blo 1313975 1971617 := bstep (se 2 (by rfl) ⟨739356, by rfl⟩ : syracuseStep 1971617 = 1478713) B1478713
theorem B1480099 : Blo 1313975 1480099 := bstep (se 1 (by rfl) ⟨1110074, by rfl⟩ : syracuseStep 1480099 = 2220149) B2220149
theorem B2217395 : Blo 1313975 2217395 := bstep (se 1 (by rfl) ⟨1663046, by rfl⟩ : syracuseStep 2217395 = 3326093) B3326093
theorem B1971635 : Blo 1313975 1971635 := bstep (se 1 (by rfl) ⟨1478726, by rfl⟩ : syracuseStep 1971635 = 2957453) B2957453
theorem B1971665 : Blo 1313975 1971665 := bstep (se 2 (by rfl) ⟨739374, by rfl⟩ : syracuseStep 1971665 = 1478749) B1478749
theorem B1971683 : Blo 1313975 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B5199331 : Blo 1313975 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B4994531 : Blo 1313975 4994531 := bstep (se 1 (by rfl) ⟨3745898, by rfl⟩ : syracuseStep 4994531 = 7491797) B7491797
theorem B2848241 : Blo 1313975 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B1971713 : Blo 1313975 1971713 := bstep (se 2 (by rfl) ⟨739392, by rfl⟩ : syracuseStep 1971713 = 1478785) B1478785
theorem B1971731 : Blo 1313975 1971731 := bstep (se 1 (by rfl) ⟨1478798, by rfl⟩ : syracuseStep 1971731 = 2957597) B2957597
theorem B2496035 : Blo 1313975 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1971761 : Blo 1313975 1971761 := bstep (se 2 (by rfl) ⟨739410, by rfl⟩ : syracuseStep 1971761 = 1478821) B1478821
theorem B2217523 : Blo 1313975 2217523 := bstep (se 1 (by rfl) ⟨1663142, by rfl⟩ : syracuseStep 2217523 = 3326285) B3326285
theorem B1480243 : Blo 1313975 1480243 := bstep (se 1 (by rfl) ⟨1110182, by rfl⟩ : syracuseStep 1480243 = 2220365) B2220365
theorem B1971779 : Blo 1313975 1971779 := bstep (se 1 (by rfl) ⟨1478834, by rfl⟩ : syracuseStep 1971779 = 2957669) B2957669
theorem B1971809 : Blo 1313975 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B1971827 : Blo 1313975 1971827 := bstep (se 1 (by rfl) ⟨1478870, by rfl⟩ : syracuseStep 1971827 = 2957741) B2957741
theorem B1971857 : Blo 1313975 1971857 := bstep (se 2 (by rfl) ⟨739446, by rfl⟩ : syracuseStep 1971857 = 1478893) B1478893
theorem B1971875 : Blo 1313975 1971875 := bstep (se 1 (by rfl) ⟨1478906, by rfl⟩ : syracuseStep 1971875 = 2957813) B2957813
theorem B6657713 : Blo 1313975 6657713 := bstep (se 2 (by rfl) ⟨2496642, by rfl⟩ : syracuseStep 6657713 = 4993285) B4993285
theorem B2217665 : Blo 1313975 2217665 := bstep (se 2 (by rfl) ⟨831624, by rfl⟩ : syracuseStep 2217665 = 1663249) B1663249
theorem B1971905 : Blo 1313975 1971905 := bstep (se 2 (by rfl) ⟨739464, by rfl⟩ : syracuseStep 1971905 = 1478929) B1478929
theorem B1480387 : Blo 1313975 1480387 := bstep (se 1 (by rfl) ⟨1110290, by rfl⟩ : syracuseStep 1480387 = 2220581) B2220581
theorem B1971923 : Blo 1313975 1971923 := bstep (se 1 (by rfl) ⟨1478942, by rfl⟩ : syracuseStep 1971923 = 2957885) B2957885
theorem B1873633 : Blo 1313975 1873633 := bstep (se 2 (by rfl) ⟨702612, by rfl⟩ : syracuseStep 1873633 = 1405225) B1405225
theorem B1971953 : Blo 1313975 1971953 := bstep (se 2 (by rfl) ⟨739482, by rfl⟩ : syracuseStep 1971953 = 1478965) B1478965
theorem B1971971 : Blo 1313975 1971971 := bstep (se 1 (by rfl) ⟨1478978, by rfl⟩ : syracuseStep 1971971 = 2957957) B2957957
theorem B4437773 : Blo 1313975 4437773 := bstep (se 3 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 4437773 = 1664165) B1664165
theorem B1972001 : Blo 1313975 1972001 := bstep (se 2 (by rfl) ⟨739500, by rfl⟩ : syracuseStep 1972001 = 1479001) B1479001
theorem B1972019 : Blo 1313975 1972019 := bstep (se 1 (by rfl) ⟨1479014, by rfl⟩ : syracuseStep 1972019 = 2958029) B2958029
theorem B2217793 : Blo 1313975 2217793 := bstep (se 2 (by rfl) ⟨831672, by rfl⟩ : syracuseStep 2217793 = 1663345) B1663345
theorem B4437827 : Blo 1313975 4437827 := bstep (se 1 (by rfl) ⟨3328370, by rfl⟩ : syracuseStep 4437827 = 6656741) B6656741
theorem B1972049 : Blo 1313975 1972049 := bstep (se 2 (by rfl) ⟨739518, by rfl⟩ : syracuseStep 1972049 = 1479037) B1479037
theorem B2217827 : Blo 1313975 2217827 := bstep (se 1 (by rfl) ⟨1663370, by rfl⟩ : syracuseStep 2217827 = 3326741) B3326741
theorem B1972067 : Blo 1313975 1972067 := bstep (se 1 (by rfl) ⟨1479050, by rfl⟩ : syracuseStep 1972067 = 2958101) B2958101
theorem B2529137 : Blo 1313975 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B1898353 : Blo 1313975 1898353 := bstep (se 2 (by rfl) ⟨711882, by rfl⟩ : syracuseStep 1898353 = 1423765) B1423765
theorem B1972097 : Blo 1313975 1972097 := bstep (se 2 (by rfl) ⟨739536, by rfl⟩ : syracuseStep 1972097 = 1479073) B1479073
theorem B1972115 : Blo 1313975 1972115 := bstep (se 1 (by rfl) ⟨1479086, by rfl⟩ : syracuseStep 1972115 = 2958173) B2958173
theorem B1972145 : Blo 1313975 1972145 := bstep (se 2 (by rfl) ⟨739554, by rfl⟩ : syracuseStep 1972145 = 1479109) B1479109
theorem B1972163 : Blo 1313975 1972163 := bstep (se 1 (by rfl) ⟨1479122, by rfl⟩ : syracuseStep 1972163 = 2958245) B2958245
theorem B11999173 : Blo 1313975 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B7493573 : Blo 1313975 7493573 := bstep (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) B1405045
theorem B1972193 : Blo 1313975 1972193 := bstep (se 2 (by rfl) ⟨739572, by rfl⟩ : syracuseStep 1972193 = 1479145) B1479145
theorem B2217955 : Blo 1313975 2217955 := bstep (se 1 (by rfl) ⟨1663466, by rfl⟩ : syracuseStep 2217955 = 3326933) B3326933
theorem B14227427 : Blo 1313975 14227427 := bstep (se 1 (by rfl) ⟨10670570, by rfl⟩ : syracuseStep 14227427 = 21341141) B21341141
theorem B4741105 : Blo 1313975 4741105 := bstep (se 2 (by rfl) ⟨1777914, by rfl⟩ : syracuseStep 4741105 = 3555829) B3555829
theorem B1972211 : Blo 1313975 1972211 := bstep (se 1 (by rfl) ⟨1479158, by rfl⟩ : syracuseStep 1972211 = 2958317) B2958317
theorem B1972241 : Blo 1313975 1972241 := bstep (se 2 (by rfl) ⟨739590, by rfl⟩ : syracuseStep 1972241 = 1479181) B1479181
theorem B1972259 : Blo 1313975 1972259 := bstep (se 1 (by rfl) ⟨1479194, by rfl⟩ : syracuseStep 1972259 = 2958389) B2958389
theorem B1972289 : Blo 1313975 1972289 := bstep (se 2 (by rfl) ⟨739608, by rfl⟩ : syracuseStep 1972289 = 1479217) B1479217
theorem B4438097 : Blo 1313975 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B1972307 : Blo 1313975 1972307 := bstep (se 1 (by rfl) ⟨1479230, by rfl⟩ : syracuseStep 1972307 = 2958461) B2958461
theorem B2218097 : Blo 1313975 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B2807921 : Blo 1313975 2807921 := bstep (se 2 (by rfl) ⟨1052970, by rfl⟩ : syracuseStep 2807921 = 2105941) B2105941
theorem B1972337 : Blo 1313975 1972337 := bstep (se 2 (by rfl) ⟨739626, by rfl⟩ : syracuseStep 1972337 = 1479253) B1479253
theorem B1972355 : Blo 1313975 1972355 := bstep (se 1 (by rfl) ⟨1479266, by rfl⟩ : syracuseStep 1972355 = 2958533) B2958533
theorem B1972385 : Blo 1313975 1972385 := bstep (se 2 (by rfl) ⟨739644, by rfl⟩ : syracuseStep 1972385 = 1479289) B1479289
theorem B1972403 : Blo 1313975 1972403 := bstep (se 1 (by rfl) ⟨1479302, by rfl⟩ : syracuseStep 1972403 = 2958605) B2958605
theorem B1972433 : Blo 1313975 1972433 := bstep (se 2 (by rfl) ⟨739662, by rfl⟩ : syracuseStep 1972433 = 1479325) B1479325
theorem B1972451 : Blo 1313975 1972451 := bstep (se 1 (by rfl) ⟨1479338, by rfl⟩ : syracuseStep 1972451 = 2958677) B2958677
theorem B11229425 : Blo 1313975 11229425 := bstep (se 2 (by rfl) ⟨4211034, by rfl⟩ : syracuseStep 11229425 = 8422069) B8422069
theorem B2218225 : Blo 1313975 2218225 := bstep (se 2 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 2218225 = 1663669) B1663669
theorem B1972481 : Blo 1313975 1972481 := bstep (se 2 (by rfl) ⟨739680, by rfl⟩ : syracuseStep 1972481 = 1479361) B1479361
theorem B2218259 : Blo 1313975 2218259 := bstep (se 1 (by rfl) ⟨1663694, by rfl⟩ : syracuseStep 2218259 = 3327389) B3327389
theorem B1972499 : Blo 1313975 1972499 := bstep (se 1 (by rfl) ⟨1479374, by rfl⟩ : syracuseStep 1972499 = 2958749) B2958749
theorem B3553571 : Blo 1313975 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B1972529 : Blo 1313975 1972529 := bstep (se 2 (by rfl) ⟨739698, by rfl⟩ : syracuseStep 1972529 = 1479397) B1479397
theorem B1972547 : Blo 1313975 1972547 := bstep (se 1 (by rfl) ⟨1479410, by rfl⟩ : syracuseStep 1972547 = 2958821) B2958821
theorem B1972577 : Blo 1313975 1972577 := bstep (se 2 (by rfl) ⟨739716, by rfl⟩ : syracuseStep 1972577 = 1479433) B1479433
theorem B1972595 : Blo 1313975 1972595 := bstep (se 1 (by rfl) ⟨1479446, by rfl⟩ : syracuseStep 1972595 = 2958893) B2958893
theorem B7494029 : Blo 1313975 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B1972625 : Blo 1313975 1972625 := bstep (se 2 (by rfl) ⟨739734, by rfl⟩ : syracuseStep 1972625 = 1479469) B1479469
theorem B2218387 : Blo 1313975 2218387 := bstep (se 1 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 2218387 = 3327581) B3327581
theorem B1972643 : Blo 1313975 1972643 := bstep (se 1 (by rfl) ⟨1479482, by rfl⟩ : syracuseStep 1972643 = 2958965) B2958965
theorem B4741553 : Blo 1313975 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B1972673 : Blo 1313975 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B9992645 : Blo 1313975 9992645 := bstep (se 4 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 9992645 = 1873621) B1873621
theorem B4995533 : Blo 1313975 4995533 := bstep (se 3 (by rfl) ⟨936662, by rfl⟩ : syracuseStep 4995533 = 1873325) B1873325
theorem B2496977 : Blo 1313975 2496977 := bstep (se 2 (by rfl) ⟨936366, by rfl⟩ : syracuseStep 2496977 = 1872733) B1872733
theorem B1972691 : Blo 1313975 1972691 := bstep (se 1 (by rfl) ⟨1479518, by rfl⟩ : syracuseStep 1972691 = 2959037) B2959037
theorem B1972721 : Blo 1313975 1972721 := bstep (se 2 (by rfl) ⟨739770, by rfl⟩ : syracuseStep 1972721 = 1479541) B1479541
theorem B1972739 : Blo 1313975 1972739 := bstep (se 1 (by rfl) ⟨1479554, by rfl⟩ : syracuseStep 1972739 = 2959109) B2959109
theorem B7485965 : Blo 1313975 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B2218529 : Blo 1313975 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1972769 : Blo 1313975 1972769 := bstep (se 2 (by rfl) ⟨739788, by rfl⟩ : syracuseStep 1972769 = 1479577) B1479577
theorem B1972787 : Blo 1313975 1972787 := bstep (se 1 (by rfl) ⟨1479590, by rfl⟩ : syracuseStep 1972787 = 2959181) B2959181
theorem B1972817 : Blo 1313975 1972817 := bstep (se 2 (by rfl) ⟨739806, by rfl⟩ : syracuseStep 1972817 = 1479613) B1479613
theorem B1579619 : Blo 1313975 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1972835 : Blo 1313975 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B4438637 : Blo 1313975 4438637 := bstep (se 3 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 4438637 = 1664489) B1664489
theorem B1972865 : Blo 1313975 1972865 := bstep (se 2 (by rfl) ⟨739824, by rfl⟩ : syracuseStep 1972865 = 1479649) B1479649
theorem B1800835 : Blo 1313975 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B1972883 : Blo 1313975 1972883 := bstep (se 1 (by rfl) ⟨1479662, by rfl⟩ : syracuseStep 1972883 = 2959325) B2959325
theorem B2218657 : Blo 1313975 2218657 := bstep (se 2 (by rfl) ⟨831996, by rfl⟩ : syracuseStep 2218657 = 1663993) B1663993
theorem B4438691 : Blo 1313975 4438691 := bstep (se 1 (by rfl) ⟨3329018, by rfl⟩ : syracuseStep 4438691 = 6658037) B6658037
theorem B1972913 : Blo 1313975 1972913 := bstep (se 2 (by rfl) ⟨739842, by rfl⟩ : syracuseStep 1972913 = 1479685) B1479685
theorem B2218691 : Blo 1313975 2218691 := bstep (se 1 (by rfl) ⟨1664018, by rfl⟩ : syracuseStep 2218691 = 3328037) B3328037
theorem B1972931 : Blo 1313975 1972931 := bstep (se 1 (by rfl) ⟨1479698, by rfl⟩ : syracuseStep 1972931 = 2959397) B2959397
theorem B4496077 : Blo 1313975 4496077 := bstep (se 3 (by rfl) ⟨843014, by rfl⟩ : syracuseStep 4496077 = 1686029) B1686029
theorem B1972961 : Blo 1313975 1972961 := bstep (se 2 (by rfl) ⟨739860, by rfl⟩ : syracuseStep 1972961 = 1479721) B1479721
theorem B1972979 : Blo 1313975 1972979 := bstep (se 1 (by rfl) ⟨1479734, by rfl⟩ : syracuseStep 1972979 = 2959469) B2959469
theorem B1973009 : Blo 1313975 1973009 := bstep (se 2 (by rfl) ⟨739878, by rfl⟩ : syracuseStep 1973009 = 1479757) B1479757
theorem B1973027 : Blo 1313975 1973027 := bstep (se 1 (by rfl) ⟨1479770, by rfl⟩ : syracuseStep 1973027 = 2959541) B2959541
theorem B1973057 : Blo 1313975 1973057 := bstep (se 2 (by rfl) ⟨739896, by rfl⟩ : syracuseStep 1973057 = 1479793) B1479793
theorem B2218819 : Blo 1313975 2218819 := bstep (se 1 (by rfl) ⟨1664114, by rfl⟩ : syracuseStep 2218819 = 3328229) B3328229
theorem B1973075 : Blo 1313975 1973075 := bstep (se 1 (by rfl) ⟨1479806, by rfl⟩ : syracuseStep 1973075 = 2959613) B2959613
theorem B1973105 : Blo 1313975 1973105 := bstep (se 2 (by rfl) ⟨739914, by rfl⟩ : syracuseStep 1973105 = 1479829) B1479829
theorem B3742595 : Blo 1313975 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B1973123 : Blo 1313975 1973123 := bstep (se 1 (by rfl) ⟨1479842, by rfl⟩ : syracuseStep 1973123 = 2959685) B2959685
theorem B1973153 : Blo 1313975 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B4438961 : Blo 1313975 4438961 := bstep (se 2 (by rfl) ⟨1664610, by rfl⟩ : syracuseStep 4438961 = 3329221) B3329221
theorem B5618609 : Blo 1313975 5618609 := bstep (se 2 (by rfl) ⟨2106978, by rfl⟩ : syracuseStep 5618609 = 4213957) B4213957
theorem B1973171 : Blo 1313975 1973171 := bstep (se 1 (by rfl) ⟨1479878, by rfl⟩ : syracuseStep 1973171 = 2959757) B2959757
theorem B2218961 : Blo 1313975 2218961 := bstep (se 2 (by rfl) ⟨832110, by rfl⟩ : syracuseStep 2218961 = 1664221) B1664221
theorem B1973201 : Blo 1313975 1973201 := bstep (se 2 (by rfl) ⟨739950, by rfl⟩ : syracuseStep 1973201 = 1479901) B1479901
theorem B1973219 : Blo 1313975 1973219 := bstep (se 1 (by rfl) ⟨1479914, by rfl⟩ : syracuseStep 1973219 = 2959829) B2959829
theorem B1973249 : Blo 1313975 1973249 := bstep (se 2 (by rfl) ⟨739968, by rfl⟩ : syracuseStep 1973249 = 1479937) B1479937
theorem B1973267 : Blo 1313975 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B1973297 : Blo 1313975 1973297 := bstep (se 2 (by rfl) ⟨739986, by rfl⟩ : syracuseStep 1973297 = 1479973) B1479973
theorem B1580099 : Blo 1313975 1580099 := bstep (se 1 (by rfl) ⟨1185074, by rfl⟩ : syracuseStep 1580099 = 2370149) B2370149
theorem B1973315 : Blo 1313975 1973315 := bstep (se 1 (by rfl) ⟨1479986, by rfl⟩ : syracuseStep 1973315 = 2959973) B2959973
theorem B8420429 : Blo 1313975 8420429 := bstep (se 3 (by rfl) ⟨1578830, by rfl⟩ : syracuseStep 8420429 = 3157661) B3157661
theorem B2219089 : Blo 1313975 2219089 := bstep (se 2 (by rfl) ⟨832158, by rfl⟩ : syracuseStep 2219089 = 1664317) B1664317
theorem B1973345 : Blo 1313975 1973345 := bstep (se 2 (by rfl) ⟨740004, by rfl⟩ : syracuseStep 1973345 = 1480009) B1480009
theorem B6659171 : Blo 1313975 6659171 := bstep (se 1 (by rfl) ⟨4994378, by rfl⟩ : syracuseStep 6659171 = 9988757) B9988757
theorem B2219123 : Blo 1313975 2219123 := bstep (se 1 (by rfl) ⟨1664342, by rfl⟩ : syracuseStep 2219123 = 3328685) B3328685
theorem B1973363 : Blo 1313975 1973363 := bstep (se 1 (by rfl) ⟨1480022, by rfl⟩ : syracuseStep 1973363 = 2960045) B2960045
theorem B1973393 : Blo 1313975 1973393 := bstep (se 2 (by rfl) ⟨740022, by rfl⟩ : syracuseStep 1973393 = 1480045) B1480045
theorem B1973411 : Blo 1313975 1973411 := bstep (se 1 (by rfl) ⟨1480058, by rfl⟩ : syracuseStep 1973411 = 2960117) B2960117
theorem B1973441 : Blo 1313975 1973441 := bstep (se 2 (by rfl) ⟨740040, by rfl⟩ : syracuseStep 1973441 = 1480081) B1480081
theorem B1973459 : Blo 1313975 1973459 := bstep (se 1 (by rfl) ⟨1480094, by rfl⟩ : syracuseStep 1973459 = 2960189) B2960189
theorem B1973489 : Blo 1313975 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B2219251 : Blo 1313975 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B1973507 : Blo 1313975 1973507 := bstep (se 1 (by rfl) ⟨1480130, by rfl⟩ : syracuseStep 1973507 = 2960261) B2960261
theorem B1973537 : Blo 1313975 1973537 := bstep (se 2 (by rfl) ⟨740076, by rfl⟩ : syracuseStep 1973537 = 1480153) B1480153
theorem B8428835 : Blo 1313975 8428835 := bstep (se 1 (by rfl) ⟨6321626, by rfl⟩ : syracuseStep 8428835 = 12643253) B12643253
theorem B1973555 : Blo 1313975 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B2956625 : Blo 1313975 2956625 := bstep (se 2 (by rfl) ⟨1108734, by rfl⟩ : syracuseStep 2956625 = 2217469) B2217469
theorem B1973585 : Blo 1313975 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B2497873 : Blo 1313975 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B2956643 : Blo 1313975 2956643 := bstep (se 1 (by rfl) ⟨2217482, by rfl⟩ : syracuseStep 2956643 = 4434965) B4434965
theorem B1973603 : Blo 1313975 1973603 := bstep (se 1 (by rfl) ⟨1480202, by rfl⟩ : syracuseStep 1973603 = 2960405) B2960405
theorem B3898733 : Blo 1313975 3898733 := bstep (se 3 (by rfl) ⟨731012, by rfl⟩ : syracuseStep 3898733 = 1462025) B1462025
theorem B2219393 : Blo 1313975 2219393 := bstep (se 2 (by rfl) ⟨832272, by rfl⟩ : syracuseStep 2219393 = 1664545) B1664545
theorem B1973633 : Blo 1313975 1973633 := bstep (se 2 (by rfl) ⟨740112, by rfl⟩ : syracuseStep 1973633 = 1480225) B1480225
theorem B3554705 : Blo 1313975 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B1973651 : Blo 1313975 1973651 := bstep (se 1 (by rfl) ⟨1480238, by rfl⟩ : syracuseStep 1973651 = 2960477) B2960477
theorem B1973681 : Blo 1313975 1973681 := bstep (se 2 (by rfl) ⟨740130, by rfl⟩ : syracuseStep 1973681 = 1480261) B1480261
theorem B1498547 : Blo 1313975 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B1973699 : Blo 1313975 1973699 := bstep (se 1 (by rfl) ⟨1480274, by rfl⟩ : syracuseStep 1973699 = 2960549) B2960549
theorem B4439501 : Blo 1313975 4439501 := bstep (se 3 (by rfl) ⟨832406, by rfl⟩ : syracuseStep 4439501 = 1664813) B1664813
theorem B1973729 : Blo 1313975 1973729 := bstep (se 2 (by rfl) ⟨740148, by rfl⟩ : syracuseStep 1973729 = 1480297) B1480297
theorem B2498033 : Blo 1313975 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B1973747 : Blo 1313975 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B2219521 : Blo 1313975 2219521 := bstep (se 2 (by rfl) ⟨832320, by rfl⟩ : syracuseStep 2219521 = 1664641) B1664641
theorem B4439555 : Blo 1313975 4439555 := bstep (se 1 (by rfl) ⟨3329666, by rfl⟩ : syracuseStep 4439555 = 6659333) B6659333
theorem B12631565 : Blo 1313975 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B1973777 : Blo 1313975 1973777 := bstep (se 2 (by rfl) ⟨740166, by rfl⟩ : syracuseStep 1973777 = 1480333) B1480333
theorem B2219555 : Blo 1313975 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B1973795 : Blo 1313975 1973795 := bstep (se 1 (by rfl) ⟨1480346, by rfl⟩ : syracuseStep 1973795 = 2960693) B2960693
theorem B1973825 : Blo 1313975 1973825 := bstep (se 2 (by rfl) ⟨740184, by rfl⟩ : syracuseStep 1973825 = 1480369) B1480369
theorem B1973843 : Blo 1313975 1973843 := bstep (se 1 (by rfl) ⟨1480382, by rfl⟩ : syracuseStep 1973843 = 2960765) B2960765
theorem B3161699 : Blo 1313975 3161699 := bstep (se 1 (by rfl) ⟨2371274, by rfl⟩ : syracuseStep 3161699 = 4742549) B4742549
theorem B2956913 : Blo 1313975 2956913 := bstep (se 2 (by rfl) ⟨1108842, by rfl⟩ : syracuseStep 2956913 = 2217685) B2217685
theorem B1973873 : Blo 1313975 1973873 := bstep (se 2 (by rfl) ⟨740202, by rfl⟩ : syracuseStep 1973873 = 1480405) B1480405
theorem B2956931 : Blo 1313975 2956931 := bstep (se 1 (by rfl) ⟨2217698, by rfl⟩ : syracuseStep 2956931 = 4435397) B4435397
theorem B1973891 : Blo 1313975 1973891 := bstep (se 1 (by rfl) ⟨1480418, by rfl⟩ : syracuseStep 1973891 = 2960837) B2960837
theorem B1973921 : Blo 1313975 1973921 := bstep (se 2 (by rfl) ⟨740220, by rfl⟩ : syracuseStep 1973921 = 1480441) B1480441
theorem B2219683 : Blo 1313975 2219683 := bstep (se 1 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 2219683 = 3329525) B3329525
theorem B3743405 : Blo 1313975 3743405 := bstep (se 3 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 3743405 = 1403777) B1403777
theorem B1973939 : Blo 1313975 1973939 := bstep (se 1 (by rfl) ⟨1480454, by rfl⟩ : syracuseStep 1973939 = 2960909) B2960909
theorem B4439825 : Blo 1313975 4439825 := bstep (se 2 (by rfl) ⟨1664934, by rfl⟩ : syracuseStep 4439825 = 3329869) B3329869
theorem B1998611 : Blo 1313975 1998611 := bstep (se 1 (by rfl) ⟨1498958, by rfl⟩ : syracuseStep 1998611 = 2997917) B2997917
theorem B2219825 : Blo 1313975 2219825 := bstep (se 2 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 2219825 = 1664869) B1664869
theorem B2105185 : Blo 1313975 2105185 := bstep (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) B1578889
theorem B3743597 : Blo 1313975 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B3604333 : Blo 1313975 3604333 := bstep (se 3 (by rfl) ⟨675812, by rfl⟩ : syracuseStep 3604333 = 1351625) B1351625
theorem B6659981 : Blo 1313975 6659981 := bstep (se 3 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 6659981 = 2497493) B2497493
theorem B2957201 : Blo 1313975 2957201 := bstep (se 2 (by rfl) ⟨1108950, by rfl⟩ : syracuseStep 2957201 = 2217901) B2217901
theorem B2957219 : Blo 1313975 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B2219953 : Blo 1313975 2219953 := bstep (se 2 (by rfl) ⟨832482, by rfl⟩ : syracuseStep 2219953 = 1664965) B1664965
theorem B2219987 : Blo 1313975 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B17088497 : Blo 1313975 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B2957363 : Blo 1313975 2957363 := bstep (se 1 (by rfl) ⟨2218022, by rfl⟩ : syracuseStep 2957363 = 4436045) B4436045
theorem B3465281 : Blo 1313975 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B3375179 : Blo 1313975 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B2957399 : Blo 1313975 2957399 := bstep (se 1 (by rfl) ⟨2218049, by rfl⟩ : syracuseStep 2957399 = 4436099) B4436099
theorem B21332119 : Blo 1313975 21332119 := bstep (se 1 (by rfl) ⟨15999089, by rfl⟩ : syracuseStep 21332119 = 31998179) B31998179
theorem B4440257 : Blo 1313975 4440257 := bstep (se 2 (by rfl) ⟨1665096, by rfl⟩ : syracuseStep 4440257 = 3330193) B3330193
theorem B2957579 : Blo 1313975 2957579 := bstep (se 1 (by rfl) ⟨2218184, by rfl⟩ : syracuseStep 2957579 = 4436369) B4436369
theorem B2220311 : Blo 1313975 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B6652205 : Blo 1313975 6652205 := bstep (se 3 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 6652205 = 2494577) B2494577
theorem B2957633 : Blo 1313975 2957633 := bstep (se 2 (by rfl) ⟨1109112, by rfl⟩ : syracuseStep 2957633 = 2218225) B2218225
theorem B5620043 : Blo 1313975 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B2810227 : Blo 1313975 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B1999243 : Blo 1313975 1999243 := bstep (se 1 (by rfl) ⟨1499432, by rfl⟩ : syracuseStep 1999243 = 2998865) B2998865
theorem B2220439 : Blo 1313975 2220439 := bstep (se 1 (by rfl) ⟨1665329, by rfl⟩ : syracuseStep 2220439 = 3330659) B3330659
theorem B7487923 : Blo 1313975 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B9478579 : Blo 1313975 9478579 := bstep (se 1 (by rfl) ⟨7108934, by rfl⟩ : syracuseStep 9478579 = 14217869) B14217869
theorem B4211137 : Blo 1313975 4211137 := bstep (se 2 (by rfl) ⟨1579176, by rfl⟩ : syracuseStep 4211137 = 3158353) B3158353
theorem B10117649 : Blo 1313975 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B2957849 : Blo 1313975 2957849 := bstep (se 2 (by rfl) ⟨1109193, by rfl⟩ : syracuseStep 2957849 = 2218387) B2218387
theorem B2957939 : Blo 1313975 2957939 := bstep (se 1 (by rfl) ⟨2218454, by rfl⟩ : syracuseStep 2957939 = 4436909) B4436909
theorem B8651395 : Blo 1313975 8651395 := bstep (se 1 (by rfl) ⟨6488546, by rfl⟩ : syracuseStep 8651395 = 12977093) B12977093
theorem B2957975 : Blo 1313975 2957975 := bstep (se 1 (by rfl) ⟨2218481, by rfl⟩ : syracuseStep 2957975 = 4436963) B4436963
theorem B3744407 : Blo 1313975 3744407 := bstep (se 1 (by rfl) ⟨2808305, by rfl⟩ : syracuseStep 3744407 = 5616611) B5616611
theorem B4440797 : Blo 1313975 4440797 := bstep (se 3 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 4440797 = 1665299) B1665299
theorem B2999063 : Blo 1313975 2999063 := bstep (se 1 (by rfl) ⟨2249297, by rfl⟩ : syracuseStep 2999063 = 4498595) B4498595
theorem B3326771 : Blo 1313975 3326771 := bstep (se 1 (by rfl) ⟨2495078, by rfl⟩ : syracuseStep 3326771 = 4990157) B4990157
theorem B2958155 : Blo 1313975 2958155 := bstep (se 1 (by rfl) ⟨2218616, by rfl⟩ : syracuseStep 2958155 = 4437233) B4437233
theorem B1663831 : Blo 1313975 1663831 := bstep (se 1 (by rfl) ⟨1247873, by rfl⟩ : syracuseStep 1663831 = 2495747) B2495747
theorem B2958209 : Blo 1313975 2958209 := bstep (se 2 (by rfl) ⟨1109328, by rfl⟩ : syracuseStep 2958209 = 2218657) B2218657
theorem B4989869 : Blo 1313975 4989869 := bstep (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) B1871201
theorem B10396621 : Blo 1313975 10396621 := bstep (se 3 (by rfl) ⟨1949366, by rfl⟩ : syracuseStep 10396621 = 3898733) B3898733
theorem B4736017 : Blo 1313975 4736017 := bstep (se 2 (by rfl) ⟨1776006, by rfl⟩ : syracuseStep 4736017 = 3552013) B3552013
theorem B18965573 : Blo 1313975 18965573 := bstep (se 4 (by rfl) ⟨1778022, by rfl⟩ : syracuseStep 18965573 = 3556045) B3556045
theorem B3327065 : Blo 1313975 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B2958425 : Blo 1313975 2958425 := bstep (se 2 (by rfl) ⟨1109409, by rfl⟩ : syracuseStep 2958425 = 2218819) B2218819
theorem B1999961 : Blo 1313975 1999961 := bstep (se 2 (by rfl) ⟨749985, by rfl⟩ : syracuseStep 1999961 = 1499971) B1499971
theorem B2958515 : Blo 1313975 2958515 := bstep (se 1 (by rfl) ⟨2218886, by rfl⟩ : syracuseStep 2958515 = 4437773) B4437773
theorem B3998899 : Blo 1313975 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B2958551 : Blo 1313975 2958551 := bstep (se 1 (by rfl) ⟨2218913, by rfl⟩ : syracuseStep 2958551 = 4437827) B4437827
theorem B7595309 : Blo 1313975 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B2958731 : Blo 1313975 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B2958785 : Blo 1313975 2958785 := bstep (se 2 (by rfl) ⟨1109544, by rfl⟩ : syracuseStep 2958785 = 2219089) B2219089
theorem B2000459 : Blo 1313975 2000459 := bstep (se 1 (by rfl) ⟨1500344, by rfl⟩ : syracuseStep 2000459 = 3000689) B3000689
theorem B4212317 : Blo 1313975 4212317 := bstep (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) B1579619
theorem B9979523 : Blo 1313975 9979523 := bstep (se 1 (by rfl) ⟨7484642, by rfl⟩ : syracuseStep 9979523 = 14969285) B14969285
theorem B6661763 : Blo 1313975 6661763 := bstep (se 1 (by rfl) ⟨4996322, by rfl⟩ : syracuseStep 6661763 = 9992645) B9992645
theorem B1664651 : Blo 1313975 1664651 := bstep (se 1 (by rfl) ⟨1248488, by rfl⟩ : syracuseStep 1664651 = 2496977) B2496977
theorem B2959001 : Blo 1313975 2959001 := bstep (se 2 (by rfl) ⟨1109625, by rfl⟩ : syracuseStep 2959001 = 2219251) B2219251
theorem B4990643 : Blo 1313975 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B2959091 : Blo 1313975 2959091 := bstep (se 1 (by rfl) ⟨2219318, by rfl⟩ : syracuseStep 2959091 = 4438637) B4438637
theorem B2959127 : Blo 1313975 2959127 := bstep (se 1 (by rfl) ⟨2219345, by rfl⟩ : syracuseStep 2959127 = 4438691) B4438691
theorem B14215013 : Blo 1313975 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B7489381 : Blo 1313975 7489381 := bstep (se 4 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 7489381 = 1404259) B1404259
theorem B25257905 : Blo 1313975 25257905 := bstep (se 2 (by rfl) ⟨9471714, by rfl⟩ : syracuseStep 25257905 = 18943429) B18943429
theorem B2959307 : Blo 1313975 2959307 := bstep (se 1 (by rfl) ⟨2219480, by rfl⟩ : syracuseStep 2959307 = 4438961) B4438961
theorem B3745739 : Blo 1313975 3745739 := bstep (se 1 (by rfl) ⟨2809304, by rfl⟩ : syracuseStep 3745739 = 5618609) B5618609
theorem B6932441 : Blo 1313975 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B2959361 : Blo 1313975 2959361 := bstep (se 2 (by rfl) ⟨1109760, by rfl⟩ : syracuseStep 2959361 = 2219521) B2219521
theorem B5613619 : Blo 1313975 5613619 := bstep (se 1 (by rfl) ⟨4210214, by rfl⟩ : syracuseStep 5613619 = 8420429) B8420429
theorem B2959577 : Blo 1313975 2959577 := bstep (se 2 (by rfl) ⟨1109841, by rfl⟩ : syracuseStep 2959577 = 2219683) B2219683
theorem B2369803 : Blo 1313975 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B2959667 : Blo 1313975 2959667 := bstep (se 1 (by rfl) ⟨2219750, by rfl⟩ : syracuseStep 2959667 = 4439501) B4439501
theorem B1665355 : Blo 1313975 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B2959703 : Blo 1313975 2959703 := bstep (se 1 (by rfl) ⟨2219777, by rfl⟩ : syracuseStep 2959703 = 4439555) B4439555
theorem B2107799 : Blo 1313975 2107799 := bstep (se 1 (by rfl) ⟨1580849, by rfl⟩ : syracuseStep 2107799 = 3161699) B3161699
theorem B17090995 : Blo 1313975 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B2959883 : Blo 1313975 2959883 := bstep (se 1 (by rfl) ⟨2219912, by rfl⟩ : syracuseStep 2959883 = 4439825) B4439825
theorem B2959937 : Blo 1313975 2959937 := bstep (se 2 (by rfl) ⟨1109976, by rfl⟩ : syracuseStep 2959937 = 2219953) B2219953
theorem B6400691 : Blo 1313975 6400691 := bstep (se 1 (by rfl) ⟨4800518, by rfl⟩ : syracuseStep 6400691 = 9601037) B9601037
theorem B3328715 : Blo 1313975 3328715 := bstep (se 1 (by rfl) ⟨2496536, by rfl⟩ : syracuseStep 3328715 = 4993073) B4993073
theorem B1403627 : Blo 1313975 1403627 := bstep (se 1 (by rfl) ⟨1052720, by rfl⟩ : syracuseStep 1403627 = 2105441) B2105441
theorem B2960153 : Blo 1313975 2960153 := bstep (se 2 (by rfl) ⟨1110057, by rfl⟩ : syracuseStep 2960153 = 2220115) B2220115
theorem B2960243 : Blo 1313975 2960243 := bstep (se 1 (by rfl) ⟨2220182, by rfl⟩ : syracuseStep 2960243 = 4440365) B4440365
theorem B2960279 : Blo 1313975 2960279 := bstep (se 1 (by rfl) ⟨2220209, by rfl⟩ : syracuseStep 2960279 = 4440419) B4440419
theorem B4435019 : Blo 1313975 4435019 := bstep (se 1 (by rfl) ⟨3326264, by rfl⟩ : syracuseStep 4435019 = 6652529) B6652529
theorem B2960459 : Blo 1313975 2960459 := bstep (se 1 (by rfl) ⟨2220344, by rfl⟩ : syracuseStep 2960459 = 4440689) B4440689
theorem B2960513 : Blo 1313975 2960513 := bstep (se 2 (by rfl) ⟨1110192, by rfl⟩ : syracuseStep 2960513 = 2220385) B2220385
theorem B4992131 : Blo 1313975 4992131 := bstep (se 1 (by rfl) ⟨3744098, by rfl⟩ : syracuseStep 4992131 = 7488197) B7488197
theorem B11234483 : Blo 1313975 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B1313975 : Blo 1313975 1313975 := bstep (se 1 (by rfl) ⟨985481, by rfl⟩ : syracuseStep 1313975 = 1970963) B1970963
theorem B1313995 : Blo 1313975 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B1314007 : Blo 1313975 1314007 := bstep (se 1 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 1314007 = 1971011) B1971011
theorem B1314027 : Blo 1313975 1314027 := bstep (se 1 (by rfl) ⟨985520, by rfl⟩ : syracuseStep 1314027 = 1971041) B1971041
theorem B1314039 : Blo 1313975 1314039 := bstep (se 1 (by rfl) ⟨985529, by rfl⟩ : syracuseStep 1314039 = 1971059) B1971059
theorem B60738821 : Blo 1313975 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B1314059 : Blo 1313975 1314059 := bstep (se 1 (by rfl) ⟨985544, by rfl⟩ : syracuseStep 1314059 = 1971089) B1971089
theorem B1314071 : Blo 1313975 1314071 := bstep (se 1 (by rfl) ⟨985553, by rfl⟩ : syracuseStep 1314071 = 1971107) B1971107
theorem B1314091 : Blo 1313975 1314091 := bstep (se 1 (by rfl) ⟨985568, by rfl⟩ : syracuseStep 1314091 = 1971137) B1971137
theorem B1314103 : Blo 1313975 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B1314123 : Blo 1313975 1314123 := bstep (se 1 (by rfl) ⟨985592, by rfl⟩ : syracuseStep 1314123 = 1971185) B1971185
theorem B1314135 : Blo 1313975 1314135 := bstep (se 1 (by rfl) ⟨985601, by rfl⟩ : syracuseStep 1314135 = 1971203) B1971203
theorem B4435289 : Blo 1313975 4435289 := bstep (se 2 (by rfl) ⟨1663233, by rfl⟩ : syracuseStep 4435289 = 3326467) B3326467
theorem B2960729 : Blo 1313975 2960729 := bstep (se 2 (by rfl) ⟨1110273, by rfl⟩ : syracuseStep 2960729 = 2220547) B2220547
theorem B1314155 : Blo 1313975 1314155 := bstep (se 1 (by rfl) ⟨985616, by rfl⟩ : syracuseStep 1314155 = 1971233) B1971233
theorem B16854389 : Blo 1313975 16854389 := bstep (se 5 (by rfl) ⟨790049, by rfl⟩ : syracuseStep 16854389 = 1580099) B1580099
theorem B1314167 : Blo 1313975 1314167 := bstep (se 1 (by rfl) ⟨985625, by rfl⟩ : syracuseStep 1314167 = 1971251) B1971251
theorem B1314187 : Blo 1313975 1314187 := bstep (se 1 (by rfl) ⟨985640, by rfl⟩ : syracuseStep 1314187 = 1971281) B1971281
theorem B1314199 : Blo 1313975 1314199 := bstep (se 1 (by rfl) ⟨985649, by rfl⟩ : syracuseStep 1314199 = 1971299) B1971299
theorem B1314219 : Blo 1313975 1314219 := bstep (se 1 (by rfl) ⟨985664, by rfl⟩ : syracuseStep 1314219 = 1971329) B1971329
theorem B5615021 : Blo 1313975 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B2960819 : Blo 1313975 2960819 := bstep (se 1 (by rfl) ⟨2220614, by rfl⟩ : syracuseStep 2960819 = 4441229) B4441229
theorem B1314231 : Blo 1313975 1314231 := bstep (se 1 (by rfl) ⟨985673, by rfl⟩ : syracuseStep 1314231 = 1971347) B1971347
theorem B3157451 : Blo 1313975 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B1314251 : Blo 1313975 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1314263 : Blo 1313975 1314263 := bstep (se 1 (by rfl) ⟨985697, by rfl⟩ : syracuseStep 1314263 = 1971395) B1971395
theorem B2960855 : Blo 1313975 2960855 := bstep (se 1 (by rfl) ⟨2220641, by rfl⟩ : syracuseStep 2960855 = 4441283) B4441283
theorem B1314283 : Blo 1313975 1314283 := bstep (se 1 (by rfl) ⟨985712, by rfl⟩ : syracuseStep 1314283 = 1971425) B1971425
theorem B1314295 : Blo 1313975 1314295 := bstep (se 1 (by rfl) ⟨985721, by rfl⟩ : syracuseStep 1314295 = 1971443) B1971443
theorem B1314315 : Blo 1313975 1314315 := bstep (se 1 (by rfl) ⟨985736, by rfl⟩ : syracuseStep 1314315 = 1971473) B1971473
theorem B1314327 : Blo 1313975 1314327 := bstep (se 1 (by rfl) ⟨985745, by rfl⟩ : syracuseStep 1314327 = 1971491) B1971491
theorem B1314347 : Blo 1313975 1314347 := bstep (se 1 (by rfl) ⟨985760, by rfl⟩ : syracuseStep 1314347 = 1971521) B1971521
theorem B11234861 : Blo 1313975 11234861 := bstep (se 3 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 11234861 = 4213073) B4213073
theorem B3747379 : Blo 1313975 3747379 := bstep (se 1 (by rfl) ⟨2810534, by rfl⟩ : syracuseStep 3747379 = 5621069) B5621069
theorem B1314359 : Blo 1313975 1314359 := bstep (se 1 (by rfl) ⟨985769, by rfl⟩ : syracuseStep 1314359 = 1971539) B1971539
theorem B1314379 : Blo 1313975 1314379 := bstep (se 1 (by rfl) ⟨985784, by rfl⟩ : syracuseStep 1314379 = 1971569) B1971569
theorem B4992587 : Blo 1313975 4992587 := bstep (se 1 (by rfl) ⟨3744440, by rfl⟩ : syracuseStep 4992587 = 7488881) B7488881
theorem B1314391 : Blo 1313975 1314391 := bstep (se 1 (by rfl) ⟨985793, by rfl⟩ : syracuseStep 1314391 = 1971587) B1971587
theorem B1314411 : Blo 1313975 1314411 := bstep (se 1 (by rfl) ⟨985808, by rfl⟩ : syracuseStep 1314411 = 1971617) B1971617
theorem B1478263 : Blo 1313975 1478263 := bstep (se 1 (by rfl) ⟨1108697, by rfl⟩ : syracuseStep 1478263 = 2217395) B2217395
theorem B1314423 : Blo 1313975 1314423 := bstep (se 1 (by rfl) ⟨985817, by rfl⟩ : syracuseStep 1314423 = 1971635) B1971635
theorem B1314443 : Blo 1313975 1314443 := bstep (se 1 (by rfl) ⟨985832, by rfl⟩ : syracuseStep 1314443 = 1971665) B1971665
theorem B1314455 : Blo 1313975 1314455 := bstep (se 1 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 1314455 = 1971683) B1971683
theorem B3329687 : Blo 1313975 3329687 := bstep (se 1 (by rfl) ⟨2497265, by rfl⟩ : syracuseStep 3329687 = 4994531) B4994531
theorem B1314475 : Blo 1313975 1314475 := bstep (se 1 (by rfl) ⟨985856, by rfl⟩ : syracuseStep 1314475 = 1971713) B1971713
theorem B1314487 : Blo 1313975 1314487 := bstep (se 1 (by rfl) ⟨985865, by rfl⟩ : syracuseStep 1314487 = 1971731) B1971731
theorem B1314507 : Blo 1313975 1314507 := bstep (se 1 (by rfl) ⟨985880, by rfl⟩ : syracuseStep 1314507 = 1971761) B1971761
theorem B1314519 : Blo 1313975 1314519 := bstep (se 1 (by rfl) ⟨985889, by rfl⟩ : syracuseStep 1314519 = 1971779) B1971779
theorem B1404631 : Blo 1313975 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1314539 : Blo 1313975 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B1314551 : Blo 1313975 1314551 := bstep (se 1 (by rfl) ⟨985913, by rfl⟩ : syracuseStep 1314551 = 1971827) B1971827
theorem B1314571 : Blo 1313975 1314571 := bstep (se 1 (by rfl) ⟨985928, by rfl⟩ : syracuseStep 1314571 = 1971857) B1971857
theorem B4992785 : Blo 1313975 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B1314583 : Blo 1313975 1314583 := bstep (se 1 (by rfl) ⟨985937, by rfl⟩ : syracuseStep 1314583 = 1971875) B1971875
theorem B1478443 : Blo 1313975 1478443 := bstep (se 1 (by rfl) ⟨1108832, by rfl⟩ : syracuseStep 1478443 = 2217665) B2217665
theorem B1314603 : Blo 1313975 1314603 := bstep (se 1 (by rfl) ⟨985952, by rfl⟩ : syracuseStep 1314603 = 1971905) B1971905
theorem B1314615 : Blo 1313975 1314615 := bstep (se 1 (by rfl) ⟨985961, by rfl⟩ : syracuseStep 1314615 = 1971923) B1971923
theorem B1314635 : Blo 1313975 1314635 := bstep (se 1 (by rfl) ⟨985976, by rfl⟩ : syracuseStep 1314635 = 1971953) B1971953
theorem B1314647 : Blo 1313975 1314647 := bstep (se 1 (by rfl) ⟨985985, by rfl⟩ : syracuseStep 1314647 = 1971971) B1971971
theorem B1314667 : Blo 1313975 1314667 := bstep (se 1 (by rfl) ⟨986000, by rfl⟩ : syracuseStep 1314667 = 1972001) B1972001
theorem B1314679 : Blo 1313975 1314679 := bstep (se 1 (by rfl) ⟨986009, by rfl⟩ : syracuseStep 1314679 = 1972019) B1972019
theorem B1314699 : Blo 1313975 1314699 := bstep (se 1 (by rfl) ⟨986024, by rfl⟩ : syracuseStep 1314699 = 1972049) B1972049
theorem B1478551 : Blo 1313975 1478551 := bstep (se 1 (by rfl) ⟨1108913, by rfl⟩ : syracuseStep 1478551 = 2217827) B2217827
theorem B1314711 : Blo 1313975 1314711 := bstep (se 1 (by rfl) ⟨986033, by rfl⟩ : syracuseStep 1314711 = 1972067) B1972067
theorem B1314731 : Blo 1313975 1314731 := bstep (se 1 (by rfl) ⟨986048, by rfl⟩ : syracuseStep 1314731 = 1972097) B1972097
theorem B1314743 : Blo 1313975 1314743 := bstep (se 1 (by rfl) ⟨986057, by rfl⟩ : syracuseStep 1314743 = 1972115) B1972115
theorem B1314763 : Blo 1313975 1314763 := bstep (se 1 (by rfl) ⟨986072, by rfl⟩ : syracuseStep 1314763 = 1972145) B1972145
theorem B1314775 : Blo 1313975 1314775 := bstep (se 1 (by rfl) ⟨986081, by rfl⟩ : syracuseStep 1314775 = 1972163) B1972163
theorem B1314795 : Blo 1313975 1314795 := bstep (se 1 (by rfl) ⟨986096, by rfl⟩ : syracuseStep 1314795 = 1972193) B1972193
theorem B1314807 : Blo 1313975 1314807 := bstep (se 1 (by rfl) ⟨986105, by rfl⟩ : syracuseStep 1314807 = 1972211) B1972211
theorem B1314827 : Blo 1313975 1314827 := bstep (se 1 (by rfl) ⟨986120, by rfl⟩ : syracuseStep 1314827 = 1972241) B1972241
theorem B4435991 : Blo 1313975 4435991 := bstep (se 1 (by rfl) ⟨3326993, by rfl⟩ : syracuseStep 4435991 = 6653987) B6653987
theorem B1314839 : Blo 1313975 1314839 := bstep (se 1 (by rfl) ⟨986129, by rfl⟩ : syracuseStep 1314839 = 1972259) B1972259
theorem B1314859 : Blo 1313975 1314859 := bstep (se 1 (by rfl) ⟨986144, by rfl⟩ : syracuseStep 1314859 = 1972289) B1972289
theorem B1314871 : Blo 1313975 1314871 := bstep (se 1 (by rfl) ⟨986153, by rfl⟩ : syracuseStep 1314871 = 1972307) B1972307
theorem B1478731 : Blo 1313975 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B1871947 : Blo 1313975 1871947 := bstep (se 1 (by rfl) ⟨1403960, by rfl⟩ : syracuseStep 1871947 = 2807921) B2807921
theorem B1314891 : Blo 1313975 1314891 := bstep (se 1 (by rfl) ⟨986168, by rfl⟩ : syracuseStep 1314891 = 1972337) B1972337
theorem B1314903 : Blo 1313975 1314903 := bstep (se 1 (by rfl) ⟨986177, by rfl⟩ : syracuseStep 1314903 = 1972355) B1972355
theorem B6656093 : Blo 1313975 6656093 := bstep (se 3 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 6656093 = 2496035) B2496035
theorem B1314923 : Blo 1313975 1314923 := bstep (se 1 (by rfl) ⟨986192, by rfl⟩ : syracuseStep 1314923 = 1972385) B1972385
theorem B1314935 : Blo 1313975 1314935 := bstep (se 1 (by rfl) ⟨986201, by rfl⟩ : syracuseStep 1314935 = 1972403) B1972403
theorem B1314955 : Blo 1313975 1314955 := bstep (se 1 (by rfl) ⟨986216, by rfl⟩ : syracuseStep 1314955 = 1972433) B1972433
theorem B1314967 : Blo 1313975 1314967 := bstep (se 1 (by rfl) ⟨986225, by rfl⟩ : syracuseStep 1314967 = 1972451) B1972451
theorem B1314987 : Blo 1313975 1314987 := bstep (se 1 (by rfl) ⟨986240, by rfl⟩ : syracuseStep 1314987 = 1972481) B1972481
theorem B1478839 : Blo 1313975 1478839 := bstep (se 1 (by rfl) ⟨1109129, by rfl⟩ : syracuseStep 1478839 = 2218259) B2218259
theorem B1314999 : Blo 1313975 1314999 := bstep (se 1 (by rfl) ⟨986249, by rfl⟩ : syracuseStep 1314999 = 1972499) B1972499
theorem B1315019 : Blo 1313975 1315019 := bstep (se 1 (by rfl) ⟨986264, by rfl⟩ : syracuseStep 1315019 = 1972529) B1972529
theorem B1315031 : Blo 1313975 1315031 := bstep (se 1 (by rfl) ⟨986273, by rfl⟩ : syracuseStep 1315031 = 1972547) B1972547
theorem B1315051 : Blo 1313975 1315051 := bstep (se 1 (by rfl) ⟨986288, by rfl⟩ : syracuseStep 1315051 = 1972577) B1972577
theorem B1315063 : Blo 1313975 1315063 := bstep (se 1 (by rfl) ⟨986297, by rfl⟩ : syracuseStep 1315063 = 1972595) B1972595
theorem B1315083 : Blo 1313975 1315083 := bstep (se 1 (by rfl) ⟨986312, by rfl⟩ : syracuseStep 1315083 = 1972625) B1972625
theorem B1315095 : Blo 1313975 1315095 := bstep (se 1 (by rfl) ⟨986321, by rfl⟩ : syracuseStep 1315095 = 1972643) B1972643
theorem B1315115 : Blo 1313975 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B3330355 : Blo 1313975 3330355 := bstep (se 1 (by rfl) ⟨2497766, by rfl⟩ : syracuseStep 3330355 = 4995533) B4995533
theorem B1315127 : Blo 1313975 1315127 := bstep (se 1 (by rfl) ⟨986345, by rfl⟩ : syracuseStep 1315127 = 1972691) B1972691
theorem B1315147 : Blo 1313975 1315147 := bstep (se 1 (by rfl) ⟨986360, by rfl⟩ : syracuseStep 1315147 = 1972721) B1972721
theorem B1315159 : Blo 1313975 1315159 := bstep (se 1 (by rfl) ⟨986369, by rfl⟩ : syracuseStep 1315159 = 1972739) B1972739
theorem B1479019 : Blo 1313975 1479019 := bstep (se 1 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 1479019 = 2218529) B2218529
theorem B1315179 : Blo 1313975 1315179 := bstep (se 1 (by rfl) ⟨986384, by rfl⟩ : syracuseStep 1315179 = 1972769) B1972769
theorem B25268597 : Blo 1313975 25268597 := bstep (se 5 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 25268597 = 2368931) B2368931
theorem B1315191 : Blo 1313975 1315191 := bstep (se 1 (by rfl) ⟨986393, by rfl⟩ : syracuseStep 1315191 = 1972787) B1972787
theorem B1315211 : Blo 1313975 1315211 := bstep (se 1 (by rfl) ⟨986408, by rfl⟩ : syracuseStep 1315211 = 1972817) B1972817
theorem B1315223 : Blo 1313975 1315223 := bstep (se 1 (by rfl) ⟨986417, by rfl⟩ : syracuseStep 1315223 = 1972835) B1972835
theorem B1315243 : Blo 1313975 1315243 := bstep (se 1 (by rfl) ⟨986432, by rfl⟩ : syracuseStep 1315243 = 1972865) B1972865
theorem B1315255 : Blo 1313975 1315255 := bstep (se 1 (by rfl) ⟨986441, by rfl⟩ : syracuseStep 1315255 = 1972883) B1972883
theorem B3330497 : Blo 1313975 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B1315275 : Blo 1313975 1315275 := bstep (se 1 (by rfl) ⟨986456, by rfl⟩ : syracuseStep 1315275 = 1972913) B1972913
theorem B1479127 : Blo 1313975 1479127 := bstep (se 1 (by rfl) ⟨1109345, by rfl⟩ : syracuseStep 1479127 = 2218691) B2218691
theorem B1315287 : Blo 1313975 1315287 := bstep (se 1 (by rfl) ⟨986465, by rfl⟩ : syracuseStep 1315287 = 1972931) B1972931
theorem B1315307 : Blo 1313975 1315307 := bstep (se 1 (by rfl) ⟨986480, by rfl⟩ : syracuseStep 1315307 = 1972961) B1972961
theorem B1315319 : Blo 1313975 1315319 := bstep (se 1 (by rfl) ⟨986489, by rfl⟩ : syracuseStep 1315319 = 1972979) B1972979
theorem B1315339 : Blo 1313975 1315339 := bstep (se 1 (by rfl) ⟨986504, by rfl⟩ : syracuseStep 1315339 = 1973009) B1973009
theorem B2667019 : Blo 1313975 2667019 := bstep (se 1 (by rfl) ⟨2000264, by rfl⟩ : syracuseStep 2667019 = 4000529) B4000529
theorem B4993559 : Blo 1313975 4993559 := bstep (se 1 (by rfl) ⟨3745169, by rfl⟩ : syracuseStep 4993559 = 7490339) B7490339
theorem B1315351 : Blo 1313975 1315351 := bstep (se 1 (by rfl) ⟨986513, by rfl⟩ : syracuseStep 1315351 = 1973027) B1973027
theorem B1315371 : Blo 1313975 1315371 := bstep (se 1 (by rfl) ⟨986528, by rfl⟩ : syracuseStep 1315371 = 1973057) B1973057
theorem B9990701 : Blo 1313975 9990701 := bstep (se 3 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 9990701 = 3746513) B3746513
theorem B4436531 : Blo 1313975 4436531 := bstep (se 1 (by rfl) ⟨3327398, by rfl⟩ : syracuseStep 4436531 = 6654797) B6654797
theorem B1315383 : Blo 1313975 1315383 := bstep (se 1 (by rfl) ⟨986537, by rfl⟩ : syracuseStep 1315383 = 1973075) B1973075
theorem B3551809 : Blo 1313975 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B1315403 : Blo 1313975 1315403 := bstep (se 1 (by rfl) ⟨986552, by rfl⟩ : syracuseStep 1315403 = 1973105) B1973105
theorem B2495063 : Blo 1313975 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B1315415 : Blo 1313975 1315415 := bstep (se 1 (by rfl) ⟨986561, by rfl⟩ : syracuseStep 1315415 = 1973123) B1973123
theorem B1315435 : Blo 1313975 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B1315447 : Blo 1313975 1315447 := bstep (se 1 (by rfl) ⟨986585, by rfl⟩ : syracuseStep 1315447 = 1973171) B1973171
theorem B1479307 : Blo 1313975 1479307 := bstep (se 1 (by rfl) ⟨1109480, by rfl⟩ : syracuseStep 1479307 = 2218961) B2218961
theorem B1315467 : Blo 1313975 1315467 := bstep (se 1 (by rfl) ⟨986600, by rfl⟩ : syracuseStep 1315467 = 1973201) B1973201
theorem B1315479 : Blo 1313975 1315479 := bstep (se 1 (by rfl) ⟨986609, by rfl⟩ : syracuseStep 1315479 = 1973219) B1973219
theorem B1315499 : Blo 1313975 1315499 := bstep (se 1 (by rfl) ⟨986624, by rfl⟩ : syracuseStep 1315499 = 1973249) B1973249
theorem B1315511 : Blo 1313975 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B1315531 : Blo 1313975 1315531 := bstep (se 1 (by rfl) ⟨986648, by rfl⟩ : syracuseStep 1315531 = 1973297) B1973297
theorem B1315543 : Blo 1313975 1315543 := bstep (se 1 (by rfl) ⟨986657, by rfl⟩ : syracuseStep 1315543 = 1973315) B1973315
theorem B4993757 : Blo 1313975 4993757 := bstep (se 3 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 4993757 = 1872659) B1872659
theorem B1315563 : Blo 1313975 1315563 := bstep (se 1 (by rfl) ⟨986672, by rfl⟩ : syracuseStep 1315563 = 1973345) B1973345
theorem B1479415 : Blo 1313975 1479415 := bstep (se 1 (by rfl) ⟨1109561, by rfl⟩ : syracuseStep 1479415 = 2219123) B2219123
theorem B1315575 : Blo 1313975 1315575 := bstep (se 1 (by rfl) ⟨986681, by rfl⟩ : syracuseStep 1315575 = 1973363) B1973363
theorem B1315595 : Blo 1313975 1315595 := bstep (se 1 (by rfl) ⟨986696, by rfl⟩ : syracuseStep 1315595 = 1973393) B1973393
theorem B1315607 : Blo 1313975 1315607 := bstep (se 1 (by rfl) ⟨986705, by rfl⟩ : syracuseStep 1315607 = 1973411) B1973411
theorem B1970969 : Blo 1313975 1970969 := bstep (se 2 (by rfl) ⟨739113, by rfl⟩ : syracuseStep 1970969 = 1478227) B1478227
theorem B1315627 : Blo 1313975 1315627 := bstep (se 1 (by rfl) ⟨986720, by rfl⟩ : syracuseStep 1315627 = 1973441) B1973441
theorem B1315639 : Blo 1313975 1315639 := bstep (se 1 (by rfl) ⟨986729, by rfl⟩ : syracuseStep 1315639 = 1973459) B1973459
theorem B4436801 : Blo 1313975 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B1315659 : Blo 1313975 1315659 := bstep (se 1 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 1315659 = 1973489) B1973489
theorem B1315671 : Blo 1313975 1315671 := bstep (se 1 (by rfl) ⟨986753, by rfl⟩ : syracuseStep 1315671 = 1973507) B1973507
theorem B1315691 : Blo 1313975 1315691 := bstep (se 1 (by rfl) ⟨986768, by rfl⟩ : syracuseStep 1315691 = 1973537) B1973537
theorem B1315703 : Blo 1313975 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1971083 : Blo 1313975 1971083 := bstep (se 1 (by rfl) ⟨1478312, by rfl⟩ : syracuseStep 1971083 = 2956625) B2956625
theorem B1315723 : Blo 1313975 1315723 := bstep (se 1 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 1315723 = 1973585) B1973585
theorem B1971095 : Blo 1313975 1971095 := bstep (se 1 (by rfl) ⟨1478321, by rfl⟩ : syracuseStep 1971095 = 2956643) B2956643
theorem B1315735 : Blo 1313975 1315735 := bstep (se 1 (by rfl) ⟨986801, by rfl⟩ : syracuseStep 1315735 = 1973603) B1973603
theorem B1479595 : Blo 1313975 1479595 := bstep (se 1 (by rfl) ⟨1109696, by rfl⟩ : syracuseStep 1479595 = 2219393) B2219393
theorem B1315755 : Blo 1313975 1315755 := bstep (se 1 (by rfl) ⟨986816, by rfl⟩ : syracuseStep 1315755 = 1973633) B1973633
theorem B1315767 : Blo 1313975 1315767 := bstep (se 1 (by rfl) ⟨986825, by rfl⟩ : syracuseStep 1315767 = 1973651) B1973651
theorem B1315787 : Blo 1313975 1315787 := bstep (se 1 (by rfl) ⟨986840, by rfl⟩ : syracuseStep 1315787 = 1973681) B1973681
theorem B9982925 : Blo 1313975 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B1315799 : Blo 1313975 1315799 := bstep (se 1 (by rfl) ⟨986849, by rfl⟩ : syracuseStep 1315799 = 1973699) B1973699
theorem B1971161 : Blo 1313975 1971161 := bstep (se 2 (by rfl) ⟨739185, by rfl⟩ : syracuseStep 1971161 = 1478371) B1478371
theorem B1315819 : Blo 1313975 1315819 := bstep (se 1 (by rfl) ⟨986864, by rfl⟩ : syracuseStep 1315819 = 1973729) B1973729
theorem B1315831 : Blo 1313975 1315831 := bstep (se 1 (by rfl) ⟨986873, by rfl⟩ : syracuseStep 1315831 = 1973747) B1973747
theorem B1315851 : Blo 1313975 1315851 := bstep (se 1 (by rfl) ⟨986888, by rfl⟩ : syracuseStep 1315851 = 1973777) B1973777
theorem B1479703 : Blo 1313975 1479703 := bstep (se 1 (by rfl) ⟨1109777, by rfl⟩ : syracuseStep 1479703 = 2219555) B2219555
theorem B1315863 : Blo 1313975 1315863 := bstep (se 1 (by rfl) ⟨986897, by rfl⟩ : syracuseStep 1315863 = 1973795) B1973795
theorem B10662947 : Blo 1313975 10662947 := bstep (se 1 (by rfl) ⟨7997210, by rfl⟩ : syracuseStep 10662947 = 15994421) B15994421
theorem B1315883 : Blo 1313975 1315883 := bstep (se 1 (by rfl) ⟨986912, by rfl⟩ : syracuseStep 1315883 = 1973825) B1973825
theorem B1315895 : Blo 1313975 1315895 := bstep (se 1 (by rfl) ⟨986921, by rfl⟩ : syracuseStep 1315895 = 1973843) B1973843
theorem B1971275 : Blo 1313975 1971275 := bstep (se 1 (by rfl) ⟨1478456, by rfl⟩ : syracuseStep 1971275 = 2956913) B2956913
theorem B1315915 : Blo 1313975 1315915 := bstep (se 1 (by rfl) ⟨986936, by rfl⟩ : syracuseStep 1315915 = 1973873) B1973873
theorem B1971287 : Blo 1313975 1971287 := bstep (se 1 (by rfl) ⟨1478465, by rfl⟩ : syracuseStep 1971287 = 2956931) B2956931
theorem B1315927 : Blo 1313975 1315927 := bstep (se 1 (by rfl) ⟨986945, by rfl⟩ : syracuseStep 1315927 = 1973891) B1973891
theorem B1315947 : Blo 1313975 1315947 := bstep (se 1 (by rfl) ⟨986960, by rfl⟩ : syracuseStep 1315947 = 1973921) B1973921
theorem B2495603 : Blo 1313975 2495603 := bstep (se 1 (by rfl) ⟨1871702, by rfl⟩ : syracuseStep 2495603 = 3743405) B3743405
theorem B1315959 : Blo 1313975 1315959 := bstep (se 1 (by rfl) ⟨986969, by rfl⟩ : syracuseStep 1315959 = 1973939) B1973939
theorem B2806913 : Blo 1313975 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B6583427 : Blo 1313975 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B4805777 : Blo 1313975 4805777 := bstep (se 2 (by rfl) ⟨1802166, by rfl⟩ : syracuseStep 4805777 = 3604333) B3604333
theorem B1971353 : Blo 1313975 1971353 := bstep (se 2 (by rfl) ⟨739257, by rfl⟩ : syracuseStep 1971353 = 1478515) B1478515
theorem B1332407 : Blo 1313975 1332407 := bstep (se 1 (by rfl) ⟨999305, by rfl⟩ : syracuseStep 1332407 = 1998611) B1998611
theorem B1479883 : Blo 1313975 1479883 := bstep (se 1 (by rfl) ⟨1109912, by rfl⟩ : syracuseStep 1479883 = 2219825) B2219825
theorem B1971467 : Blo 1313975 1971467 := bstep (se 1 (by rfl) ⟨1478600, by rfl⟩ : syracuseStep 1971467 = 2957201) B2957201
theorem B1971479 : Blo 1313975 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B1479991 : Blo 1313975 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B6321473 : Blo 1313975 6321473 := bstep (se 2 (by rfl) ⟨2370552, by rfl⟩ : syracuseStep 6321473 = 4741105) B4741105
theorem B11392331 : Blo 1313975 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B1971545 : Blo 1313975 1971545 := bstep (se 2 (by rfl) ⟨739329, by rfl⟩ : syracuseStep 1971545 = 1478659) B1478659
theorem B4437341 : Blo 1313975 4437341 := bstep (se 3 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 4437341 = 1664003) B1664003
theorem B38417813 : Blo 1313975 38417813 := bstep (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) B1800835
theorem B9983411 : Blo 1313975 9983411 := bstep (se 1 (by rfl) ⟨7487558, by rfl⟩ : syracuseStep 9983411 = 14975117) B14975117
theorem B1971659 : Blo 1313975 1971659 := bstep (se 1 (by rfl) ⟨1478744, by rfl⟩ : syracuseStep 1971659 = 2957489) B2957489
theorem B1971671 : Blo 1313975 1971671 := bstep (se 1 (by rfl) ⟨1478753, by rfl⟩ : syracuseStep 1971671 = 2957507) B2957507
theorem B1480171 : Blo 1313975 1480171 := bstep (se 1 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 1480171 = 2220257) B2220257
theorem B1971737 : Blo 1313975 1971737 := bstep (se 2 (by rfl) ⟨739401, by rfl⟩ : syracuseStep 1971737 = 1478803) B1478803
theorem B1480279 : Blo 1313975 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B2496089 : Blo 1313975 2496089 := bstep (se 2 (by rfl) ⟨936033, by rfl⟩ : syracuseStep 2496089 = 1872067) B1872067
theorem B2217611 : Blo 1313975 2217611 := bstep (se 1 (by rfl) ⟨1663208, by rfl⟩ : syracuseStep 2217611 = 3326417) B3326417
theorem B1971851 : Blo 1313975 1971851 := bstep (se 1 (by rfl) ⟨1478888, by rfl⟩ : syracuseStep 1971851 = 2957777) B2957777
theorem B1971863 : Blo 1313975 1971863 := bstep (se 1 (by rfl) ⟨1478897, by rfl⟩ : syracuseStep 1971863 = 2957795) B2957795
theorem B1971929 : Blo 1313975 1971929 := bstep (se 2 (by rfl) ⟨739473, by rfl⟩ : syracuseStep 1971929 = 1478947) B1478947
theorem B2217739 : Blo 1313975 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B1922827 : Blo 1313975 1922827 := bstep (se 1 (by rfl) ⟨1442120, by rfl⟩ : syracuseStep 1922827 = 2884241) B2884241
theorem B1480459 : Blo 1313975 1480459 := bstep (se 1 (by rfl) ⟨1110344, by rfl⟩ : syracuseStep 1480459 = 2220689) B2220689
theorem B1972043 : Blo 1313975 1972043 := bstep (se 1 (by rfl) ⟨1479032, by rfl⟩ : syracuseStep 1972043 = 2958065) B2958065
theorem B1972055 : Blo 1313975 1972055 := bstep (se 1 (by rfl) ⟨1479041, by rfl⟩ : syracuseStep 1972055 = 2958083) B2958083
theorem B1333079 : Blo 1313975 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B2217881 : Blo 1313975 2217881 := bstep (se 2 (by rfl) ⟨831705, by rfl⟩ : syracuseStep 2217881 = 1663411) B1663411
theorem B1972121 : Blo 1313975 1972121 := bstep (se 2 (by rfl) ⟨739545, by rfl⟩ : syracuseStep 1972121 = 1479091) B1479091
theorem B1972235 : Blo 1313975 1972235 := bstep (se 1 (by rfl) ⟨1479176, by rfl⟩ : syracuseStep 1972235 = 2958353) B2958353
theorem B11999249 : Blo 1313975 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B1972247 : Blo 1313975 1972247 := bstep (se 1 (by rfl) ⟨1479185, by rfl⟩ : syracuseStep 1972247 = 2958371) B2958371
theorem B2218009 : Blo 1313975 2218009 := bstep (se 2 (by rfl) ⟨831753, by rfl⟩ : syracuseStep 2218009 = 1663507) B1663507
theorem B2250775 : Blo 1313975 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B8419403 : Blo 1313975 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B1972313 : Blo 1313975 1972313 := bstep (se 2 (by rfl) ⟨739617, by rfl⟩ : syracuseStep 1972313 = 1479235) B1479235
theorem B7485533 : Blo 1313975 7485533 := bstep (se 3 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 7485533 = 2807075) B2807075
theorem B9476189 : Blo 1313975 9476189 := bstep (se 3 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 9476189 = 3553571) B3553571
theorem B6658199 : Blo 1313975 6658199 := bstep (se 1 (by rfl) ⟨4993649, by rfl⟩ : syracuseStep 6658199 = 9987299) B9987299
theorem B3741889 : Blo 1313975 3741889 := bstep (se 2 (by rfl) ⟨1403208, by rfl⟩ : syracuseStep 3741889 = 2806417) B2806417
theorem B1972427 : Blo 1313975 1972427 := bstep (se 1 (by rfl) ⟨1479320, by rfl⟩ : syracuseStep 1972427 = 2958641) B2958641
theorem B1972439 : Blo 1313975 1972439 := bstep (se 1 (by rfl) ⟨1479329, by rfl⟩ : syracuseStep 1972439 = 2958659) B2958659
theorem B5994769 : Blo 1313975 5994769 := bstep (se 2 (by rfl) ⟨2248038, by rfl⟩ : syracuseStep 5994769 = 4496077) B4496077
theorem B5691665 : Blo 1313975 5691665 := bstep (se 2 (by rfl) ⟨2134374, by rfl⟩ : syracuseStep 5691665 = 4268749) B4268749
theorem B1972505 : Blo 1313975 1972505 := bstep (se 2 (by rfl) ⟨739689, by rfl⟩ : syracuseStep 1972505 = 1479379) B1479379
theorem B3553625 : Blo 1313975 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B1972619 : Blo 1313975 1972619 := bstep (se 1 (by rfl) ⟨1479464, by rfl⟩ : syracuseStep 1972619 = 2958929) B2958929
theorem B1972631 : Blo 1313975 1972631 := bstep (se 1 (by rfl) ⟨1479473, by rfl⟩ : syracuseStep 1972631 = 2958947) B2958947
theorem B4438475 : Blo 1313975 4438475 := bstep (se 1 (by rfl) ⟨3328856, by rfl⟩ : syracuseStep 4438475 = 6657713) B6657713
theorem B1972697 : Blo 1313975 1972697 := bstep (se 2 (by rfl) ⟨739761, by rfl⟩ : syracuseStep 1972697 = 1479523) B1479523
theorem B3996125 : Blo 1313975 3996125 := bstep (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) B1498547
theorem B1686091 : Blo 1313975 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B1579595 : Blo 1313975 1579595 := bstep (se 1 (by rfl) ⟨1184696, by rfl⟩ : syracuseStep 1579595 = 2369393) B2369393
theorem B1972811 : Blo 1313975 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B2218583 : Blo 1313975 2218583 := bstep (se 1 (by rfl) ⟨1663937, by rfl⟩ : syracuseStep 2218583 = 3327875) B3327875
theorem B1972823 : Blo 1313975 1972823 := bstep (se 1 (by rfl) ⟨1479617, by rfl⟩ : syracuseStep 1972823 = 2959235) B2959235
theorem B40483421 : Blo 1313975 40483421 := bstep (se 3 (by rfl) ⟨7590641, by rfl⟩ : syracuseStep 40483421 = 15181283) B15181283
theorem B4995715 : Blo 1313975 4995715 := bstep (se 1 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 4995715 = 7493573) B7493573
theorem B9484951 : Blo 1313975 9484951 := bstep (se 1 (by rfl) ⟨7113713, by rfl⟩ : syracuseStep 9484951 = 14227427) B14227427
theorem B1972889 : Blo 1313975 1972889 := bstep (se 2 (by rfl) ⟨739833, by rfl⟩ : syracuseStep 1972889 = 1479667) B1479667
theorem B33684173 : Blo 1313975 33684173 := bstep (se 3 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 33684173 = 12631565) B12631565
theorem B2218711 : Blo 1313975 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B4438745 : Blo 1313975 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B2808587 : Blo 1313975 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B1973003 : Blo 1313975 1973003 := bstep (se 1 (by rfl) ⟨1479752, by rfl⟩ : syracuseStep 1973003 = 2959505) B2959505
theorem B5692183 : Blo 1313975 5692183 := bstep (se 1 (by rfl) ⟨4269137, by rfl⟩ : syracuseStep 5692183 = 8538275) B8538275
theorem B1973015 : Blo 1313975 1973015 := bstep (se 1 (by rfl) ⟨1479761, by rfl⟩ : syracuseStep 1973015 = 2959523) B2959523
theorem B7486283 : Blo 1313975 7486283 := bstep (se 1 (by rfl) ⟨5614712, by rfl⟩ : syracuseStep 7486283 = 11229425) B11229425
theorem B4209497 : Blo 1313975 4209497 := bstep (se 2 (by rfl) ⟨1578561, by rfl⟩ : syracuseStep 4209497 = 3157123) B3157123
theorem B1973081 : Blo 1313975 1973081 := bstep (se 2 (by rfl) ⟨739905, by rfl⟩ : syracuseStep 1973081 = 1479811) B1479811
theorem B9984869 : Blo 1313975 9984869 := bstep (se 4 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 9984869 = 1872163) B1872163
theorem B1579927 : Blo 1313975 1579927 := bstep (se 1 (by rfl) ⟨1184945, by rfl⟩ : syracuseStep 1579927 = 2369891) B2369891
theorem B4996019 : Blo 1313975 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B1973195 : Blo 1313975 1973195 := bstep (se 1 (by rfl) ⟨1479896, by rfl⟩ : syracuseStep 1973195 = 2959793) B2959793
theorem B3161035 : Blo 1313975 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B1973207 : Blo 1313975 1973207 := bstep (se 1 (by rfl) ⟨1479905, by rfl⟩ : syracuseStep 1973207 = 2959811) B2959811
theorem B2497547 : Blo 1313975 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B1973273 : Blo 1313975 1973273 := bstep (se 2 (by rfl) ⟨739977, by rfl⟩ : syracuseStep 1973273 = 1479955) B1479955
theorem B5332043 : Blo 1313975 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B1973387 : Blo 1313975 1973387 := bstep (se 1 (by rfl) ⟨1480040, by rfl⟩ : syracuseStep 1973387 = 2960081) B2960081
theorem B1973399 : Blo 1313975 1973399 := bstep (se 1 (by rfl) ⟨1480049, by rfl⟩ : syracuseStep 1973399 = 2960099) B2960099
theorem B2956481 : Blo 1313975 2956481 := bstep (se 2 (by rfl) ⟨1108680, by rfl⟩ : syracuseStep 2956481 = 2217361) B2217361
theorem B4209857 : Blo 1313975 4209857 := bstep (se 2 (by rfl) ⟨1578696, by rfl⟩ : syracuseStep 4209857 = 3157393) B3157393
theorem B2497729 : Blo 1313975 2497729 := bstep (se 2 (by rfl) ⟨936648, by rfl⟩ : syracuseStep 2497729 = 1873297) B1873297
theorem B1973465 : Blo 1313975 1973465 := bstep (se 2 (by rfl) ⟨740049, by rfl⟩ : syracuseStep 1973465 = 1480099) B1480099
theorem B1580311 : Blo 1313975 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B9985355 : Blo 1313975 9985355 := bstep (se 1 (by rfl) ⟨7489016, by rfl⟩ : syracuseStep 9985355 = 14978033) B14978033
theorem B2219339 : Blo 1313975 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B1973579 : Blo 1313975 1973579 := bstep (se 1 (by rfl) ⟨1480184, by rfl⟩ : syracuseStep 1973579 = 2960369) B2960369
theorem B1973591 : Blo 1313975 1973591 := bstep (se 1 (by rfl) ⟨1480193, by rfl⟩ : syracuseStep 1973591 = 2960387) B2960387
theorem B4742489 : Blo 1313975 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B9485669 : Blo 1313975 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B4439447 : Blo 1313975 4439447 := bstep (se 1 (by rfl) ⟨3329585, by rfl⟩ : syracuseStep 4439447 = 6659171) B6659171
theorem B2956697 : Blo 1313975 2956697 := bstep (se 2 (by rfl) ⟨1108761, by rfl⟩ : syracuseStep 2956697 = 2217523) B2217523
theorem B1973657 : Blo 1313975 1973657 := bstep (se 2 (by rfl) ⟨740121, by rfl⟩ : syracuseStep 1973657 = 1480243) B1480243
theorem B2219467 : Blo 1313975 2219467 := bstep (se 1 (by rfl) ⟨1664600, by rfl⟩ : syracuseStep 2219467 = 3329201) B3329201
theorem B2956787 : Blo 1313975 2956787 := bstep (se 1 (by rfl) ⟨2217590, by rfl⟩ : syracuseStep 2956787 = 4435181) B4435181
theorem B1973771 : Blo 1313975 1973771 := bstep (se 1 (by rfl) ⟨1480328, by rfl⟩ : syracuseStep 1973771 = 2960657) B2960657
theorem B2956823 : Blo 1313975 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B5619223 : Blo 1313975 5619223 := bstep (se 1 (by rfl) ⟨4214417, by rfl⟩ : syracuseStep 5619223 = 8428835) B8428835
theorem B1973783 : Blo 1313975 1973783 := bstep (se 1 (by rfl) ⟨1480337, by rfl⟩ : syracuseStep 1973783 = 2960675) B2960675
theorem B4742707 : Blo 1313975 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B2219609 : Blo 1313975 2219609 := bstep (se 2 (by rfl) ⟨832353, by rfl⟩ : syracuseStep 2219609 = 1664707) B1664707
theorem B1973849 : Blo 1313975 1973849 := bstep (se 2 (by rfl) ⟨740193, by rfl⟩ : syracuseStep 1973849 = 1480387) B1480387
theorem B5619293 : Blo 1313975 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B4742749 : Blo 1313975 4742749 := bstep (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) B1778531
theorem B2498177 : Blo 1313975 2498177 := bstep (se 2 (by rfl) ⟨936816, by rfl⟩ : syracuseStep 2498177 = 1873633) B1873633
theorem B2957003 : Blo 1313975 2957003 := bstep (se 1 (by rfl) ⟨2217752, by rfl⟩ : syracuseStep 2957003 = 4435505) B4435505
theorem B1973963 : Blo 1313975 1973963 := bstep (se 1 (by rfl) ⟨1480472, by rfl⟩ : syracuseStep 1973963 = 2960945) B2960945
theorem B2219737 : Blo 1313975 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B2809561 : Blo 1313975 2809561 := bstep (se 2 (by rfl) ⟨1053585, by rfl⟩ : syracuseStep 2809561 = 2107171) B2107171
theorem B2957057 : Blo 1313975 2957057 := bstep (se 2 (by rfl) ⟨1108896, by rfl⟩ : syracuseStep 2957057 = 2217793) B2217793
theorem B3555137 : Blo 1313975 3555137 := bstep (se 2 (by rfl) ⟨1333176, by rfl⟩ : syracuseStep 3555137 = 2666353) B2666353
theorem B2531137 : Blo 1313975 2531137 := bstep (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) B1898353
theorem B15998897 : Blo 1313975 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B4439987 : Blo 1313975 4439987 := bstep (se 1 (by rfl) ⟨3329990, by rfl⟩ : syracuseStep 4439987 = 6659981) B6659981
theorem B4210625 : Blo 1313975 4210625 := bstep (se 2 (by rfl) ⟨1578984, by rfl⟩ : syracuseStep 4210625 = 3157969) B3157969
theorem B1499095 : Blo 1313975 1499095 := bstep (se 1 (by rfl) ⟨1124321, by rfl⟩ : syracuseStep 1499095 = 2248643) B2248643
theorem B2957273 : Blo 1313975 2957273 := bstep (se 2 (by rfl) ⟨1108977, by rfl⟩ : syracuseStep 2957273 = 2217955) B2217955
theorem B2809817 : Blo 1313975 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B2957327 : Blo 1313975 2957327 := bstep (se 1 (by rfl) ⟨2217995, by rfl⟩ : syracuseStep 2957327 = 4435991) B4435991
theorem B2957345 : Blo 1313975 2957345 := bstep (se 2 (by rfl) ⟨1109004, by rfl⟩ : syracuseStep 2957345 = 2218009) B2218009
theorem B2310187 : Blo 1313975 2310187 := bstep (se 1 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 2310187 = 3465281) B3465281
theorem B28442825 : Blo 1313975 28442825 := bstep (se 2 (by rfl) ⟨10666059, by rfl⟩ : syracuseStep 28442825 = 21332119) B21332119
theorem B4989185 : Blo 1313975 4989185 := bstep (se 2 (by rfl) ⟨1870944, by rfl⟩ : syracuseStep 4989185 = 3741889) B3741889
theorem B2220331 : Blo 1313975 2220331 := bstep (se 1 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 2220331 = 3330497) B3330497
theorem B6660467 : Blo 1313975 6660467 := bstep (se 1 (by rfl) ⟨4995350, by rfl⟩ : syracuseStep 6660467 = 9990701) B9990701
theorem B2957687 : Blo 1313975 2957687 := bstep (se 1 (by rfl) ⟨2218265, by rfl⟩ : syracuseStep 2957687 = 4436531) B4436531
theorem B4440473 : Blo 1313975 4440473 := bstep (se 2 (by rfl) ⟨1665177, by rfl⟩ : syracuseStep 4440473 = 3330355) B3330355
theorem B2220473 : Blo 1313975 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B2957867 : Blo 1313975 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B3326579 : Blo 1313975 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B3556025 : Blo 1313975 3556025 := bstep (se 2 (by rfl) ⟨1333509, by rfl⟩ : syracuseStep 3556025 = 2667019) B2667019
theorem B1663735 : Blo 1313975 1663735 := bstep (se 1 (by rfl) ⟨1247801, by rfl⟩ : syracuseStep 1663735 = 2495603) B2495603
theorem B4735745 : Blo 1313975 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B11535193 : Blo 1313975 11535193 := bstep (se 2 (by rfl) ⟨4325697, by rfl⟩ : syracuseStep 11535193 = 8651395) B8651395
theorem B6660953 : Blo 1313975 6660953 := bstep (se 2 (by rfl) ⟨2497857, by rfl⟩ : syracuseStep 6660953 = 4995715) B4995715
theorem B2958227 : Blo 1313975 2958227 := bstep (se 1 (by rfl) ⟨2218670, by rfl⟩ : syracuseStep 2958227 = 4437341) B4437341
theorem B2958281 : Blo 1313975 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B1664059 : Blo 1313975 1664059 := bstep (se 1 (by rfl) ⟨1248044, by rfl⟩ : syracuseStep 1664059 = 2496089) B2496089
theorem B6653015 : Blo 1313975 6653015 := bstep (se 1 (by rfl) ⟨4989761, by rfl⟩ : syracuseStep 6653015 = 9979523) B9979523
theorem B4441175 : Blo 1313975 4441175 := bstep (se 1 (by rfl) ⟨3330881, by rfl⟩ : syracuseStep 4441175 = 6661763) B6661763
theorem B3327095 : Blo 1313975 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B2106569 : Blo 1313975 2106569 := bstep (se 2 (by rfl) ⟨789963, by rfl⟩ : syracuseStep 2106569 = 1579927) B1579927
theorem B13862161 : Blo 1313975 13862161 := bstep (se 2 (by rfl) ⟨5198310, by rfl⟩ : syracuseStep 13862161 = 10396621) B10396621
theorem B4621627 : Blo 1313975 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B4990355 : Blo 1313975 4990355 := bstep (se 1 (by rfl) ⟨3742766, by rfl⟩ : syracuseStep 4990355 = 7485533) B7485533
theorem B6317459 : Blo 1313975 6317459 := bstep (se 1 (by rfl) ⟨4738094, by rfl⟩ : syracuseStep 6317459 = 9476189) B9476189
theorem B4212253 : Blo 1313975 4212253 := bstep (se 3 (by rfl) ⟨789797, by rfl⟩ : syracuseStep 4212253 = 1579595) B1579595
theorem B2369083 : Blo 1313975 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B6653501 : Blo 1313975 6653501 := bstep (se 3 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 6653501 = 2495063) B2495063
theorem B2958983 : Blo 1313975 2958983 := bstep (se 1 (by rfl) ⟨2219237, by rfl⟩ : syracuseStep 2958983 = 4438475) B4438475
theorem B2664083 : Blo 1313975 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B2107081 : Blo 1313975 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B22456115 : Blo 1313975 22456115 := bstep (se 1 (by rfl) ⟨16842086, by rfl⟩ : syracuseStep 22456115 = 33684173) B33684173
theorem B2959163 : Blo 1313975 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B4990855 : Blo 1313975 4990855 := bstep (se 1 (by rfl) ⟨3743141, by rfl⟩ : syracuseStep 4990855 = 7486283) B7486283
theorem B2959289 : Blo 1313975 2959289 := bstep (se 2 (by rfl) ⟨1109733, by rfl⟩ : syracuseStep 2959289 = 2219467) B2219467
theorem B1665031 : Blo 1313975 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B7997501 : Blo 1313975 7997501 := bstep (se 3 (by rfl) ⟨1499531, by rfl⟩ : syracuseStep 7997501 = 2999063) B2999063
theorem B3328087 : Blo 1313975 3328087 := bstep (se 1 (by rfl) ⟨2496065, by rfl⟩ : syracuseStep 3328087 = 4992131) B4992131
theorem B7489655 : Blo 1313975 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B9480365 : Blo 1313975 9480365 := bstep (se 3 (by rfl) ⟨1777568, by rfl⟩ : syracuseStep 9480365 = 3555137) B3555137
theorem B2959631 : Blo 1313975 2959631 := bstep (se 1 (by rfl) ⟨2219723, by rfl⟩ : syracuseStep 2959631 = 4439447) B4439447
theorem B2959649 : Blo 1313975 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B3746081 : Blo 1313975 3746081 := bstep (se 2 (by rfl) ⟨1404780, by rfl⟩ : syracuseStep 3746081 = 2809561) B2809561
theorem B7489907 : Blo 1313975 7489907 := bstep (se 1 (by rfl) ⟨5617430, by rfl⟩ : syracuseStep 7489907 = 11234861) B11234861
theorem B3328391 : Blo 1313975 3328391 := bstep (se 1 (by rfl) ⟨2496293, by rfl⟩ : syracuseStep 3328391 = 4992587) B4992587
theorem B3746195 : Blo 1313975 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B1665451 : Blo 1313975 1665451 := bstep (se 1 (by rfl) ⟨1249088, by rfl⟩ : syracuseStep 1665451 = 2498177) B2498177
theorem B3328523 : Blo 1313975 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B2959991 : Blo 1313975 2959991 := bstep (se 1 (by rfl) ⟨2219993, by rfl⟩ : syracuseStep 2959991 = 4439987) B4439987
theorem B3001033 : Blo 1313975 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B2960171 : Blo 1313975 2960171 := bstep (se 1 (by rfl) ⟨2220128, by rfl⟩ : syracuseStep 2960171 = 4440257) B4440257
theorem B4434803 : Blo 1313975 4434803 := bstep (se 1 (by rfl) ⟨3326102, by rfl⟩ : syracuseStep 4434803 = 6652205) B6652205
theorem B16845731 : Blo 1313975 16845731 := bstep (se 1 (by rfl) ⟨12634298, by rfl⟩ : syracuseStep 16845731 = 25268597) B25268597
theorem B3329039 : Blo 1313975 3329039 := bstep (se 1 (by rfl) ⟨2496779, by rfl⟩ : syracuseStep 3329039 = 4993559) B4993559
theorem B12815405 : Blo 1313975 12815405 := bstep (se 3 (by rfl) ⟨2402888, by rfl⟩ : syracuseStep 12815405 = 4805777) B4805777
theorem B3329171 : Blo 1313975 3329171 := bstep (se 1 (by rfl) ⟨2496878, by rfl⟩ : syracuseStep 3329171 = 4993757) B4993757
theorem B2960531 : Blo 1313975 2960531 := bstep (se 1 (by rfl) ⟨2220398, by rfl⟩ : syracuseStep 2960531 = 4440797) B4440797
theorem B3746969 : Blo 1313975 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B2665657 : Blo 1313975 2665657 := bstep (se 2 (by rfl) ⟨999621, by rfl⟩ : syracuseStep 2665657 = 1999243) B1999243
theorem B1313979 : Blo 1313975 1313979 := bstep (se 1 (by rfl) ⟨985484, by rfl⟩ : syracuseStep 1313979 = 1970969) B1970969
theorem B2960585 : Blo 1313975 2960585 := bstep (se 2 (by rfl) ⟨1110219, by rfl⟩ : syracuseStep 2960585 = 2220439) B2220439
theorem B5614849 : Blo 1313975 5614849 := bstep (se 2 (by rfl) ⟨2105568, by rfl⟩ : syracuseStep 5614849 = 4211137) B4211137
theorem B1314055 : Blo 1313975 1314055 := bstep (se 1 (by rfl) ⟨985541, by rfl⟩ : syracuseStep 1314055 = 1971083) B1971083
theorem B1314063 : Blo 1313975 1314063 := bstep (se 1 (by rfl) ⟨985547, by rfl⟩ : syracuseStep 1314063 = 1971095) B1971095
theorem B6655283 : Blo 1313975 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B1314107 : Blo 1313975 1314107 := bstep (se 1 (by rfl) ⟨985580, by rfl⟩ : syracuseStep 1314107 = 1971161) B1971161
theorem B12643715 : Blo 1313975 12643715 := bstep (se 1 (by rfl) ⟨9482786, by rfl⟩ : syracuseStep 12643715 = 18965573) B18965573
theorem B1314183 : Blo 1313975 1314183 := bstep (se 1 (by rfl) ⟨985637, by rfl⟩ : syracuseStep 1314183 = 1971275) B1971275
theorem B1314191 : Blo 1313975 1314191 := bstep (se 1 (by rfl) ⟨985643, by rfl⟩ : syracuseStep 1314191 = 1971287) B1971287
theorem B1871275 : Blo 1313975 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B2248121 : Blo 1313975 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B1314235 : Blo 1313975 1314235 := bstep (se 1 (by rfl) ⟨985676, by rfl⟩ : syracuseStep 1314235 = 1971353) B1971353
theorem B20254157 : Blo 1313975 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B1314311 : Blo 1313975 1314311 := bstep (se 1 (by rfl) ⟨985733, by rfl⟩ : syracuseStep 1314311 = 1971467) B1971467
theorem B1314319 : Blo 1313975 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B30379549 : Blo 1313975 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B14986781 : Blo 1313975 14986781 := bstep (se 3 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 14986781 = 5620043) B5620043
theorem B4214315 : Blo 1313975 4214315 := bstep (se 1 (by rfl) ⟨3160736, by rfl⟩ : syracuseStep 4214315 = 6321473) B6321473
theorem B1314363 : Blo 1313975 1314363 := bstep (se 1 (by rfl) ⟨985772, by rfl⟩ : syracuseStep 1314363 = 1971545) B1971545
theorem B25611875 : Blo 1313975 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B6655607 : Blo 1313975 6655607 := bstep (se 1 (by rfl) ⟨4991705, by rfl⟩ : syracuseStep 6655607 = 9983411) B9983411
theorem B1314439 : Blo 1313975 1314439 := bstep (se 1 (by rfl) ⟨985829, by rfl⟩ : syracuseStep 1314439 = 1971659) B1971659
theorem B1314447 : Blo 1313975 1314447 := bstep (se 1 (by rfl) ⟨985835, by rfl⟩ : syracuseStep 1314447 = 1971671) B1971671
theorem B1314491 : Blo 1313975 1314491 := bstep (se 1 (by rfl) ⟨985868, by rfl⟩ : syracuseStep 1314491 = 1971737) B1971737
theorem B1478407 : Blo 1313975 1478407 := bstep (se 1 (by rfl) ⟨1108805, by rfl⟩ : syracuseStep 1478407 = 2217611) B2217611
theorem B1314567 : Blo 1313975 1314567 := bstep (se 1 (by rfl) ⟨985925, by rfl⟩ : syracuseStep 1314567 = 1971851) B1971851
theorem B1314575 : Blo 1313975 1314575 := bstep (se 1 (by rfl) ⟨985931, by rfl⟩ : syracuseStep 1314575 = 1971863) B1971863
theorem B7491365 : Blo 1313975 7491365 := bstep (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) B1404631
theorem B1314619 : Blo 1313975 1314619 := bstep (se 1 (by rfl) ⟨985964, by rfl⟩ : syracuseStep 1314619 = 1971929) B1971929
theorem B1314695 : Blo 1313975 1314695 := bstep (se 1 (by rfl) ⟨986021, by rfl⟩ : syracuseStep 1314695 = 1972043) B1972043
theorem B1314703 : Blo 1313975 1314703 := bstep (se 1 (by rfl) ⟨986027, by rfl⟩ : syracuseStep 1314703 = 1972055) B1972055
theorem B1478587 : Blo 1313975 1478587 := bstep (se 1 (by rfl) ⟨1108940, by rfl⟩ : syracuseStep 1478587 = 2217881) B2217881
theorem B1314747 : Blo 1313975 1314747 := bstep (se 1 (by rfl) ⟨986060, by rfl⟩ : syracuseStep 1314747 = 1972121) B1972121
theorem B16838603 : Blo 1313975 16838603 := bstep (se 1 (by rfl) ⟨12628952, by rfl⟩ : syracuseStep 16838603 = 25257905) B25257905
theorem B1314823 : Blo 1313975 1314823 := bstep (se 1 (by rfl) ⟨986117, by rfl⟩ : syracuseStep 1314823 = 1972235) B1972235
theorem B7999499 : Blo 1313975 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1314831 : Blo 1313975 1314831 := bstep (se 1 (by rfl) ⟨986123, by rfl⟩ : syracuseStep 1314831 = 1972247) B1972247
theorem B26980397 : Blo 1313975 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B1314875 : Blo 1313975 1314875 := bstep (se 1 (by rfl) ⟨986156, by rfl⟩ : syracuseStep 1314875 = 1972313) B1972313
theorem B1314951 : Blo 1313975 1314951 := bstep (se 1 (by rfl) ⟨986213, by rfl⟩ : syracuseStep 1314951 = 1972427) B1972427
theorem B1314959 : Blo 1313975 1314959 := bstep (se 1 (by rfl) ⟨986219, by rfl⟩ : syracuseStep 1314959 = 1972439) B1972439
theorem B1315003 : Blo 1313975 1315003 := bstep (se 1 (by rfl) ⟨986252, by rfl⟩ : syracuseStep 1315003 = 1972505) B1972505
theorem B3330305 : Blo 1313975 3330305 := bstep (se 2 (by rfl) ⟨1248864, by rfl⟩ : syracuseStep 3330305 = 2497729) B2497729
theorem B1315079 : Blo 1313975 1315079 := bstep (se 1 (by rfl) ⟨986309, by rfl⟩ : syracuseStep 1315079 = 1972619) B1972619
theorem B1315087 : Blo 1313975 1315087 := bstep (se 1 (by rfl) ⟨986315, by rfl⟩ : syracuseStep 1315087 = 1972631) B1972631
theorem B1405199 : Blo 1313975 1405199 := bstep (se 1 (by rfl) ⟨1053899, by rfl⟩ : syracuseStep 1405199 = 2107799) B2107799
theorem B1315131 : Blo 1313975 1315131 := bstep (se 1 (by rfl) ⟨986348, by rfl⟩ : syracuseStep 1315131 = 1972697) B1972697
theorem B1315207 : Blo 1313975 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B1479055 : Blo 1313975 1479055 := bstep (se 1 (by rfl) ⟨1109291, by rfl⟩ : syracuseStep 1479055 = 2218583) B2218583
theorem B1315215 : Blo 1313975 1315215 := bstep (se 1 (by rfl) ⟨986411, by rfl⟩ : syracuseStep 1315215 = 1972823) B1972823
theorem B26988947 : Blo 1313975 26988947 := bstep (se 1 (by rfl) ⟨20241710, by rfl⟩ : syracuseStep 26988947 = 40483421) B40483421
theorem B1315259 : Blo 1313975 1315259 := bstep (se 1 (by rfl) ⟨986444, by rfl⟩ : syracuseStep 1315259 = 1972889) B1972889
theorem B1872391 : Blo 1313975 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B1315335 : Blo 1313975 1315335 := bstep (se 1 (by rfl) ⟨986501, by rfl⟩ : syracuseStep 1315335 = 1973003) B1973003
theorem B1315343 : Blo 1313975 1315343 := bstep (se 1 (by rfl) ⟨986507, by rfl⟩ : syracuseStep 1315343 = 1973015) B1973015
theorem B2806331 : Blo 1313975 2806331 := bstep (se 1 (by rfl) ⟨2104748, by rfl⟩ : syracuseStep 2806331 = 4209497) B4209497
theorem B1315387 : Blo 1313975 1315387 := bstep (se 1 (by rfl) ⟨986540, by rfl⟩ : syracuseStep 1315387 = 1973081) B1973081
theorem B6656579 : Blo 1313975 6656579 := bstep (se 1 (by rfl) ⟨4992434, by rfl⟩ : syracuseStep 6656579 = 9984869) B9984869
theorem B3330679 : Blo 1313975 3330679 := bstep (se 1 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 3330679 = 4996019) B4996019
theorem B1315463 : Blo 1313975 1315463 := bstep (se 1 (by rfl) ⟨986597, by rfl⟩ : syracuseStep 1315463 = 1973195) B1973195
theorem B1315471 : Blo 1313975 1315471 := bstep (se 1 (by rfl) ⟨986603, by rfl⟩ : syracuseStep 1315471 = 1973207) B1973207
theorem B1315515 : Blo 1313975 1315515 := bstep (se 1 (by rfl) ⟨986636, by rfl⟩ : syracuseStep 1315515 = 1973273) B1973273
theorem B7492297 : Blo 1313975 7492297 := bstep (se 2 (by rfl) ⟨2809611, by rfl⟩ : syracuseStep 7492297 = 5619223) B5619223
theorem B1315591 : Blo 1313975 1315591 := bstep (se 1 (by rfl) ⟨986693, by rfl⟩ : syracuseStep 1315591 = 1973387) B1973387
theorem B1315599 : Blo 1313975 1315599 := bstep (se 1 (by rfl) ⟨986699, by rfl⟩ : syracuseStep 1315599 = 1973399) B1973399
theorem B1970987 : Blo 1313975 1970987 := bstep (se 1 (by rfl) ⟨1478240, by rfl⟩ : syracuseStep 1970987 = 2956481) B2956481
theorem B2806571 : Blo 1313975 2806571 := bstep (se 1 (by rfl) ⟨2104928, by rfl⟩ : syracuseStep 2806571 = 4209857) B4209857
theorem B1315643 : Blo 1313975 1315643 := bstep (se 1 (by rfl) ⟨986732, by rfl⟩ : syracuseStep 1315643 = 1973465) B1973465
theorem B1971017 : Blo 1313975 1971017 := bstep (se 2 (by rfl) ⟨739131, by rfl⟩ : syracuseStep 1971017 = 1478263) B1478263
theorem B6656903 : Blo 1313975 6656903 := bstep (se 1 (by rfl) ⟨4992677, by rfl⟩ : syracuseStep 6656903 = 9985355) B9985355
theorem B1479559 : Blo 1313975 1479559 := bstep (se 1 (by rfl) ⟨1109669, by rfl⟩ : syracuseStep 1479559 = 2219339) B2219339
theorem B1315719 : Blo 1313975 1315719 := bstep (se 1 (by rfl) ⟨986789, by rfl⟩ : syracuseStep 1315719 = 1973579) B1973579
theorem B1315727 : Blo 1313975 1315727 := bstep (se 1 (by rfl) ⟨986795, by rfl⟩ : syracuseStep 1315727 = 1973591) B1973591
theorem B11236259 : Blo 1313975 11236259 := bstep (se 1 (by rfl) ⟨8427194, by rfl⟩ : syracuseStep 11236259 = 16854389) B16854389
theorem B1971131 : Blo 1313975 1971131 := bstep (se 1 (by rfl) ⟨1478348, by rfl⟩ : syracuseStep 1971131 = 2956697) B2956697
theorem B1315771 : Blo 1313975 1315771 := bstep (se 1 (by rfl) ⟨986828, by rfl⟩ : syracuseStep 1315771 = 1973657) B1973657
theorem B1971191 : Blo 1313975 1971191 := bstep (se 1 (by rfl) ⟨1478393, by rfl⟩ : syracuseStep 1971191 = 2956787) B2956787
theorem B1315847 : Blo 1313975 1315847 := bstep (se 1 (by rfl) ⟨986885, by rfl⟩ : syracuseStep 1315847 = 1973771) B1973771
theorem B1971215 : Blo 1313975 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B1315855 : Blo 1313975 1315855 := bstep (se 1 (by rfl) ⟨986891, by rfl⟩ : syracuseStep 1315855 = 1973783) B1973783
theorem B1971257 : Blo 1313975 1971257 := bstep (se 2 (by rfl) ⟨739221, by rfl⟩ : syracuseStep 1971257 = 1478443) B1478443
theorem B1479739 : Blo 1313975 1479739 := bstep (se 1 (by rfl) ⟨1109804, by rfl⟩ : syracuseStep 1479739 = 2219609) B2219609
theorem B1315899 : Blo 1313975 1315899 := bstep (se 1 (by rfl) ⟨986924, by rfl⟩ : syracuseStep 1315899 = 1973849) B1973849
theorem B1971335 : Blo 1313975 1971335 := bstep (se 1 (by rfl) ⟨1478501, by rfl⟩ : syracuseStep 1971335 = 2957003) B2957003
theorem B1315975 : Blo 1313975 1315975 := bstep (se 1 (by rfl) ⟨986981, by rfl⟩ : syracuseStep 1315975 = 1973963) B1973963
theorem B1971371 : Blo 1313975 1971371 := bstep (se 1 (by rfl) ⟨1478528, by rfl⟩ : syracuseStep 1971371 = 2957057) B2957057
theorem B1971401 : Blo 1313975 1971401 := bstep (se 2 (by rfl) ⟨739275, by rfl⟩ : syracuseStep 1971401 = 1478551) B1478551
theorem B2807083 : Blo 1313975 2807083 := bstep (se 1 (by rfl) ⟨2105312, by rfl⟩ : syracuseStep 2807083 = 4210625) B4210625
theorem B1971515 : Blo 1313975 1971515 := bstep (se 1 (by rfl) ⟨1478636, by rfl⟩ : syracuseStep 1971515 = 2957273) B2957273
theorem B1873211 : Blo 1313975 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B1971575 : Blo 1313975 1971575 := bstep (se 1 (by rfl) ⟨1478681, by rfl⟩ : syracuseStep 1971575 = 2957363) B2957363
theorem B2250119 : Blo 1313975 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B1971599 : Blo 1313975 1971599 := bstep (se 1 (by rfl) ⟨1478699, by rfl⟩ : syracuseStep 1971599 = 2957399) B2957399
theorem B4437395 : Blo 1313975 4437395 := bstep (se 1 (by rfl) ⟨3328046, by rfl⟩ : syracuseStep 4437395 = 6656093) B6656093
theorem B7484825 : Blo 1313975 7484825 := bstep (se 2 (by rfl) ⟨2806809, by rfl⟩ : syracuseStep 7484825 = 5613619) B5613619
theorem B1971641 : Blo 1313975 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B2495929 : Blo 1313975 2495929 := bstep (se 2 (by rfl) ⟨935973, by rfl⟩ : syracuseStep 2495929 = 1871947) B1871947
theorem B1971719 : Blo 1313975 1971719 := bstep (se 1 (by rfl) ⟨1478789, by rfl⟩ : syracuseStep 1971719 = 2957579) B2957579
theorem B1480207 : Blo 1313975 1480207 := bstep (se 1 (by rfl) ⟨1110155, by rfl⟩ : syracuseStep 1480207 = 2220311) B2220311
theorem B22451741 : Blo 1313975 22451741 := bstep (se 3 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 22451741 = 8419403) B8419403
theorem B1971755 : Blo 1313975 1971755 := bstep (se 1 (by rfl) ⟨1478816, by rfl⟩ : syracuseStep 1971755 = 2957633) B2957633
theorem B1971785 : Blo 1313975 1971785 := bstep (se 2 (by rfl) ⟨739419, by rfl⟩ : syracuseStep 1971785 = 1478839) B1478839
theorem B3159737 : Blo 1313975 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1971899 : Blo 1313975 1971899 := bstep (se 1 (by rfl) ⟨1478924, by rfl⟩ : syracuseStep 1971899 = 2957849) B2957849
theorem B7993025 : Blo 1313975 7993025 := bstep (se 2 (by rfl) ⟨2997384, by rfl⟩ : syracuseStep 7993025 = 5994769) B5994769
theorem B1971959 : Blo 1313975 1971959 := bstep (se 1 (by rfl) ⟨1478969, by rfl⟩ : syracuseStep 1971959 = 2957939) B2957939
theorem B1971983 : Blo 1313975 1971983 := bstep (se 1 (by rfl) ⟨1478987, by rfl⟩ : syracuseStep 1971983 = 2957975) B2957975
theorem B2496271 : Blo 1313975 2496271 := bstep (se 1 (by rfl) ⟨1872203, by rfl⟩ : syracuseStep 2496271 = 3744407) B3744407
theorem B1972025 : Blo 1313975 1972025 := bstep (se 2 (by rfl) ⟨739509, by rfl⟩ : syracuseStep 1972025 = 1479019) B1479019
theorem B3553085 : Blo 1313975 3553085 := bstep (se 3 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 3553085 = 1332407) B1332407
theorem B2217847 : Blo 1313975 2217847 := bstep (se 1 (by rfl) ⟨1663385, by rfl⟩ : syracuseStep 2217847 = 3326771) B3326771
theorem B1972103 : Blo 1313975 1972103 := bstep (se 1 (by rfl) ⟨1479077, by rfl⟩ : syracuseStep 1972103 = 2958155) B2958155
theorem B9983897 : Blo 1313975 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B12638105 : Blo 1313975 12638105 := bstep (se 2 (by rfl) ⟨4739289, by rfl⟩ : syracuseStep 12638105 = 9478579) B9478579
theorem B22787993 : Blo 1313975 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B1972139 : Blo 1313975 1972139 := bstep (se 1 (by rfl) ⟨1479104, by rfl⟩ : syracuseStep 1972139 = 2958209) B2958209
theorem B1972169 : Blo 1313975 1972169 := bstep (se 2 (by rfl) ⟨739563, by rfl⟩ : syracuseStep 1972169 = 1479127) B1479127
theorem B7108631 : Blo 1313975 7108631 := bstep (se 1 (by rfl) ⟨5331473, by rfl⟩ : syracuseStep 7108631 = 10662947) B10662947
theorem B15177773 : Blo 1313975 15177773 := bstep (se 3 (by rfl) ⟨2845832, by rfl⟩ : syracuseStep 15177773 = 5691665) B5691665
theorem B2218043 : Blo 1313975 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B1972283 : Blo 1313975 1972283 := bstep (se 1 (by rfl) ⟨1479212, by rfl⟩ : syracuseStep 1972283 = 2958425) B2958425
theorem B1333307 : Blo 1313975 1333307 := bstep (se 1 (by rfl) ⟨999980, by rfl⟩ : syracuseStep 1333307 = 1999961) B1999961
theorem B4388951 : Blo 1313975 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B1972343 : Blo 1313975 1972343 := bstep (se 1 (by rfl) ⟨1479257, by rfl⟩ : syracuseStep 1972343 = 2958515) B2958515
theorem B1972367 : Blo 1313975 1972367 := bstep (se 1 (by rfl) ⟨1479275, by rfl⟩ : syracuseStep 1972367 = 2958551) B2958551
theorem B1972409 : Blo 1313975 1972409 := bstep (se 2 (by rfl) ⟨739653, by rfl⟩ : syracuseStep 1972409 = 1479307) B1479307
theorem B12646601 : Blo 1313975 12646601 := bstep (se 2 (by rfl) ⟨4742475, by rfl⟩ : syracuseStep 12646601 = 9484951) B9484951
theorem B12646637 : Blo 1313975 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B14219509 : Blo 1313975 14219509 := bstep (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) B1333079
theorem B1972487 : Blo 1313975 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B1972523 : Blo 1313975 1972523 := bstep (se 1 (by rfl) ⟨1479392, by rfl⟩ : syracuseStep 1972523 = 2958785) B2958785
theorem B1972553 : Blo 1313975 1972553 := bstep (se 2 (by rfl) ⟨739707, by rfl⟩ : syracuseStep 1972553 = 1479415) B1479415
theorem B1333639 : Blo 1313975 1333639 := bstep (se 1 (by rfl) ⟨1000229, by rfl⟩ : syracuseStep 1333639 = 2000459) B2000459
theorem B2808211 : Blo 1313975 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B1972667 : Blo 1313975 1972667 := bstep (se 1 (by rfl) ⟨1479500, by rfl⟩ : syracuseStep 1972667 = 2959001) B2959001
theorem B2218441 : Blo 1313975 2218441 := bstep (se 2 (by rfl) ⟨831915, by rfl⟩ : syracuseStep 2218441 = 1663831) B1663831
theorem B1972727 : Blo 1313975 1972727 := bstep (se 1 (by rfl) ⟨1479545, by rfl⟩ : syracuseStep 1972727 = 2959091) B2959091
theorem B1972751 : Blo 1313975 1972751 := bstep (se 1 (by rfl) ⟨1479563, by rfl⟩ : syracuseStep 1972751 = 2959127) B2959127
theorem B1972793 : Blo 1313975 1972793 := bstep (se 2 (by rfl) ⟨739797, by rfl⟩ : syracuseStep 1972793 = 1479595) B1479595
theorem B9476675 : Blo 1313975 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B1972871 : Blo 1313975 1972871 := bstep (se 1 (by rfl) ⟨1479653, by rfl⟩ : syracuseStep 1972871 = 2959307) B2959307
theorem B2497159 : Blo 1313975 2497159 := bstep (se 1 (by rfl) ⟨1872869, by rfl⟩ : syracuseStep 2497159 = 3745739) B3745739
theorem B1972907 : Blo 1313975 1972907 := bstep (se 1 (by rfl) ⟨1479680, by rfl⟩ : syracuseStep 1972907 = 2959361) B2959361
theorem B6314689 : Blo 1313975 6314689 := bstep (se 2 (by rfl) ⟨2368008, by rfl⟩ : syracuseStep 6314689 = 4736017) B4736017
theorem B1972937 : Blo 1313975 1972937 := bstep (se 2 (by rfl) ⟨739851, by rfl⟩ : syracuseStep 1972937 = 1479703) B1479703
theorem B4438799 : Blo 1313975 4438799 := bstep (se 1 (by rfl) ⟨3329099, by rfl⟩ : syracuseStep 4438799 = 6658199) B6658199
theorem B30358309 : Blo 1313975 30358309 := bstep (se 4 (by rfl) ⟨2846091, by rfl⟩ : syracuseStep 30358309 = 5692183) B5692183
theorem B1973051 : Blo 1313975 1973051 := bstep (se 1 (by rfl) ⟨1479788, by rfl⟩ : syracuseStep 1973051 = 2959577) B2959577
theorem B1973111 : Blo 1313975 1973111 := bstep (se 1 (by rfl) ⟨1479833, by rfl⟩ : syracuseStep 1973111 = 2959667) B2959667
theorem B1973135 : Blo 1313975 1973135 := bstep (se 1 (by rfl) ⟨1479851, by rfl⟩ : syracuseStep 1973135 = 2959703) B2959703
theorem B5331865 : Blo 1313975 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B1973177 : Blo 1313975 1973177 := bstep (se 2 (by rfl) ⟨739941, by rfl⟩ : syracuseStep 1973177 = 1479883) B1479883
theorem B1973255 : Blo 1313975 1973255 := bstep (se 1 (by rfl) ⟨1479941, by rfl⟩ : syracuseStep 1973255 = 2959883) B2959883
theorem B4439069 : Blo 1313975 4439069 := bstep (se 3 (by rfl) ⟨832325, by rfl⟩ : syracuseStep 4439069 = 1664651) B1664651
theorem B1973291 : Blo 1313975 1973291 := bstep (se 1 (by rfl) ⟨1479968, by rfl⟩ : syracuseStep 1973291 = 2959937) B2959937
theorem B1973321 : Blo 1313975 1973321 := bstep (se 2 (by rfl) ⟨739995, by rfl⟩ : syracuseStep 1973321 = 1479991) B1479991
theorem B4267127 : Blo 1313975 4267127 := bstep (se 1 (by rfl) ⟨3200345, by rfl⟩ : syracuseStep 4267127 = 6400691) B6400691
theorem B2219143 : Blo 1313975 2219143 := bstep (se 1 (by rfl) ⟨1664357, by rfl⟩ : syracuseStep 2219143 = 3328715) B3328715
theorem B1973435 : Blo 1313975 1973435 := bstep (se 1 (by rfl) ⟨1480076, by rfl⟩ : syracuseStep 1973435 = 2960153) B2960153
theorem B1973495 : Blo 1313975 1973495 := bstep (se 1 (by rfl) ⟨1480121, by rfl⟩ : syracuseStep 1973495 = 2960243) B2960243
theorem B1973519 : Blo 1313975 1973519 := bstep (se 1 (by rfl) ⟨1480139, by rfl⟩ : syracuseStep 1973519 = 2960279) B2960279
theorem B3743005 : Blo 1313975 3743005 := bstep (se 3 (by rfl) ⟨701813, by rfl⟩ : syracuseStep 3743005 = 1403627) B1403627
theorem B1973561 : Blo 1313975 1973561 := bstep (se 2 (by rfl) ⟨740085, by rfl⟩ : syracuseStep 1973561 = 1480171) B1480171
theorem B2956679 : Blo 1313975 2956679 := bstep (se 1 (by rfl) ⟨2217509, by rfl⟩ : syracuseStep 2956679 = 4435019) B4435019
theorem B3554695 : Blo 1313975 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B1973639 : Blo 1313975 1973639 := bstep (se 1 (by rfl) ⟨1480229, by rfl⟩ : syracuseStep 1973639 = 2960459) B2960459
theorem B6323609 : Blo 1313975 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B4996505 : Blo 1313975 4996505 := bstep (se 2 (by rfl) ⟨1873689, by rfl⟩ : syracuseStep 4996505 = 3747379) B3747379
theorem B1973675 : Blo 1313975 1973675 := bstep (se 1 (by rfl) ⟨1480256, by rfl⟩ : syracuseStep 1973675 = 2960513) B2960513
theorem B1973705 : Blo 1313975 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B6323665 : Blo 1313975 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B40492547 : Blo 1313975 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B2956859 : Blo 1313975 2956859 := bstep (se 1 (by rfl) ⟨2217644, by rfl⟩ : syracuseStep 2956859 = 4435289) B4435289
theorem B1973819 : Blo 1313975 1973819 := bstep (se 1 (by rfl) ⟨1480364, by rfl⟩ : syracuseStep 1973819 = 2960729) B2960729
theorem B6323779 : Blo 1313975 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B3743347 : Blo 1313975 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1973879 : Blo 1313975 1973879 := bstep (se 1 (by rfl) ⟨1480409, by rfl⟩ : syracuseStep 1973879 = 2960819) B2960819
theorem B2104967 : Blo 1313975 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B1973903 : Blo 1313975 1973903 := bstep (se 1 (by rfl) ⟨1480427, by rfl⟩ : syracuseStep 1973903 = 2960855) B2960855
theorem B2956985 : Blo 1313975 2956985 := bstep (se 2 (by rfl) ⟨1108869, by rfl⟩ : syracuseStep 2956985 = 2217739) B2217739
theorem B2563769 : Blo 1313975 2563769 := bstep (se 2 (by rfl) ⟨961413, by rfl⟩ : syracuseStep 2563769 = 1922827) B1922827
theorem B1973945 : Blo 1313975 1973945 := bstep (se 2 (by rfl) ⟨740229, by rfl⟩ : syracuseStep 1973945 = 1480459) B1480459
theorem B16858853 : Blo 1313975 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B3374849 : Blo 1313975 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B2219791 : Blo 1313975 2219791 := bstep (se 1 (by rfl) ⟨1664843, by rfl⟩ : syracuseStep 2219791 = 3329687) B3329687
theorem B9985841 : Blo 1313975 9985841 := bstep (se 2 (by rfl) ⟨3744690, by rfl⟩ : syracuseStep 9985841 = 7489381) B7489381
theorem B1998793 : Blo 1313975 1998793 := bstep (se 2 (by rfl) ⟨749547, by rfl⟩ : syracuseStep 1998793 = 1499095) B1499095
theorem B10665931 : Blo 1313975 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B2220041 : Blo 1313975 2220041 := bstep (se 2 (by rfl) ⟨832515, by rfl⟩ : syracuseStep 2220041 = 1665031) B1665031
theorem B21331997 : Blo 1313975 21331997 := bstep (se 3 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 21331997 = 7999499) B7999499
theorem B3080249 : Blo 1313975 3080249 := bstep (se 2 (by rfl) ⟨1155093, by rfl⟩ : syracuseStep 3080249 = 2310187) B2310187
theorem B3555485 : Blo 1313975 3555485 := bstep (se 3 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 3555485 = 1333307) B1333307
theorem B3326123 : Blo 1313975 3326123 := bstep (se 1 (by rfl) ⟨2494592, by rfl⟩ : syracuseStep 3326123 = 4989185) B4989185
theorem B2220203 : Blo 1313975 2220203 := bstep (se 1 (by rfl) ⟨1665152, by rfl⟩ : syracuseStep 2220203 = 3330305) B3330305
theorem B4440311 : Blo 1313975 4440311 := bstep (se 1 (by rfl) ⟨3330233, by rfl⟩ : syracuseStep 4440311 = 6660467) B6660467
theorem B11379005 : Blo 1313975 11379005 := bstep (se 3 (by rfl) ⟨2133563, by rfl⟩ : syracuseStep 11379005 = 4267127) B4267127
theorem B1778185 : Blo 1313975 1778185 := bstep (se 2 (by rfl) ⟨666819, by rfl⟩ : syracuseStep 1778185 = 1333639) B1333639
theorem B3744281 : Blo 1313975 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B2220601 : Blo 1313975 2220601 := bstep (se 2 (by rfl) ⟨832725, by rfl⟩ : syracuseStep 2220601 = 1665451) B1665451
theorem B4440635 : Blo 1313975 4440635 := bstep (se 1 (by rfl) ⟨3330476, by rfl⟩ : syracuseStep 4440635 = 6660953) B6660953
theorem B2957921 : Blo 1313975 2957921 := bstep (se 2 (by rfl) ⟨1109220, by rfl⟩ : syracuseStep 2957921 = 2218441) B2218441
theorem B4440905 : Blo 1313975 4440905 := bstep (se 2 (by rfl) ⟨1665339, by rfl⟩ : syracuseStep 4440905 = 3330679) B3330679
theorem B3326903 : Blo 1313975 3326903 := bstep (se 1 (by rfl) ⟨2495177, by rfl⟩ : syracuseStep 3326903 = 4990355) B4990355
theorem B4211639 : Blo 1313975 4211639 := bstep (se 1 (by rfl) ⟨3158729, by rfl⟩ : syracuseStep 4211639 = 6317459) B6317459
theorem B2958263 : Blo 1313975 2958263 := bstep (se 1 (by rfl) ⟨2218697, by rfl⟩ : syracuseStep 2958263 = 4437395) B4437395
theorem B4989883 : Blo 1313975 4989883 := bstep (se 1 (by rfl) ⟨3742412, by rfl⟩ : syracuseStep 4989883 = 7484825) B7484825
theorem B14967827 : Blo 1313975 14967827 := bstep (se 1 (by rfl) ⟨11225870, by rfl⟩ : syracuseStep 14967827 = 22451741) B22451741
theorem B40477745 : Blo 1313975 40477745 := bstep (se 2 (by rfl) ⟨15179154, by rfl⟩ : syracuseStep 40477745 = 30358309) B30358309
theorem B2106491 : Blo 1313975 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B2368723 : Blo 1313975 2368723 := bstep (se 1 (by rfl) ⟨1776542, by rfl⟩ : syracuseStep 2368723 = 3553085) B3553085
theorem B10118515 : Blo 1313975 10118515 := bstep (se 1 (by rfl) ⟨7588886, by rfl⟩ : syracuseStep 10118515 = 15177773) B15177773
theorem B2925967 : Blo 1313975 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B8431067 : Blo 1313975 8431067 := bstep (se 1 (by rfl) ⟨6323300, by rfl⟩ : syracuseStep 8431067 = 12646601) B12646601
theorem B8431091 : Blo 1313975 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B2958857 : Blo 1313975 2958857 := bstep (se 2 (by rfl) ⟨1109571, by rfl⟩ : syracuseStep 2958857 = 2219143) B2219143
theorem B5613245 : Blo 1313975 5613245 := bstep (se 3 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 5613245 = 2104967) B2104967
theorem B4990673 : Blo 1313975 4990673 := bstep (se 2 (by rfl) ⟨1871502, by rfl⟩ : syracuseStep 4990673 = 3743005) B3743005
theorem B6317783 : Blo 1313975 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B6162169 : Blo 1313975 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B2959199 : Blo 1313975 2959199 := bstep (se 1 (by rfl) ⟨2219399, by rfl⟩ : syracuseStep 2959199 = 4438799) B4438799
theorem B3327905 : Blo 1313975 3327905 := bstep (se 2 (by rfl) ⟨1247964, by rfl⟩ : syracuseStep 3327905 = 2495929) B2495929
theorem B8431553 : Blo 1313975 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B2959379 : Blo 1313975 2959379 := bstep (se 1 (by rfl) ⟨2219534, by rfl⟩ : syracuseStep 2959379 = 4439069) B4439069
theorem B18958373 : Blo 1313975 18958373 := bstep (se 4 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 18958373 = 3554695) B3554695
theorem B8431705 : Blo 1313975 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B4991129 : Blo 1313975 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B13502771 : Blo 1313975 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B26995031 : Blo 1313975 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B3328361 : Blo 1313975 3328361 := bstep (se 2 (by rfl) ⟨1248135, by rfl⟩ : syracuseStep 3328361 = 2496271) B2496271
theorem B2959721 : Blo 1313975 2959721 := bstep (se 2 (by rfl) ⟨1109895, by rfl⟩ : syracuseStep 2959721 = 2219791) B2219791
theorem B17074583 : Blo 1313975 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B6654473 : Blo 1313975 6654473 := bstep (se 2 (by rfl) ⟨2495427, by rfl⟩ : syracuseStep 6654473 = 4990855) B4990855
theorem B2665057 : Blo 1313975 2665057 := bstep (se 2 (by rfl) ⟨999396, by rfl⟩ : syracuseStep 2665057 = 1998793) B1998793
theorem B11225735 : Blo 1313975 11225735 := bstep (se 1 (by rfl) ⟨8419301, by rfl⟩ : syracuseStep 11225735 = 16838603) B16838603
theorem B17992631 : Blo 1313975 17992631 := bstep (se 1 (by rfl) ⟨13494473, by rfl⟩ : syracuseStep 17992631 = 26988947) B26988947
theorem B2960315 : Blo 1313975 2960315 := bstep (se 1 (by rfl) ⟨2220236, by rfl⟩ : syracuseStep 2960315 = 4440473) B4440473
theorem B18959345 : Blo 1313975 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B2960441 : Blo 1313975 2960441 := bstep (se 2 (by rfl) ⟨1110165, by rfl⟩ : syracuseStep 2960441 = 2220331) B2220331
theorem B2370683 : Blo 1313975 2370683 := bstep (se 1 (by rfl) ⟨1778012, by rfl⟩ : syracuseStep 2370683 = 3556025) B3556025
theorem B3157163 : Blo 1313975 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B1313991 : Blo 1313975 1313991 := bstep (se 1 (by rfl) ⟨985493, by rfl⟩ : syracuseStep 1313991 = 1970987) B1970987
theorem B1871047 : Blo 1313975 1871047 := bstep (se 1 (by rfl) ⟨1403285, by rfl⟩ : syracuseStep 1871047 = 2806571) B2806571
theorem B1314011 : Blo 1313975 1314011 := bstep (se 1 (by rfl) ⟨985508, by rfl⟩ : syracuseStep 1314011 = 1971017) B1971017
theorem B7490839 : Blo 1313975 7490839 := bstep (se 1 (by rfl) ⟨5618129, by rfl⟩ : syracuseStep 7490839 = 11236259) B11236259
theorem B1314087 : Blo 1313975 1314087 := bstep (se 1 (by rfl) ⟨985565, by rfl⟩ : syracuseStep 1314087 = 1971131) B1971131
theorem B1314127 : Blo 1313975 1314127 := bstep (se 1 (by rfl) ⟨985595, by rfl⟩ : syracuseStep 1314127 = 1971191) B1971191
theorem B1314143 : Blo 1313975 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B1314171 : Blo 1313975 1314171 := bstep (se 1 (by rfl) ⟨985628, by rfl⟩ : syracuseStep 1314171 = 1971257) B1971257
theorem B3747197 : Blo 1313975 3747197 := bstep (se 3 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 3747197 = 1405199) B1405199
theorem B4435343 : Blo 1313975 4435343 := bstep (se 1 (by rfl) ⟨3326507, by rfl⟩ : syracuseStep 4435343 = 6653015) B6653015
theorem B2960783 : Blo 1313975 2960783 := bstep (se 1 (by rfl) ⟨2220587, by rfl⟩ : syracuseStep 2960783 = 4441175) B4441175
theorem B1314223 : Blo 1313975 1314223 := bstep (se 1 (by rfl) ⟨985667, by rfl⟩ : syracuseStep 1314223 = 1971335) B1971335
theorem B1314247 : Blo 1313975 1314247 := bstep (se 1 (by rfl) ⟨985685, by rfl⟩ : syracuseStep 1314247 = 1971371) B1971371
theorem B1314267 : Blo 1313975 1314267 := bstep (se 1 (by rfl) ⟨985700, by rfl⟩ : syracuseStep 1314267 = 1971401) B1971401
theorem B1404379 : Blo 1313975 1404379 := bstep (se 1 (by rfl) ⟨1053284, by rfl⟩ : syracuseStep 1404379 = 2106569) B2106569
theorem B3329545 : Blo 1313975 3329545 := bstep (se 2 (by rfl) ⟨1248579, by rfl⟩ : syracuseStep 3329545 = 2497159) B2497159
theorem B1314343 : Blo 1313975 1314343 := bstep (se 1 (by rfl) ⟨985757, by rfl⟩ : syracuseStep 1314343 = 1971515) B1971515
theorem B1314383 : Blo 1313975 1314383 := bstep (se 1 (by rfl) ⟨985787, by rfl⟩ : syracuseStep 1314383 = 1971575) B1971575
theorem B1314399 : Blo 1313975 1314399 := bstep (se 1 (by rfl) ⟨985799, by rfl⟩ : syracuseStep 1314399 = 1971599) B1971599
theorem B9989729 : Blo 1313975 9989729 := bstep (se 2 (by rfl) ⟨3746148, by rfl⟩ : syracuseStep 9989729 = 7492297) B7492297
theorem B1314427 : Blo 1313975 1314427 := bstep (se 1 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 1314427 = 1971641) B1971641
theorem B1314479 : Blo 1313975 1314479 := bstep (se 1 (by rfl) ⟨985859, by rfl⟩ : syracuseStep 1314479 = 1971719) B1971719
theorem B6000317 : Blo 1313975 6000317 := bstep (se 3 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 6000317 = 2250119) B2250119
theorem B1314503 : Blo 1313975 1314503 := bstep (se 1 (by rfl) ⟨985877, by rfl⟩ : syracuseStep 1314503 = 1971755) B1971755
theorem B4435667 : Blo 1313975 4435667 := bstep (se 1 (by rfl) ⟨3326750, by rfl⟩ : syracuseStep 4435667 = 6653501) B6653501
theorem B1314523 : Blo 1313975 1314523 := bstep (se 1 (by rfl) ⟨985892, by rfl⟩ : syracuseStep 1314523 = 1971785) B1971785
theorem B15380257 : Blo 1313975 15380257 := bstep (se 2 (by rfl) ⟨5767596, by rfl⟩ : syracuseStep 15380257 = 11535193) B11535193
theorem B1314599 : Blo 1313975 1314599 := bstep (se 1 (by rfl) ⟨985949, by rfl⟩ : syracuseStep 1314599 = 1971899) B1971899
theorem B5328683 : Blo 1313975 5328683 := bstep (se 1 (by rfl) ⟨3996512, by rfl⟩ : syracuseStep 5328683 = 7993025) B7993025
theorem B1314639 : Blo 1313975 1314639 := bstep (se 1 (by rfl) ⟨985979, by rfl⟩ : syracuseStep 1314639 = 1971959) B1971959
theorem B1314655 : Blo 1313975 1314655 := bstep (se 1 (by rfl) ⟨985991, by rfl⟩ : syracuseStep 1314655 = 1971983) B1971983
theorem B14970743 : Blo 1313975 14970743 := bstep (se 1 (by rfl) ⟨11228057, by rfl⟩ : syracuseStep 14970743 = 22456115) B22456115
theorem B1314683 : Blo 1313975 1314683 := bstep (se 1 (by rfl) ⟨986012, by rfl⟩ : syracuseStep 1314683 = 1972025) B1972025
theorem B1314735 : Blo 1313975 1314735 := bstep (se 1 (by rfl) ⟨986051, by rfl⟩ : syracuseStep 1314735 = 1972103) B1972103
theorem B6655931 : Blo 1313975 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B8425403 : Blo 1313975 8425403 := bstep (se 1 (by rfl) ⟨6319052, by rfl⟩ : syracuseStep 8425403 = 12638105) B12638105
theorem B1314759 : Blo 1313975 1314759 := bstep (se 1 (by rfl) ⟨986069, by rfl⟩ : syracuseStep 1314759 = 1972139) B1972139
theorem B1314779 : Blo 1313975 1314779 := bstep (se 1 (by rfl) ⟨986084, by rfl⟩ : syracuseStep 1314779 = 1972169) B1972169
theorem B4739087 : Blo 1313975 4739087 := bstep (se 1 (by rfl) ⟨3554315, by rfl⟩ : syracuseStep 4739087 = 7108631) B7108631
theorem B1478695 : Blo 1313975 1478695 := bstep (se 1 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 1478695 = 2218043) B2218043
theorem B1314855 : Blo 1313975 1314855 := bstep (se 1 (by rfl) ⟨986141, by rfl⟩ : syracuseStep 1314855 = 1972283) B1972283
theorem B1314895 : Blo 1313975 1314895 := bstep (se 1 (by rfl) ⟨986171, by rfl⟩ : syracuseStep 1314895 = 1972343) B1972343
theorem B4993103 : Blo 1313975 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B1314911 : Blo 1313975 1314911 := bstep (se 1 (by rfl) ⟨986183, by rfl⟩ : syracuseStep 1314911 = 1972367) B1972367
theorem B6320243 : Blo 1313975 6320243 := bstep (se 1 (by rfl) ⟨4740182, by rfl⟩ : syracuseStep 6320243 = 9480365) B9480365
theorem B1314939 : Blo 1313975 1314939 := bstep (se 1 (by rfl) ⟨986204, by rfl⟩ : syracuseStep 1314939 = 1972409) B1972409
theorem B7483549 : Blo 1313975 7483549 := bstep (se 3 (by rfl) ⟨1403165, by rfl⟩ : syracuseStep 7483549 = 2806331) B2806331
theorem B1314991 : Blo 1313975 1314991 := bstep (se 1 (by rfl) ⟨986243, by rfl⟩ : syracuseStep 1314991 = 1972487) B1972487
theorem B1315015 : Blo 1313975 1315015 := bstep (se 1 (by rfl) ⟨986261, by rfl⟩ : syracuseStep 1315015 = 1972523) B1972523
theorem B1315035 : Blo 1313975 1315035 := bstep (se 1 (by rfl) ⟨986276, by rfl⟩ : syracuseStep 1315035 = 1972553) B1972553
theorem B4993271 : Blo 1313975 4993271 := bstep (se 1 (by rfl) ⟨3744953, by rfl⟩ : syracuseStep 4993271 = 7489907) B7489907
theorem B1315111 : Blo 1313975 1315111 := bstep (se 1 (by rfl) ⟨986333, by rfl⟩ : syracuseStep 1315111 = 1972667) B1972667
theorem B1315151 : Blo 1313975 1315151 := bstep (se 1 (by rfl) ⟨986363, by rfl⟩ : syracuseStep 1315151 = 1972727) B1972727
theorem B1315167 : Blo 1313975 1315167 := bstep (se 1 (by rfl) ⟨986375, by rfl⟩ : syracuseStep 1315167 = 1972751) B1972751
theorem B1315195 : Blo 1313975 1315195 := bstep (se 1 (by rfl) ⟨986396, by rfl⟩ : syracuseStep 1315195 = 1972793) B1972793
theorem B1315247 : Blo 1313975 1315247 := bstep (se 1 (by rfl) ⟨986435, by rfl⟩ : syracuseStep 1315247 = 1972871) B1972871
theorem B1315271 : Blo 1313975 1315271 := bstep (se 1 (by rfl) ⟨986453, by rfl⟩ : syracuseStep 1315271 = 1972907) B1972907
theorem B1315291 : Blo 1313975 1315291 := bstep (se 1 (by rfl) ⟨986468, by rfl⟩ : syracuseStep 1315291 = 1972937) B1972937
theorem B6836717 : Blo 1313975 6836717 := bstep (se 3 (by rfl) ⟨1281884, by rfl⟩ : syracuseStep 6836717 = 2563769) B2563769
theorem B1315367 : Blo 1313975 1315367 := bstep (se 1 (by rfl) ⟨986525, by rfl⟩ : syracuseStep 1315367 = 1973051) B1973051
theorem B2495033 : Blo 1313975 2495033 := bstep (se 2 (by rfl) ⟨935637, by rfl⟩ : syracuseStep 2495033 = 1871275) B1871275
theorem B1315407 : Blo 1313975 1315407 := bstep (se 1 (by rfl) ⟨986555, by rfl⟩ : syracuseStep 1315407 = 1973111) B1973111
theorem B1315423 : Blo 1313975 1315423 := bstep (se 1 (by rfl) ⟨986567, by rfl⟩ : syracuseStep 1315423 = 1973135) B1973135
theorem B1315451 : Blo 1313975 1315451 := bstep (se 1 (by rfl) ⟨986588, by rfl⟩ : syracuseStep 1315451 = 1973177) B1973177
theorem B1315503 : Blo 1313975 1315503 := bstep (se 1 (by rfl) ⟨986627, by rfl⟩ : syracuseStep 1315503 = 1973255) B1973255
theorem B1315527 : Blo 1313975 1315527 := bstep (se 1 (by rfl) ⟨986645, by rfl⟩ : syracuseStep 1315527 = 1973291) B1973291
theorem B5616337 : Blo 1313975 5616337 := bstep (se 2 (by rfl) ⟨2106126, by rfl⟩ : syracuseStep 5616337 = 4212253) B4212253
theorem B40506065 : Blo 1313975 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B1315547 : Blo 1313975 1315547 := bstep (se 1 (by rfl) ⟨986660, by rfl⟩ : syracuseStep 1315547 = 1973321) B1973321
theorem B3158777 : Blo 1313975 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B1315623 : Blo 1313975 1315623 := bstep (se 1 (by rfl) ⟨986717, by rfl⟩ : syracuseStep 1315623 = 1973435) B1973435
theorem B1315663 : Blo 1313975 1315663 := bstep (se 1 (by rfl) ⟨986747, by rfl⟩ : syracuseStep 1315663 = 1973495) B1973495
theorem B1315679 : Blo 1313975 1315679 := bstep (se 1 (by rfl) ⟨986759, by rfl⟩ : syracuseStep 1315679 = 1973519) B1973519
theorem B4436855 : Blo 1313975 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B1315707 : Blo 1313975 1315707 := bstep (se 1 (by rfl) ⟨986780, by rfl⟩ : syracuseStep 1315707 = 1973561) B1973561
theorem B1971119 : Blo 1313975 1971119 := bstep (se 1 (by rfl) ⟨1478339, by rfl⟩ : syracuseStep 1971119 = 2956679) B2956679
theorem B1315759 : Blo 1313975 1315759 := bstep (se 1 (by rfl) ⟨986819, by rfl⟩ : syracuseStep 1315759 = 1973639) B1973639
theorem B4215739 : Blo 1313975 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B3331003 : Blo 1313975 3331003 := bstep (se 1 (by rfl) ⟨2498252, by rfl⟩ : syracuseStep 3331003 = 4996505) B4996505
theorem B1315783 : Blo 1313975 1315783 := bstep (se 1 (by rfl) ⟨986837, by rfl⟩ : syracuseStep 1315783 = 1973675) B1973675
theorem B1315803 : Blo 1313975 1315803 := bstep (se 1 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 1315803 = 1973705) B1973705
theorem B1971209 : Blo 1313975 1971209 := bstep (se 2 (by rfl) ⟨739203, by rfl⟩ : syracuseStep 1971209 = 1478407) B1478407
theorem B9991187 : Blo 1313975 9991187 := bstep (se 1 (by rfl) ⟨7493390, by rfl⟩ : syracuseStep 9991187 = 14986781) B14986781
theorem B1971239 : Blo 1313975 1971239 := bstep (se 1 (by rfl) ⟨1478429, by rfl⟩ : syracuseStep 1971239 = 2956859) B2956859
theorem B1315879 : Blo 1313975 1315879 := bstep (se 1 (by rfl) ⟨986909, by rfl⟩ : syracuseStep 1315879 = 1973819) B1973819
theorem B4437071 : Blo 1313975 4437071 := bstep (se 1 (by rfl) ⟨3327803, by rfl⟩ : syracuseStep 4437071 = 6655607) B6655607
theorem B1315919 : Blo 1313975 1315919 := bstep (se 1 (by rfl) ⟨986939, by rfl⟩ : syracuseStep 1315919 = 1973879) B1973879
theorem B1315935 : Blo 1313975 1315935 := bstep (se 1 (by rfl) ⟨986951, by rfl⟩ : syracuseStep 1315935 = 1973903) B1973903
theorem B1971323 : Blo 1313975 1971323 := bstep (se 1 (by rfl) ⟨1478492, by rfl⟩ : syracuseStep 1971323 = 2956985) B2956985
theorem B1315963 : Blo 1313975 1315963 := bstep (se 1 (by rfl) ⟨986972, by rfl⟩ : syracuseStep 1315963 = 1973945) B1973945
theorem B2249899 : Blo 1313975 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B4994243 : Blo 1313975 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B6657227 : Blo 1313975 6657227 := bstep (se 1 (by rfl) ⟨4992920, by rfl⟩ : syracuseStep 6657227 = 9985841) B9985841
theorem B1971449 : Blo 1313975 1971449 := bstep (se 2 (by rfl) ⟨739293, by rfl⟩ : syracuseStep 1971449 = 1478587) B1478587
theorem B1971551 : Blo 1313975 1971551 := bstep (se 1 (by rfl) ⟨1478663, by rfl⟩ : syracuseStep 1971551 = 2957327) B2957327
theorem B1971563 : Blo 1313975 1971563 := bstep (se 1 (by rfl) ⟨1478672, by rfl⟩ : syracuseStep 1971563 = 2957345) B2957345
theorem B17986931 : Blo 1313975 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B4437449 : Blo 1313975 4437449 := bstep (se 2 (by rfl) ⟨1664043, by rfl⟩ : syracuseStep 4437449 = 3328087) B3328087
theorem B18961883 : Blo 1313975 18961883 := bstep (se 1 (by rfl) ⟨14221412, by rfl⟩ : syracuseStep 18961883 = 28442825) B28442825
theorem B1971791 : Blo 1313975 1971791 := bstep (se 1 (by rfl) ⟨1478843, by rfl⟩ : syracuseStep 1971791 = 2957687) B2957687
theorem B1480315 : Blo 1313975 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B1971911 : Blo 1313975 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B4437719 : Blo 1313975 4437719 := bstep (se 1 (by rfl) ⟨3328289, by rfl⟩ : syracuseStep 4437719 = 6656579) B6656579
theorem B2217719 : Blo 1313975 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B1972073 : Blo 1313975 1972073 := bstep (se 2 (by rfl) ⟨739527, by rfl⟩ : syracuseStep 1972073 = 1479055) B1479055
theorem B4437935 : Blo 1313975 4437935 := bstep (se 1 (by rfl) ⟨3328451, by rfl⟩ : syracuseStep 4437935 = 6656903) B6656903
theorem B1972151 : Blo 1313975 1972151 := bstep (se 1 (by rfl) ⟨1479113, by rfl⟩ : syracuseStep 1972151 = 2958227) B2958227
theorem B1972187 : Blo 1313975 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B2496521 : Blo 1313975 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B2218063 : Blo 1313975 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B4995229 : Blo 1313975 4995229 := bstep (se 3 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 4995229 = 1873211) B1873211
theorem B8419585 : Blo 1313975 8419585 := bstep (se 2 (by rfl) ⟨3157344, by rfl⟩ : syracuseStep 8419585 = 6314689) B6314689
theorem B2218313 : Blo 1313975 2218313 := bstep (se 2 (by rfl) ⟨831867, by rfl⟩ : syracuseStep 2218313 = 1663735) B1663735
theorem B16005509 : Blo 1313975 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B1972655 : Blo 1313975 1972655 := bstep (se 1 (by rfl) ⟨1479491, by rfl⟩ : syracuseStep 1972655 = 2958983) B2958983
theorem B1776055 : Blo 1313975 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B5994989 : Blo 1313975 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B1972745 : Blo 1313975 1972745 := bstep (se 2 (by rfl) ⟨739779, by rfl⟩ : syracuseStep 1972745 = 1479559) B1479559
theorem B7109153 : Blo 1313975 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B1972775 : Blo 1313975 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B1972859 : Blo 1313975 1972859 := bstep (se 1 (by rfl) ⟨1479644, by rfl⟩ : syracuseStep 1972859 = 2959289) B2959289
theorem B5331667 : Blo 1313975 5331667 := bstep (se 1 (by rfl) ⟨3998750, by rfl⟩ : syracuseStep 5331667 = 7997501) B7997501
theorem B2218745 : Blo 1313975 2218745 := bstep (se 2 (by rfl) ⟨832029, by rfl⟩ : syracuseStep 2218745 = 1664059) B1664059
theorem B1972985 : Blo 1313975 1972985 := bstep (se 2 (by rfl) ⟨739869, by rfl⟩ : syracuseStep 1972985 = 1479739) B1479739
theorem B73931525 : Blo 1313975 73931525 := bstep (se 4 (by rfl) ⟨6931080, by rfl⟩ : syracuseStep 73931525 = 13862161) B13862161
theorem B11238173 : Blo 1313975 11238173 := bstep (se 3 (by rfl) ⟨2107157, by rfl⟩ : syracuseStep 11238173 = 4214315) B4214315
theorem B1973087 : Blo 1313975 1973087 := bstep (se 1 (by rfl) ⟨1479815, by rfl⟩ : syracuseStep 1973087 = 2959631) B2959631
theorem B1973099 : Blo 1313975 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B2497387 : Blo 1313975 2497387 := bstep (se 1 (by rfl) ⟨1873040, by rfl⟩ : syracuseStep 2497387 = 3746081) B3746081
theorem B3554209 : Blo 1313975 3554209 := bstep (se 2 (by rfl) ⟨1332828, by rfl⟩ : syracuseStep 3554209 = 2665657) B2665657
theorem B2218927 : Blo 1313975 2218927 := bstep (se 1 (by rfl) ⟨1664195, by rfl⟩ : syracuseStep 2218927 = 3328391) B3328391
theorem B2497463 : Blo 1313975 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B7486465 : Blo 1313975 7486465 := bstep (se 2 (by rfl) ⟨2807424, by rfl⟩ : syracuseStep 7486465 = 5614849) B5614849
theorem B2219015 : Blo 1313975 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B3742777 : Blo 1313975 3742777 := bstep (se 2 (by rfl) ⟨1403541, by rfl⟩ : syracuseStep 3742777 = 2807083) B2807083
theorem B1973327 : Blo 1313975 1973327 := bstep (se 1 (by rfl) ⟨1479995, by rfl⟩ : syracuseStep 1973327 = 2959991) B2959991
theorem B1973447 : Blo 1313975 1973447 := bstep (se 1 (by rfl) ⟨1480085, by rfl⟩ : syracuseStep 1973447 = 2960171) B2960171
theorem B2956535 : Blo 1313975 2956535 := bstep (se 1 (by rfl) ⟨2217401, by rfl⟩ : syracuseStep 2956535 = 4434803) B4434803
theorem B11230487 : Blo 1313975 11230487 := bstep (se 1 (by rfl) ⟨8422865, by rfl⟩ : syracuseStep 11230487 = 16845731) B16845731
theorem B2219359 : Blo 1313975 2219359 := bstep (se 1 (by rfl) ⟨1664519, by rfl⟩ : syracuseStep 2219359 = 3329039) B3329039
theorem B1973609 : Blo 1313975 1973609 := bstep (se 2 (by rfl) ⟨740103, by rfl⟩ : syracuseStep 1973609 = 1480207) B1480207
theorem B8543603 : Blo 1313975 8543603 := bstep (se 1 (by rfl) ⟨6407702, by rfl⟩ : syracuseStep 8543603 = 12815405) B12815405
theorem B2219447 : Blo 1313975 2219447 := bstep (se 1 (by rfl) ⟨1664585, by rfl⟩ : syracuseStep 2219447 = 3329171) B3329171
theorem B1973687 : Blo 1313975 1973687 := bstep (se 1 (by rfl) ⟨1480265, by rfl⟩ : syracuseStep 1973687 = 2960531) B2960531
theorem B2497979 : Blo 1313975 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B1973723 : Blo 1313975 1973723 := bstep (se 1 (by rfl) ⟨1480292, by rfl⟩ : syracuseStep 1973723 = 2960585) B2960585
theorem B8429143 : Blo 1313975 8429143 := bstep (se 1 (by rfl) ⟨6321857, by rfl⟩ : syracuseStep 8429143 = 12643715) B12643715
theorem B2809441 : Blo 1313975 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B60767981 : Blo 1313975 60767981 := bstep (se 3 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 60767981 = 22787993) B22787993
theorem B11239235 : Blo 1313975 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B2957129 : Blo 1313975 2957129 := bstep (se 2 (by rfl) ⟨1108923, by rfl⟩ : syracuseStep 2957129 = 2217847) B2217847
theorem B14221241 : Blo 1313975 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B14221331 : Blo 1313975 14221331 := bstep (se 1 (by rfl) ⟨10665998, by rfl⟩ : syracuseStep 14221331 = 21331997) B21331997
theorem B2957417 : Blo 1313975 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B9978065 : Blo 1313975 9978065 := bstep (se 2 (by rfl) ⟨3741774, by rfl⟩ : syracuseStep 9978065 = 7483549) B7483549
theorem B6660305 : Blo 1313975 6660305 := bstep (se 2 (by rfl) ⟨2497614, by rfl⟩ : syracuseStep 6660305 = 4995229) B4995229
theorem B7586003 : Blo 1313975 7586003 := bstep (se 1 (by rfl) ⟨5689502, by rfl⟩ : syracuseStep 7586003 = 11379005) B11379005
theorem B1663355 : Blo 1313975 1663355 := bstep (se 1 (by rfl) ⟨1247516, by rfl⟩ : syracuseStep 1663355 = 2495033) B2495033
theorem B2105851 : Blo 1313975 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B2368073 : Blo 1313975 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B2957903 : Blo 1313975 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B9978551 : Blo 1313975 9978551 := bstep (se 1 (by rfl) ⟨7483913, by rfl⟩ : syracuseStep 9978551 = 14967827) B14967827
theorem B6660791 : Blo 1313975 6660791 := bstep (se 1 (by rfl) ⟨4995593, by rfl⟩ : syracuseStep 6660791 = 9991187) B9991187
theorem B26985163 : Blo 1313975 26985163 := bstep (se 1 (by rfl) ⟨20238872, by rfl⟩ : syracuseStep 26985163 = 40477745) B40477745
theorem B2958047 : Blo 1313975 2958047 := bstep (se 1 (by rfl) ⟨2218535, by rfl⟩ : syracuseStep 2958047 = 4437071) B4437071
theorem B47997845 : Blo 1313975 47997845 := bstep (se 6 (by rfl) ⟨1124949, by rfl⟩ : syracuseStep 47997845 = 2249899) B2249899
theorem B7488449 : Blo 1313975 7488449 := bstep (se 2 (by rfl) ⟨2808168, by rfl⟩ : syracuseStep 7488449 = 5616337) B5616337
theorem B2958299 : Blo 1313975 2958299 := bstep (se 1 (by rfl) ⟨2218724, by rfl⟩ : syracuseStep 2958299 = 4437449) B4437449
theorem B22782941 : Blo 1313975 22782941 := bstep (se 3 (by rfl) ⟨4271801, by rfl⟩ : syracuseStep 22782941 = 8543603) B8543603
theorem B12641255 : Blo 1313975 12641255 := bstep (se 1 (by rfl) ⟨9480941, by rfl⟩ : syracuseStep 12641255 = 18961883) B18961883
theorem B5620711 : Blo 1313975 5620711 := bstep (se 1 (by rfl) ⟨4215533, by rfl⟩ : syracuseStep 5620711 = 8431067) B8431067
theorem B5620727 : Blo 1313975 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B3327115 : Blo 1313975 3327115 := bstep (se 1 (by rfl) ⟨2495336, by rfl⟩ : syracuseStep 3327115 = 4990673) B4990673
theorem B4211855 : Blo 1313975 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B2958479 : Blo 1313975 2958479 := bstep (se 1 (by rfl) ⟨2218859, by rfl⟩ : syracuseStep 2958479 = 4437719) B4437719
theorem B6661277 : Blo 1313975 6661277 := bstep (se 3 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 6661277 = 2497979) B2497979
theorem B2958569 : Blo 1313975 2958569 := bstep (se 2 (by rfl) ⟨1109463, by rfl⟩ : syracuseStep 2958569 = 2218927) B2218927
theorem B6653177 : Blo 1313975 6653177 := bstep (se 2 (by rfl) ⟨2494941, by rfl⟩ : syracuseStep 6653177 = 4989883) B4989883
theorem B5620985 : Blo 1313975 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B4441337 : Blo 1313975 4441337 := bstep (se 2 (by rfl) ⟨1665501, by rfl⟩ : syracuseStep 4441337 = 3331003) B3331003
theorem B2958623 : Blo 1313975 2958623 := bstep (se 1 (by rfl) ⟨2218967, by rfl⟩ : syracuseStep 2958623 = 4437935) B4437935
theorem B5621035 : Blo 1313975 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B4990369 : Blo 1313975 4990369 := bstep (se 2 (by rfl) ⟨1871388, by rfl⟩ : syracuseStep 4990369 = 3742777) B3742777
theorem B3327419 : Blo 1313975 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B9987785 : Blo 1313975 9987785 := bstep (se 2 (by rfl) ⟨3745419, by rfl⟩ : syracuseStep 9987785 = 7490839) B7490839
theorem B2959145 : Blo 1313975 2959145 := bstep (se 2 (by rfl) ⟨1109679, by rfl⟩ : syracuseStep 2959145 = 2219359) B2219359
theorem B3901289 : Blo 1313975 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B11995087 : Blo 1313975 11995087 := bstep (se 1 (by rfl) ⟨8996315, by rfl⟩ : syracuseStep 11995087 = 17992631) B17992631
theorem B1664975 : Blo 1313975 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B3745921 : Blo 1313975 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B20507009 : Blo 1313975 20507009 := bstep (se 2 (by rfl) ⟨7690128, by rfl⟩ : syracuseStep 20507009 = 15380257) B15380257
theorem B4000211 : Blo 1313975 4000211 := bstep (se 1 (by rfl) ⟨3000158, by rfl⟩ : syracuseStep 4000211 = 6000317) B6000317
theorem B40511987 : Blo 1313975 40511987 := bstep (se 1 (by rfl) ⟨30383990, by rfl⟩ : syracuseStep 40511987 = 60767981) B60767981
theorem B9980495 : Blo 1313975 9980495 := bstep (se 1 (by rfl) ⟨7485371, by rfl⟩ : syracuseStep 9980495 = 14970743) B14970743
theorem B9480827 : Blo 1313975 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B3328735 : Blo 1313975 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B4213495 : Blo 1313975 4213495 := bstep (se 1 (by rfl) ⟨3160121, by rfl⟩ : syracuseStep 4213495 = 6320243) B6320243
theorem B2370323 : Blo 1313975 2370323 := bstep (se 1 (by rfl) ⟨1777742, by rfl⟩ : syracuseStep 2370323 = 3555485) B3555485
theorem B11242273 : Blo 1313975 11242273 := bstep (se 2 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 11242273 = 8431705) B8431705
theorem B3328847 : Blo 1313975 3328847 := bstep (se 1 (by rfl) ⟨2496635, by rfl⟩ : syracuseStep 3328847 = 4993271) B4993271
theorem B2960207 : Blo 1313975 2960207 := bstep (se 1 (by rfl) ⟨2220155, by rfl⟩ : syracuseStep 2960207 = 4440311) B4440311
theorem B4557811 : Blo 1313975 4557811 := bstep (se 1 (by rfl) ⟨3418358, by rfl⟩ : syracuseStep 4557811 = 6836717) B6836717
theorem B11226113 : Blo 1313975 11226113 := bstep (se 2 (by rfl) ⟨4209792, by rfl⟩ : syracuseStep 11226113 = 8419585) B8419585
theorem B2960423 : Blo 1313975 2960423 := bstep (se 1 (by rfl) ⟨2220317, by rfl⟩ : syracuseStep 2960423 = 4440635) B4440635
theorem B27004043 : Blo 1313975 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B2960603 : Blo 1313975 2960603 := bstep (se 1 (by rfl) ⟨2220452, by rfl⟩ : syracuseStep 2960603 = 4440905) B4440905
theorem B1314079 : Blo 1313975 1314079 := bstep (se 1 (by rfl) ⟨985559, by rfl⟩ : syracuseStep 1314079 = 1971119) B1971119
theorem B1314139 : Blo 1313975 1314139 := bstep (se 1 (by rfl) ⟨985604, by rfl⟩ : syracuseStep 1314139 = 1971209) B1971209
theorem B2370913 : Blo 1313975 2370913 := bstep (se 2 (by rfl) ⟨889092, by rfl⟩ : syracuseStep 2370913 = 1778185) B1778185
theorem B1314159 : Blo 1313975 1314159 := bstep (se 1 (by rfl) ⟨985619, by rfl⟩ : syracuseStep 1314159 = 1971239) B1971239
theorem B2960801 : Blo 1313975 2960801 := bstep (se 2 (by rfl) ⟨1110300, by rfl⟩ : syracuseStep 2960801 = 2220601) B2220601
theorem B1314215 : Blo 1313975 1314215 := bstep (se 1 (by rfl) ⟨985661, by rfl⟩ : syracuseStep 1314215 = 1971323) B1971323
theorem B3329495 : Blo 1313975 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B1314299 : Blo 1313975 1314299 := bstep (se 1 (by rfl) ⟨985724, by rfl⟩ : syracuseStep 1314299 = 1971449) B1971449
theorem B1314367 : Blo 1313975 1314367 := bstep (se 1 (by rfl) ⟨985775, by rfl⟩ : syracuseStep 1314367 = 1971551) B1971551
theorem B1314375 : Blo 1313975 1314375 := bstep (se 1 (by rfl) ⟨985781, by rfl⟩ : syracuseStep 1314375 = 1971563) B1971563
theorem B1314527 : Blo 1313975 1314527 := bstep (se 1 (by rfl) ⟨985895, by rfl⟩ : syracuseStep 1314527 = 1971791) B1971791
theorem B1314607 : Blo 1313975 1314607 := bstep (se 1 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 1314607 = 1971911) B1971911
theorem B3329849 : Blo 1313975 3329849 := bstep (se 2 (by rfl) ⟨1248693, by rfl⟩ : syracuseStep 3329849 = 2497387) B2497387
theorem B1478479 : Blo 1313975 1478479 := bstep (se 1 (by rfl) ⟨1108859, by rfl⟩ : syracuseStep 1478479 = 2217719) B2217719
theorem B4738945 : Blo 1313975 4738945 := bstep (se 2 (by rfl) ⟨1777104, by rfl⟩ : syracuseStep 4738945 = 3554209) B3554209
theorem B1314715 : Blo 1313975 1314715 := bstep (se 1 (by rfl) ⟨986036, by rfl⟩ : syracuseStep 1314715 = 1972073) B1972073
theorem B1314767 : Blo 1313975 1314767 := bstep (se 1 (by rfl) ⟨986075, by rfl⟩ : syracuseStep 1314767 = 1972151) B1972151
theorem B1314791 : Blo 1313975 1314791 := bstep (se 1 (by rfl) ⟨986093, by rfl⟩ : syracuseStep 1314791 = 1972187) B1972187
theorem B9981953 : Blo 1313975 9981953 := bstep (se 2 (by rfl) ⟨3743232, by rfl⟩ : syracuseStep 9981953 = 7486465) B7486465
theorem B1478875 : Blo 1313975 1478875 := bstep (se 1 (by rfl) ⟨1109156, by rfl⟩ : syracuseStep 1478875 = 2218313) B2218313
theorem B10670339 : Blo 1313975 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B2494729 : Blo 1313975 2494729 := bstep (se 2 (by rfl) ⟨935523, by rfl⟩ : syracuseStep 2494729 = 1871047) B1871047
theorem B11383055 : Blo 1313975 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B3158297 : Blo 1313975 3158297 := bstep (se 2 (by rfl) ⟨1184361, by rfl⟩ : syracuseStep 3158297 = 2368723) B2368723
theorem B1315103 : Blo 1313975 1315103 := bstep (se 1 (by rfl) ⟨986327, by rfl⟩ : syracuseStep 1315103 = 1972655) B1972655
theorem B4436315 : Blo 1313975 4436315 := bstep (se 1 (by rfl) ⟨3327236, by rfl⟩ : syracuseStep 4436315 = 6654473) B6654473
theorem B1315163 : Blo 1313975 1315163 := bstep (se 1 (by rfl) ⟨986372, by rfl⟩ : syracuseStep 1315163 = 1972745) B1972745
theorem B4739435 : Blo 1313975 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B1315183 : Blo 1313975 1315183 := bstep (se 1 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 1315183 = 1972775) B1972775
theorem B1315239 : Blo 1313975 1315239 := bstep (se 1 (by rfl) ⟨986429, by rfl⟩ : syracuseStep 1315239 = 1972859) B1972859
theorem B7483823 : Blo 1313975 7483823 := bstep (se 1 (by rfl) ⟨5612867, by rfl⟩ : syracuseStep 7483823 = 11225735) B11225735
theorem B1479163 : Blo 1313975 1479163 := bstep (se 1 (by rfl) ⟨1109372, by rfl⟩ : syracuseStep 1479163 = 2218745) B2218745
theorem B1315323 : Blo 1313975 1315323 := bstep (se 1 (by rfl) ⟨986492, by rfl⟩ : syracuseStep 1315323 = 1972985) B1972985
theorem B49287683 : Blo 1313975 49287683 := bstep (se 1 (by rfl) ⟨36965762, by rfl⟩ : syracuseStep 49287683 = 73931525) B73931525
theorem B7492115 : Blo 1313975 7492115 := bstep (se 1 (by rfl) ⟨5619086, by rfl⟩ : syracuseStep 7492115 = 11238173) B11238173
theorem B1315391 : Blo 1313975 1315391 := bstep (se 1 (by rfl) ⟨986543, by rfl⟩ : syracuseStep 1315391 = 1973087) B1973087
theorem B1315399 : Blo 1313975 1315399 := bstep (se 1 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 1315399 = 1973099) B1973099
theorem B1872505 : Blo 1313975 1872505 := bstep (se 2 (by rfl) ⟨702189, by rfl⟩ : syracuseStep 1872505 = 1404379) B1404379
theorem B1479343 : Blo 1313975 1479343 := bstep (se 1 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 1479343 = 2219015) B2219015
theorem B1315551 : Blo 1313975 1315551 := bstep (se 1 (by rfl) ⟨986663, by rfl⟩ : syracuseStep 1315551 = 1973327) B1973327
theorem B1315631 : Blo 1313975 1315631 := bstep (se 1 (by rfl) ⟨986723, by rfl⟩ : syracuseStep 1315631 = 1973447) B1973447
theorem B1971023 : Blo 1313975 1971023 := bstep (se 1 (by rfl) ⟨1478267, by rfl⟩ : syracuseStep 1971023 = 2956535) B2956535
theorem B1315739 : Blo 1313975 1315739 := bstep (se 1 (by rfl) ⟨986804, by rfl⟩ : syracuseStep 1315739 = 1973609) B1973609
theorem B1479631 : Blo 1313975 1479631 := bstep (se 1 (by rfl) ⟨1109723, by rfl⟩ : syracuseStep 1479631 = 2219447) B2219447
theorem B1315791 : Blo 1313975 1315791 := bstep (se 1 (by rfl) ⟨986843, by rfl⟩ : syracuseStep 1315791 = 1973687) B1973687
theorem B1315815 : Blo 1313975 1315815 := bstep (se 1 (by rfl) ⟨986861, by rfl⟩ : syracuseStep 1315815 = 1973723) B1973723
theorem B3552455 : Blo 1313975 3552455 := bstep (se 1 (by rfl) ⟨2664341, by rfl⟩ : syracuseStep 3552455 = 5328683) B5328683
theorem B7492823 : Blo 1313975 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B1971419 : Blo 1313975 1971419 := bstep (se 1 (by rfl) ⟨1478564, by rfl⟩ : syracuseStep 1971419 = 2957129) B2957129
theorem B4437287 : Blo 1313975 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B5616935 : Blo 1313975 5616935 := bstep (se 1 (by rfl) ⟨4212701, by rfl⟩ : syracuseStep 5616935 = 8425403) B8425403
theorem B1480027 : Blo 1313975 1480027 := bstep (se 1 (by rfl) ⟨1110020, by rfl⟩ : syracuseStep 1480027 = 2220041) B2220041
theorem B6657389 : Blo 1313975 6657389 := bstep (se 3 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 6657389 = 2496521) B2496521
theorem B2053499 : Blo 1313975 2053499 := bstep (se 1 (by rfl) ⟨1540124, by rfl⟩ : syracuseStep 2053499 = 3080249) B3080249
theorem B12637565 : Blo 1313975 12637565 := bstep (se 3 (by rfl) ⟨2369543, by rfl⟩ : syracuseStep 12637565 = 4739087) B4739087
theorem B1971593 : Blo 1313975 1971593 := bstep (se 2 (by rfl) ⟨739347, by rfl⟩ : syracuseStep 1971593 = 1478695) B1478695
theorem B2217415 : Blo 1313975 2217415 := bstep (se 1 (by rfl) ⟨1663061, by rfl⟩ : syracuseStep 2217415 = 3326123) B3326123
theorem B1480135 : Blo 1313975 1480135 := bstep (se 1 (by rfl) ⟨1110101, by rfl⟩ : syracuseStep 1480135 = 2220203) B2220203
theorem B2496187 : Blo 1313975 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B1971947 : Blo 1313975 1971947 := bstep (se 1 (by rfl) ⟨1478960, by rfl⟩ : syracuseStep 1971947 = 2957921) B2957921
theorem B2217935 : Blo 1313975 2217935 := bstep (se 1 (by rfl) ⟨1663451, by rfl⟩ : syracuseStep 2217935 = 3326903) B3326903
theorem B2807759 : Blo 1313975 2807759 := bstep (se 1 (by rfl) ⟨2105819, by rfl⟩ : syracuseStep 2807759 = 4211639) B4211639
theorem B1972175 : Blo 1313975 1972175 := bstep (se 1 (by rfl) ⟨1479131, by rfl⟩ : syracuseStep 1972175 = 2958263) B2958263
theorem B3553409 : Blo 1313975 3553409 := bstep (se 2 (by rfl) ⟨1332528, by rfl⟩ : syracuseStep 3553409 = 2665057) B2665057
theorem B4438151 : Blo 1313975 4438151 := bstep (se 1 (by rfl) ⟨3328613, by rfl⟩ : syracuseStep 4438151 = 6657227) B6657227
theorem B11991287 : Blo 1313975 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B7108889 : Blo 1313975 7108889 := bstep (se 2 (by rfl) ⟨2665833, by rfl⟩ : syracuseStep 7108889 = 5331667) B5331667
theorem B1972571 : Blo 1313975 1972571 := bstep (se 1 (by rfl) ⟨1479428, by rfl⟩ : syracuseStep 1972571 = 2958857) B2958857
theorem B3742163 : Blo 1313975 3742163 := bstep (se 1 (by rfl) ⟨2806622, by rfl⟩ : syracuseStep 3742163 = 5613245) B5613245
theorem B1972799 : Blo 1313975 1972799 := bstep (se 1 (by rfl) ⟨1479599, by rfl⟩ : syracuseStep 1972799 = 2959199) B2959199
theorem B2218603 : Blo 1313975 2218603 := bstep (se 1 (by rfl) ⟨1663952, by rfl⟩ : syracuseStep 2218603 = 3327905) B3327905
theorem B22469237 : Blo 1313975 22469237 := bstep (se 5 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 22469237 = 2106491) B2106491
theorem B1972919 : Blo 1313975 1972919 := bstep (se 1 (by rfl) ⟨1479689, by rfl⟩ : syracuseStep 1972919 = 2959379) B2959379
theorem B12638915 : Blo 1313975 12638915 := bstep (se 1 (by rfl) ⟨9479186, by rfl⟩ : syracuseStep 12638915 = 18958373) B18958373
theorem B9001847 : Blo 1313975 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B17996687 : Blo 1313975 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B2218907 : Blo 1313975 2218907 := bstep (se 1 (by rfl) ⟨1664180, by rfl⟩ : syracuseStep 2218907 = 3328361) B3328361
theorem B1973147 : Blo 1313975 1973147 := bstep (se 1 (by rfl) ⟨1479860, by rfl⟩ : syracuseStep 1973147 = 2959721) B2959721
theorem B3996659 : Blo 1313975 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B13491353 : Blo 1313975 13491353 := bstep (se 2 (by rfl) ⟨5059257, by rfl⟩ : syracuseStep 13491353 = 10118515) B10118515
theorem B1973543 : Blo 1313975 1973543 := bstep (se 1 (by rfl) ⟨1480157, by rfl⟩ : syracuseStep 1973543 = 2960315) B2960315
theorem B12639563 : Blo 1313975 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B4439393 : Blo 1313975 4439393 := bstep (se 2 (by rfl) ⟨1664772, by rfl⟩ : syracuseStep 4439393 = 3329545) B3329545
theorem B1973627 : Blo 1313975 1973627 := bstep (se 1 (by rfl) ⟨1480220, by rfl⟩ : syracuseStep 1973627 = 2960441) B2960441
theorem B1580455 : Blo 1313975 1580455 := bstep (se 1 (by rfl) ⟨1185341, by rfl⟩ : syracuseStep 1580455 = 2370683) B2370683
theorem B2104775 : Blo 1313975 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B11238857 : Blo 1313975 11238857 := bstep (se 2 (by rfl) ⟨4214571, by rfl⟩ : syracuseStep 11238857 = 8429143) B8429143
theorem B1973753 : Blo 1313975 1973753 := bstep (se 2 (by rfl) ⟨740157, by rfl⟩ : syracuseStep 1973753 = 1480315) B1480315
theorem B7486991 : Blo 1313975 7486991 := bstep (se 1 (by rfl) ⟨5615243, by rfl⟩ : syracuseStep 7486991 = 11230487) B11230487
theorem B2498131 : Blo 1313975 2498131 := bstep (se 1 (by rfl) ⟨1873598, by rfl⟩ : syracuseStep 2498131 = 3747197) B3747197
theorem B2956895 : Blo 1313975 2956895 := bstep (se 1 (by rfl) ⟨2217671, by rfl⟩ : syracuseStep 2956895 = 4435343) B4435343
theorem B1973855 : Blo 1313975 1973855 := bstep (se 1 (by rfl) ⟨1480391, by rfl⟩ : syracuseStep 1973855 = 2960783) B2960783
theorem B8216225 : Blo 1313975 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B6659819 : Blo 1313975 6659819 := bstep (se 1 (by rfl) ⟨4994864, by rfl⟩ : syracuseStep 6659819 = 9989729) B9989729
theorem B2957111 : Blo 1313975 2957111 := bstep (se 1 (by rfl) ⟨2217833, by rfl⟩ : syracuseStep 2957111 = 4435667) B4435667
theorem B6652043 : Blo 1313975 6652043 := bstep (se 1 (by rfl) ⟨4989032, by rfl⟩ : syracuseStep 6652043 = 9978065) B9978065
theorem B4440203 : Blo 1313975 4440203 := bstep (se 1 (by rfl) ⟨3330152, by rfl⟩ : syracuseStep 4440203 = 6660305) B6660305
theorem B2105531 : Blo 1313975 2105531 := bstep (se 1 (by rfl) ⟨1579148, by rfl⟩ : syracuseStep 2105531 = 3158297) B3158297
theorem B2957543 : Blo 1313975 2957543 := bstep (se 1 (by rfl) ⟨2218157, by rfl⟩ : syracuseStep 2957543 = 4436315) B4436315
theorem B4989215 : Blo 1313975 4989215 := bstep (se 1 (by rfl) ⟨3741911, by rfl⟩ : syracuseStep 4989215 = 7483823) B7483823
theorem B32858455 : Blo 1313975 32858455 := bstep (se 1 (by rfl) ⟨24643841, by rfl⟩ : syracuseStep 32858455 = 49287683) B49287683
theorem B3326305 : Blo 1313975 3326305 := bstep (se 2 (by rfl) ⟨1247364, by rfl⟩ : syracuseStep 3326305 = 2494729) B2494729
theorem B6652367 : Blo 1313975 6652367 := bstep (se 1 (by rfl) ⟨4989275, by rfl⟩ : syracuseStep 6652367 = 9978551) B9978551
theorem B4440527 : Blo 1313975 4440527 := bstep (se 1 (by rfl) ⟨3330395, by rfl⟩ : syracuseStep 4440527 = 6660791) B6660791
theorem B31998563 : Blo 1313975 31998563 := bstep (se 1 (by rfl) ⟨23998922, by rfl⟩ : syracuseStep 31998563 = 47997845) B47997845
theorem B15188627 : Blo 1313975 15188627 := bstep (se 1 (by rfl) ⟨11391470, by rfl⟩ : syracuseStep 15188627 = 22782941) B22782941
theorem B18957037 : Blo 1313975 18957037 := bstep (se 3 (by rfl) ⟨3554444, by rfl⟩ : syracuseStep 18957037 = 7108889) B7108889
theorem B4440851 : Blo 1313975 4440851 := bstep (se 1 (by rfl) ⟨3330638, by rfl⟩ : syracuseStep 4440851 = 6661277) B6661277
theorem B2958137 : Blo 1313975 2958137 := bstep (se 2 (by rfl) ⟨1109301, by rfl⟩ : syracuseStep 2958137 = 2218603) B2218603
theorem B2958191 : Blo 1313975 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B3744623 : Blo 1313975 3744623 := bstep (se 1 (by rfl) ⟨2808467, by rfl⟩ : syracuseStep 3744623 = 5616935) B5616935
theorem B35980217 : Blo 1313975 35980217 := bstep (se 2 (by rfl) ⟨13492581, by rfl⟩ : syracuseStep 35980217 = 26985163) B26985163
theorem B2368939 : Blo 1313975 2368939 := bstep (se 1 (by rfl) ⟨1776704, by rfl⟩ : syracuseStep 2368939 = 3553409) B3553409
theorem B2958767 : Blo 1313975 2958767 := bstep (se 1 (by rfl) ⟨2219075, by rfl⟩ : syracuseStep 2958767 = 4438151) B4438151
theorem B6653663 : Blo 1313975 6653663 := bstep (se 1 (by rfl) ⟨4990247, by rfl⟩ : syracuseStep 6653663 = 9980495) B9980495
theorem B6653825 : Blo 1313975 6653825 := bstep (se 2 (by rfl) ⟨2495184, by rfl⟩ : syracuseStep 6653825 = 4990369) B4990369
theorem B2959595 : Blo 1313975 2959595 := bstep (se 1 (by rfl) ⟨2219696, by rfl⟩ : syracuseStep 2959595 = 4439393) B4439393
theorem B3328249 : Blo 1313975 3328249 := bstep (se 2 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 3328249 = 2496187) B2496187
theorem B1403183 : Blo 1313975 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B4991327 : Blo 1313975 4991327 := bstep (se 1 (by rfl) ⟨3743495, by rfl⟩ : syracuseStep 4991327 = 7486991) B7486991
theorem B6318593 : Blo 1313975 6318593 := bstep (se 2 (by rfl) ⟨2369472, by rfl⟩ : syracuseStep 6318593 = 4738945) B4738945
theorem B15993449 : Blo 1313975 15993449 := bstep (se 2 (by rfl) ⟨5997543, by rfl⟩ : syracuseStep 15993449 = 11995087) B11995087
theorem B6654635 : Blo 1313975 6654635 := bstep (se 1 (by rfl) ⟨4990976, by rfl⟩ : syracuseStep 6654635 = 9981953) B9981953
theorem B9480887 : Blo 1313975 9480887 := bstep (se 1 (by rfl) ⟨7110665, by rfl⟩ : syracuseStep 9480887 = 14221331) B14221331
theorem B5057335 : Blo 1313975 5057335 := bstep (se 1 (by rfl) ⟨3793001, by rfl⟩ : syracuseStep 5057335 = 7586003) B7586003
theorem B7588703 : Blo 1313975 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B72010781 : Blo 1313975 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B9473213 : Blo 1313975 9473213 := bstep (se 3 (by rfl) ⟨1776227, by rfl⟩ : syracuseStep 9473213 = 3552455) B3552455
theorem B1314015 : Blo 1313975 1314015 := bstep (se 1 (by rfl) ⟨985511, by rfl⟩ : syracuseStep 1314015 = 1971023) B1971023
theorem B4992299 : Blo 1313975 4992299 := bstep (se 1 (by rfl) ⟨3744224, by rfl⟩ : syracuseStep 4992299 = 7488449) B7488449
theorem B31976765 : Blo 1313975 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B3747151 : Blo 1313975 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B28454237 : Blo 1313975 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B1314279 : Blo 1313975 1314279 := bstep (se 1 (by rfl) ⟨985709, by rfl⟩ : syracuseStep 1314279 = 1971419) B1971419
theorem B4435451 : Blo 1313975 4435451 := bstep (se 1 (by rfl) ⟨3326588, by rfl⟩ : syracuseStep 4435451 = 6653177) B6653177
theorem B3747323 : Blo 1313975 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B2960891 : Blo 1313975 2960891 := bstep (se 1 (by rfl) ⟨2220668, by rfl⟩ : syracuseStep 2960891 = 4441337) B4441337
theorem B8425043 : Blo 1313975 8425043 := bstep (se 1 (by rfl) ⟨6318782, by rfl⟩ : syracuseStep 8425043 = 12637565) B12637565
theorem B1314395 : Blo 1313975 1314395 := bstep (se 1 (by rfl) ⟨985796, by rfl⟩ : syracuseStep 1314395 = 1971593) B1971593
theorem B4435613 : Blo 1313975 4435613 := bstep (se 3 (by rfl) ⟨831677, by rfl⟩ : syracuseStep 4435613 = 1663355) B1663355
theorem B5475997 : Blo 1313975 5475997 := bstep (se 3 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 5475997 = 2053499) B2053499
theorem B54685357 : Blo 1313975 54685357 := bstep (se 3 (by rfl) ⟨10253504, by rfl⟩ : syracuseStep 54685357 = 20507009) B20507009
theorem B1314631 : Blo 1313975 1314631 := bstep (se 1 (by rfl) ⟨985973, by rfl⟩ : syracuseStep 1314631 = 1971947) B1971947
theorem B1478623 : Blo 1313975 1478623 := bstep (se 1 (by rfl) ⟨1108967, by rfl⟩ : syracuseStep 1478623 = 2217935) B2217935
theorem B1871839 : Blo 1313975 1871839 := bstep (se 1 (by rfl) ⟨1403879, by rfl⟩ : syracuseStep 1871839 = 2807759) B2807759
theorem B1314783 : Blo 1313975 1314783 := bstep (se 1 (by rfl) ⟨986087, by rfl⟩ : syracuseStep 1314783 = 1972175) B1972175
theorem B4436153 : Blo 1313975 4436153 := bstep (se 2 (by rfl) ⟨1663557, by rfl⟩ : syracuseStep 4436153 = 3327115) B3327115
theorem B1315047 : Blo 1313975 1315047 := bstep (se 1 (by rfl) ⟨986285, by rfl⟩ : syracuseStep 1315047 = 1972571) B1972571
theorem B2494775 : Blo 1313975 2494775 := bstep (se 1 (by rfl) ⟨1871081, by rfl⟩ : syracuseStep 2494775 = 3742163) B3742163
theorem B2666807 : Blo 1313975 2666807 := bstep (se 1 (by rfl) ⟨2000105, by rfl⟩ : syracuseStep 2666807 = 4000211) B4000211
theorem B1315199 : Blo 1313975 1315199 := bstep (se 1 (by rfl) ⟨986399, by rfl⟩ : syracuseStep 1315199 = 1972799) B1972799
theorem B14979491 : Blo 1313975 14979491 := bstep (se 1 (by rfl) ⟨11234618, by rfl⟩ : syracuseStep 14979491 = 22469237) B22469237
theorem B6320551 : Blo 1313975 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B1315279 : Blo 1313975 1315279 := bstep (se 1 (by rfl) ⟨986459, by rfl⟩ : syracuseStep 1315279 = 1972919) B1972919
theorem B8425943 : Blo 1313975 8425943 := bstep (se 1 (by rfl) ⟨6319457, by rfl⟩ : syracuseStep 8425943 = 12638915) B12638915
theorem B12644869 : Blo 1313975 12644869 := bstep (se 4 (by rfl) ⟨1185456, by rfl⟩ : syracuseStep 12644869 = 2370913) B2370913
theorem B6001231 : Blo 1313975 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B11997791 : Blo 1313975 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B1479271 : Blo 1313975 1479271 := bstep (se 1 (by rfl) ⟨1109453, by rfl⟩ : syracuseStep 1479271 = 2218907) B2218907
theorem B1315431 : Blo 1313975 1315431 := bstep (se 1 (by rfl) ⟨986573, by rfl⟩ : syracuseStep 1315431 = 1973147) B1973147
theorem B7484075 : Blo 1313975 7484075 := bstep (se 1 (by rfl) ⟨5613056, by rfl⟩ : syracuseStep 7484075 = 11226113) B11226113
theorem B3330841 : Blo 1313975 3330841 := bstep (se 2 (by rfl) ⟨1249065, by rfl⟩ : syracuseStep 3330841 = 2498131) B2498131
theorem B1315695 : Blo 1313975 1315695 := bstep (se 1 (by rfl) ⟨986771, by rfl⟩ : syracuseStep 1315695 = 1973543) B1973543
theorem B8426375 : Blo 1313975 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B1315751 : Blo 1313975 1315751 := bstep (se 1 (by rfl) ⟨986813, by rfl⟩ : syracuseStep 1315751 = 1973627) B1973627
theorem B7492571 : Blo 1313975 7492571 := bstep (se 1 (by rfl) ⟨5619428, by rfl⟩ : syracuseStep 7492571 = 11238857) B11238857
theorem B1315835 : Blo 1313975 1315835 := bstep (se 1 (by rfl) ⟨986876, by rfl⟩ : syracuseStep 1315835 = 1973753) B1973753
theorem B1971263 : Blo 1313975 1971263 := bstep (se 1 (by rfl) ⟨1478447, by rfl⟩ : syracuseStep 1971263 = 2956895) B2956895
theorem B1315903 : Blo 1313975 1315903 := bstep (se 1 (by rfl) ⟨986927, by rfl⟩ : syracuseStep 1315903 = 1973855) B1973855
theorem B1971305 : Blo 1313975 1971305 := bstep (se 2 (by rfl) ⟨739239, by rfl⟩ : syracuseStep 1971305 = 1478479) B1478479
theorem B5477483 : Blo 1313975 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B1971407 : Blo 1313975 1971407 := bstep (se 1 (by rfl) ⟨1478555, by rfl⟩ : syracuseStep 1971407 = 2957111) B2957111
theorem B1971611 : Blo 1313975 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B4994561 : Blo 1313975 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B3159623 : Blo 1313975 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B1971833 : Blo 1313975 1971833 := bstep (se 2 (by rfl) ⟨739437, by rfl⟩ : syracuseStep 1971833 = 1478875) B1478875
theorem B4994743 : Blo 1313975 4994743 := bstep (se 1 (by rfl) ⟨3746057, by rfl⟩ : syracuseStep 4994743 = 7492115) B7492115
theorem B1971935 : Blo 1313975 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B1972031 : Blo 1313975 1972031 := bstep (se 1 (by rfl) ⟨1479023, by rfl⟩ : syracuseStep 1972031 = 2958047) B2958047
theorem B1972199 : Blo 1313975 1972199 := bstep (se 1 (by rfl) ⟨1479149, by rfl⟩ : syracuseStep 1972199 = 2958299) B2958299
theorem B8427503 : Blo 1313975 8427503 := bstep (se 1 (by rfl) ⟨6320627, by rfl⟩ : syracuseStep 8427503 = 12641255) B12641255
theorem B2807801 : Blo 1313975 2807801 := bstep (se 2 (by rfl) ⟨1052925, by rfl⟩ : syracuseStep 2807801 = 2105851) B2105851
theorem B1972217 : Blo 1313975 1972217 := bstep (se 2 (by rfl) ⟨739581, by rfl⟩ : syracuseStep 1972217 = 1479163) B1479163
theorem B2807903 : Blo 1313975 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B1972319 : Blo 1313975 1972319 := bstep (se 1 (by rfl) ⟨1479239, by rfl⟩ : syracuseStep 1972319 = 2958479) B2958479
theorem B4995215 : Blo 1313975 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B1972379 : Blo 1313975 1972379 := bstep (se 1 (by rfl) ⟨1479284, by rfl⟩ : syracuseStep 1972379 = 2958569) B2958569
theorem B2496673 : Blo 1313975 2496673 := bstep (se 2 (by rfl) ⟨936252, by rfl⟩ : syracuseStep 2496673 = 1872505) B1872505
theorem B1972415 : Blo 1313975 1972415 := bstep (se 1 (by rfl) ⟨1479311, by rfl⟩ : syracuseStep 1972415 = 2958623) B2958623
theorem B1972457 : Blo 1313975 1972457 := bstep (se 2 (by rfl) ⟨739671, by rfl⟩ : syracuseStep 1972457 = 1479343) B1479343
theorem B4438259 : Blo 1313975 4438259 := bstep (se 1 (by rfl) ⟨3328694, by rfl⟩ : syracuseStep 4438259 = 6657389) B6657389
theorem B2218279 : Blo 1313975 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B4438313 : Blo 1313975 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B5617993 : Blo 1313975 5617993 := bstep (se 2 (by rfl) ⟨2106747, by rfl⟩ : syracuseStep 5617993 = 4213495) B4213495
theorem B14989697 : Blo 1313975 14989697 := bstep (se 2 (by rfl) ⟨5621136, by rfl⟩ : syracuseStep 14989697 = 11242273) B11242273
theorem B41613749 : Blo 1313975 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B6658523 : Blo 1313975 6658523 := bstep (se 1 (by rfl) ⟨4993892, by rfl⟩ : syracuseStep 6658523 = 9987785) B9987785
theorem B1972763 : Blo 1313975 1972763 := bstep (se 1 (by rfl) ⟨1479572, by rfl⟩ : syracuseStep 1972763 = 2959145) B2959145
theorem B1972841 : Blo 1313975 1972841 := bstep (se 2 (by rfl) ⟨739815, by rfl⟩ : syracuseStep 1972841 = 1479631) B1479631
theorem B7494281 : Blo 1313975 7494281 := bstep (se 2 (by rfl) ⟨2810355, by rfl⟩ : syracuseStep 7494281 = 5620711) B5620711
theorem B6077081 : Blo 1313975 6077081 := bstep (se 2 (by rfl) ⟨2278905, by rfl⟩ : syracuseStep 6077081 = 4557811) B4557811
theorem B6314861 : Blo 1313975 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B27007991 : Blo 1313975 27007991 := bstep (se 1 (by rfl) ⟨20255993, by rfl⟩ : syracuseStep 27007991 = 40511987) B40511987
theorem B7494713 : Blo 1313975 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B1973369 : Blo 1313975 1973369 := bstep (se 2 (by rfl) ⟨740013, by rfl⟩ : syracuseStep 1973369 = 1480027) B1480027
theorem B1580215 : Blo 1313975 1580215 := bstep (se 1 (by rfl) ⟨1185161, by rfl⟩ : syracuseStep 1580215 = 2370323) B2370323
theorem B2219231 : Blo 1313975 2219231 := bstep (se 1 (by rfl) ⟨1664423, by rfl⟩ : syracuseStep 2219231 = 3328847) B3328847
theorem B1973471 : Blo 1313975 1973471 := bstep (se 1 (by rfl) ⟨1480103, by rfl⟩ : syracuseStep 1973471 = 2960207) B2960207
theorem B2956553 : Blo 1313975 2956553 := bstep (se 2 (by rfl) ⟨1108707, by rfl⟩ : syracuseStep 2956553 = 2217415) B2217415
theorem B1973513 : Blo 1313975 1973513 := bstep (se 2 (by rfl) ⟨740067, by rfl⟩ : syracuseStep 1973513 = 1480135) B1480135
theorem B1973615 : Blo 1313975 1973615 := bstep (se 1 (by rfl) ⟨1480211, by rfl⟩ : syracuseStep 1973615 = 2960423) B2960423
theorem B8994235 : Blo 1313975 8994235 := bstep (se 1 (by rfl) ⟨6745676, by rfl⟩ : syracuseStep 8994235 = 13491353) B13491353
theorem B1973735 : Blo 1313975 1973735 := bstep (se 1 (by rfl) ⟨1480301, by rfl⟩ : syracuseStep 1973735 = 2960603) B2960603
theorem B8429093 : Blo 1313975 8429093 := bstep (se 4 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 8429093 = 1580455) B1580455
theorem B1973867 : Blo 1313975 1973867 := bstep (se 1 (by rfl) ⟨1480400, by rfl⟩ : syracuseStep 1973867 = 2960801) B2960801
theorem B2219663 : Blo 1313975 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B4439879 : Blo 1313975 4439879 := bstep (se 1 (by rfl) ⟨3329909, by rfl⟩ : syracuseStep 4439879 = 6659819) B6659819
theorem B2219899 : Blo 1313975 2219899 := bstep (se 1 (by rfl) ⟨1664924, by rfl⟩ : syracuseStep 2219899 = 3329849) B3329849
theorem B4439933 : Blo 1313975 4439933 := bstep (se 3 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 4439933 = 1664975) B1664975
theorem B10657757 : Blo 1313975 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B2957435 : Blo 1313975 2957435 := bstep (se 1 (by rfl) ⟨2218076, by rfl⟩ : syracuseStep 2957435 = 4436153) B4436153
theorem B3326143 : Blo 1313975 3326143 := bstep (se 1 (by rfl) ⟨2494607, by rfl⟩ : syracuseStep 3326143 = 4989215) B4989215
theorem B1663183 : Blo 1313975 1663183 := bstep (se 1 (by rfl) ⟨1247387, by rfl⟩ : syracuseStep 1663183 = 2494775) B2494775
theorem B1777871 : Blo 1313975 1777871 := bstep (se 1 (by rfl) ⟨1333403, by rfl⟩ : syracuseStep 1777871 = 2666807) B2666807
theorem B7487741 : Blo 1313975 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B9986327 : Blo 1313975 9986327 := bstep (se 1 (by rfl) ⟨7489745, by rfl⟩ : syracuseStep 9986327 = 14979491) B14979491
theorem B2957705 : Blo 1313975 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B21332375 : Blo 1313975 21332375 := bstep (se 1 (by rfl) ⟨15999281, by rfl⟩ : syracuseStep 21332375 = 31998563) B31998563
theorem B10125751 : Blo 1313975 10125751 := bstep (se 1 (by rfl) ⟨7594313, by rfl⟩ : syracuseStep 10125751 = 15188627) B15188627
theorem B4989383 : Blo 1313975 4989383 := bstep (se 1 (by rfl) ⟨3742037, by rfl⟩ : syracuseStep 4989383 = 7484075) B7484075
theorem B43811273 : Blo 1313975 43811273 := bstep (se 2 (by rfl) ⟨16429227, by rfl⟩ : syracuseStep 43811273 = 32858455) B32858455
theorem B23986811 : Blo 1313975 23986811 := bstep (se 1 (by rfl) ⟨17990108, by rfl⟩ : syracuseStep 23986811 = 35980217) B35980217
theorem B16859825 : Blo 1313975 16859825 := bstep (se 2 (by rfl) ⟨6322434, by rfl⟩ : syracuseStep 16859825 = 12644869) B12644869
theorem B4441121 : Blo 1313975 4441121 := bstep (se 2 (by rfl) ⟨1665420, by rfl⟩ : syracuseStep 4441121 = 3330841) B3330841
theorem B2106415 : Blo 1313975 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B2958839 : Blo 1313975 2958839 := bstep (se 1 (by rfl) ⟨2219129, by rfl⟩ : syracuseStep 2958839 = 4438259) B4438259
theorem B2958875 : Blo 1313975 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B3327551 : Blo 1313975 3327551 := bstep (se 1 (by rfl) ⟨2495663, by rfl⟩ : syracuseStep 3327551 = 4991327) B4991327
theorem B2106953 : Blo 1313975 2106953 := bstep (se 2 (by rfl) ⟨790107, by rfl⟩ : syracuseStep 2106953 = 1580215) B1580215
theorem B4212395 : Blo 1313975 4212395 := bstep (se 1 (by rfl) ⟨3159296, by rfl⟩ : syracuseStep 4212395 = 6318593) B6318593
theorem B48007187 : Blo 1313975 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B3328199 : Blo 1313975 3328199 := bstep (se 1 (by rfl) ⟨2496149, by rfl⟩ : syracuseStep 3328199 = 4992299) B4992299
theorem B7301329 : Blo 1313975 7301329 := bstep (se 2 (by rfl) ⟨2737998, by rfl⟩ : syracuseStep 7301329 = 5475997) B5475997
theorem B21317843 : Blo 1313975 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B2959865 : Blo 1313975 2959865 := bstep (se 2 (by rfl) ⟨1109949, by rfl⟩ : syracuseStep 2959865 = 2219899) B2219899
theorem B2959919 : Blo 1313975 2959919 := bstep (se 1 (by rfl) ⟨2219939, by rfl⟩ : syracuseStep 2959919 = 4439879) B4439879
theorem B2959955 : Blo 1313975 2959955 := bstep (se 1 (by rfl) ⟨2219966, by rfl⟩ : syracuseStep 2959955 = 4439933) B4439933
theorem B7105171 : Blo 1313975 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B4434695 : Blo 1313975 4434695 := bstep (se 1 (by rfl) ⟨3326021, by rfl⟩ : syracuseStep 4434695 = 6652043) B6652043
theorem B2960135 : Blo 1313975 2960135 := bstep (se 1 (by rfl) ⟨2220101, by rfl⟩ : syracuseStep 2960135 = 4440203) B4440203
theorem B1403687 : Blo 1313975 1403687 := bstep (se 1 (by rfl) ⟨1052765, by rfl⟩ : syracuseStep 1403687 = 2105531) B2105531
theorem B3328897 : Blo 1313975 3328897 := bstep (se 2 (by rfl) ⟨1248336, by rfl⟩ : syracuseStep 3328897 = 2496673) B2496673
theorem B4434911 : Blo 1313975 4434911 := bstep (se 1 (by rfl) ⟨3326183, by rfl⟩ : syracuseStep 4434911 = 6652367) B6652367
theorem B2960351 : Blo 1313975 2960351 := bstep (se 1 (by rfl) ⟨2220263, by rfl⟩ : syracuseStep 2960351 = 4440527) B4440527
theorem B7998527 : Blo 1313975 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B7490657 : Blo 1313975 7490657 := bstep (se 2 (by rfl) ⟨2808996, by rfl⟩ : syracuseStep 7490657 = 5617993) B5617993
theorem B4435073 : Blo 1313975 4435073 := bstep (se 2 (by rfl) ⟨1663152, by rfl⟩ : syracuseStep 4435073 = 3326305) B3326305
theorem B2960567 : Blo 1313975 2960567 := bstep (se 1 (by rfl) ⟨2220425, by rfl⟩ : syracuseStep 2960567 = 4440851) B4440851
theorem B1314175 : Blo 1313975 1314175 := bstep (se 1 (by rfl) ⟨985631, by rfl⟩ : syracuseStep 1314175 = 1971263) B1971263
theorem B1314203 : Blo 1313975 1314203 := bstep (se 1 (by rfl) ⟨985652, by rfl⟩ : syracuseStep 1314203 = 1971305) B1971305
theorem B1314271 : Blo 1313975 1314271 := bstep (se 1 (by rfl) ⟨985703, by rfl⟩ : syracuseStep 1314271 = 1971407) B1971407
theorem B291655237 : Blo 1313975 291655237 := bstep (se 4 (by rfl) ⟨27342678, by rfl⟩ : syracuseStep 291655237 = 54685357) B54685357
theorem B1314407 : Blo 1313975 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B25276049 : Blo 1313975 25276049 := bstep (se 2 (by rfl) ⟨9478518, by rfl⟩ : syracuseStep 25276049 = 18957037) B18957037
theorem B3329707 : Blo 1313975 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B1314555 : Blo 1313975 1314555 := bstep (se 1 (by rfl) ⟨985916, by rfl⟩ : syracuseStep 1314555 = 1971833) B1971833
theorem B4435775 : Blo 1313975 4435775 := bstep (se 1 (by rfl) ⟨3326831, by rfl⟩ : syracuseStep 4435775 = 6653663) B6653663
theorem B1314623 : Blo 1313975 1314623 := bstep (se 1 (by rfl) ⟨985967, by rfl⟩ : syracuseStep 1314623 = 1971935) B1971935
theorem B1314687 : Blo 1313975 1314687 := bstep (se 1 (by rfl) ⟨986015, by rfl⟩ : syracuseStep 1314687 = 1972031) B1972031
theorem B4435883 : Blo 1313975 4435883 := bstep (se 1 (by rfl) ⟨3326912, by rfl⟩ : syracuseStep 4435883 = 6653825) B6653825
theorem B1314799 : Blo 1313975 1314799 := bstep (se 1 (by rfl) ⟨986099, by rfl⟩ : syracuseStep 1314799 = 1972199) B1972199
theorem B1871867 : Blo 1313975 1871867 := bstep (se 1 (by rfl) ⟨1403900, by rfl⟩ : syracuseStep 1871867 = 2807801) B2807801
theorem B1314811 : Blo 1313975 1314811 := bstep (se 1 (by rfl) ⟨986108, by rfl⟩ : syracuseStep 1314811 = 1972217) B1972217
theorem B1314879 : Blo 1313975 1314879 := bstep (se 1 (by rfl) ⟨986159, by rfl⟩ : syracuseStep 1314879 = 1972319) B1972319
theorem B3330143 : Blo 1313975 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B1314919 : Blo 1313975 1314919 := bstep (se 1 (by rfl) ⟨986189, by rfl⟩ : syracuseStep 1314919 = 1972379) B1972379
theorem B1314943 : Blo 1313975 1314943 := bstep (se 1 (by rfl) ⟨986207, by rfl⟩ : syracuseStep 1314943 = 1972415) B1972415
theorem B1314971 : Blo 1313975 1314971 := bstep (se 1 (by rfl) ⟨986228, by rfl⟩ : syracuseStep 1314971 = 1972457) B1972457
theorem B26972453 : Blo 1313975 26972453 := bstep (se 4 (by rfl) ⟨2528667, by rfl⟩ : syracuseStep 26972453 = 5057335) B5057335
theorem B27742499 : Blo 1313975 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B1315175 : Blo 1313975 1315175 := bstep (se 1 (by rfl) ⟨986381, by rfl⟩ : syracuseStep 1315175 = 1972763) B1972763
theorem B10662299 : Blo 1313975 10662299 := bstep (se 1 (by rfl) ⟨7996724, by rfl⟩ : syracuseStep 10662299 = 15993449) B15993449
theorem B1315227 : Blo 1313975 1315227 := bstep (se 1 (by rfl) ⟨986420, by rfl⟩ : syracuseStep 1315227 = 1972841) B1972841
theorem B4051387 : Blo 1313975 4051387 := bstep (se 1 (by rfl) ⟨3038540, by rfl⟩ : syracuseStep 4051387 = 6077081) B6077081
theorem B4436423 : Blo 1313975 4436423 := bstep (se 1 (by rfl) ⟨3327317, by rfl⟩ : syracuseStep 4436423 = 6654635) B6654635
theorem B6320591 : Blo 1313975 6320591 := bstep (se 1 (by rfl) ⟨4740443, by rfl⟩ : syracuseStep 6320591 = 9480887) B9480887
theorem B3158585 : Blo 1313975 3158585 := bstep (se 2 (by rfl) ⟨1184469, by rfl⟩ : syracuseStep 3158585 = 2368939) B2368939
theorem B5059135 : Blo 1313975 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B1315579 : Blo 1313975 1315579 := bstep (se 1 (by rfl) ⟨986684, by rfl⟩ : syracuseStep 1315579 = 1973369) B1973369
theorem B1479487 : Blo 1313975 1479487 := bstep (se 1 (by rfl) ⟨1109615, by rfl⟩ : syracuseStep 1479487 = 2219231) B2219231
theorem B1315647 : Blo 1313975 1315647 := bstep (se 1 (by rfl) ⟨986735, by rfl⟩ : syracuseStep 1315647 = 1973471) B1973471
theorem B1971035 : Blo 1313975 1971035 := bstep (se 1 (by rfl) ⟨1478276, by rfl⟩ : syracuseStep 1971035 = 2956553) B2956553
theorem B1315675 : Blo 1313975 1315675 := bstep (se 1 (by rfl) ⟨986756, by rfl⟩ : syracuseStep 1315675 = 1973513) B1973513
theorem B18969491 : Blo 1313975 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1315743 : Blo 1313975 1315743 := bstep (se 1 (by rfl) ⟨986807, by rfl⟩ : syracuseStep 1315743 = 1973615) B1973615
theorem B1315823 : Blo 1313975 1315823 := bstep (se 1 (by rfl) ⟨986867, by rfl⟩ : syracuseStep 1315823 = 1973735) B1973735
theorem B5616695 : Blo 1313975 5616695 := bstep (se 1 (by rfl) ⟨4212521, by rfl⟩ : syracuseStep 5616695 = 8425043) B8425043
theorem B1315911 : Blo 1313975 1315911 := bstep (se 1 (by rfl) ⟨986933, by rfl⟩ : syracuseStep 1315911 = 1973867) B1973867
theorem B1479775 : Blo 1313975 1479775 := bstep (se 1 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 1479775 = 2219663) B2219663
theorem B1971497 : Blo 1313975 1971497 := bstep (se 2 (by rfl) ⟨739311, by rfl⟩ : syracuseStep 1971497 = 1478623) B1478623
theorem B2495785 : Blo 1313975 2495785 := bstep (se 2 (by rfl) ⟨935919, by rfl⟩ : syracuseStep 2495785 = 1871839) B1871839
theorem B1971695 : Blo 1313975 1971695 := bstep (se 1 (by rfl) ⟨1478771, by rfl⟩ : syracuseStep 1971695 = 2957543) B2957543
theorem B5617295 : Blo 1313975 5617295 := bstep (se 1 (by rfl) ⟨4212971, by rfl⟩ : syracuseStep 5617295 = 8425943) B8425943
theorem B4437665 : Blo 1313975 4437665 := bstep (se 2 (by rfl) ⟨1664124, by rfl⟩ : syracuseStep 4437665 = 3328249) B3328249
theorem B25261901 : Blo 1313975 25261901 := bstep (se 3 (by rfl) ⟨4736606, by rfl⟩ : syracuseStep 25261901 = 9473213) B9473213
theorem B1972091 : Blo 1313975 1972091 := bstep (se 1 (by rfl) ⟨1479068, by rfl⟩ : syracuseStep 1972091 = 2958137) B2958137
theorem B8427401 : Blo 1313975 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B1972127 : Blo 1313975 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B2496415 : Blo 1313975 2496415 := bstep (se 1 (by rfl) ⟨1872311, by rfl⟩ : syracuseStep 2496415 = 3744623) B3744623
theorem B5617583 : Blo 1313975 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B4995047 : Blo 1313975 4995047 := bstep (se 1 (by rfl) ⟨3746285, by rfl⟩ : syracuseStep 4995047 = 7492571) B7492571
theorem B3651655 : Blo 1313975 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B8001641 : Blo 1313975 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B3741821 : Blo 1313975 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B1972361 : Blo 1313975 1972361 := bstep (se 2 (by rfl) ⟨739635, by rfl⟩ : syracuseStep 1972361 = 1479271) B1479271
theorem B1972511 : Blo 1313975 1972511 := bstep (se 1 (by rfl) ⟨1479383, by rfl⟩ : syracuseStep 1972511 = 2958767) B2958767
theorem B5618335 : Blo 1313975 5618335 := bstep (se 1 (by rfl) ⟨4213751, by rfl⟩ : syracuseStep 5618335 = 8427503) B8427503
theorem B1973063 : Blo 1313975 1973063 := bstep (se 1 (by rfl) ⟨1479797, by rfl⟩ : syracuseStep 1973063 = 2959595) B2959595
theorem B9993131 : Blo 1313975 9993131 := bstep (se 1 (by rfl) ⟨7494848, by rfl⟩ : syracuseStep 9993131 = 14989697) B14989697
theorem B4439015 : Blo 1313975 4439015 := bstep (se 1 (by rfl) ⟨3329261, by rfl⟩ : syracuseStep 4439015 = 6658523) B6658523
theorem B4996187 : Blo 1313975 4996187 := bstep (se 1 (by rfl) ⟨3747140, by rfl⟩ : syracuseStep 4996187 = 7494281) B7494281
theorem B4996201 : Blo 1313975 4996201 := bstep (se 2 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 4996201 = 3747151) B3747151
theorem B4209907 : Blo 1313975 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B11992313 : Blo 1313975 11992313 := bstep (se 2 (by rfl) ⟨4497117, by rfl⟩ : syracuseStep 11992313 = 8994235) B8994235
theorem B18005327 : Blo 1313975 18005327 := bstep (se 1 (by rfl) ⟨13503995, by rfl⟩ : syracuseStep 18005327 = 27007991) B27007991
theorem B4996475 : Blo 1313975 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B6659657 : Blo 1313975 6659657 := bstep (se 2 (by rfl) ⟨2497371, by rfl⟩ : syracuseStep 6659657 = 4994743) B4994743
theorem B2956967 : Blo 1313975 2956967 := bstep (se 1 (by rfl) ⟨2217725, by rfl⟩ : syracuseStep 2956967 = 4435451) B4435451
theorem B2498215 : Blo 1313975 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B1973927 : Blo 1313975 1973927 := bstep (se 1 (by rfl) ⟨1480445, by rfl⟩ : syracuseStep 1973927 = 2960891) B2960891
theorem B5619395 : Blo 1313975 5619395 := bstep (se 1 (by rfl) ⟨4214546, by rfl⟩ : syracuseStep 5619395 = 8429093) B8429093
theorem B2957075 : Blo 1313975 2957075 := bstep (se 1 (by rfl) ⟨2217806, by rfl⟩ : syracuseStep 2957075 = 4435613) B4435613
theorem B2220095 : Blo 1313975 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B17981635 : Blo 1313975 17981635 := bstep (se 1 (by rfl) ⟨13486226, by rfl⟩ : syracuseStep 17981635 = 26972453) B26972453
theorem B14221583 : Blo 1313975 14221583 := bstep (se 1 (by rfl) ⟨10666187, by rfl⟩ : syracuseStep 14221583 = 21332375) B21332375
theorem B3326255 : Blo 1313975 3326255 := bstep (se 1 (by rfl) ⟨2494691, by rfl⟩ : syracuseStep 3326255 = 4989383) B4989383
theorem B2957615 : Blo 1313975 2957615 := bstep (se 1 (by rfl) ⟨2218211, by rfl⟩ : syracuseStep 2957615 = 4436423) B4436423
theorem B2105723 : Blo 1313975 2105723 := bstep (se 1 (by rfl) ⟨1579292, by rfl⟩ : syracuseStep 2105723 = 3158585) B3158585
theorem B11239883 : Blo 1313975 11239883 := bstep (se 1 (by rfl) ⟨8429912, by rfl⟩ : syracuseStep 11239883 = 16859825) B16859825
theorem B13501001 : Blo 1313975 13501001 := bstep (se 2 (by rfl) ⟨5062875, by rfl⟩ : syracuseStep 13501001 = 10125751) B10125751
theorem B3744463 : Blo 1313975 3744463 := bstep (se 1 (by rfl) ⟨2808347, by rfl⟩ : syracuseStep 3744463 = 5616695) B5616695
theorem B3744863 : Blo 1313975 3744863 := bstep (se 1 (by rfl) ⟨2808647, by rfl⟩ : syracuseStep 3744863 = 5617295) B5617295
theorem B2958443 : Blo 1313975 2958443 := bstep (se 1 (by rfl) ⟨2218832, by rfl⟩ : syracuseStep 2958443 = 4437665) B4437665
theorem B3745055 : Blo 1313975 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B5334427 : Blo 1313975 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B6661601 : Blo 1313975 6661601 := bstep (se 2 (by rfl) ⟨2498100, by rfl⟩ : syracuseStep 6661601 = 4996201) B4996201
theorem B5613209 : Blo 1313975 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B63964829 : Blo 1313975 63964829 := bstep (se 3 (by rfl) ⟨11993405, by rfl⟩ : syracuseStep 63964829 = 23986811) B23986811
theorem B3327713 : Blo 1313975 3327713 := bstep (se 2 (by rfl) ⟨1247892, by rfl⟩ : syracuseStep 3327713 = 2495785) B2495785
theorem B6662087 : Blo 1313975 6662087 := bstep (se 1 (by rfl) ⟨4996565, by rfl⟩ : syracuseStep 6662087 = 9993131) B9993131
theorem B2959343 : Blo 1313975 2959343 := bstep (se 1 (by rfl) ⟨2219507, by rfl⟩ : syracuseStep 2959343 = 4439015) B4439015
theorem B12003551 : Blo 1313975 12003551 := bstep (se 1 (by rfl) ⟨9002663, by rfl⟩ : syracuseStep 12003551 = 18005327) B18005327
theorem B3746263 : Blo 1313975 3746263 := bstep (se 1 (by rfl) ⟨2809697, by rfl⟩ : syracuseStep 3746263 = 5619395) B5619395
theorem B3328553 : Blo 1313975 3328553 := bstep (se 2 (by rfl) ⟨1248207, by rfl⟩ : syracuseStep 3328553 = 2496415) B2496415
theorem B4991645 : Blo 1313975 4991645 := bstep (se 3 (by rfl) ⟨935933, by rfl⟩ : syracuseStep 4991645 = 1871867) B1871867
theorem B4868873 : Blo 1313975 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B4991827 : Blo 1313975 4991827 := bstep (se 1 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 4991827 = 7487741) B7487741
theorem B4434857 : Blo 1313975 4434857 := bstep (se 2 (by rfl) ⟨1663071, by rfl⟩ : syracuseStep 4434857 = 3326143) B3326143
theorem B29207515 : Blo 1313975 29207515 := bstep (se 1 (by rfl) ⟨21905636, by rfl⟩ : syracuseStep 29207515 = 43811273) B43811273
theorem B4213727 : Blo 1313975 4213727 := bstep (se 1 (by rfl) ⟨3160295, by rfl⟩ : syracuseStep 4213727 = 6320591) B6320591
theorem B56847581 : Blo 1313975 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B1314023 : Blo 1313975 1314023 := bstep (se 1 (by rfl) ⟨985517, by rfl⟩ : syracuseStep 1314023 = 1971035) B1971035
theorem B5401849 : Blo 1313975 5401849 := bstep (se 2 (by rfl) ⟨2025693, by rfl⟩ : syracuseStep 5401849 = 4051387) B4051387
theorem B2960747 : Blo 1313975 2960747 := bstep (se 1 (by rfl) ⟨2220560, by rfl⟩ : syracuseStep 2960747 = 4441121) B4441121
theorem B6745513 : Blo 1313975 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B9473561 : Blo 1313975 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B1314331 : Blo 1313975 1314331 := bstep (se 1 (by rfl) ⟨985748, by rfl⟩ : syracuseStep 1314331 = 1971497) B1971497
theorem B7491113 : Blo 1313975 7491113 := bstep (se 2 (by rfl) ⟨2809167, by rfl⟩ : syracuseStep 7491113 = 5618335) B5618335
theorem B1314463 : Blo 1313975 1314463 := bstep (se 1 (by rfl) ⟨985847, by rfl⟩ : syracuseStep 1314463 = 1971695) B1971695
theorem B1404635 : Blo 1313975 1404635 := bstep (se 1 (by rfl) ⟨1053476, by rfl⟩ : syracuseStep 1404635 = 2106953) B2106953
theorem B38940421 : Blo 1313975 38940421 := bstep (se 4 (by rfl) ⟨3650664, by rfl⟩ : syracuseStep 38940421 = 7301329) B7301329
theorem B1314727 : Blo 1313975 1314727 := bstep (se 1 (by rfl) ⟨986045, by rfl⟩ : syracuseStep 1314727 = 1972091) B1972091
theorem B1314751 : Blo 1313975 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B3330031 : Blo 1313975 3330031 := bstep (se 1 (by rfl) ⟨2497523, by rfl⟩ : syracuseStep 3330031 = 4995047) B4995047
theorem B2494547 : Blo 1313975 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B1314907 : Blo 1313975 1314907 := bstep (se 1 (by rfl) ⟨986180, by rfl⟩ : syracuseStep 1314907 = 1972361) B1972361
theorem B1315007 : Blo 1313975 1315007 := bstep (se 1 (by rfl) ⟨986255, by rfl⟩ : syracuseStep 1315007 = 1972511) B1972511
theorem B1315375 : Blo 1313975 1315375 := bstep (se 1 (by rfl) ⟨986531, by rfl⟩ : syracuseStep 1315375 = 1973063) B1973063
theorem B3330791 : Blo 1313975 3330791 := bstep (se 1 (by rfl) ⟨2498093, by rfl⟩ : syracuseStep 3330791 = 4996187) B4996187
theorem B4993771 : Blo 1313975 4993771 := bstep (se 1 (by rfl) ⟨3745328, by rfl⟩ : syracuseStep 4993771 = 7490657) B7490657
theorem B3330953 : Blo 1313975 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B3330983 : Blo 1313975 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B1971311 : Blo 1313975 1971311 := bstep (se 1 (by rfl) ⟨1478483, by rfl⟩ : syracuseStep 1971311 = 2956967) B2956967
theorem B1315951 : Blo 1313975 1315951 := bstep (se 1 (by rfl) ⟨986963, by rfl⟩ : syracuseStep 1315951 = 1973927) B1973927
theorem B1971383 : Blo 1313975 1971383 := bstep (se 1 (by rfl) ⟨1478537, by rfl⟩ : syracuseStep 1971383 = 2957075) B2957075
theorem B1971623 : Blo 1313975 1971623 := bstep (se 1 (by rfl) ⟨1478717, by rfl⟩ : syracuseStep 1971623 = 2957435) B2957435
theorem B6657551 : Blo 1313975 6657551 := bstep (se 1 (by rfl) ⟨4993163, by rfl⟩ : syracuseStep 6657551 = 9986327) B9986327
theorem B18494999 : Blo 1313975 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B1971803 : Blo 1313975 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B7108199 : Blo 1313975 7108199 := bstep (se 1 (by rfl) ⟨5331149, by rfl⟩ : syracuseStep 7108199 = 10662299) B10662299
theorem B2217577 : Blo 1313975 2217577 := bstep (se 2 (by rfl) ⟨831591, by rfl⟩ : syracuseStep 2217577 = 1663183) B1663183
theorem B4740989 : Blo 1313975 4740989 := bstep (se 3 (by rfl) ⟨888935, by rfl⟩ : syracuseStep 4740989 = 1777871) B1777871
theorem B1972559 : Blo 1313975 1972559 := bstep (se 1 (by rfl) ⟨1479419, by rfl⟩ : syracuseStep 1972559 = 2958839) B2958839
theorem B1972583 : Blo 1313975 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B2218367 : Blo 1313975 2218367 := bstep (se 1 (by rfl) ⟨1663775, by rfl⟩ : syracuseStep 2218367 = 3327551) B3327551
theorem B1972649 : Blo 1313975 1972649 := bstep (se 2 (by rfl) ⟨739743, by rfl⟩ : syracuseStep 1972649 = 1479487) B1479487
theorem B2808263 : Blo 1313975 2808263 := bstep (se 1 (by rfl) ⟨2106197, by rfl⟩ : syracuseStep 2808263 = 4212395) B4212395
theorem B4438529 : Blo 1313975 4438529 := bstep (se 2 (by rfl) ⟨1664448, by rfl⟩ : syracuseStep 4438529 = 3328897) B3328897
theorem B16841267 : Blo 1313975 16841267 := bstep (se 1 (by rfl) ⟨12630950, by rfl⟩ : syracuseStep 16841267 = 25261901) B25261901
theorem B5618267 : Blo 1313975 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B32004791 : Blo 1313975 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B2808553 : Blo 1313975 2808553 := bstep (se 2 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 2808553 = 2106415) B2106415
theorem B1973033 : Blo 1313975 1973033 := bstep (se 2 (by rfl) ⟨739887, by rfl⟩ : syracuseStep 1973033 = 1479775) B1479775
theorem B2218799 : Blo 1313975 2218799 := bstep (se 1 (by rfl) ⟨1664099, by rfl⟩ : syracuseStep 2218799 = 3328199) B3328199
theorem B1973243 : Blo 1313975 1973243 := bstep (se 1 (by rfl) ⟨1479932, by rfl⟩ : syracuseStep 1973243 = 2959865) B2959865
theorem B1973279 : Blo 1313975 1973279 := bstep (se 1 (by rfl) ⟨1479959, by rfl⟩ : syracuseStep 1973279 = 2959919) B2959919
theorem B1973303 : Blo 1313975 1973303 := bstep (se 1 (by rfl) ⟨1479977, by rfl⟩ : syracuseStep 1973303 = 2959955) B2959955
theorem B2956463 : Blo 1313975 2956463 := bstep (se 1 (by rfl) ⟨2217347, by rfl⟩ : syracuseStep 2956463 = 4434695) B4434695
theorem B1973423 : Blo 1313975 1973423 := bstep (se 1 (by rfl) ⟨1480067, by rfl⟩ : syracuseStep 1973423 = 2960135) B2960135
theorem B2956607 : Blo 1313975 2956607 := bstep (se 1 (by rfl) ⟨2217455, by rfl⟩ : syracuseStep 2956607 = 4434911) B4434911
theorem B1973567 : Blo 1313975 1973567 := bstep (se 1 (by rfl) ⟨1480175, by rfl⟩ : syracuseStep 1973567 = 2960351) B2960351
theorem B5332351 : Blo 1313975 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B2956715 : Blo 1313975 2956715 := bstep (se 1 (by rfl) ⟨2217536, by rfl⟩ : syracuseStep 2956715 = 4435073) B4435073
theorem B388873649 : Blo 1313975 388873649 := bstep (se 2 (by rfl) ⟨145827618, by rfl⟩ : syracuseStep 388873649 = 291655237) B291655237
theorem B3743165 : Blo 1313975 3743165 := bstep (se 3 (by rfl) ⟨701843, by rfl⟩ : syracuseStep 3743165 = 1403687) B1403687
theorem B1973711 : Blo 1313975 1973711 := bstep (se 1 (by rfl) ⟨1480283, by rfl⟩ : syracuseStep 1973711 = 2960567) B2960567
theorem B7994875 : Blo 1313975 7994875 := bstep (se 1 (by rfl) ⟨5996156, by rfl⟩ : syracuseStep 7994875 = 11992313) B11992313
theorem B4439609 : Blo 1313975 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B4439771 : Blo 1313975 4439771 := bstep (se 1 (by rfl) ⟨3329828, by rfl⟩ : syracuseStep 4439771 = 6659657) B6659657
theorem B50585309 : Blo 1313975 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B16850699 : Blo 1313975 16850699 := bstep (se 1 (by rfl) ⟨12638024, by rfl⟩ : syracuseStep 16850699 = 25276049) B25276049
theorem B2957183 : Blo 1313975 2957183 := bstep (se 1 (by rfl) ⟨2217887, by rfl⟩ : syracuseStep 2957183 = 4435775) B4435775
theorem B2957255 : Blo 1313975 2957255 := bstep (se 1 (by rfl) ⟨2217941, by rfl⟩ : syracuseStep 2957255 = 4435883) B4435883
theorem B1663031 : Blo 1313975 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B2220527 : Blo 1313975 2220527 := bstep (se 1 (by rfl) ⟨1665395, by rfl⟩ : syracuseStep 2220527 = 3330791) B3330791
theorem B2220635 : Blo 1313975 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B2220655 : Blo 1313975 2220655 := bstep (se 1 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 2220655 = 3330983) B3330983
theorem B9986813 : Blo 1313975 9986813 := bstep (se 3 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 9986813 = 3745055) B3745055
theorem B3744737 : Blo 1313975 3744737 := bstep (se 2 (by rfl) ⟨1404276, by rfl⟩ : syracuseStep 3744737 = 2808553) B2808553
theorem B4441067 : Blo 1313975 4441067 := bstep (se 1 (by rfl) ⟨3330800, by rfl⟩ : syracuseStep 4441067 = 6661601) B6661601
theorem B12329999 : Blo 1313975 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B4441391 : Blo 1313975 4441391 := bstep (se 1 (by rfl) ⟨3331043, by rfl⟩ : syracuseStep 4441391 = 6662087) B6662087
theorem B7202465 : Blo 1313975 7202465 := bstep (se 2 (by rfl) ⟨2700924, by rfl⟩ : syracuseStep 7202465 = 5401849) B5401849
theorem B2959019 : Blo 1313975 2959019 := bstep (se 1 (by rfl) ⟨2219264, by rfl⟩ : syracuseStep 2959019 = 4438529) B4438529
theorem B3745511 : Blo 1313975 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B3327763 : Blo 1313975 3327763 := bstep (se 1 (by rfl) ⟨2495822, by rfl⟩ : syracuseStep 3327763 = 4991645) B4991645
theorem B3245915 : Blo 1313975 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B7112569 : Blo 1313975 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B3745693 : Blo 1313975 3745693 := bstep (se 3 (by rfl) ⟨702317, by rfl⟩ : syracuseStep 3745693 = 1404635) B1404635
theorem B10659833 : Blo 1313975 10659833 := bstep (se 2 (by rfl) ⟨3997437, by rfl⟩ : syracuseStep 10659833 = 7994875) B7994875
theorem B37898387 : Blo 1313975 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B12642637 : Blo 1313975 12642637 := bstep (se 3 (by rfl) ⟨2370494, by rfl⟩ : syracuseStep 12642637 = 4740989) B4740989
theorem B2959739 : Blo 1313975 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B2959847 : Blo 1313975 2959847 := bstep (se 1 (by rfl) ⟨2219885, by rfl⟩ : syracuseStep 2959847 = 4439771) B4439771
theorem B11233799 : Blo 1313975 11233799 := bstep (se 1 (by rfl) ⟨8425349, by rfl⟩ : syracuseStep 11233799 = 16850699) B16850699
theorem B9481055 : Blo 1313975 9481055 := bstep (se 1 (by rfl) ⟨7110791, by rfl⟩ : syracuseStep 9481055 = 14221583) B14221583
theorem B1403815 : Blo 1313975 1403815 := bstep (se 1 (by rfl) ⟨1052861, by rfl⟩ : syracuseStep 1403815 = 2105723) B2105723
theorem B1314207 : Blo 1313975 1314207 := bstep (se 1 (by rfl) ⟨985655, by rfl⟩ : syracuseStep 1314207 = 1971311) B1971311
theorem B1314255 : Blo 1313975 1314255 := bstep (se 1 (by rfl) ⟨985691, by rfl⟩ : syracuseStep 1314255 = 1971383) B1971383
theorem B4992617 : Blo 1313975 4992617 := bstep (se 2 (by rfl) ⟨1872231, by rfl⟩ : syracuseStep 4992617 = 3744463) B3744463
theorem B1314415 : Blo 1313975 1314415 := bstep (se 1 (by rfl) ⟨985811, by rfl⟩ : syracuseStep 1314415 = 1971623) B1971623
theorem B1314535 : Blo 1313975 1314535 := bstep (se 1 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 1314535 = 1971803) B1971803
theorem B4738799 : Blo 1313975 4738799 := bstep (se 1 (by rfl) ⟨3554099, by rfl⟩ : syracuseStep 4738799 = 7108199) B7108199
theorem B42643219 : Blo 1313975 42643219 := bstep (se 1 (by rfl) ⟨31982414, by rfl⟩ : syracuseStep 42643219 = 63964829) B63964829
theorem B6655769 : Blo 1313975 6655769 := bstep (se 2 (by rfl) ⟨2495913, by rfl⟩ : syracuseStep 6655769 = 4991827) B4991827
theorem B1315039 : Blo 1313975 1315039 := bstep (se 1 (by rfl) ⟨986279, by rfl⟩ : syracuseStep 1315039 = 1972559) B1972559
theorem B1315055 : Blo 1313975 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B1478911 : Blo 1313975 1478911 := bstep (se 1 (by rfl) ⟨1109183, by rfl⟩ : syracuseStep 1478911 = 2218367) B2218367
theorem B1315099 : Blo 1313975 1315099 := bstep (se 1 (by rfl) ⟨986324, by rfl⟩ : syracuseStep 1315099 = 1972649) B1972649
theorem B1872175 : Blo 1313975 1872175 := bstep (se 1 (by rfl) ⟨1404131, by rfl⟩ : syracuseStep 1872175 = 2808263) B2808263
theorem B11227511 : Blo 1313975 11227511 := bstep (se 1 (by rfl) ⟨8420633, by rfl⟩ : syracuseStep 11227511 = 16841267) B16841267
theorem B21336527 : Blo 1313975 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B1315355 : Blo 1313975 1315355 := bstep (se 1 (by rfl) ⟨986516, by rfl⟩ : syracuseStep 1315355 = 1973033) B1973033
theorem B1479199 : Blo 1313975 1479199 := bstep (se 1 (by rfl) ⟨1109399, by rfl⟩ : syracuseStep 1479199 = 2218799) B2218799
theorem B1315495 : Blo 1313975 1315495 := bstep (se 1 (by rfl) ⟨986621, by rfl⟩ : syracuseStep 1315495 = 1973243) B1973243
theorem B1315519 : Blo 1313975 1315519 := bstep (se 1 (by rfl) ⟨986639, by rfl⟩ : syracuseStep 1315519 = 1973279) B1973279
theorem B1315535 : Blo 1313975 1315535 := bstep (se 1 (by rfl) ⟨986651, by rfl⟩ : syracuseStep 1315535 = 1973303) B1973303
theorem B1970975 : Blo 1313975 1970975 := bstep (se 1 (by rfl) ⟨1478231, by rfl⟩ : syracuseStep 1970975 = 2956463) B2956463
theorem B1315615 : Blo 1313975 1315615 := bstep (se 1 (by rfl) ⟨986711, by rfl⟩ : syracuseStep 1315615 = 1973423) B1973423
theorem B1971071 : Blo 1313975 1971071 := bstep (se 1 (by rfl) ⟨1478303, by rfl⟩ : syracuseStep 1971071 = 2956607) B2956607
theorem B1315711 : Blo 1313975 1315711 := bstep (se 1 (by rfl) ⟨986783, by rfl⟩ : syracuseStep 1315711 = 1973567) B1973567
theorem B1971143 : Blo 1313975 1971143 := bstep (se 1 (by rfl) ⟨1478357, by rfl⟩ : syracuseStep 1971143 = 2956715) B2956715
theorem B259249099 : Blo 1313975 259249099 := bstep (se 1 (by rfl) ⟨194436824, by rfl⟩ : syracuseStep 259249099 = 388873649) B388873649
theorem B2495443 : Blo 1313975 2495443 := bstep (se 1 (by rfl) ⟨1871582, by rfl⟩ : syracuseStep 2495443 = 3743165) B3743165
theorem B1315807 : Blo 1313975 1315807 := bstep (se 1 (by rfl) ⟨986855, by rfl⟩ : syracuseStep 1315807 = 1973711) B1973711
theorem B4994075 : Blo 1313975 4994075 := bstep (se 1 (by rfl) ⟨3745556, by rfl⟩ : syracuseStep 4994075 = 7491113) B7491113
theorem B33723539 : Blo 1313975 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B1971455 : Blo 1313975 1971455 := bstep (se 1 (by rfl) ⟨1478591, by rfl⟩ : syracuseStep 1971455 = 2957183) B2957183
theorem B1971503 : Blo 1313975 1971503 := bstep (se 1 (by rfl) ⟨1478627, by rfl⟩ : syracuseStep 1971503 = 2957255) B2957255
theorem B1480063 : Blo 1313975 1480063 := bstep (se 1 (by rfl) ⟨1110047, by rfl⟩ : syracuseStep 1480063 = 2220095) B2220095
theorem B2217503 : Blo 1313975 2217503 := bstep (se 1 (by rfl) ⟨1663127, by rfl⟩ : syracuseStep 2217503 = 3326255) B3326255
theorem B1971743 : Blo 1313975 1971743 := bstep (se 1 (by rfl) ⟨1478807, by rfl⟩ : syracuseStep 1971743 = 2957615) B2957615
theorem B23975513 : Blo 1313975 23975513 := bstep (se 2 (by rfl) ⟨8990817, by rfl⟩ : syracuseStep 23975513 = 17981635) B17981635
theorem B7493255 : Blo 1313975 7493255 := bstep (se 1 (by rfl) ⟨5619941, by rfl⟩ : syracuseStep 7493255 = 11239883) B11239883
theorem B9000667 : Blo 1313975 9000667 := bstep (se 1 (by rfl) ⟨6750500, by rfl⟩ : syracuseStep 9000667 = 13501001) B13501001
theorem B4995017 : Blo 1313975 4995017 := bstep (se 2 (by rfl) ⟨1873131, by rfl⟩ : syracuseStep 4995017 = 3746263) B3746263
theorem B2496575 : Blo 1313975 2496575 := bstep (se 1 (by rfl) ⟨1872431, by rfl⟩ : syracuseStep 2496575 = 3744863) B3744863
theorem B1972295 : Blo 1313975 1972295 := bstep (se 1 (by rfl) ⟨1479221, by rfl⟩ : syracuseStep 1972295 = 2958443) B2958443
theorem B6658361 : Blo 1313975 6658361 := bstep (se 2 (by rfl) ⟨2496885, by rfl⟩ : syracuseStep 6658361 = 4993771) B4993771
theorem B4438367 : Blo 1313975 4438367 := bstep (se 1 (by rfl) ⟨3328775, by rfl⟩ : syracuseStep 4438367 = 6657551) B6657551
theorem B3742139 : Blo 1313975 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B2218475 : Blo 1313975 2218475 := bstep (se 1 (by rfl) ⟨1663856, by rfl⟩ : syracuseStep 2218475 = 3327713) B3327713
theorem B38943353 : Blo 1313975 38943353 := bstep (se 2 (by rfl) ⟨14603757, by rfl⟩ : syracuseStep 38943353 = 29207515) B29207515
theorem B1972895 : Blo 1313975 1972895 := bstep (se 1 (by rfl) ⟨1479671, by rfl⟩ : syracuseStep 1972895 = 2959343) B2959343
theorem B8002367 : Blo 1313975 8002367 := bstep (se 1 (by rfl) ⟨6001775, by rfl⟩ : syracuseStep 8002367 = 12003551) B12003551
theorem B2219035 : Blo 1313975 2219035 := bstep (se 1 (by rfl) ⟨1664276, by rfl⟩ : syracuseStep 2219035 = 3328553) B3328553
theorem B7109801 : Blo 1313975 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B8994017 : Blo 1313975 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B2956571 : Blo 1313975 2956571 := bstep (se 1 (by rfl) ⟨2217428, by rfl⟩ : syracuseStep 2956571 = 4434857) B4434857
theorem B2809151 : Blo 1313975 2809151 := bstep (se 1 (by rfl) ⟨2106863, by rfl⟩ : syracuseStep 2809151 = 4213727) B4213727
theorem B2956769 : Blo 1313975 2956769 := bstep (se 2 (by rfl) ⟨1108788, by rfl⟩ : syracuseStep 2956769 = 2217577) B2217577
theorem B1973831 : Blo 1313975 1973831 := bstep (se 1 (by rfl) ⟨1480373, by rfl⟩ : syracuseStep 1973831 = 2960747) B2960747
theorem B51920561 : Blo 1313975 51920561 := bstep (se 2 (by rfl) ⟨19470210, by rfl⟩ : syracuseStep 51920561 = 38940421) B38940421
theorem B6315707 : Blo 1313975 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B4440041 : Blo 1313975 4440041 := bstep (se 2 (by rfl) ⟨1665015, by rfl⟩ : syracuseStep 4440041 = 3330031) B3330031
theorem B15983675 : Blo 1313975 15983675 := bstep (se 1 (by rfl) ⟨11987756, by rfl⟩ : syracuseStep 15983675 = 23975513) B23975513
theorem B4801643 : Blo 1313975 4801643 := bstep (se 1 (by rfl) ⟨3601232, by rfl⟩ : syracuseStep 4801643 = 7202465) B7202465
theorem B9979037 : Blo 1313975 9979037 := bstep (se 3 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 9979037 = 3742139) B3742139
theorem B2163943 : Blo 1313975 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B3327257 : Blo 1313975 3327257 := bstep (se 2 (by rfl) ⟨1247721, by rfl⟩ : syracuseStep 3327257 = 2495443) B2495443
theorem B2958713 : Blo 1313975 2958713 := bstep (se 2 (by rfl) ⟨1109517, by rfl⟩ : syracuseStep 2958713 = 2219035) B2219035
theorem B1664383 : Blo 1313975 1664383 := bstep (se 1 (by rfl) ⟨1248287, by rfl⟩ : syracuseStep 1664383 = 2496575) B2496575
theorem B25265591 : Blo 1313975 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B2958911 : Blo 1313975 2958911 := bstep (se 1 (by rfl) ⟨2219183, by rfl⟩ : syracuseStep 2958911 = 4438367) B4438367
theorem B7489199 : Blo 1313975 7489199 := bstep (se 1 (by rfl) ⟨5616899, by rfl⟩ : syracuseStep 7489199 = 11233799) B11233799
theorem B138454829 : Blo 1313975 138454829 := bstep (se 3 (by rfl) ⟨25960280, by rfl⟩ : syracuseStep 138454829 = 51920561) B51920561
theorem B5334911 : Blo 1313975 5334911 := bstep (se 1 (by rfl) ⟨4001183, by rfl⟩ : syracuseStep 5334911 = 8002367) B8002367
theorem B25282813 : Blo 1313975 25282813 := bstep (se 3 (by rfl) ⟨4740527, by rfl⟩ : syracuseStep 25282813 = 9481055) B9481055
theorem B3328411 : Blo 1313975 3328411 := bstep (se 1 (by rfl) ⟨2496308, by rfl⟩ : syracuseStep 3328411 = 4992617) B4992617
theorem B2960027 : Blo 1313975 2960027 := bstep (se 1 (by rfl) ⟨2220020, by rfl⟩ : syracuseStep 2960027 = 4440041) B4440041
theorem B4434749 : Blo 1313975 4434749 := bstep (se 3 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 4434749 = 1663031) B1663031
theorem B14224351 : Blo 1313975 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B1313983 : Blo 1313975 1313983 := bstep (se 1 (by rfl) ⟨985487, by rfl⟩ : syracuseStep 1313983 = 1970975) B1970975
theorem B1314047 : Blo 1313975 1314047 := bstep (se 1 (by rfl) ⟨985535, by rfl⟩ : syracuseStep 1314047 = 1971071) B1971071
theorem B1314095 : Blo 1313975 1314095 := bstep (se 1 (by rfl) ⟨985571, by rfl⟩ : syracuseStep 1314095 = 1971143) B1971143
theorem B2960711 : Blo 1313975 2960711 := bstep (se 1 (by rfl) ⟨2220533, by rfl⟩ : syracuseStep 2960711 = 4441067) B4441067
theorem B8219999 : Blo 1313975 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B3329383 : Blo 1313975 3329383 := bstep (se 1 (by rfl) ⟨2497037, by rfl⟩ : syracuseStep 3329383 = 4994075) B4994075
theorem B22482359 : Blo 1313975 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B2960873 : Blo 1313975 2960873 := bstep (se 2 (by rfl) ⟨1110327, by rfl⟩ : syracuseStep 2960873 = 2220655) B2220655
theorem B1314303 : Blo 1313975 1314303 := bstep (se 1 (by rfl) ⟨985727, by rfl⟩ : syracuseStep 1314303 = 1971455) B1971455
theorem B1314335 : Blo 1313975 1314335 := bstep (se 1 (by rfl) ⟨985751, by rfl⟩ : syracuseStep 1314335 = 1971503) B1971503
theorem B2960927 : Blo 1313975 2960927 := bstep (se 1 (by rfl) ⟨2220695, by rfl⟩ : syracuseStep 2960927 = 4441391) B4441391
theorem B1478335 : Blo 1313975 1478335 := bstep (se 1 (by rfl) ⟨1108751, by rfl⟩ : syracuseStep 1478335 = 2217503) B2217503
theorem B1314495 : Blo 1313975 1314495 := bstep (se 1 (by rfl) ⟨985871, by rfl⟩ : syracuseStep 1314495 = 1971743) B1971743
theorem B1871753 : Blo 1313975 1871753 := bstep (se 2 (by rfl) ⟨701907, by rfl⟩ : syracuseStep 1871753 = 1403815) B1403815
theorem B345665465 : Blo 1313975 345665465 := bstep (se 2 (by rfl) ⟨129624549, by rfl⟩ : syracuseStep 345665465 = 259249099) B259249099
theorem B3330011 : Blo 1313975 3330011 := bstep (se 1 (by rfl) ⟨2497508, by rfl⟩ : syracuseStep 3330011 = 4995017) B4995017
theorem B7106555 : Blo 1313975 7106555 := bstep (se 1 (by rfl) ⟨5329916, by rfl⟩ : syracuseStep 7106555 = 10659833) B10659833
theorem B1314863 : Blo 1313975 1314863 := bstep (se 1 (by rfl) ⟨986147, by rfl⟩ : syracuseStep 1314863 = 1972295) B1972295
theorem B1478983 : Blo 1313975 1478983 := bstep (se 1 (by rfl) ⟨1109237, by rfl⟩ : syracuseStep 1478983 = 2218475) B2218475
theorem B1315263 : Blo 1313975 1315263 := bstep (se 1 (by rfl) ⟨986447, by rfl⟩ : syracuseStep 1315263 = 1972895) B1972895
theorem B4739867 : Blo 1313975 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B1971047 : Blo 1313975 1971047 := bstep (se 1 (by rfl) ⟨1478285, by rfl⟩ : syracuseStep 1971047 = 2956571) B2956571
theorem B1872767 : Blo 1313975 1872767 := bstep (se 1 (by rfl) ⟨1404575, by rfl⟩ : syracuseStep 1872767 = 2809151) B2809151
theorem B1971179 : Blo 1313975 1971179 := bstep (se 1 (by rfl) ⟨1478384, by rfl⟩ : syracuseStep 1971179 = 2956769) B2956769
theorem B56857625 : Blo 1313975 56857625 := bstep (se 2 (by rfl) ⟨21321609, by rfl⟩ : syracuseStep 56857625 = 42643219) B42643219
theorem B4437017 : Blo 1313975 4437017 := bstep (se 2 (by rfl) ⟨1663881, by rfl⟩ : syracuseStep 4437017 = 3327763) B3327763
theorem B1315887 : Blo 1313975 1315887 := bstep (se 1 (by rfl) ⟨986915, by rfl⟩ : syracuseStep 1315887 = 1973831) B1973831
theorem B3159199 : Blo 1313975 3159199 := bstep (se 1 (by rfl) ⟨2369399, by rfl⟩ : syracuseStep 3159199 = 4738799) B4738799
theorem B9483425 : Blo 1313975 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B4437179 : Blo 1313975 4437179 := bstep (se 1 (by rfl) ⟨3327884, by rfl⟩ : syracuseStep 4437179 = 6655769) B6655769
theorem B4994257 : Blo 1313975 4994257 := bstep (se 2 (by rfl) ⟨1872846, by rfl⟩ : syracuseStep 4994257 = 3745693) B3745693
theorem B7485007 : Blo 1313975 7485007 := bstep (se 1 (by rfl) ⟨5613755, by rfl⟩ : syracuseStep 7485007 = 11227511) B11227511
theorem B1480351 : Blo 1313975 1480351 := bstep (se 1 (by rfl) ⟨1110263, by rfl⟩ : syracuseStep 1480351 = 2220527) B2220527
theorem B1971881 : Blo 1313975 1971881 := bstep (se 2 (by rfl) ⟨739455, by rfl⟩ : syracuseStep 1971881 = 1478911) B1478911
theorem B1480423 : Blo 1313975 1480423 := bstep (se 1 (by rfl) ⟨1110317, by rfl⟩ : syracuseStep 1480423 = 2220635) B2220635
theorem B2496233 : Blo 1313975 2496233 := bstep (se 2 (by rfl) ⟨936087, by rfl⟩ : syracuseStep 2496233 = 1872175) B1872175
theorem B16856849 : Blo 1313975 16856849 := bstep (se 2 (by rfl) ⟨6321318, by rfl⟩ : syracuseStep 16856849 = 12642637) B12642637
theorem B6657875 : Blo 1313975 6657875 := bstep (se 1 (by rfl) ⟨4993406, by rfl⟩ : syracuseStep 6657875 = 9986813) B9986813
theorem B23984045 : Blo 1313975 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B2496491 : Blo 1313975 2496491 := bstep (se 1 (by rfl) ⟨1872368, by rfl⟩ : syracuseStep 2496491 = 3744737) B3744737
theorem B1972265 : Blo 1313975 1972265 := bstep (se 2 (by rfl) ⟨739599, by rfl⟩ : syracuseStep 1972265 = 1479199) B1479199
theorem B4995503 : Blo 1313975 4995503 := bstep (se 1 (by rfl) ⟨3746627, by rfl⟩ : syracuseStep 4995503 = 7493255) B7493255
theorem B1972679 : Blo 1313975 1972679 := bstep (se 1 (by rfl) ⟨1479509, by rfl⟩ : syracuseStep 1972679 = 2959019) B2959019
theorem B2497007 : Blo 1313975 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B4438907 : Blo 1313975 4438907 := bstep (se 1 (by rfl) ⟨3329180, by rfl⟩ : syracuseStep 4438907 = 6658361) B6658361
theorem B1973159 : Blo 1313975 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B103848941 : Blo 1313975 103848941 := bstep (se 3 (by rfl) ⟨19471676, by rfl⟩ : syracuseStep 103848941 = 38943353) B38943353
theorem B1973231 : Blo 1313975 1973231 := bstep (se 1 (by rfl) ⟨1479923, by rfl⟩ : syracuseStep 1973231 = 2959847) B2959847
theorem B1973417 : Blo 1313975 1973417 := bstep (se 2 (by rfl) ⟨740031, by rfl⟩ : syracuseStep 1973417 = 1480063) B1480063
theorem B12000889 : Blo 1313975 12000889 := bstep (se 2 (by rfl) ⟨4500333, by rfl⟩ : syracuseStep 12000889 = 9000667) B9000667
theorem B4210471 : Blo 1313975 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B33710417 : Blo 1313975 33710417 := bstep (se 2 (by rfl) ⟨12641406, by rfl⟩ : syracuseStep 33710417 = 25282813) B25282813
theorem B64004741 : Blo 1313975 64004741 := bstep (se 4 (by rfl) ⟨6000444, by rfl⟩ : syracuseStep 64004741 = 12000889) B12000889
theorem B37905083 : Blo 1313975 37905083 := bstep (se 1 (by rfl) ⟨28428812, by rfl⟩ : syracuseStep 37905083 = 56857625) B56857625
theorem B2958011 : Blo 1313975 2958011 := bstep (se 1 (by rfl) ⟨2218508, by rfl⟩ : syracuseStep 2958011 = 4437017) B4437017
theorem B6652691 : Blo 1313975 6652691 := bstep (se 1 (by rfl) ⟨4989518, by rfl⟩ : syracuseStep 6652691 = 9979037) B9979037
theorem B2958119 : Blo 1313975 2958119 := bstep (se 1 (by rfl) ⟨2218589, by rfl⟩ : syracuseStep 2958119 = 4437179) B4437179
theorem B16843727 : Blo 1313975 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B1664155 : Blo 1313975 1664155 := bstep (se 1 (by rfl) ⟨1248116, by rfl⟩ : syracuseStep 1664155 = 2496233) B2496233
theorem B3556607 : Blo 1313975 3556607 := bstep (se 1 (by rfl) ⟨2667455, by rfl⟩ : syracuseStep 3556607 = 5334911) B5334911
theorem B18965801 : Blo 1313975 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B1664327 : Blo 1313975 1664327 := bstep (se 1 (by rfl) ⟨1248245, by rfl⟩ : syracuseStep 1664327 = 2496491) B2496491
theorem B4212265 : Blo 1313975 4212265 := bstep (se 2 (by rfl) ⟨1579599, by rfl⟩ : syracuseStep 4212265 = 3159199) B3159199
theorem B2885257 : Blo 1313975 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B2959271 : Blo 1313975 2959271 := bstep (se 1 (by rfl) ⟨2219453, by rfl⟩ : syracuseStep 2959271 = 4438907) B4438907
theorem B69232627 : Blo 1313975 69232627 := bstep (se 1 (by rfl) ⟨51924470, by rfl⟩ : syracuseStep 69232627 = 103848941) B103848941
theorem B9980009 : Blo 1313975 9980009 := bstep (se 2 (by rfl) ⟨3742503, by rfl⟩ : syracuseStep 9980009 = 7485007) B7485007
theorem B4991341 : Blo 1313975 4991341 := bstep (se 3 (by rfl) ⟨935876, by rfl⟩ : syracuseStep 4991341 = 1871753) B1871753
theorem B5613961 : Blo 1313975 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B230443643 : Blo 1313975 230443643 := bstep (se 1 (by rfl) ⟨172832732, by rfl⟩ : syracuseStep 230443643 = 345665465) B345665465
theorem B4737703 : Blo 1313975 4737703 := bstep (se 1 (by rfl) ⟨3553277, by rfl⟩ : syracuseStep 4737703 = 7106555) B7106555
theorem B1314031 : Blo 1313975 1314031 := bstep (se 1 (by rfl) ⟨985523, by rfl⟩ : syracuseStep 1314031 = 1971047) B1971047
theorem B1314119 : Blo 1313975 1314119 := bstep (se 1 (by rfl) ⟨985589, by rfl⟩ : syracuseStep 1314119 = 1971179) B1971179
theorem B1314587 : Blo 1313975 1314587 := bstep (se 1 (by rfl) ⟨985940, by rfl⟩ : syracuseStep 1314587 = 1971881) B1971881
theorem B4992799 : Blo 1313975 4992799 := bstep (se 1 (by rfl) ⟨3744599, by rfl⟩ : syracuseStep 4992799 = 7489199) B7489199
theorem B92303219 : Blo 1313975 92303219 := bstep (se 1 (by rfl) ⟨69227414, by rfl⟩ : syracuseStep 92303219 = 138454829) B138454829
theorem B1314843 : Blo 1313975 1314843 := bstep (se 1 (by rfl) ⟨986132, by rfl⟩ : syracuseStep 1314843 = 1972265) B1972265
theorem B3330335 : Blo 1313975 3330335 := bstep (se 1 (by rfl) ⟨2497751, by rfl⟩ : syracuseStep 3330335 = 4995503) B4995503
theorem B1315119 : Blo 1313975 1315119 := bstep (se 1 (by rfl) ⟨986339, by rfl⟩ : syracuseStep 1315119 = 1972679) B1972679
theorem B1315439 : Blo 1313975 1315439 := bstep (se 1 (by rfl) ⟨986579, by rfl⟩ : syracuseStep 1315439 = 1973159) B1973159
theorem B1315487 : Blo 1313975 1315487 := bstep (se 1 (by rfl) ⟨986615, by rfl⟩ : syracuseStep 1315487 = 1973231) B1973231
theorem B1315611 : Blo 1313975 1315611 := bstep (se 1 (by rfl) ⟨986708, by rfl⟩ : syracuseStep 1315611 = 1973417) B1973417
theorem B1971113 : Blo 1313975 1971113 := bstep (se 2 (by rfl) ⟨739167, by rfl⟩ : syracuseStep 1971113 = 1478335) B1478335
theorem B14988239 : Blo 1313975 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B4994045 : Blo 1313975 4994045 := bstep (se 3 (by rfl) ⟨936383, by rfl⟩ : syracuseStep 4994045 = 1872767) B1872767
theorem B1971977 : Blo 1313975 1971977 := bstep (se 2 (by rfl) ⟨739491, by rfl⟩ : syracuseStep 1971977 = 1478983) B1478983
theorem B3159911 : Blo 1313975 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B4437881 : Blo 1313975 4437881 := bstep (se 2 (by rfl) ⟨1664205, by rfl⟩ : syracuseStep 4437881 = 3328411) B3328411
theorem B10655783 : Blo 1313975 10655783 := bstep (se 1 (by rfl) ⟨7991837, by rfl⟩ : syracuseStep 10655783 = 15983675) B15983675
theorem B3201095 : Blo 1313975 3201095 := bstep (se 1 (by rfl) ⟨2400821, by rfl⟩ : syracuseStep 3201095 = 4801643) B4801643
theorem B6322283 : Blo 1313975 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B2218171 : Blo 1313975 2218171 := bstep (se 1 (by rfl) ⟨1663628, by rfl⟩ : syracuseStep 2218171 = 3327257) B3327257
theorem B1972475 : Blo 1313975 1972475 := bstep (se 1 (by rfl) ⟨1479356, by rfl⟩ : syracuseStep 1972475 = 2958713) B2958713
theorem B21919997 : Blo 1313975 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B1972607 : Blo 1313975 1972607 := bstep (se 1 (by rfl) ⟨1479455, by rfl⟩ : syracuseStep 1972607 = 2958911) B2958911
theorem B11237899 : Blo 1313975 11237899 := bstep (se 1 (by rfl) ⟨8428424, by rfl⟩ : syracuseStep 11237899 = 16856849) B16856849
theorem B4438583 : Blo 1313975 4438583 := bstep (se 1 (by rfl) ⟨3328937, by rfl⟩ : syracuseStep 4438583 = 6657875) B6657875
theorem B15989363 : Blo 1313975 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B6658685 : Blo 1313975 6658685 := bstep (se 3 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 6658685 = 2497007) B2497007
theorem B6659009 : Blo 1313975 6659009 := bstep (se 2 (by rfl) ⟨2497128, by rfl⟩ : syracuseStep 6659009 = 4994257) B4994257
theorem B1973351 : Blo 1313975 1973351 := bstep (se 1 (by rfl) ⟨1480013, by rfl⟩ : syracuseStep 1973351 = 2960027) B2960027
theorem B4439177 : Blo 1313975 4439177 := bstep (se 2 (by rfl) ⟨1664691, by rfl⟩ : syracuseStep 4439177 = 3329383) B3329383
theorem B2219177 : Blo 1313975 2219177 := bstep (se 2 (by rfl) ⟨832191, by rfl⟩ : syracuseStep 2219177 = 1664383) B1664383
theorem B2956499 : Blo 1313975 2956499 := bstep (se 1 (by rfl) ⟨2217374, by rfl⟩ : syracuseStep 2956499 = 4434749) B4434749
theorem B1973801 : Blo 1313975 1973801 := bstep (se 2 (by rfl) ⟨740175, by rfl⟩ : syracuseStep 1973801 = 1480351) B1480351
theorem B1973807 : Blo 1313975 1973807 := bstep (se 1 (by rfl) ⟨1480355, by rfl⟩ : syracuseStep 1973807 = 2960711) B2960711
theorem B1973897 : Blo 1313975 1973897 := bstep (se 2 (by rfl) ⟨740211, by rfl⟩ : syracuseStep 1973897 = 1480423) B1480423
theorem B1973915 : Blo 1313975 1973915 := bstep (se 1 (by rfl) ⟨1480436, by rfl⟩ : syracuseStep 1973915 = 2960873) B2960873
theorem B1973951 : Blo 1313975 1973951 := bstep (se 1 (by rfl) ⟨1480463, by rfl⟩ : syracuseStep 1973951 = 2960927) B2960927
theorem B2220007 : Blo 1313975 2220007 := bstep (se 1 (by rfl) ⟨1665005, by rfl⟩ : syracuseStep 2220007 = 3330011) B3330011
theorem B2220223 : Blo 1313975 2220223 := bstep (se 1 (by rfl) ⟨1665167, by rfl⟩ : syracuseStep 2220223 = 3330335) B3330335
theorem B2957561 : Blo 1313975 2957561 := bstep (se 2 (by rfl) ⟨1109085, by rfl⟩ : syracuseStep 2957561 = 2218171) B2218171
theorem B14983865 : Blo 1313975 14983865 := bstep (se 2 (by rfl) ⟨5618949, by rfl⟩ : syracuseStep 14983865 = 11237899) B11237899
theorem B6316937 : Blo 1313975 6316937 := bstep (se 2 (by rfl) ⟨2368851, by rfl⟩ : syracuseStep 6316937 = 4737703) B4737703
theorem B2958587 : Blo 1313975 2958587 := bstep (se 1 (by rfl) ⟨2218940, by rfl⟩ : syracuseStep 2958587 = 4437881) B4437881
theorem B7103855 : Blo 1313975 7103855 := bstep (se 1 (by rfl) ⟨5327891, by rfl⟩ : syracuseStep 7103855 = 10655783) B10655783
theorem B6653339 : Blo 1313975 6653339 := bstep (se 1 (by rfl) ⟨4990004, by rfl⟩ : syracuseStep 6653339 = 9980009) B9980009
theorem B614516381 : Blo 1313975 614516381 := bstep (se 3 (by rfl) ⟨115221821, by rfl⟩ : syracuseStep 614516381 = 230443643) B230443643
theorem B2959055 : Blo 1313975 2959055 := bstep (se 1 (by rfl) ⟨2219291, by rfl⟩ : syracuseStep 2959055 = 4438583) B4438583
theorem B10659575 : Blo 1313975 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B2959451 : Blo 1313975 2959451 := bstep (se 1 (by rfl) ⟨2219588, by rfl⟩ : syracuseStep 2959451 = 4439177) B4439177
theorem B369240677 : Blo 1313975 369240677 := bstep (se 4 (by rfl) ⟨34616313, by rfl⟩ : syracuseStep 369240677 = 69232627) B69232627
theorem B2960009 : Blo 1313975 2960009 := bstep (se 2 (by rfl) ⟨1110003, by rfl⟩ : syracuseStep 2960009 = 2220007) B2220007
theorem B22473611 : Blo 1313975 22473611 := bstep (se 1 (by rfl) ⟨16855208, by rfl⟩ : syracuseStep 22473611 = 33710417) B33710417
theorem B6655121 : Blo 1313975 6655121 := bstep (se 2 (by rfl) ⟨2495670, by rfl⟩ : syracuseStep 6655121 = 4991341) B4991341
theorem B4435127 : Blo 1313975 4435127 := bstep (se 1 (by rfl) ⟨3326345, by rfl⟩ : syracuseStep 4435127 = 6652691) B6652691
theorem B1314075 : Blo 1313975 1314075 := bstep (se 1 (by rfl) ⟨985556, by rfl⟩ : syracuseStep 1314075 = 1971113) B1971113
theorem B58453325 : Blo 1313975 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B3329363 : Blo 1313975 3329363 := bstep (se 1 (by rfl) ⟨2497022, by rfl⟩ : syracuseStep 3329363 = 4994045) B4994045
theorem B12643867 : Blo 1313975 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B1314651 : Blo 1313975 1314651 := bstep (se 1 (by rfl) ⟨985988, by rfl⟩ : syracuseStep 1314651 = 1971977) B1971977
theorem B2134063 : Blo 1313975 2134063 := bstep (se 1 (by rfl) ⟨1600547, by rfl⟩ : syracuseStep 2134063 = 3201095) B3201095
theorem B4214855 : Blo 1313975 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B1314983 : Blo 1313975 1314983 := bstep (se 1 (by rfl) ⟨986237, by rfl⟩ : syracuseStep 1314983 = 1972475) B1972475
theorem B1315071 : Blo 1313975 1315071 := bstep (se 1 (by rfl) ⟨986303, by rfl⟩ : syracuseStep 1315071 = 1972607) B1972607
theorem B5616353 : Blo 1313975 5616353 := bstep (se 2 (by rfl) ⟨2106132, by rfl⟩ : syracuseStep 5616353 = 4212265) B4212265
theorem B1315567 : Blo 1313975 1315567 := bstep (se 1 (by rfl) ⟨986675, by rfl⟩ : syracuseStep 1315567 = 1973351) B1973351
theorem B1479451 : Blo 1313975 1479451 := bstep (se 1 (by rfl) ⟨1109588, by rfl⟩ : syracuseStep 1479451 = 2219177) B2219177
theorem B1970999 : Blo 1313975 1970999 := bstep (se 1 (by rfl) ⟨1478249, by rfl⟩ : syracuseStep 1970999 = 2956499) B2956499
theorem B3847009 : Blo 1313975 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B8426429 : Blo 1313975 8426429 := bstep (se 3 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 8426429 = 3159911) B3159911
theorem B1315867 : Blo 1313975 1315867 := bstep (se 1 (by rfl) ⟨986900, by rfl⟩ : syracuseStep 1315867 = 1973801) B1973801
theorem B1315871 : Blo 1313975 1315871 := bstep (se 1 (by rfl) ⟨986903, by rfl⟩ : syracuseStep 1315871 = 1973807) B1973807
theorem B6657065 : Blo 1313975 6657065 := bstep (se 2 (by rfl) ⟨2496399, by rfl⟩ : syracuseStep 6657065 = 4992799) B4992799
theorem B1315931 : Blo 1313975 1315931 := bstep (se 1 (by rfl) ⟨986948, by rfl⟩ : syracuseStep 1315931 = 1973897) B1973897
theorem B1315943 : Blo 1313975 1315943 := bstep (se 1 (by rfl) ⟨986957, by rfl⟩ : syracuseStep 1315943 = 1973915) B1973915
theorem B1315967 : Blo 1313975 1315967 := bstep (se 1 (by rfl) ⟨986975, by rfl⟩ : syracuseStep 1315967 = 1973951) B1973951
theorem B61535479 : Blo 1313975 61535479 := bstep (se 1 (by rfl) ⟨46151609, by rfl⟩ : syracuseStep 61535479 = 92303219) B92303219
theorem B42669827 : Blo 1313975 42669827 := bstep (se 1 (by rfl) ⟨32002370, by rfl⟩ : syracuseStep 42669827 = 64004741) B64004741
theorem B25270055 : Blo 1313975 25270055 := bstep (se 1 (by rfl) ⟨18952541, by rfl⟩ : syracuseStep 25270055 = 37905083) B37905083
theorem B1972007 : Blo 1313975 1972007 := bstep (se 1 (by rfl) ⟨1479005, by rfl⟩ : syracuseStep 1972007 = 2958011) B2958011
theorem B7485281 : Blo 1313975 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B1972079 : Blo 1313975 1972079 := bstep (se 1 (by rfl) ⟨1479059, by rfl⟩ : syracuseStep 1972079 = 2958119) B2958119
theorem B11229151 : Blo 1313975 11229151 := bstep (se 1 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 11229151 = 16843727) B16843727
theorem B9992159 : Blo 1313975 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B9484285 : Blo 1313975 9484285 := bstep (se 3 (by rfl) ⟨1778303, by rfl⟩ : syracuseStep 9484285 = 3556607) B3556607
theorem B4438205 : Blo 1313975 4438205 := bstep (se 3 (by rfl) ⟨832163, by rfl⟩ : syracuseStep 4438205 = 1664327) B1664327
theorem B1972847 : Blo 1313975 1972847 := bstep (se 1 (by rfl) ⟨1479635, by rfl⟩ : syracuseStep 1972847 = 2959271) B2959271
theorem B2218873 : Blo 1313975 2218873 := bstep (se 2 (by rfl) ⟨832077, by rfl⟩ : syracuseStep 2218873 = 1664155) B1664155
theorem B4439123 : Blo 1313975 4439123 := bstep (se 1 (by rfl) ⟨3329342, by rfl⟩ : syracuseStep 4439123 = 6658685) B6658685
theorem B4439339 : Blo 1313975 4439339 := bstep (se 1 (by rfl) ⟨3329504, by rfl⟩ : syracuseStep 4439339 = 6659009) B6659009
theorem B2809903 : Blo 1313975 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B3744235 : Blo 1313975 3744235 := bstep (se 1 (by rfl) ⟨2808176, by rfl⟩ : syracuseStep 3744235 = 5616353) B5616353
theorem B4211291 : Blo 1313975 4211291 := bstep (se 1 (by rfl) ⟨3158468, by rfl⟩ : syracuseStep 4211291 = 6316937) B6316937
theorem B4735903 : Blo 1313975 4735903 := bstep (se 1 (by rfl) ⟨3551927, by rfl⟩ : syracuseStep 4735903 = 7103855) B7103855
theorem B5129345 : Blo 1313975 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B2958497 : Blo 1313975 2958497 := bstep (se 2 (by rfl) ⟨1109436, by rfl⟩ : syracuseStep 2958497 = 2218873) B2218873
theorem B4990187 : Blo 1313975 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B6661439 : Blo 1313975 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B2958803 : Blo 1313975 2958803 := bstep (se 1 (by rfl) ⟨2219102, by rfl⟩ : syracuseStep 2958803 = 4438205) B4438205
theorem B2959415 : Blo 1313975 2959415 := bstep (se 1 (by rfl) ⟨2219561, by rfl⟩ : syracuseStep 2959415 = 4439123) B4439123
theorem B2959559 : Blo 1313975 2959559 := bstep (se 1 (by rfl) ⟨2219669, by rfl⟩ : syracuseStep 2959559 = 4439339) B4439339
theorem B2845417 : Blo 1313975 2845417 := bstep (se 2 (by rfl) ⟨1067031, by rfl⟩ : syracuseStep 2845417 = 2134063) B2134063
theorem B2960297 : Blo 1313975 2960297 := bstep (se 2 (by rfl) ⟨1110111, by rfl⟩ : syracuseStep 2960297 = 2220223) B2220223
theorem B9989243 : Blo 1313975 9989243 := bstep (se 1 (by rfl) ⟨7491932, by rfl⟩ : syracuseStep 9989243 = 14983865) B14983865
theorem B1313999 : Blo 1313975 1313999 := bstep (se 1 (by rfl) ⟨985499, by rfl⟩ : syracuseStep 1313999 = 1970999) B1970999
theorem B4435559 : Blo 1313975 4435559 := bstep (se 1 (by rfl) ⟨3326669, by rfl⟩ : syracuseStep 4435559 = 6653339) B6653339
theorem B409677587 : Blo 1313975 409677587 := bstep (se 1 (by rfl) ⟨307258190, by rfl⟩ : syracuseStep 409677587 = 614516381) B614516381
theorem B7106383 : Blo 1313975 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B28446551 : Blo 1313975 28446551 := bstep (se 1 (by rfl) ⟨21334913, by rfl⟩ : syracuseStep 28446551 = 42669827) B42669827
theorem B16846703 : Blo 1313975 16846703 := bstep (se 1 (by rfl) ⟨12635027, by rfl⟩ : syracuseStep 16846703 = 25270055) B25270055
theorem B1314671 : Blo 1313975 1314671 := bstep (se 1 (by rfl) ⟨986003, by rfl⟩ : syracuseStep 1314671 = 1972007) B1972007
theorem B1314719 : Blo 1313975 1314719 := bstep (se 1 (by rfl) ⟨986039, by rfl⟩ : syracuseStep 1314719 = 1972079) B1972079
theorem B82047305 : Blo 1313975 82047305 := bstep (se 2 (by rfl) ⟨30767739, by rfl⟩ : syracuseStep 82047305 = 61535479) B61535479
theorem B1315231 : Blo 1313975 1315231 := bstep (se 1 (by rfl) ⟨986423, by rfl⟩ : syracuseStep 1315231 = 1972847) B1972847
theorem B4436747 : Blo 1313975 4436747 := bstep (se 1 (by rfl) ⟨3327560, by rfl⟩ : syracuseStep 4436747 = 6655121) B6655121
theorem B14972201 : Blo 1313975 14972201 := bstep (se 2 (by rfl) ⟨5614575, by rfl⟩ : syracuseStep 14972201 = 11229151) B11229151
theorem B12645713 : Blo 1313975 12645713 := bstep (se 2 (by rfl) ⟨4742142, by rfl⟩ : syracuseStep 12645713 = 9484285) B9484285
theorem B1971707 : Blo 1313975 1971707 := bstep (se 1 (by rfl) ⟨1478780, by rfl⟩ : syracuseStep 1971707 = 2957561) B2957561
theorem B5617619 : Blo 1313975 5617619 := bstep (se 1 (by rfl) ⟨4213214, by rfl⟩ : syracuseStep 5617619 = 8426429) B8426429
theorem B4438043 : Blo 1313975 4438043 := bstep (se 1 (by rfl) ⟨3328532, by rfl⟩ : syracuseStep 4438043 = 6657065) B6657065
theorem B1972391 : Blo 1313975 1972391 := bstep (se 1 (by rfl) ⟨1479293, by rfl⟩ : syracuseStep 1972391 = 2958587) B2958587
theorem B1972601 : Blo 1313975 1972601 := bstep (se 2 (by rfl) ⟨739725, by rfl⟩ : syracuseStep 1972601 = 1479451) B1479451
theorem B1972703 : Blo 1313975 1972703 := bstep (se 1 (by rfl) ⟨1479527, by rfl⟩ : syracuseStep 1972703 = 2959055) B2959055
theorem B1972967 : Blo 1313975 1972967 := bstep (se 1 (by rfl) ⟨1479725, by rfl⟩ : syracuseStep 1972967 = 2959451) B2959451
theorem B246160451 : Blo 1313975 246160451 := bstep (se 1 (by rfl) ⟨184620338, by rfl⟩ : syracuseStep 246160451 = 369240677) B369240677
theorem B1973339 : Blo 1313975 1973339 := bstep (se 1 (by rfl) ⟨1480004, by rfl⟩ : syracuseStep 1973339 = 2960009) B2960009
theorem B14982407 : Blo 1313975 14982407 := bstep (se 1 (by rfl) ⟨11236805, by rfl⟩ : syracuseStep 14982407 = 22473611) B22473611
theorem B16858489 : Blo 1313975 16858489 := bstep (se 2 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 16858489 = 12643867) B12643867
theorem B2956751 : Blo 1313975 2956751 := bstep (se 1 (by rfl) ⟨2217563, by rfl⟩ : syracuseStep 2956751 = 4435127) B4435127
theorem B38968883 : Blo 1313975 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B2219575 : Blo 1313975 2219575 := bstep (se 1 (by rfl) ⟨1664681, by rfl⟩ : syracuseStep 2219575 = 3329363) B3329363
theorem B54698203 : Blo 1313975 54698203 := bstep (se 1 (by rfl) ⟨41023652, by rfl⟩ : syracuseStep 54698203 = 82047305) B82047305
theorem B2957831 : Blo 1313975 2957831 := bstep (se 1 (by rfl) ⟨2218373, by rfl⟩ : syracuseStep 2957831 = 4436747) B4436747
theorem B3326791 : Blo 1313975 3326791 := bstep (se 1 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 3326791 = 4990187) B4990187
theorem B4440959 : Blo 1313975 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B8430475 : Blo 1313975 8430475 := bstep (se 1 (by rfl) ⟨6322856, by rfl⟩ : syracuseStep 8430475 = 12645713) B12645713
theorem B3793889 : Blo 1313975 3793889 := bstep (se 2 (by rfl) ⟨1422708, by rfl⟩ : syracuseStep 3793889 = 2845417) B2845417
theorem B3745079 : Blo 1313975 3745079 := bstep (se 1 (by rfl) ⟨2808809, by rfl⟩ : syracuseStep 3745079 = 5617619) B5617619
theorem B2958695 : Blo 1313975 2958695 := bstep (se 1 (by rfl) ⟨2219021, by rfl⟩ : syracuseStep 2958695 = 4438043) B4438043
theorem B2959433 : Blo 1313975 2959433 := bstep (se 2 (by rfl) ⟨1109787, by rfl⟩ : syracuseStep 2959433 = 2219575) B2219575
theorem B9988271 : Blo 1313975 9988271 := bstep (se 1 (by rfl) ⟨7491203, by rfl⟩ : syracuseStep 9988271 = 14982407) B14982407
theorem B25979255 : Blo 1313975 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B3746537 : Blo 1313975 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B4992313 : Blo 1313975 4992313 := bstep (se 2 (by rfl) ⟨1872117, by rfl⟩ : syracuseStep 4992313 = 3744235) B3744235
theorem B3419563 : Blo 1313975 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B9981467 : Blo 1313975 9981467 := bstep (se 1 (by rfl) ⟨7486100, by rfl⟩ : syracuseStep 9981467 = 14972201) B14972201
theorem B1314471 : Blo 1313975 1314471 := bstep (se 1 (by rfl) ⟨985853, by rfl⟩ : syracuseStep 1314471 = 1971707) B1971707
theorem B1314927 : Blo 1313975 1314927 := bstep (se 1 (by rfl) ⟨986195, by rfl⟩ : syracuseStep 1314927 = 1972391) B1972391
theorem B1315067 : Blo 1313975 1315067 := bstep (se 1 (by rfl) ⟨986300, by rfl⟩ : syracuseStep 1315067 = 1972601) B1972601
theorem B1315135 : Blo 1313975 1315135 := bstep (se 1 (by rfl) ⟨986351, by rfl⟩ : syracuseStep 1315135 = 1972703) B1972703
theorem B1315311 : Blo 1313975 1315311 := bstep (se 1 (by rfl) ⟨986483, by rfl⟩ : syracuseStep 1315311 = 1972967) B1972967
theorem B164106967 : Blo 1313975 164106967 := bstep (se 1 (by rfl) ⟨123080225, by rfl⟩ : syracuseStep 164106967 = 246160451) B246160451
theorem B1315559 : Blo 1313975 1315559 := bstep (se 1 (by rfl) ⟨986669, by rfl⟩ : syracuseStep 1315559 = 1973339) B1973339
theorem B1971167 : Blo 1313975 1971167 := bstep (se 1 (by rfl) ⟨1478375, by rfl⟩ : syracuseStep 1971167 = 2956751) B2956751
theorem B9475177 : Blo 1313975 9475177 := bstep (se 2 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 9475177 = 7106383) B7106383
theorem B273118391 : Blo 1313975 273118391 := bstep (se 1 (by rfl) ⟨204838793, by rfl⟩ : syracuseStep 273118391 = 409677587) B409677587
theorem B1972331 : Blo 1313975 1972331 := bstep (se 1 (by rfl) ⟨1479248, by rfl⟩ : syracuseStep 1972331 = 2958497) B2958497
theorem B1972535 : Blo 1313975 1972535 := bstep (se 1 (by rfl) ⟨1479401, by rfl⟩ : syracuseStep 1972535 = 2958803) B2958803
theorem B6314537 : Blo 1313975 6314537 := bstep (se 2 (by rfl) ⟨2367951, by rfl⟩ : syracuseStep 6314537 = 4735903) B4735903
theorem B1972943 : Blo 1313975 1972943 := bstep (se 1 (by rfl) ⟨1479707, by rfl⟩ : syracuseStep 1972943 = 2959415) B2959415
theorem B1973039 : Blo 1313975 1973039 := bstep (se 1 (by rfl) ⟨1479779, by rfl⟩ : syracuseStep 1973039 = 2959559) B2959559
theorem B11230109 : Blo 1313975 11230109 := bstep (se 3 (by rfl) ⟨2105645, by rfl⟩ : syracuseStep 11230109 = 4211291) B4211291
theorem B22477985 : Blo 1313975 22477985 := bstep (se 2 (by rfl) ⟨8429244, by rfl⟩ : syracuseStep 22477985 = 16858489) B16858489
theorem B1973531 : Blo 1313975 1973531 := bstep (se 1 (by rfl) ⟨1480148, by rfl⟩ : syracuseStep 1973531 = 2960297) B2960297
theorem B6659495 : Blo 1313975 6659495 := bstep (se 1 (by rfl) ⟨4994621, by rfl⟩ : syracuseStep 6659495 = 9989243) B9989243
theorem B2957039 : Blo 1313975 2957039 := bstep (se 1 (by rfl) ⟨2217779, by rfl⟩ : syracuseStep 2957039 = 4435559) B4435559
theorem B18964367 : Blo 1313975 18964367 := bstep (se 1 (by rfl) ⟨14223275, by rfl⟩ : syracuseStep 18964367 = 28446551) B28446551
theorem B11231135 : Blo 1313975 11231135 := bstep (se 1 (by rfl) ⟨8423351, by rfl⟩ : syracuseStep 11231135 = 16846703) B16846703
theorem B218809289 : Blo 1313975 218809289 := bstep (se 2 (by rfl) ⟨82053483, by rfl⟩ : syracuseStep 218809289 = 164106967) B164106967
theorem B11240633 : Blo 1313975 11240633 := bstep (se 2 (by rfl) ⟨4215237, by rfl⟩ : syracuseStep 11240633 = 8430475) B8430475
theorem B12633569 : Blo 1313975 12633569 := bstep (se 2 (by rfl) ⟨4737588, by rfl⟩ : syracuseStep 12633569 = 9475177) B9475177
theorem B17319503 : Blo 1313975 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B14985323 : Blo 1313975 14985323 := bstep (se 1 (by rfl) ⟨11238992, by rfl⟩ : syracuseStep 14985323 = 22477985) B22477985
theorem B6654311 : Blo 1313975 6654311 := bstep (se 1 (by rfl) ⟨4990733, by rfl⟩ : syracuseStep 6654311 = 9981467) B9981467
theorem B12642911 : Blo 1313975 12642911 := bstep (se 1 (by rfl) ⟨9482183, by rfl⟩ : syracuseStep 12642911 = 18964367) B18964367
theorem B2960639 : Blo 1313975 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B1314111 : Blo 1313975 1314111 := bstep (se 1 (by rfl) ⟨985583, by rfl⟩ : syracuseStep 1314111 = 1971167) B1971167
theorem B182078927 : Blo 1313975 182078927 := bstep (se 1 (by rfl) ⟨136559195, by rfl⟩ : syracuseStep 182078927 = 273118391) B273118391
theorem B4435721 : Blo 1313975 4435721 := bstep (se 2 (by rfl) ⟨1663395, by rfl⟩ : syracuseStep 4435721 = 3326791) B3326791
theorem B1314887 : Blo 1313975 1314887 := bstep (se 1 (by rfl) ⟨986165, by rfl⟩ : syracuseStep 1314887 = 1972331) B1972331
theorem B1315023 : Blo 1313975 1315023 := bstep (se 1 (by rfl) ⟨986267, by rfl⟩ : syracuseStep 1315023 = 1972535) B1972535
theorem B6656417 : Blo 1313975 6656417 := bstep (se 2 (by rfl) ⟨2496156, by rfl⟩ : syracuseStep 6656417 = 4992313) B4992313
theorem B1315295 : Blo 1313975 1315295 := bstep (se 1 (by rfl) ⟨986471, by rfl⟩ : syracuseStep 1315295 = 1972943) B1972943
theorem B1315359 : Blo 1313975 1315359 := bstep (se 1 (by rfl) ⟨986519, by rfl⟩ : syracuseStep 1315359 = 1973039) B1973039
theorem B4559417 : Blo 1313975 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B1315687 : Blo 1313975 1315687 := bstep (se 1 (by rfl) ⟨986765, by rfl⟩ : syracuseStep 1315687 = 1973531) B1973531
theorem B1971359 : Blo 1313975 1971359 := bstep (se 1 (by rfl) ⟨1478519, by rfl⟩ : syracuseStep 1971359 = 2957039) B2957039
theorem B72930937 : Blo 1313975 72930937 := bstep (se 2 (by rfl) ⟨27349101, by rfl⟩ : syracuseStep 72930937 = 54698203) B54698203
theorem B1971887 : Blo 1313975 1971887 := bstep (se 1 (by rfl) ⟨1478915, by rfl⟩ : syracuseStep 1971887 = 2957831) B2957831
theorem B2496719 : Blo 1313975 2496719 := bstep (se 1 (by rfl) ⟨1872539, by rfl⟩ : syracuseStep 2496719 = 3745079) B3745079
theorem B1972463 : Blo 1313975 1972463 := bstep (se 1 (by rfl) ⟨1479347, by rfl⟩ : syracuseStep 1972463 = 2958695) B2958695
theorem B1972955 : Blo 1313975 1972955 := bstep (se 1 (by rfl) ⟨1479716, by rfl⟩ : syracuseStep 1972955 = 2959433) B2959433
theorem B6658847 : Blo 1313975 6658847 := bstep (se 1 (by rfl) ⟨4994135, by rfl⟩ : syracuseStep 6658847 = 9988271) B9988271
theorem B4209691 : Blo 1313975 4209691 := bstep (se 1 (by rfl) ⟨3157268, by rfl⟩ : syracuseStep 4209691 = 6314537) B6314537
theorem B2497691 : Blo 1313975 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B7486739 : Blo 1313975 7486739 := bstep (se 1 (by rfl) ⟨5615054, by rfl⟩ : syracuseStep 7486739 = 11230109) B11230109
theorem B4439663 : Blo 1313975 4439663 := bstep (se 1 (by rfl) ⟨3329747, by rfl⟩ : syracuseStep 4439663 = 6659495) B6659495
theorem B10117037 : Blo 1313975 10117037 := bstep (se 3 (by rfl) ⟨1896944, by rfl⟩ : syracuseStep 10117037 = 3793889) B3793889
theorem B7487423 : Blo 1313975 7487423 := bstep (se 1 (by rfl) ⟨5615567, by rfl⟩ : syracuseStep 7487423 = 11231135) B11231135
theorem B3039611 : Blo 1313975 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B8422379 : Blo 1313975 8422379 := bstep (se 1 (by rfl) ⟨6316784, by rfl⟩ : syracuseStep 8422379 = 12633569) B12633569
theorem B5612921 : Blo 1313975 5612921 := bstep (se 2 (by rfl) ⟨2104845, by rfl⟩ : syracuseStep 5612921 = 4209691) B4209691
theorem B1664479 : Blo 1313975 1664479 := bstep (se 1 (by rfl) ⟨1248359, by rfl⟩ : syracuseStep 1664479 = 2496719) B2496719
theorem B1665127 : Blo 1313975 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B97241249 : Blo 1313975 97241249 := bstep (se 2 (by rfl) ⟨36465468, by rfl⟩ : syracuseStep 97241249 = 72930937) B72930937
theorem B4991159 : Blo 1313975 4991159 := bstep (se 1 (by rfl) ⟨3743369, by rfl⟩ : syracuseStep 4991159 = 7486739) B7486739
theorem B2959775 : Blo 1313975 2959775 := bstep (se 1 (by rfl) ⟨2219831, by rfl⟩ : syracuseStep 2959775 = 4439663) B4439663
theorem B6744691 : Blo 1313975 6744691 := bstep (se 1 (by rfl) ⟨5058518, by rfl⟩ : syracuseStep 6744691 = 10117037) B10117037
theorem B4991615 : Blo 1313975 4991615 := bstep (se 1 (by rfl) ⟨3743711, by rfl⟩ : syracuseStep 4991615 = 7487423) B7487423
theorem B1314239 : Blo 1313975 1314239 := bstep (se 1 (by rfl) ⟨985679, by rfl⟩ : syracuseStep 1314239 = 1971359) B1971359
theorem B11546335 : Blo 1313975 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B1314591 : Blo 1313975 1314591 := bstep (se 1 (by rfl) ⟨985943, by rfl⟩ : syracuseStep 1314591 = 1971887) B1971887
theorem B9990215 : Blo 1313975 9990215 := bstep (se 1 (by rfl) ⟨7492661, by rfl⟩ : syracuseStep 9990215 = 14985323) B14985323
theorem B1314975 : Blo 1313975 1314975 := bstep (se 1 (by rfl) ⟨986231, by rfl⟩ : syracuseStep 1314975 = 1972463) B1972463
theorem B4436207 : Blo 1313975 4436207 := bstep (se 1 (by rfl) ⟨3327155, by rfl⟩ : syracuseStep 4436207 = 6654311) B6654311
theorem B1315303 : Blo 1313975 1315303 := bstep (se 1 (by rfl) ⟨986477, by rfl⟩ : syracuseStep 1315303 = 1972955) B1972955
theorem B121385951 : Blo 1313975 121385951 := bstep (se 1 (by rfl) ⟨91039463, by rfl⟩ : syracuseStep 121385951 = 182078927) B182078927
theorem B4437611 : Blo 1313975 4437611 := bstep (se 1 (by rfl) ⟨3328208, by rfl⟩ : syracuseStep 4437611 = 6656417) B6656417
theorem B145872859 : Blo 1313975 145872859 := bstep (se 1 (by rfl) ⟨109404644, by rfl⟩ : syracuseStep 145872859 = 218809289) B218809289
theorem B7493755 : Blo 1313975 7493755 := bstep (se 1 (by rfl) ⟨5620316, by rfl⟩ : syracuseStep 7493755 = 11240633) B11240633
theorem B8428607 : Blo 1313975 8428607 := bstep (se 1 (by rfl) ⟨6321455, by rfl⟩ : syracuseStep 8428607 = 12642911) B12642911
theorem B4439231 : Blo 1313975 4439231 := bstep (se 1 (by rfl) ⟨3329423, by rfl⟩ : syracuseStep 4439231 = 6658847) B6658847
theorem B1973759 : Blo 1313975 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B2957147 : Blo 1313975 2957147 := bstep (se 1 (by rfl) ⟨2217860, by rfl⟩ : syracuseStep 2957147 = 4435721) B4435721
theorem B6660143 : Blo 1313975 6660143 := bstep (se 1 (by rfl) ⟨4995107, by rfl⟩ : syracuseStep 6660143 = 9990215) B9990215
theorem B2220169 : Blo 1313975 2220169 := bstep (se 2 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 2220169 = 1665127) B1665127
theorem B2957471 : Blo 1313975 2957471 := bstep (se 1 (by rfl) ⟨2218103, by rfl⟩ : syracuseStep 2957471 = 4436207) B4436207
theorem B35971685 : Blo 1313975 35971685 := bstep (se 4 (by rfl) ⟨3372345, by rfl⟩ : syracuseStep 35971685 = 6744691) B6744691
theorem B2958407 : Blo 1313975 2958407 := bstep (se 1 (by rfl) ⟨2218805, by rfl⟩ : syracuseStep 2958407 = 4437611) B4437611
theorem B3327439 : Blo 1313975 3327439 := bstep (se 1 (by rfl) ⟨2495579, by rfl⟩ : syracuseStep 3327439 = 4991159) B4991159
theorem B3327743 : Blo 1313975 3327743 := bstep (se 1 (by rfl) ⟨2495807, by rfl⟩ : syracuseStep 3327743 = 4991615) B4991615
theorem B2959487 : Blo 1313975 2959487 := bstep (se 1 (by rfl) ⟨2219615, by rfl⟩ : syracuseStep 2959487 = 4439231) B4439231
theorem B15395113 : Blo 1313975 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B194497145 : Blo 1313975 194497145 := bstep (se 2 (by rfl) ⟨72936429, by rfl⟩ : syracuseStep 194497145 = 145872859) B145872859
theorem B80923967 : Blo 1313975 80923967 := bstep (se 1 (by rfl) ⟨60692975, by rfl⟩ : syracuseStep 80923967 = 121385951) B121385951
theorem B5614919 : Blo 1313975 5614919 := bstep (se 1 (by rfl) ⟨4211189, by rfl⟩ : syracuseStep 5614919 = 8422379) B8422379
theorem B64827499 : Blo 1313975 64827499 := bstep (se 1 (by rfl) ⟨48620624, by rfl⟩ : syracuseStep 64827499 = 97241249) B97241249
theorem B1315839 : Blo 1313975 1315839 := bstep (se 1 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 1315839 = 1973759) B1973759
theorem B1971431 : Blo 1313975 1971431 := bstep (se 1 (by rfl) ⟨1478573, by rfl⟩ : syracuseStep 1971431 = 2957147) B2957147
theorem B9991673 : Blo 1313975 9991673 := bstep (se 2 (by rfl) ⟨3746877, by rfl⟩ : syracuseStep 9991673 = 7493755) B7493755
theorem B3741947 : Blo 1313975 3741947 := bstep (se 1 (by rfl) ⟨2806460, by rfl⟩ : syracuseStep 3741947 = 5612921) B5612921
theorem B32422517 : Blo 1313975 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B1973183 : Blo 1313975 1973183 := bstep (se 1 (by rfl) ⟨1479887, by rfl⟩ : syracuseStep 1973183 = 2959775) B2959775
theorem B2219305 : Blo 1313975 2219305 := bstep (se 2 (by rfl) ⟨832239, by rfl⟩ : syracuseStep 2219305 = 1664479) B1664479
theorem B5619071 : Blo 1313975 5619071 := bstep (se 1 (by rfl) ⟨4214303, by rfl⟩ : syracuseStep 5619071 = 8428607) B8428607
theorem B4440095 : Blo 1313975 4440095 := bstep (se 1 (by rfl) ⟨3330071, by rfl⟩ : syracuseStep 4440095 = 6660143) B6660143
theorem B6661115 : Blo 1313975 6661115 := bstep (se 1 (by rfl) ⟨4995836, by rfl⟩ : syracuseStep 6661115 = 9991673) B9991673
theorem B2959073 : Blo 1313975 2959073 := bstep (se 2 (by rfl) ⟨1109652, by rfl⟩ : syracuseStep 2959073 = 2219305) B2219305
theorem B129664763 : Blo 1313975 129664763 := bstep (se 1 (by rfl) ⟨97248572, by rfl⟩ : syracuseStep 129664763 = 194497145) B194497145
theorem B3746047 : Blo 1313975 3746047 := bstep (se 1 (by rfl) ⟨2809535, by rfl⟩ : syracuseStep 3746047 = 5619071) B5619071
theorem B86436665 : Blo 1313975 86436665 := bstep (se 2 (by rfl) ⟨32413749, by rfl⟩ : syracuseStep 86436665 = 64827499) B64827499
theorem B2960225 : Blo 1313975 2960225 := bstep (se 2 (by rfl) ⟨1110084, by rfl⟩ : syracuseStep 2960225 = 2220169) B2220169
theorem B23981123 : Blo 1313975 23981123 := bstep (se 1 (by rfl) ⟨17985842, by rfl⟩ : syracuseStep 23981123 = 35971685) B35971685
theorem B1314287 : Blo 1313975 1314287 := bstep (se 1 (by rfl) ⟨985715, by rfl⟩ : syracuseStep 1314287 = 1971431) B1971431
theorem B2494631 : Blo 1313975 2494631 := bstep (se 1 (by rfl) ⟨1870973, by rfl⟩ : syracuseStep 2494631 = 3741947) B3741947
theorem B21615011 : Blo 1313975 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B4436585 : Blo 1313975 4436585 := bstep (se 2 (by rfl) ⟨1663719, by rfl⟩ : syracuseStep 4436585 = 3327439) B3327439
theorem B1315455 : Blo 1313975 1315455 := bstep (se 1 (by rfl) ⟨986591, by rfl⟩ : syracuseStep 1315455 = 1973183) B1973183
theorem B53949311 : Blo 1313975 53949311 := bstep (se 1 (by rfl) ⟨40461983, by rfl⟩ : syracuseStep 53949311 = 80923967) B80923967
theorem B1971647 : Blo 1313975 1971647 := bstep (se 1 (by rfl) ⟨1478735, by rfl⟩ : syracuseStep 1971647 = 2957471) B2957471
theorem B20526817 : Blo 1313975 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B1972271 : Blo 1313975 1972271 := bstep (se 1 (by rfl) ⟨1479203, by rfl⟩ : syracuseStep 1972271 = 2958407) B2958407
theorem B2218495 : Blo 1313975 2218495 := bstep (se 1 (by rfl) ⟨1663871, by rfl⟩ : syracuseStep 2218495 = 3327743) B3327743
theorem B1972991 : Blo 1313975 1972991 := bstep (se 1 (by rfl) ⟨1479743, by rfl⟩ : syracuseStep 1972991 = 2959487) B2959487
theorem B3743279 : Blo 1313975 3743279 := bstep (se 1 (by rfl) ⟨2807459, by rfl⟩ : syracuseStep 3743279 = 5614919) B5614919
theorem B1663087 : Blo 1313975 1663087 := bstep (se 1 (by rfl) ⟨1247315, by rfl⟩ : syracuseStep 1663087 = 2494631) B2494631
theorem B14410007 : Blo 1313975 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B2957723 : Blo 1313975 2957723 := bstep (se 1 (by rfl) ⟨2218292, by rfl⟩ : syracuseStep 2957723 = 4436585) B4436585
theorem B4440743 : Blo 1313975 4440743 := bstep (se 1 (by rfl) ⟨3330557, by rfl⟩ : syracuseStep 4440743 = 6661115) B6661115
theorem B2957993 : Blo 1313975 2957993 := bstep (se 2 (by rfl) ⟨1109247, by rfl⟩ : syracuseStep 2957993 = 2218495) B2218495
theorem B86443175 : Blo 1313975 86443175 := bstep (se 1 (by rfl) ⟨64832381, by rfl⟩ : syracuseStep 86443175 = 129664763) B129664763
theorem B57624443 : Blo 1313975 57624443 := bstep (se 1 (by rfl) ⟨43218332, by rfl⟩ : syracuseStep 57624443 = 86436665) B86436665
theorem B2960063 : Blo 1313975 2960063 := bstep (se 1 (by rfl) ⟨2220047, by rfl⟩ : syracuseStep 2960063 = 4440095) B4440095
theorem B35966207 : Blo 1313975 35966207 := bstep (se 1 (by rfl) ⟨26974655, by rfl⟩ : syracuseStep 35966207 = 53949311) B53949311
theorem B1314431 : Blo 1313975 1314431 := bstep (se 1 (by rfl) ⟨985823, by rfl⟩ : syracuseStep 1314431 = 1971647) B1971647
theorem B1314847 : Blo 1313975 1314847 := bstep (se 1 (by rfl) ⟨986135, by rfl⟩ : syracuseStep 1314847 = 1972271) B1972271
theorem B1315327 : Blo 1313975 1315327 := bstep (se 1 (by rfl) ⟨986495, by rfl⟩ : syracuseStep 1315327 = 1972991) B1972991
theorem B15987415 : Blo 1313975 15987415 := bstep (se 1 (by rfl) ⟨11990561, by rfl⟩ : syracuseStep 15987415 = 23981123) B23981123
theorem B2495519 : Blo 1313975 2495519 := bstep (se 1 (by rfl) ⟨1871639, by rfl⟩ : syracuseStep 2495519 = 3743279) B3743279
theorem B4994729 : Blo 1313975 4994729 := bstep (se 2 (by rfl) ⟨1873023, by rfl⟩ : syracuseStep 4994729 = 3746047) B3746047
theorem B1972715 : Blo 1313975 1972715 := bstep (se 1 (by rfl) ⟨1479536, by rfl⟩ : syracuseStep 1972715 = 2959073) B2959073
theorem B1973483 : Blo 1313975 1973483 := bstep (se 1 (by rfl) ⟨1480112, by rfl⟩ : syracuseStep 1973483 = 2960225) B2960225
theorem B27369089 : Blo 1313975 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B1663679 : Blo 1313975 1663679 := bstep (se 1 (by rfl) ⟨1247759, by rfl⟩ : syracuseStep 1663679 = 2495519) B2495519
theorem B21316553 : Blo 1313975 21316553 := bstep (se 2 (by rfl) ⟨7993707, by rfl⟩ : syracuseStep 21316553 = 15987415) B15987415
theorem B18246059 : Blo 1313975 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B2960495 : Blo 1313975 2960495 := bstep (se 1 (by rfl) ⟨2220371, by rfl⟩ : syracuseStep 2960495 = 4440743) B4440743
theorem B3329819 : Blo 1313975 3329819 := bstep (se 1 (by rfl) ⟨2497364, by rfl⟩ : syracuseStep 3329819 = 4994729) B4994729
theorem B38416295 : Blo 1313975 38416295 := bstep (se 1 (by rfl) ⟨28812221, by rfl⟩ : syracuseStep 38416295 = 57624443) B57624443
theorem B1315143 : Blo 1313975 1315143 := bstep (se 1 (by rfl) ⟨986357, by rfl⟩ : syracuseStep 1315143 = 1972715) B1972715
theorem B1315655 : Blo 1313975 1315655 := bstep (se 1 (by rfl) ⟨986741, by rfl⟩ : syracuseStep 1315655 = 1973483) B1973483
theorem B2217449 : Blo 1313975 2217449 := bstep (se 2 (by rfl) ⟨831543, by rfl⟩ : syracuseStep 2217449 = 1663087) B1663087
theorem B9606671 : Blo 1313975 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B1971815 : Blo 1313975 1971815 := bstep (se 1 (by rfl) ⟨1478861, by rfl⟩ : syracuseStep 1971815 = 2957723) B2957723
theorem B1971995 : Blo 1313975 1971995 := bstep (se 1 (by rfl) ⟨1478996, by rfl⟩ : syracuseStep 1971995 = 2957993) B2957993
theorem B57628783 : Blo 1313975 57628783 := bstep (se 1 (by rfl) ⟨43221587, by rfl⟩ : syracuseStep 57628783 = 86443175) B86443175
theorem B1973375 : Blo 1313975 1973375 := bstep (se 1 (by rfl) ⟨1480031, by rfl⟩ : syracuseStep 1973375 = 2960063) B2960063
theorem B23977471 : Blo 1313975 23977471 := bstep (se 1 (by rfl) ⟨17983103, by rfl⟩ : syracuseStep 23977471 = 35966207) B35966207
theorem B102443453 : Blo 1313975 102443453 := bstep (se 3 (by rfl) ⟨19208147, by rfl⟩ : syracuseStep 102443453 = 38416295) B38416295
theorem B1478299 : Blo 1313975 1478299 := bstep (se 1 (by rfl) ⟨1108724, by rfl⟩ : syracuseStep 1478299 = 2217449) B2217449
theorem B1314543 : Blo 1313975 1314543 := bstep (se 1 (by rfl) ⟨985907, by rfl⟩ : syracuseStep 1314543 = 1971815) B1971815
theorem B1314663 : Blo 1313975 1314663 := bstep (se 1 (by rfl) ⟨985997, by rfl⟩ : syracuseStep 1314663 = 1971995) B1971995
theorem B4436477 : Blo 1313975 4436477 := bstep (se 3 (by rfl) ⟨831839, by rfl⟩ : syracuseStep 4436477 = 1663679) B1663679
theorem B31969961 : Blo 1313975 31969961 := bstep (se 2 (by rfl) ⟨11988735, by rfl⟩ : syracuseStep 31969961 = 23977471) B23977471
theorem B1315583 : Blo 1313975 1315583 := bstep (se 1 (by rfl) ⟨986687, by rfl⟩ : syracuseStep 1315583 = 1973375) B1973375
theorem B76838377 : Blo 1313975 76838377 := bstep (se 2 (by rfl) ⟨28814391, by rfl⟩ : syracuseStep 76838377 = 57628783) B57628783
theorem B14211035 : Blo 1313975 14211035 := bstep (se 1 (by rfl) ⟨10658276, by rfl⟩ : syracuseStep 14211035 = 21316553) B21316553
theorem B6404447 : Blo 1313975 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B12164039 : Blo 1313975 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B1973663 : Blo 1313975 1973663 := bstep (se 1 (by rfl) ⟨1480247, by rfl⟩ : syracuseStep 1973663 = 2960495) B2960495
theorem B2219879 : Blo 1313975 2219879 := bstep (se 1 (by rfl) ⟨1664909, by rfl⟩ : syracuseStep 2219879 = 3329819) B3329819
theorem B2957651 : Blo 1313975 2957651 := bstep (se 1 (by rfl) ⟨2218238, by rfl⟩ : syracuseStep 2957651 = 4436477) B4436477
theorem B102451169 : Blo 1313975 102451169 := bstep (se 2 (by rfl) ⟨38419188, by rfl⟩ : syracuseStep 102451169 = 76838377) B76838377
theorem B9474023 : Blo 1313975 9474023 := bstep (se 1 (by rfl) ⟨7105517, by rfl⟩ : syracuseStep 9474023 = 14211035) B14211035
theorem B1971065 : Blo 1313975 1971065 := bstep (se 2 (by rfl) ⟨739149, by rfl⟩ : syracuseStep 1971065 = 1478299) B1478299
theorem B1315775 : Blo 1313975 1315775 := bstep (se 1 (by rfl) ⟨986831, by rfl⟩ : syracuseStep 1315775 = 1973663) B1973663
theorem B1479919 : Blo 1313975 1479919 := bstep (se 1 (by rfl) ⟨1109939, by rfl⟩ : syracuseStep 1479919 = 2219879) B2219879
theorem B21313307 : Blo 1313975 21313307 := bstep (se 1 (by rfl) ⟨15984980, by rfl⟩ : syracuseStep 21313307 = 31969961) B31969961
theorem B17078525 : Blo 1313975 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B68295635 : Blo 1313975 68295635 := bstep (se 1 (by rfl) ⟨51221726, by rfl⟩ : syracuseStep 68295635 = 102443453) B102443453
theorem B8109359 : Blo 1313975 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B1314043 : Blo 1313975 1314043 := bstep (se 1 (by rfl) ⟨985532, by rfl⟩ : syracuseStep 1314043 = 1971065) B1971065
theorem B14208871 : Blo 1313975 14208871 := bstep (se 1 (by rfl) ⟨10656653, by rfl⟩ : syracuseStep 14208871 = 21313307) B21313307
theorem B1971767 : Blo 1313975 1971767 := bstep (se 1 (by rfl) ⟨1478825, by rfl⟩ : syracuseStep 1971767 = 2957651) B2957651
theorem B11385683 : Blo 1313975 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B1973225 : Blo 1313975 1973225 := bstep (se 2 (by rfl) ⟨739959, by rfl⟩ : syracuseStep 1973225 = 1479919) B1479919
theorem B45530423 : Blo 1313975 45530423 := bstep (se 1 (by rfl) ⟨34147817, by rfl⟩ : syracuseStep 45530423 = 68295635) B68295635
theorem B5406239 : Blo 1313975 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B273203117 : Blo 1313975 273203117 := bstep (se 3 (by rfl) ⟨51225584, by rfl⟩ : syracuseStep 273203117 = 102451169) B102451169
theorem B6316015 : Blo 1313975 6316015 := bstep (se 1 (by rfl) ⟨4737011, by rfl⟩ : syracuseStep 6316015 = 9474023) B9474023
theorem B30353615 : Blo 1313975 30353615 := bstep (se 1 (by rfl) ⟨22765211, by rfl⟩ : syracuseStep 30353615 = 45530423) B45530423
theorem B182135411 : Blo 1313975 182135411 := bstep (se 1 (by rfl) ⟨136601558, by rfl⟩ : syracuseStep 182135411 = 273203117) B273203117
theorem B1314511 : Blo 1313975 1314511 := bstep (se 1 (by rfl) ⟨985883, by rfl⟩ : syracuseStep 1314511 = 1971767) B1971767
theorem B7590455 : Blo 1313975 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B1315483 : Blo 1313975 1315483 := bstep (se 1 (by rfl) ⟨986612, by rfl⟩ : syracuseStep 1315483 = 1973225) B1973225
theorem B18945161 : Blo 1313975 18945161 := bstep (se 2 (by rfl) ⟨7104435, by rfl⟩ : syracuseStep 18945161 = 14208871) B14208871
theorem B3604159 : Blo 1313975 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B8421353 : Blo 1313975 8421353 := bstep (se 2 (by rfl) ⟨3158007, by rfl⟩ : syracuseStep 8421353 = 6316015) B6316015
theorem B20235743 : Blo 1313975 20235743 := bstep (se 1 (by rfl) ⟨15176807, by rfl⟩ : syracuseStep 20235743 = 30353615) B30353615
theorem B121423607 : Blo 1313975 121423607 := bstep (se 1 (by rfl) ⟨91067705, by rfl⟩ : syracuseStep 121423607 = 182135411) B182135411
theorem B5614235 : Blo 1313975 5614235 := bstep (se 1 (by rfl) ⟨4210676, by rfl⟩ : syracuseStep 5614235 = 8421353) B8421353
theorem B19222181 : Blo 1313975 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B5060303 : Blo 1313975 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B12630107 : Blo 1313975 12630107 := bstep (se 1 (by rfl) ⟨9472580, by rfl⟩ : syracuseStep 12630107 = 18945161) B18945161
theorem B12814787 : Blo 1313975 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B80949071 : Blo 1313975 80949071 := bstep (se 1 (by rfl) ⟨60711803, by rfl⟩ : syracuseStep 80949071 = 121423607) B121423607
theorem B13490495 : Blo 1313975 13490495 := bstep (se 1 (by rfl) ⟨10117871, by rfl⟩ : syracuseStep 13490495 = 20235743) B20235743
theorem B3373535 : Blo 1313975 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B8420071 : Blo 1313975 8420071 := bstep (se 1 (by rfl) ⟨6315053, by rfl⟩ : syracuseStep 8420071 = 12630107) B12630107
theorem B3742823 : Blo 1313975 3742823 := bstep (se 1 (by rfl) ⟨2807117, by rfl⟩ : syracuseStep 3742823 = 5614235) B5614235
theorem B8996093 : Blo 1313975 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B11226761 : Blo 1313975 11226761 := bstep (se 2 (by rfl) ⟨4210035, by rfl⟩ : syracuseStep 11226761 = 8420071) B8420071
theorem B34172765 : Blo 1313975 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B2495215 : Blo 1313975 2495215 := bstep (se 1 (by rfl) ⟨1871411, by rfl⟩ : syracuseStep 2495215 = 3742823) B3742823
theorem B53966047 : Blo 1313975 53966047 := bstep (se 1 (by rfl) ⟨40474535, by rfl⟩ : syracuseStep 53966047 = 80949071) B80949071
theorem B8993663 : Blo 1313975 8993663 := bstep (se 1 (by rfl) ⟨6745247, by rfl⟩ : syracuseStep 8993663 = 13490495) B13490495
theorem B5997395 : Blo 1313975 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B3326953 : Blo 1313975 3326953 := bstep (se 2 (by rfl) ⟨1247607, by rfl⟩ : syracuseStep 3326953 = 2495215) B2495215
theorem B71954729 : Blo 1313975 71954729 := bstep (se 2 (by rfl) ⟨26983023, by rfl⟩ : syracuseStep 71954729 = 53966047) B53966047
theorem B7484507 : Blo 1313975 7484507 := bstep (se 1 (by rfl) ⟨5613380, by rfl⟩ : syracuseStep 7484507 = 11226761) B11226761
theorem B5995775 : Blo 1313975 5995775 := bstep (se 1 (by rfl) ⟨4496831, by rfl⟩ : syracuseStep 5995775 = 8993663) B8993663
theorem B22781843 : Blo 1313975 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B4989671 : Blo 1313975 4989671 := bstep (se 1 (by rfl) ⟨3742253, by rfl⟩ : syracuseStep 4989671 = 7484507) B7484507
theorem B15993053 : Blo 1313975 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B4435937 : Blo 1313975 4435937 := bstep (se 2 (by rfl) ⟨1663476, by rfl⟩ : syracuseStep 4435937 = 3326953) B3326953
theorem B47969819 : Blo 1313975 47969819 := bstep (se 1 (by rfl) ⟨35977364, by rfl⟩ : syracuseStep 47969819 = 71954729) B71954729
theorem B3997183 : Blo 1313975 3997183 := bstep (se 1 (by rfl) ⟨2997887, by rfl⟩ : syracuseStep 3997183 = 5995775) B5995775
theorem B15187895 : Blo 1313975 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B3326447 : Blo 1313975 3326447 := bstep (se 1 (by rfl) ⟨2494835, by rfl⟩ : syracuseStep 3326447 = 4989671) B4989671
theorem B10662035 : Blo 1313975 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B5329577 : Blo 1313975 5329577 := bstep (se 2 (by rfl) ⟨1998591, by rfl⟩ : syracuseStep 5329577 = 3997183) B3997183
theorem B31979879 : Blo 1313975 31979879 := bstep (se 1 (by rfl) ⟨23984909, by rfl⟩ : syracuseStep 31979879 = 47969819) B47969819
theorem B10125263 : Blo 1313975 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B2957291 : Blo 1313975 2957291 := bstep (se 1 (by rfl) ⟨2217968, by rfl⟩ : syracuseStep 2957291 = 4435937) B4435937
theorem B21319919 : Blo 1313975 21319919 := bstep (se 1 (by rfl) ⟨15989939, by rfl⟩ : syracuseStep 21319919 = 31979879) B31979879
theorem B1971527 : Blo 1313975 1971527 := bstep (se 1 (by rfl) ⟨1478645, by rfl⟩ : syracuseStep 1971527 = 2957291) B2957291
theorem B2217631 : Blo 1313975 2217631 := bstep (se 1 (by rfl) ⟨1663223, by rfl⟩ : syracuseStep 2217631 = 3326447) B3326447
theorem B113728373 : Blo 1313975 113728373 := bstep (se 5 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 113728373 = 10662035) B10662035
theorem B14212205 : Blo 1313975 14212205 := bstep (se 3 (by rfl) ⟨2664788, by rfl⟩ : syracuseStep 14212205 = 5329577) B5329577
theorem B27000701 : Blo 1313975 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B14213279 : Blo 1313975 14213279 := bstep (se 1 (by rfl) ⟨10659959, by rfl⟩ : syracuseStep 14213279 = 21319919) B21319919
theorem B75818915 : Blo 1313975 75818915 := bstep (se 1 (by rfl) ⟨56864186, by rfl⟩ : syracuseStep 75818915 = 113728373) B113728373
theorem B18000467 : Blo 1313975 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B1314351 : Blo 1313975 1314351 := bstep (se 1 (by rfl) ⟨985763, by rfl⟩ : syracuseStep 1314351 = 1971527) B1971527
theorem B9474803 : Blo 1313975 9474803 := bstep (se 1 (by rfl) ⟨7106102, by rfl⟩ : syracuseStep 9474803 = 14212205) B14212205
theorem B2956841 : Blo 1313975 2956841 := bstep (se 2 (by rfl) ⟨1108815, by rfl⟩ : syracuseStep 2956841 = 2217631) B2217631
theorem B6316535 : Blo 1313975 6316535 := bstep (se 1 (by rfl) ⟨4737401, by rfl⟩ : syracuseStep 6316535 = 9474803) B9474803
theorem B50545943 : Blo 1313975 50545943 := bstep (se 1 (by rfl) ⟨37909457, by rfl⟩ : syracuseStep 50545943 = 75818915) B75818915
theorem B1971227 : Blo 1313975 1971227 := bstep (se 1 (by rfl) ⟨1478420, by rfl⟩ : syracuseStep 1971227 = 2956841) B2956841
theorem B37902077 : Blo 1313975 37902077 := bstep (se 3 (by rfl) ⟨7106639, by rfl⟩ : syracuseStep 37902077 = 14213279) B14213279
theorem B12000311 : Blo 1313975 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B4211023 : Blo 1313975 4211023 := bstep (se 1 (by rfl) ⟨3158267, by rfl⟩ : syracuseStep 4211023 = 6316535) B6316535
theorem B1314151 : Blo 1313975 1314151 := bstep (se 1 (by rfl) ⟨985613, by rfl⟩ : syracuseStep 1314151 = 1971227) B1971227
theorem B33697295 : Blo 1313975 33697295 := bstep (se 1 (by rfl) ⟨25272971, by rfl⟩ : syracuseStep 33697295 = 50545943) B50545943
theorem B25268051 : Blo 1313975 25268051 := bstep (se 1 (by rfl) ⟨18951038, by rfl⟩ : syracuseStep 25268051 = 37902077) B37902077
theorem B8000207 : Blo 1313975 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B5333471 : Blo 1313975 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B22464863 : Blo 1313975 22464863 := bstep (se 1 (by rfl) ⟨16848647, by rfl⟩ : syracuseStep 22464863 = 33697295) B33697295
theorem B16845367 : Blo 1313975 16845367 := bstep (se 1 (by rfl) ⟨12634025, by rfl⟩ : syracuseStep 16845367 = 25268051) B25268051
theorem B5614697 : Blo 1313975 5614697 := bstep (se 2 (by rfl) ⟨2105511, by rfl⟩ : syracuseStep 5614697 = 4211023) B4211023
theorem B3555647 : Blo 1313975 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B14976575 : Blo 1313975 14976575 := bstep (se 1 (by rfl) ⟨11232431, by rfl⟩ : syracuseStep 14976575 = 22464863) B22464863
theorem B22460489 : Blo 1313975 22460489 := bstep (se 2 (by rfl) ⟨8422683, by rfl⟩ : syracuseStep 22460489 = 16845367) B16845367
theorem B3743131 : Blo 1313975 3743131 := bstep (se 1 (by rfl) ⟨2807348, by rfl⟩ : syracuseStep 3743131 = 5614697) B5614697
theorem B4990841 : Blo 1313975 4990841 := bstep (se 2 (by rfl) ⟨1871565, by rfl⟩ : syracuseStep 4990841 = 3743131) B3743131
theorem B2370431 : Blo 1313975 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B9984383 : Blo 1313975 9984383 := bstep (se 1 (by rfl) ⟨7488287, by rfl⟩ : syracuseStep 9984383 = 14976575) B14976575
theorem B14973659 : Blo 1313975 14973659 := bstep (se 1 (by rfl) ⟨11230244, by rfl⟩ : syracuseStep 14973659 = 22460489) B22460489
theorem B3327227 : Blo 1313975 3327227 := bstep (se 1 (by rfl) ⟨2495420, by rfl⟩ : syracuseStep 3327227 = 4990841) B4990841
theorem B6656255 : Blo 1313975 6656255 := bstep (se 1 (by rfl) ⟨4992191, by rfl⟩ : syracuseStep 6656255 = 9984383) B9984383
theorem B9982439 : Blo 1313975 9982439 := bstep (se 1 (by rfl) ⟨7486829, by rfl⟩ : syracuseStep 9982439 = 14973659) B14973659
theorem B6321149 : Blo 1313975 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B6654959 : Blo 1313975 6654959 := bstep (se 1 (by rfl) ⟨4991219, by rfl⟩ : syracuseStep 6654959 = 9982439) B9982439
theorem B4214099 : Blo 1313975 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B4437503 : Blo 1313975 4437503 := bstep (se 1 (by rfl) ⟨3328127, by rfl⟩ : syracuseStep 4437503 = 6656255) B6656255
theorem B2218151 : Blo 1313975 2218151 := bstep (se 1 (by rfl) ⟨1663613, by rfl⟩ : syracuseStep 2218151 = 3327227) B3327227
theorem B2958335 : Blo 1313975 2958335 := bstep (se 1 (by rfl) ⟨2218751, by rfl⟩ : syracuseStep 2958335 = 4437503) B4437503
theorem B1478767 : Blo 1313975 1478767 := bstep (se 1 (by rfl) ⟨1109075, by rfl⟩ : syracuseStep 1478767 = 2218151) B2218151
theorem B4436639 : Blo 1313975 4436639 := bstep (se 1 (by rfl) ⟨3327479, by rfl⟩ : syracuseStep 4436639 = 6654959) B6654959
theorem B2809399 : Blo 1313975 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B2957759 : Blo 1313975 2957759 := bstep (se 1 (by rfl) ⟨2218319, by rfl⟩ : syracuseStep 2957759 = 4436639) B4436639
theorem B3745865 : Blo 1313975 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B1971689 : Blo 1313975 1971689 := bstep (se 2 (by rfl) ⟨739383, by rfl⟩ : syracuseStep 1971689 = 1478767) B1478767
theorem B1972223 : Blo 1313975 1972223 := bstep (se 1 (by rfl) ⟨1479167, by rfl⟩ : syracuseStep 1972223 = 2958335) B2958335
theorem B1314459 : Blo 1313975 1314459 := bstep (se 1 (by rfl) ⟨985844, by rfl⟩ : syracuseStep 1314459 = 1971689) B1971689
theorem B1314815 : Blo 1313975 1314815 := bstep (se 1 (by rfl) ⟨986111, by rfl⟩ : syracuseStep 1314815 = 1972223) B1972223
theorem B1971839 : Blo 1313975 1971839 := bstep (se 1 (by rfl) ⟨1478879, by rfl⟩ : syracuseStep 1971839 = 2957759) B2957759
theorem B2497243 : Blo 1313975 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B3329657 : Blo 1313975 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B1314559 : Blo 1313975 1314559 := bstep (se 1 (by rfl) ⟨985919, by rfl⟩ : syracuseStep 1314559 = 1971839) B1971839
theorem B2219771 : Blo 1313975 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B1479847 : Blo 1313975 1479847 := bstep (se 1 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 1479847 = 2219771) B2219771
theorem B1973129 : Blo 1313975 1973129 := bstep (se 2 (by rfl) ⟨739923, by rfl⟩ : syracuseStep 1973129 = 1479847) B1479847
theorem B1315419 : Blo 1313975 1315419 := bstep (se 1 (by rfl) ⟨986564, by rfl⟩ : syracuseStep 1315419 = 1973129) B1973129

theorem C0 (j : ℕ) (h1 : 328493 ≤ j) (h2 : j ≤ 328993) : Blo 1313975 (4 * j + 3) := by
  interval_cases j
  · exact B1313975
  · exact B1313979
  · exact B1313983
  · exact B1313987
  · exact B1313991
  · exact B1313995
  · exact B1313999
  · exact B1314003
  · exact B1314007
  · exact B1314011
  · exact B1314015
  · exact B1314019
  · exact B1314023
  · exact B1314027
  · exact B1314031
  · exact B1314035
  · exact B1314039
  · exact B1314043
  · exact B1314047
  · exact B1314051
  · exact B1314055
  · exact B1314059
  · exact B1314063
  · exact B1314067
  · exact B1314071
  · exact B1314075
  · exact B1314079
  · exact B1314083
  · exact B1314087
  · exact B1314091
  · exact B1314095
  · exact B1314099
  · exact B1314103
  · exact B1314107
  · exact B1314111
  · exact B1314115
  · exact B1314119
  · exact B1314123
  · exact B1314127
  · exact B1314131
  · exact B1314135
  · exact B1314139
  · exact B1314143
  · exact B1314147
  · exact B1314151
  · exact B1314155
  · exact B1314159
  · exact B1314163
  · exact B1314167
  · exact B1314171
  · exact B1314175
  · exact B1314179
  · exact B1314183
  · exact B1314187
  · exact B1314191
  · exact B1314195
  · exact B1314199
  · exact B1314203
  · exact B1314207
  · exact B1314211
  · exact B1314215
  · exact B1314219
  · exact B1314223
  · exact B1314227
  · exact B1314231
  · exact B1314235
  · exact B1314239
  · exact B1314243
  · exact B1314247
  · exact B1314251
  · exact B1314255
  · exact B1314259
  · exact B1314263
  · exact B1314267
  · exact B1314271
  · exact B1314275
  · exact B1314279
  · exact B1314283
  · exact B1314287
  · exact B1314291
  · exact B1314295
  · exact B1314299
  · exact B1314303
  · exact B1314307
  · exact B1314311
  · exact B1314315
  · exact B1314319
  · exact B1314323
  · exact B1314327
  · exact B1314331
  · exact B1314335
  · exact B1314339
  · exact B1314343
  · exact B1314347
  · exact B1314351
  · exact B1314355
  · exact B1314359
  · exact B1314363
  · exact B1314367
  · exact B1314371
  · exact B1314375
  · exact B1314379
  · exact B1314383
  · exact B1314387
  · exact B1314391
  · exact B1314395
  · exact B1314399
  · exact B1314403
  · exact B1314407
  · exact B1314411
  · exact B1314415
  · exact B1314419
  · exact B1314423
  · exact B1314427
  · exact B1314431
  · exact B1314435
  · exact B1314439
  · exact B1314443
  · exact B1314447
  · exact B1314451
  · exact B1314455
  · exact B1314459
  · exact B1314463
  · exact B1314467
  · exact B1314471
  · exact B1314475
  · exact B1314479
  · exact B1314483
  · exact B1314487
  · exact B1314491
  · exact B1314495
  · exact B1314499
  · exact B1314503
  · exact B1314507
  · exact B1314511
  · exact B1314515
  · exact B1314519
  · exact B1314523
  · exact B1314527
  · exact B1314531
  · exact B1314535
  · exact B1314539
  · exact B1314543
  · exact B1314547
  · exact B1314551
  · exact B1314555
  · exact B1314559
  · exact B1314563
  · exact B1314567
  · exact B1314571
  · exact B1314575
  · exact B1314579
  · exact B1314583
  · exact B1314587
  · exact B1314591
  · exact B1314595
  · exact B1314599
  · exact B1314603
  · exact B1314607
  · exact B1314611
  · exact B1314615
  · exact B1314619
  · exact B1314623
  · exact B1314627
  · exact B1314631
  · exact B1314635
  · exact B1314639
  · exact B1314643
  · exact B1314647
  · exact B1314651
  · exact B1314655
  · exact B1314659
  · exact B1314663
  · exact B1314667
  · exact B1314671
  · exact B1314675
  · exact B1314679
  · exact B1314683
  · exact B1314687
  · exact B1314691
  · exact B1314695
  · exact B1314699
  · exact B1314703
  · exact B1314707
  · exact B1314711
  · exact B1314715
  · exact B1314719
  · exact B1314723
  · exact B1314727
  · exact B1314731
  · exact B1314735
  · exact B1314739
  · exact B1314743
  · exact B1314747
  · exact B1314751
  · exact B1314755
  · exact B1314759
  · exact B1314763
  · exact B1314767
  · exact B1314771
  · exact B1314775
  · exact B1314779
  · exact B1314783
  · exact B1314787
  · exact B1314791
  · exact B1314795
  · exact B1314799
  · exact B1314803
  · exact B1314807
  · exact B1314811
  · exact B1314815
  · exact B1314819
  · exact B1314823
  · exact B1314827
  · exact B1314831
  · exact B1314835
  · exact B1314839
  · exact B1314843
  · exact B1314847
  · exact B1314851
  · exact B1314855
  · exact B1314859
  · exact B1314863
  · exact B1314867
  · exact B1314871
  · exact B1314875
  · exact B1314879
  · exact B1314883
  · exact B1314887
  · exact B1314891
  · exact B1314895
  · exact B1314899
  · exact B1314903
  · exact B1314907
  · exact B1314911
  · exact B1314915
  · exact B1314919
  · exact B1314923
  · exact B1314927
  · exact B1314931
  · exact B1314935
  · exact B1314939
  · exact B1314943
  · exact B1314947
  · exact B1314951
  · exact B1314955
  · exact B1314959
  · exact B1314963
  · exact B1314967
  · exact B1314971
  · exact B1314975
  · exact B1314979
  · exact B1314983
  · exact B1314987
  · exact B1314991
  · exact B1314995
  · exact B1314999
  · exact B1315003
  · exact B1315007
  · exact B1315011
  · exact B1315015
  · exact B1315019
  · exact B1315023
  · exact B1315027
  · exact B1315031
  · exact B1315035
  · exact B1315039
  · exact B1315043
  · exact B1315047
  · exact B1315051
  · exact B1315055
  · exact B1315059
  · exact B1315063
  · exact B1315067
  · exact B1315071
  · exact B1315075
  · exact B1315079
  · exact B1315083
  · exact B1315087
  · exact B1315091
  · exact B1315095
  · exact B1315099
  · exact B1315103
  · exact B1315107
  · exact B1315111
  · exact B1315115
  · exact B1315119
  · exact B1315123
  · exact B1315127
  · exact B1315131
  · exact B1315135
  · exact B1315139
  · exact B1315143
  · exact B1315147
  · exact B1315151
  · exact B1315155
  · exact B1315159
  · exact B1315163
  · exact B1315167
  · exact B1315171
  · exact B1315175
  · exact B1315179
  · exact B1315183
  · exact B1315187
  · exact B1315191
  · exact B1315195
  · exact B1315199
  · exact B1315203
  · exact B1315207
  · exact B1315211
  · exact B1315215
  · exact B1315219
  · exact B1315223
  · exact B1315227
  · exact B1315231
  · exact B1315235
  · exact B1315239
  · exact B1315243
  · exact B1315247
  · exact B1315251
  · exact B1315255
  · exact B1315259
  · exact B1315263
  · exact B1315267
  · exact B1315271
  · exact B1315275
  · exact B1315279
  · exact B1315283
  · exact B1315287
  · exact B1315291
  · exact B1315295
  · exact B1315299
  · exact B1315303
  · exact B1315307
  · exact B1315311
  · exact B1315315
  · exact B1315319
  · exact B1315323
  · exact B1315327
  · exact B1315331
  · exact B1315335
  · exact B1315339
  · exact B1315343
  · exact B1315347
  · exact B1315351
  · exact B1315355
  · exact B1315359
  · exact B1315363
  · exact B1315367
  · exact B1315371
  · exact B1315375
  · exact B1315379
  · exact B1315383
  · exact B1315387
  · exact B1315391
  · exact B1315395
  · exact B1315399
  · exact B1315403
  · exact B1315407
  · exact B1315411
  · exact B1315415
  · exact B1315419
  · exact B1315423
  · exact B1315427
  · exact B1315431
  · exact B1315435
  · exact B1315439
  · exact B1315443
  · exact B1315447
  · exact B1315451
  · exact B1315455
  · exact B1315459
  · exact B1315463
  · exact B1315467
  · exact B1315471
  · exact B1315475
  · exact B1315479
  · exact B1315483
  · exact B1315487
  · exact B1315491
  · exact B1315495
  · exact B1315499
  · exact B1315503
  · exact B1315507
  · exact B1315511
  · exact B1315515
  · exact B1315519
  · exact B1315523
  · exact B1315527
  · exact B1315531
  · exact B1315535
  · exact B1315539
  · exact B1315543
  · exact B1315547
  · exact B1315551
  · exact B1315555
  · exact B1315559
  · exact B1315563
  · exact B1315567
  · exact B1315571
  · exact B1315575
  · exact B1315579
  · exact B1315583
  · exact B1315587
  · exact B1315591
  · exact B1315595
  · exact B1315599
  · exact B1315603
  · exact B1315607
  · exact B1315611
  · exact B1315615
  · exact B1315619
  · exact B1315623
  · exact B1315627
  · exact B1315631
  · exact B1315635
  · exact B1315639
  · exact B1315643
  · exact B1315647
  · exact B1315651
  · exact B1315655
  · exact B1315659
  · exact B1315663
  · exact B1315667
  · exact B1315671
  · exact B1315675
  · exact B1315679
  · exact B1315683
  · exact B1315687
  · exact B1315691
  · exact B1315695
  · exact B1315699
  · exact B1315703
  · exact B1315707
  · exact B1315711
  · exact B1315715
  · exact B1315719
  · exact B1315723
  · exact B1315727
  · exact B1315731
  · exact B1315735
  · exact B1315739
  · exact B1315743
  · exact B1315747
  · exact B1315751
  · exact B1315755
  · exact B1315759
  · exact B1315763
  · exact B1315767
  · exact B1315771
  · exact B1315775
  · exact B1315779
  · exact B1315783
  · exact B1315787
  · exact B1315791
  · exact B1315795
  · exact B1315799
  · exact B1315803
  · exact B1315807
  · exact B1315811
  · exact B1315815
  · exact B1315819
  · exact B1315823
  · exact B1315827
  · exact B1315831
  · exact B1315835
  · exact B1315839
  · exact B1315843
  · exact B1315847
  · exact B1315851
  · exact B1315855
  · exact B1315859
  · exact B1315863
  · exact B1315867
  · exact B1315871
  · exact B1315875
  · exact B1315879
  · exact B1315883
  · exact B1315887
  · exact B1315891
  · exact B1315895
  · exact B1315899
  · exact B1315903
  · exact B1315907
  · exact B1315911
  · exact B1315915
  · exact B1315919
  · exact B1315923
  · exact B1315927
  · exact B1315931
  · exact B1315935
  · exact B1315939
  · exact B1315943
  · exact B1315947
  · exact B1315951
  · exact B1315955
  · exact B1315959
  · exact B1315963
  · exact B1315967
  · exact B1315971
  · exact B1315975

theorem solution (m : ℕ) (hlo : 1313975 ≤ m) (hhi : m ≤ 1315975) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 328493 ≤ j := by omega
    have hj2 : j ≤ 328993 := by omega
    have hb : Blo 1313975 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
