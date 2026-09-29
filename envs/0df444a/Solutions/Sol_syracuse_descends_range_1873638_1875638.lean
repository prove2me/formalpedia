-- Prove2me | solution 1 for syracuse_descends_range_1873638_1875638
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:14:53.837056+00:00
-- url     : https://prove2.me/submissions/f699f892-0917-4a35-aada-6cdc5c0d44a0

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


theorem B3162125 : Blo 1873638 3162125 := bbase (se 3 (by rfl) ⟨592898, by rfl⟩ : syracuseStep 3162125 = 1185797) (by norm_num)
theorem B4218893 : Blo 1873638 4218893 := bbase (se 3 (by rfl) ⟨791042, by rfl⟩ : syracuseStep 4218893 = 1582085) (by norm_num)
theorem B4218965 : Blo 1873638 4218965 := bbase (se 8 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 4218965 = 49441) (by norm_num)
theorem B3801181 : Blo 1873638 3801181 := bbase (se 3 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 3801181 = 1425443) (by norm_num)
theorem B4743269 : Blo 1873638 4743269 := bbase (se 4 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 4743269 = 889363) (by norm_num)
theorem B3162253 : Blo 1873638 3162253 := bbase (se 3 (by rfl) ⟨592922, by rfl⟩ : syracuseStep 3162253 = 1185845) (by norm_num)
theorem B4219037 : Blo 1873638 4219037 := bbase (se 3 (by rfl) ⟨791069, by rfl⟩ : syracuseStep 4219037 = 1582139) (by norm_num)
theorem B3801277 : Blo 1873638 3801277 := bbase (se 3 (by rfl) ⟨712739, by rfl⟩ : syracuseStep 3801277 = 1425479) (by norm_num)
theorem B3162341 : Blo 1873638 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B4219109 : Blo 1873638 4219109 := bbase (se 4 (by rfl) ⟨395541, by rfl⟩ : syracuseStep 4219109 = 791083) (by norm_num)
theorem B4743461 : Blo 1873638 4743461 := bbase (se 4 (by rfl) ⟨444699, by rfl⟩ : syracuseStep 4743461 = 889399) (by norm_num)
theorem B4219181 : Blo 1873638 4219181 := bbase (se 3 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 4219181 = 1582193) (by norm_num)
theorem B6324533 : Blo 1873638 6324533 := bbase (se 5 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 6324533 = 592925) (by norm_num)
theorem B4276565 : Blo 1873638 4276565 := bbase (se 10 (by rfl) ⟨6264, by rfl⟩ : syracuseStep 4276565 = 12529) (by norm_num)
theorem B3162469 : Blo 1873638 3162469 := bbase (se 4 (by rfl) ⟨296481, by rfl⟩ : syracuseStep 3162469 = 592963) (by norm_num)
theorem B6414709 : Blo 1873638 6414709 := bbase (se 5 (by rfl) ⟨300689, by rfl⟩ : syracuseStep 6414709 = 601379) (by norm_num)
theorem B4219253 : Blo 1873638 4219253 := bbase (se 5 (by rfl) ⟨197777, by rfl⟩ : syracuseStep 4219253 = 395555) (by norm_num)
theorem B3162557 : Blo 1873638 3162557 := bbase (se 3 (by rfl) ⟨592979, by rfl⟩ : syracuseStep 3162557 = 1185959) (by norm_num)
theorem B4219325 : Blo 1873638 4219325 := bbase (se 3 (by rfl) ⟨791123, by rfl⟩ : syracuseStep 4219325 = 1582247) (by norm_num)
theorem B9494981 : Blo 1873638 9494981 := bbase (se 4 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 9494981 = 1780309) (by norm_num)
theorem B6414821 : Blo 1873638 6414821 := bbase (se 4 (by rfl) ⟨601389, by rfl⟩ : syracuseStep 6414821 = 1202779) (by norm_num)
theorem B4506101 : Blo 1873638 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B4219397 : Blo 1873638 4219397 := bbase (se 4 (by rfl) ⟨395568, by rfl⟩ : syracuseStep 4219397 = 791137) (by norm_num)
theorem B3162685 : Blo 1873638 3162685 := bbase (se 3 (by rfl) ⟨593003, by rfl⟩ : syracuseStep 3162685 = 1186007) (by norm_num)
theorem B4219469 : Blo 1873638 4219469 := bbase (se 3 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 4219469 = 1582301) (by norm_num)
theorem B2810477 : Blo 1873638 2810477 := bbase (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) (by norm_num)
theorem B8553077 : Blo 1873638 8553077 := bbase (se 5 (by rfl) ⟨400925, by rfl⟩ : syracuseStep 8553077 = 801851) (by norm_num)
theorem B4743805 : Blo 1873638 4743805 := bbase (se 3 (by rfl) ⟨889463, by rfl⟩ : syracuseStep 4743805 = 1778927) (by norm_num)
theorem B2810501 : Blo 1873638 2810501 := bbase (se 4 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 2810501 = 526969) (by norm_num)
theorem B3162773 : Blo 1873638 3162773 := bbase (se 6 (by rfl) ⟨74127, by rfl⟩ : syracuseStep 3162773 = 148255) (by norm_num)
theorem B4219541 : Blo 1873638 4219541 := bbase (se 6 (by rfl) ⟨98895, by rfl⟩ : syracuseStep 4219541 = 197791) (by norm_num)
theorem B2810525 : Blo 1873638 2810525 := bbase (se 3 (by rfl) ⟨526973, by rfl⟩ : syracuseStep 2810525 = 1053947) (by norm_num)
theorem B2810549 : Blo 1873638 2810549 := bbase (se 5 (by rfl) ⟨131744, by rfl⟩ : syracuseStep 2810549 = 263489) (by norm_num)
theorem B9011893 : Blo 1873638 9011893 := bbase (se 5 (by rfl) ⟨422432, by rfl⟩ : syracuseStep 9011893 = 844865) (by norm_num)
theorem B4506293 : Blo 1873638 4506293 := bbase (se 5 (by rfl) ⟨211232, by rfl⟩ : syracuseStep 4506293 = 422465) (by norm_num)
theorem B2810573 : Blo 1873638 2810573 := bbase (se 3 (by rfl) ⟨526982, by rfl⟩ : syracuseStep 2810573 = 1053965) (by norm_num)
theorem B4219613 : Blo 1873638 4219613 := bbase (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) (by norm_num)
theorem B2810597 : Blo 1873638 2810597 := bbase (se 4 (by rfl) ⟨263493, by rfl⟩ : syracuseStep 2810597 = 526987) (by norm_num)
theorem B6324965 : Blo 1873638 6324965 := bbase (se 4 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 6324965 = 1185931) (by norm_num)
theorem B3801829 : Blo 1873638 3801829 := bbase (se 4 (by rfl) ⟨356421, by rfl⟩ : syracuseStep 3801829 = 712843) (by norm_num)
theorem B4743917 : Blo 1873638 4743917 := bbase (se 3 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 4743917 = 1778969) (by norm_num)
theorem B2810621 : Blo 1873638 2810621 := bbase (se 3 (by rfl) ⟨526991, by rfl⟩ : syracuseStep 2810621 = 1053983) (by norm_num)
theorem B2810645 : Blo 1873638 2810645 := bbase (se 6 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 2810645 = 131749) (by norm_num)
theorem B3162901 : Blo 1873638 3162901 := bbase (se 6 (by rfl) ⟨74130, by rfl⟩ : syracuseStep 3162901 = 148261) (by norm_num)
theorem B4219685 : Blo 1873638 4219685 := bbase (se 4 (by rfl) ⟨395595, by rfl⟩ : syracuseStep 4219685 = 791191) (by norm_num)
theorem B2810669 : Blo 1873638 2810669 := bbase (se 3 (by rfl) ⟨527000, by rfl⟩ : syracuseStep 2810669 = 1054001) (by norm_num)
theorem B2810693 : Blo 1873638 2810693 := bbase (se 4 (by rfl) ⟨263502, by rfl⟩ : syracuseStep 2810693 = 527005) (by norm_num)
theorem B2810717 : Blo 1873638 2810717 := bbase (se 3 (by rfl) ⟨527009, by rfl⟩ : syracuseStep 2810717 = 1054019) (by norm_num)
theorem B9487205 : Blo 1873638 9487205 := bbase (se 4 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 9487205 = 1778851) (by norm_num)
theorem B5702501 : Blo 1873638 5702501 := bbase (se 4 (by rfl) ⟨534609, by rfl⟩ : syracuseStep 5702501 = 1069219) (by norm_num)
theorem B3162989 : Blo 1873638 3162989 := bbase (se 3 (by rfl) ⟨593060, by rfl⟩ : syracuseStep 3162989 = 1186121) (by norm_num)
theorem B4219757 : Blo 1873638 4219757 := bbase (se 3 (by rfl) ⟨791204, by rfl⟩ : syracuseStep 4219757 = 1582409) (by norm_num)
theorem B2810741 : Blo 1873638 2810741 := bbase (se 5 (by rfl) ⟨131753, by rfl⟩ : syracuseStep 2810741 = 263507) (by norm_num)
theorem B2810765 : Blo 1873638 2810765 := bbase (se 3 (by rfl) ⟨527018, by rfl⟩ : syracuseStep 2810765 = 1054037) (by norm_num)
theorem B2810789 : Blo 1873638 2810789 := bbase (se 4 (by rfl) ⟨263511, by rfl⟩ : syracuseStep 2810789 = 527023) (by norm_num)
theorem B4744109 : Blo 1873638 4744109 := bbase (se 3 (by rfl) ⟨889520, by rfl⟩ : syracuseStep 4744109 = 1779041) (by norm_num)
theorem B4219829 : Blo 1873638 4219829 := bbase (se 5 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 4219829 = 395609) (by norm_num)
theorem B2810813 : Blo 1873638 2810813 := bbase (se 3 (by rfl) ⟨527027, by rfl⟩ : syracuseStep 2810813 = 1054055) (by norm_num)
theorem B2810837 : Blo 1873638 2810837 := bbase (se 7 (by rfl) ⟨32939, by rfl⟩ : syracuseStep 2810837 = 65879) (by norm_num)
theorem B2810861 : Blo 1873638 2810861 := bbase (se 3 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 2810861 = 1054073) (by norm_num)
theorem B3163117 : Blo 1873638 3163117 := bbase (se 3 (by rfl) ⟨593084, by rfl⟩ : syracuseStep 3163117 = 1186169) (by norm_num)
theorem B4219901 : Blo 1873638 4219901 := bbase (se 3 (by rfl) ⟨791231, by rfl⟩ : syracuseStep 4219901 = 1582463) (by norm_num)
theorem B2810885 : Blo 1873638 2810885 := bbase (se 4 (by rfl) ⟨263520, by rfl⟩ : syracuseStep 2810885 = 527041) (by norm_num)
theorem B6005765 : Blo 1873638 6005765 := bbase (se 4 (by rfl) ⟨563040, by rfl⟩ : syracuseStep 6005765 = 1126081) (by norm_num)
theorem B2810909 : Blo 1873638 2810909 := bbase (se 3 (by rfl) ⟨527045, by rfl⟩ : syracuseStep 2810909 = 1054091) (by norm_num)
theorem B2810933 : Blo 1873638 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B7603253 : Blo 1873638 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B3163205 : Blo 1873638 3163205 := bbase (se 4 (by rfl) ⟨296550, by rfl⟩ : syracuseStep 3163205 = 593101) (by norm_num)
theorem B4219973 : Blo 1873638 4219973 := bbase (se 4 (by rfl) ⟨395622, by rfl⟩ : syracuseStep 4219973 = 791245) (by norm_num)
theorem B2810957 : Blo 1873638 2810957 := bbase (se 3 (by rfl) ⟨527054, by rfl⟩ : syracuseStep 2810957 = 1054109) (by norm_num)
theorem B58491989 : Blo 1873638 58491989 := bbase (se 8 (by rfl) ⟨342726, by rfl⟩ : syracuseStep 58491989 = 685453) (by norm_num)
theorem B2810981 : Blo 1873638 2810981 := bbase (se 4 (by rfl) ⟨263529, by rfl⟩ : syracuseStep 2810981 = 527059) (by norm_num)
theorem B2811005 : Blo 1873638 2811005 := bbase (se 3 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 2811005 = 1054127) (by norm_num)
theorem B4220045 : Blo 1873638 4220045 := bbase (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) (by norm_num)
theorem B2811029 : Blo 1873638 2811029 := bbase (se 6 (by rfl) ⟨65883, by rfl⟩ : syracuseStep 2811029 = 131767) (by norm_num)
theorem B6325397 : Blo 1873638 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B7120021 : Blo 1873638 7120021 := bbase (se 6 (by rfl) ⟨166875, by rfl⟩ : syracuseStep 7120021 = 333751) (by norm_num)
theorem B2811053 : Blo 1873638 2811053 := bbase (se 3 (by rfl) ⟨527072, by rfl⟩ : syracuseStep 2811053 = 1054145) (by norm_num)
theorem B2811077 : Blo 1873638 2811077 := bbase (se 4 (by rfl) ⟨263538, by rfl⟩ : syracuseStep 2811077 = 527077) (by norm_num)
theorem B3163333 : Blo 1873638 3163333 := bbase (se 4 (by rfl) ⟨296562, by rfl⟩ : syracuseStep 3163333 = 593125) (by norm_num)
theorem B4220117 : Blo 1873638 4220117 := bbase (se 7 (by rfl) ⟨49454, by rfl⟩ : syracuseStep 4220117 = 98909) (by norm_num)
theorem B2811101 : Blo 1873638 2811101 := bbase (se 3 (by rfl) ⟨527081, by rfl⟩ : syracuseStep 2811101 = 1054163) (by norm_num)
theorem B2811125 : Blo 1873638 2811125 := bbase (se 5 (by rfl) ⟨131771, by rfl⟩ : syracuseStep 2811125 = 263543) (by norm_num)
theorem B4744453 : Blo 1873638 4744453 := bbase (se 4 (by rfl) ⟨444792, by rfl⟩ : syracuseStep 4744453 = 889585) (by norm_num)
theorem B2811149 : Blo 1873638 2811149 := bbase (se 3 (by rfl) ⟨527090, by rfl⟩ : syracuseStep 2811149 = 1054181) (by norm_num)
theorem B3163421 : Blo 1873638 3163421 := bbase (se 3 (by rfl) ⟨593141, by rfl⟩ : syracuseStep 3163421 = 1186283) (by norm_num)
theorem B2811173 : Blo 1873638 2811173 := bbase (se 4 (by rfl) ⟨263547, by rfl⟩ : syracuseStep 2811173 = 527095) (by norm_num)
theorem B3802405 : Blo 1873638 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B2811197 : Blo 1873638 2811197 := bbase (se 3 (by rfl) ⟨527099, by rfl⟩ : syracuseStep 2811197 = 1054199) (by norm_num)
theorem B2811221 : Blo 1873638 2811221 := bbase (se 12 (by rfl) ⟨1029, by rfl⟩ : syracuseStep 2811221 = 2059) (by norm_num)
theorem B2811245 : Blo 1873638 2811245 := bbase (se 3 (by rfl) ⟨527108, by rfl⟩ : syracuseStep 2811245 = 1054217) (by norm_num)
theorem B4744565 : Blo 1873638 4744565 := bbase (se 5 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 4744565 = 444803) (by norm_num)
theorem B2811269 : Blo 1873638 2811269 := bbase (se 4 (by rfl) ⟨263556, by rfl⟩ : syracuseStep 2811269 = 527113) (by norm_num)
theorem B2811293 : Blo 1873638 2811293 := bbase (se 3 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 2811293 = 1054235) (by norm_num)
theorem B3163549 : Blo 1873638 3163549 := bbase (se 3 (by rfl) ⟨593165, by rfl⟩ : syracuseStep 3163549 = 1186331) (by norm_num)
theorem B2811317 : Blo 1873638 2811317 := bbase (se 5 (by rfl) ⟨131780, by rfl⟩ : syracuseStep 2811317 = 263561) (by norm_num)
theorem B10675637 : Blo 1873638 10675637 := bbase (se 5 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 10675637 = 1000841) (by norm_num)
theorem B7120325 : Blo 1873638 7120325 := bbase (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) (by norm_num)
theorem B2811341 : Blo 1873638 2811341 := bbase (se 3 (by rfl) ⟨527126, by rfl⟩ : syracuseStep 2811341 = 1054253) (by norm_num)
theorem B2811365 : Blo 1873638 2811365 := bbase (se 4 (by rfl) ⟨263565, by rfl⟩ : syracuseStep 2811365 = 527131) (by norm_num)
theorem B4335077 : Blo 1873638 4335077 := bbase (se 4 (by rfl) ⟨406413, by rfl⟩ : syracuseStep 4335077 = 812827) (by norm_num)
theorem B3163637 : Blo 1873638 3163637 := bbase (se 5 (by rfl) ⟨148295, by rfl⟩ : syracuseStep 3163637 = 296591) (by norm_num)
theorem B2811389 : Blo 1873638 2811389 := bbase (se 3 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 2811389 = 1054271) (by norm_num)
theorem B2811413 : Blo 1873638 2811413 := bbase (se 6 (by rfl) ⟨65892, by rfl⟩ : syracuseStep 2811413 = 131785) (by norm_num)
theorem B2811437 : Blo 1873638 2811437 := bbase (se 3 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 2811437 = 1054289) (by norm_num)
theorem B4744757 : Blo 1873638 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B2811461 : Blo 1873638 2811461 := bbase (se 4 (by rfl) ⟨263574, by rfl⟩ : syracuseStep 2811461 = 527149) (by norm_num)
theorem B6325829 : Blo 1873638 6325829 := bbase (se 4 (by rfl) ⟨593046, by rfl⟩ : syracuseStep 6325829 = 1186093) (by norm_num)
theorem B2811485 : Blo 1873638 2811485 := bbase (se 3 (by rfl) ⟨527153, by rfl⟩ : syracuseStep 2811485 = 1054307) (by norm_num)
theorem B2705005 : Blo 1873638 2705005 := bbase (se 3 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 2705005 = 1014377) (by norm_num)
theorem B2811509 : Blo 1873638 2811509 := bbase (se 5 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 2811509 = 263579) (by norm_num)
theorem B3163765 : Blo 1873638 3163765 := bbase (se 5 (by rfl) ⟨148301, by rfl⟩ : syracuseStep 3163765 = 296603) (by norm_num)
theorem B2811533 : Blo 1873638 2811533 := bbase (se 3 (by rfl) ⟨527162, by rfl⟩ : syracuseStep 2811533 = 1054325) (by norm_num)
theorem B2811557 : Blo 1873638 2811557 := bbase (se 4 (by rfl) ⟨263583, by rfl⟩ : syracuseStep 2811557 = 527167) (by norm_num)
theorem B2811581 : Blo 1873638 2811581 := bbase (se 3 (by rfl) ⟨527171, by rfl⟩ : syracuseStep 2811581 = 1054343) (by norm_num)
theorem B3163853 : Blo 1873638 3163853 := bbase (se 3 (by rfl) ⟨593222, by rfl⟩ : syracuseStep 3163853 = 1186445) (by norm_num)
theorem B2811605 : Blo 1873638 2811605 := bbase (se 7 (by rfl) ⟨32948, by rfl⟩ : syracuseStep 2811605 = 65897) (by norm_num)
theorem B14436053 : Blo 1873638 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B2811629 : Blo 1873638 2811629 := bbase (se 3 (by rfl) ⟨527180, by rfl⟩ : syracuseStep 2811629 = 1054361) (by norm_num)
theorem B19244789 : Blo 1873638 19244789 := bbase (se 5 (by rfl) ⟨902099, by rfl⟩ : syracuseStep 19244789 = 1804199) (by norm_num)
theorem B3557125 : Blo 1873638 3557125 := bbase (se 4 (by rfl) ⟨333480, by rfl⟩ : syracuseStep 3557125 = 666961) (by norm_num)
theorem B2811653 : Blo 1873638 2811653 := bbase (se 4 (by rfl) ⟨263592, by rfl⟩ : syracuseStep 2811653 = 527185) (by norm_num)
theorem B2197253 : Blo 1873638 2197253 := bbase (se 4 (by rfl) ⟨205992, by rfl⟩ : syracuseStep 2197253 = 411985) (by norm_num)
theorem B2811677 : Blo 1873638 2811677 := bbase (se 3 (by rfl) ⟨527189, by rfl⟩ : syracuseStep 2811677 = 1054379) (by norm_num)
theorem B2811701 : Blo 1873638 2811701 := bbase (se 5 (by rfl) ⟨131798, by rfl⟩ : syracuseStep 2811701 = 263597) (by norm_num)
theorem B2811725 : Blo 1873638 2811725 := bbase (se 3 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 2811725 = 1054397) (by norm_num)
theorem B3163981 : Blo 1873638 3163981 := bbase (se 3 (by rfl) ⟨593246, by rfl⟩ : syracuseStep 3163981 = 1186493) (by norm_num)
theorem B3376981 : Blo 1873638 3376981 := bbase (se 9 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 3376981 = 19787) (by norm_num)
theorem B3606365 : Blo 1873638 3606365 := bbase (se 3 (by rfl) ⟨676193, by rfl⟩ : syracuseStep 3606365 = 1352387) (by norm_num)
theorem B2811749 : Blo 1873638 2811749 := bbase (se 4 (by rfl) ⟨263601, by rfl⟩ : syracuseStep 2811749 = 527203) (by norm_num)
theorem B8669045 : Blo 1873638 8669045 := bbase (se 5 (by rfl) ⟨406361, by rfl⟩ : syracuseStep 8669045 = 812723) (by norm_num)
theorem B2811773 : Blo 1873638 2811773 := bbase (se 3 (by rfl) ⟨527207, by rfl⟩ : syracuseStep 2811773 = 1054415) (by norm_num)
theorem B4745101 : Blo 1873638 4745101 := bbase (se 3 (by rfl) ⟨889706, by rfl⟩ : syracuseStep 4745101 = 1779413) (by norm_num)
theorem B2811797 : Blo 1873638 2811797 := bbase (se 6 (by rfl) ⟨65901, by rfl⟩ : syracuseStep 2811797 = 131803) (by norm_num)
theorem B8120213 : Blo 1873638 8120213 := bbase (se 6 (by rfl) ⟨190317, by rfl⟩ : syracuseStep 8120213 = 380635) (by norm_num)
theorem B3377053 : Blo 1873638 3377053 := bbase (se 3 (by rfl) ⟨633197, by rfl⟩ : syracuseStep 3377053 = 1266395) (by norm_num)
theorem B3164069 : Blo 1873638 3164069 := bbase (se 4 (by rfl) ⟨296631, by rfl⟩ : syracuseStep 3164069 = 593263) (by norm_num)
theorem B2811821 : Blo 1873638 2811821 := bbase (se 3 (by rfl) ⟨527216, by rfl⟩ : syracuseStep 2811821 = 1054433) (by norm_num)
theorem B2811845 : Blo 1873638 2811845 := bbase (se 4 (by rfl) ⟨263610, by rfl⟩ : syracuseStep 2811845 = 527221) (by norm_num)
theorem B2811869 : Blo 1873638 2811869 := bbase (se 3 (by rfl) ⟨527225, by rfl⟩ : syracuseStep 2811869 = 1054451) (by norm_num)
theorem B6326261 : Blo 1873638 6326261 := bbase (se 5 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 6326261 = 593087) (by norm_num)
theorem B2811893 : Blo 1873638 2811893 := bbase (se 5 (by rfl) ⟨131807, by rfl⟩ : syracuseStep 2811893 = 263615) (by norm_num)
theorem B4745213 : Blo 1873638 4745213 := bbase (se 3 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 4745213 = 1779455) (by norm_num)
theorem B2000909 : Blo 1873638 2000909 := bbase (se 3 (by rfl) ⟨375170, by rfl⟩ : syracuseStep 2000909 = 750341) (by norm_num)
theorem B2811917 : Blo 1873638 2811917 := bbase (se 3 (by rfl) ⟨527234, by rfl⟩ : syracuseStep 2811917 = 1054469) (by norm_num)
theorem B9127973 : Blo 1873638 9127973 := bbase (se 4 (by rfl) ⟨855747, by rfl⟩ : syracuseStep 9127973 = 1711495) (by norm_num)
theorem B2811941 : Blo 1873638 2811941 := bbase (se 4 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 2811941 = 527239) (by norm_num)
theorem B3164197 : Blo 1873638 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B3557429 : Blo 1873638 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B2811965 : Blo 1873638 2811965 := bbase (se 3 (by rfl) ⟨527243, by rfl⟩ : syracuseStep 2811965 = 1054487) (by norm_num)
theorem B2811989 : Blo 1873638 2811989 := bbase (se 8 (by rfl) ⟨16476, by rfl⟩ : syracuseStep 2811989 = 32953) (by norm_num)
theorem B2812013 : Blo 1873638 2812013 := bbase (se 3 (by rfl) ⟨527252, by rfl⟩ : syracuseStep 2812013 = 1054505) (by norm_num)
theorem B9488501 : Blo 1873638 9488501 := bbase (se 5 (by rfl) ⟨444773, by rfl⟩ : syracuseStep 9488501 = 889547) (by norm_num)
theorem B3164285 : Blo 1873638 3164285 := bbase (se 3 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 3164285 = 1186607) (by norm_num)
theorem B2812037 : Blo 1873638 2812037 := bbase (se 4 (by rfl) ⟨263628, by rfl⟩ : syracuseStep 2812037 = 527257) (by norm_num)
theorem B2812061 : Blo 1873638 2812061 := bbase (se 3 (by rfl) ⟨527261, by rfl⟩ : syracuseStep 2812061 = 1054523) (by norm_num)
theorem B2812085 : Blo 1873638 2812085 := bbase (se 5 (by rfl) ⟨131816, by rfl⟩ : syracuseStep 2812085 = 263633) (by norm_num)
theorem B4745405 : Blo 1873638 4745405 := bbase (se 3 (by rfl) ⟨889763, by rfl⟩ : syracuseStep 4745405 = 1779527) (by norm_num)
theorem B2812109 : Blo 1873638 2812109 := bbase (se 3 (by rfl) ⟨527270, by rfl⟩ : syracuseStep 2812109 = 1054541) (by norm_num)
theorem B2812133 : Blo 1873638 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B2812157 : Blo 1873638 2812157 := bbase (se 3 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 2812157 = 1054559) (by norm_num)
theorem B3164413 : Blo 1873638 3164413 := bbase (se 3 (by rfl) ⟨593327, by rfl⟩ : syracuseStep 3164413 = 1186655) (by norm_num)
theorem B2812181 : Blo 1873638 2812181 := bbase (se 6 (by rfl) ⟨65910, by rfl⟩ : syracuseStep 2812181 = 131821) (by norm_num)
theorem B2812205 : Blo 1873638 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B2812229 : Blo 1873638 2812229 := bbase (se 4 (by rfl) ⟨263646, by rfl⟩ : syracuseStep 2812229 = 527293) (by norm_num)
theorem B3164501 : Blo 1873638 3164501 := bbase (se 10 (by rfl) ⟨4635, by rfl⟩ : syracuseStep 3164501 = 9271) (by norm_num)
theorem B2812253 : Blo 1873638 2812253 := bbase (se 3 (by rfl) ⟨527297, by rfl⟩ : syracuseStep 2812253 = 1054595) (by norm_num)
theorem B2812277 : Blo 1873638 2812277 := bbase (se 5 (by rfl) ⟨131825, by rfl⟩ : syracuseStep 2812277 = 263651) (by norm_num)
theorem B2812301 : Blo 1873638 2812301 := bbase (se 3 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 2812301 = 1054613) (by norm_num)
theorem B6326693 : Blo 1873638 6326693 := bbase (se 4 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 6326693 = 1186255) (by norm_num)
theorem B2812325 : Blo 1873638 2812325 := bbase (se 4 (by rfl) ⟨263655, by rfl⟩ : syracuseStep 2812325 = 527311) (by norm_num)
theorem B2812349 : Blo 1873638 2812349 := bbase (se 3 (by rfl) ⟨527315, by rfl⟩ : syracuseStep 2812349 = 1054631) (by norm_num)
theorem B2107849 : Blo 1873638 2107849 := bbase (se 2 (by rfl) ⟨790443, by rfl⟩ : syracuseStep 2107849 = 1580887) (by norm_num)
theorem B2001353 : Blo 1873638 2001353 := bbase (se 2 (by rfl) ⟨750507, by rfl⟩ : syracuseStep 2001353 = 1501015) (by norm_num)
theorem B24021461 : Blo 1873638 24021461 := bbase (se 7 (by rfl) ⟨281501, by rfl⟩ : syracuseStep 24021461 = 563003) (by norm_num)
theorem B2812373 : Blo 1873638 2812373 := bbase (se 7 (by rfl) ⟨32957, by rfl⟩ : syracuseStep 2812373 = 65915) (by norm_num)
theorem B3164629 : Blo 1873638 3164629 := bbase (se 7 (by rfl) ⟨37085, by rfl⟩ : syracuseStep 3164629 = 74171) (by norm_num)
theorem B7604693 : Blo 1873638 7604693 := bbase (se 7 (by rfl) ⟨89117, by rfl⟩ : syracuseStep 7604693 = 178235) (by norm_num)
theorem B3607013 : Blo 1873638 3607013 := bbase (se 4 (by rfl) ⟨338157, by rfl⟩ : syracuseStep 3607013 = 676315) (by norm_num)
theorem B2107885 : Blo 1873638 2107885 := bbase (se 3 (by rfl) ⟨395228, by rfl⟩ : syracuseStep 2107885 = 790457) (by norm_num)
theorem B2812397 : Blo 1873638 2812397 := bbase (se 3 (by rfl) ⟨527324, by rfl⟩ : syracuseStep 2812397 = 1054649) (by norm_num)
theorem B5335541 : Blo 1873638 5335541 := bbase (se 5 (by rfl) ⟨250103, by rfl⟩ : syracuseStep 5335541 = 500207) (by norm_num)
theorem B2812421 : Blo 1873638 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B2107921 : Blo 1873638 2107921 := bbase (se 2 (by rfl) ⟨790470, by rfl⟩ : syracuseStep 2107921 = 1580941) (by norm_num)
theorem B4745749 : Blo 1873638 4745749 := bbase (se 6 (by rfl) ⟨111228, by rfl⟩ : syracuseStep 4745749 = 222457) (by norm_num)
theorem B2812445 : Blo 1873638 2812445 := bbase (se 3 (by rfl) ⟨527333, by rfl⟩ : syracuseStep 2812445 = 1054667) (by norm_num)
theorem B3164717 : Blo 1873638 3164717 := bbase (se 3 (by rfl) ⟨593384, by rfl⟩ : syracuseStep 3164717 = 1186769) (by norm_num)
theorem B2107957 : Blo 1873638 2107957 := bbase (se 5 (by rfl) ⟨98810, by rfl⟩ : syracuseStep 2107957 = 197621) (by norm_num)
theorem B8006197 : Blo 1873638 8006197 := bbase (se 5 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 8006197 = 750581) (by norm_num)
theorem B2812469 : Blo 1873638 2812469 := bbase (se 5 (by rfl) ⟨131834, by rfl⟩ : syracuseStep 2812469 = 263669) (by norm_num)
theorem B2812493 : Blo 1873638 2812493 := bbase (se 3 (by rfl) ⟨527342, by rfl⟩ : syracuseStep 2812493 = 1054685) (by norm_num)
theorem B2107993 : Blo 1873638 2107993 := bbase (se 2 (by rfl) ⟨790497, by rfl⟩ : syracuseStep 2107993 = 1580995) (by norm_num)
theorem B2812517 : Blo 1873638 2812517 := bbase (se 4 (by rfl) ⟨263673, by rfl⟩ : syracuseStep 2812517 = 527347) (by norm_num)
theorem B2108029 : Blo 1873638 2108029 := bbase (se 3 (by rfl) ⟨395255, by rfl⟩ : syracuseStep 2108029 = 790511) (by norm_num)
theorem B2812541 : Blo 1873638 2812541 := bbase (se 3 (by rfl) ⟨527351, by rfl⟩ : syracuseStep 2812541 = 1054703) (by norm_num)
theorem B4745861 : Blo 1873638 4745861 := bbase (se 4 (by rfl) ⟨444924, by rfl⟩ : syracuseStep 4745861 = 889849) (by norm_num)
theorem B2812565 : Blo 1873638 2812565 := bbase (se 6 (by rfl) ⟨65919, by rfl⟩ : syracuseStep 2812565 = 131839) (by norm_num)
theorem B2108065 : Blo 1873638 2108065 := bbase (se 2 (by rfl) ⟨790524, by rfl⟩ : syracuseStep 2108065 = 1581049) (by norm_num)
theorem B2812589 : Blo 1873638 2812589 := bbase (se 3 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 2812589 = 1054721) (by norm_num)
theorem B3164845 : Blo 1873638 3164845 := bbase (se 3 (by rfl) ⟨593408, by rfl⟩ : syracuseStep 3164845 = 1186817) (by norm_num)
theorem B5335733 : Blo 1873638 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B11553461 : Blo 1873638 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B2001601 : Blo 1873638 2001601 := bbase (se 2 (by rfl) ⟨750600, by rfl⟩ : syracuseStep 2001601 = 1501201) (by norm_num)
theorem B2108101 : Blo 1873638 2108101 := bbase (se 4 (by rfl) ⟨197634, by rfl⟩ : syracuseStep 2108101 = 395269) (by norm_num)
theorem B2812613 : Blo 1873638 2812613 := bbase (se 4 (by rfl) ⟨263682, by rfl⟩ : syracuseStep 2812613 = 527365) (by norm_num)
theorem B5065429 : Blo 1873638 5065429 := bbase (se 7 (by rfl) ⟨59360, by rfl⟩ : syracuseStep 5065429 = 118721) (by norm_num)
theorem B2812637 : Blo 1873638 2812637 := bbase (se 3 (by rfl) ⟨527369, by rfl⟩ : syracuseStep 2812637 = 1054739) (by norm_num)
theorem B2108137 : Blo 1873638 2108137 := bbase (se 2 (by rfl) ⟨790551, by rfl⟩ : syracuseStep 2108137 = 1581103) (by norm_num)
theorem B2812661 : Blo 1873638 2812661 := bbase (se 5 (by rfl) ⟨131843, by rfl⟩ : syracuseStep 2812661 = 263687) (by norm_num)
theorem B3164933 : Blo 1873638 3164933 := bbase (se 4 (by rfl) ⟨296712, by rfl⟩ : syracuseStep 3164933 = 593425) (by norm_num)
theorem B2108173 : Blo 1873638 2108173 := bbase (se 3 (by rfl) ⟨395282, by rfl⟩ : syracuseStep 2108173 = 790565) (by norm_num)
theorem B2812685 : Blo 1873638 2812685 := bbase (se 3 (by rfl) ⟨527378, by rfl⟩ : syracuseStep 2812685 = 1054757) (by norm_num)
theorem B3558181 : Blo 1873638 3558181 := bbase (se 4 (by rfl) ⟨333579, by rfl⟩ : syracuseStep 3558181 = 667159) (by norm_num)
theorem B2812709 : Blo 1873638 2812709 := bbase (se 4 (by rfl) ⟨263691, by rfl⟩ : syracuseStep 2812709 = 527383) (by norm_num)
theorem B2108209 : Blo 1873638 2108209 := bbase (se 2 (by rfl) ⟨790578, by rfl⟩ : syracuseStep 2108209 = 1581157) (by norm_num)
theorem B2812733 : Blo 1873638 2812733 := bbase (se 3 (by rfl) ⟨527387, by rfl⟩ : syracuseStep 2812733 = 1054775) (by norm_num)
theorem B4746053 : Blo 1873638 4746053 := bbase (se 4 (by rfl) ⟨444942, by rfl⟩ : syracuseStep 4746053 = 889885) (by norm_num)
theorem B6007621 : Blo 1873638 6007621 := bbase (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) (by norm_num)
theorem B2108245 : Blo 1873638 2108245 := bbase (se 9 (by rfl) ⟨6176, by rfl⟩ : syracuseStep 2108245 = 12353) (by norm_num)
theorem B6327125 : Blo 1873638 6327125 := bbase (se 9 (by rfl) ⟨18536, by rfl⟩ : syracuseStep 6327125 = 37073) (by norm_num)
theorem B2812757 : Blo 1873638 2812757 := bbase (se 9 (by rfl) ⟨8240, by rfl⟩ : syracuseStep 2812757 = 16481) (by norm_num)
theorem B2812781 : Blo 1873638 2812781 := bbase (se 3 (by rfl) ⟨527396, by rfl⟩ : syracuseStep 2812781 = 1054793) (by norm_num)
theorem B2108281 : Blo 1873638 2108281 := bbase (se 2 (by rfl) ⟨790605, by rfl⟩ : syracuseStep 2108281 = 1581211) (by norm_num)
theorem B2812805 : Blo 1873638 2812805 := bbase (se 4 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 2812805 = 527401) (by norm_num)
theorem B3165061 : Blo 1873638 3165061 := bbase (se 4 (by rfl) ⟨296724, by rfl⟩ : syracuseStep 3165061 = 593449) (by norm_num)
theorem B2108317 : Blo 1873638 2108317 := bbase (se 3 (by rfl) ⟨395309, by rfl⟩ : syracuseStep 2108317 = 790619) (by norm_num)
theorem B2812829 : Blo 1873638 2812829 := bbase (se 3 (by rfl) ⟨527405, by rfl⟩ : syracuseStep 2812829 = 1054811) (by norm_num)
theorem B3558325 : Blo 1873638 3558325 := bbase (se 5 (by rfl) ⟨166796, by rfl⟩ : syracuseStep 3558325 = 333593) (by norm_num)
theorem B2812853 : Blo 1873638 2812853 := bbase (se 5 (by rfl) ⟨131852, by rfl⟩ : syracuseStep 2812853 = 263705) (by norm_num)
theorem B2108353 : Blo 1873638 2108353 := bbase (se 2 (by rfl) ⟨790632, by rfl⟩ : syracuseStep 2108353 = 1581265) (by norm_num)
theorem B2812877 : Blo 1873638 2812877 := bbase (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) (by norm_num)
theorem B2108389 : Blo 1873638 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B2812901 : Blo 1873638 2812901 := bbase (se 4 (by rfl) ⟨263709, by rfl⟩ : syracuseStep 2812901 = 527419) (by norm_num)
theorem B6753269 : Blo 1873638 6753269 := bbase (se 5 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 6753269 = 633119) (by norm_num)
theorem B2812925 : Blo 1873638 2812925 := bbase (se 3 (by rfl) ⟨527423, by rfl⟩ : syracuseStep 2812925 = 1054847) (by norm_num)
theorem B2108425 : Blo 1873638 2108425 := bbase (se 2 (by rfl) ⟨790659, by rfl⟩ : syracuseStep 2108425 = 1581319) (by norm_num)
theorem B2812949 : Blo 1873638 2812949 := bbase (se 6 (by rfl) ⟨65928, by rfl⟩ : syracuseStep 2812949 = 131857) (by norm_num)
theorem B2108461 : Blo 1873638 2108461 := bbase (se 3 (by rfl) ⟨395336, by rfl⟩ : syracuseStep 2108461 = 790673) (by norm_num)
theorem B2812973 : Blo 1873638 2812973 := bbase (se 3 (by rfl) ⟨527432, by rfl⟩ : syracuseStep 2812973 = 1054865) (by norm_num)
theorem B3042365 : Blo 1873638 3042365 := bbase (se 3 (by rfl) ⟨570443, by rfl⟩ : syracuseStep 3042365 = 1140887) (by norm_num)
theorem B2812997 : Blo 1873638 2812997 := bbase (se 4 (by rfl) ⟨263718, by rfl⟩ : syracuseStep 2812997 = 527437) (by norm_num)
theorem B2108497 : Blo 1873638 2108497 := bbase (se 2 (by rfl) ⟨790686, by rfl⟩ : syracuseStep 2108497 = 1581373) (by norm_num)
theorem B3558485 : Blo 1873638 3558485 := bbase (se 8 (by rfl) ⟨20850, by rfl⟩ : syracuseStep 3558485 = 41701) (by norm_num)
theorem B2813021 : Blo 1873638 2813021 := bbase (se 3 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 2813021 = 1054883) (by norm_num)
theorem B2108533 : Blo 1873638 2108533 := bbase (se 5 (by rfl) ⟨98837, by rfl⟩ : syracuseStep 2108533 = 197675) (by norm_num)
theorem B2813045 : Blo 1873638 2813045 := bbase (se 5 (by rfl) ⟨131861, by rfl⟩ : syracuseStep 2813045 = 263723) (by norm_num)
theorem B2002045 : Blo 1873638 2002045 := bbase (se 3 (by rfl) ⟨375383, by rfl⟩ : syracuseStep 2002045 = 750767) (by norm_num)
theorem B2813069 : Blo 1873638 2813069 := bbase (se 3 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 2813069 = 1054901) (by norm_num)
theorem B2108569 : Blo 1873638 2108569 := bbase (se 2 (by rfl) ⟨790713, by rfl⟩ : syracuseStep 2108569 = 1581427) (by norm_num)
theorem B4746397 : Blo 1873638 4746397 := bbase (se 3 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 4746397 = 1779899) (by norm_num)
theorem B2813093 : Blo 1873638 2813093 := bbase (se 4 (by rfl) ⟨263727, by rfl⟩ : syracuseStep 2813093 = 527455) (by norm_num)
theorem B2002105 : Blo 1873638 2002105 := bbase (se 2 (by rfl) ⟨750789, by rfl⟩ : syracuseStep 2002105 = 1501579) (by norm_num)
theorem B2108605 : Blo 1873638 2108605 := bbase (se 3 (by rfl) ⟨395363, by rfl⟩ : syracuseStep 2108605 = 790727) (by norm_num)
theorem B3378365 : Blo 1873638 3378365 := bbase (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) (by norm_num)
theorem B2813117 : Blo 1873638 2813117 := bbase (se 3 (by rfl) ⟨527459, by rfl⟩ : syracuseStep 2813117 = 1054919) (by norm_num)
theorem B2813141 : Blo 1873638 2813141 := bbase (se 7 (by rfl) ⟨32966, by rfl⟩ : syracuseStep 2813141 = 65933) (by norm_num)
theorem B2108641 : Blo 1873638 2108641 := bbase (se 2 (by rfl) ⟨790740, by rfl⟩ : syracuseStep 2108641 = 1581481) (by norm_num)
theorem B3558629 : Blo 1873638 3558629 := bbase (se 4 (by rfl) ⟨333621, by rfl⟩ : syracuseStep 3558629 = 667243) (by norm_num)
theorem B2813165 : Blo 1873638 2813165 := bbase (se 3 (by rfl) ⟨527468, by rfl⟩ : syracuseStep 2813165 = 1054937) (by norm_num)
theorem B2108677 : Blo 1873638 2108677 := bbase (se 4 (by rfl) ⟨197688, by rfl⟩ : syracuseStep 2108677 = 395377) (by norm_num)
theorem B3378437 : Blo 1873638 3378437 := bbase (se 4 (by rfl) ⟨316728, by rfl⟩ : syracuseStep 3378437 = 633457) (by norm_num)
theorem B6327557 : Blo 1873638 6327557 := bbase (se 4 (by rfl) ⟨593208, by rfl⟩ : syracuseStep 6327557 = 1186417) (by norm_num)
theorem B2813189 : Blo 1873638 2813189 := bbase (se 4 (by rfl) ⟨263736, by rfl⟩ : syracuseStep 2813189 = 527473) (by norm_num)
theorem B4746509 : Blo 1873638 4746509 := bbase (se 3 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 4746509 = 1779941) (by norm_num)
theorem B2813213 : Blo 1873638 2813213 := bbase (se 3 (by rfl) ⟨527477, by rfl⟩ : syracuseStep 2813213 = 1054955) (by norm_num)
theorem B2108713 : Blo 1873638 2108713 := bbase (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) (by norm_num)
theorem B2813237 : Blo 1873638 2813237 := bbase (se 5 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 2813237 = 263741) (by norm_num)
theorem B2108749 : Blo 1873638 2108749 := bbase (se 3 (by rfl) ⟨395390, by rfl⟩ : syracuseStep 2108749 = 790781) (by norm_num)
theorem B2813261 : Blo 1873638 2813261 := bbase (se 3 (by rfl) ⟨527486, by rfl⟩ : syracuseStep 2813261 = 1054973) (by norm_num)
theorem B2813285 : Blo 1873638 2813285 := bbase (se 4 (by rfl) ⟨263745, by rfl⟩ : syracuseStep 2813285 = 527491) (by norm_num)
theorem B3001709 : Blo 1873638 3001709 := bbase (se 3 (by rfl) ⟨562820, by rfl⟩ : syracuseStep 3001709 = 1125641) (by norm_num)
theorem B2108785 : Blo 1873638 2108785 := bbase (se 2 (by rfl) ⟨790794, by rfl⟩ : syracuseStep 2108785 = 1581589) (by norm_num)
theorem B2813309 : Blo 1873638 2813309 := bbase (se 3 (by rfl) ⟨527495, by rfl⟩ : syracuseStep 2813309 = 1054991) (by norm_num)
theorem B9489797 : Blo 1873638 9489797 := bbase (se 4 (by rfl) ⟨889668, by rfl⟩ : syracuseStep 9489797 = 1779337) (by norm_num)
theorem B2108821 : Blo 1873638 2108821 := bbase (se 6 (by rfl) ⟨49425, by rfl⟩ : syracuseStep 2108821 = 98851) (by norm_num)
theorem B3206549 : Blo 1873638 3206549 := bbase (se 6 (by rfl) ⟨75153, by rfl⟩ : syracuseStep 3206549 = 150307) (by norm_num)
theorem B2813333 : Blo 1873638 2813333 := bbase (se 6 (by rfl) ⟨65937, by rfl⟩ : syracuseStep 2813333 = 131875) (by norm_num)
theorem B2813357 : Blo 1873638 2813357 := bbase (se 3 (by rfl) ⟨527504, by rfl⟩ : syracuseStep 2813357 = 1055009) (by norm_num)
theorem B2108857 : Blo 1873638 2108857 := bbase (se 2 (by rfl) ⟨790821, by rfl⟩ : syracuseStep 2108857 = 1581643) (by norm_num)
theorem B2813381 : Blo 1873638 2813381 := bbase (se 4 (by rfl) ⟨263754, by rfl⟩ : syracuseStep 2813381 = 527509) (by norm_num)
theorem B4746701 : Blo 1873638 4746701 := bbase (se 3 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 4746701 = 1780013) (by norm_num)
theorem B2108893 : Blo 1873638 2108893 := bbase (se 3 (by rfl) ⟨395417, by rfl⟩ : syracuseStep 2108893 = 790835) (by norm_num)
theorem B2813405 : Blo 1873638 2813405 := bbase (se 3 (by rfl) ⟨527513, by rfl⟩ : syracuseStep 2813405 = 1055027) (by norm_num)
theorem B2002421 : Blo 1873638 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B2813429 : Blo 1873638 2813429 := bbase (se 5 (by rfl) ⟨131879, by rfl⟩ : syracuseStep 2813429 = 263759) (by norm_num)
theorem B2108929 : Blo 1873638 2108929 := bbase (se 2 (by rfl) ⟨790848, by rfl⟩ : syracuseStep 2108929 = 1581697) (by norm_num)
theorem B3558917 : Blo 1873638 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B3853829 : Blo 1873638 3853829 := bbase (se 4 (by rfl) ⟨361296, by rfl⟩ : syracuseStep 3853829 = 722593) (by norm_num)
theorem B2813453 : Blo 1873638 2813453 := bbase (se 3 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 2813453 = 1055045) (by norm_num)
theorem B2534941 : Blo 1873638 2534941 := bbase (se 3 (by rfl) ⟨475301, by rfl⟩ : syracuseStep 2534941 = 950603) (by norm_num)
theorem B2108965 : Blo 1873638 2108965 := bbase (se 4 (by rfl) ⟨197715, by rfl⟩ : syracuseStep 2108965 = 395431) (by norm_num)
theorem B2109001 : Blo 1873638 2109001 := bbase (se 2 (by rfl) ⟨790875, by rfl⟩ : syracuseStep 2109001 = 1581751) (by norm_num)
theorem B6409813 : Blo 1873638 6409813 := bbase (se 8 (by rfl) ⟨37557, by rfl⟩ : syracuseStep 6409813 = 75115) (by norm_num)
theorem B10677845 : Blo 1873638 10677845 := bbase (se 8 (by rfl) ⟨62565, by rfl⟩ : syracuseStep 10677845 = 125131) (by norm_num)
theorem B2109037 : Blo 1873638 2109037 := bbase (se 3 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 2109037 = 790889) (by norm_num)
theorem B2109073 : Blo 1873638 2109073 := bbase (se 2 (by rfl) ⟨790902, by rfl⟩ : syracuseStep 2109073 = 1581805) (by norm_num)
theorem B5336725 : Blo 1873638 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B3559069 : Blo 1873638 3559069 := bbase (se 3 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 3559069 = 1334651) (by norm_num)
theorem B2109109 : Blo 1873638 2109109 := bbase (se 5 (by rfl) ⟨98864, by rfl⟩ : syracuseStep 2109109 = 197729) (by norm_num)
theorem B6327989 : Blo 1873638 6327989 := bbase (se 5 (by rfl) ⟨296624, by rfl⟩ : syracuseStep 6327989 = 593249) (by norm_num)
theorem B4067029 : Blo 1873638 4067029 := bbase (se 7 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 4067029 = 95321) (by norm_num)
theorem B2109145 : Blo 1873638 2109145 := bbase (se 2 (by rfl) ⟨790929, by rfl⟩ : syracuseStep 2109145 = 1581859) (by norm_num)
theorem B2109181 : Blo 1873638 2109181 := bbase (se 3 (by rfl) ⟨395471, by rfl⟩ : syracuseStep 2109181 = 790943) (by norm_num)
theorem B2109217 : Blo 1873638 2109217 := bbase (se 2 (by rfl) ⟨790956, by rfl⟩ : syracuseStep 2109217 = 1581913) (by norm_num)
theorem B4747045 : Blo 1873638 4747045 := bbase (se 4 (by rfl) ⟨445035, by rfl⟩ : syracuseStep 4747045 = 890071) (by norm_num)
theorem B2109253 : Blo 1873638 2109253 := bbase (se 4 (by rfl) ⟨197742, by rfl⟩ : syracuseStep 2109253 = 395485) (by norm_num)
theorem B12013397 : Blo 1873638 12013397 := bbase (se 9 (by rfl) ⟨35195, by rfl⟩ : syracuseStep 12013397 = 70391) (by norm_num)
theorem B2109289 : Blo 1873638 2109289 := bbase (se 2 (by rfl) ⟨790983, by rfl⟩ : syracuseStep 2109289 = 1581967) (by norm_num)
theorem B2371457 : Blo 1873638 2371457 := bbase (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) (by norm_num)
theorem B2109325 : Blo 1873638 2109325 := bbase (se 3 (by rfl) ⟨395498, by rfl⟩ : syracuseStep 2109325 = 790997) (by norm_num)
theorem B4747157 : Blo 1873638 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B7114661 : Blo 1873638 7114661 := bbase (se 4 (by rfl) ⟨666999, by rfl⟩ : syracuseStep 7114661 = 1333999) (by norm_num)
theorem B2109361 : Blo 1873638 2109361 := bbase (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) (by norm_num)
theorem B2002865 : Blo 1873638 2002865 := bbase (se 2 (by rfl) ⟨751074, by rfl⟩ : syracuseStep 2002865 = 1502149) (by norm_num)
theorem B2371513 : Blo 1873638 2371513 := bbase (se 2 (by rfl) ⟨889317, by rfl⟩ : syracuseStep 2371513 = 1778635) (by norm_num)
theorem B3559373 : Blo 1873638 3559373 := bbase (se 3 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 3559373 = 1334765) (by norm_num)
theorem B2109397 : Blo 1873638 2109397 := bbase (se 7 (by rfl) ⟨24719, by rfl⟩ : syracuseStep 2109397 = 49439) (by norm_num)
theorem B2002925 : Blo 1873638 2002925 := bbase (se 3 (by rfl) ⟨375548, by rfl⟩ : syracuseStep 2002925 = 751097) (by norm_num)
theorem B2109433 : Blo 1873638 2109433 := bbase (se 2 (by rfl) ⟨791037, by rfl⟩ : syracuseStep 2109433 = 1582075) (by norm_num)
theorem B2371609 : Blo 1873638 2371609 := bbase (se 2 (by rfl) ⟨889353, by rfl⟩ : syracuseStep 2371609 = 1778707) (by norm_num)
theorem B2109469 : Blo 1873638 2109469 := bbase (se 3 (by rfl) ⟨395525, by rfl⟩ : syracuseStep 2109469 = 791051) (by norm_num)
theorem B3469373 : Blo 1873638 3469373 := bbase (se 3 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 3469373 = 1301015) (by norm_num)
theorem B2109505 : Blo 1873638 2109505 := bbase (se 2 (by rfl) ⟨791064, by rfl⟩ : syracuseStep 2109505 = 1582129) (by norm_num)
theorem B4001861 : Blo 1873638 4001861 := bbase (se 4 (by rfl) ⟨375174, by rfl⟩ : syracuseStep 4001861 = 750349) (by norm_num)
theorem B4747349 : Blo 1873638 4747349 := bbase (se 8 (by rfl) ⟨27816, by rfl⟩ : syracuseStep 4747349 = 55633) (by norm_num)
theorem B6328421 : Blo 1873638 6328421 := bbase (se 4 (by rfl) ⟨593289, by rfl⟩ : syracuseStep 6328421 = 1186579) (by norm_num)
theorem B2109541 : Blo 1873638 2109541 := bbase (se 4 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 2109541 = 395539) (by norm_num)
theorem B2109577 : Blo 1873638 2109577 := bbase (se 2 (by rfl) ⟨791091, by rfl⟩ : syracuseStep 2109577 = 1582183) (by norm_num)
theorem B2109613 : Blo 1873638 2109613 := bbase (se 3 (by rfl) ⟨395552, by rfl⟩ : syracuseStep 2109613 = 791105) (by norm_num)
theorem B7114949 : Blo 1873638 7114949 := bbase (se 4 (by rfl) ⟨667026, by rfl⟩ : syracuseStep 7114949 = 1334053) (by norm_num)
theorem B2371781 : Blo 1873638 2371781 := bbase (se 4 (by rfl) ⟨222354, by rfl⟩ : syracuseStep 2371781 = 444709) (by norm_num)
theorem B2109649 : Blo 1873638 2109649 := bbase (se 2 (by rfl) ⟨791118, by rfl⟩ : syracuseStep 2109649 = 1582237) (by norm_num)
theorem B4002005 : Blo 1873638 4002005 := bbase (se 7 (by rfl) ⟨46898, by rfl⟩ : syracuseStep 4002005 = 93797) (by norm_num)
theorem B12824821 : Blo 1873638 12824821 := bbase (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) (by norm_num)
theorem B2109685 : Blo 1873638 2109685 := bbase (se 5 (by rfl) ⟨98891, by rfl⟩ : syracuseStep 2109685 = 197783) (by norm_num)
theorem B2371837 : Blo 1873638 2371837 := bbase (se 3 (by rfl) ⟨444719, by rfl⟩ : syracuseStep 2371837 = 889439) (by norm_num)
theorem B2404613 : Blo 1873638 2404613 := bbase (se 4 (by rfl) ⟨225432, by rfl⟩ : syracuseStep 2404613 = 450865) (by norm_num)
theorem B3002645 : Blo 1873638 3002645 := bbase (se 6 (by rfl) ⟨70374, by rfl⟩ : syracuseStep 3002645 = 140749) (by norm_num)
theorem B2109721 : Blo 1873638 2109721 := bbase (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) (by norm_num)
theorem B2109757 : Blo 1873638 2109757 := bbase (se 3 (by rfl) ⟨395579, by rfl⟩ : syracuseStep 2109757 = 791159) (by norm_num)
theorem B2371933 : Blo 1873638 2371933 := bbase (se 3 (by rfl) ⟨444737, by rfl⟩ : syracuseStep 2371933 = 889475) (by norm_num)
theorem B2109793 : Blo 1873638 2109793 := bbase (se 2 (by rfl) ⟨791172, by rfl⟩ : syracuseStep 2109793 = 1582345) (by norm_num)
theorem B2109829 : Blo 1873638 2109829 := bbase (se 4 (by rfl) ⟨197796, by rfl⟩ : syracuseStep 2109829 = 395593) (by norm_num)
theorem B2109865 : Blo 1873638 2109865 := bbase (se 2 (by rfl) ⟨791199, by rfl⟩ : syracuseStep 2109865 = 1582399) (by norm_num)
theorem B4747693 : Blo 1873638 4747693 := bbase (se 3 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 4747693 = 1780385) (by norm_num)
theorem B14242229 : Blo 1873638 14242229 := bbase (se 5 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 14242229 = 1335209) (by norm_num)
theorem B2281921 : Blo 1873638 2281921 := bbase (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) (by norm_num)
theorem B2109901 : Blo 1873638 2109901 := bbase (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) (by norm_num)
theorem B2109937 : Blo 1873638 2109937 := bbase (se 2 (by rfl) ⟨791226, by rfl⟩ : syracuseStep 2109937 = 1582453) (by norm_num)
theorem B2372105 : Blo 1873638 2372105 := bbase (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) (by norm_num)
theorem B3125773 : Blo 1873638 3125773 := bbase (se 3 (by rfl) ⟨586082, by rfl⟩ : syracuseStep 3125773 = 1172165) (by norm_num)
theorem B20263445 : Blo 1873638 20263445 := bbase (se 6 (by rfl) ⟨474924, by rfl⟩ : syracuseStep 20263445 = 949849) (by norm_num)
theorem B6328853 : Blo 1873638 6328853 := bbase (se 6 (by rfl) ⟨148332, by rfl⟩ : syracuseStep 6328853 = 296665) (by norm_num)
theorem B2109973 : Blo 1873638 2109973 := bbase (se 6 (by rfl) ⟨49452, by rfl⟩ : syracuseStep 2109973 = 98905) (by norm_num)
theorem B2110009 : Blo 1873638 2110009 := bbase (se 2 (by rfl) ⟨791253, by rfl⟩ : syracuseStep 2110009 = 1582507) (by norm_num)
theorem B4002365 : Blo 1873638 4002365 := bbase (se 3 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 4002365 = 1500887) (by norm_num)
theorem B2372161 : Blo 1873638 2372161 := bbase (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) (by norm_num)
theorem B2110045 : Blo 1873638 2110045 := bbase (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) (by norm_num)
theorem B2110081 : Blo 1873638 2110081 := bbase (se 2 (by rfl) ⟨791280, by rfl⟩ : syracuseStep 2110081 = 1582561) (by norm_num)
theorem B9491093 : Blo 1873638 9491093 := bbase (se 6 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 9491093 = 444895) (by norm_num)
theorem B2372257 : Blo 1873638 2372257 := bbase (se 2 (by rfl) ⟨889596, by rfl⟩ : syracuseStep 2372257 = 1779193) (by norm_num)
theorem B3560125 : Blo 1873638 3560125 := bbase (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) (by norm_num)
theorem B5067461 : Blo 1873638 5067461 := bbase (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) (by norm_num)
theorem B22794965 : Blo 1873638 22794965 := bbase (se 7 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 22794965 = 534257) (by norm_num)
theorem B5337829 : Blo 1873638 5337829 := bbase (se 4 (by rfl) ⟨500421, by rfl⟩ : syracuseStep 5337829 = 1000843) (by norm_num)
theorem B4502333 : Blo 1873638 4502333 := bbase (se 3 (by rfl) ⟨844187, by rfl⟩ : syracuseStep 4502333 = 1688375) (by norm_num)
theorem B2372429 : Blo 1873638 2372429 := bbase (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) (by norm_num)
theorem B3560269 : Blo 1873638 3560269 := bbase (se 3 (by rfl) ⟨667550, by rfl⟩ : syracuseStep 3560269 = 1335101) (by norm_num)
theorem B14234453 : Blo 1873638 14234453 := bbase (se 9 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 14234453 = 83405) (by norm_num)
theorem B9007973 : Blo 1873638 9007973 := bbase (se 4 (by rfl) ⟨844497, by rfl⟩ : syracuseStep 9007973 = 1688995) (by norm_num)
theorem B3208061 : Blo 1873638 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2372485 : Blo 1873638 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B3003293 : Blo 1873638 3003293 := bbase (se 3 (by rfl) ⟨563117, by rfl⟩ : syracuseStep 3003293 = 1126235) (by norm_num)
theorem B4215725 : Blo 1873638 4215725 := bbase (se 3 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 4215725 = 1580897) (by norm_num)
theorem B6329285 : Blo 1873638 6329285 := bbase (se 4 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 6329285 = 1186741) (by norm_num)
theorem B2372581 : Blo 1873638 2372581 := bbase (se 4 (by rfl) ⟨222429, by rfl⟩ : syracuseStep 2372581 = 444859) (by norm_num)
theorem B3560429 : Blo 1873638 3560429 := bbase (se 3 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 3560429 = 1335161) (by norm_num)
theorem B4215797 : Blo 1873638 4215797 := bbase (se 5 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 4215797 = 395231) (by norm_num)
theorem B7918597 : Blo 1873638 7918597 := bbase (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) (by norm_num)
theorem B2405389 : Blo 1873638 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B4215869 : Blo 1873638 4215869 := bbase (se 3 (by rfl) ⟨790475, by rfl⟩ : syracuseStep 4215869 = 1580951) (by norm_num)
theorem B5067893 : Blo 1873638 5067893 := bbase (se 5 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 5067893 = 475115) (by norm_num)
theorem B3560573 : Blo 1873638 3560573 := bbase (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) (by norm_num)
theorem B4215941 : Blo 1873638 4215941 := bbase (se 4 (by rfl) ⟨395244, by rfl⟩ : syracuseStep 4215941 = 790489) (by norm_num)
theorem B2372753 : Blo 1873638 2372753 := bbase (se 2 (by rfl) ⟨889782, by rfl⟩ : syracuseStep 2372753 = 1779565) (by norm_num)
theorem B2372809 : Blo 1873638 2372809 := bbase (se 2 (by rfl) ⟨889803, by rfl⟩ : syracuseStep 2372809 = 1779607) (by norm_num)
theorem B4216013 : Blo 1873638 4216013 := bbase (se 3 (by rfl) ⟨790502, by rfl⟩ : syracuseStep 4216013 = 1581005) (by norm_num)
theorem B4216085 : Blo 1873638 4216085 := bbase (se 6 (by rfl) ⟨98814, by rfl⟩ : syracuseStep 4216085 = 197629) (by norm_num)
theorem B2372905 : Blo 1873638 2372905 := bbase (se 2 (by rfl) ⟨889839, by rfl⟩ : syracuseStep 2372905 = 1779679) (by norm_num)
theorem B2667821 : Blo 1873638 2667821 := bbase (se 3 (by rfl) ⟨500216, by rfl⟩ : syracuseStep 2667821 = 1000433) (by norm_num)
theorem B4216157 : Blo 1873638 4216157 := bbase (se 3 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 4216157 = 1581059) (by norm_num)
theorem B7116133 : Blo 1873638 7116133 := bbase (se 4 (by rfl) ⟨667137, by rfl⟩ : syracuseStep 7116133 = 1334275) (by norm_num)
theorem B6329717 : Blo 1873638 6329717 := bbase (se 5 (by rfl) ⟨296705, by rfl⟩ : syracuseStep 6329717 = 593411) (by norm_num)
theorem B4216229 : Blo 1873638 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B4003253 : Blo 1873638 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2373077 : Blo 1873638 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B8009189 : Blo 1873638 8009189 := bbase (se 4 (by rfl) ⟨750861, by rfl⟩ : syracuseStep 8009189 = 1501723) (by norm_num)
theorem B4216301 : Blo 1873638 4216301 := bbase (se 3 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 4216301 = 1581113) (by norm_num)
theorem B2373133 : Blo 1873638 2373133 := bbase (se 3 (by rfl) ⟨444962, by rfl⟩ : syracuseStep 2373133 = 889925) (by norm_num)
theorem B4216373 : Blo 1873638 4216373 := bbase (se 5 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 4216373 = 395285) (by norm_num)
theorem B2373229 : Blo 1873638 2373229 := bbase (se 3 (by rfl) ⟨444980, by rfl⟩ : syracuseStep 2373229 = 889961) (by norm_num)
theorem B4216445 : Blo 1873638 4216445 := bbase (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) (by norm_num)
theorem B7116437 : Blo 1873638 7116437 := bbase (se 6 (by rfl) ⟨166791, by rfl⟩ : syracuseStep 7116437 = 333583) (by norm_num)
theorem B4003501 : Blo 1873638 4003501 := bbase (se 3 (by rfl) ⟨750656, by rfl⟩ : syracuseStep 4003501 = 1501313) (by norm_num)
theorem B4216517 : Blo 1873638 4216517 := bbase (se 4 (by rfl) ⟨395298, by rfl⟩ : syracuseStep 4216517 = 790597) (by norm_num)
theorem B4216589 : Blo 1873638 4216589 := bbase (se 3 (by rfl) ⟨790610, by rfl⟩ : syracuseStep 4216589 = 1581221) (by norm_num)
theorem B2373401 : Blo 1873638 2373401 := bbase (se 2 (by rfl) ⟨890025, by rfl⟩ : syracuseStep 2373401 = 1780051) (by norm_num)
theorem B6330149 : Blo 1873638 6330149 := bbase (se 4 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 6330149 = 1186903) (by norm_num)
theorem B2373457 : Blo 1873638 2373457 := bbase (se 2 (by rfl) ⟨890046, by rfl⟩ : syracuseStep 2373457 = 1780093) (by norm_num)
theorem B4216661 : Blo 1873638 4216661 := bbase (se 9 (by rfl) ⟨12353, by rfl⟩ : syracuseStep 4216661 = 24707) (by norm_num)
theorem B3004285 : Blo 1873638 3004285 := bbase (se 3 (by rfl) ⟨563303, by rfl⟩ : syracuseStep 3004285 = 1126607) (by norm_num)
theorem B4216733 : Blo 1873638 4216733 := bbase (se 3 (by rfl) ⟨790637, by rfl⟩ : syracuseStep 4216733 = 1581275) (by norm_num)
theorem B9492389 : Blo 1873638 9492389 := bbase (se 4 (by rfl) ⟨889911, by rfl⟩ : syracuseStep 9492389 = 1779823) (by norm_num)
theorem B2373553 : Blo 1873638 2373553 := bbase (se 2 (by rfl) ⟨890082, by rfl⟩ : syracuseStep 2373553 = 1780165) (by norm_num)
theorem B12007349 : Blo 1873638 12007349 := bbase (se 5 (by rfl) ⟨562844, by rfl⟩ : syracuseStep 12007349 = 1125689) (by norm_num)
theorem B3798973 : Blo 1873638 3798973 := bbase (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) (by norm_num)
theorem B4216805 : Blo 1873638 4216805 := bbase (se 4 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 4216805 = 790651) (by norm_num)
theorem B2668573 : Blo 1873638 2668573 := bbase (se 3 (by rfl) ⟨500357, by rfl⟩ : syracuseStep 2668573 = 1000715) (by norm_num)
theorem B4216877 : Blo 1873638 4216877 := bbase (se 3 (by rfl) ⟨790664, by rfl⟩ : syracuseStep 4216877 = 1581329) (by norm_num)
theorem B2373725 : Blo 1873638 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B4216949 : Blo 1873638 4216949 := bbase (se 5 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 4216949 = 395339) (by norm_num)
theorem B5699717 : Blo 1873638 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B2373781 : Blo 1873638 2373781 := bbase (se 6 (by rfl) ⟨55635, by rfl⟩ : syracuseStep 2373781 = 111271) (by norm_num)
theorem B4004005 : Blo 1873638 4004005 := bbase (se 4 (by rfl) ⟨375375, by rfl⟩ : syracuseStep 4004005 = 750751) (by norm_num)
theorem B4217021 : Blo 1873638 4217021 := bbase (se 3 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 4217021 = 1581383) (by norm_num)
theorem B2283709 : Blo 1873638 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B5339333 : Blo 1873638 5339333 := bbase (se 4 (by rfl) ⟨500562, by rfl⟩ : syracuseStep 5339333 = 1001125) (by norm_num)
theorem B4274429 : Blo 1873638 4274429 := bbase (se 3 (by rfl) ⟨801455, by rfl⟩ : syracuseStep 4274429 = 1602911) (by norm_num)
theorem B4217093 : Blo 1873638 4217093 := bbase (se 4 (by rfl) ⟨395352, by rfl⟩ : syracuseStep 4217093 = 790705) (by norm_num)
theorem B4217165 : Blo 1873638 4217165 := bbase (se 3 (by rfl) ⟨790718, by rfl⟩ : syracuseStep 4217165 = 1581437) (by norm_num)
theorem B10672469 : Blo 1873638 10672469 := bbase (se 10 (by rfl) ⟨15633, by rfl⟩ : syracuseStep 10672469 = 31267) (by norm_num)
theorem B2283869 : Blo 1873638 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B4217237 : Blo 1873638 4217237 := bbase (se 6 (by rfl) ⟨98841, by rfl⟩ : syracuseStep 4217237 = 197683) (by norm_num)
theorem B10131893 : Blo 1873638 10131893 := bbase (se 5 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 10131893 = 949865) (by norm_num)
theorem B18020789 : Blo 1873638 18020789 := bbase (se 5 (by rfl) ⟨844724, by rfl⟩ : syracuseStep 18020789 = 1689449) (by norm_num)
theorem B8010197 : Blo 1873638 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B4217309 : Blo 1873638 4217309 := bbase (se 3 (by rfl) ⟨790745, by rfl⟩ : syracuseStep 4217309 = 1581491) (by norm_num)
theorem B4217381 : Blo 1873638 4217381 := bbase (se 4 (by rfl) ⟨395379, by rfl⟩ : syracuseStep 4217381 = 790759) (by norm_num)
theorem B4217453 : Blo 1873638 4217453 := bbase (se 3 (by rfl) ⟨790772, by rfl⟩ : syracuseStep 4217453 = 1581545) (by norm_num)
theorem B2251397 : Blo 1873638 2251397 := bbase (se 4 (by rfl) ⟨211068, by rfl⟩ : syracuseStep 2251397 = 422137) (by norm_num)
theorem B4217525 : Blo 1873638 4217525 := bbase (se 5 (by rfl) ⟨197696, by rfl⟩ : syracuseStep 4217525 = 395393) (by norm_num)
theorem B2251513 : Blo 1873638 2251513 := bbase (se 2 (by rfl) ⟨844317, by rfl⟩ : syracuseStep 2251513 = 1688635) (by norm_num)
theorem B4217597 : Blo 1873638 4217597 := bbase (se 3 (by rfl) ⟨790799, by rfl⟩ : syracuseStep 4217597 = 1581599) (by norm_num)
theorem B2669365 : Blo 1873638 2669365 := bbase (se 5 (by rfl) ⟨125126, by rfl⟩ : syracuseStep 2669365 = 250253) (by norm_num)
theorem B2251585 : Blo 1873638 2251585 := bbase (se 2 (by rfl) ⟨844344, by rfl⟩ : syracuseStep 2251585 = 1688689) (by norm_num)
theorem B4275013 : Blo 1873638 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B4217669 : Blo 1873638 4217669 := bbase (se 4 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 4217669 = 790813) (by norm_num)
theorem B4873085 : Blo 1873638 4873085 := bbase (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) (by norm_num)
theorem B4217741 : Blo 1873638 4217741 := bbase (se 3 (by rfl) ⟨790826, by rfl⟩ : syracuseStep 4217741 = 1581653) (by norm_num)
theorem B4275125 : Blo 1873638 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B2251705 : Blo 1873638 2251705 := bbase (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) (by norm_num)
theorem B4217813 : Blo 1873638 4217813 := bbase (se 7 (by rfl) ⟨49427, by rfl⟩ : syracuseStep 4217813 = 98855) (by norm_num)
theorem B4217885 : Blo 1873638 4217885 := bbase (se 3 (by rfl) ⟨790853, by rfl⟩ : syracuseStep 4217885 = 1581707) (by norm_num)
theorem B4004893 : Blo 1873638 4004893 := bbase (se 3 (by rfl) ⟨750917, by rfl⟩ : syracuseStep 4004893 = 1501835) (by norm_num)
theorem B4217957 : Blo 1873638 4217957 := bbase (se 4 (by rfl) ⟨395433, by rfl⟩ : syracuseStep 4217957 = 790867) (by norm_num)
theorem B2669701 : Blo 1873638 2669701 := bbase (se 4 (by rfl) ⟨250284, by rfl⟩ : syracuseStep 2669701 = 500569) (by norm_num)
theorem B4807853 : Blo 1873638 4807853 := bbase (se 3 (by rfl) ⟨901472, by rfl⟩ : syracuseStep 4807853 = 1802945) (by norm_num)
theorem B4218029 : Blo 1873638 4218029 := bbase (se 3 (by rfl) ⟨790880, by rfl⟩ : syracuseStep 4218029 = 1581761) (by norm_num)
theorem B9493685 : Blo 1873638 9493685 := bbase (se 5 (by rfl) ⟨445016, by rfl⟩ : syracuseStep 9493685 = 890033) (by norm_num)
theorem B2137297 : Blo 1873638 2137297 := bbase (se 2 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 2137297 = 1602973) (by norm_num)
theorem B16014581 : Blo 1873638 16014581 := bbase (se 5 (by rfl) ⟨750683, by rfl⟩ : syracuseStep 16014581 = 1501367) (by norm_num)
theorem B4218101 : Blo 1873638 4218101 := bbase (se 5 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 4218101 = 395447) (by norm_num)
theorem B8117509 : Blo 1873638 8117509 := bbase (se 4 (by rfl) ⟨761016, by rfl⟩ : syracuseStep 8117509 = 1522033) (by norm_num)
theorem B2252089 : Blo 1873638 2252089 := bbase (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) (by norm_num)
theorem B4218173 : Blo 1873638 4218173 := bbase (se 3 (by rfl) ⟨790907, by rfl⟩ : syracuseStep 4218173 = 1581815) (by norm_num)
theorem B4504909 : Blo 1873638 4504909 := bbase (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) (by norm_num)
theorem B2669917 : Blo 1873638 2669917 := bbase (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) (by norm_num)
theorem B16006517 : Blo 1873638 16006517 := bbase (se 5 (by rfl) ⟨750305, by rfl⟩ : syracuseStep 16006517 = 1500611) (by norm_num)
theorem B4808069 : Blo 1873638 4808069 := bbase (se 4 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 4808069 = 901513) (by norm_num)
theorem B4218245 : Blo 1873638 4218245 := bbase (se 4 (by rfl) ⟨395460, by rfl⟩ : syracuseStep 4218245 = 790921) (by norm_num)
theorem B4218317 : Blo 1873638 4218317 := bbase (se 3 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 4218317 = 1581869) (by norm_num)
theorem B6323669 : Blo 1873638 6323669 := bbase (se 7 (by rfl) ⟨74105, by rfl⟩ : syracuseStep 6323669 = 148211) (by norm_num)
theorem B10673653 : Blo 1873638 10673653 := bbase (se 5 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 10673653 = 1000655) (by norm_num)
theorem B4005389 : Blo 1873638 4005389 := bbase (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) (by norm_num)
theorem B4218389 : Blo 1873638 4218389 := bbase (se 6 (by rfl) ⟨98868, by rfl⟩ : syracuseStep 4218389 = 197737) (by norm_num)
theorem B9485909 : Blo 1873638 9485909 := bbase (se 8 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 9485909 = 111163) (by norm_num)
theorem B2137685 : Blo 1873638 2137685 := bbase (se 8 (by rfl) ⟨12525, by rfl⟩ : syracuseStep 2137685 = 25051) (by norm_num)
theorem B4218461 : Blo 1873638 4218461 := bbase (se 3 (by rfl) ⟨790961, by rfl⟩ : syracuseStep 4218461 = 1581923) (by norm_num)
theorem B4742813 : Blo 1873638 4742813 := bbase (se 3 (by rfl) ⟨889277, by rfl⟩ : syracuseStep 4742813 = 1778555) (by norm_num)
theorem B4218533 : Blo 1873638 4218533 := bbase (se 4 (by rfl) ⟨395487, by rfl⟩ : syracuseStep 4218533 = 790975) (by norm_num)
theorem B1900217 : Blo 1873638 1900217 := bbase (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) (by norm_num)
theorem B1900241 : Blo 1873638 1900241 := bbase (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) (by norm_num)
theorem B7118549 : Blo 1873638 7118549 := bbase (se 7 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 7118549 = 166841) (by norm_num)
theorem B2670293 : Blo 1873638 2670293 := bbase (se 7 (by rfl) ⟨31292, by rfl⟩ : syracuseStep 2670293 = 62585) (by norm_num)
theorem B1900249 : Blo 1873638 1900249 := bbase (se 2 (by rfl) ⟨712593, by rfl⟩ : syracuseStep 1900249 = 1425187) (by norm_num)
theorem B3161821 : Blo 1873638 3161821 := bbase (se 3 (by rfl) ⟨592841, by rfl⟩ : syracuseStep 3161821 = 1185683) (by norm_num)
theorem B1900265 : Blo 1873638 1900265 := bbase (se 2 (by rfl) ⟨712599, by rfl⟩ : syracuseStep 1900265 = 1425199) (by norm_num)
theorem B4218605 : Blo 1873638 4218605 := bbase (se 3 (by rfl) ⟨790988, by rfl⟩ : syracuseStep 4218605 = 1581977) (by norm_num)
theorem B6004469 : Blo 1873638 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B5340917 : Blo 1873638 5340917 := bbase (se 5 (by rfl) ⟨250355, by rfl⟩ : syracuseStep 5340917 = 500711) (by norm_num)
theorem B3161909 : Blo 1873638 3161909 := bbase (se 5 (by rfl) ⟨148214, by rfl⟩ : syracuseStep 3161909 = 296429) (by norm_num)
theorem B4218677 : Blo 1873638 4218677 := bbase (se 5 (by rfl) ⟨197750, by rfl⟩ : syracuseStep 4218677 = 395501) (by norm_num)
theorem B4218749 : Blo 1873638 4218749 := bbase (se 3 (by rfl) ⟨791015, by rfl⟩ : syracuseStep 4218749 = 1582031) (by norm_num)
theorem B6324101 : Blo 1873638 6324101 := bbase (se 4 (by rfl) ⟨592884, by rfl⟩ : syracuseStep 6324101 = 1185769) (by norm_num)
theorem B4276109 : Blo 1873638 4276109 := bbase (se 3 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 4276109 = 1603541) (by norm_num)
theorem B3162037 : Blo 1873638 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B4218821 : Blo 1873638 4218821 := bbase (se 4 (by rfl) ⟨395514, by rfl⟩ : syracuseStep 4218821 = 791029) (by norm_num)
theorem B2252777 : Blo 1873638 2252777 := bbase (se 2 (by rfl) ⟨844791, by rfl⟩ : syracuseStep 2252777 = 1689583) (by norm_num)
theorem B4743157 : Blo 1873638 4743157 := bbase (se 5 (by rfl) ⟨222335, by rfl⟩ : syracuseStep 4743157 = 444671) (by norm_num)
theorem B7118837 : Blo 1873638 7118837 := bbase (se 5 (by rfl) ⟨333695, by rfl⟩ : syracuseStep 7118837 = 667391) (by norm_num)
theorem B3162145 : Blo 1873638 3162145 := bstep (se 2 (by rfl) ⟨1185804, by rfl⟩ : syracuseStep 3162145 = 2371609) B2371609
theorem B4218929 : Blo 1873638 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B3162179 : Blo 1873638 3162179 := bstep (se 1 (by rfl) ⟨2371634, by rfl⟩ : syracuseStep 3162179 = 4743269) B4743269
theorem B4218947 : Blo 1873638 4218947 := bstep (se 1 (by rfl) ⟨3164210, by rfl⟩ : syracuseStep 4218947 = 6328421) B6328421
theorem B4743299 : Blo 1873638 4743299 := bstep (se 1 (by rfl) ⟨3557474, by rfl⟩ : syracuseStep 4743299 = 7114949) B7114949
theorem B3162307 : Blo 1873638 3162307 := bstep (se 1 (by rfl) ⟨2371730, by rfl⟩ : syracuseStep 3162307 = 4743461) B4743461
theorem B2851043 : Blo 1873638 2851043 := bstep (se 1 (by rfl) ⟨2138282, by rfl⟩ : syracuseStep 2851043 = 4276565) B4276565
theorem B9494819 : Blo 1873638 9494819 := bstep (se 1 (by rfl) ⟨7121114, by rfl⟩ : syracuseStep 9494819 = 14242229) B14242229
theorem B4276547 : Blo 1873638 4276547 := bstep (se 1 (by rfl) ⟨3207410, by rfl⟩ : syracuseStep 4276547 = 6414821) B6414821
theorem B3162449 : Blo 1873638 3162449 := bstep (se 2 (by rfl) ⟨1185918, by rfl⟩ : syracuseStep 3162449 = 2371837) B2371837
theorem B4219217 : Blo 1873638 4219217 := bstep (se 2 (by rfl) ⟨1582206, by rfl⟩ : syracuseStep 4219217 = 3164413) B3164413
theorem B13508963 : Blo 1873638 13508963 := bstep (se 1 (by rfl) ⟨10131722, by rfl⟩ : syracuseStep 13508963 = 20263445) B20263445
theorem B4219235 : Blo 1873638 4219235 := bstep (se 1 (by rfl) ⟨3164426, by rfl⟩ : syracuseStep 4219235 = 6328853) B6328853
theorem B5702051 : Blo 1873638 5702051 := bstep (se 1 (by rfl) ⟨4276538, by rfl⟩ : syracuseStep 5702051 = 8553077) B8553077
theorem B3162577 : Blo 1873638 3162577 := bstep (se 2 (by rfl) ⟨1185966, by rfl⟩ : syracuseStep 3162577 = 2371933) B2371933
theorem B15196643 : Blo 1873638 15196643 := bstep (se 1 (by rfl) ⟨11397482, by rfl⟩ : syracuseStep 15196643 = 22794965) B22794965
theorem B8552945 : Blo 1873638 8552945 := bstep (se 2 (by rfl) ⟨3207354, by rfl⟩ : syracuseStep 8552945 = 6414709) B6414709
theorem B3162611 : Blo 1873638 3162611 := bstep (se 1 (by rfl) ⟨2371958, by rfl⟩ : syracuseStep 3162611 = 4743917) B4743917
theorem B6324749 : Blo 1873638 6324749 := bstep (se 3 (by rfl) ⟨1185890, by rfl⟩ : syracuseStep 6324749 = 2371781) B2371781
theorem B6324803 : Blo 1873638 6324803 := bstep (se 1 (by rfl) ⟨4743602, by rfl⟩ : syracuseStep 6324803 = 9487205) B9487205
theorem B6005315 : Blo 1873638 6005315 := bstep (se 1 (by rfl) ⟨4503986, by rfl⟩ : syracuseStep 6005315 = 9007973) B9007973
theorem B14426693 : Blo 1873638 14426693 := bstep (se 4 (by rfl) ⟨1352502, by rfl⟩ : syracuseStep 14426693 = 2705005) B2705005
theorem B3801667 : Blo 1873638 3801667 := bstep (se 1 (by rfl) ⟨2851250, by rfl⟩ : syracuseStep 3801667 = 5702501) B5702501
theorem B2138707 : Blo 1873638 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B2810465 : Blo 1873638 2810465 := bstep (se 2 (by rfl) ⟨1053924, by rfl⟩ : syracuseStep 2810465 = 2107849) B2107849
theorem B4219505 : Blo 1873638 4219505 := bstep (se 2 (by rfl) ⟨1582314, by rfl⟩ : syracuseStep 4219505 = 3164629) B3164629
theorem B2810483 : Blo 1873638 2810483 := bstep (se 1 (by rfl) ⟨2107862, by rfl⟩ : syracuseStep 2810483 = 4215725) B4215725
theorem B3162739 : Blo 1873638 3162739 := bstep (se 1 (by rfl) ⟨2372054, by rfl⟩ : syracuseStep 3162739 = 4744109) B4744109
theorem B4219523 : Blo 1873638 4219523 := bstep (se 1 (by rfl) ⟨3164642, by rfl⟩ : syracuseStep 4219523 = 6329285) B6329285
theorem B2810513 : Blo 1873638 2810513 := bstep (se 2 (by rfl) ⟨1053942, by rfl⟩ : syracuseStep 2810513 = 2107885) B2107885
theorem B2810531 : Blo 1873638 2810531 := bstep (se 1 (by rfl) ⟨2107898, by rfl⟩ : syracuseStep 2810531 = 4215797) B4215797
theorem B2810561 : Blo 1873638 2810561 := bstep (se 2 (by rfl) ⟨1053960, by rfl⟩ : syracuseStep 2810561 = 2107921) B2107921
theorem B2810579 : Blo 1873638 2810579 := bstep (se 1 (by rfl) ⟨2107934, by rfl⟩ : syracuseStep 2810579 = 4215869) B4215869
theorem B38994659 : Blo 1873638 38994659 := bstep (se 1 (by rfl) ⟨29245994, by rfl⟩ : syracuseStep 38994659 = 58491989) B58491989
theorem B2810609 : Blo 1873638 2810609 := bstep (se 2 (by rfl) ⟨1053978, by rfl⟩ : syracuseStep 2810609 = 2107957) B2107957
theorem B10674929 : Blo 1873638 10674929 := bstep (se 2 (by rfl) ⟨4003098, by rfl⟩ : syracuseStep 10674929 = 8006197) B8006197
theorem B3162881 : Blo 1873638 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B2810627 : Blo 1873638 2810627 := bstep (se 1 (by rfl) ⟨2107970, by rfl⟩ : syracuseStep 2810627 = 4215941) B4215941
theorem B2810657 : Blo 1873638 2810657 := bstep (se 2 (by rfl) ⟨1053996, by rfl⟩ : syracuseStep 2810657 = 2107993) B2107993
theorem B2810675 : Blo 1873638 2810675 := bstep (se 1 (by rfl) ⟨2108006, by rfl⟩ : syracuseStep 2810675 = 4216013) B4216013
theorem B2810705 : Blo 1873638 2810705 := bstep (se 2 (by rfl) ⟨1054014, by rfl⟩ : syracuseStep 2810705 = 2108029) B2108029
theorem B6325073 : Blo 1873638 6325073 := bstep (se 2 (by rfl) ⟨2371902, by rfl⟩ : syracuseStep 6325073 = 4743805) B4743805
theorem B2810723 : Blo 1873638 2810723 := bstep (se 1 (by rfl) ⟨2108042, by rfl⟩ : syracuseStep 2810723 = 4216085) B4216085
theorem B2810753 : Blo 1873638 2810753 := bstep (se 2 (by rfl) ⟨1054032, by rfl⟩ : syracuseStep 2810753 = 2108065) B2108065
theorem B3163009 : Blo 1873638 3163009 := bstep (se 2 (by rfl) ⟨1186128, by rfl⟩ : syracuseStep 3163009 = 2372257) B2372257
theorem B4219793 : Blo 1873638 4219793 := bstep (se 2 (by rfl) ⟨1582422, by rfl⟩ : syracuseStep 4219793 = 3164845) B3164845
theorem B2810771 : Blo 1873638 2810771 := bstep (se 1 (by rfl) ⟨2108078, by rfl⟩ : syracuseStep 2810771 = 4216157) B4216157
theorem B3163043 : Blo 1873638 3163043 := bstep (se 1 (by rfl) ⟨2372282, by rfl⟩ : syracuseStep 3163043 = 4744565) B4744565
theorem B4219811 : Blo 1873638 4219811 := bstep (se 1 (by rfl) ⟨3164858, by rfl⟩ : syracuseStep 4219811 = 6329717) B6329717
theorem B2810801 : Blo 1873638 2810801 := bstep (se 2 (by rfl) ⟨1054050, by rfl⟩ : syracuseStep 2810801 = 2108101) B2108101
theorem B2810819 : Blo 1873638 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B8004557 : Blo 1873638 8004557 := bstep (se 3 (by rfl) ⟨1500854, by rfl⟩ : syracuseStep 8004557 = 3001709) B3001709
theorem B2810849 : Blo 1873638 2810849 := bstep (se 2 (by rfl) ⟨1054068, by rfl⟩ : syracuseStep 2810849 = 2108137) B2108137
theorem B2810867 : Blo 1873638 2810867 := bstep (se 1 (by rfl) ⟨2108150, by rfl⟩ : syracuseStep 2810867 = 4216301) B4216301
theorem B2810897 : Blo 1873638 2810897 := bstep (se 2 (by rfl) ⟨1054086, by rfl⟩ : syracuseStep 2810897 = 2108173) B2108173
theorem B2810915 : Blo 1873638 2810915 := bstep (se 1 (by rfl) ⟨2108186, by rfl⟩ : syracuseStep 2810915 = 4216373) B4216373
theorem B3163171 : Blo 1873638 3163171 := bstep (se 1 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 3163171 = 4744757) B4744757
theorem B4744241 : Blo 1873638 4744241 := bstep (se 2 (by rfl) ⟨1779090, by rfl⟩ : syracuseStep 4744241 = 3558181) B3558181
theorem B2810945 : Blo 1873638 2810945 := bstep (se 2 (by rfl) ⟨1054104, by rfl⟩ : syracuseStep 2810945 = 2108209) B2108209
theorem B2810963 : Blo 1873638 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B4744291 : Blo 1873638 4744291 := bstep (se 1 (by rfl) ⟨3558218, by rfl⟩ : syracuseStep 4744291 = 7116437) B7116437
theorem B2810993 : Blo 1873638 2810993 := bstep (se 2 (by rfl) ⟨1054122, by rfl⟩ : syracuseStep 2810993 = 2108245) B2108245
theorem B2811011 : Blo 1873638 2811011 := bstep (se 1 (by rfl) ⟨2108258, by rfl⟩ : syracuseStep 2811011 = 4216517) B4216517
theorem B10134661 : Blo 1873638 10134661 := bstep (se 4 (by rfl) ⟨950124, by rfl⟩ : syracuseStep 10134661 = 1900249) B1900249
theorem B2811041 : Blo 1873638 2811041 := bstep (se 2 (by rfl) ⟨1054140, by rfl⟩ : syracuseStep 2811041 = 2108281) B2108281
theorem B12829859 : Blo 1873638 12829859 := bstep (se 1 (by rfl) ⟨9622394, by rfl⟩ : syracuseStep 12829859 = 19244789) B19244789
theorem B3163313 : Blo 1873638 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B4220081 : Blo 1873638 4220081 := bstep (se 2 (by rfl) ⟨1582530, by rfl⟩ : syracuseStep 4220081 = 3165061) B3165061
theorem B2811059 : Blo 1873638 2811059 := bstep (se 1 (by rfl) ⟨2108294, by rfl⟩ : syracuseStep 2811059 = 4216589) B4216589
theorem B4220099 : Blo 1873638 4220099 := bstep (se 1 (by rfl) ⟨3165074, by rfl⟩ : syracuseStep 4220099 = 6330149) B6330149
theorem B2811089 : Blo 1873638 2811089 := bstep (se 2 (by rfl) ⟨1054158, by rfl⟩ : syracuseStep 2811089 = 2108317) B2108317
theorem B2811107 : Blo 1873638 2811107 := bstep (se 1 (by rfl) ⟨2108330, by rfl⟩ : syracuseStep 2811107 = 4216661) B4216661
theorem B4744433 : Blo 1873638 4744433 := bstep (se 2 (by rfl) ⟨1779162, by rfl⟩ : syracuseStep 4744433 = 3558325) B3558325
theorem B2811137 : Blo 1873638 2811137 := bstep (se 2 (by rfl) ⟨1054176, by rfl⟩ : syracuseStep 2811137 = 2108353) B2108353
theorem B11560205 : Blo 1873638 11560205 := bstep (se 3 (by rfl) ⟨2167538, by rfl⟩ : syracuseStep 11560205 = 4335077) B4335077
theorem B2811155 : Blo 1873638 2811155 := bstep (se 1 (by rfl) ⟨2108366, by rfl⟩ : syracuseStep 2811155 = 4216733) B4216733
theorem B8004899 : Blo 1873638 8004899 := bstep (se 1 (by rfl) ⟨6003674, by rfl⟩ : syracuseStep 8004899 = 12007349) B12007349
theorem B2811185 : Blo 1873638 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B3163441 : Blo 1873638 3163441 := bstep (se 2 (by rfl) ⟨1186290, by rfl⟩ : syracuseStep 3163441 = 2372581) B2372581
theorem B2811203 : Blo 1873638 2811203 := bstep (se 1 (by rfl) ⟨2108402, by rfl⟩ : syracuseStep 2811203 = 4216805) B4216805
theorem B3163475 : Blo 1873638 3163475 := bstep (se 1 (by rfl) ⟨2372606, by rfl⟩ : syracuseStep 3163475 = 4745213) B4745213
theorem B2811233 : Blo 1873638 2811233 := bstep (se 2 (by rfl) ⟨1054212, by rfl⟩ : syracuseStep 2811233 = 2108425) B2108425
theorem B6325613 : Blo 1873638 6325613 := bstep (se 3 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 6325613 = 2372105) B2372105
theorem B2811251 : Blo 1873638 2811251 := bstep (se 1 (by rfl) ⟨2108438, by rfl⟩ : syracuseStep 2811251 = 4216877) B4216877
theorem B2811281 : Blo 1873638 2811281 := bstep (se 2 (by rfl) ⟨1054230, by rfl⟩ : syracuseStep 2811281 = 2108461) B2108461
theorem B2811299 : Blo 1873638 2811299 := bstep (se 1 (by rfl) ⟨2108474, by rfl⟩ : syracuseStep 2811299 = 4216949) B4216949
theorem B6325667 : Blo 1873638 6325667 := bstep (se 1 (by rfl) ⟨4744250, by rfl⟩ : syracuseStep 6325667 = 9488501) B9488501
theorem B2811329 : Blo 1873638 2811329 := bstep (se 2 (by rfl) ⟨1054248, by rfl⟩ : syracuseStep 2811329 = 2108497) B2108497
theorem B2811347 : Blo 1873638 2811347 := bstep (se 1 (by rfl) ⟨2108510, by rfl⟩ : syracuseStep 2811347 = 4217021) B4217021
theorem B3163603 : Blo 1873638 3163603 := bstep (se 1 (by rfl) ⟨2372702, by rfl⟩ : syracuseStep 3163603 = 4745405) B4745405
theorem B2811377 : Blo 1873638 2811377 := bstep (se 2 (by rfl) ⟨1054266, by rfl⟩ : syracuseStep 2811377 = 2108533) B2108533
theorem B2811395 : Blo 1873638 2811395 := bstep (se 1 (by rfl) ⟨2108546, by rfl⟩ : syracuseStep 2811395 = 4217093) B4217093
theorem B2811425 : Blo 1873638 2811425 := bstep (se 2 (by rfl) ⟨1054284, by rfl⟩ : syracuseStep 2811425 = 2108569) B2108569
theorem B2811443 : Blo 1873638 2811443 := bstep (se 1 (by rfl) ⟨2108582, by rfl⟩ : syracuseStep 2811443 = 4217165) B4217165
theorem B2811473 : Blo 1873638 2811473 := bstep (se 2 (by rfl) ⟨1054302, by rfl⟩ : syracuseStep 2811473 = 2108605) B2108605
theorem B3163745 : Blo 1873638 3163745 := bstep (se 2 (by rfl) ⟨1186404, by rfl⟩ : syracuseStep 3163745 = 2372809) B2372809
theorem B2811491 : Blo 1873638 2811491 := bstep (se 1 (by rfl) ⟨2108618, by rfl⟩ : syracuseStep 2811491 = 4217237) B4217237
theorem B2811521 : Blo 1873638 2811521 := bstep (se 2 (by rfl) ⟨1054320, by rfl⟩ : syracuseStep 2811521 = 2108641) B2108641
theorem B12011141 : Blo 1873638 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B2811539 : Blo 1873638 2811539 := bstep (se 1 (by rfl) ⟨2108654, by rfl⟩ : syracuseStep 2811539 = 4217309) B4217309
theorem B3557027 : Blo 1873638 3557027 := bstep (se 1 (by rfl) ⟨2667770, by rfl⟩ : syracuseStep 3557027 = 5335541) B5335541
theorem B6325937 : Blo 1873638 6325937 := bstep (se 2 (by rfl) ⟨2372226, by rfl⟩ : syracuseStep 6325937 = 4744453) B4744453
theorem B2811569 : Blo 1873638 2811569 := bstep (se 2 (by rfl) ⟨1054338, by rfl⟩ : syracuseStep 2811569 = 2108677) B2108677
theorem B10823345 : Blo 1873638 10823345 := bstep (se 2 (by rfl) ⟨4058754, by rfl⟩ : syracuseStep 10823345 = 8117509) B8117509
theorem B2811587 : Blo 1873638 2811587 := bstep (se 1 (by rfl) ⟨2108690, by rfl⟩ : syracuseStep 2811587 = 4217381) B4217381
theorem B2811617 : Blo 1873638 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B3163873 : Blo 1873638 3163873 := bstep (se 2 (by rfl) ⟨1186452, by rfl⟩ : syracuseStep 3163873 = 2372905) B2372905
theorem B2811635 : Blo 1873638 2811635 := bstep (se 1 (by rfl) ⟨2108726, by rfl⟩ : syracuseStep 2811635 = 4217453) B4217453
theorem B3163907 : Blo 1873638 3163907 := bstep (se 1 (by rfl) ⟨2372930, by rfl⟩ : syracuseStep 3163907 = 4745861) B4745861
theorem B2811665 : Blo 1873638 2811665 := bstep (se 2 (by rfl) ⟨1054374, by rfl⟩ : syracuseStep 2811665 = 2108749) B2108749
theorem B6006545 : Blo 1873638 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B7702307 : Blo 1873638 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B2811683 : Blo 1873638 2811683 := bstep (se 1 (by rfl) ⟨2108762, by rfl⟩ : syracuseStep 2811683 = 4217525) B4217525
theorem B9488177 : Blo 1873638 9488177 := bstep (se 2 (by rfl) ⟨3558066, by rfl⟩ : syracuseStep 9488177 = 7116133) B7116133
theorem B2811713 : Blo 1873638 2811713 := bstep (se 2 (by rfl) ⟨1054392, by rfl⟩ : syracuseStep 2811713 = 2108785) B2108785
theorem B2811731 : Blo 1873638 2811731 := bstep (se 1 (by rfl) ⟨2108798, by rfl⟩ : syracuseStep 2811731 = 4217597) B4217597
theorem B2811761 : Blo 1873638 2811761 := bstep (se 2 (by rfl) ⟨1054410, by rfl⟩ : syracuseStep 2811761 = 2108821) B2108821
theorem B2811779 : Blo 1873638 2811779 := bstep (se 1 (by rfl) ⟨2108834, by rfl⟩ : syracuseStep 2811779 = 4217669) B4217669
theorem B3164035 : Blo 1873638 3164035 := bstep (se 1 (by rfl) ⟨2373026, by rfl⟩ : syracuseStep 3164035 = 4746053) B4746053
theorem B7120781 : Blo 1873638 7120781 := bstep (se 3 (by rfl) ⟨1335146, by rfl⟩ : syracuseStep 7120781 = 2670293) B2670293
theorem B2811809 : Blo 1873638 2811809 := bstep (se 2 (by rfl) ⟨1054428, by rfl⟩ : syracuseStep 2811809 = 2108857) B2108857
theorem B2811827 : Blo 1873638 2811827 := bstep (se 1 (by rfl) ⟨2108870, by rfl⟩ : syracuseStep 2811827 = 4217741) B4217741
theorem B2811857 : Blo 1873638 2811857 := bstep (se 2 (by rfl) ⟨1054446, by rfl⟩ : syracuseStep 2811857 = 2108893) B2108893
theorem B2811875 : Blo 1873638 2811875 := bstep (se 1 (by rfl) ⟨2108906, by rfl⟩ : syracuseStep 2811875 = 4217813) B4217813
theorem B14231537 : Blo 1873638 14231537 := bstep (se 2 (by rfl) ⟨5336826, by rfl⟩ : syracuseStep 14231537 = 10673653) B10673653
theorem B2811905 : Blo 1873638 2811905 := bstep (se 2 (by rfl) ⟨1054464, by rfl⟩ : syracuseStep 2811905 = 2108929) B2108929
theorem B5859341 : Blo 1873638 5859341 := bstep (se 3 (by rfl) ⟨1098626, by rfl⟩ : syracuseStep 5859341 = 2197253) B2197253
theorem B3164177 : Blo 1873638 3164177 := bstep (se 2 (by rfl) ⟨1186566, by rfl⟩ : syracuseStep 3164177 = 2373133) B2373133
theorem B2811923 : Blo 1873638 2811923 := bstep (se 1 (by rfl) ⟨2108942, by rfl⟩ : syracuseStep 2811923 = 4217885) B4217885
theorem B2811953 : Blo 1873638 2811953 := bstep (se 2 (by rfl) ⟨1054482, by rfl⟩ : syracuseStep 2811953 = 2108965) B2108965
theorem B2811971 : Blo 1873638 2811971 := bstep (se 1 (by rfl) ⟨2108978, by rfl⟩ : syracuseStep 2811971 = 4217957) B4217957
theorem B2812001 : Blo 1873638 2812001 := bstep (se 2 (by rfl) ⟨1054500, by rfl⟩ : syracuseStep 2812001 = 2109001) B2109001
theorem B8546417 : Blo 1873638 8546417 := bstep (se 2 (by rfl) ⟨3204906, by rfl⟩ : syracuseStep 8546417 = 6409813) B6409813
theorem B3205235 : Blo 1873638 3205235 := bstep (se 1 (by rfl) ⟨2403926, by rfl⟩ : syracuseStep 3205235 = 4807853) B4807853
theorem B2812019 : Blo 1873638 2812019 := bstep (se 1 (by rfl) ⟨2109014, by rfl⟩ : syracuseStep 2812019 = 4218029) B4218029
theorem B2812049 : Blo 1873638 2812049 := bstep (se 2 (by rfl) ⟨1054518, by rfl⟩ : syracuseStep 2812049 = 2109037) B2109037
theorem B3164305 : Blo 1873638 3164305 := bstep (se 2 (by rfl) ⟨1186614, by rfl⟩ : syracuseStep 3164305 = 2373229) B2373229
theorem B10676387 : Blo 1873638 10676387 := bstep (se 1 (by rfl) ⟨8007290, by rfl⟩ : syracuseStep 10676387 = 16014581) B16014581
theorem B2812067 : Blo 1873638 2812067 := bstep (se 1 (by rfl) ⟨2109050, by rfl⟩ : syracuseStep 2812067 = 4218101) B4218101
theorem B3164339 : Blo 1873638 3164339 := bstep (se 1 (by rfl) ⟨2373254, by rfl⟩ : syracuseStep 3164339 = 4746509) B4746509
theorem B20269237 : Blo 1873638 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B2812097 : Blo 1873638 2812097 := bstep (se 2 (by rfl) ⟨1054536, by rfl⟩ : syracuseStep 2812097 = 2109073) B2109073
theorem B6326477 : Blo 1873638 6326477 := bstep (se 3 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 6326477 = 2372429) B2372429
theorem B4745425 : Blo 1873638 4745425 := bstep (se 2 (by rfl) ⟨1779534, by rfl⟩ : syracuseStep 4745425 = 3559069) B3559069
theorem B2812115 : Blo 1873638 2812115 := bstep (se 1 (by rfl) ⟨2109086, by rfl⟩ : syracuseStep 2812115 = 4218173) B4218173
theorem B2812145 : Blo 1873638 2812145 := bstep (se 2 (by rfl) ⟨1054554, by rfl⟩ : syracuseStep 2812145 = 2109109) B2109109
theorem B3205379 : Blo 1873638 3205379 := bstep (se 1 (by rfl) ⟨2404034, by rfl⟩ : syracuseStep 3205379 = 4808069) B4808069
theorem B6326531 : Blo 1873638 6326531 := bstep (se 1 (by rfl) ⟨4744898, by rfl⟩ : syracuseStep 6326531 = 9489797) B9489797
theorem B2812163 : Blo 1873638 2812163 := bstep (se 1 (by rfl) ⟨2109122, by rfl⟩ : syracuseStep 2812163 = 4218245) B4218245
theorem B2812193 : Blo 1873638 2812193 := bstep (se 2 (by rfl) ⟨1054572, by rfl⟩ : syracuseStep 2812193 = 2109145) B2109145
theorem B2812211 : Blo 1873638 2812211 := bstep (se 1 (by rfl) ⟨2109158, by rfl⟩ : syracuseStep 2812211 = 4218317) B4218317
theorem B3164467 : Blo 1873638 3164467 := bstep (se 1 (by rfl) ⟨2373350, by rfl⟩ : syracuseStep 3164467 = 4746701) B4746701
theorem B2812241 : Blo 1873638 2812241 := bstep (se 2 (by rfl) ⟨1054590, by rfl⟩ : syracuseStep 2812241 = 2109181) B2109181
theorem B2812259 : Blo 1873638 2812259 := bstep (se 1 (by rfl) ⟨2109194, by rfl⟩ : syracuseStep 2812259 = 4218389) B4218389
theorem B2812289 : Blo 1873638 2812289 := bstep (se 2 (by rfl) ⟨1054608, by rfl⟩ : syracuseStep 2812289 = 2109217) B2109217
theorem B2812307 : Blo 1873638 2812307 := bstep (se 1 (by rfl) ⟨2109230, by rfl⟩ : syracuseStep 2812307 = 4218461) B4218461
theorem B2812337 : Blo 1873638 2812337 := bstep (se 2 (by rfl) ⟨1054626, by rfl⟩ : syracuseStep 2812337 = 2109253) B2109253
theorem B20269493 : Blo 1873638 20269493 := bstep (se 5 (by rfl) ⟨950132, by rfl⟩ : syracuseStep 20269493 = 1900265) B1900265
theorem B3164609 : Blo 1873638 3164609 := bstep (se 2 (by rfl) ⟨1186728, by rfl⟩ : syracuseStep 3164609 = 2373457) B2373457
theorem B2812355 : Blo 1873638 2812355 := bstep (se 1 (by rfl) ⟨2109266, by rfl⟩ : syracuseStep 2812355 = 4218533) B4218533
theorem B2812385 : Blo 1873638 2812385 := bstep (se 2 (by rfl) ⟨1054644, by rfl⟩ : syracuseStep 2812385 = 2109289) B2109289
theorem B4745699 : Blo 1873638 4745699 := bstep (se 1 (by rfl) ⟨3559274, by rfl⟩ : syracuseStep 4745699 = 7118549) B7118549
theorem B2812403 : Blo 1873638 2812403 := bstep (se 1 (by rfl) ⟨2109302, by rfl⟩ : syracuseStep 2812403 = 4218605) B4218605
theorem B6326801 : Blo 1873638 6326801 := bstep (se 2 (by rfl) ⟨2372550, by rfl⟩ : syracuseStep 6326801 = 4745101) B4745101
theorem B2812433 : Blo 1873638 2812433 := bstep (se 2 (by rfl) ⟨1054662, by rfl⟩ : syracuseStep 2812433 = 2109325) B2109325
theorem B2107939 : Blo 1873638 2107939 := bstep (se 1 (by rfl) ⟨1580954, by rfl⟩ : syracuseStep 2107939 = 3161909) B3161909
theorem B2812451 : Blo 1873638 2812451 := bstep (se 1 (by rfl) ⟨2109338, by rfl⟩ : syracuseStep 2812451 = 4218677) B4218677
theorem B2812481 : Blo 1873638 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B3164737 : Blo 1873638 3164737 := bstep (se 2 (by rfl) ⟨1186776, by rfl⟩ : syracuseStep 3164737 = 2373553) B2373553
theorem B5065297 : Blo 1873638 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B2812499 : Blo 1873638 2812499 := bstep (se 1 (by rfl) ⟨2109374, by rfl⟩ : syracuseStep 2812499 = 4218749) B4218749
theorem B3164771 : Blo 1873638 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B6007405 : Blo 1873638 6007405 := bstep (se 3 (by rfl) ⟨1126388, by rfl⟩ : syracuseStep 6007405 = 2252777) B2252777
theorem B2812529 : Blo 1873638 2812529 := bstep (se 2 (by rfl) ⟨1054698, by rfl⟩ : syracuseStep 2812529 = 2109397) B2109397
theorem B2812547 : Blo 1873638 2812547 := bstep (se 1 (by rfl) ⟨2109410, by rfl⟩ : syracuseStep 2812547 = 4218821) B4218821
theorem B2812577 : Blo 1873638 2812577 := bstep (se 2 (by rfl) ⟨1054716, by rfl⟩ : syracuseStep 2812577 = 2109433) B2109433
theorem B4745891 : Blo 1873638 4745891 := bstep (se 1 (by rfl) ⟨3559418, by rfl⟩ : syracuseStep 4745891 = 7118837) B7118837
theorem B2108083 : Blo 1873638 2108083 := bstep (se 1 (by rfl) ⟨1581062, by rfl⟩ : syracuseStep 2108083 = 3162125) B3162125
theorem B2812595 : Blo 1873638 2812595 := bstep (se 1 (by rfl) ⟨2109446, by rfl⟩ : syracuseStep 2812595 = 4218893) B4218893
theorem B5335757 : Blo 1873638 5335757 := bstep (se 3 (by rfl) ⟨1000454, by rfl⟩ : syracuseStep 5335757 = 2000909) B2000909
theorem B3558097 : Blo 1873638 3558097 := bstep (se 2 (by rfl) ⟨1334286, by rfl⟩ : syracuseStep 3558097 = 2668573) B2668573
theorem B2812625 : Blo 1873638 2812625 := bstep (se 2 (by rfl) ⟨1054734, by rfl⟩ : syracuseStep 2812625 = 2109469) B2109469
theorem B2312915 : Blo 1873638 2312915 := bstep (se 1 (by rfl) ⟨1734686, by rfl⟩ : syracuseStep 2312915 = 3469373) B3469373
theorem B2812643 : Blo 1873638 2812643 := bstep (se 1 (by rfl) ⟨2109482, by rfl⟩ : syracuseStep 2812643 = 4218965) B4218965
theorem B3164899 : Blo 1873638 3164899 := bstep (se 1 (by rfl) ⟨2373674, by rfl⟩ : syracuseStep 3164899 = 4747349) B4747349
theorem B2812673 : Blo 1873638 2812673 := bstep (se 2 (by rfl) ⟨1054752, by rfl⟩ : syracuseStep 2812673 = 2109505) B2109505
theorem B2812691 : Blo 1873638 2812691 := bstep (se 1 (by rfl) ⟨2109518, by rfl⟩ : syracuseStep 2812691 = 4219037) B4219037
theorem B2812721 : Blo 1873638 2812721 := bstep (se 2 (by rfl) ⟨1054770, by rfl⟩ : syracuseStep 2812721 = 2109541) B2109541
theorem B2108227 : Blo 1873638 2108227 := bstep (se 1 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 2108227 = 3162341) B3162341
theorem B2812739 : Blo 1873638 2812739 := bstep (se 1 (by rfl) ⟨2109554, by rfl⟩ : syracuseStep 2812739 = 4219109) B4219109
theorem B13519685 : Blo 1873638 13519685 := bstep (se 4 (by rfl) ⟨1267470, by rfl⟩ : syracuseStep 13519685 = 2534941) B2534941
theorem B8112973 : Blo 1873638 8112973 := bstep (se 3 (by rfl) ⟨1521182, by rfl⟩ : syracuseStep 8112973 = 3042365) B3042365
theorem B2812769 : Blo 1873638 2812769 := bstep (se 2 (by rfl) ⟨1054788, by rfl⟩ : syracuseStep 2812769 = 2109577) B2109577
theorem B2001763 : Blo 1873638 2001763 := bstep (se 1 (by rfl) ⟨1501322, by rfl⟩ : syracuseStep 2001763 = 3002645) B3002645
theorem B3165041 : Blo 1873638 3165041 := bstep (se 2 (by rfl) ⟨1186890, by rfl⟩ : syracuseStep 3165041 = 2373781) B2373781
theorem B2812787 : Blo 1873638 2812787 := bstep (se 1 (by rfl) ⟨2109590, by rfl⟩ : syracuseStep 2812787 = 4219181) B4219181
theorem B2812817 : Blo 1873638 2812817 := bstep (se 2 (by rfl) ⟨1054806, by rfl⟩ : syracuseStep 2812817 = 2109613) B2109613
theorem B2812835 : Blo 1873638 2812835 := bstep (se 1 (by rfl) ⟨2109626, by rfl⟩ : syracuseStep 2812835 = 4219253) B4219253
theorem B2812865 : Blo 1873638 2812865 := bstep (se 2 (by rfl) ⟨1054824, by rfl⟩ : syracuseStep 2812865 = 2109649) B2109649
theorem B2108371 : Blo 1873638 2108371 := bstep (se 1 (by rfl) ⟨1581278, by rfl⟩ : syracuseStep 2108371 = 3162557) B3162557
theorem B2812883 : Blo 1873638 2812883 := bstep (se 1 (by rfl) ⟨2109662, by rfl⟩ : syracuseStep 2812883 = 4219325) B4219325
theorem B17099761 : Blo 1873638 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B2812913 : Blo 1873638 2812913 := bstep (se 2 (by rfl) ⟨1054842, by rfl⟩ : syracuseStep 2812913 = 2109685) B2109685
theorem B2812931 : Blo 1873638 2812931 := bstep (se 1 (by rfl) ⟨2109698, by rfl⟩ : syracuseStep 2812931 = 4219397) B4219397
theorem B2812961 : Blo 1873638 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B6327341 : Blo 1873638 6327341 := bstep (se 3 (by rfl) ⟨1186376, by rfl⟩ : syracuseStep 6327341 = 2372753) B2372753
theorem B2812979 : Blo 1873638 2812979 := bstep (se 1 (by rfl) ⟨2109734, by rfl⟩ : syracuseStep 2812979 = 4219469) B4219469
theorem B2813009 : Blo 1873638 2813009 := bstep (se 2 (by rfl) ⟨1054878, by rfl⟩ : syracuseStep 2813009 = 2109757) B2109757
theorem B2108515 : Blo 1873638 2108515 := bstep (se 1 (by rfl) ⟨1581386, by rfl⟩ : syracuseStep 2108515 = 3162773) B3162773
theorem B6327395 : Blo 1873638 6327395 := bstep (se 1 (by rfl) ⟨4745546, by rfl⟩ : syracuseStep 6327395 = 9491093) B9491093
theorem B2813027 : Blo 1873638 2813027 := bstep (se 1 (by rfl) ⟨2109770, by rfl⟩ : syracuseStep 2813027 = 4219541) B4219541
theorem B2813057 : Blo 1873638 2813057 := bstep (se 2 (by rfl) ⟨1054896, by rfl⟩ : syracuseStep 2813057 = 2109793) B2109793
theorem B2813075 : Blo 1873638 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B2813105 : Blo 1873638 2813105 := bstep (se 2 (by rfl) ⟨1054914, by rfl⟩ : syracuseStep 2813105 = 2109829) B2109829
theorem B2813123 : Blo 1873638 2813123 := bstep (se 1 (by rfl) ⟨2109842, by rfl⟩ : syracuseStep 2813123 = 4219685) B4219685
theorem B3001555 : Blo 1873638 3001555 := bstep (se 1 (by rfl) ⟨2251166, by rfl⟩ : syracuseStep 3001555 = 4502333) B4502333
theorem B2813153 : Blo 1873638 2813153 := bstep (se 2 (by rfl) ⟨1054932, by rfl⟩ : syracuseStep 2813153 = 2109865) B2109865
theorem B9489635 : Blo 1873638 9489635 := bstep (se 1 (by rfl) ⟨7117226, by rfl⟩ : syracuseStep 9489635 = 14234453) B14234453
theorem B2108659 : Blo 1873638 2108659 := bstep (se 1 (by rfl) ⟨1581494, by rfl⟩ : syracuseStep 2108659 = 3162989) B3162989
theorem B2813171 : Blo 1873638 2813171 := bstep (se 1 (by rfl) ⟨2109878, by rfl⟩ : syracuseStep 2813171 = 4219757) B4219757
theorem B2813201 : Blo 1873638 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B2002195 : Blo 1873638 2002195 := bstep (se 1 (by rfl) ⟨1501646, by rfl⟩ : syracuseStep 2002195 = 3003293) B3003293
theorem B2813219 : Blo 1873638 2813219 := bstep (se 1 (by rfl) ⟨2109914, by rfl⟩ : syracuseStep 2813219 = 4219829) B4219829
theorem B2813249 : Blo 1873638 2813249 := bstep (se 2 (by rfl) ⟨1054968, by rfl⟩ : syracuseStep 2813249 = 2109937) B2109937
theorem B11398477 : Blo 1873638 11398477 := bstep (se 3 (by rfl) ⟨2137214, by rfl⟩ : syracuseStep 11398477 = 4274429) B4274429
theorem B2813267 : Blo 1873638 2813267 := bstep (se 1 (by rfl) ⟨2109950, by rfl⟩ : syracuseStep 2813267 = 4219901) B4219901
theorem B6327665 : Blo 1873638 6327665 := bstep (se 2 (by rfl) ⟨2372874, by rfl⟩ : syracuseStep 6327665 = 4745749) B4745749
theorem B2813297 : Blo 1873638 2813297 := bstep (se 2 (by rfl) ⟨1054986, by rfl⟩ : syracuseStep 2813297 = 2109973) B2109973
theorem B2108803 : Blo 1873638 2108803 := bstep (se 1 (by rfl) ⟨1581602, by rfl⟩ : syracuseStep 2108803 = 3163205) B3163205
theorem B2813315 : Blo 1873638 2813315 := bstep (se 1 (by rfl) ⟨2109986, by rfl⟩ : syracuseStep 2813315 = 4219973) B4219973
theorem B2813345 : Blo 1873638 2813345 := bstep (se 2 (by rfl) ⟨1055004, by rfl⟩ : syracuseStep 2813345 = 2110009) B2110009
theorem B3378595 : Blo 1873638 3378595 := bstep (se 1 (by rfl) ⟨2533946, by rfl⟩ : syracuseStep 3378595 = 5067893) B5067893
theorem B2813363 : Blo 1873638 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B7114189 : Blo 1873638 7114189 := bstep (se 3 (by rfl) ⟨1333910, by rfl⟩ : syracuseStep 7114189 = 2667821) B2667821
theorem B2813393 : Blo 1873638 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B2813411 : Blo 1873638 2813411 := bstep (se 1 (by rfl) ⟨2110058, by rfl⟩ : syracuseStep 2813411 = 4220117) B4220117
theorem B2813441 : Blo 1873638 2813441 := bstep (se 2 (by rfl) ⟨1055040, by rfl⟩ : syracuseStep 2813441 = 2110081) B2110081
theorem B2108947 : Blo 1873638 2108947 := bstep (se 1 (by rfl) ⟨1581710, by rfl⟩ : syracuseStep 2108947 = 3163421) B3163421
theorem B6090317 : Blo 1873638 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B4746833 : Blo 1873638 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B6753905 : Blo 1873638 6753905 := bstep (se 2 (by rfl) ⟨2532714, by rfl⟩ : syracuseStep 6753905 = 5065429) B5065429
theorem B4746883 : Blo 1873638 4746883 := bstep (se 1 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 4746883 = 7120325) B7120325
theorem B3002017 : Blo 1873638 3002017 := bstep (se 2 (by rfl) ⟨1125756, by rfl⟩ : syracuseStep 3002017 = 2251513) B2251513
theorem B2109091 : Blo 1873638 2109091 := bstep (se 1 (by rfl) ⟨1581818, by rfl⟩ : syracuseStep 2109091 = 3163637) B3163637
theorem B3559153 : Blo 1873638 3559153 := bstep (se 2 (by rfl) ⟨1334682, by rfl⟩ : syracuseStep 3559153 = 2669365) B2669365
theorem B3002113 : Blo 1873638 3002113 := bstep (se 2 (by rfl) ⟨1125792, by rfl⟩ : syracuseStep 3002113 = 2251585) B2251585
theorem B4747025 : Blo 1873638 4747025 := bstep (se 2 (by rfl) ⟨1780134, by rfl⟩ : syracuseStep 4747025 = 3560269) B3560269
theorem B2109235 : Blo 1873638 2109235 := bstep (se 1 (by rfl) ⟨1581926, by rfl⟩ : syracuseStep 2109235 = 3163853) B3163853
theorem B5336941 : Blo 1873638 5336941 := bstep (se 3 (by rfl) ⟨1000676, by rfl⟩ : syracuseStep 5336941 = 2001353) B2001353
theorem B6328205 : Blo 1873638 6328205 := bstep (se 3 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 6328205 = 2373077) B2373077
theorem B2404243 : Blo 1873638 2404243 := bstep (se 1 (by rfl) ⟨1803182, by rfl⟩ : syracuseStep 2404243 = 3606365) B3606365
theorem B3002273 : Blo 1873638 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B5779363 : Blo 1873638 5779363 := bstep (se 1 (by rfl) ⟨4334522, by rfl⟩ : syracuseStep 5779363 = 8669045) B8669045
theorem B2109379 : Blo 1873638 2109379 := bstep (se 1 (by rfl) ⟨1582034, by rfl⟩ : syracuseStep 2109379 = 3164069) B3164069
theorem B6328259 : Blo 1873638 6328259 := bstep (se 1 (by rfl) ⟨4746194, by rfl⟩ : syracuseStep 6328259 = 9492389) B9492389
theorem B9490445 : Blo 1873638 9490445 := bstep (se 3 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 9490445 = 3558917) B3558917
theorem B10276877 : Blo 1873638 10276877 := bstep (se 3 (by rfl) ⟨1926914, by rfl⟩ : syracuseStep 10276877 = 3853829) B3853829
theorem B3207185 : Blo 1873638 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B2371619 : Blo 1873638 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B2109523 : Blo 1873638 2109523 := bstep (se 1 (by rfl) ⟨1582142, by rfl⟩ : syracuseStep 2109523 = 3164285) B3164285
theorem B3559555 : Blo 1873638 3559555 := bstep (se 1 (by rfl) ⟨2669666, by rfl⟩ : syracuseStep 3559555 = 5339333) B5339333
theorem B3559601 : Blo 1873638 3559601 := bstep (se 2 (by rfl) ⟨1334850, by rfl⟩ : syracuseStep 3559601 = 2669701) B2669701
theorem B6328529 : Blo 1873638 6328529 := bstep (se 2 (by rfl) ⟨2373198, by rfl⟩ : syracuseStep 6328529 = 4746397) B4746397
theorem B7114979 : Blo 1873638 7114979 := bstep (se 1 (by rfl) ⟨5336234, by rfl⟩ : syracuseStep 7114979 = 10672469) B10672469
theorem B2109667 : Blo 1873638 2109667 := bstep (se 1 (by rfl) ⟨1582250, by rfl⟩ : syracuseStep 2109667 = 3164501) B3164501
theorem B6754595 : Blo 1873638 6754595 := bstep (se 1 (by rfl) ⟨5065946, by rfl⟩ : syracuseStep 6754595 = 10131893) B10131893
theorem B12013859 : Blo 1873638 12013859 := bstep (se 1 (by rfl) ⟨9010394, by rfl⟩ : syracuseStep 12013859 = 18020789) B18020789
theorem B2404675 : Blo 1873638 2404675 := bstep (se 1 (by rfl) ⟨1803506, by rfl⟩ : syracuseStep 2404675 = 3607013) B3607013
theorem B2109811 : Blo 1873638 2109811 := bstep (se 1 (by rfl) ⟨1582358, by rfl⟩ : syracuseStep 2109811 = 3164717) B3164717
theorem B3559889 : Blo 1873638 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B5067245 : Blo 1873638 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B2109955 : Blo 1873638 2109955 := bstep (se 1 (by rfl) ⟨1582466, by rfl⟩ : syracuseStep 2109955 = 3164933) B3164933
theorem B13513229 : Blo 1873638 13513229 := bstep (se 3 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 13513229 = 5067461) B5067461
theorem B3248723 : Blo 1873638 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B16011917 : Blo 1873638 16011917 := bstep (se 3 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 16011917 = 6004469) B6004469
theorem B4502179 : Blo 1873638 4502179 := bstep (se 1 (by rfl) ⟨3376634, by rfl⟩ : syracuseStep 4502179 = 6753269) B6753269
theorem B2372323 : Blo 1873638 2372323 := bstep (se 1 (by rfl) ⟨1779242, by rfl⟩ : syracuseStep 2372323 = 3558485) B3558485
theorem B6329069 : Blo 1873638 6329069 := bstep (se 3 (by rfl) ⟨1186700, by rfl⟩ : syracuseStep 6329069 = 2373401) B2373401
theorem B6329123 : Blo 1873638 6329123 := bstep (se 1 (by rfl) ⟨4746842, by rfl⟩ : syracuseStep 6329123 = 9493685) B9493685
theorem B2372419 : Blo 1873638 2372419 := bstep (se 1 (by rfl) ⟨1779314, by rfl⟩ : syracuseStep 2372419 = 3558629) B3558629
theorem B7115633 : Blo 1873638 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B5338001 : Blo 1873638 5338001 := bstep (se 2 (by rfl) ⟨2001750, by rfl⟩ : syracuseStep 5338001 = 4003501) B4003501
theorem B10671011 : Blo 1873638 10671011 := bstep (se 1 (by rfl) ⟨8003258, by rfl⟩ : syracuseStep 10671011 = 16006517) B16006517
theorem B4215761 : Blo 1873638 4215761 := bstep (se 2 (by rfl) ⟨1580910, by rfl⟩ : syracuseStep 4215761 = 3161821) B3161821
theorem B4215779 : Blo 1873638 4215779 := bstep (se 1 (by rfl) ⟨3161834, by rfl⟩ : syracuseStep 4215779 = 6323669) B6323669
theorem B12170245 : Blo 1873638 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B6329393 : Blo 1873638 6329393 := bstep (se 2 (by rfl) ⟨2373522, by rfl⟩ : syracuseStep 6329393 = 4747045) B4747045
theorem B4502641 : Blo 1873638 4502641 := bstep (se 2 (by rfl) ⟨1688490, by rfl⟩ : syracuseStep 4502641 = 3376981) B3376981
theorem B3560611 : Blo 1873638 3560611 := bstep (se 1 (by rfl) ⟨2670458, by rfl⟩ : syracuseStep 3560611 = 5340917) B5340917
theorem B4502737 : Blo 1873638 4502737 := bstep (se 2 (by rfl) ⟨1688526, by rfl⟩ : syracuseStep 4502737 = 3377053) B3377053
theorem B8008931 : Blo 1873638 8008931 := bstep (se 1 (by rfl) ⟨6006698, by rfl⟩ : syracuseStep 8008931 = 12013397) B12013397
theorem B4216049 : Blo 1873638 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B4216067 : Blo 1873638 4216067 := bstep (se 1 (by rfl) ⟨3162050, by rfl⟩ : syracuseStep 4216067 = 6324101) B6324101
theorem B2372915 : Blo 1873638 2372915 := bstep (se 1 (by rfl) ⟨1779686, by rfl⟩ : syracuseStep 2372915 = 3559373) B3559373
theorem B2667907 : Blo 1873638 2667907 := bstep (se 1 (by rfl) ⟨2000930, by rfl⟩ : syracuseStep 2667907 = 4001861) B4001861
theorem B5068241 : Blo 1873638 5068241 := bstep (se 2 (by rfl) ⟨1900590, by rfl⟩ : syracuseStep 5068241 = 3801181) B3801181
theorem B4216337 : Blo 1873638 4216337 := bstep (se 2 (by rfl) ⟨1581126, by rfl⟩ : syracuseStep 4216337 = 3162253) B3162253
theorem B4216355 : Blo 1873638 4216355 := bstep (se 1 (by rfl) ⟨3162266, by rfl⟩ : syracuseStep 4216355 = 6324533) B6324533
theorem B5338673 : Blo 1873638 5338673 := bstep (se 2 (by rfl) ⟨2002002, by rfl⟩ : syracuseStep 5338673 = 4004005) B4004005
theorem B6329933 : Blo 1873638 6329933 := bstep (se 3 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 6329933 = 2373725) B2373725
theorem B5068369 : Blo 1873638 5068369 := bstep (se 2 (by rfl) ⟨1900638, by rfl⟩ : syracuseStep 5068369 = 3801277) B3801277
theorem B3044945 : Blo 1873638 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B6329987 : Blo 1873638 6329987 := bstep (se 1 (by rfl) ⟨4747490, by rfl⟩ : syracuseStep 6329987 = 9494981) B9494981
theorem B3004067 : Blo 1873638 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B2668243 : Blo 1873638 2668243 := bstep (se 1 (by rfl) ⟨2001182, by rfl⟩ : syracuseStep 2668243 = 4002365) B4002365
theorem B1873651 : Blo 1873638 1873651 := bstep (se 1 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 1873651 = 2810477) B2810477
theorem B1873667 : Blo 1873638 1873667 := bstep (se 1 (by rfl) ⟨1405250, by rfl⟩ : syracuseStep 1873667 = 2810501) B2810501
theorem B1873683 : Blo 1873638 1873683 := bstep (se 1 (by rfl) ⟨1405262, by rfl⟩ : syracuseStep 1873683 = 2810525) B2810525
theorem B1873699 : Blo 1873638 1873699 := bstep (se 1 (by rfl) ⟨1405274, by rfl⟩ : syracuseStep 1873699 = 2810549) B2810549
theorem B4216625 : Blo 1873638 4216625 := bstep (se 2 (by rfl) ⟨1581234, by rfl⟩ : syracuseStep 4216625 = 3162469) B3162469
theorem B1873715 : Blo 1873638 1873715 := bstep (se 1 (by rfl) ⟨1405286, by rfl⟩ : syracuseStep 1873715 = 2810573) B2810573
theorem B1873731 : Blo 1873638 1873731 := bstep (se 1 (by rfl) ⟨1405298, by rfl⟩ : syracuseStep 1873731 = 2810597) B2810597
theorem B4216643 : Blo 1873638 4216643 := bstep (se 1 (by rfl) ⟨3162482, by rfl⟩ : syracuseStep 4216643 = 6324965) B6324965
theorem B1873747 : Blo 1873638 1873747 := bstep (se 1 (by rfl) ⟨1405310, by rfl⟩ : syracuseStep 1873747 = 2810621) B2810621
theorem B1873763 : Blo 1873638 1873763 := bstep (se 1 (by rfl) ⟨1405322, by rfl⟩ : syracuseStep 1873763 = 2810645) B2810645
theorem B1873779 : Blo 1873638 1873779 := bstep (se 1 (by rfl) ⟨1405334, by rfl⟩ : syracuseStep 1873779 = 2810669) B2810669
theorem B1873795 : Blo 1873638 1873795 := bstep (se 1 (by rfl) ⟨1405346, by rfl⟩ : syracuseStep 1873795 = 2810693) B2810693
theorem B10672013 : Blo 1873638 10672013 := bstep (se 3 (by rfl) ⟨2001002, by rfl⟩ : syracuseStep 10672013 = 4002005) B4002005
theorem B6330257 : Blo 1873638 6330257 := bstep (se 2 (by rfl) ⟨2373846, by rfl⟩ : syracuseStep 6330257 = 4747693) B4747693
theorem B1873811 : Blo 1873638 1873811 := bstep (se 1 (by rfl) ⟨1405358, by rfl⟩ : syracuseStep 1873811 = 2810717) B2810717
theorem B1873827 : Blo 1873638 1873827 := bstep (se 1 (by rfl) ⟨1405370, by rfl⟩ : syracuseStep 1873827 = 2810741) B2810741
theorem B1873843 : Blo 1873638 1873843 := bstep (se 1 (by rfl) ⟨1405382, by rfl⟩ : syracuseStep 1873843 = 2810765) B2810765
theorem B1873859 : Blo 1873638 1873859 := bstep (se 1 (by rfl) ⟨1405394, by rfl⟩ : syracuseStep 1873859 = 2810789) B2810789
theorem B1873875 : Blo 1873638 1873875 := bstep (se 1 (by rfl) ⟨1405406, by rfl⟩ : syracuseStep 1873875 = 2810813) B2810813
theorem B1873891 : Blo 1873638 1873891 := bstep (se 1 (by rfl) ⟨1405418, by rfl⟩ : syracuseStep 1873891 = 2810837) B2810837
theorem B1873907 : Blo 1873638 1873907 := bstep (se 1 (by rfl) ⟨1405430, by rfl⟩ : syracuseStep 1873907 = 2810861) B2810861
theorem B2373619 : Blo 1873638 2373619 := bstep (se 1 (by rfl) ⟨1780214, by rfl⟩ : syracuseStep 2373619 = 3560429) B3560429
theorem B1873923 : Blo 1873638 1873923 := bstep (se 1 (by rfl) ⟨1405442, by rfl⟩ : syracuseStep 1873923 = 2810885) B2810885
theorem B4003843 : Blo 1873638 4003843 := bstep (se 1 (by rfl) ⟨3002882, by rfl⟩ : syracuseStep 4003843 = 6005765) B6005765
theorem B6412301 : Blo 1873638 6412301 := bstep (se 3 (by rfl) ⟨1202306, by rfl⟩ : syracuseStep 6412301 = 2404613) B2404613
theorem B4167697 : Blo 1873638 4167697 := bstep (se 2 (by rfl) ⟨1562886, by rfl⟩ : syracuseStep 4167697 = 3125773) B3125773
theorem B1873939 : Blo 1873638 1873939 := bstep (se 1 (by rfl) ⟨1405454, by rfl⟩ : syracuseStep 1873939 = 2810909) B2810909
theorem B1873955 : Blo 1873638 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B5068835 : Blo 1873638 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B1873971 : Blo 1873638 1873971 := bstep (se 1 (by rfl) ⟨1405478, by rfl⟩ : syracuseStep 1873971 = 2810957) B2810957
theorem B1873987 : Blo 1873638 1873987 := bstep (se 1 (by rfl) ⟨1405490, by rfl⟩ : syracuseStep 1873987 = 2810981) B2810981
theorem B4216913 : Blo 1873638 4216913 := bstep (se 2 (by rfl) ⟨1581342, by rfl⟩ : syracuseStep 4216913 = 3162685) B3162685
theorem B1874003 : Blo 1873638 1874003 := bstep (se 1 (by rfl) ⟨1405502, by rfl⟩ : syracuseStep 1874003 = 2811005) B2811005
theorem B2373715 : Blo 1873638 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B1874019 : Blo 1873638 1874019 := bstep (se 1 (by rfl) ⟨1405514, by rfl⟩ : syracuseStep 1874019 = 2811029) B2811029
theorem B4216931 : Blo 1873638 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B1874035 : Blo 1873638 1874035 := bstep (se 1 (by rfl) ⟨1405526, by rfl⟩ : syracuseStep 1874035 = 2811053) B2811053
theorem B1874051 : Blo 1873638 1874051 := bstep (se 1 (by rfl) ⟨1405538, by rfl⟩ : syracuseStep 1874051 = 2811077) B2811077
theorem B1874067 : Blo 1873638 1874067 := bstep (se 1 (by rfl) ⟨1405550, by rfl⟩ : syracuseStep 1874067 = 2811101) B2811101
theorem B1874083 : Blo 1873638 1874083 := bstep (se 1 (by rfl) ⟨1405562, by rfl⟩ : syracuseStep 1874083 = 2811125) B2811125
theorem B1874099 : Blo 1873638 1874099 := bstep (se 1 (by rfl) ⟨1405574, by rfl⟩ : syracuseStep 1874099 = 2811149) B2811149
theorem B1874115 : Blo 1873638 1874115 := bstep (se 1 (by rfl) ⟨1405586, by rfl⟩ : syracuseStep 1874115 = 2811173) B2811173
theorem B1874131 : Blo 1873638 1874131 := bstep (se 1 (by rfl) ⟨1405598, by rfl⟩ : syracuseStep 1874131 = 2811197) B2811197
theorem B1874147 : Blo 1873638 1874147 := bstep (se 1 (by rfl) ⟨1405610, by rfl⟩ : syracuseStep 1874147 = 2811221) B2811221
theorem B12015857 : Blo 1873638 12015857 := bstep (se 2 (by rfl) ⟨4505946, by rfl⟩ : syracuseStep 12015857 = 9011893) B9011893
theorem B1874163 : Blo 1873638 1874163 := bstep (se 1 (by rfl) ⟨1405622, by rfl⟩ : syracuseStep 1874163 = 2811245) B2811245
theorem B2668801 : Blo 1873638 2668801 := bstep (se 2 (by rfl) ⟨1000800, by rfl⟩ : syracuseStep 2668801 = 2001601) B2001601
theorem B1874179 : Blo 1873638 1874179 := bstep (se 1 (by rfl) ⟨1405634, by rfl⟩ : syracuseStep 1874179 = 2811269) B2811269
theorem B1874195 : Blo 1873638 1874195 := bstep (se 1 (by rfl) ⟨1405646, by rfl⟩ : syracuseStep 1874195 = 2811293) B2811293
theorem B1874211 : Blo 1873638 1874211 := bstep (se 1 (by rfl) ⟨1405658, by rfl⟩ : syracuseStep 1874211 = 2811317) B2811317
theorem B2668835 : Blo 1873638 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B7117091 : Blo 1873638 7117091 := bstep (se 1 (by rfl) ⟨5337818, by rfl⟩ : syracuseStep 7117091 = 10675637) B10675637
theorem B7117105 : Blo 1873638 7117105 := bstep (se 2 (by rfl) ⟨2668914, by rfl⟩ : syracuseStep 7117105 = 5337829) B5337829
theorem B5069105 : Blo 1873638 5069105 := bstep (se 2 (by rfl) ⟨1900914, by rfl⟩ : syracuseStep 5069105 = 3801829) B3801829
theorem B1874227 : Blo 1873638 1874227 := bstep (se 1 (by rfl) ⟨1405670, by rfl⟩ : syracuseStep 1874227 = 2811341) B2811341
theorem B1874243 : Blo 1873638 1874243 := bstep (se 1 (by rfl) ⟨1405682, by rfl⟩ : syracuseStep 1874243 = 2811365) B2811365
theorem B5339459 : Blo 1873638 5339459 := bstep (se 1 (by rfl) ⟨4004594, by rfl⟩ : syracuseStep 5339459 = 8009189) B8009189
theorem B1874259 : Blo 1873638 1874259 := bstep (se 1 (by rfl) ⟨1405694, by rfl⟩ : syracuseStep 1874259 = 2811389) B2811389
theorem B1874275 : Blo 1873638 1874275 := bstep (se 1 (by rfl) ⟨1405706, by rfl⟩ : syracuseStep 1874275 = 2811413) B2811413
theorem B4217201 : Blo 1873638 4217201 := bstep (se 2 (by rfl) ⟨1581450, by rfl⟩ : syracuseStep 4217201 = 3162901) B3162901
theorem B1874291 : Blo 1873638 1874291 := bstep (se 1 (by rfl) ⟨1405718, by rfl⟩ : syracuseStep 1874291 = 2811437) B2811437
theorem B1874307 : Blo 1873638 1874307 := bstep (se 1 (by rfl) ⟨1405730, by rfl⟩ : syracuseStep 1874307 = 2811461) B2811461
theorem B4217219 : Blo 1873638 4217219 := bstep (se 1 (by rfl) ⟨3162914, by rfl⟩ : syracuseStep 4217219 = 6325829) B6325829
theorem B1874323 : Blo 1873638 1874323 := bstep (se 1 (by rfl) ⟨1405742, by rfl⟩ : syracuseStep 1874323 = 2811485) B2811485
theorem B1874339 : Blo 1873638 1874339 := bstep (se 1 (by rfl) ⟨1405754, by rfl⟩ : syracuseStep 1874339 = 2811509) B2811509
theorem B5700017 : Blo 1873638 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B8010161 : Blo 1873638 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B1874355 : Blo 1873638 1874355 := bstep (se 1 (by rfl) ⟨1405766, by rfl⟩ : syracuseStep 1874355 = 2811533) B2811533
theorem B1874371 : Blo 1873638 1874371 := bstep (se 1 (by rfl) ⟨1405778, by rfl⟩ : syracuseStep 1874371 = 2811557) B2811557
theorem B21690821 : Blo 1873638 21690821 := bstep (se 4 (by rfl) ⟨2033514, by rfl⟩ : syracuseStep 21690821 = 4067029) B4067029
theorem B1874387 : Blo 1873638 1874387 := bstep (se 1 (by rfl) ⟨1405790, by rfl⟩ : syracuseStep 1874387 = 2811581) B2811581
theorem B1874403 : Blo 1873638 1874403 := bstep (se 1 (by rfl) ⟨1405802, by rfl⟩ : syracuseStep 1874403 = 2811605) B2811605
theorem B9624035 : Blo 1873638 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B1874419 : Blo 1873638 1874419 := bstep (se 1 (by rfl) ⟨1405814, by rfl⟩ : syracuseStep 1874419 = 2811629) B2811629
theorem B1874435 : Blo 1873638 1874435 := bstep (se 1 (by rfl) ⟨1405826, by rfl⟩ : syracuseStep 1874435 = 2811653) B2811653
theorem B1874451 : Blo 1873638 1874451 := bstep (se 1 (by rfl) ⟨1405838, by rfl⟩ : syracuseStep 1874451 = 2811677) B2811677
theorem B1874467 : Blo 1873638 1874467 := bstep (se 1 (by rfl) ⟨1405850, by rfl⟩ : syracuseStep 1874467 = 2811701) B2811701
theorem B1874483 : Blo 1873638 1874483 := bstep (se 1 (by rfl) ⟨1405862, by rfl⟩ : syracuseStep 1874483 = 2811725) B2811725
theorem B1874499 : Blo 1873638 1874499 := bstep (se 1 (by rfl) ⟨1405874, by rfl⟩ : syracuseStep 1874499 = 2811749) B2811749
theorem B1874515 : Blo 1873638 1874515 := bstep (se 1 (by rfl) ⟨1405886, by rfl⟩ : syracuseStep 1874515 = 2811773) B2811773
theorem B1874531 : Blo 1873638 1874531 := bstep (se 1 (by rfl) ⟨1405898, by rfl⟩ : syracuseStep 1874531 = 2811797) B2811797
theorem B5413475 : Blo 1873638 5413475 := bstep (se 1 (by rfl) ⟨4060106, by rfl⟩ : syracuseStep 5413475 = 8120213) B8120213
theorem B1874547 : Blo 1873638 1874547 := bstep (se 1 (by rfl) ⟨1405910, by rfl⟩ : syracuseStep 1874547 = 2811821) B2811821
theorem B1874563 : Blo 1873638 1874563 := bstep (se 1 (by rfl) ⟨1405922, by rfl⟩ : syracuseStep 1874563 = 2811845) B2811845
theorem B5339789 : Blo 1873638 5339789 := bstep (se 3 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 5339789 = 2002421) B2002421
theorem B4217489 : Blo 1873638 4217489 := bstep (se 2 (by rfl) ⟨1581558, by rfl⟩ : syracuseStep 4217489 = 3163117) B3163117
theorem B1874579 : Blo 1873638 1874579 := bstep (se 1 (by rfl) ⟨1405934, by rfl⟩ : syracuseStep 1874579 = 2811869) B2811869
theorem B4217507 : Blo 1873638 4217507 := bstep (se 1 (by rfl) ⟨3163130, by rfl⟩ : syracuseStep 4217507 = 6326261) B6326261
theorem B1874595 : Blo 1873638 1874595 := bstep (se 1 (by rfl) ⟨1405946, by rfl⟩ : syracuseStep 1874595 = 2811893) B2811893
theorem B10558129 : Blo 1873638 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B1874611 : Blo 1873638 1874611 := bstep (se 1 (by rfl) ⟨1405958, by rfl⟩ : syracuseStep 1874611 = 2811917) B2811917
theorem B6085315 : Blo 1873638 6085315 := bstep (se 1 (by rfl) ⟨4563986, by rfl⟩ : syracuseStep 6085315 = 9127973) B9127973
theorem B1874627 : Blo 1873638 1874627 := bstep (se 1 (by rfl) ⟨1405970, by rfl⟩ : syracuseStep 1874627 = 2811941) B2811941
theorem B5339857 : Blo 1873638 5339857 := bstep (se 2 (by rfl) ⟨2002446, by rfl⟩ : syracuseStep 5339857 = 4004893) B4004893
theorem B1874643 : Blo 1873638 1874643 := bstep (se 1 (by rfl) ⟨1405982, by rfl⟩ : syracuseStep 1874643 = 2811965) B2811965
theorem B1874659 : Blo 1873638 1874659 := bstep (se 1 (by rfl) ⟨1405994, by rfl⟩ : syracuseStep 1874659 = 2811989) B2811989
theorem B1874675 : Blo 1873638 1874675 := bstep (se 1 (by rfl) ⟨1406006, by rfl⟩ : syracuseStep 1874675 = 2812013) B2812013
theorem B3799811 : Blo 1873638 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B1874691 : Blo 1873638 1874691 := bstep (se 1 (by rfl) ⟨1406018, by rfl⟩ : syracuseStep 1874691 = 2812037) B2812037
theorem B1874707 : Blo 1873638 1874707 := bstep (se 1 (by rfl) ⟨1406030, by rfl⟩ : syracuseStep 1874707 = 2812061) B2812061
theorem B1874723 : Blo 1873638 1874723 := bstep (se 1 (by rfl) ⟨1406042, by rfl⟩ : syracuseStep 1874723 = 2812085) B2812085
theorem B1874739 : Blo 1873638 1874739 := bstep (se 1 (by rfl) ⟨1406054, by rfl⟩ : syracuseStep 1874739 = 2812109) B2812109
theorem B1874755 : Blo 1873638 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B2669393 : Blo 1873638 2669393 := bstep (se 2 (by rfl) ⟨1001022, by rfl⟩ : syracuseStep 2669393 = 2002045) B2002045
theorem B1874771 : Blo 1873638 1874771 := bstep (se 1 (by rfl) ⟨1406078, by rfl⟩ : syracuseStep 1874771 = 2812157) B2812157
theorem B1874787 : Blo 1873638 1874787 := bstep (se 1 (by rfl) ⟨1406090, by rfl⟩ : syracuseStep 1874787 = 2812181) B2812181
theorem B9493361 : Blo 1873638 9493361 := bstep (se 2 (by rfl) ⟨3560010, by rfl⟩ : syracuseStep 9493361 = 7120021) B7120021
theorem B1874803 : Blo 1873638 1874803 := bstep (se 1 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 1874803 = 2812205) B2812205
theorem B1874819 : Blo 1873638 1874819 := bstep (se 1 (by rfl) ⟨1406114, by rfl⟩ : syracuseStep 1874819 = 2812229) B2812229
theorem B5700493 : Blo 1873638 5700493 := bstep (se 3 (by rfl) ⟨1068842, by rfl⟩ : syracuseStep 5700493 = 2137685) B2137685
theorem B1874835 : Blo 1873638 1874835 := bstep (se 1 (by rfl) ⟨1406126, by rfl⟩ : syracuseStep 1874835 = 2812253) B2812253
theorem B2669473 : Blo 1873638 2669473 := bstep (se 2 (by rfl) ⟨1001052, by rfl⟩ : syracuseStep 2669473 = 2002105) B2002105
theorem B1874851 : Blo 1873638 1874851 := bstep (se 1 (by rfl) ⟨1406138, by rfl⟩ : syracuseStep 1874851 = 2812277) B2812277
theorem B4217777 : Blo 1873638 4217777 := bstep (se 2 (by rfl) ⟨1581666, by rfl⟩ : syracuseStep 4217777 = 3163333) B3163333
theorem B1874867 : Blo 1873638 1874867 := bstep (se 1 (by rfl) ⟨1406150, by rfl⟩ : syracuseStep 1874867 = 2812301) B2812301
theorem B4217795 : Blo 1873638 4217795 := bstep (se 1 (by rfl) ⟨3163346, by rfl⟩ : syracuseStep 4217795 = 6326693) B6326693
theorem B1874883 : Blo 1873638 1874883 := bstep (se 1 (by rfl) ⟨1406162, by rfl⟩ : syracuseStep 1874883 = 2812325) B2812325
theorem B1874899 : Blo 1873638 1874899 := bstep (se 1 (by rfl) ⟨1406174, by rfl⟩ : syracuseStep 1874899 = 2812349) B2812349
theorem B16014307 : Blo 1873638 16014307 := bstep (se 1 (by rfl) ⟨12010730, by rfl⟩ : syracuseStep 16014307 = 24021461) B24021461
theorem B1874915 : Blo 1873638 1874915 := bstep (se 1 (by rfl) ⟨1406186, by rfl⟩ : syracuseStep 1874915 = 2812373) B2812373
theorem B5340131 : Blo 1873638 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B5069795 : Blo 1873638 5069795 := bstep (se 1 (by rfl) ⟨3802346, by rfl⟩ : syracuseStep 5069795 = 7604693) B7604693
theorem B1874931 : Blo 1873638 1874931 := bstep (se 1 (by rfl) ⟨1406198, by rfl⟩ : syracuseStep 1874931 = 2812397) B2812397
theorem B1874947 : Blo 1873638 1874947 := bstep (se 1 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 1874947 = 2812421) B2812421
theorem B6003725 : Blo 1873638 6003725 := bstep (se 3 (by rfl) ⟨1125698, by rfl⟩ : syracuseStep 6003725 = 2251397) B2251397
theorem B1874963 : Blo 1873638 1874963 := bstep (se 1 (by rfl) ⟨1406222, by rfl⟩ : syracuseStep 1874963 = 2812445) B2812445
theorem B45595669 : Blo 1873638 45595669 := bstep (se 6 (by rfl) ⟨1068648, by rfl⟩ : syracuseStep 45595669 = 2137297) B2137297
theorem B1874979 : Blo 1873638 1874979 := bstep (se 1 (by rfl) ⟨1406234, by rfl⟩ : syracuseStep 1874979 = 2812469) B2812469
theorem B1874995 : Blo 1873638 1874995 := bstep (se 1 (by rfl) ⟨1406246, by rfl⟩ : syracuseStep 1874995 = 2812493) B2812493
theorem B5069873 : Blo 1873638 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1875011 : Blo 1873638 1875011 := bstep (se 1 (by rfl) ⟨1406258, by rfl⟩ : syracuseStep 1875011 = 2812517) B2812517
theorem B1875027 : Blo 1873638 1875027 := bstep (se 1 (by rfl) ⟨1406270, by rfl⟩ : syracuseStep 1875027 = 2812541) B2812541
theorem B1875043 : Blo 1873638 1875043 := bstep (se 1 (by rfl) ⟨1406282, by rfl⟩ : syracuseStep 1875043 = 2812565) B2812565
theorem B1875059 : Blo 1873638 1875059 := bstep (se 1 (by rfl) ⟨1406294, by rfl⟩ : syracuseStep 1875059 = 2812589) B2812589
theorem B1875075 : Blo 1873638 1875075 := bstep (se 1 (by rfl) ⟨1406306, by rfl⟩ : syracuseStep 1875075 = 2812613) B2812613
theorem B14228621 : Blo 1873638 14228621 := bstep (se 3 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 14228621 = 5335733) B5335733
theorem B12016781 : Blo 1873638 12016781 := bstep (se 3 (by rfl) ⟨2253146, by rfl⟩ : syracuseStep 12016781 = 4506293) B4506293
theorem B1875091 : Blo 1873638 1875091 := bstep (se 1 (by rfl) ⟨1406318, by rfl⟩ : syracuseStep 1875091 = 2812637) B2812637
theorem B1875107 : Blo 1873638 1875107 := bstep (se 1 (by rfl) ⟨1406330, by rfl⟩ : syracuseStep 1875107 = 2812661) B2812661
theorem B1875123 : Blo 1873638 1875123 := bstep (se 1 (by rfl) ⟨1406342, by rfl⟩ : syracuseStep 1875123 = 2812685) B2812685
theorem B1875139 : Blo 1873638 1875139 := bstep (se 1 (by rfl) ⟨1406354, by rfl⟩ : syracuseStep 1875139 = 2812709) B2812709
theorem B4218065 : Blo 1873638 4218065 := bstep (se 2 (by rfl) ⟨1581774, by rfl⟩ : syracuseStep 4218065 = 3163549) B3163549
theorem B1875155 : Blo 1873638 1875155 := bstep (se 1 (by rfl) ⟨1406366, by rfl⟩ : syracuseStep 1875155 = 2812733) B2812733
theorem B4218083 : Blo 1873638 4218083 := bstep (se 1 (by rfl) ⟨3163562, by rfl⟩ : syracuseStep 4218083 = 6327125) B6327125
theorem B1875171 : Blo 1873638 1875171 := bstep (se 1 (by rfl) ⟨1406378, by rfl⟩ : syracuseStep 1875171 = 2812757) B2812757
theorem B1875187 : Blo 1873638 1875187 := bstep (se 1 (by rfl) ⟨1406390, by rfl⟩ : syracuseStep 1875187 = 2812781) B2812781
theorem B1875203 : Blo 1873638 1875203 := bstep (se 1 (by rfl) ⟨1406402, by rfl⟩ : syracuseStep 1875203 = 2812805) B2812805
theorem B1875219 : Blo 1873638 1875219 := bstep (se 1 (by rfl) ⟨1406414, by rfl⟩ : syracuseStep 1875219 = 2812829) B2812829
theorem B2850083 : Blo 1873638 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B1875235 : Blo 1873638 1875235 := bstep (se 1 (by rfl) ⟨1406426, by rfl⟩ : syracuseStep 1875235 = 2812853) B2812853
theorem B1875251 : Blo 1873638 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B1875267 : Blo 1873638 1875267 := bstep (se 1 (by rfl) ⟨1406450, by rfl⟩ : syracuseStep 1875267 = 2812901) B2812901
theorem B1875283 : Blo 1873638 1875283 := bstep (se 1 (by rfl) ⟨1406462, by rfl⟩ : syracuseStep 1875283 = 2812925) B2812925
theorem B1875299 : Blo 1873638 1875299 := bstep (se 1 (by rfl) ⟨1406474, by rfl⟩ : syracuseStep 1875299 = 2812949) B2812949
theorem B1875315 : Blo 1873638 1875315 := bstep (se 1 (by rfl) ⟨1406486, by rfl⟩ : syracuseStep 1875315 = 2812973) B2812973
theorem B1875331 : Blo 1873638 1875331 := bstep (se 1 (by rfl) ⟨1406498, by rfl⟩ : syracuseStep 1875331 = 2812997) B2812997
theorem B1875347 : Blo 1873638 1875347 := bstep (se 1 (by rfl) ⟨1406510, by rfl⟩ : syracuseStep 1875347 = 2813021) B2813021
theorem B1875363 : Blo 1873638 1875363 := bstep (se 1 (by rfl) ⟨1406522, by rfl⟩ : syracuseStep 1875363 = 2813045) B2813045
theorem B1875379 : Blo 1873638 1875379 := bstep (se 1 (by rfl) ⟨1406534, by rfl⟩ : syracuseStep 1875379 = 2813069) B2813069
theorem B1875395 : Blo 1873638 1875395 := bstep (se 1 (by rfl) ⟨1406546, by rfl⟩ : syracuseStep 1875395 = 2813093) B2813093
theorem B2252243 : Blo 1873638 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B1875411 : Blo 1873638 1875411 := bstep (se 1 (by rfl) ⟨1406558, by rfl⟩ : syracuseStep 1875411 = 2813117) B2813117
theorem B1875427 : Blo 1873638 1875427 := bstep (se 1 (by rfl) ⟨1406570, by rfl⟩ : syracuseStep 1875427 = 2813141) B2813141
theorem B4218353 : Blo 1873638 4218353 := bstep (se 2 (by rfl) ⟨1581882, by rfl⟩ : syracuseStep 4218353 = 3163765) B3163765
theorem B1875443 : Blo 1873638 1875443 := bstep (se 1 (by rfl) ⟨1406582, by rfl⟩ : syracuseStep 1875443 = 2813165) B2813165
theorem B2252291 : Blo 1873638 2252291 := bstep (se 1 (by rfl) ⟨1689218, by rfl⟩ : syracuseStep 2252291 = 3378437) B3378437
theorem B4218371 : Blo 1873638 4218371 := bstep (se 1 (by rfl) ⟨3163778, by rfl⟩ : syracuseStep 4218371 = 6327557) B6327557
theorem B1875459 : Blo 1873638 1875459 := bstep (se 1 (by rfl) ⟨1406594, by rfl⟩ : syracuseStep 1875459 = 2813189) B2813189
theorem B1875475 : Blo 1873638 1875475 := bstep (se 1 (by rfl) ⟨1406606, by rfl⟩ : syracuseStep 1875475 = 2813213) B2813213
theorem B1875491 : Blo 1873638 1875491 := bstep (se 1 (by rfl) ⟨1406618, by rfl⟩ : syracuseStep 1875491 = 2813237) B2813237
theorem B1875507 : Blo 1873638 1875507 := bstep (se 1 (by rfl) ⟨1406630, by rfl⟩ : syracuseStep 1875507 = 2813261) B2813261
theorem B1875523 : Blo 1873638 1875523 := bstep (se 1 (by rfl) ⟨1406642, by rfl⟩ : syracuseStep 1875523 = 2813285) B2813285
theorem B1875539 : Blo 1873638 1875539 := bstep (se 1 (by rfl) ⟨1406654, by rfl⟩ : syracuseStep 1875539 = 2813309) B2813309
theorem B2137699 : Blo 1873638 2137699 := bstep (se 1 (by rfl) ⟨1603274, by rfl⟩ : syracuseStep 2137699 = 3206549) B3206549
theorem B1875555 : Blo 1873638 1875555 := bstep (se 1 (by rfl) ⟨1406666, by rfl⟩ : syracuseStep 1875555 = 2813333) B2813333
theorem B1875571 : Blo 1873638 1875571 := bstep (se 1 (by rfl) ⟨1406678, by rfl⟩ : syracuseStep 1875571 = 2813357) B2813357
theorem B1875587 : Blo 1873638 1875587 := bstep (se 1 (by rfl) ⟨1406690, by rfl⟩ : syracuseStep 1875587 = 2813381) B2813381
theorem B1875603 : Blo 1873638 1875603 := bstep (se 1 (by rfl) ⟨1406702, by rfl⟩ : syracuseStep 1875603 = 2813405) B2813405
theorem B1875619 : Blo 1873638 1875619 := bstep (se 1 (by rfl) ⟨1406714, by rfl⟩ : syracuseStep 1875619 = 2813429) B2813429
theorem B6323885 : Blo 1873638 6323885 := bstep (se 3 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 6323885 = 2371457) B2371457
theorem B4742833 : Blo 1873638 4742833 := bstep (se 2 (by rfl) ⟨1778562, by rfl⟩ : syracuseStep 4742833 = 3557125) B3557125
theorem B2670259 : Blo 1873638 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B1875635 : Blo 1873638 1875635 := bstep (se 1 (by rfl) ⟨1406726, by rfl⟩ : syracuseStep 1875635 = 2813453) B2813453
theorem B11402957 : Blo 1873638 11402957 := bstep (se 3 (by rfl) ⟨2138054, by rfl⟩ : syracuseStep 11402957 = 4276109) B4276109
theorem B6323939 : Blo 1873638 6323939 := bstep (se 1 (by rfl) ⟨4742954, by rfl⟩ : syracuseStep 6323939 = 9485909) B9485909
theorem B7118563 : Blo 1873638 7118563 := bstep (se 1 (by rfl) ⟨5338922, by rfl⟩ : syracuseStep 7118563 = 10677845) B10677845
theorem B4218641 : Blo 1873638 4218641 := bstep (se 2 (by rfl) ⟨1581990, by rfl⟩ : syracuseStep 4218641 = 3163981) B3163981
theorem B3161875 : Blo 1873638 3161875 := bstep (se 1 (by rfl) ⟨2371406, by rfl⟩ : syracuseStep 3161875 = 4742813) B4742813
theorem B4218659 : Blo 1873638 4218659 := bstep (se 1 (by rfl) ⟨3163994, by rfl⟩ : syracuseStep 4218659 = 6327989) B6327989
theorem B5340973 : Blo 1873638 5340973 := bstep (se 3 (by rfl) ⟨1001432, by rfl⟩ : syracuseStep 5340973 = 2002865) B2002865
theorem B4005713 : Blo 1873638 4005713 := bstep (se 2 (by rfl) ⟨1502142, by rfl⟩ : syracuseStep 4005713 = 3004285) B3004285
theorem B3162017 : Blo 1873638 3162017 := bstep (se 2 (by rfl) ⟨1185756, by rfl⟩ : syracuseStep 3162017 = 2371513) B2371513
theorem B4743107 : Blo 1873638 4743107 := bstep (se 1 (by rfl) ⟨3557330, by rfl⟩ : syracuseStep 4743107 = 7114661) B7114661
theorem B5341133 : Blo 1873638 5341133 := bstep (se 3 (by rfl) ⟨1001462, by rfl⟩ : syracuseStep 5341133 = 2002925) B2002925
theorem B6324209 : Blo 1873638 6324209 := bstep (se 2 (by rfl) ⟨2371578, by rfl⟩ : syracuseStep 6324209 = 4743157) B4743157
theorem B2138123 : Blo 1873638 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B3162199 : Blo 1873638 3162199 := bstep (se 1 (by rfl) ⟨2371649, by rfl⟩ : syracuseStep 3162199 = 4743299) B4743299
theorem B6324317 : Blo 1873638 6324317 := bstep (se 3 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 6324317 = 2371619) B2371619
theorem B4219019 : Blo 1873638 4219019 := bstep (se 1 (by rfl) ⟨3164264, by rfl⟩ : syracuseStep 4219019 = 6328529) B6328529
theorem B4743319 : Blo 1873638 4743319 := bstep (se 1 (by rfl) ⟨3557489, by rfl⟩ : syracuseStep 4743319 = 7114979) B7114979
theorem B4219073 : Blo 1873638 4219073 := bstep (se 2 (by rfl) ⟨1582152, by rfl⟩ : syracuseStep 4219073 = 3164305) B3164305
theorem B2851031 : Blo 1873638 2851031 := bstep (se 1 (by rfl) ⟨2138273, by rfl⟩ : syracuseStep 2851031 = 4276547) B4276547
theorem B27025649 : Blo 1873638 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B3801367 : Blo 1873638 3801367 := bstep (se 1 (by rfl) ⟨2851025, by rfl⟩ : syracuseStep 3801367 = 5702051) B5702051
theorem B5701963 : Blo 1873638 5701963 := bstep (se 1 (by rfl) ⟨4276472, by rfl⟩ : syracuseStep 5701963 = 8552945) B8552945
theorem B9617795 : Blo 1873638 9617795 := bstep (se 1 (by rfl) ⟨7213346, by rfl⟩ : syracuseStep 9617795 = 14426693) B14426693
theorem B4219289 : Blo 1873638 4219289 := bstep (se 2 (by rfl) ⟨1582233, by rfl⟩ : syracuseStep 4219289 = 3164467) B3164467
theorem B10674611 : Blo 1873638 10674611 := bstep (se 1 (by rfl) ⟨8005958, by rfl⟩ : syracuseStep 10674611 = 16011917) B16011917
theorem B4219379 : Blo 1873638 4219379 := bstep (se 1 (by rfl) ⟨3164534, by rfl⟩ : syracuseStep 4219379 = 6329069) B6329069
theorem B4219415 : Blo 1873638 4219415 := bstep (se 1 (by rfl) ⟨3164561, by rfl⟩ : syracuseStep 4219415 = 6329123) B6329123
theorem B4743755 : Blo 1873638 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B2810507 : Blo 1873638 2810507 := bstep (se 1 (by rfl) ⟨2107880, by rfl⟩ : syracuseStep 2810507 = 4215761) B4215761
theorem B2810519 : Blo 1873638 2810519 := bstep (se 1 (by rfl) ⟨2107889, by rfl⟩ : syracuseStep 2810519 = 4215779) B4215779
theorem B3162827 : Blo 1873638 3162827 := bstep (se 1 (by rfl) ⟨2372120, by rfl⟩ : syracuseStep 3162827 = 4744241) B4744241
theorem B4219595 : Blo 1873638 4219595 := bstep (se 1 (by rfl) ⟨3164696, by rfl⟩ : syracuseStep 4219595 = 6329393) B6329393
theorem B2810585 : Blo 1873638 2810585 := bstep (se 2 (by rfl) ⟨1053969, by rfl⟩ : syracuseStep 2810585 = 2107939) B2107939
theorem B4219649 : Blo 1873638 4219649 := bstep (se 2 (by rfl) ⟨1582368, by rfl⟩ : syracuseStep 4219649 = 3164737) B3164737
theorem B8553239 : Blo 1873638 8553239 := bstep (se 1 (by rfl) ⟨6414929, by rfl⟩ : syracuseStep 8553239 = 12829859) B12829859
theorem B2851609 : Blo 1873638 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B2810699 : Blo 1873638 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B3162955 : Blo 1873638 3162955 := bstep (se 1 (by rfl) ⟨2372216, by rfl⟩ : syracuseStep 3162955 = 4744433) B4744433
theorem B2810711 : Blo 1873638 2810711 := bstep (se 1 (by rfl) ⟨2108033, by rfl⟩ : syracuseStep 2810711 = 4216067) B4216067
theorem B2810777 : Blo 1873638 2810777 := bstep (se 2 (by rfl) ⟨1054041, by rfl⟩ : syracuseStep 2810777 = 2108083) B2108083
theorem B4744129 : Blo 1873638 4744129 := bstep (se 2 (by rfl) ⟨1779048, by rfl⟩ : syracuseStep 4744129 = 3558097) B3558097
theorem B7119809 : Blo 1873638 7119809 := bstep (se 2 (by rfl) ⟨2669928, by rfl⟩ : syracuseStep 7119809 = 5339857) B5339857
theorem B3163097 : Blo 1873638 3163097 := bstep (se 2 (by rfl) ⟨1186161, by rfl⟩ : syracuseStep 3163097 = 2372323) B2372323
theorem B4219865 : Blo 1873638 4219865 := bstep (se 2 (by rfl) ⟨1582449, by rfl⟩ : syracuseStep 4219865 = 3164899) B3164899
theorem B2810891 : Blo 1873638 2810891 := bstep (se 1 (by rfl) ⟨2108168, by rfl⟩ : syracuseStep 2810891 = 4216337) B4216337
theorem B2810903 : Blo 1873638 2810903 := bstep (se 1 (by rfl) ⟨2108177, by rfl⟩ : syracuseStep 2810903 = 4216355) B4216355
theorem B4219955 : Blo 1873638 4219955 := bstep (se 1 (by rfl) ⟨3164966, by rfl⟩ : syracuseStep 4219955 = 6329933) B6329933
theorem B4219991 : Blo 1873638 4219991 := bstep (se 1 (by rfl) ⟨3164993, by rfl⟩ : syracuseStep 4219991 = 6329987) B6329987
theorem B2810969 : Blo 1873638 2810969 := bstep (se 2 (by rfl) ⟨1054113, by rfl⟩ : syracuseStep 2810969 = 2108227) B2108227
theorem B3163225 : Blo 1873638 3163225 := bstep (se 2 (by rfl) ⟨1186209, by rfl⟩ : syracuseStep 3163225 = 2372419) B2372419
theorem B16008293 : Blo 1873638 16008293 := bstep (se 4 (by rfl) ⟨1500777, by rfl⟩ : syracuseStep 16008293 = 3001555) B3001555
theorem B2811083 : Blo 1873638 2811083 := bstep (se 1 (by rfl) ⟨2108312, by rfl⟩ : syracuseStep 2811083 = 4216625) B4216625
theorem B6325451 : Blo 1873638 6325451 := bstep (se 1 (by rfl) ⟨4744088, by rfl⟩ : syracuseStep 6325451 = 9488177) B9488177
theorem B2811095 : Blo 1873638 2811095 := bstep (se 1 (by rfl) ⟨2108321, by rfl⟩ : syracuseStep 2811095 = 4216643) B4216643
theorem B6005981 : Blo 1873638 6005981 := bstep (se 3 (by rfl) ⟨1126121, by rfl⟩ : syracuseStep 6005981 = 2252243) B2252243
theorem B4220171 : Blo 1873638 4220171 := bstep (se 1 (by rfl) ⟨3165128, by rfl⟩ : syracuseStep 4220171 = 6330257) B6330257
theorem B2811161 : Blo 1873638 2811161 := bstep (se 2 (by rfl) ⟨1054185, by rfl⟩ : syracuseStep 2811161 = 2108371) B2108371
theorem B22799681 : Blo 1873638 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B9487691 : Blo 1873638 9487691 := bstep (se 1 (by rfl) ⟨7115768, by rfl⟩ : syracuseStep 9487691 = 14231537) B14231537
theorem B60794225 : Blo 1873638 60794225 := bstep (se 2 (by rfl) ⟨22797834, by rfl⟩ : syracuseStep 60794225 = 45595669) B45595669
theorem B2811275 : Blo 1873638 2811275 := bstep (se 1 (by rfl) ⟨2108456, by rfl⟩ : syracuseStep 2811275 = 4216913) B4216913
theorem B2811287 : Blo 1873638 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B2811353 : Blo 1873638 2811353 := bstep (se 2 (by rfl) ⟨1054257, by rfl⟩ : syracuseStep 2811353 = 2108515) B2108515
theorem B6325721 : Blo 1873638 6325721 := bstep (se 2 (by rfl) ⟨2372145, by rfl⟩ : syracuseStep 6325721 = 4744291) B4744291
theorem B4744727 : Blo 1873638 4744727 := bstep (se 1 (by rfl) ⟨3558545, by rfl⟩ : syracuseStep 4744727 = 7117091) B7117091
theorem B8119853 : Blo 1873638 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B2811467 : Blo 1873638 2811467 := bstep (se 1 (by rfl) ⟨2108600, by rfl⟩ : syracuseStep 2811467 = 4217201) B4217201
theorem B2811479 : Blo 1873638 2811479 := bstep (se 1 (by rfl) ⟨2108609, by rfl⟩ : syracuseStep 2811479 = 4217219) B4217219
theorem B14460547 : Blo 1873638 14460547 := bstep (se 1 (by rfl) ⟨10845410, by rfl⟩ : syracuseStep 14460547 = 21690821) B21690821
theorem B3163799 : Blo 1873638 3163799 := bstep (se 1 (by rfl) ⟨2372849, by rfl⟩ : syracuseStep 3163799 = 4745699) B4745699
theorem B6416023 : Blo 1873638 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B2811545 : Blo 1873638 2811545 := bstep (se 2 (by rfl) ⟨1054329, by rfl⟩ : syracuseStep 2811545 = 2108659) B2108659
theorem B2811659 : Blo 1873638 2811659 := bstep (se 1 (by rfl) ⟨2108744, by rfl⟩ : syracuseStep 2811659 = 4217489) B4217489
theorem B15197969 : Blo 1873638 15197969 := bstep (se 2 (by rfl) ⟨5699238, by rfl⟩ : syracuseStep 15197969 = 11398477) B11398477
theorem B2811671 : Blo 1873638 2811671 := bstep (se 1 (by rfl) ⟨2108753, by rfl⟩ : syracuseStep 2811671 = 4217507) B4217507
theorem B3163927 : Blo 1873638 3163927 := bstep (se 1 (by rfl) ⟨2372945, by rfl⟩ : syracuseStep 3163927 = 4745891) B4745891
theorem B3557171 : Blo 1873638 3557171 := bstep (se 1 (by rfl) ⟨2667878, by rfl⟩ : syracuseStep 3557171 = 5335757) B5335757
theorem B2533207 : Blo 1873638 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B3557209 : Blo 1873638 3557209 := bstep (se 2 (by rfl) ⟨1333953, by rfl⟩ : syracuseStep 3557209 = 2667907) B2667907
theorem B2811737 : Blo 1873638 2811737 := bstep (se 2 (by rfl) ⟨1054401, by rfl⟩ : syracuseStep 2811737 = 2108803) B2108803
theorem B10676069 : Blo 1873638 10676069 := bstep (se 4 (by rfl) ⟨1000881, by rfl⟩ : syracuseStep 10676069 = 2001763) B2001763
theorem B9013123 : Blo 1873638 9013123 := bstep (se 1 (by rfl) ⟨6759842, by rfl⟩ : syracuseStep 9013123 = 13519685) B13519685
theorem B2811851 : Blo 1873638 2811851 := bstep (se 1 (by rfl) ⟨2108888, by rfl⟩ : syracuseStep 2811851 = 4217777) B4217777
theorem B2811863 : Blo 1873638 2811863 := bstep (se 1 (by rfl) ⟨2108897, by rfl⟩ : syracuseStep 2811863 = 4217795) B4217795
theorem B2811929 : Blo 1873638 2811929 := bstep (se 2 (by rfl) ⟨1054473, by rfl⟩ : syracuseStep 2811929 = 2108947) B2108947
theorem B12822629 : Blo 1873638 12822629 := bstep (se 4 (by rfl) ⟨1202121, by rfl⟩ : syracuseStep 12822629 = 2404243) B2404243
theorem B2812043 : Blo 1873638 2812043 := bstep (se 1 (by rfl) ⟨2109032, by rfl⟩ : syracuseStep 2812043 = 4218065) B4218065
theorem B6326423 : Blo 1873638 6326423 := bstep (se 1 (by rfl) ⟨4744817, by rfl⟩ : syracuseStep 6326423 = 9489635) B9489635
theorem B2812055 : Blo 1873638 2812055 := bstep (se 1 (by rfl) ⟨2109041, by rfl⟩ : syracuseStep 2812055 = 4218083) B4218083
theorem B2812121 : Blo 1873638 2812121 := bstep (se 2 (by rfl) ⟨1054545, by rfl⟩ : syracuseStep 2812121 = 2109091) B2109091
theorem B3557657 : Blo 1873638 3557657 := bstep (se 2 (by rfl) ⟨1334121, by rfl⟩ : syracuseStep 3557657 = 2668243) B2668243
theorem B4745537 : Blo 1873638 4745537 := bstep (se 2 (by rfl) ⟨1779576, by rfl⟩ : syracuseStep 4745537 = 3559153) B3559153
theorem B2812235 : Blo 1873638 2812235 := bstep (se 1 (by rfl) ⟨2109176, by rfl⟩ : syracuseStep 2812235 = 4218353) B4218353
theorem B2812247 : Blo 1873638 2812247 := bstep (se 1 (by rfl) ⟨2109185, by rfl⟩ : syracuseStep 2812247 = 4218371) B4218371
theorem B30411125 : Blo 1873638 30411125 := bstep (se 5 (by rfl) ⟨1425521, by rfl⟩ : syracuseStep 30411125 = 2851043) B2851043
theorem B54077813 : Blo 1873638 54077813 := bstep (se 5 (by rfl) ⟨2534897, by rfl⟩ : syracuseStep 54077813 = 5069795) B5069795
theorem B3164555 : Blo 1873638 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B7121297 : Blo 1873638 7121297 := bstep (se 2 (by rfl) ⟨2670486, by rfl⟩ : syracuseStep 7121297 = 5340973) B5340973
theorem B2812313 : Blo 1873638 2812313 := bstep (se 2 (by rfl) ⟨1054617, by rfl⟩ : syracuseStep 2812313 = 2109235) B2109235
theorem B2812427 : Blo 1873638 2812427 := bstep (se 1 (by rfl) ⟨2109320, by rfl⟩ : syracuseStep 2812427 = 4218641) B4218641
theorem B3164683 : Blo 1873638 3164683 := bstep (se 1 (by rfl) ⟨2373512, by rfl⟩ : syracuseStep 3164683 = 4747025) B4747025
theorem B2812439 : Blo 1873638 2812439 := bstep (se 1 (by rfl) ⟨2109329, by rfl⟩ : syracuseStep 2812439 = 4218659) B4218659
theorem B2812505 : Blo 1873638 2812505 := bstep (se 2 (by rfl) ⟨1054689, by rfl⟩ : syracuseStep 2812505 = 2109379) B2109379
theorem B2108011 : Blo 1873638 2108011 := bstep (se 1 (by rfl) ⟨1581008, by rfl⟩ : syracuseStep 2108011 = 3162017) B3162017
theorem B2001515 : Blo 1873638 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B3164825 : Blo 1873638 3164825 := bstep (se 2 (by rfl) ⟨1186809, by rfl⟩ : syracuseStep 3164825 = 2373619) B2373619
theorem B6326963 : Blo 1873638 6326963 := bstep (se 1 (by rfl) ⟨4745222, by rfl⟩ : syracuseStep 6326963 = 9490445) B9490445
theorem B6851251 : Blo 1873638 6851251 := bstep (se 1 (by rfl) ⟨5138438, by rfl⟩ : syracuseStep 6851251 = 10276877) B10276877
theorem B5556929 : Blo 1873638 5556929 := bstep (se 2 (by rfl) ⟨2083848, by rfl⟩ : syracuseStep 5556929 = 4167697) B4167697
theorem B2812619 : Blo 1873638 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B16009933 : Blo 1873638 16009933 := bstep (se 3 (by rfl) ⟨3001862, by rfl⟩ : syracuseStep 16009933 = 6003725) B6003725
theorem B2108119 : Blo 1873638 2108119 := bstep (se 1 (by rfl) ⟨1581089, by rfl⟩ : syracuseStep 2108119 = 3162179) B3162179
theorem B2812631 : Blo 1873638 2812631 := bstep (se 1 (by rfl) ⟨2109473, by rfl⟩ : syracuseStep 2812631 = 4218947) B4218947
theorem B2812697 : Blo 1873638 2812697 := bstep (se 2 (by rfl) ⟨1054761, by rfl⟩ : syracuseStep 2812697 = 2109523) B2109523
theorem B3164953 : Blo 1873638 3164953 := bstep (se 2 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 3164953 = 2373715) B2373715
theorem B4746073 : Blo 1873638 4746073 := bstep (se 2 (by rfl) ⟨1779777, by rfl⟩ : syracuseStep 4746073 = 3559555) B3559555
theorem B2108299 : Blo 1873638 2108299 := bstep (se 1 (by rfl) ⟨1581224, by rfl⟩ : syracuseStep 2108299 = 3162449) B3162449
theorem B2812811 : Blo 1873638 2812811 := bstep (se 1 (by rfl) ⟨2109608, by rfl⟩ : syracuseStep 2812811 = 4219217) B4219217
theorem B9005975 : Blo 1873638 9005975 := bstep (se 1 (by rfl) ⟨6754481, by rfl⟩ : syracuseStep 9005975 = 13508963) B13508963
theorem B2812823 : Blo 1873638 2812823 := bstep (se 1 (by rfl) ⟨2109617, by rfl⟩ : syracuseStep 2812823 = 4219235) B4219235
theorem B6327233 : Blo 1873638 6327233 := bstep (se 2 (by rfl) ⟨2372712, by rfl⟩ : syracuseStep 6327233 = 4745425) B4745425
theorem B2812889 : Blo 1873638 2812889 := bstep (se 2 (by rfl) ⟨1054833, by rfl⟩ : syracuseStep 2812889 = 2109667) B2109667
theorem B2108407 : Blo 1873638 2108407 := bstep (se 1 (by rfl) ⟨1581305, by rfl⟩ : syracuseStep 2108407 = 3162611) B3162611
theorem B3558401 : Blo 1873638 3558401 := bstep (se 2 (by rfl) ⟨1334400, by rfl⟩ : syracuseStep 3558401 = 2668801) B2668801
theorem B2165815 : Blo 1873638 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B9489473 : Blo 1873638 9489473 := bstep (se 2 (by rfl) ⟨3558552, by rfl⟩ : syracuseStep 9489473 = 7117105) B7117105
theorem B2813003 : Blo 1873638 2813003 := bstep (se 1 (by rfl) ⟨2109752, by rfl⟩ : syracuseStep 2813003 = 4219505) B4219505
theorem B2813015 : Blo 1873638 2813015 := bstep (se 1 (by rfl) ⟨2109761, by rfl⟩ : syracuseStep 2813015 = 4219523) B4219523
theorem B3206233 : Blo 1873638 3206233 := bstep (se 2 (by rfl) ⟨1202337, by rfl⟩ : syracuseStep 3206233 = 2404675) B2404675
theorem B25996439 : Blo 1873638 25996439 := bstep (se 1 (by rfl) ⟨19497329, by rfl⟩ : syracuseStep 25996439 = 38994659) B38994659
theorem B2813081 : Blo 1873638 2813081 := bstep (se 2 (by rfl) ⟨1054905, by rfl⟩ : syracuseStep 2813081 = 2109811) B2109811
theorem B2108587 : Blo 1873638 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B3558667 : Blo 1873638 3558667 := bstep (se 1 (by rfl) ⟨2669000, by rfl⟩ : syracuseStep 3558667 = 5338001) B5338001
theorem B2813195 : Blo 1873638 2813195 := bstep (se 1 (by rfl) ⟨2109896, by rfl⟩ : syracuseStep 2813195 = 4219793) B4219793
theorem B7114007 : Blo 1873638 7114007 := bstep (se 1 (by rfl) ⟨5335505, by rfl⟩ : syracuseStep 7114007 = 10671011) B10671011
theorem B2108695 : Blo 1873638 2108695 := bstep (se 1 (by rfl) ⟨1581521, by rfl⟩ : syracuseStep 2108695 = 3163043) B3163043
theorem B2813207 : Blo 1873638 2813207 := bstep (se 1 (by rfl) ⟨2109905, by rfl⟩ : syracuseStep 2813207 = 4219811) B4219811
theorem B5336371 : Blo 1873638 5336371 := bstep (se 1 (by rfl) ⟨4002278, by rfl⟩ : syracuseStep 5336371 = 8004557) B8004557
theorem B2813273 : Blo 1873638 2813273 := bstep (se 2 (by rfl) ⟨1054977, by rfl⟩ : syracuseStep 2813273 = 2109955) B2109955
theorem B8547677 : Blo 1873638 8547677 := bstep (se 3 (by rfl) ⟨1602689, by rfl⟩ : syracuseStep 8547677 = 3205379) B3205379
theorem B2108875 : Blo 1873638 2108875 := bstep (se 1 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 2108875 = 3163313) B3163313
theorem B2813387 : Blo 1873638 2813387 := bstep (se 1 (by rfl) ⟨2110040, by rfl⟩ : syracuseStep 2813387 = 4220081) B4220081
theorem B2813399 : Blo 1873638 2813399 := bstep (se 1 (by rfl) ⟨2110049, by rfl⟩ : syracuseStep 2813399 = 4220099) B4220099
theorem B6327773 : Blo 1873638 6327773 := bstep (se 3 (by rfl) ⟨1186457, by rfl⟩ : syracuseStep 6327773 = 2372915) B2372915
theorem B5336599 : Blo 1873638 5336599 := bstep (se 1 (by rfl) ⟨4002449, by rfl⟩ : syracuseStep 5336599 = 8004899) B8004899
theorem B2108983 : Blo 1873638 2108983 := bstep (se 1 (by rfl) ⟨1581737, by rfl⟩ : syracuseStep 2108983 = 3163475) B3163475
theorem B14077505 : Blo 1873638 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B8113753 : Blo 1873638 8113753 := bstep (se 2 (by rfl) ⟨3042657, by rfl⟩ : syracuseStep 8113753 = 6085315) B6085315
theorem B3378827 : Blo 1873638 3378827 := bstep (se 1 (by rfl) ⟨2534120, by rfl⟩ : syracuseStep 3378827 = 5068241) B5068241
theorem B3559115 : Blo 1873638 3559115 := bstep (se 1 (by rfl) ⟨2669336, by rfl⟩ : syracuseStep 3559115 = 5338673) B5338673
theorem B2109163 : Blo 1873638 2109163 := bstep (se 1 (by rfl) ⟨1581872, by rfl⟩ : syracuseStep 2109163 = 3163745) B3163745
theorem B8007427 : Blo 1873638 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B10817297 : Blo 1873638 10817297 := bstep (se 2 (by rfl) ⟨4056486, by rfl⟩ : syracuseStep 10817297 = 8112973) B8112973
theorem B2371351 : Blo 1873638 2371351 := bstep (se 1 (by rfl) ⟨1778513, by rfl⟩ : syracuseStep 2371351 = 3557027) B3557027
theorem B2109271 : Blo 1873638 2109271 := bstep (se 1 (by rfl) ⟨1581953, by rfl⟩ : syracuseStep 2109271 = 3163907) B3163907
theorem B3559297 : Blo 1873638 3559297 := bstep (se 2 (by rfl) ⟨1334736, by rfl⟩ : syracuseStep 3559297 = 2669473) B2669473
theorem B7114675 : Blo 1873638 7114675 := bstep (se 1 (by rfl) ⟨5336006, by rfl⟩ : syracuseStep 7114675 = 10672013) B10672013
theorem B4747187 : Blo 1873638 4747187 := bstep (se 1 (by rfl) ⟨3560390, by rfl⟩ : syracuseStep 4747187 = 7120781) B7120781
theorem B13512653 : Blo 1873638 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B21352409 : Blo 1873638 21352409 := bstep (se 2 (by rfl) ⟨8007153, by rfl⟩ : syracuseStep 21352409 = 16014307) B16014307
theorem B16011269 : Blo 1873638 16011269 := bstep (se 4 (by rfl) ⟨1501056, by rfl⟩ : syracuseStep 16011269 = 3002113) B3002113
theorem B2109451 : Blo 1873638 2109451 := bstep (se 1 (by rfl) ⟨1582088, by rfl⟩ : syracuseStep 2109451 = 3164177) B3164177
theorem B3379223 : Blo 1873638 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B5697611 : Blo 1873638 5697611 := bstep (se 1 (by rfl) ⟨4273208, by rfl⟩ : syracuseStep 5697611 = 8546417) B8546417
theorem B2109559 : Blo 1873638 2109559 := bstep (se 1 (by rfl) ⟨1582169, by rfl⟩ : syracuseStep 2109559 = 3164339) B3164339
theorem B13512881 : Blo 1873638 13512881 := bstep (se 2 (by rfl) ⟨5067330, by rfl⟩ : syracuseStep 13512881 = 10134661) B10134661
theorem B3379403 : Blo 1873638 3379403 := bstep (se 1 (by rfl) ⟨2534552, by rfl⟩ : syracuseStep 3379403 = 5069105) B5069105
theorem B3559639 : Blo 1873638 3559639 := bstep (se 1 (by rfl) ⟨2669729, by rfl⟩ : syracuseStep 3559639 = 5339459) B5339459
theorem B4747481 : Blo 1873638 4747481 := bstep (se 2 (by rfl) ⟨1780305, by rfl⟩ : syracuseStep 4747481 = 3560611) B3560611
theorem B13512995 : Blo 1873638 13512995 := bstep (se 1 (by rfl) ⟨10134746, by rfl⟩ : syracuseStep 13512995 = 20269493) B20269493
theorem B2109739 : Blo 1873638 2109739 := bstep (se 1 (by rfl) ⟨1582304, by rfl⟩ : syracuseStep 2109739 = 3164609) B3164609
theorem B2109847 : Blo 1873638 2109847 := bstep (se 1 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 2109847 = 3164771) B3164771
theorem B3608983 : Blo 1873638 3608983 := bstep (se 1 (by rfl) ⟨2706737, by rfl⟩ : syracuseStep 3608983 = 5413475) B5413475
theorem B3559859 : Blo 1873638 3559859 := bstep (se 1 (by rfl) ⟨2669894, by rfl⟩ : syracuseStep 3559859 = 5339789) B5339789
theorem B6328907 : Blo 1873638 6328907 := bstep (se 1 (by rfl) ⟨4746680, by rfl⟩ : syracuseStep 6328907 = 9493361) B9493361
theorem B2110027 : Blo 1873638 2110027 := bstep (se 1 (by rfl) ⟨1582520, by rfl⟩ : syracuseStep 2110027 = 3165041) B3165041
theorem B3560087 : Blo 1873638 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B3379915 : Blo 1873638 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B6329177 : Blo 1873638 6329177 := bstep (se 2 (by rfl) ⟨2373441, by rfl⟩ : syracuseStep 6329177 = 4746883) B4746883
theorem B4002689 : Blo 1873638 4002689 := bstep (se 2 (by rfl) ⟨1501008, by rfl⟩ : syracuseStep 4002689 = 3002017) B3002017
theorem B3560345 : Blo 1873638 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B9491417 : Blo 1873638 9491417 := bstep (se 2 (by rfl) ⟨3559281, by rfl⟩ : syracuseStep 9491417 = 7118563) B7118563
theorem B4215833 : Blo 1873638 4215833 := bstep (se 2 (by rfl) ⟨1580937, by rfl⟩ : syracuseStep 4215833 = 3161875) B3161875
theorem B4060211 : Blo 1873638 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B4502603 : Blo 1873638 4502603 := bstep (se 1 (by rfl) ⟨3376952, by rfl⟩ : syracuseStep 4502603 = 6753905) B6753905
theorem B4215923 : Blo 1873638 4215923 := bstep (se 1 (by rfl) ⟨3161942, by rfl⟩ : syracuseStep 4215923 = 6323885) B6323885
theorem B7115921 : Blo 1873638 7115921 := bstep (se 2 (by rfl) ⟨2668470, by rfl⟩ : syracuseStep 7115921 = 5336941) B5336941
theorem B4215959 : Blo 1873638 4215959 := bstep (se 1 (by rfl) ⟨3161969, by rfl⟩ : syracuseStep 4215959 = 6323939) B6323939
theorem B7705817 : Blo 1873638 7705817 := bstep (se 2 (by rfl) ⟨2889681, by rfl⟩ : syracuseStep 7705817 = 5779363) B5779363
theorem B3560755 : Blo 1873638 3560755 := bstep (se 1 (by rfl) ⟨2670566, by rfl⟩ : syracuseStep 3560755 = 5341133) B5341133
theorem B4216139 : Blo 1873638 4216139 := bstep (se 1 (by rfl) ⟨3162104, by rfl⟩ : syracuseStep 4216139 = 6324209) B6324209
theorem B5338457 : Blo 1873638 5338457 := bstep (se 2 (by rfl) ⟨2001921, by rfl⟩ : syracuseStep 5338457 = 4003843) B4003843
theorem B24024437 : Blo 1873638 24024437 := bstep (se 5 (by rfl) ⟨1126145, by rfl⟩ : syracuseStep 24024437 = 2252291) B2252291
theorem B4216193 : Blo 1873638 4216193 := bstep (se 2 (by rfl) ⟨1581072, by rfl⟩ : syracuseStep 4216193 = 3162145) B3162145
theorem B2373067 : Blo 1873638 2373067 := bstep (se 1 (by rfl) ⟨1779800, by rfl⟩ : syracuseStep 2373067 = 3559601) B3559601
theorem B8009239 : Blo 1873638 8009239 := bstep (se 1 (by rfl) ⟨6006929, by rfl⟩ : syracuseStep 8009239 = 12013859) B12013859
theorem B6329879 : Blo 1873638 6329879 := bstep (se 1 (by rfl) ⟨4747409, by rfl⟩ : syracuseStep 6329879 = 9494819) B9494819
theorem B4216409 : Blo 1873638 4216409 := bstep (se 2 (by rfl) ⟨1581153, by rfl⟩ : syracuseStep 4216409 = 3162307) B3162307
theorem B10131095 : Blo 1873638 10131095 := bstep (se 1 (by rfl) ⟨7598321, by rfl⟩ : syracuseStep 10131095 = 15196643) B15196643
theorem B4216499 : Blo 1873638 4216499 := bstep (se 1 (by rfl) ⟨3162374, by rfl⟩ : syracuseStep 4216499 = 6324749) B6324749
theorem B9008819 : Blo 1873638 9008819 := bstep (se 1 (by rfl) ⟨6756614, by rfl⟩ : syracuseStep 9008819 = 13513229) B13513229
theorem B4216535 : Blo 1873638 4216535 := bstep (se 1 (by rfl) ⟨3162401, by rfl⟩ : syracuseStep 4216535 = 6324803) B6324803
theorem B4003543 : Blo 1873638 4003543 := bstep (se 1 (by rfl) ⟨3002657, by rfl⟩ : syracuseStep 4003543 = 6005315) B6005315
theorem B1873643 : Blo 1873638 1873643 := bstep (se 1 (by rfl) ⟨1405232, by rfl⟩ : syracuseStep 1873643 = 2810465) B2810465
theorem B1873655 : Blo 1873638 1873655 := bstep (se 1 (by rfl) ⟨1405241, by rfl⟩ : syracuseStep 1873655 = 2810483) B2810483
theorem B1873675 : Blo 1873638 1873675 := bstep (se 1 (by rfl) ⟨1405256, by rfl⟩ : syracuseStep 1873675 = 2810513) B2810513
theorem B1873687 : Blo 1873638 1873687 := bstep (se 1 (by rfl) ⟨1405265, by rfl⟩ : syracuseStep 1873687 = 2810531) B2810531
theorem B1873707 : Blo 1873638 1873707 := bstep (se 1 (by rfl) ⟨1405280, by rfl⟩ : syracuseStep 1873707 = 2810561) B2810561
theorem B1873719 : Blo 1873638 1873719 := bstep (se 1 (by rfl) ⟨1405289, by rfl⟩ : syracuseStep 1873719 = 2810579) B2810579
theorem B1873739 : Blo 1873638 1873739 := bstep (se 1 (by rfl) ⟨1405304, by rfl⟩ : syracuseStep 1873739 = 2810609) B2810609
theorem B7116619 : Blo 1873638 7116619 := bstep (se 1 (by rfl) ⟨5337464, by rfl⟩ : syracuseStep 7116619 = 10674929) B10674929
theorem B1873751 : Blo 1873638 1873751 := bstep (se 1 (by rfl) ⟨1405313, by rfl⟩ : syracuseStep 1873751 = 2810627) B2810627
theorem B1873771 : Blo 1873638 1873771 := bstep (se 1 (by rfl) ⟨1405328, by rfl⟩ : syracuseStep 1873771 = 2810657) B2810657
theorem B1873783 : Blo 1873638 1873783 := bstep (se 1 (by rfl) ⟨1405337, by rfl⟩ : syracuseStep 1873783 = 2810675) B2810675
theorem B1873803 : Blo 1873638 1873803 := bstep (se 1 (by rfl) ⟨1405352, by rfl⟩ : syracuseStep 1873803 = 2810705) B2810705
theorem B4216715 : Blo 1873638 4216715 := bstep (se 1 (by rfl) ⟨3162536, by rfl⟩ : syracuseStep 4216715 = 6325073) B6325073
theorem B1873815 : Blo 1873638 1873815 := bstep (se 1 (by rfl) ⟨1405361, by rfl⟩ : syracuseStep 1873815 = 2810723) B2810723
theorem B1873835 : Blo 1873638 1873835 := bstep (se 1 (by rfl) ⟨1405376, by rfl⟩ : syracuseStep 1873835 = 2810753) B2810753
theorem B1873847 : Blo 1873638 1873847 := bstep (se 1 (by rfl) ⟨1405385, by rfl⟩ : syracuseStep 1873847 = 2810771) B2810771
theorem B4216769 : Blo 1873638 4216769 := bstep (se 2 (by rfl) ⟨1581288, by rfl⟩ : syracuseStep 4216769 = 3162577) B3162577
theorem B1873867 : Blo 1873638 1873867 := bstep (se 1 (by rfl) ⟨1405400, by rfl⟩ : syracuseStep 1873867 = 2810801) B2810801
theorem B1873879 : Blo 1873638 1873879 := bstep (se 1 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 1873879 = 2810819) B2810819
theorem B1873899 : Blo 1873638 1873899 := bstep (se 1 (by rfl) ⟨1405424, by rfl⟩ : syracuseStep 1873899 = 2810849) B2810849
theorem B1873911 : Blo 1873638 1873911 := bstep (se 1 (by rfl) ⟨1405433, by rfl⟩ : syracuseStep 1873911 = 2810867) B2810867
theorem B1873931 : Blo 1873638 1873931 := bstep (se 1 (by rfl) ⟨1405448, by rfl⟩ : syracuseStep 1873931 = 2810897) B2810897
theorem B1873943 : Blo 1873638 1873943 := bstep (se 1 (by rfl) ⟨1405457, by rfl⟩ : syracuseStep 1873943 = 2810915) B2810915
theorem B1873963 : Blo 1873638 1873963 := bstep (se 1 (by rfl) ⟨1405472, by rfl⟩ : syracuseStep 1873963 = 2810945) B2810945
theorem B1873975 : Blo 1873638 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B1873995 : Blo 1873638 1873995 := bstep (se 1 (by rfl) ⟨1405496, by rfl⟩ : syracuseStep 1873995 = 2810993) B2810993
theorem B1874007 : Blo 1873638 1874007 := bstep (se 1 (by rfl) ⟨1405505, by rfl⟩ : syracuseStep 1874007 = 2811011) B2811011
theorem B5068889 : Blo 1873638 5068889 := bstep (se 2 (by rfl) ⟨1900833, by rfl⟩ : syracuseStep 5068889 = 3801667) B3801667
theorem B18012253 : Blo 1873638 18012253 := bstep (se 3 (by rfl) ⟨3377297, by rfl⟩ : syracuseStep 18012253 = 6754595) B6754595
theorem B7116893 : Blo 1873638 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B1874027 : Blo 1873638 1874027 := bstep (se 1 (by rfl) ⟨1405520, by rfl⟩ : syracuseStep 1874027 = 2811041) B2811041
theorem B1874039 : Blo 1873638 1874039 := bstep (se 1 (by rfl) ⟨1405529, by rfl⟩ : syracuseStep 1874039 = 2811059) B2811059
theorem B1874059 : Blo 1873638 1874059 := bstep (se 1 (by rfl) ⟨1405544, by rfl⟩ : syracuseStep 1874059 = 2811089) B2811089
theorem B8009873 : Blo 1873638 8009873 := bstep (se 2 (by rfl) ⟨3003702, by rfl⟩ : syracuseStep 8009873 = 6007405) B6007405
theorem B1874071 : Blo 1873638 1874071 := bstep (se 1 (by rfl) ⟨1405553, by rfl⟩ : syracuseStep 1874071 = 2811107) B2811107
theorem B5339287 : Blo 1873638 5339287 := bstep (se 1 (by rfl) ⟨4004465, by rfl⟩ : syracuseStep 5339287 = 8008931) B8008931
theorem B4216985 : Blo 1873638 4216985 := bstep (se 2 (by rfl) ⟨1581369, by rfl⟩ : syracuseStep 4216985 = 3162739) B3162739
theorem B1874091 : Blo 1873638 1874091 := bstep (se 1 (by rfl) ⟨1405568, by rfl⟩ : syracuseStep 1874091 = 2811137) B2811137
theorem B7706803 : Blo 1873638 7706803 := bstep (se 1 (by rfl) ⟨5780102, by rfl⟩ : syracuseStep 7706803 = 11560205) B11560205
theorem B1874103 : Blo 1873638 1874103 := bstep (se 1 (by rfl) ⟨1405577, by rfl⟩ : syracuseStep 1874103 = 2811155) B2811155
theorem B1874123 : Blo 1873638 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B1874135 : Blo 1873638 1874135 := bstep (se 1 (by rfl) ⟨1405601, by rfl⟩ : syracuseStep 1874135 = 2811203) B2811203
theorem B6002905 : Blo 1873638 6002905 := bstep (se 2 (by rfl) ⟨2251089, by rfl⟩ : syracuseStep 6002905 = 4502179) B4502179
theorem B1874155 : Blo 1873638 1874155 := bstep (se 1 (by rfl) ⟨1405616, by rfl⟩ : syracuseStep 1874155 = 2811233) B2811233
theorem B4217075 : Blo 1873638 4217075 := bstep (se 1 (by rfl) ⟨3162806, by rfl⟩ : syracuseStep 4217075 = 6325613) B6325613
theorem B1874167 : Blo 1873638 1874167 := bstep (se 1 (by rfl) ⟨1405625, by rfl⟩ : syracuseStep 1874167 = 2811251) B2811251
theorem B1874187 : Blo 1873638 1874187 := bstep (se 1 (by rfl) ⟨1405640, by rfl⟩ : syracuseStep 1874187 = 2811281) B2811281
theorem B1874199 : Blo 1873638 1874199 := bstep (se 1 (by rfl) ⟨1405649, by rfl⟩ : syracuseStep 1874199 = 2811299) B2811299
theorem B4217111 : Blo 1873638 4217111 := bstep (se 1 (by rfl) ⟨3162833, by rfl⟩ : syracuseStep 4217111 = 6325667) B6325667
theorem B1874219 : Blo 1873638 1874219 := bstep (se 1 (by rfl) ⟨1405664, by rfl⟩ : syracuseStep 1874219 = 2811329) B2811329
theorem B1874231 : Blo 1873638 1874231 := bstep (se 1 (by rfl) ⟨1405673, by rfl⟩ : syracuseStep 1874231 = 2811347) B2811347
theorem B1874251 : Blo 1873638 1874251 := bstep (se 1 (by rfl) ⟨1405688, by rfl⟩ : syracuseStep 1874251 = 2811377) B2811377
theorem B1874263 : Blo 1873638 1874263 := bstep (se 1 (by rfl) ⟨1405697, by rfl⟩ : syracuseStep 1874263 = 2811395) B2811395
theorem B1874283 : Blo 1873638 1874283 := bstep (se 1 (by rfl) ⟨1405712, by rfl⟩ : syracuseStep 1874283 = 2811425) B2811425
theorem B1874295 : Blo 1873638 1874295 := bstep (se 1 (by rfl) ⟨1405721, by rfl⟩ : syracuseStep 1874295 = 2811443) B2811443
theorem B1874315 : Blo 1873638 1874315 := bstep (se 1 (by rfl) ⟨1405736, by rfl⟩ : syracuseStep 1874315 = 2811473) B2811473
theorem B1874327 : Blo 1873638 1874327 := bstep (se 1 (by rfl) ⟨1405745, by rfl⟩ : syracuseStep 1874327 = 2811491) B2811491
theorem B1874347 : Blo 1873638 1874347 := bstep (se 1 (by rfl) ⟨1405760, by rfl⟩ : syracuseStep 1874347 = 2811521) B2811521
theorem B1874359 : Blo 1873638 1874359 := bstep (se 1 (by rfl) ⟨1405769, by rfl⟩ : syracuseStep 1874359 = 2811539) B2811539
theorem B4217291 : Blo 1873638 4217291 := bstep (se 1 (by rfl) ⟨3162968, by rfl⟩ : syracuseStep 4217291 = 6325937) B6325937
theorem B1874379 : Blo 1873638 1874379 := bstep (se 1 (by rfl) ⟨1405784, by rfl⟩ : syracuseStep 1874379 = 2811569) B2811569
theorem B7215563 : Blo 1873638 7215563 := bstep (se 1 (by rfl) ⟨5411672, by rfl⟩ : syracuseStep 7215563 = 10823345) B10823345
theorem B1874391 : Blo 1873638 1874391 := bstep (se 1 (by rfl) ⟨1405793, by rfl⟩ : syracuseStep 1874391 = 2811587) B2811587
theorem B1874411 : Blo 1873638 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B1874423 : Blo 1873638 1874423 := bstep (se 1 (by rfl) ⟨1405817, by rfl⟩ : syracuseStep 1874423 = 2811635) B2811635
theorem B4217345 : Blo 1873638 4217345 := bstep (se 2 (by rfl) ⟨1581504, by rfl⟩ : syracuseStep 4217345 = 3163009) B3163009
theorem B1874443 : Blo 1873638 1874443 := bstep (se 1 (by rfl) ⟨1405832, by rfl⟩ : syracuseStep 1874443 = 2811665) B2811665
theorem B4004363 : Blo 1873638 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B7600657 : Blo 1873638 7600657 := bstep (se 2 (by rfl) ⟨2850246, by rfl⟩ : syracuseStep 7600657 = 5700493) B5700493
theorem B5134871 : Blo 1873638 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B1874455 : Blo 1873638 1874455 := bstep (se 1 (by rfl) ⟨1405841, by rfl⟩ : syracuseStep 1874455 = 2811683) B2811683
theorem B1874475 : Blo 1873638 1874475 := bstep (se 1 (by rfl) ⟨1405856, by rfl⟩ : syracuseStep 1874475 = 2811713) B2811713
theorem B9493037 : Blo 1873638 9493037 := bstep (se 3 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 9493037 = 3559889) B3559889
theorem B1874487 : Blo 1873638 1874487 := bstep (se 1 (by rfl) ⟨1405865, by rfl⟩ : syracuseStep 1874487 = 2811731) B2811731
theorem B1874507 : Blo 1873638 1874507 := bstep (se 1 (by rfl) ⟨1405880, by rfl⟩ : syracuseStep 1874507 = 2811761) B2811761
theorem B1874519 : Blo 1873638 1874519 := bstep (se 1 (by rfl) ⟨1405889, by rfl⟩ : syracuseStep 1874519 = 2811779) B2811779
theorem B1874539 : Blo 1873638 1874539 := bstep (se 1 (by rfl) ⟨1405904, by rfl⟩ : syracuseStep 1874539 = 2811809) B2811809
theorem B1874551 : Blo 1873638 1874551 := bstep (se 1 (by rfl) ⟨1405913, by rfl⟩ : syracuseStep 1874551 = 2811827) B2811827
theorem B1874571 : Blo 1873638 1874571 := bstep (se 1 (by rfl) ⟨1405928, by rfl⟩ : syracuseStep 1874571 = 2811857) B2811857
theorem B1874583 : Blo 1873638 1874583 := bstep (se 1 (by rfl) ⟨1405937, by rfl⟩ : syracuseStep 1874583 = 2811875) B2811875
theorem B1874603 : Blo 1873638 1874603 := bstep (se 1 (by rfl) ⟨1405952, by rfl⟩ : syracuseStep 1874603 = 2811905) B2811905
theorem B16226993 : Blo 1873638 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B4274867 : Blo 1873638 4274867 := bstep (se 1 (by rfl) ⟨3206150, by rfl⟩ : syracuseStep 4274867 = 6412301) B6412301
theorem B3906227 : Blo 1873638 3906227 := bstep (se 1 (by rfl) ⟨2929670, by rfl⟩ : syracuseStep 3906227 = 5859341) B5859341
theorem B1874615 : Blo 1873638 1874615 := bstep (se 1 (by rfl) ⟨1405961, by rfl⟩ : syracuseStep 1874615 = 2811923) B2811923
theorem B1874635 : Blo 1873638 1874635 := bstep (se 1 (by rfl) ⟨1405976, by rfl⟩ : syracuseStep 1874635 = 2811953) B2811953
theorem B1874647 : Blo 1873638 1874647 := bstep (se 1 (by rfl) ⟨1405985, by rfl⟩ : syracuseStep 1874647 = 2811971) B2811971
theorem B4217561 : Blo 1873638 4217561 := bstep (se 2 (by rfl) ⟨1581585, by rfl⟩ : syracuseStep 4217561 = 3163171) B3163171
theorem B1874667 : Blo 1873638 1874667 := bstep (se 1 (by rfl) ⟨1406000, by rfl⟩ : syracuseStep 1874667 = 2812001) B2812001
theorem B2136823 : Blo 1873638 2136823 := bstep (se 1 (by rfl) ⟨1602617, by rfl⟩ : syracuseStep 2136823 = 3205235) B3205235
theorem B1874679 : Blo 1873638 1874679 := bstep (se 1 (by rfl) ⟨1406009, by rfl⟩ : syracuseStep 1874679 = 2812019) B2812019
theorem B1874699 : Blo 1873638 1874699 := bstep (se 1 (by rfl) ⟨1406024, by rfl⟩ : syracuseStep 1874699 = 2812049) B2812049
theorem B7117591 : Blo 1873638 7117591 := bstep (se 1 (by rfl) ⟨5338193, by rfl⟩ : syracuseStep 7117591 = 10676387) B10676387
theorem B1874711 : Blo 1873638 1874711 := bstep (se 1 (by rfl) ⟨1406033, by rfl⟩ : syracuseStep 1874711 = 2812067) B2812067
theorem B1874731 : Blo 1873638 1874731 := bstep (se 1 (by rfl) ⟨1406048, by rfl⟩ : syracuseStep 1874731 = 2812097) B2812097
theorem B4217651 : Blo 1873638 4217651 := bstep (se 1 (by rfl) ⟨3163238, by rfl⟩ : syracuseStep 4217651 = 6326477) B6326477
theorem B1874743 : Blo 1873638 1874743 := bstep (se 1 (by rfl) ⟨1406057, by rfl⟩ : syracuseStep 1874743 = 2812115) B2812115
theorem B6003521 : Blo 1873638 6003521 := bstep (se 2 (by rfl) ⟨2251320, by rfl⟩ : syracuseStep 6003521 = 4502641) B4502641
theorem B1874763 : Blo 1873638 1874763 := bstep (se 1 (by rfl) ⟨1406072, by rfl⟩ : syracuseStep 1874763 = 2812145) B2812145
theorem B8010571 : Blo 1873638 8010571 := bstep (se 1 (by rfl) ⟨6007928, by rfl⟩ : syracuseStep 8010571 = 12015857) B12015857
theorem B4217687 : Blo 1873638 4217687 := bstep (se 1 (by rfl) ⟨3163265, by rfl⟩ : syracuseStep 4217687 = 6326531) B6326531
theorem B1874775 : Blo 1873638 1874775 := bstep (se 1 (by rfl) ⟨1406081, by rfl⟩ : syracuseStep 1874775 = 2812163) B2812163
theorem B1874795 : Blo 1873638 1874795 := bstep (se 1 (by rfl) ⟨1406096, by rfl⟩ : syracuseStep 1874795 = 2812193) B2812193
theorem B1874807 : Blo 1873638 1874807 := bstep (se 1 (by rfl) ⟨1406105, by rfl⟩ : syracuseStep 1874807 = 2812211) B2812211
theorem B1874827 : Blo 1873638 1874827 := bstep (se 1 (by rfl) ⟨1406120, by rfl⟩ : syracuseStep 1874827 = 2812241) B2812241
theorem B1874839 : Blo 1873638 1874839 := bstep (se 1 (by rfl) ⟨1406129, by rfl⟩ : syracuseStep 1874839 = 2812259) B2812259
theorem B1874859 : Blo 1873638 1874859 := bstep (se 1 (by rfl) ⟨1406144, by rfl⟩ : syracuseStep 1874859 = 2812289) B2812289
theorem B1874871 : Blo 1873638 1874871 := bstep (se 1 (by rfl) ⟨1406153, by rfl⟩ : syracuseStep 1874871 = 2812307) B2812307
theorem B6003649 : Blo 1873638 6003649 := bstep (se 2 (by rfl) ⟨2251368, by rfl⟩ : syracuseStep 6003649 = 4502737) B4502737
theorem B3800011 : Blo 1873638 3800011 := bstep (se 1 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 3800011 = 5700017) B5700017
theorem B1874891 : Blo 1873638 1874891 := bstep (se 1 (by rfl) ⟨1406168, by rfl⟩ : syracuseStep 1874891 = 2812337) B2812337
theorem B5340107 : Blo 1873638 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B1874903 : Blo 1873638 1874903 := bstep (se 1 (by rfl) ⟨1406177, by rfl⟩ : syracuseStep 1874903 = 2812355) B2812355
theorem B1874923 : Blo 1873638 1874923 := bstep (se 1 (by rfl) ⟨1406192, by rfl⟩ : syracuseStep 1874923 = 2812385) B2812385
theorem B1874935 : Blo 1873638 1874935 := bstep (se 1 (by rfl) ⟨1406201, by rfl⟩ : syracuseStep 1874935 = 2812403) B2812403
theorem B4217867 : Blo 1873638 4217867 := bstep (se 1 (by rfl) ⟨3163400, by rfl⟩ : syracuseStep 4217867 = 6326801) B6326801
theorem B1874955 : Blo 1873638 1874955 := bstep (se 1 (by rfl) ⟨1406216, by rfl⟩ : syracuseStep 1874955 = 2812433) B2812433
theorem B108059669 : Blo 1873638 108059669 := bstep (se 6 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 108059669 = 5065297) B5065297
theorem B1874967 : Blo 1873638 1874967 := bstep (se 1 (by rfl) ⟨1406225, by rfl⟩ : syracuseStep 1874967 = 2812451) B2812451
theorem B2669593 : Blo 1873638 2669593 := bstep (se 2 (by rfl) ⟨1001097, by rfl⟩ : syracuseStep 2669593 = 2002195) B2002195
theorem B1874987 : Blo 1873638 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B1874999 : Blo 1873638 1874999 := bstep (se 1 (by rfl) ⟨1406249, by rfl⟩ : syracuseStep 1874999 = 2812499) B2812499
theorem B4217921 : Blo 1873638 4217921 := bstep (se 2 (by rfl) ⟨1581720, by rfl⟩ : syracuseStep 4217921 = 3163441) B3163441
theorem B1875019 : Blo 1873638 1875019 := bstep (se 1 (by rfl) ⟨1406264, by rfl⟩ : syracuseStep 1875019 = 2812529) B2812529
theorem B1875031 : Blo 1873638 1875031 := bstep (se 1 (by rfl) ⟨1406273, by rfl⟩ : syracuseStep 1875031 = 2812547) B2812547
theorem B8010845 : Blo 1873638 8010845 := bstep (se 3 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 8010845 = 3004067) B3004067
theorem B1875051 : Blo 1873638 1875051 := bstep (se 1 (by rfl) ⟨1406288, by rfl⟩ : syracuseStep 1875051 = 2812577) B2812577
theorem B1875063 : Blo 1873638 1875063 := bstep (se 1 (by rfl) ⟨1406297, by rfl⟩ : syracuseStep 1875063 = 2812595) B2812595
theorem B1875083 : Blo 1873638 1875083 := bstep (se 1 (by rfl) ⟨1406312, by rfl⟩ : syracuseStep 1875083 = 2812625) B2812625
theorem B1875095 : Blo 1873638 1875095 := bstep (se 1 (by rfl) ⟨1406321, by rfl⟩ : syracuseStep 1875095 = 2812643) B2812643
theorem B1875115 : Blo 1873638 1875115 := bstep (se 1 (by rfl) ⟨1406336, by rfl⟩ : syracuseStep 1875115 = 2812673) B2812673
theorem B1875127 : Blo 1873638 1875127 := bstep (se 1 (by rfl) ⟨1406345, by rfl⟩ : syracuseStep 1875127 = 2812691) B2812691
theorem B1875147 : Blo 1873638 1875147 := bstep (se 1 (by rfl) ⟨1406360, by rfl⟩ : syracuseStep 1875147 = 2812721) B2812721
theorem B1875159 : Blo 1873638 1875159 := bstep (se 1 (by rfl) ⟨1406369, by rfl⟩ : syracuseStep 1875159 = 2812739) B2812739
theorem B4504793 : Blo 1873638 4504793 := bstep (se 2 (by rfl) ⟨1689297, by rfl⟩ : syracuseStep 4504793 = 3378595) B3378595
theorem B6167773 : Blo 1873638 6167773 := bstep (se 3 (by rfl) ⟨1156457, by rfl⟩ : syracuseStep 6167773 = 2312915) B2312915
theorem B1875179 : Blo 1873638 1875179 := bstep (se 1 (by rfl) ⟨1406384, by rfl⟩ : syracuseStep 1875179 = 2812769) B2812769
theorem B1875191 : Blo 1873638 1875191 := bstep (se 1 (by rfl) ⟨1406393, by rfl⟩ : syracuseStep 1875191 = 2812787) B2812787
theorem B1875211 : Blo 1873638 1875211 := bstep (se 1 (by rfl) ⟨1406408, by rfl⟩ : syracuseStep 1875211 = 2812817) B2812817
theorem B9485585 : Blo 1873638 9485585 := bstep (se 2 (by rfl) ⟨3557094, by rfl⟩ : syracuseStep 9485585 = 7114189) B7114189
theorem B1875223 : Blo 1873638 1875223 := bstep (se 1 (by rfl) ⟨1406417, by rfl⟩ : syracuseStep 1875223 = 2812835) B2812835
theorem B4218137 : Blo 1873638 4218137 := bstep (se 2 (by rfl) ⟨1581801, by rfl⟩ : syracuseStep 4218137 = 3163603) B3163603
theorem B1875243 : Blo 1873638 1875243 := bstep (se 1 (by rfl) ⟨1406432, by rfl⟩ : syracuseStep 1875243 = 2812865) B2812865
theorem B1875255 : Blo 1873638 1875255 := bstep (se 1 (by rfl) ⟨1406441, by rfl⟩ : syracuseStep 1875255 = 2812883) B2812883
theorem B1875275 : Blo 1873638 1875275 := bstep (se 1 (by rfl) ⟨1406456, by rfl⟩ : syracuseStep 1875275 = 2812913) B2812913
theorem B1875287 : Blo 1873638 1875287 := bstep (se 1 (by rfl) ⟨1406465, by rfl⟩ : syracuseStep 1875287 = 2812931) B2812931
theorem B1875307 : Blo 1873638 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B4218227 : Blo 1873638 4218227 := bstep (se 1 (by rfl) ⟨3163670, by rfl⟩ : syracuseStep 4218227 = 6327341) B6327341
theorem B1875319 : Blo 1873638 1875319 := bstep (se 1 (by rfl) ⟨1406489, by rfl⟩ : syracuseStep 1875319 = 2812979) B2812979
theorem B1875339 : Blo 1873638 1875339 := bstep (se 1 (by rfl) ⟨1406504, by rfl⟩ : syracuseStep 1875339 = 2813009) B2813009
theorem B4218263 : Blo 1873638 4218263 := bstep (se 1 (by rfl) ⟨3163697, by rfl⟩ : syracuseStep 4218263 = 6327395) B6327395
theorem B1875351 : Blo 1873638 1875351 := bstep (se 1 (by rfl) ⟨1406513, by rfl⟩ : syracuseStep 1875351 = 2813027) B2813027
theorem B1875371 : Blo 1873638 1875371 := bstep (se 1 (by rfl) ⟨1406528, by rfl⟩ : syracuseStep 1875371 = 2813057) B2813057
theorem B9485747 : Blo 1873638 9485747 := bstep (se 1 (by rfl) ⟨7114310, by rfl⟩ : syracuseStep 9485747 = 14228621) B14228621
theorem B8011187 : Blo 1873638 8011187 := bstep (se 1 (by rfl) ⟨6008390, by rfl⟩ : syracuseStep 8011187 = 12016781) B12016781
theorem B1875383 : Blo 1873638 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B6757825 : Blo 1873638 6757825 := bstep (se 2 (by rfl) ⟨2534184, by rfl⟩ : syracuseStep 6757825 = 5068369) B5068369
theorem B1875403 : Blo 1873638 1875403 := bstep (se 1 (by rfl) ⟨1406552, by rfl⟩ : syracuseStep 1875403 = 2813105) B2813105
theorem B1875415 : Blo 1873638 1875415 := bstep (se 1 (by rfl) ⟨1406561, by rfl⟩ : syracuseStep 1875415 = 2813123) B2813123
theorem B2850265 : Blo 1873638 2850265 := bstep (se 2 (by rfl) ⟨1068849, by rfl⟩ : syracuseStep 2850265 = 2137699) B2137699
theorem B1875435 : Blo 1873638 1875435 := bstep (se 1 (by rfl) ⟨1406576, by rfl⟩ : syracuseStep 1875435 = 2813153) B2813153
theorem B1875447 : Blo 1873638 1875447 := bstep (se 1 (by rfl) ⟨1406585, by rfl⟩ : syracuseStep 1875447 = 2813171) B2813171
theorem B1875467 : Blo 1873638 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B1900055 : Blo 1873638 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B1875479 : Blo 1873638 1875479 := bstep (se 1 (by rfl) ⟨1406609, by rfl⟩ : syracuseStep 1875479 = 2813219) B2813219
theorem B1875499 : Blo 1873638 1875499 := bstep (se 1 (by rfl) ⟨1406624, by rfl⟩ : syracuseStep 1875499 = 2813249) B2813249
theorem B7118381 : Blo 1873638 7118381 := bstep (se 3 (by rfl) ⟨1334696, by rfl⟩ : syracuseStep 7118381 = 2669393) B2669393
theorem B10681901 : Blo 1873638 10681901 := bstep (se 3 (by rfl) ⟨2002856, by rfl⟩ : syracuseStep 10681901 = 4005713) B4005713
theorem B1875511 : Blo 1873638 1875511 := bstep (se 1 (by rfl) ⟨1406633, by rfl⟩ : syracuseStep 1875511 = 2813267) B2813267
theorem B6323777 : Blo 1873638 6323777 := bstep (se 2 (by rfl) ⟨2371416, by rfl⟩ : syracuseStep 6323777 = 4742833) B4742833
theorem B4218443 : Blo 1873638 4218443 := bstep (se 1 (by rfl) ⟨3163832, by rfl⟩ : syracuseStep 4218443 = 6327665) B6327665
theorem B1875531 : Blo 1873638 1875531 := bstep (se 1 (by rfl) ⟨1406648, by rfl⟩ : syracuseStep 1875531 = 2813297) B2813297
theorem B1875543 : Blo 1873638 1875543 := bstep (se 1 (by rfl) ⟨1406657, by rfl⟩ : syracuseStep 1875543 = 2813315) B2813315
theorem B1875563 : Blo 1873638 1875563 := bstep (se 1 (by rfl) ⟨1406672, by rfl⟩ : syracuseStep 1875563 = 2813345) B2813345
theorem B1875575 : Blo 1873638 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B4218497 : Blo 1873638 4218497 := bstep (se 2 (by rfl) ⟨1581936, by rfl⟩ : syracuseStep 4218497 = 3163873) B3163873
theorem B1875595 : Blo 1873638 1875595 := bstep (se 1 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 1875595 = 2813393) B2813393
theorem B1875607 : Blo 1873638 1875607 := bstep (se 1 (by rfl) ⟨1406705, by rfl⟩ : syracuseStep 1875607 = 2813411) B2813411
theorem B1875627 : Blo 1873638 1875627 := bstep (se 1 (by rfl) ⟨1406720, by rfl⟩ : syracuseStep 1875627 = 2813441) B2813441
theorem B7601971 : Blo 1873638 7601971 := bstep (se 1 (by rfl) ⟨5701478, by rfl⟩ : syracuseStep 7601971 = 11402957) B11402957
theorem B4218713 : Blo 1873638 4218713 := bstep (se 2 (by rfl) ⟨1582017, by rfl⟩ : syracuseStep 4218713 = 3164035) B3164035
theorem B4218803 : Blo 1873638 4218803 := bstep (se 1 (by rfl) ⟨3164102, by rfl⟩ : syracuseStep 4218803 = 6328205) B6328205
theorem B3162071 : Blo 1873638 3162071 := bstep (se 1 (by rfl) ⟨2371553, by rfl⟩ : syracuseStep 3162071 = 4743107) B4743107
theorem B4218839 : Blo 1873638 4218839 := bstep (se 1 (by rfl) ⟨3164129, by rfl⟩ : syracuseStep 4218839 = 6328259) B6328259
theorem B10674179 : Blo 1873638 10674179 := bstep (se 1 (by rfl) ⟨8005634, by rfl⟩ : syracuseStep 10674179 = 16011269) B16011269
theorem B2252815 : Blo 1873638 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B5701661 : Blo 1873638 5701661 := bstep (se 3 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 5701661 = 2138123) B2138123
theorem B2252935 : Blo 1873638 2252935 := bstep (se 1 (by rfl) ⟨1689701, by rfl⟩ : syracuseStep 2252935 = 3379403) B3379403
theorem B1900687 : Blo 1873638 1900687 := bstep (se 1 (by rfl) ⟨1425515, by rfl⟩ : syracuseStep 1900687 = 2851031) B2851031
theorem B6324425 : Blo 1873638 6324425 := bstep (se 2 (by rfl) ⟨2371659, by rfl⟩ : syracuseStep 6324425 = 4743319) B4743319
theorem B7119049 : Blo 1873638 7119049 := bstep (se 2 (by rfl) ⟨2669643, by rfl⟩ : syracuseStep 7119049 = 5339287) B5339287
theorem B34193677 : Blo 1873638 34193677 := bstep (se 3 (by rfl) ⟨6411314, by rfl⟩ : syracuseStep 34193677 = 12822629) B12822629
theorem B8003873 : Blo 1873638 8003873 := bstep (se 2 (by rfl) ⟨3001452, by rfl⟩ : syracuseStep 8003873 = 6002905) B6002905
theorem B3162503 : Blo 1873638 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B4219271 : Blo 1873638 4219271 := bstep (se 1 (by rfl) ⟨3164453, by rfl⟩ : syracuseStep 4219271 = 6328907) B6328907
theorem B7602617 : Blo 1873638 7602617 := bstep (se 2 (by rfl) ⟨2850981, by rfl⟩ : syracuseStep 7602617 = 5701963) B5701963
theorem B5702159 : Blo 1873638 5702159 := bstep (se 1 (by rfl) ⟨4276619, by rfl⟩ : syracuseStep 5702159 = 8553239) B8553239
theorem B4219451 : Blo 1873638 4219451 := bstep (se 1 (by rfl) ⟨3164588, by rfl⟩ : syracuseStep 4219451 = 6329177) B6329177
theorem B4219577 : Blo 1873638 4219577 := bstep (se 2 (by rfl) ⟨1582341, by rfl⟩ : syracuseStep 4219577 = 3164683) B3164683
theorem B2810555 : Blo 1873638 2810555 := bstep (se 1 (by rfl) ⟨2107916, by rfl⟩ : syracuseStep 2810555 = 4215833) B4215833
theorem B10134209 : Blo 1873638 10134209 := bstep (se 2 (by rfl) ⟨3800328, by rfl⟩ : syracuseStep 10134209 = 7600657) B7600657
theorem B2810615 : Blo 1873638 2810615 := bstep (se 1 (by rfl) ⟨2107961, by rfl⟩ : syracuseStep 2810615 = 4215923) B4215923
theorem B4743947 : Blo 1873638 4743947 := bstep (se 1 (by rfl) ⟨3557960, by rfl⟩ : syracuseStep 4743947 = 7115921) B7115921
theorem B2810639 : Blo 1873638 2810639 := bstep (se 1 (by rfl) ⟨2107979, by rfl⟩ : syracuseStep 2810639 = 4215959) B4215959
theorem B2810681 : Blo 1873638 2810681 := bstep (se 2 (by rfl) ⟨1054005, by rfl⟩ : syracuseStep 2810681 = 2108011) B2108011
theorem B5137211 : Blo 1873638 5137211 := bstep (se 1 (by rfl) ⟨3852908, by rfl⟩ : syracuseStep 5137211 = 7705817) B7705817
theorem B2810759 : Blo 1873638 2810759 := bstep (se 1 (by rfl) ⟨2108069, by rfl⟩ : syracuseStep 2810759 = 4216139) B4216139
theorem B6325127 : Blo 1873638 6325127 := bstep (se 1 (by rfl) ⟨4743845, by rfl⟩ : syracuseStep 6325127 = 9487691) B9487691
theorem B9135001 : Blo 1873638 9135001 := bstep (se 2 (by rfl) ⟨3425625, by rfl⟩ : syracuseStep 9135001 = 6851251) B6851251
theorem B16016291 : Blo 1873638 16016291 := bstep (se 1 (by rfl) ⟨12012218, by rfl⟩ : syracuseStep 16016291 = 24024437) B24024437
theorem B2810795 : Blo 1873638 2810795 := bstep (se 1 (by rfl) ⟨2108096, by rfl⟩ : syracuseStep 2810795 = 4216193) B4216193
theorem B4506553 : Blo 1873638 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B2810825 : Blo 1873638 2810825 := bstep (se 2 (by rfl) ⟨1054059, by rfl⟩ : syracuseStep 2810825 = 2108119) B2108119
theorem B3163151 : Blo 1873638 3163151 := bstep (se 1 (by rfl) ⟨2372363, by rfl⟩ : syracuseStep 3163151 = 4744727) B4744727
theorem B4219919 : Blo 1873638 4219919 := bstep (se 1 (by rfl) ⟨3164939, by rfl⟩ : syracuseStep 4219919 = 6329879) B6329879
theorem B3802145 : Blo 1873638 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B4219937 : Blo 1873638 4219937 := bstep (se 2 (by rfl) ⟨1582476, by rfl⟩ : syracuseStep 4219937 = 3164953) B3164953
theorem B2810939 : Blo 1873638 2810939 := bstep (se 1 (by rfl) ⟨2108204, by rfl⟩ : syracuseStep 2810939 = 4216409) B4216409
theorem B21349493 : Blo 1873638 21349493 := bstep (se 5 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 21349493 = 2001515) B2001515
theorem B2810999 : Blo 1873638 2810999 := bstep (se 1 (by rfl) ⟨2108249, by rfl⟩ : syracuseStep 2810999 = 4216499) B4216499
theorem B6005879 : Blo 1873638 6005879 := bstep (se 1 (by rfl) ⟨4504409, by rfl⟩ : syracuseStep 6005879 = 9008819) B9008819
theorem B2811023 : Blo 1873638 2811023 := bstep (se 1 (by rfl) ⟨2108267, by rfl⟩ : syracuseStep 2811023 = 4216535) B4216535
theorem B2811065 : Blo 1873638 2811065 := bstep (se 2 (by rfl) ⟨1054149, by rfl⟩ : syracuseStep 2811065 = 2108299) B2108299
theorem B8004865 : Blo 1873638 8004865 := bstep (se 2 (by rfl) ⟨3001824, by rfl⟩ : syracuseStep 8004865 = 6003649) B6003649
theorem B6325505 : Blo 1873638 6325505 := bstep (se 2 (by rfl) ⟨2372064, by rfl⟩ : syracuseStep 6325505 = 4744129) B4744129
theorem B2811143 : Blo 1873638 2811143 := bstep (se 1 (by rfl) ⟨2108357, by rfl⟩ : syracuseStep 2811143 = 4216715) B4216715
theorem B11396389 : Blo 1873638 11396389 := bstep (se 4 (by rfl) ⟨1068411, by rfl⟩ : syracuseStep 11396389 = 2136823) B2136823
theorem B2811179 : Blo 1873638 2811179 := bstep (se 1 (by rfl) ⟨2108384, by rfl⟩ : syracuseStep 2811179 = 4216769) B4216769
theorem B2811209 : Blo 1873638 2811209 := bstep (se 2 (by rfl) ⟨1054203, by rfl⟩ : syracuseStep 2811209 = 2108407) B2108407
theorem B4744595 : Blo 1873638 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B2811323 : Blo 1873638 2811323 := bstep (se 1 (by rfl) ⟨2108492, by rfl⟩ : syracuseStep 2811323 = 4216985) B4216985
theorem B2811383 : Blo 1873638 2811383 := bstep (se 1 (by rfl) ⟨2108537, by rfl⟩ : syracuseStep 2811383 = 4217075) B4217075
theorem B2811407 : Blo 1873638 2811407 := bstep (se 1 (by rfl) ⟨2108555, by rfl⟩ : syracuseStep 2811407 = 4217111) B4217111
theorem B3163691 : Blo 1873638 3163691 := bstep (se 1 (by rfl) ⟨2372768, by rfl⟩ : syracuseStep 3163691 = 4745537) B4745537
theorem B2811449 : Blo 1873638 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B2811527 : Blo 1873638 2811527 := bstep (se 1 (by rfl) ⟨2108645, by rfl⟩ : syracuseStep 2811527 = 4217291) B4217291
theorem B4810375 : Blo 1873638 4810375 := bstep (se 1 (by rfl) ⟨3607781, by rfl⟩ : syracuseStep 4810375 = 7215563) B7215563
theorem B2811563 : Blo 1873638 2811563 := bstep (se 1 (by rfl) ⟨2108672, by rfl⟩ : syracuseStep 2811563 = 4217345) B4217345
theorem B4744889 : Blo 1873638 4744889 := bstep (se 2 (by rfl) ⟨1779333, by rfl⟩ : syracuseStep 4744889 = 3558667) B3558667
theorem B2811593 : Blo 1873638 2811593 := bstep (se 2 (by rfl) ⟨1054347, by rfl⟩ : syracuseStep 2811593 = 2108695) B2108695
theorem B2811707 : Blo 1873638 2811707 := bstep (se 1 (by rfl) ⟨2108780, by rfl⟩ : syracuseStep 2811707 = 4217561) B4217561
theorem B2811767 : Blo 1873638 2811767 := bstep (se 1 (by rfl) ⟨2108825, by rfl⟩ : syracuseStep 2811767 = 4217651) B4217651
theorem B2811791 : Blo 1873638 2811791 := bstep (se 1 (by rfl) ⟨2108843, by rfl⟩ : syracuseStep 2811791 = 4217687) B4217687
theorem B2811833 : Blo 1873638 2811833 := bstep (se 2 (by rfl) ⟨1054437, by rfl⟩ : syracuseStep 2811833 = 2108875) B2108875
theorem B3164089 : Blo 1873638 3164089 := bstep (se 2 (by rfl) ⟨1186533, by rfl⟩ : syracuseStep 3164089 = 2373067) B2373067
theorem B2811911 : Blo 1873638 2811911 := bstep (se 1 (by rfl) ⟨2108933, by rfl⟩ : syracuseStep 2811911 = 4217867) B4217867
theorem B6326315 : Blo 1873638 6326315 := bstep (se 1 (by rfl) ⟨4744736, by rfl⟩ : syracuseStep 6326315 = 9489473) B9489473
theorem B2811947 : Blo 1873638 2811947 := bstep (se 1 (by rfl) ⟨2108960, by rfl⟩ : syracuseStep 2811947 = 4217921) B4217921
theorem B2811977 : Blo 1873638 2811977 := bstep (se 2 (by rfl) ⟨1054491, by rfl⟩ : syracuseStep 2811977 = 2108983) B2108983
theorem B2812091 : Blo 1873638 2812091 := bstep (se 1 (by rfl) ⟨2109068, by rfl⟩ : syracuseStep 2812091 = 4218137) B4218137
theorem B8554697 : Blo 1873638 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B2812151 : Blo 1873638 2812151 := bstep (se 1 (by rfl) ⟨2109113, by rfl⟩ : syracuseStep 2812151 = 4218227) B4218227
theorem B2812175 : Blo 1873638 2812175 := bstep (se 1 (by rfl) ⟨2109131, by rfl⟩ : syracuseStep 2812175 = 4218263) B4218263
theorem B2812217 : Blo 1873638 2812217 := bstep (se 2 (by rfl) ⟨1054581, by rfl⟩ : syracuseStep 2812217 = 2109163) B2109163
theorem B10676569 : Blo 1873638 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B4745587 : Blo 1873638 4745587 := bstep (se 1 (by rfl) ⟨3559190, by rfl⟩ : syracuseStep 4745587 = 7118381) B7118381
theorem B7121267 : Blo 1873638 7121267 := bstep (se 1 (by rfl) ⟨5340950, by rfl⟩ : syracuseStep 7121267 = 10681901) B10681901
theorem B2812295 : Blo 1873638 2812295 := bstep (se 1 (by rfl) ⟨2109221, by rfl⟩ : syracuseStep 2812295 = 4218443) B4218443
theorem B10135961 : Blo 1873638 10135961 := bstep (se 2 (by rfl) ⟨3800985, by rfl⟩ : syracuseStep 10135961 = 7601971) B7601971
theorem B2812331 : Blo 1873638 2812331 := bstep (se 1 (by rfl) ⟨2109248, by rfl⟩ : syracuseStep 2812331 = 4218497) B4218497
theorem B9488825 : Blo 1873638 9488825 := bstep (se 2 (by rfl) ⟨3558309, by rfl⟩ : syracuseStep 9488825 = 7116619) B7116619
theorem B3377609 : Blo 1873638 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B2812361 : Blo 1873638 2812361 := bstep (se 2 (by rfl) ⟨1054635, by rfl⟩ : syracuseStep 2812361 = 2109271) B2109271
theorem B4745729 : Blo 1873638 4745729 := bstep (se 2 (by rfl) ⟨1779648, by rfl⟩ : syracuseStep 4745729 = 3559297) B3559297
theorem B7211531 : Blo 1873638 7211531 := bstep (se 1 (by rfl) ⟨5408648, by rfl⟩ : syracuseStep 7211531 = 10817297) B10817297
theorem B14240285 : Blo 1873638 14240285 := bstep (se 3 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 14240285 = 5340107) B5340107
theorem B2812475 : Blo 1873638 2812475 := bstep (se 1 (by rfl) ⟨2109356, by rfl⟩ : syracuseStep 2812475 = 4218713) B4218713
theorem B2812535 : Blo 1873638 2812535 := bstep (se 1 (by rfl) ⟨2109401, by rfl⟩ : syracuseStep 2812535 = 4218803) B4218803
theorem B3164791 : Blo 1873638 3164791 := bstep (se 1 (by rfl) ⟨2373593, by rfl⟩ : syracuseStep 3164791 = 4747187) B4747187
theorem B2108047 : Blo 1873638 2108047 := bstep (se 1 (by rfl) ⟨1581035, by rfl⟩ : syracuseStep 2108047 = 3162071) B3162071
theorem B2812559 : Blo 1873638 2812559 := bstep (se 1 (by rfl) ⟨2109419, by rfl⟩ : syracuseStep 2812559 = 4218839) B4218839
theorem B2812601 : Blo 1873638 2812601 := bstep (se 2 (by rfl) ⟨1054725, by rfl⟩ : syracuseStep 2812601 = 2109451) B2109451
theorem B2812679 : Blo 1873638 2812679 := bstep (se 1 (by rfl) ⟨2109509, by rfl⟩ : syracuseStep 2812679 = 4219019) B4219019
theorem B2812715 : Blo 1873638 2812715 := bstep (se 1 (by rfl) ⟨2109536, by rfl⟩ : syracuseStep 2812715 = 4219073) B4219073
theorem B3164987 : Blo 1873638 3164987 := bstep (se 1 (by rfl) ⟨2373740, by rfl⟩ : syracuseStep 3164987 = 4747481) B4747481
theorem B2812745 : Blo 1873638 2812745 := bstep (se 2 (by rfl) ⟨1054779, by rfl⟩ : syracuseStep 2812745 = 2109559) B2109559
theorem B18017099 : Blo 1873638 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B10275737 : Blo 1873638 10275737 := bstep (se 2 (by rfl) ⟨3853401, by rfl⟩ : syracuseStep 10275737 = 7706803) B7706803
theorem B2812859 : Blo 1873638 2812859 := bstep (se 1 (by rfl) ⟨2109644, by rfl⟩ : syracuseStep 2812859 = 4219289) B4219289
theorem B4746185 : Blo 1873638 4746185 := bstep (se 2 (by rfl) ⟨1779819, by rfl⟩ : syracuseStep 4746185 = 3559639) B3559639
theorem B2812919 : Blo 1873638 2812919 := bstep (se 1 (by rfl) ⟨2109689, by rfl⟩ : syracuseStep 2812919 = 4219379) B4219379
theorem B2812943 : Blo 1873638 2812943 := bstep (se 1 (by rfl) ⟨2109707, by rfl⟩ : syracuseStep 2812943 = 4219415) B4219415
theorem B2812985 : Blo 1873638 2812985 := bstep (se 2 (by rfl) ⟨1054869, by rfl⟩ : syracuseStep 2812985 = 2109739) B2109739
theorem B43273349 : Blo 1873638 43273349 := bstep (se 4 (by rfl) ⟨4056876, by rfl⟩ : syracuseStep 43273349 = 8113753) B8113753
theorem B17099909 : Blo 1873638 17099909 := bstep (se 4 (by rfl) ⟨1603116, by rfl⟩ : syracuseStep 17099909 = 3206233) B3206233
theorem B2108551 : Blo 1873638 2108551 := bstep (se 1 (by rfl) ⟨1581413, by rfl⟩ : syracuseStep 2108551 = 3162827) B3162827
theorem B2813063 : Blo 1873638 2813063 := bstep (se 1 (by rfl) ⟨2109797, by rfl⟩ : syracuseStep 2813063 = 4219595) B4219595
theorem B2813099 : Blo 1873638 2813099 := bstep (se 1 (by rfl) ⟨2109824, by rfl⟩ : syracuseStep 2813099 = 4219649) B4219649
theorem B2813129 : Blo 1873638 2813129 := bstep (se 2 (by rfl) ⟨1054923, by rfl⟩ : syracuseStep 2813129 = 2109847) B2109847
theorem B4811977 : Blo 1873638 4811977 := bstep (se 2 (by rfl) ⟨1804491, by rfl⟩ : syracuseStep 4811977 = 3608983) B3608983
theorem B12012781 : Blo 1873638 12012781 := bstep (se 3 (by rfl) ⟨2252396, by rfl⟩ : syracuseStep 12012781 = 4504793) B4504793
theorem B4746539 : Blo 1873638 4746539 := bstep (se 1 (by rfl) ⟨3559904, by rfl⟩ : syracuseStep 4746539 = 7119809) B7119809
theorem B2108731 : Blo 1873638 2108731 := bstep (se 1 (by rfl) ⟨1581548, by rfl⟩ : syracuseStep 2108731 = 3163097) B3163097
theorem B6327611 : Blo 1873638 6327611 := bstep (se 1 (by rfl) ⟨4745708, by rfl⟩ : syracuseStep 6327611 = 9491417) B9491417
theorem B2813243 : Blo 1873638 2813243 := bstep (se 1 (by rfl) ⟨2109932, by rfl⟩ : syracuseStep 2813243 = 4219865) B4219865
theorem B2813303 : Blo 1873638 2813303 := bstep (se 1 (by rfl) ⟨2109977, by rfl⟩ : syracuseStep 2813303 = 4219955) B4219955
theorem B3001735 : Blo 1873638 3001735 := bstep (se 1 (by rfl) ⟨2251301, by rfl⟩ : syracuseStep 3001735 = 4502603) B4502603
theorem B2813327 : Blo 1873638 2813327 := bstep (se 1 (by rfl) ⟨2109995, by rfl⟩ : syracuseStep 2813327 = 4219991) B4219991
theorem B2813369 : Blo 1873638 2813369 := bstep (se 2 (by rfl) ⟨1055013, by rfl⟩ : syracuseStep 2813369 = 2110027) B2110027
theorem B2813447 : Blo 1873638 2813447 := bstep (se 1 (by rfl) ⟨2110085, by rfl⟩ : syracuseStep 2813447 = 4220171) B4220171
theorem B15199787 : Blo 1873638 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B3558971 : Blo 1873638 3558971 := bstep (se 1 (by rfl) ⟨2669228, by rfl⟩ : syracuseStep 3558971 = 5338457) B5338457
theorem B40529483 : Blo 1873638 40529483 := bstep (se 1 (by rfl) ⟨30397112, by rfl⟩ : syracuseStep 40529483 = 60794225) B60794225
theorem B9490121 : Blo 1873638 9490121 := bstep (se 2 (by rfl) ⟨3558795, by rfl⟩ : syracuseStep 9490121 = 7117591) B7117591
theorem B2109199 : Blo 1873638 2109199 := bstep (se 1 (by rfl) ⟨1581899, by rfl⟩ : syracuseStep 2109199 = 3163799) B3163799
theorem B6328097 : Blo 1873638 6328097 := bstep (se 2 (by rfl) ⟨2373036, by rfl⟩ : syracuseStep 6328097 = 4746073) B4746073
theorem B2371447 : Blo 1873638 2371447 := bstep (se 1 (by rfl) ⟨1778585, by rfl⟩ : syracuseStep 2371447 = 3557171) B3557171
theorem B5066681 : Blo 1873638 5066681 := bstep (se 2 (by rfl) ⟨1900005, by rfl⟩ : syracuseStep 5066681 = 3800011) B3800011
theorem B10678301 : Blo 1873638 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B3559457 : Blo 1873638 3559457 := bstep (se 2 (by rfl) ⟨1334796, by rfl⟩ : syracuseStep 3559457 = 2669593) B2669593
theorem B3379259 : Blo 1873638 3379259 := bstep (se 1 (by rfl) ⟨2534444, by rfl⟩ : syracuseStep 3379259 = 5068889) B5068889
theorem B13692989 : Blo 1873638 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B5066813 : Blo 1873638 5066813 := bstep (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) B1900055
theorem B2887753 : Blo 1873638 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B2371771 : Blo 1873638 2371771 := bstep (se 1 (by rfl) ⟨1778828, by rfl⟩ : syracuseStep 2371771 = 3557657) B3557657
theorem B2109703 : Blo 1873638 2109703 := bstep (se 1 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 2109703 = 3164555) B3164555
theorem B4747531 : Blo 1873638 4747531 := bstep (se 1 (by rfl) ⟨3560648, by rfl⟩ : syracuseStep 4747531 = 7121297) B7121297
theorem B6328691 : Blo 1873638 6328691 := bstep (se 1 (by rfl) ⟨4746518, by rfl⟩ : syracuseStep 6328691 = 9493037) B9493037
theorem B7115161 : Blo 1873638 7115161 := bstep (se 2 (by rfl) ⟨2668185, by rfl⟩ : syracuseStep 7115161 = 5336371) B5336371
theorem B4747673 : Blo 1873638 4747673 := bstep (se 2 (by rfl) ⟨1780377, by rfl⟩ : syracuseStep 4747673 = 3560755) B3560755
theorem B2109883 : Blo 1873638 2109883 := bstep (se 1 (by rfl) ⟨1582412, by rfl⟩ : syracuseStep 2109883 = 3164825) B3164825
theorem B10817995 : Blo 1873638 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B4002347 : Blo 1873638 4002347 := bstep (se 1 (by rfl) ⟨3001760, by rfl⟩ : syracuseStep 4002347 = 6003521) B6003521
theorem B2372267 : Blo 1873638 2372267 := bstep (se 1 (by rfl) ⟨1779200, by rfl⟩ : syracuseStep 2372267 = 3558401) B3558401
theorem B7115465 : Blo 1873638 7115465 := bstep (se 2 (by rfl) ⟨2668299, by rfl⟩ : syracuseStep 7115465 = 5336599) B5336599
theorem B10678985 : Blo 1873638 10678985 := bstep (se 2 (by rfl) ⟨4004619, by rfl⟩ : syracuseStep 10678985 = 8009239) B8009239
theorem B17330959 : Blo 1873638 17330959 := bstep (se 1 (by rfl) ⟨12998219, by rfl⟩ : syracuseStep 17330959 = 25996439) B25996439
theorem B19280729 : Blo 1873638 19280729 := bstep (se 2 (by rfl) ⟨7230273, by rfl⟩ : syracuseStep 19280729 = 14460547) B14460547
theorem B5698451 : Blo 1873638 5698451 := bstep (se 1 (by rfl) ⟨4273838, by rfl⟩ : syracuseStep 5698451 = 8547677) B8547677
theorem B5338057 : Blo 1873638 5338057 := bstep (se 2 (by rfl) ⟨2001771, by rfl⟩ : syracuseStep 5338057 = 4003543) B4003543
theorem B4215851 : Blo 1873638 4215851 := bstep (se 1 (by rfl) ⟨3161888, by rfl⟩ : syracuseStep 4215851 = 6323777) B6323777
theorem B9385003 : Blo 1873638 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B2372743 : Blo 1873638 2372743 := bstep (se 1 (by rfl) ⟨1779557, by rfl⟩ : syracuseStep 2372743 = 3559115) B3559115
theorem B9008435 : Blo 1873638 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B14234939 : Blo 1873638 14234939 := bstep (se 1 (by rfl) ⟨10676204, by rfl⟩ : syracuseStep 14234939 = 21352409) B21352409
theorem B3798407 : Blo 1873638 3798407 := bstep (se 1 (by rfl) ⟨2848805, by rfl⟩ : syracuseStep 3798407 = 5697611) B5697611
theorem B4216211 : Blo 1873638 4216211 := bstep (se 1 (by rfl) ⟨3162158, by rfl⟩ : syracuseStep 4216211 = 6324317) B6324317
theorem B4216265 : Blo 1873638 4216265 := bstep (se 2 (by rfl) ⟨1581099, by rfl⟩ : syracuseStep 4216265 = 3162199) B3162199
theorem B9008587 : Blo 1873638 9008587 := bstep (se 1 (by rfl) ⟨6756440, by rfl⟩ : syracuseStep 9008587 = 13512881) B13512881
theorem B24016337 : Blo 1873638 24016337 := bstep (se 2 (by rfl) ⟨9006126, by rfl⟩ : syracuseStep 24016337 = 18012253) B18012253
theorem B10827229 : Blo 1873638 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B9008663 : Blo 1873638 9008663 := bstep (se 1 (by rfl) ⟨6756497, by rfl⟩ : syracuseStep 9008663 = 13512995) B13512995
theorem B6411863 : Blo 1873638 6411863 := bstep (se 1 (by rfl) ⟨4808897, by rfl⟩ : syracuseStep 6411863 = 9617795) B9617795
theorem B7116407 : Blo 1873638 7116407 := bstep (se 1 (by rfl) ⟨5337305, by rfl⟩ : syracuseStep 7116407 = 10674611) B10674611
theorem B2373239 : Blo 1873638 2373239 := bstep (se 1 (by rfl) ⟨1779929, by rfl⟩ : syracuseStep 2373239 = 3559859) B3559859
theorem B5068489 : Blo 1873638 5068489 := bstep (se 2 (by rfl) ⟨1900683, by rfl⟩ : syracuseStep 5068489 = 3801367) B3801367
theorem B1873671 : Blo 1873638 1873671 := bstep (se 1 (by rfl) ⟨1405253, by rfl⟩ : syracuseStep 1873671 = 2810507) B2810507
theorem B1873679 : Blo 1873638 1873679 := bstep (se 1 (by rfl) ⟨1405259, by rfl⟩ : syracuseStep 1873679 = 2810519) B2810519
theorem B2373391 : Blo 1873638 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B1873723 : Blo 1873638 1873723 := bstep (se 1 (by rfl) ⟨1405292, by rfl⟩ : syracuseStep 1873723 = 2810585) B2810585
theorem B1873799 : Blo 1873638 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B1873807 : Blo 1873638 1873807 := bstep (se 1 (by rfl) ⟨1405355, by rfl⟩ : syracuseStep 1873807 = 2810711) B2810711
theorem B2668459 : Blo 1873638 2668459 := bstep (se 1 (by rfl) ⟨2001344, by rfl⟩ : syracuseStep 2668459 = 4002689) B4002689
theorem B1873851 : Blo 1873638 1873851 := bstep (se 1 (by rfl) ⟨1405388, by rfl⟩ : syracuseStep 1873851 = 2810777) B2810777
theorem B2373563 : Blo 1873638 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B1873927 : Blo 1873638 1873927 := bstep (se 1 (by rfl) ⟨1405445, by rfl⟩ : syracuseStep 1873927 = 2810891) B2810891
theorem B1873935 : Blo 1873638 1873935 := bstep (se 1 (by rfl) ⟨1405451, by rfl⟩ : syracuseStep 1873935 = 2810903) B2810903
theorem B1873979 : Blo 1873638 1873979 := bstep (se 1 (by rfl) ⟨1405484, by rfl⟩ : syracuseStep 1873979 = 2810969) B2810969
theorem B10672195 : Blo 1873638 10672195 := bstep (se 1 (by rfl) ⟨8004146, by rfl⟩ : syracuseStep 10672195 = 16008293) B16008293
theorem B1874055 : Blo 1873638 1874055 := bstep (se 1 (by rfl) ⟨1405541, by rfl⟩ : syracuseStep 1874055 = 2811083) B2811083
theorem B4216967 : Blo 1873638 4216967 := bstep (se 1 (by rfl) ⟨3162725, by rfl⟩ : syracuseStep 4216967 = 6325451) B6325451
theorem B1874063 : Blo 1873638 1874063 := bstep (se 1 (by rfl) ⟨1405547, by rfl⟩ : syracuseStep 1874063 = 2811095) B2811095
theorem B4003987 : Blo 1873638 4003987 := bstep (se 1 (by rfl) ⟨3002990, by rfl⟩ : syracuseStep 4003987 = 6005981) B6005981
theorem B1874107 : Blo 1873638 1874107 := bstep (se 1 (by rfl) ⟨1405580, by rfl⟩ : syracuseStep 1874107 = 2811161) B2811161
theorem B1874183 : Blo 1873638 1874183 := bstep (se 1 (by rfl) ⟨1405637, by rfl⟩ : syracuseStep 1874183 = 2811275) B2811275
theorem B1874191 : Blo 1873638 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B21346577 : Blo 1873638 21346577 := bstep (se 2 (by rfl) ⟨8004966, by rfl⟩ : syracuseStep 21346577 = 16009933) B16009933
theorem B1874235 : Blo 1873638 1874235 := bstep (se 1 (by rfl) ⟨1405676, by rfl⟩ : syracuseStep 1874235 = 2811353) B2811353
theorem B4217147 : Blo 1873638 4217147 := bstep (se 1 (by rfl) ⟨3162860, by rfl⟩ : syracuseStep 4217147 = 6325721) B6325721
theorem B5413235 : Blo 1873638 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B1874311 : Blo 1873638 1874311 := bstep (se 1 (by rfl) ⟨1405733, by rfl⟩ : syracuseStep 1874311 = 2811467) B2811467
theorem B1874319 : Blo 1873638 1874319 := bstep (se 1 (by rfl) ⟨1405739, by rfl⟩ : syracuseStep 1874319 = 2811479) B2811479
theorem B4217273 : Blo 1873638 4217273 := bstep (se 2 (by rfl) ⟨1581477, by rfl⟩ : syracuseStep 4217273 = 3162955) B3162955
theorem B10680761 : Blo 1873638 10680761 := bstep (se 2 (by rfl) ⟨4005285, by rfl⟩ : syracuseStep 10680761 = 8010571) B8010571
theorem B1874363 : Blo 1873638 1874363 := bstep (se 1 (by rfl) ⟨1405772, by rfl⟩ : syracuseStep 1874363 = 2811545) B2811545
theorem B1874439 : Blo 1873638 1874439 := bstep (se 1 (by rfl) ⟨1405829, by rfl⟩ : syracuseStep 1874439 = 2811659) B2811659
theorem B10131979 : Blo 1873638 10131979 := bstep (se 1 (by rfl) ⟨7598984, by rfl⟩ : syracuseStep 10131979 = 15197969) B15197969
theorem B1874447 : Blo 1873638 1874447 := bstep (se 1 (by rfl) ⟨1405835, by rfl⟩ : syracuseStep 1874447 = 2811671) B2811671
theorem B1874491 : Blo 1873638 1874491 := bstep (se 1 (by rfl) ⟨1405868, by rfl⟩ : syracuseStep 1874491 = 2811737) B2811737
theorem B7117379 : Blo 1873638 7117379 := bstep (se 1 (by rfl) ⟨5338034, by rfl⟩ : syracuseStep 7117379 = 10676069) B10676069
theorem B1874567 : Blo 1873638 1874567 := bstep (se 1 (by rfl) ⟨1405925, by rfl⟩ : syracuseStep 1874567 = 2811851) B2811851
theorem B1874575 : Blo 1873638 1874575 := bstep (se 1 (by rfl) ⟨1405931, by rfl⟩ : syracuseStep 1874575 = 2811863) B2811863
theorem B1874619 : Blo 1873638 1874619 := bstep (se 1 (by rfl) ⟨1405964, by rfl⟩ : syracuseStep 1874619 = 2811929) B2811929
theorem B1874695 : Blo 1873638 1874695 := bstep (se 1 (by rfl) ⟨1406021, by rfl⟩ : syracuseStep 1874695 = 2812043) B2812043
theorem B5339915 : Blo 1873638 5339915 := bstep (se 1 (by rfl) ⟨4004936, by rfl⟩ : syracuseStep 5339915 = 8009873) B8009873
theorem B4217615 : Blo 1873638 4217615 := bstep (se 1 (by rfl) ⟨3163211, by rfl⟩ : syracuseStep 4217615 = 6326423) B6326423
theorem B1874703 : Blo 1873638 1874703 := bstep (se 1 (by rfl) ⟨1406027, by rfl⟩ : syracuseStep 1874703 = 2812055) B2812055
theorem B4217633 : Blo 1873638 4217633 := bstep (se 2 (by rfl) ⟨1581612, by rfl⟩ : syracuseStep 4217633 = 3163225) B3163225
theorem B1874747 : Blo 1873638 1874747 := bstep (se 1 (by rfl) ⟨1406060, by rfl⟩ : syracuseStep 1874747 = 2812121) B2812121
theorem B1874823 : Blo 1873638 1874823 := bstep (se 1 (by rfl) ⟨1406117, by rfl⟩ : syracuseStep 1874823 = 2812235) B2812235
theorem B1874831 : Blo 1873638 1874831 := bstep (se 1 (by rfl) ⟨1406123, by rfl⟩ : syracuseStep 1874831 = 2812247) B2812247
theorem B20274083 : Blo 1873638 20274083 := bstep (se 1 (by rfl) ⟨15205562, by rfl⟩ : syracuseStep 20274083 = 30411125) B30411125
theorem B36051875 : Blo 1873638 36051875 := bstep (se 1 (by rfl) ⟨27038906, by rfl⟩ : syracuseStep 36051875 = 54077813) B54077813
theorem B1874875 : Blo 1873638 1874875 := bstep (se 1 (by rfl) ⟨1406156, by rfl⟩ : syracuseStep 1874875 = 2812313) B2812313
theorem B8223697 : Blo 1873638 8223697 := bstep (se 2 (by rfl) ⟨3083886, by rfl⟩ : syracuseStep 8223697 = 6167773) B6167773
theorem B1874951 : Blo 1873638 1874951 := bstep (se 1 (by rfl) ⟨1406213, by rfl⟩ : syracuseStep 1874951 = 2812427) B2812427
theorem B1874959 : Blo 1873638 1874959 := bstep (se 1 (by rfl) ⟨1406219, by rfl⟩ : syracuseStep 1874959 = 2812439) B2812439
theorem B1875003 : Blo 1873638 1875003 := bstep (se 1 (by rfl) ⟨1406252, by rfl⟩ : syracuseStep 1875003 = 2812505) B2812505
theorem B27016253 : Blo 1873638 27016253 := bstep (se 3 (by rfl) ⟨5065547, by rfl⟩ : syracuseStep 27016253 = 10131095) B10131095
theorem B2849911 : Blo 1873638 2849911 := bstep (se 1 (by rfl) ⟨2137433, by rfl⟩ : syracuseStep 2849911 = 4274867) B4274867
theorem B4217975 : Blo 1873638 4217975 := bstep (se 1 (by rfl) ⟨3163481, by rfl⟩ : syracuseStep 4217975 = 6326963) B6326963
theorem B2604151 : Blo 1873638 2604151 := bstep (se 1 (by rfl) ⟨1953113, by rfl⟩ : syracuseStep 2604151 = 3906227) B3906227
theorem B1875079 : Blo 1873638 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1875087 : Blo 1873638 1875087 := bstep (se 1 (by rfl) ⟨1406315, by rfl⟩ : syracuseStep 1875087 = 2812631) B2812631
theorem B14818477 : Blo 1873638 14818477 := bstep (se 3 (by rfl) ⟨2778464, by rfl⟩ : syracuseStep 14818477 = 5556929) B5556929
theorem B1875131 : Blo 1873638 1875131 := bstep (se 1 (by rfl) ⟨1406348, by rfl⟩ : syracuseStep 1875131 = 2812697) B2812697
theorem B9010433 : Blo 1873638 9010433 := bstep (se 2 (by rfl) ⟨3378912, by rfl⟩ : syracuseStep 9010433 = 6757825) B6757825
theorem B1875207 : Blo 1873638 1875207 := bstep (se 1 (by rfl) ⟨1406405, by rfl⟩ : syracuseStep 1875207 = 2812811) B2812811
theorem B6003983 : Blo 1873638 6003983 := bstep (se 1 (by rfl) ⟨4502987, by rfl⟩ : syracuseStep 6003983 = 9005975) B9005975
theorem B1875215 : Blo 1873638 1875215 := bstep (se 1 (by rfl) ⟨1406411, by rfl⟩ : syracuseStep 1875215 = 2812823) B2812823
theorem B3800353 : Blo 1873638 3800353 := bstep (se 2 (by rfl) ⟨1425132, by rfl⟩ : syracuseStep 3800353 = 2850265) B2850265
theorem B4218155 : Blo 1873638 4218155 := bstep (se 1 (by rfl) ⟨3163616, by rfl⟩ : syracuseStep 4218155 = 6327233) B6327233
theorem B1875259 : Blo 1873638 1875259 := bstep (se 1 (by rfl) ⟨1406444, by rfl⟩ : syracuseStep 1875259 = 2812889) B2812889
theorem B72039779 : Blo 1873638 72039779 := bstep (se 1 (by rfl) ⟨54029834, by rfl⟩ : syracuseStep 72039779 = 108059669) B108059669
theorem B1875335 : Blo 1873638 1875335 := bstep (se 1 (by rfl) ⟨1406501, by rfl⟩ : syracuseStep 1875335 = 2813003) B2813003
theorem B1875343 : Blo 1873638 1875343 := bstep (se 1 (by rfl) ⟨1406507, by rfl⟩ : syracuseStep 1875343 = 2813015) B2813015
theorem B5340563 : Blo 1873638 5340563 := bstep (se 1 (by rfl) ⟨4005422, by rfl⟩ : syracuseStep 5340563 = 8010845) B8010845
theorem B1875387 : Blo 1873638 1875387 := bstep (se 1 (by rfl) ⟨1406540, by rfl⟩ : syracuseStep 1875387 = 2813081) B2813081
theorem B1875463 : Blo 1873638 1875463 := bstep (se 1 (by rfl) ⟨1406597, by rfl⟩ : syracuseStep 1875463 = 2813195) B2813195
theorem B6323723 : Blo 1873638 6323723 := bstep (se 1 (by rfl) ⟨4742792, by rfl⟩ : syracuseStep 6323723 = 9485585) B9485585
theorem B4742671 : Blo 1873638 4742671 := bstep (se 1 (by rfl) ⟨3557003, by rfl⟩ : syracuseStep 4742671 = 7114007) B7114007
theorem B1875471 : Blo 1873638 1875471 := bstep (se 1 (by rfl) ⟨1406603, by rfl⟩ : syracuseStep 1875471 = 2813207) B2813207
theorem B1875515 : Blo 1873638 1875515 := bstep (se 1 (by rfl) ⟨1406636, by rfl⟩ : syracuseStep 1875515 = 2813273) B2813273
theorem B6323831 : Blo 1873638 6323831 := bstep (se 1 (by rfl) ⟨4742873, by rfl⟩ : syracuseStep 6323831 = 9485747) B9485747
theorem B5340791 : Blo 1873638 5340791 := bstep (se 1 (by rfl) ⟨4005593, by rfl⟩ : syracuseStep 5340791 = 8011187) B8011187
theorem B1875591 : Blo 1873638 1875591 := bstep (se 1 (by rfl) ⟨1406693, by rfl⟩ : syracuseStep 1875591 = 2813387) B2813387
theorem B1875599 : Blo 1873638 1875599 := bstep (se 1 (by rfl) ⟨1406699, by rfl⟩ : syracuseStep 1875599 = 2813399) B2813399
theorem B4218515 : Blo 1873638 4218515 := bstep (se 1 (by rfl) ⟨3163886, by rfl⟩ : syracuseStep 4218515 = 6327773) B6327773
theorem B3161801 : Blo 1873638 3161801 := bstep (se 2 (by rfl) ⟨1185675, by rfl⟩ : syracuseStep 3161801 = 2371351) B2371351
theorem B4218569 : Blo 1873638 4218569 := bstep (se 2 (by rfl) ⟨1581963, by rfl⟩ : syracuseStep 4218569 = 3163927) B3163927
theorem B2252551 : Blo 1873638 2252551 := bstep (se 1 (by rfl) ⟨1689413, by rfl⟩ : syracuseStep 2252551 = 3378827) B3378827
theorem B4742945 : Blo 1873638 4742945 := bstep (se 2 (by rfl) ⟨1778604, by rfl⟩ : syracuseStep 4742945 = 3557209) B3557209
theorem B12017497 : Blo 1873638 12017497 := bstep (se 2 (by rfl) ⟨4506561, by rfl⟩ : syracuseStep 12017497 = 9013123) B9013123
theorem B9486233 : Blo 1873638 9486233 := bstep (se 2 (by rfl) ⟨3557337, by rfl⟩ : syracuseStep 9486233 = 7114675) B7114675
theorem B7118867 : Blo 1873638 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B3801107 : Blo 1873638 3801107 := bstep (se 1 (by rfl) ⟨2850830, by rfl⟩ : syracuseStep 3801107 = 5701661) B5701661
theorem B14229593 : Blo 1873638 14229593 := bstep (se 2 (by rfl) ⟨5336097, by rfl⟩ : syracuseStep 14229593 = 10672195) B10672195
theorem B3850337 : Blo 1873638 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B9011357 : Blo 1873638 9011357 := bstep (se 3 (by rfl) ⟨1689629, by rfl⟩ : syracuseStep 9011357 = 3379259) B3379259
theorem B4219127 : Blo 1873638 4219127 := bstep (se 1 (by rfl) ⟨3164345, by rfl⟩ : syracuseStep 4219127 = 6328691) B6328691
theorem B3162361 : Blo 1873638 3162361 := bstep (se 2 (by rfl) ⟨1185885, by rfl⟩ : syracuseStep 3162361 = 2371771) B2371771
theorem B3801439 : Blo 1873638 3801439 := bstep (se 1 (by rfl) ⟨2851079, by rfl⟩ : syracuseStep 3801439 = 5702159) B5702159
theorem B4743643 : Blo 1873638 4743643 := bstep (se 1 (by rfl) ⟨3557732, by rfl⟩ : syracuseStep 4743643 = 7115465) B7115465
theorem B7119323 : Blo 1873638 7119323 := bstep (se 1 (by rfl) ⟨5339492, by rfl⟩ : syracuseStep 7119323 = 10678985) B10678985
theorem B3162631 : Blo 1873638 3162631 := bstep (se 1 (by rfl) ⟨2371973, by rfl⟩ : syracuseStep 3162631 = 4743947) B4743947
theorem B9486881 : Blo 1873638 9486881 := bstep (se 2 (by rfl) ⟨3557580, by rfl⟩ : syracuseStep 9486881 = 7115161) B7115161
theorem B3424807 : Blo 1873638 3424807 := bstep (se 1 (by rfl) ⟨2568605, by rfl⟩ : syracuseStep 3424807 = 5137211) B5137211
theorem B12853819 : Blo 1873638 12853819 := bstep (se 1 (by rfl) ⟨9640364, by rfl⟩ : syracuseStep 12853819 = 19280729) B19280729
theorem B13509305 : Blo 1873638 13509305 := bstep (se 2 (by rfl) ⟨5065989, by rfl⟩ : syracuseStep 13509305 = 10131979) B10131979
theorem B2810567 : Blo 1873638 2810567 := bstep (se 1 (by rfl) ⟨2107925, by rfl⟩ : syracuseStep 2810567 = 4215851) B4215851
theorem B4219721 : Blo 1873638 4219721 := bstep (se 2 (by rfl) ⟨1582395, by rfl⟩ : syracuseStep 4219721 = 3164791) B3164791
theorem B2810729 : Blo 1873638 2810729 := bstep (se 2 (by rfl) ⟨1054023, by rfl⟩ : syracuseStep 2810729 = 2108047) B2108047
theorem B6005623 : Blo 1873638 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B2532271 : Blo 1873638 2532271 := bstep (se 1 (by rfl) ⟨1899203, by rfl⟩ : syracuseStep 2532271 = 3798407) B3798407
theorem B2810807 : Blo 1873638 2810807 := bstep (se 1 (by rfl) ⟨2108105, by rfl⟩ : syracuseStep 2810807 = 4216211) B4216211
theorem B3163063 : Blo 1873638 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B2810843 : Blo 1873638 2810843 := bstep (se 1 (by rfl) ⟨2108132, by rfl⟩ : syracuseStep 2810843 = 4216265) B4216265
theorem B14435293 : Blo 1873638 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B4744271 : Blo 1873638 4744271 := bstep (se 1 (by rfl) ⟨3558203, by rfl⟩ : syracuseStep 4744271 = 7116407) B7116407
theorem B3163259 : Blo 1873638 3163259 := bstep (se 1 (by rfl) ⟨2372444, by rfl⟩ : syracuseStep 3163259 = 4744889) B4744889
theorem B2811311 : Blo 1873638 2811311 := bstep (se 1 (by rfl) ⟨2108483, by rfl⟩ : syracuseStep 2811311 = 4216967) B4216967
theorem B5703131 : Blo 1873638 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B2811401 : Blo 1873638 2811401 := bstep (se 2 (by rfl) ⟨1054275, by rfl⟩ : syracuseStep 2811401 = 2108551) B2108551
theorem B14231051 : Blo 1873638 14231051 := bstep (se 1 (by rfl) ⟨10673288, by rfl⟩ : syracuseStep 14231051 = 21346577) B21346577
theorem B3163657 : Blo 1873638 3163657 := bstep (se 2 (by rfl) ⟨1186371, by rfl⟩ : syracuseStep 3163657 = 2372743) B2372743
theorem B2811431 : Blo 1873638 2811431 := bstep (se 1 (by rfl) ⟨2108573, by rfl⟩ : syracuseStep 2811431 = 4217147) B4217147
theorem B6325883 : Blo 1873638 6325883 := bstep (se 1 (by rfl) ⟨4744412, by rfl⟩ : syracuseStep 6325883 = 9488825) B9488825
theorem B2811515 : Blo 1873638 2811515 := bstep (se 1 (by rfl) ⟨2108636, by rfl⟩ : syracuseStep 2811515 = 4217273) B4217273
theorem B7120507 : Blo 1873638 7120507 := bstep (se 1 (by rfl) ⟨5340380, by rfl⟩ : syracuseStep 7120507 = 10680761) B10680761
theorem B16017041 : Blo 1873638 16017041 := bstep (se 2 (by rfl) ⟨6006390, by rfl⟩ : syracuseStep 16017041 = 12012781) B12012781
theorem B3163819 : Blo 1873638 3163819 := bstep (se 1 (by rfl) ⟨2372864, by rfl⟩ : syracuseStep 3163819 = 4745729) B4745729
theorem B4744919 : Blo 1873638 4744919 := bstep (se 1 (by rfl) ⟨3558689, by rfl⟩ : syracuseStep 4744919 = 7117379) B7117379
theorem B2811641 : Blo 1873638 2811641 := bstep (se 2 (by rfl) ⟨1054365, by rfl⟩ : syracuseStep 2811641 = 2108731) B2108731
theorem B6326045 : Blo 1873638 6326045 := bstep (se 3 (by rfl) ⟨1186133, by rfl⟩ : syracuseStep 6326045 = 2372267) B2372267
theorem B2811743 : Blo 1873638 2811743 := bstep (se 1 (by rfl) ⟨2108807, by rfl⟩ : syracuseStep 2811743 = 4217615) B4217615
theorem B2811755 : Blo 1873638 2811755 := bstep (se 1 (by rfl) ⟨2108816, by rfl⟩ : syracuseStep 2811755 = 4217633) B4217633
theorem B12011399 : Blo 1873638 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B54044597 : Blo 1873638 54044597 := bstep (se 5 (by rfl) ⟨2533340, by rfl⟩ : syracuseStep 54044597 = 5066681) B5066681
theorem B12011449 : Blo 1873638 12011449 := bstep (se 2 (by rfl) ⟨4504293, by rfl⟩ : syracuseStep 12011449 = 9008587) B9008587
theorem B14436305 : Blo 1873638 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B3164123 : Blo 1873638 3164123 := bstep (se 1 (by rfl) ⟨2373092, by rfl⟩ : syracuseStep 3164123 = 4746185) B4746185
theorem B2811983 : Blo 1873638 2811983 := bstep (se 1 (by rfl) ⟨2108987, by rfl⟩ : syracuseStep 2811983 = 4217975) B4217975
theorem B48720005 : Blo 1873638 48720005 := bstep (se 4 (by rfl) ⟨4567500, by rfl⟩ : syracuseStep 48720005 = 9135001) B9135001
theorem B6006955 : Blo 1873638 6006955 := bstep (se 1 (by rfl) ⟨4505216, by rfl⟩ : syracuseStep 6006955 = 9010433) B9010433
theorem B2812103 : Blo 1873638 2812103 := bstep (se 1 (by rfl) ⟨2109077, by rfl⟩ : syracuseStep 2812103 = 4218155) B4218155
theorem B3164359 : Blo 1873638 3164359 := bstep (se 1 (by rfl) ⟨2373269, by rfl⟩ : syracuseStep 3164359 = 4746539) B4746539
theorem B2812265 : Blo 1873638 2812265 := bstep (se 2 (by rfl) ⟨1054599, by rfl⟩ : syracuseStep 2812265 = 2109199) B2109199
theorem B3164521 : Blo 1873638 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B27019655 : Blo 1873638 27019655 := bstep (se 1 (by rfl) ⟨20264741, by rfl⟩ : syracuseStep 27019655 = 40529483) B40529483
theorem B2812343 : Blo 1873638 2812343 := bstep (se 1 (by rfl) ⟨2109257, by rfl⟩ : syracuseStep 2812343 = 4218515) B4218515
theorem B2107867 : Blo 1873638 2107867 := bstep (se 1 (by rfl) ⟨1580900, by rfl⟩ : syracuseStep 2107867 = 3161801) B3161801
theorem B6326747 : Blo 1873638 6326747 := bstep (se 1 (by rfl) ⟨4745060, by rfl⟩ : syracuseStep 6326747 = 9490121) B9490121
theorem B2812379 : Blo 1873638 2812379 := bstep (se 1 (by rfl) ⟨2109284, by rfl⟩ : syracuseStep 2812379 = 4218569) B4218569
theorem B3557945 : Blo 1873638 3557945 := bstep (se 2 (by rfl) ⟨1334229, by rfl⟩ : syracuseStep 3557945 = 2668459) B2668459
theorem B9128659 : Blo 1873638 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B3377875 : Blo 1873638 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B2534249 : Blo 1873638 2534249 := bstep (se 2 (by rfl) ⟨950343, by rfl⟩ : syracuseStep 2534249 = 1900687) B1900687
theorem B2108335 : Blo 1873638 2108335 := bstep (se 1 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 2108335 = 3162503) B3162503
theorem B2812847 : Blo 1873638 2812847 := bstep (se 1 (by rfl) ⟨2109635, by rfl⟩ : syracuseStep 2812847 = 4219271) B4219271
theorem B3165115 : Blo 1873638 3165115 := bstep (se 1 (by rfl) ⟨2373836, by rfl⟩ : syracuseStep 3165115 = 4747673) B4747673
theorem B2812937 : Blo 1873638 2812937 := bstep (se 2 (by rfl) ⟨1054851, by rfl⟩ : syracuseStep 2812937 = 2109703) B2109703
theorem B45591569 : Blo 1873638 45591569 := bstep (se 2 (by rfl) ⟨17096838, by rfl⟩ : syracuseStep 45591569 = 34193677) B34193677
theorem B2812967 : Blo 1873638 2812967 := bstep (se 1 (by rfl) ⟨2109725, by rfl⟩ : syracuseStep 2812967 = 4219451) B4219451
theorem B2813051 : Blo 1873638 2813051 := bstep (se 1 (by rfl) ⟨2109788, by rfl⟩ : syracuseStep 2813051 = 4219577) B4219577
theorem B6327449 : Blo 1873638 6327449 := bstep (se 2 (by rfl) ⟨2372793, by rfl⟩ : syracuseStep 6327449 = 4745587) B4745587
theorem B2813177 : Blo 1873638 2813177 := bstep (se 2 (by rfl) ⟨1054941, by rfl⟩ : syracuseStep 2813177 = 2109883) B2109883
theorem B10677527 : Blo 1873638 10677527 := bstep (se 1 (by rfl) ⟨8008145, by rfl⟩ : syracuseStep 10677527 = 16016291) B16016291
theorem B15199525 : Blo 1873638 15199525 := bstep (se 4 (by rfl) ⟨1424955, by rfl⟩ : syracuseStep 15199525 = 2849911) B2849911
theorem B2108767 : Blo 1873638 2108767 := bstep (se 1 (by rfl) ⟨1581575, by rfl⟩ : syracuseStep 2108767 = 3163151) B3163151
theorem B2813279 : Blo 1873638 2813279 := bstep (se 1 (by rfl) ⟨2109959, by rfl⟩ : syracuseStep 2813279 = 4219919) B4219919
theorem B2813291 : Blo 1873638 2813291 := bstep (se 1 (by rfl) ⟨2109968, by rfl⟩ : syracuseStep 2813291 = 4219937) B4219937
theorem B14232995 : Blo 1873638 14232995 := bstep (se 1 (by rfl) ⟨10674746, by rfl⟩ : syracuseStep 14232995 = 21349493) B21349493
theorem B21343661 : Blo 1873638 21343661 := bstep (se 3 (by rfl) ⟨4001936, by rfl⟩ : syracuseStep 21343661 = 8003873) B8003873
theorem B9489959 : Blo 1873638 9489959 := bstep (se 1 (by rfl) ⟨7117469, by rfl⟩ : syracuseStep 9489959 = 14234939) B14234939
theorem B16010891 : Blo 1873638 16010891 := bstep (se 1 (by rfl) ⟨12008168, by rfl⟩ : syracuseStep 16010891 = 24016337) B24016337
theorem B2109127 : Blo 1873638 2109127 := bstep (se 1 (by rfl) ⟨1581845, by rfl⟩ : syracuseStep 2109127 = 3163691) B3163691
theorem B6008737 : Blo 1873638 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B12513337 : Blo 1873638 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B24023101 : Blo 1873638 24023101 := bstep (se 3 (by rfl) ⟨4504331, by rfl⟩ : syracuseStep 24023101 = 9008663) B9008663
theorem B4747511 : Blo 1873638 4747511 := bstep (se 1 (by rfl) ⟨3560633, by rfl⟩ : syracuseStep 4747511 = 7121267) B7121267
theorem B6328637 : Blo 1873638 6328637 := bstep (se 3 (by rfl) ⟨1186619, by rfl⟩ : syracuseStep 6328637 = 2373239) B2373239
theorem B5067137 : Blo 1873638 5067137 := bstep (se 2 (by rfl) ⟨1900176, by rfl⟩ : syracuseStep 5067137 = 3800353) B3800353
theorem B3559943 : Blo 1873638 3559943 := bstep (se 1 (by rfl) ⟨2669957, by rfl⟩ : syracuseStep 3559943 = 5339915) B5339915
theorem B4002313 : Blo 1873638 4002313 := bstep (se 2 (by rfl) ⟨1500867, by rfl⟩ : syracuseStep 4002313 = 3001735) B3001735
theorem B2109991 : Blo 1873638 2109991 := bstep (se 1 (by rfl) ⟨1582493, by rfl⟩ : syracuseStep 2109991 = 3164987) B3164987
theorem B18010835 : Blo 1873638 18010835 := bstep (se 1 (by rfl) ⟨13508126, by rfl⟩ : syracuseStep 18010835 = 27016253) B27016253
theorem B28848899 : Blo 1873638 28848899 := bstep (se 1 (by rfl) ⟨21636674, by rfl⟩ : syracuseStep 28848899 = 43273349) B43273349
theorem B11399939 : Blo 1873638 11399939 := bstep (se 1 (by rfl) ⟨8549954, by rfl⟩ : syracuseStep 11399939 = 17099909) B17099909
theorem B4002655 : Blo 1873638 4002655 := bstep (se 1 (by rfl) ⟨3001991, by rfl⟩ : syracuseStep 4002655 = 6003983) B6003983
theorem B48026519 : Blo 1873638 48026519 := bstep (se 1 (by rfl) ⟨36019889, by rfl⟩ : syracuseStep 48026519 = 72039779) B72039779
theorem B3560375 : Blo 1873638 3560375 := bstep (se 1 (by rfl) ⟨2670281, by rfl⟩ : syracuseStep 3560375 = 5340563) B5340563
theorem B4215815 : Blo 1873638 4215815 := bstep (se 1 (by rfl) ⟨3161861, by rfl⟩ : syracuseStep 4215815 = 6323723) B6323723
theorem B3003401 : Blo 1873638 3003401 := bstep (se 2 (by rfl) ⟨1126275, by rfl⟩ : syracuseStep 3003401 = 2252551) B2252551
theorem B2372647 : Blo 1873638 2372647 := bstep (se 1 (by rfl) ⟨1779485, by rfl⟩ : syracuseStep 2372647 = 3558971) B3558971
theorem B4215887 : Blo 1873638 4215887 := bstep (se 1 (by rfl) ⟨3161915, by rfl⟩ : syracuseStep 4215887 = 6323831) B6323831
theorem B3560527 : Blo 1873638 3560527 := bstep (se 1 (by rfl) ⟨2670395, by rfl⟩ : syracuseStep 3560527 = 5340791) B5340791
theorem B6329501 : Blo 1873638 6329501 := bstep (se 3 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 6329501 = 2373563) B2373563
theorem B7116119 : Blo 1873638 7116119 := bstep (se 1 (by rfl) ⟨5337089, by rfl⟩ : syracuseStep 7116119 = 10674179) B10674179
theorem B2372971 : Blo 1873638 2372971 := bstep (se 1 (by rfl) ⟨1779728, by rfl⟩ : syracuseStep 2372971 = 3559457) B3559457
theorem B12015013 : Blo 1873638 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B10139053 : Blo 1873638 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B4216283 : Blo 1873638 4216283 := bstep (se 1 (by rfl) ⟨3162212, by rfl⟩ : syracuseStep 4216283 = 6324425) B6324425
theorem B3003913 : Blo 1873638 3003913 := bstep (se 2 (by rfl) ⟨1126467, by rfl⟩ : syracuseStep 3003913 = 2252935) B2252935
theorem B5338649 : Blo 1873638 5338649 := bstep (se 2 (by rfl) ⟨2001993, by rfl⟩ : syracuseStep 5338649 = 4003987) B4003987
theorem B9492065 : Blo 1873638 9492065 := bstep (se 2 (by rfl) ⟨3559524, by rfl⟩ : syracuseStep 9492065 = 7119049) B7119049
theorem B6330041 : Blo 1873638 6330041 := bstep (se 2 (by rfl) ⟨2373765, by rfl⟩ : syracuseStep 6330041 = 4747531) B4747531
theorem B2668231 : Blo 1873638 2668231 := bstep (se 1 (by rfl) ⟨2001173, by rfl⟩ : syracuseStep 2668231 = 4002347) B4002347
theorem B14235425 : Blo 1873638 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B1873703 : Blo 1873638 1873703 := bstep (se 1 (by rfl) ⟨1405277, by rfl⟩ : syracuseStep 1873703 = 2810555) B2810555
theorem B6756139 : Blo 1873638 6756139 := bstep (se 1 (by rfl) ⟨5067104, by rfl⟩ : syracuseStep 6756139 = 10134209) B10134209
theorem B1873743 : Blo 1873638 1873743 := bstep (se 1 (by rfl) ⟨1405307, by rfl⟩ : syracuseStep 1873743 = 2810615) B2810615
theorem B1873759 : Blo 1873638 1873759 := bstep (se 1 (by rfl) ⟨1405319, by rfl⟩ : syracuseStep 1873759 = 2810639) B2810639
theorem B1873787 : Blo 1873638 1873787 := bstep (se 1 (by rfl) ⟨1405340, by rfl⟩ : syracuseStep 1873787 = 2810681) B2810681
theorem B1873839 : Blo 1873638 1873839 := bstep (se 1 (by rfl) ⟨1405379, by rfl⟩ : syracuseStep 1873839 = 2810759) B2810759
theorem B4216751 : Blo 1873638 4216751 := bstep (se 1 (by rfl) ⟨3162563, by rfl⟩ : syracuseStep 4216751 = 6325127) B6325127
theorem B14423993 : Blo 1873638 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B1873863 : Blo 1873638 1873863 := bstep (se 1 (by rfl) ⟨1405397, by rfl⟩ : syracuseStep 1873863 = 2810795) B2810795
theorem B1873883 : Blo 1873638 1873883 := bstep (se 1 (by rfl) ⟨1405412, by rfl⟩ : syracuseStep 1873883 = 2810825) B2810825
theorem B1873959 : Blo 1873638 1873959 := bstep (se 1 (by rfl) ⟨1405469, by rfl⟩ : syracuseStep 1873959 = 2810939) B2810939
theorem B1873999 : Blo 1873638 1873999 := bstep (se 1 (by rfl) ⟨1405499, by rfl⟩ : syracuseStep 1873999 = 2810999) B2810999
theorem B4003919 : Blo 1873638 4003919 := bstep (se 1 (by rfl) ⟨3002939, by rfl⟩ : syracuseStep 4003919 = 6005879) B6005879
theorem B1874015 : Blo 1873638 1874015 := bstep (se 1 (by rfl) ⟨1405511, by rfl⟩ : syracuseStep 1874015 = 2811023) B2811023
theorem B1874043 : Blo 1873638 1874043 := bstep (se 1 (by rfl) ⟨1405532, by rfl⟩ : syracuseStep 1874043 = 2811065) B2811065
theorem B4217003 : Blo 1873638 4217003 := bstep (se 1 (by rfl) ⟨3162752, by rfl⟩ : syracuseStep 4217003 = 6325505) B6325505
theorem B1874095 : Blo 1873638 1874095 := bstep (se 1 (by rfl) ⟨1405571, by rfl⟩ : syracuseStep 1874095 = 2811143) B2811143
theorem B1874119 : Blo 1873638 1874119 := bstep (se 1 (by rfl) ⟨1405589, by rfl⟩ : syracuseStep 1874119 = 2811179) B2811179
theorem B1874139 : Blo 1873638 1874139 := bstep (se 1 (by rfl) ⟨1405604, by rfl⟩ : syracuseStep 1874139 = 2811209) B2811209
theorem B1874215 : Blo 1873638 1874215 := bstep (se 1 (by rfl) ⟨1405661, by rfl⟩ : syracuseStep 1874215 = 2811323) B2811323
theorem B1874255 : Blo 1873638 1874255 := bstep (se 1 (by rfl) ⟨1405691, by rfl⟩ : syracuseStep 1874255 = 2811383) B2811383
theorem B1874271 : Blo 1873638 1874271 := bstep (se 1 (by rfl) ⟨1405703, by rfl⟩ : syracuseStep 1874271 = 2811407) B2811407
theorem B23107945 : Blo 1873638 23107945 := bstep (se 2 (by rfl) ⟨8665479, by rfl⟩ : syracuseStep 23107945 = 17330959) B17330959
theorem B1874299 : Blo 1873638 1874299 := bstep (se 1 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 1874299 = 2811449) B2811449
theorem B25663877 : Blo 1873638 25663877 := bstep (se 4 (by rfl) ⟨2405988, by rfl⟩ : syracuseStep 25663877 = 4811977) B4811977
theorem B4274575 : Blo 1873638 4274575 := bstep (se 1 (by rfl) ⟨3205931, by rfl⟩ : syracuseStep 4274575 = 6411863) B6411863
theorem B1874351 : Blo 1873638 1874351 := bstep (se 1 (by rfl) ⟨1405763, by rfl⟩ : syracuseStep 1874351 = 2811527) B2811527
theorem B1874375 : Blo 1873638 1874375 := bstep (se 1 (by rfl) ⟨1405781, by rfl⟩ : syracuseStep 1874375 = 2811563) B2811563
theorem B1874395 : Blo 1873638 1874395 := bstep (se 1 (by rfl) ⟨1405796, by rfl⟩ : syracuseStep 1874395 = 2811593) B2811593
theorem B20273645 : Blo 1873638 20273645 := bstep (se 3 (by rfl) ⟨3801308, by rfl⟩ : syracuseStep 20273645 = 7602617) B7602617
theorem B1874471 : Blo 1873638 1874471 := bstep (se 1 (by rfl) ⟨1405853, by rfl⟩ : syracuseStep 1874471 = 2811707) B2811707
theorem B1874511 : Blo 1873638 1874511 := bstep (se 1 (by rfl) ⟨1405883, by rfl⟩ : syracuseStep 1874511 = 2811767) B2811767
theorem B1874527 : Blo 1873638 1874527 := bstep (se 1 (by rfl) ⟨1405895, by rfl⟩ : syracuseStep 1874527 = 2811791) B2811791
theorem B7117409 : Blo 1873638 7117409 := bstep (se 2 (by rfl) ⟨2669028, by rfl⟩ : syracuseStep 7117409 = 5338057) B5338057
theorem B1874555 : Blo 1873638 1874555 := bstep (se 1 (by rfl) ⟨1405916, by rfl⟩ : syracuseStep 1874555 = 2811833) B2811833
theorem B1874607 : Blo 1873638 1874607 := bstep (se 1 (by rfl) ⟨1405955, by rfl⟩ : syracuseStep 1874607 = 2811911) B2811911
theorem B4217543 : Blo 1873638 4217543 := bstep (se 1 (by rfl) ⟨3163157, by rfl⟩ : syracuseStep 4217543 = 6326315) B6326315
theorem B1874631 : Blo 1873638 1874631 := bstep (se 1 (by rfl) ⟨1405973, by rfl⟩ : syracuseStep 1874631 = 2811947) B2811947
theorem B1874651 : Blo 1873638 1874651 := bstep (se 1 (by rfl) ⟨1405988, by rfl⟩ : syracuseStep 1874651 = 2811977) B2811977
theorem B1874727 : Blo 1873638 1874727 := bstep (se 1 (by rfl) ⟨1406045, by rfl⟩ : syracuseStep 1874727 = 2812091) B2812091
theorem B3472201 : Blo 1873638 3472201 := bstep (se 2 (by rfl) ⟨1302075, by rfl⟩ : syracuseStep 3472201 = 2604151) B2604151
theorem B1874767 : Blo 1873638 1874767 := bstep (se 1 (by rfl) ⟨1406075, by rfl⟩ : syracuseStep 1874767 = 2812151) B2812151
theorem B1874783 : Blo 1873638 1874783 := bstep (se 1 (by rfl) ⟨1406087, by rfl⟩ : syracuseStep 1874783 = 2812175) B2812175
theorem B1874811 : Blo 1873638 1874811 := bstep (se 1 (by rfl) ⟨1406108, by rfl⟩ : syracuseStep 1874811 = 2812217) B2812217
theorem B19757969 : Blo 1873638 19757969 := bstep (se 2 (by rfl) ⟨7409238, by rfl⟩ : syracuseStep 19757969 = 14818477) B14818477
theorem B1874863 : Blo 1873638 1874863 := bstep (se 1 (by rfl) ⟨1406147, by rfl⟩ : syracuseStep 1874863 = 2812295) B2812295
theorem B109607861 : Blo 1873638 109607861 := bstep (se 5 (by rfl) ⟨5137868, by rfl⟩ : syracuseStep 109607861 = 10275737) B10275737
theorem B6757307 : Blo 1873638 6757307 := bstep (se 1 (by rfl) ⟨5067980, by rfl⟩ : syracuseStep 6757307 = 10135961) B10135961
theorem B1874887 : Blo 1873638 1874887 := bstep (se 1 (by rfl) ⟨1406165, by rfl⟩ : syracuseStep 1874887 = 2812331) B2812331
theorem B2251739 : Blo 1873638 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B1874907 : Blo 1873638 1874907 := bstep (se 1 (by rfl) ⟨1406180, by rfl⟩ : syracuseStep 1874907 = 2812361) B2812361
theorem B10673153 : Blo 1873638 10673153 := bstep (se 2 (by rfl) ⟨4002432, by rfl⟩ : syracuseStep 10673153 = 8004865) B8004865
theorem B4807687 : Blo 1873638 4807687 := bstep (se 1 (by rfl) ⟨3605765, by rfl⟩ : syracuseStep 4807687 = 7211531) B7211531
theorem B9493523 : Blo 1873638 9493523 := bstep (se 1 (by rfl) ⟨7120142, by rfl⟩ : syracuseStep 9493523 = 14240285) B14240285
theorem B1874983 : Blo 1873638 1874983 := bstep (se 1 (by rfl) ⟨1406237, by rfl⟩ : syracuseStep 1874983 = 2812475) B2812475
theorem B15195185 : Blo 1873638 15195185 := bstep (se 2 (by rfl) ⟨5698194, by rfl⟩ : syracuseStep 15195185 = 11396389) B11396389
theorem B1875023 : Blo 1873638 1875023 := bstep (se 1 (by rfl) ⟨1406267, by rfl⟩ : syracuseStep 1875023 = 2812535) B2812535
theorem B1875039 : Blo 1873638 1875039 := bstep (se 1 (by rfl) ⟨1406279, by rfl⟩ : syracuseStep 1875039 = 2812559) B2812559
theorem B1875067 : Blo 1873638 1875067 := bstep (se 1 (by rfl) ⟨1406300, by rfl⟩ : syracuseStep 1875067 = 2812601) B2812601
theorem B1875119 : Blo 1873638 1875119 := bstep (se 1 (by rfl) ⟨1406339, by rfl⟩ : syracuseStep 1875119 = 2812679) B2812679
theorem B1875143 : Blo 1873638 1875143 := bstep (se 1 (by rfl) ⟨1406357, by rfl⟩ : syracuseStep 1875143 = 2812715) B2812715
theorem B1875163 : Blo 1873638 1875163 := bstep (se 1 (by rfl) ⟨1406372, by rfl⟩ : syracuseStep 1875163 = 2812745) B2812745
theorem B13516055 : Blo 1873638 13516055 := bstep (se 1 (by rfl) ⟨10137041, by rfl⟩ : syracuseStep 13516055 = 20274083) B20274083
theorem B24034583 : Blo 1873638 24034583 := bstep (se 1 (by rfl) ⟨18025937, by rfl⟩ : syracuseStep 24034583 = 36051875) B36051875
theorem B1875239 : Blo 1873638 1875239 := bstep (se 1 (by rfl) ⟨1406429, by rfl⟩ : syracuseStep 1875239 = 2812859) B2812859
theorem B1875279 : Blo 1873638 1875279 := bstep (se 1 (by rfl) ⟨1406459, by rfl⟩ : syracuseStep 1875279 = 2812919) B2812919
theorem B1875295 : Blo 1873638 1875295 := bstep (se 1 (by rfl) ⟨1406471, by rfl⟩ : syracuseStep 1875295 = 2812943) B2812943
theorem B6323561 : Blo 1873638 6323561 := bstep (se 2 (by rfl) ⟨2371335, by rfl⟩ : syracuseStep 6323561 = 4742671) B4742671
theorem B1875323 : Blo 1873638 1875323 := bstep (se 1 (by rfl) ⟨1406492, by rfl⟩ : syracuseStep 1875323 = 2812985) B2812985
theorem B1875375 : Blo 1873638 1875375 := bstep (se 1 (by rfl) ⟨1406531, by rfl⟩ : syracuseStep 1875375 = 2813063) B2813063
theorem B1875399 : Blo 1873638 1875399 := bstep (se 1 (by rfl) ⟨1406549, by rfl⟩ : syracuseStep 1875399 = 2813099) B2813099
theorem B1875419 : Blo 1873638 1875419 := bstep (se 1 (by rfl) ⟨1406564, by rfl⟩ : syracuseStep 1875419 = 2813129) B2813129
theorem B6413833 : Blo 1873638 6413833 := bstep (se 2 (by rfl) ⟨2405187, by rfl⟩ : syracuseStep 6413833 = 4810375) B4810375
theorem B4218407 : Blo 1873638 4218407 := bstep (se 1 (by rfl) ⟨3163805, by rfl⟩ : syracuseStep 4218407 = 6327611) B6327611
theorem B1875495 : Blo 1873638 1875495 := bstep (se 1 (by rfl) ⟨1406621, by rfl⟩ : syracuseStep 1875495 = 2813243) B2813243
theorem B1875535 : Blo 1873638 1875535 := bstep (se 1 (by rfl) ⟨1406651, by rfl⟩ : syracuseStep 1875535 = 2813303) B2813303
theorem B1875551 : Blo 1873638 1875551 := bstep (se 1 (by rfl) ⟨1406663, by rfl⟩ : syracuseStep 1875551 = 2813327) B2813327
theorem B6757985 : Blo 1873638 6757985 := bstep (se 2 (by rfl) ⟨2534244, by rfl⟩ : syracuseStep 6757985 = 5068489) B5068489
theorem B1875579 : Blo 1873638 1875579 := bstep (se 1 (by rfl) ⟨1406684, by rfl⟩ : syracuseStep 1875579 = 2813369) B2813369
theorem B1875631 : Blo 1873638 1875631 := bstep (se 1 (by rfl) ⟨1406723, by rfl⟩ : syracuseStep 1875631 = 2813447) B2813447
theorem B10133191 : Blo 1873638 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B15195869 : Blo 1873638 15195869 := bstep (se 3 (by rfl) ⟨2849225, by rfl⟩ : syracuseStep 15195869 = 5698451) B5698451
theorem B43859717 : Blo 1873638 43859717 := bstep (se 4 (by rfl) ⟨4111848, by rfl⟩ : syracuseStep 43859717 = 8223697) B8223697
theorem B16023329 : Blo 1873638 16023329 := bstep (se 2 (by rfl) ⟨6008748, by rfl⟩ : syracuseStep 16023329 = 12017497) B12017497
theorem B3161929 : Blo 1873638 3161929 := bstep (se 2 (by rfl) ⟨1185723, by rfl⟩ : syracuseStep 3161929 = 2371447) B2371447
theorem B3161963 : Blo 1873638 3161963 := bstep (se 1 (by rfl) ⟨2371472, by rfl⟩ : syracuseStep 3161963 = 4742945) B4742945
theorem B4218731 : Blo 1873638 4218731 := bstep (se 1 (by rfl) ⟨3164048, by rfl⟩ : syracuseStep 4218731 = 6328097) B6328097
theorem B4218785 : Blo 1873638 4218785 := bstep (se 2 (by rfl) ⟨1582044, by rfl⟩ : syracuseStep 4218785 = 3164089) B3164089
theorem B6324155 : Blo 1873638 6324155 := bstep (se 1 (by rfl) ⟨4743116, by rfl⟩ : syracuseStep 6324155 = 9486233) B9486233
theorem B9486395 : Blo 1873638 9486395 := bstep (se 1 (by rfl) ⟨7114796, by rfl⟩ : syracuseStep 9486395 = 14229593) B14229593
theorem B32030801 : Blo 1873638 32030801 := bstep (se 2 (by rfl) ⟨12011550, by rfl⟩ : syracuseStep 32030801 = 24023101) B24023101
theorem B4219091 : Blo 1873638 4219091 := bstep (se 1 (by rfl) ⟨3164318, by rfl⟩ : syracuseStep 4219091 = 6328637) B6328637
theorem B4219145 : Blo 1873638 4219145 := bstep (se 2 (by rfl) ⟨1582179, by rfl⟩ : syracuseStep 4219145 = 3164359) B3164359
theorem B6324587 : Blo 1873638 6324587 := bstep (se 1 (by rfl) ⟨4743440, by rfl⟩ : syracuseStep 6324587 = 9486881) B9486881
theorem B30810593 : Blo 1873638 30810593 := bstep (se 2 (by rfl) ⟨11553972, by rfl⟩ : syracuseStep 30810593 = 23107945) B23107945
theorem B4219361 : Blo 1873638 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B2810489 : Blo 1873638 2810489 := bstep (se 2 (by rfl) ⟨1053933, by rfl⟩ : syracuseStep 2810489 = 2107867) B2107867
theorem B6324857 : Blo 1873638 6324857 := bstep (se 2 (by rfl) ⟨2371821, by rfl⟩ : syracuseStep 6324857 = 4743643) B4743643
theorem B2810543 : Blo 1873638 2810543 := bstep (se 1 (by rfl) ⟨2107907, by rfl⟩ : syracuseStep 2810543 = 4215815) B4215815
theorem B2810591 : Blo 1873638 2810591 := bstep (se 1 (by rfl) ⟨2107943, by rfl⟩ : syracuseStep 2810591 = 4215887) B4215887
theorem B3162847 : Blo 1873638 3162847 := bstep (se 1 (by rfl) ⟨2372135, by rfl⟩ : syracuseStep 3162847 = 4744271) B4744271
theorem B17138425 : Blo 1873638 17138425 := bstep (se 2 (by rfl) ⟨6426909, by rfl⟩ : syracuseStep 17138425 = 12853819) B12853819
theorem B4219667 : Blo 1873638 4219667 := bstep (se 1 (by rfl) ⟨3164750, by rfl⟩ : syracuseStep 4219667 = 6329501) B6329501
theorem B4744079 : Blo 1873638 4744079 := bstep (se 1 (by rfl) ⟨3558059, by rfl⟩ : syracuseStep 4744079 = 7116119) B7116119
theorem B2810855 : Blo 1873638 2810855 := bstep (se 1 (by rfl) ⟨2108141, by rfl⟩ : syracuseStep 2810855 = 4216283) B4216283
theorem B3802087 : Blo 1873638 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B9487367 : Blo 1873638 9487367 := bstep (se 1 (by rfl) ⟨7115525, by rfl⟩ : syracuseStep 9487367 = 14231051) B14231051
theorem B14230565 : Blo 1873638 14230565 := bstep (se 4 (by rfl) ⟨1334115, by rfl⟩ : syracuseStep 14230565 = 2668231) B2668231
theorem B4629601 : Blo 1873638 4629601 := bstep (se 2 (by rfl) ⟨1736100, by rfl⟩ : syracuseStep 4629601 = 3472201) B3472201
theorem B4220027 : Blo 1873638 4220027 := bstep (se 1 (by rfl) ⟨3165020, by rfl⟩ : syracuseStep 4220027 = 6330041) B6330041
theorem B3163279 : Blo 1873638 3163279 := bstep (se 1 (by rfl) ⟨2372459, by rfl⟩ : syracuseStep 3163279 = 4744919) B4744919
theorem B3376361 : Blo 1873638 3376361 := bstep (se 2 (by rfl) ⟨1266135, by rfl⟩ : syracuseStep 3376361 = 2532271) B2532271
theorem B2811113 : Blo 1873638 2811113 := bstep (se 2 (by rfl) ⟨1054167, by rfl⟩ : syracuseStep 2811113 = 2108335) B2108335
theorem B4220153 : Blo 1873638 4220153 := bstep (se 2 (by rfl) ⟨1582557, by rfl⟩ : syracuseStep 4220153 = 3165115) B3165115
theorem B2811167 : Blo 1873638 2811167 := bstep (se 1 (by rfl) ⟨2108375, by rfl⟩ : syracuseStep 2811167 = 4216751) B4216751
theorem B36029731 : Blo 1873638 36029731 := bstep (se 1 (by rfl) ⟨27022298, by rfl⟩ : syracuseStep 36029731 = 54044597) B54044597
theorem B3163529 : Blo 1873638 3163529 := bstep (se 2 (by rfl) ⟨1186323, by rfl⟩ : syracuseStep 3163529 = 2372647) B2372647
theorem B2811335 : Blo 1873638 2811335 := bstep (se 1 (by rfl) ⟨2108501, by rfl⟩ : syracuseStep 2811335 = 4217003) B4217003
theorem B9487853 : Blo 1873638 9487853 := bstep (se 3 (by rfl) ⟨1778972, by rfl⟩ : syracuseStep 9487853 = 3557945) B3557945
theorem B4744939 : Blo 1873638 4744939 := bstep (se 1 (by rfl) ⟨3558704, by rfl⟩ : syracuseStep 4744939 = 7117409) B7117409
theorem B2811689 : Blo 1873638 2811689 := bstep (se 2 (by rfl) ⟨1054383, by rfl⟩ : syracuseStep 2811689 = 2108767) B2108767
theorem B2811695 : Blo 1873638 2811695 := bstep (se 1 (by rfl) ⟨2108771, by rfl⟩ : syracuseStep 2811695 = 4217543) B4217543
theorem B3163961 : Blo 1873638 3163961 := bstep (se 2 (by rfl) ⟨1186485, by rfl⟩ : syracuseStep 3163961 = 2372971) B2372971
theorem B13518737 : Blo 1873638 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B30394379 : Blo 1873638 30394379 := bstep (se 1 (by rfl) ⟨22795784, by rfl⟩ : syracuseStep 30394379 = 45591569) B45591569
theorem B13510921 : Blo 1873638 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B2812169 : Blo 1873638 2812169 := bstep (se 2 (by rfl) ⟨1054563, by rfl⟩ : syracuseStep 2812169 = 2109127) B2109127
theorem B9488663 : Blo 1873638 9488663 := bstep (se 1 (by rfl) ⟨7116497, by rfl⟩ : syracuseStep 9488663 = 14232995) B14232995
theorem B6326639 : Blo 1873638 6326639 := bstep (se 1 (by rfl) ⟨4744979, by rfl⟩ : syracuseStep 6326639 = 9489959) B9489959
theorem B2812271 : Blo 1873638 2812271 := bstep (se 1 (by rfl) ⟨2109203, by rfl⟩ : syracuseStep 2812271 = 4218407) B4218407
theorem B29239811 : Blo 1873638 29239811 := bstep (se 1 (by rfl) ⟨21929858, by rfl⟩ : syracuseStep 29239811 = 43859717) B43859717
theorem B2107975 : Blo 1873638 2107975 := bstep (se 1 (by rfl) ⟨1580981, by rfl⟩ : syracuseStep 2107975 = 3161963) B3161963
theorem B2812487 : Blo 1873638 2812487 := bstep (se 1 (by rfl) ⟨2109365, by rfl⟩ : syracuseStep 2812487 = 4218731) B4218731
theorem B2812523 : Blo 1873638 2812523 := bstep (se 1 (by rfl) ⟨2109392, by rfl⟩ : syracuseStep 2812523 = 4218785) B4218785
theorem B4745911 : Blo 1873638 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B10136285 : Blo 1873638 10136285 := bstep (se 3 (by rfl) ⟨1900553, by rfl⟩ : syracuseStep 10136285 = 3801107) B3801107
theorem B2566891 : Blo 1873638 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B6007571 : Blo 1873638 6007571 := bstep (se 1 (by rfl) ⟨4505678, by rfl⟩ : syracuseStep 6007571 = 9011357) B9011357
theorem B2812751 : Blo 1873638 2812751 := bstep (se 1 (by rfl) ⟨2109563, by rfl⟩ : syracuseStep 2812751 = 4219127) B4219127
theorem B3165007 : Blo 1873638 3165007 := bstep (se 1 (by rfl) ⟨2373755, by rfl⟩ : syracuseStep 3165007 = 4747511) B4747511
theorem B4746215 : Blo 1873638 4746215 := bstep (se 1 (by rfl) ⟨3559661, by rfl⟩ : syracuseStep 4746215 = 7119323) B7119323
theorem B9006203 : Blo 1873638 9006203 := bstep (se 1 (by rfl) ⟨6754652, by rfl⟩ : syracuseStep 9006203 = 13509305) B13509305
theorem B2813147 : Blo 1873638 2813147 := bstep (se 1 (by rfl) ⟨2109860, by rfl⟩ : syracuseStep 2813147 = 4219721) B4219721
theorem B32017679 : Blo 1873638 32017679 := bstep (se 1 (by rfl) ⟨24013259, by rfl⟩ : syracuseStep 32017679 = 48026519) B48026519
theorem B2002267 : Blo 1873638 2002267 := bstep (se 1 (by rfl) ⟨1501700, by rfl⟩ : syracuseStep 2002267 = 3003401) B3003401
theorem B5336417 : Blo 1873638 5336417 := bstep (se 2 (by rfl) ⟨2001156, by rfl⟩ : syracuseStep 5336417 = 4002313) B4002313
theorem B2813321 : Blo 1873638 2813321 := bstep (se 2 (by rfl) ⟨1054995, by rfl⟩ : syracuseStep 2813321 = 2109991) B2109991
theorem B2108839 : Blo 1873638 2108839 := bstep (se 1 (by rfl) ⟨1581629, by rfl⟩ : syracuseStep 2108839 = 3163259) B3163259
theorem B13512365 : Blo 1873638 13512365 := bstep (se 3 (by rfl) ⟨2533568, by rfl⟩ : syracuseStep 13512365 = 5067137) B5067137
theorem B6328043 : Blo 1873638 6328043 := bstep (se 1 (by rfl) ⟨4746032, by rfl⟩ : syracuseStep 6328043 = 9492065) B9492065
theorem B10678027 : Blo 1873638 10678027 := bstep (se 1 (by rfl) ⟨8008520, by rfl⟩ : syracuseStep 10678027 = 16017041) B16017041
theorem B5336873 : Blo 1873638 5336873 := bstep (se 2 (by rfl) ⟨2001327, by rfl⟩ : syracuseStep 5336873 = 4002655) B4002655
theorem B8007497 : Blo 1873638 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B9490283 : Blo 1873638 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B8007599 : Blo 1873638 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B19247057 : Blo 1873638 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B2109415 : Blo 1873638 2109415 := bstep (se 1 (by rfl) ⟨1582061, by rfl⟩ : syracuseStep 2109415 = 3164123) B3164123
theorem B6410249 : Blo 1873638 6410249 := bstep (se 2 (by rfl) ⟨2403843, by rfl⟩ : syracuseStep 6410249 = 4807687) B4807687
theorem B4747369 : Blo 1873638 4747369 := bstep (se 2 (by rfl) ⟨1780263, by rfl⟩ : syracuseStep 4747369 = 3560527) B3560527
theorem B17109251 : Blo 1873638 17109251 := bstep (se 1 (by rfl) ⟨12831938, by rfl⟩ : syracuseStep 17109251 = 25663877) B25663877
theorem B16020017 : Blo 1873638 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B7115435 : Blo 1873638 7115435 := bstep (se 1 (by rfl) ⟨5336576, by rfl⟩ : syracuseStep 7115435 = 10673153) B10673153
theorem B6329015 : Blo 1873638 6329015 := bstep (se 1 (by rfl) ⟨4746761, by rfl⟩ : syracuseStep 6329015 = 9493523) B9493523
theorem B10130123 : Blo 1873638 10130123 := bstep (se 1 (by rfl) ⟨7597592, by rfl⟩ : syracuseStep 10130123 = 15195185) B15195185
theorem B4215707 : Blo 1873638 4215707 := bstep (se 1 (by rfl) ⟨3161780, by rfl⟩ : syracuseStep 4215707 = 6323561) B6323561
theorem B9008185 : Blo 1873638 9008185 := bstep (se 2 (by rfl) ⟨3378069, by rfl⟩ : syracuseStep 9008185 = 6756139) B6756139
theorem B4215905 : Blo 1873638 4215905 := bstep (se 2 (by rfl) ⟨1580964, by rfl⟩ : syracuseStep 4215905 = 3161929) B3161929
theorem B292287629 : Blo 1873638 292287629 := bstep (se 3 (by rfl) ⟨54803930, by rfl⟩ : syracuseStep 292287629 = 109607861) B109607861
theorem B10130579 : Blo 1873638 10130579 := bstep (se 1 (by rfl) ⟨7597934, by rfl⟩ : syracuseStep 10130579 = 15195869) B15195869
theorem B4216103 : Blo 1873638 4216103 := bstep (se 1 (by rfl) ⟨3162077, by rfl⟩ : syracuseStep 4216103 = 6324155) B6324155
theorem B34207109 : Blo 1873638 34207109 := bstep (se 4 (by rfl) ⟨3206916, by rfl⟩ : syracuseStep 34207109 = 6413833) B6413833
theorem B18265637 : Blo 1873638 18265637 := bstep (se 4 (by rfl) ⟨1712403, by rfl⟩ : syracuseStep 18265637 = 3424807) B3424807
theorem B8009273 : Blo 1873638 8009273 := bstep (se 2 (by rfl) ⟨3003477, by rfl⟩ : syracuseStep 8009273 = 6006955) B6006955
theorem B4216481 : Blo 1873638 4216481 := bstep (se 2 (by rfl) ⟨1581180, by rfl⟩ : syracuseStep 4216481 = 3162361) B3162361
theorem B2373295 : Blo 1873638 2373295 := bstep (se 1 (by rfl) ⟨1779971, by rfl⟩ : syracuseStep 2373295 = 3559943) B3559943
theorem B5068585 : Blo 1873638 5068585 := bstep (se 2 (by rfl) ⟨1900719, by rfl⟩ : syracuseStep 5068585 = 3801439) B3801439
theorem B1873711 : Blo 1873638 1873711 := bstep (se 1 (by rfl) ⟨1405283, by rfl⟩ : syracuseStep 1873711 = 2810567) B2810567
theorem B12007223 : Blo 1873638 12007223 := bstep (se 1 (by rfl) ⟨9005417, by rfl⟩ : syracuseStep 12007223 = 18010835) B18010835
theorem B19232599 : Blo 1873638 19232599 := bstep (se 1 (by rfl) ⟨14424449, by rfl⟩ : syracuseStep 19232599 = 28848899) B28848899
theorem B7599959 : Blo 1873638 7599959 := bstep (se 1 (by rfl) ⟨5699969, by rfl⟩ : syracuseStep 7599959 = 11399939) B11399939
theorem B1873819 : Blo 1873638 1873819 := bstep (se 1 (by rfl) ⟨1405364, by rfl⟩ : syracuseStep 1873819 = 2810729) B2810729
theorem B1873871 : Blo 1873638 1873871 := bstep (se 1 (by rfl) ⟨1405403, by rfl⟩ : syracuseStep 1873871 = 2810807) B2810807
theorem B1873895 : Blo 1873638 1873895 := bstep (se 1 (by rfl) ⟨1405421, by rfl⟩ : syracuseStep 1873895 = 2810843) B2810843
theorem B4216841 : Blo 1873638 4216841 := bstep (se 2 (by rfl) ⟨1581315, by rfl⟩ : syracuseStep 4216841 = 3162631) B3162631
theorem B12171545 : Blo 1873638 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B4503833 : Blo 1873638 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B1874207 : Blo 1873638 1874207 := bstep (se 1 (by rfl) ⟨1405655, by rfl⟩ : syracuseStep 1874207 = 2811311) B2811311
theorem B1874267 : Blo 1873638 1874267 := bstep (se 1 (by rfl) ⟨1405700, by rfl⟩ : syracuseStep 1874267 = 2811401) B2811401
theorem B1874287 : Blo 1873638 1874287 := bstep (se 1 (by rfl) ⟨1405715, by rfl⟩ : syracuseStep 1874287 = 2811431) B2811431
theorem B4217255 : Blo 1873638 4217255 := bstep (se 1 (by rfl) ⟨3162941, by rfl⟩ : syracuseStep 4217255 = 6325883) B6325883
theorem B1874343 : Blo 1873638 1874343 := bstep (se 1 (by rfl) ⟨1405757, by rfl⟩ : syracuseStep 1874343 = 2811515) B2811515
theorem B1874427 : Blo 1873638 1874427 := bstep (se 1 (by rfl) ⟨1405820, by rfl⟩ : syracuseStep 1874427 = 2811641) B2811641
theorem B4217363 : Blo 1873638 4217363 := bstep (se 1 (by rfl) ⟨3163022, by rfl⟩ : syracuseStep 4217363 = 6326045) B6326045
theorem B266951189 : Blo 1873638 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B1874495 : Blo 1873638 1874495 := bstep (se 1 (by rfl) ⟨1405871, by rfl⟩ : syracuseStep 1874495 = 2811743) B2811743
theorem B1874503 : Blo 1873638 1874503 := bstep (se 1 (by rfl) ⟨1405877, by rfl⟩ : syracuseStep 1874503 = 2811755) B2811755
theorem B4217417 : Blo 1873638 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B9615995 : Blo 1873638 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B9624203 : Blo 1873638 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B1874655 : Blo 1873638 1874655 := bstep (se 1 (by rfl) ⟨1405991, by rfl⟩ : syracuseStep 1874655 = 2811983) B2811983
theorem B2669279 : Blo 1873638 2669279 := bstep (se 1 (by rfl) ⟨2001959, by rfl⟩ : syracuseStep 2669279 = 4003919) B4003919
theorem B14236397 : Blo 1873638 14236397 := bstep (se 3 (by rfl) ⟨2669324, by rfl⟩ : syracuseStep 14236397 = 5338649) B5338649
theorem B32480003 : Blo 1873638 32480003 := bstep (se 1 (by rfl) ⟨24360002, by rfl⟩ : syracuseStep 32480003 = 48720005) B48720005
theorem B1874735 : Blo 1873638 1874735 := bstep (se 1 (by rfl) ⟨1406051, by rfl⟩ : syracuseStep 1874735 = 2812103) B2812103
theorem B1874843 : Blo 1873638 1874843 := bstep (se 1 (by rfl) ⟨1406132, by rfl⟩ : syracuseStep 1874843 = 2812265) B2812265
theorem B18013103 : Blo 1873638 18013103 := bstep (se 1 (by rfl) ⟨13509827, by rfl⟩ : syracuseStep 18013103 = 27019655) B27019655
theorem B1874895 : Blo 1873638 1874895 := bstep (se 1 (by rfl) ⟨1406171, by rfl⟩ : syracuseStep 1874895 = 2812343) B2812343
theorem B4217831 : Blo 1873638 4217831 := bstep (se 1 (by rfl) ⟨3163373, by rfl⟩ : syracuseStep 4217831 = 6326747) B6326747
theorem B1874919 : Blo 1873638 1874919 := bstep (se 1 (by rfl) ⟨1406189, by rfl⟩ : syracuseStep 1874919 = 2812379) B2812379
theorem B13515763 : Blo 1873638 13515763 := bstep (se 1 (by rfl) ⟨10136822, by rfl⟩ : syracuseStep 13515763 = 20273645) B20273645
theorem B20266033 : Blo 1873638 20266033 := bstep (se 2 (by rfl) ⟨7599762, by rfl⟩ : syracuseStep 20266033 = 15199525) B15199525
theorem B13171979 : Blo 1873638 13171979 := bstep (se 1 (by rfl) ⟨9878984, by rfl⟩ : syracuseStep 13171979 = 19757969) B19757969
theorem B1875231 : Blo 1873638 1875231 := bstep (se 1 (by rfl) ⟨1406423, by rfl⟩ : syracuseStep 1875231 = 2812847) B2812847
theorem B4504871 : Blo 1873638 4504871 := bstep (se 1 (by rfl) ⟨3378653, by rfl⟩ : syracuseStep 4504871 = 6757307) B6757307
theorem B1875291 : Blo 1873638 1875291 := bstep (se 1 (by rfl) ⟨1406468, by rfl⟩ : syracuseStep 1875291 = 2812937) B2812937
theorem B4218209 : Blo 1873638 4218209 := bstep (se 2 (by rfl) ⟨1581828, by rfl⟩ : syracuseStep 4218209 = 3163657) B3163657
theorem B4005217 : Blo 1873638 4005217 := bstep (se 2 (by rfl) ⟨1501956, by rfl⟩ : syracuseStep 4005217 = 3003913) B3003913
theorem B1875311 : Blo 1873638 1875311 := bstep (se 1 (by rfl) ⟨1406483, by rfl⟩ : syracuseStep 1875311 = 2812967) B2812967
theorem B22797733 : Blo 1873638 22797733 := bstep (se 4 (by rfl) ⟨2137287, by rfl⟩ : syracuseStep 22797733 = 4274575) B4274575
theorem B1875367 : Blo 1873638 1875367 := bstep (se 1 (by rfl) ⟨1406525, by rfl⟩ : syracuseStep 1875367 = 2813051) B2813051
theorem B4218299 : Blo 1873638 4218299 := bstep (se 1 (by rfl) ⟨3163724, by rfl⟩ : syracuseStep 4218299 = 6327449) B6327449
theorem B9494009 : Blo 1873638 9494009 := bstep (se 2 (by rfl) ⟨3560253, by rfl⟩ : syracuseStep 9494009 = 7120507) B7120507
theorem B1875451 : Blo 1873638 1875451 := bstep (se 1 (by rfl) ⟨1406588, by rfl⟩ : syracuseStep 1875451 = 2813177) B2813177
theorem B7118351 : Blo 1873638 7118351 := bstep (se 1 (by rfl) ⟨5338763, by rfl⟩ : syracuseStep 7118351 = 10677527) B10677527
theorem B9010703 : Blo 1873638 9010703 := bstep (se 1 (by rfl) ⟨6758027, by rfl⟩ : syracuseStep 9010703 = 13516055) B13516055
theorem B16023055 : Blo 1873638 16023055 := bstep (se 1 (by rfl) ⟨12017291, by rfl⟩ : syracuseStep 16023055 = 24034583) B24034583
theorem B4218425 : Blo 1873638 4218425 := bstep (se 2 (by rfl) ⟨1581909, by rfl⟩ : syracuseStep 4218425 = 3163819) B3163819
theorem B1875519 : Blo 1873638 1875519 := bstep (se 1 (by rfl) ⟨1406639, by rfl⟩ : syracuseStep 1875519 = 2813279) B2813279
theorem B1875527 : Blo 1873638 1875527 := bstep (se 1 (by rfl) ⟨1406645, by rfl⟩ : syracuseStep 1875527 = 2813291) B2813291
theorem B6757997 : Blo 1873638 6757997 := bstep (se 3 (by rfl) ⟨1267124, by rfl⟩ : syracuseStep 6757997 = 2534249) B2534249
theorem B14229107 : Blo 1873638 14229107 := bstep (se 1 (by rfl) ⟨10671830, by rfl⟩ : syracuseStep 14229107 = 21343661) B21343661
theorem B4505323 : Blo 1873638 4505323 := bstep (se 1 (by rfl) ⟨3378992, by rfl⟩ : syracuseStep 4505323 = 6757985) B6757985
theorem B10673927 : Blo 1873638 10673927 := bstep (se 1 (by rfl) ⟨8005445, by rfl⟩ : syracuseStep 10673927 = 16010891) B16010891
theorem B9494333 : Blo 1873638 9494333 := bstep (se 3 (by rfl) ⟨1780187, by rfl⟩ : syracuseStep 9494333 = 3560375) B3560375
theorem B10682219 : Blo 1873638 10682219 := bstep (se 1 (by rfl) ⟨8011664, by rfl⟩ : syracuseStep 10682219 = 16023329) B16023329
theorem B8011649 : Blo 1873638 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B6004637 : Blo 1873638 6004637 := bstep (se 3 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 6004637 = 2251739) B2251739
theorem B16015265 : Blo 1873638 16015265 := bstep (se 2 (by rfl) ⟨6005724, by rfl⟩ : syracuseStep 16015265 = 12011449) B12011449
theorem B81051677 : Blo 1873638 81051677 := bstep (se 3 (by rfl) ⟨15197189, by rfl⟩ : syracuseStep 81051677 = 30394379) B30394379
theorem B6324263 : Blo 1873638 6324263 := bstep (se 1 (by rfl) ⟨4743197, by rfl⟩ : syracuseStep 6324263 = 9486395) B9486395
theorem B18014561 : Blo 1873638 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B4743623 : Blo 1873638 4743623 := bstep (se 1 (by rfl) ⟨3557717, by rfl⟩ : syracuseStep 4743623 = 7115435) B7115435
theorem B4219343 : Blo 1873638 4219343 := bstep (se 1 (by rfl) ⟨3164507, by rfl⟩ : syracuseStep 4219343 = 6329015) B6329015
theorem B24691205 : Blo 1873638 24691205 := bstep (se 4 (by rfl) ⟨2314800, by rfl⟩ : syracuseStep 24691205 = 4629601) B4629601
theorem B3162719 : Blo 1873638 3162719 := bstep (se 1 (by rfl) ⟨2372039, by rfl⟩ : syracuseStep 3162719 = 4744079) B4744079
theorem B2810471 : Blo 1873638 2810471 := bstep (se 1 (by rfl) ⟨2107853, by rfl⟩ : syracuseStep 2810471 = 4215707) B4215707
theorem B9003629 : Blo 1873638 9003629 := bstep (se 3 (by rfl) ⟨1688180, by rfl⟩ : syracuseStep 9003629 = 3376361) B3376361
theorem B6324911 : Blo 1873638 6324911 := bstep (se 1 (by rfl) ⟨4743683, by rfl⟩ : syracuseStep 6324911 = 9487367) B9487367
theorem B9487043 : Blo 1873638 9487043 := bstep (se 1 (by rfl) ⟨7115282, by rfl⟩ : syracuseStep 9487043 = 14230565) B14230565
theorem B2810603 : Blo 1873638 2810603 := bstep (se 1 (by rfl) ⟨2107952, by rfl⟩ : syracuseStep 2810603 = 4215905) B4215905
theorem B2810633 : Blo 1873638 2810633 := bstep (se 2 (by rfl) ⟨1053987, by rfl⟩ : syracuseStep 2810633 = 2107975) B2107975
theorem B2810735 : Blo 1873638 2810735 := bstep (se 1 (by rfl) ⟨2108051, by rfl⟩ : syracuseStep 2810735 = 4216103) B4216103
theorem B6325235 : Blo 1873638 6325235 := bstep (se 1 (by rfl) ⟨4743926, by rfl⟩ : syracuseStep 6325235 = 9487853) B9487853
theorem B4220009 : Blo 1873638 4220009 := bstep (se 2 (by rfl) ⟨1582503, by rfl⟩ : syracuseStep 4220009 = 3165007) B3165007
theorem B2810987 : Blo 1873638 2810987 := bstep (se 1 (by rfl) ⟨2108240, by rfl⟩ : syracuseStep 2810987 = 4216481) B4216481
theorem B8004815 : Blo 1873638 8004815 := bstep (se 1 (by rfl) ⟨6003611, by rfl⟩ : syracuseStep 8004815 = 12007223) B12007223
theorem B9012491 : Blo 1873638 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B2811227 : Blo 1873638 2811227 := bstep (se 1 (by rfl) ⟨2108420, by rfl⟩ : syracuseStep 2811227 = 4216841) B4216841
theorem B12010913 : Blo 1873638 12010913 := bstep (se 2 (by rfl) ⟨4504092, by rfl⟩ : syracuseStep 12010913 = 9008185) B9008185
theorem B6325775 : Blo 1873638 6325775 := bstep (se 1 (by rfl) ⟨4744331, by rfl⟩ : syracuseStep 6325775 = 9488663) B9488663
theorem B2811503 : Blo 1873638 2811503 := bstep (se 1 (by rfl) ⟨2108627, by rfl⟩ : syracuseStep 2811503 = 4217255) B4217255
theorem B2811575 : Blo 1873638 2811575 := bstep (se 1 (by rfl) ⟨2108681, by rfl⟩ : syracuseStep 2811575 = 4217363) B4217363
theorem B48039641 : Blo 1873638 48039641 := bstep (se 2 (by rfl) ⟨18014865, by rfl⟩ : syracuseStep 48039641 = 36029731) B36029731
theorem B2811611 : Blo 1873638 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B6416135 : Blo 1873638 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B21653335 : Blo 1873638 21653335 := bstep (se 1 (by rfl) ⟨16240001, by rfl⟩ : syracuseStep 21653335 = 32480003) B32480003
theorem B2811785 : Blo 1873638 2811785 := bstep (se 2 (by rfl) ⟨1054419, by rfl⟩ : syracuseStep 2811785 = 2108839) B2108839
theorem B2811887 : Blo 1873638 2811887 := bstep (se 1 (by rfl) ⟨2108915, by rfl⟩ : syracuseStep 2811887 = 4217831) B4217831
theorem B3164143 : Blo 1873638 3164143 := bstep (se 1 (by rfl) ⟨2373107, by rfl⟩ : syracuseStep 3164143 = 4746215) B4746215
theorem B3164393 : Blo 1873638 3164393 := bstep (se 2 (by rfl) ⟨1186647, by rfl⟩ : syracuseStep 3164393 = 2373295) B2373295
theorem B3557611 : Blo 1873638 3557611 := bstep (se 1 (by rfl) ⟨2668208, by rfl⟩ : syracuseStep 3557611 = 5336417) B5336417
theorem B2812139 : Blo 1873638 2812139 := bstep (se 1 (by rfl) ⟨2109104, by rfl⟩ : syracuseStep 2812139 = 4218209) B4218209
theorem B2812199 : Blo 1873638 2812199 := bstep (se 1 (by rfl) ⟨2109149, by rfl⟩ : syracuseStep 2812199 = 4218299) B4218299
theorem B6326585 : Blo 1873638 6326585 := bstep (se 2 (by rfl) ⟨2372469, by rfl⟩ : syracuseStep 6326585 = 4744939) B4744939
theorem B6007097 : Blo 1873638 6007097 := bstep (se 2 (by rfl) ⟨2252661, by rfl⟩ : syracuseStep 6007097 = 4505323) B4505323
theorem B4745567 : Blo 1873638 4745567 := bstep (se 1 (by rfl) ⟨3559175, by rfl⟩ : syracuseStep 4745567 = 7118351) B7118351
theorem B6007135 : Blo 1873638 6007135 := bstep (se 1 (by rfl) ⟨4505351, by rfl⟩ : syracuseStep 6007135 = 9010703) B9010703
theorem B2812283 : Blo 1873638 2812283 := bstep (se 1 (by rfl) ⟨2109212, by rfl⟩ : syracuseStep 2812283 = 4218425) B4218425
theorem B25643465 : Blo 1873638 25643465 := bstep (se 2 (by rfl) ⟨9616299, by rfl⟩ : syracuseStep 25643465 = 19232599) B19232599
theorem B3557915 : Blo 1873638 3557915 := bstep (se 1 (by rfl) ⟨2668436, by rfl⟩ : syracuseStep 3557915 = 5336873) B5336873
theorem B6326855 : Blo 1873638 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B7121479 : Blo 1873638 7121479 := bstep (se 1 (by rfl) ⟨5341109, by rfl⟩ : syracuseStep 7121479 = 10682219) B10682219
theorem B10676843 : Blo 1873638 10676843 := bstep (se 1 (by rfl) ⟨8007632, by rfl⟩ : syracuseStep 10676843 = 16015265) B16015265
theorem B2812553 : Blo 1873638 2812553 := bstep (se 2 (by rfl) ⟨1054707, by rfl⟩ : syracuseStep 2812553 = 2109415) B2109415
theorem B12831371 : Blo 1873638 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B2812727 : Blo 1873638 2812727 := bstep (se 1 (by rfl) ⟨2109545, by rfl⟩ : syracuseStep 2812727 = 4219091) B4219091
theorem B11406167 : Blo 1873638 11406167 := bstep (se 1 (by rfl) ⟨8554625, by rfl⟩ : syracuseStep 11406167 = 17109251) B17109251
theorem B2812763 : Blo 1873638 2812763 := bstep (se 1 (by rfl) ⟨2109572, by rfl⟩ : syracuseStep 2812763 = 4219145) B4219145
theorem B20540395 : Blo 1873638 20540395 := bstep (se 1 (by rfl) ⟨15405296, by rfl⟩ : syracuseStep 20540395 = 30810593) B30810593
theorem B2812907 : Blo 1873638 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B6753415 : Blo 1873638 6753415 := bstep (se 1 (by rfl) ⟨5065061, by rfl⟩ : syracuseStep 6753415 = 10130123) B10130123
theorem B2813111 : Blo 1873638 2813111 := bstep (se 1 (by rfl) ⟨2109833, by rfl⟩ : syracuseStep 2813111 = 4219667) B4219667
theorem B2813351 : Blo 1873638 2813351 := bstep (se 1 (by rfl) ⟨2110013, by rfl⟩ : syracuseStep 2813351 = 4220027) B4220027
theorem B194858419 : Blo 1873638 194858419 := bstep (se 1 (by rfl) ⟨146143814, by rfl⟩ : syracuseStep 194858419 = 292287629) B292287629
theorem B6753719 : Blo 1873638 6753719 := bstep (se 1 (by rfl) ⟨5065289, by rfl⟩ : syracuseStep 6753719 = 10130579) B10130579
theorem B2813435 : Blo 1873638 2813435 := bstep (se 1 (by rfl) ⟨2110076, by rfl⟩ : syracuseStep 2813435 = 4220153) B4220153
theorem B6327881 : Blo 1873638 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B2109019 : Blo 1873638 2109019 := bstep (se 1 (by rfl) ⟨1581764, by rfl⟩ : syracuseStep 2109019 = 3163529) B3163529
theorem B22851233 : Blo 1873638 22851233 := bstep (se 2 (by rfl) ⟨8569212, by rfl⟩ : syracuseStep 22851233 = 17138425) B17138425
theorem B12177091 : Blo 1873638 12177091 := bstep (se 1 (by rfl) ⟨9132818, by rfl⟩ : syracuseStep 12177091 = 18265637) B18265637
theorem B2109307 : Blo 1873638 2109307 := bstep (se 1 (by rfl) ⟨1581980, by rfl⟩ : syracuseStep 2109307 = 3163961) B3163961
theorem B5066639 : Blo 1873638 5066639 := bstep (se 1 (by rfl) ⟨3799979, by rfl⟩ : syracuseStep 5066639 = 7599959) B7599959
theorem B27021377 : Blo 1873638 27021377 := bstep (se 2 (by rfl) ⟨10133016, by rfl⟩ : syracuseStep 27021377 = 20266033) B20266033
theorem B8114363 : Blo 1873638 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B3002555 : Blo 1873638 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B19493207 : Blo 1873638 19493207 := bstep (se 1 (by rfl) ⟨14619905, by rfl⟩ : syracuseStep 19493207 = 29239811) B29239811
theorem B177967459 : Blo 1873638 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B6410663 : Blo 1873638 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B9490931 : Blo 1873638 9490931 := bstep (se 1 (by rfl) ⟨7118198, by rfl⟩ : syracuseStep 9490931 = 14236397) B14236397
theorem B21361157 : Blo 1873638 21361157 := bstep (se 4 (by rfl) ⟨2002608, by rfl⟩ : syracuseStep 21361157 = 4005217) B4005217
theorem B30396977 : Blo 1873638 30396977 := bstep (se 2 (by rfl) ⟨11398866, by rfl⟩ : syracuseStep 30396977 = 22797733) B22797733
theorem B21345119 : Blo 1873638 21345119 := bstep (se 1 (by rfl) ⟨16008839, by rfl⟩ : syracuseStep 21345119 = 32017679) B32017679
theorem B3003247 : Blo 1873638 3003247 := bstep (se 1 (by rfl) ⟨2252435, by rfl⟩ : syracuseStep 3003247 = 4504871) B4504871
theorem B6329339 : Blo 1873638 6329339 := bstep (se 1 (by rfl) ⟨4747004, by rfl⟩ : syracuseStep 6329339 = 9494009) B9494009
theorem B9008243 : Blo 1873638 9008243 := bstep (se 1 (by rfl) ⟨6756182, by rfl⟩ : syracuseStep 9008243 = 13512365) B13512365
theorem B7115951 : Blo 1873638 7115951 := bstep (se 1 (by rfl) ⟨5336963, by rfl⟩ : syracuseStep 7115951 = 10673927) B10673927
theorem B6329555 : Blo 1873638 6329555 := bstep (se 1 (by rfl) ⟨4747166, by rfl⟩ : syracuseStep 6329555 = 9494333) B9494333
theorem B5338331 : Blo 1873638 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B4003091 : Blo 1873638 4003091 := bstep (se 1 (by rfl) ⟨3002318, by rfl⟩ : syracuseStep 4003091 = 6004637) B6004637
theorem B5338399 : Blo 1873638 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B4273499 : Blo 1873638 4273499 := bstep (se 1 (by rfl) ⟨3205124, by rfl⟩ : syracuseStep 4273499 = 6410249) B6410249
theorem B21353867 : Blo 1873638 21353867 := bstep (se 1 (by rfl) ⟨16015400, by rfl⟩ : syracuseStep 21353867 = 32030801) B32030801
theorem B6329825 : Blo 1873638 6329825 := bstep (se 2 (by rfl) ⟨2373684, by rfl⟩ : syracuseStep 6329825 = 4747369) B4747369
theorem B4216391 : Blo 1873638 4216391 := bstep (se 1 (by rfl) ⟨3162293, by rfl⟩ : syracuseStep 4216391 = 6324587) B6324587
theorem B10680011 : Blo 1873638 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B1873659 : Blo 1873638 1873659 := bstep (se 1 (by rfl) ⟨1405244, by rfl⟩ : syracuseStep 1873659 = 2810489) B2810489
theorem B4216571 : Blo 1873638 4216571 := bstep (se 1 (by rfl) ⟨3162428, by rfl⟩ : syracuseStep 4216571 = 6324857) B6324857
theorem B1873695 : Blo 1873638 1873695 := bstep (se 1 (by rfl) ⟨1405271, by rfl⟩ : syracuseStep 1873695 = 2810543) B2810543
theorem B1873727 : Blo 1873638 1873727 := bstep (se 1 (by rfl) ⟨1405295, by rfl⟩ : syracuseStep 1873727 = 2810591) B2810591
theorem B1873903 : Blo 1873638 1873903 := bstep (se 1 (by rfl) ⟨1405427, by rfl⟩ : syracuseStep 1873903 = 2810855) B2810855
theorem B1874075 : Blo 1873638 1874075 := bstep (se 1 (by rfl) ⟨1405556, by rfl⟩ : syracuseStep 1874075 = 2811113) B2811113
theorem B1874111 : Blo 1873638 1874111 := bstep (se 1 (by rfl) ⟨1405583, by rfl⟩ : syracuseStep 1874111 = 2811167) B2811167
theorem B22804739 : Blo 1873638 22804739 := bstep (se 1 (by rfl) ⟨17103554, by rfl⟩ : syracuseStep 22804739 = 34207109) B34207109
theorem B4217129 : Blo 1873638 4217129 := bstep (se 2 (by rfl) ⟨1581423, by rfl⟩ : syracuseStep 4217129 = 3162847) B3162847
theorem B1874223 : Blo 1873638 1874223 := bstep (se 1 (by rfl) ⟨1405667, by rfl⟩ : syracuseStep 1874223 = 2811335) B2811335
theorem B3422521 : Blo 1873638 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B5339515 : Blo 1873638 5339515 := bstep (se 1 (by rfl) ⟨4004636, by rfl⟩ : syracuseStep 5339515 = 8009273) B8009273
theorem B1874459 : Blo 1873638 1874459 := bstep (se 1 (by rfl) ⟨1405844, by rfl⟩ : syracuseStep 1874459 = 2811689) B2811689
theorem B1874463 : Blo 1873638 1874463 := bstep (se 1 (by rfl) ⟨1405847, by rfl⟩ : syracuseStep 1874463 = 2811695) B2811695
theorem B5069449 : Blo 1873638 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B18021017 : Blo 1873638 18021017 := bstep (se 2 (by rfl) ⟨6757881, by rfl⟩ : syracuseStep 18021017 = 13515763) B13515763
theorem B1874779 : Blo 1873638 1874779 := bstep (se 1 (by rfl) ⟨1406084, by rfl⟩ : syracuseStep 1874779 = 2812169) B2812169
theorem B4217705 : Blo 1873638 4217705 := bstep (se 2 (by rfl) ⟨1581639, by rfl⟩ : syracuseStep 4217705 = 3163279) B3163279
theorem B4217759 : Blo 1873638 4217759 := bstep (se 1 (by rfl) ⟨3163319, by rfl⟩ : syracuseStep 4217759 = 6326639) B6326639
theorem B1874847 : Blo 1873638 1874847 := bstep (se 1 (by rfl) ⟨1406135, by rfl⟩ : syracuseStep 1874847 = 2812271) B2812271
theorem B18021325 : Blo 1873638 18021325 := bstep (se 3 (by rfl) ⟨3378998, by rfl⟩ : syracuseStep 18021325 = 6757997) B6757997
theorem B1874991 : Blo 1873638 1874991 := bstep (se 1 (by rfl) ⟨1406243, by rfl⟩ : syracuseStep 1874991 = 2812487) B2812487
theorem B1875015 : Blo 1873638 1875015 := bstep (se 1 (by rfl) ⟨1406261, by rfl⟩ : syracuseStep 1875015 = 2812523) B2812523
theorem B2669689 : Blo 1873638 2669689 := bstep (se 2 (by rfl) ⟨1001133, by rfl⟩ : syracuseStep 2669689 = 2002267) B2002267
theorem B6757523 : Blo 1873638 6757523 := bstep (se 1 (by rfl) ⟨5068142, by rfl⟩ : syracuseStep 6757523 = 10136285) B10136285
theorem B4005047 : Blo 1873638 4005047 := bstep (se 1 (by rfl) ⟨3003785, by rfl⟩ : syracuseStep 4005047 = 6007571) B6007571
theorem B1875167 : Blo 1873638 1875167 := bstep (se 1 (by rfl) ⟨1406375, by rfl⟩ : syracuseStep 1875167 = 2812751) B2812751
theorem B7118077 : Blo 1873638 7118077 := bstep (se 3 (by rfl) ⟨1334639, by rfl⟩ : syracuseStep 7118077 = 2669279) B2669279
theorem B12008735 : Blo 1873638 12008735 := bstep (se 1 (by rfl) ⟨9006551, by rfl⟩ : syracuseStep 12008735 = 18013103) B18013103
theorem B21364073 : Blo 1873638 21364073 := bstep (se 2 (by rfl) ⟨8011527, by rfl⟩ : syracuseStep 21364073 = 16023055) B16023055
theorem B6004135 : Blo 1873638 6004135 := bstep (se 1 (by rfl) ⟨4503101, by rfl⟩ : syracuseStep 6004135 = 9006203) B9006203
theorem B1875431 : Blo 1873638 1875431 := bstep (se 1 (by rfl) ⟨1406573, by rfl⟩ : syracuseStep 1875431 = 2813147) B2813147
theorem B8781319 : Blo 1873638 8781319 := bstep (se 1 (by rfl) ⟨6585989, by rfl⟩ : syracuseStep 8781319 = 13171979) B13171979
theorem B1875547 : Blo 1873638 1875547 := bstep (se 1 (by rfl) ⟨1406660, by rfl⟩ : syracuseStep 1875547 = 2813321) B2813321
theorem B14237369 : Blo 1873638 14237369 := bstep (se 2 (by rfl) ⟨5339013, by rfl⟩ : syracuseStep 14237369 = 10678027) B10678027
theorem B6758113 : Blo 1873638 6758113 := bstep (se 2 (by rfl) ⟨2534292, by rfl⟩ : syracuseStep 6758113 = 5068585) B5068585
theorem B9486071 : Blo 1873638 9486071 := bstep (se 1 (by rfl) ⟨7114553, by rfl⟩ : syracuseStep 9486071 = 14229107) B14229107
theorem B4218695 : Blo 1873638 4218695 := bstep (se 1 (by rfl) ⟨3164021, by rfl⟩ : syracuseStep 4218695 = 6328043) B6328043
theorem B5341099 : Blo 1873638 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B54034451 : Blo 1873638 54034451 := bstep (se 1 (by rfl) ⟨40525838, by rfl⟩ : syracuseStep 54034451 = 81051677) B81051677
theorem B18014251 : Blo 1873638 18014251 := bstep (se 1 (by rfl) ⟨13510688, by rfl⟩ : syracuseStep 18014251 = 27021377) B27021377
theorem B12009707 : Blo 1873638 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B3162415 : Blo 1873638 3162415 := bstep (se 1 (by rfl) ⟨2371811, by rfl⟩ : syracuseStep 3162415 = 4743623) B4743623
theorem B4743481 : Blo 1873638 4743481 := bstep (se 2 (by rfl) ⟨1778805, by rfl⟩ : syracuseStep 4743481 = 3557611) B3557611
theorem B4563361 : Blo 1873638 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B6324695 : Blo 1873638 6324695 := bstep (se 1 (by rfl) ⟨4743521, by rfl⟩ : syracuseStep 6324695 = 9487043) B9487043
theorem B237289945 : Blo 1873638 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B7119353 : Blo 1873638 7119353 := bstep (se 2 (by rfl) ⟨2669757, by rfl⟩ : syracuseStep 7119353 = 5339515) B5339515
theorem B14230079 : Blo 1873638 14230079 := bstep (se 1 (by rfl) ⟨10672559, by rfl⟩ : syracuseStep 14230079 = 21345119) B21345119
theorem B14238341 : Blo 1873638 14238341 := bstep (se 4 (by rfl) ⟨1334844, by rfl⟩ : syracuseStep 14238341 = 2669689) B2669689
theorem B4219559 : Blo 1873638 4219559 := bstep (se 1 (by rfl) ⟨3164669, by rfl⟩ : syracuseStep 4219559 = 6329339) B6329339
theorem B6005495 : Blo 1873638 6005495 := bstep (se 1 (by rfl) ⟨4504121, by rfl⟩ : syracuseStep 6005495 = 9008243) B9008243
theorem B9495305 : Blo 1873638 9495305 := bstep (se 2 (by rfl) ⟨3560739, by rfl⟩ : syracuseStep 9495305 = 7121479) B7121479
theorem B4743967 : Blo 1873638 4743967 := bstep (se 1 (by rfl) ⟨3557975, by rfl⟩ : syracuseStep 4743967 = 7115951) B7115951
theorem B4219703 : Blo 1873638 4219703 := bstep (se 1 (by rfl) ⟨3164777, by rfl⟩ : syracuseStep 4219703 = 6329555) B6329555
theorem B11395997 : Blo 1873638 11395997 := bstep (se 3 (by rfl) ⟨2136749, by rfl⟩ : syracuseStep 11395997 = 4273499) B4273499
theorem B4219883 : Blo 1873638 4219883 := bstep (se 1 (by rfl) ⟨3164912, by rfl⟩ : syracuseStep 4219883 = 6329825) B6329825
theorem B2810927 : Blo 1873638 2810927 := bstep (se 1 (by rfl) ⟨2108195, by rfl⟩ : syracuseStep 2810927 = 4216391) B4216391
theorem B7120007 : Blo 1873638 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B2811047 : Blo 1873638 2811047 := bstep (se 1 (by rfl) ⟨2108285, by rfl⟩ : syracuseStep 2811047 = 4216571) B4216571
theorem B4277423 : Blo 1873638 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B24028433 : Blo 1873638 24028433 := bstep (se 2 (by rfl) ⟨9010662, by rfl⟩ : syracuseStep 24028433 = 18021325) B18021325
theorem B27387193 : Blo 1873638 27387193 := bstep (se 2 (by rfl) ⟨10270197, by rfl⟩ : syracuseStep 27387193 = 20540395) B20540395
theorem B9004553 : Blo 1873638 9004553 := bstep (se 2 (by rfl) ⟨3376707, by rfl⟩ : syracuseStep 9004553 = 6753415) B6753415
theorem B2811419 : Blo 1873638 2811419 := bstep (se 1 (by rfl) ⟨2108564, by rfl⟩ : syracuseStep 2811419 = 4217129) B4217129
theorem B3163711 : Blo 1873638 3163711 := bstep (se 1 (by rfl) ⟨2372783, by rfl⟩ : syracuseStep 3163711 = 4745567) B4745567
theorem B8554247 : Blo 1873638 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B115484453 : Blo 1873638 115484453 := bstep (se 4 (by rfl) ⟨10826667, by rfl⟩ : syracuseStep 115484453 = 21653335) B21653335
theorem B7604111 : Blo 1873638 7604111 := bstep (se 1 (by rfl) ⟨5703083, by rfl⟩ : syracuseStep 7604111 = 11406167) B11406167
theorem B259811225 : Blo 1873638 259811225 := bstep (se 2 (by rfl) ⟨97429209, by rfl⟩ : syracuseStep 259811225 = 194858419) B194858419
theorem B2811803 : Blo 1873638 2811803 := bstep (se 1 (by rfl) ⟨2108852, by rfl⟩ : syracuseStep 2811803 = 4217705) B4217705
theorem B2811839 : Blo 1873638 2811839 := bstep (se 1 (by rfl) ⟨2108879, by rfl⟩ : syracuseStep 2811839 = 4217759) B4217759
theorem B11708425 : Blo 1873638 11708425 := bstep (se 2 (by rfl) ⟨4390659, by rfl⟩ : syracuseStep 11708425 = 8781319) B8781319
theorem B2812025 : Blo 1873638 2812025 := bstep (se 2 (by rfl) ⟨1054509, by rfl⟩ : syracuseStep 2812025 = 2109019) B2109019
theorem B8005823 : Blo 1873638 8005823 := bstep (se 1 (by rfl) ⟨6004367, by rfl⟩ : syracuseStep 8005823 = 12008735) B12008735
theorem B2812409 : Blo 1873638 2812409 := bstep (se 2 (by rfl) ⟨1054653, by rfl⟩ : syracuseStep 2812409 = 2109307) B2109307
theorem B2812463 : Blo 1873638 2812463 := bstep (se 1 (by rfl) ⟨2109347, by rfl⟩ : syracuseStep 2812463 = 4218695) B4218695
theorem B7121465 : Blo 1873638 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B3377759 : Blo 1873638 3377759 := bstep (se 1 (by rfl) ⟨2533319, by rfl⟩ : syracuseStep 3377759 = 5066639) B5066639
theorem B5409575 : Blo 1873638 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B12995471 : Blo 1873638 12995471 := bstep (se 1 (by rfl) ⟨9746603, by rfl⟩ : syracuseStep 12995471 = 19493207) B19493207
theorem B2812895 : Blo 1873638 2812895 := bstep (se 1 (by rfl) ⟨2109671, by rfl⟩ : syracuseStep 2812895 = 4219343) B4219343
theorem B6327287 : Blo 1873638 6327287 := bstep (se 1 (by rfl) ⟨4745465, by rfl⟩ : syracuseStep 6327287 = 9490931) B9490931
theorem B16460803 : Blo 1873638 16460803 := bstep (se 1 (by rfl) ⟨12345602, by rfl⟩ : syracuseStep 16460803 = 24691205) B24691205
theorem B14240771 : Blo 1873638 14240771 := bstep (se 1 (by rfl) ⟨10680578, by rfl⟩ : syracuseStep 14240771 = 21361157) B21361157
theorem B2108479 : Blo 1873638 2108479 := bstep (se 1 (by rfl) ⟨1581359, by rfl⟩ : syracuseStep 2108479 = 3162719) B3162719
theorem B8006813 : Blo 1873638 8006813 := bstep (se 3 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 8006813 = 3002555) B3002555
theorem B27037061 : Blo 1873638 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B2813339 : Blo 1873638 2813339 := bstep (se 1 (by rfl) ⟨2110004, by rfl⟩ : syracuseStep 2813339 = 4220009) B4220009
theorem B5336543 : Blo 1873638 5336543 := bstep (se 1 (by rfl) ⟨4002407, by rfl⟩ : syracuseStep 5336543 = 8004815) B8004815
theorem B3558887 : Blo 1873638 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B6008327 : Blo 1873638 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B8007275 : Blo 1873638 8007275 := bstep (se 1 (by rfl) ⟨6005456, by rfl⟩ : syracuseStep 8007275 = 12010913) B12010913
theorem B32026427 : Blo 1873638 32026427 := bstep (se 1 (by rfl) ⟨24019820, by rfl⟩ : syracuseStep 32026427 = 48039641) B48039641
theorem B2109595 : Blo 1873638 2109595 := bstep (se 1 (by rfl) ⟨1582196, by rfl⟩ : syracuseStep 2109595 = 3164393) B3164393
theorem B9490769 : Blo 1873638 9490769 := bstep (se 2 (by rfl) ⟨3559038, by rfl⟩ : syracuseStep 9490769 = 7118077) B7118077
theorem B2371943 : Blo 1873638 2371943 := bstep (se 1 (by rfl) ⟨1778957, by rfl⟩ : syracuseStep 2371943 = 3557915) B3557915
theorem B12014011 : Blo 1873638 12014011 := bstep (se 1 (by rfl) ⟨9010508, by rfl⟩ : syracuseStep 12014011 = 18021017) B18021017
theorem B14242715 : Blo 1873638 14242715 := bstep (se 1 (by rfl) ⟨10682036, by rfl⟩ : syracuseStep 14242715 = 21364073) B21364073
theorem B4502479 : Blo 1873638 4502479 := bstep (se 1 (by rfl) ⟨3376859, by rfl⟩ : syracuseStep 4502479 = 6753719) B6753719
theorem B15234155 : Blo 1873638 15234155 := bstep (se 1 (by rfl) ⟨11425616, by rfl⟩ : syracuseStep 15234155 = 22851233) B22851233
theorem B9491579 : Blo 1873638 9491579 := bstep (se 1 (by rfl) ⟨7118684, by rfl⟩ : syracuseStep 9491579 = 14237369) B14237369
theorem B4216175 : Blo 1873638 4216175 := bstep (se 1 (by rfl) ⟨3162131, by rfl⟩ : syracuseStep 4216175 = 6324263) B6324263
theorem B4273775 : Blo 1873638 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B20264651 : Blo 1873638 20264651 := bstep (se 1 (by rfl) ⟨15198488, by rfl⟩ : syracuseStep 20264651 = 30396977) B30396977
theorem B1873647 : Blo 1873638 1873647 := bstep (se 1 (by rfl) ⟨1405235, by rfl⟩ : syracuseStep 1873647 = 2810471) B2810471
theorem B6002419 : Blo 1873638 6002419 := bstep (se 1 (by rfl) ⟨4501814, by rfl⟩ : syracuseStep 6002419 = 9003629) B9003629
theorem B4216607 : Blo 1873638 4216607 := bstep (se 1 (by rfl) ⟨3162455, by rfl⟩ : syracuseStep 4216607 = 6324911) B6324911
theorem B8009513 : Blo 1873638 8009513 := bstep (se 2 (by rfl) ⟨3003567, by rfl⟩ : syracuseStep 8009513 = 6007135) B6007135
theorem B1873735 : Blo 1873638 1873735 := bstep (se 1 (by rfl) ⟨1405301, by rfl⟩ : syracuseStep 1873735 = 2810603) B2810603
theorem B1873755 : Blo 1873638 1873755 := bstep (se 1 (by rfl) ⟨1405316, by rfl⟩ : syracuseStep 1873755 = 2810633) B2810633
theorem B1873823 : Blo 1873638 1873823 := bstep (se 1 (by rfl) ⟨1405367, by rfl⟩ : syracuseStep 1873823 = 2810735) B2810735
theorem B4216823 : Blo 1873638 4216823 := bstep (se 1 (by rfl) ⟨3162617, by rfl⟩ : syracuseStep 4216823 = 6325235) B6325235
theorem B1873991 : Blo 1873638 1873991 := bstep (se 1 (by rfl) ⟨1405493, by rfl⟩ : syracuseStep 1873991 = 2810987) B2810987
theorem B2668727 : Blo 1873638 2668727 := bstep (se 1 (by rfl) ⟨2001545, by rfl⟩ : syracuseStep 2668727 = 4003091) B4003091
theorem B1874151 : Blo 1873638 1874151 := bstep (se 1 (by rfl) ⟨1405613, by rfl⟩ : syracuseStep 1874151 = 2811227) B2811227
theorem B14235911 : Blo 1873638 14235911 := bstep (se 1 (by rfl) ⟨10676933, by rfl⟩ : syracuseStep 14235911 = 21353867) B21353867
theorem B4217183 : Blo 1873638 4217183 := bstep (se 1 (by rfl) ⟨3162887, by rfl⟩ : syracuseStep 4217183 = 6325775) B6325775
theorem B1874335 : Blo 1873638 1874335 := bstep (se 1 (by rfl) ⟨1405751, by rfl⟩ : syracuseStep 1874335 = 2811503) B2811503
theorem B1874383 : Blo 1873638 1874383 := bstep (se 1 (by rfl) ⟨1405787, by rfl⟩ : syracuseStep 1874383 = 2811575) B2811575
theorem B1874407 : Blo 1873638 1874407 := bstep (se 1 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 1874407 = 2811611) B2811611
theorem B4004329 : Blo 1873638 4004329 := bstep (se 2 (by rfl) ⟨1501623, by rfl⟩ : syracuseStep 4004329 = 3003247) B3003247
theorem B1874523 : Blo 1873638 1874523 := bstep (se 1 (by rfl) ⟨1405892, by rfl⟩ : syracuseStep 1874523 = 2811785) B2811785
theorem B1874591 : Blo 1873638 1874591 := bstep (se 1 (by rfl) ⟨1405943, by rfl⟩ : syracuseStep 1874591 = 2811887) B2811887
theorem B1874759 : Blo 1873638 1874759 := bstep (se 1 (by rfl) ⟨1406069, by rfl⟩ : syracuseStep 1874759 = 2812139) B2812139
theorem B15203159 : Blo 1873638 15203159 := bstep (se 1 (by rfl) ⟨11402369, by rfl⟩ : syracuseStep 15203159 = 22804739) B22804739
theorem B1874799 : Blo 1873638 1874799 := bstep (se 1 (by rfl) ⟨1406099, by rfl⟩ : syracuseStep 1874799 = 2812199) B2812199
theorem B4217723 : Blo 1873638 4217723 := bstep (se 1 (by rfl) ⟨3163292, by rfl⟩ : syracuseStep 4217723 = 6326585) B6326585
theorem B4004731 : Blo 1873638 4004731 := bstep (se 1 (by rfl) ⟨3003548, by rfl⟩ : syracuseStep 4004731 = 6007097) B6007097
theorem B1874855 : Blo 1873638 1874855 := bstep (se 1 (by rfl) ⟨1406141, by rfl⟩ : syracuseStep 1874855 = 2812283) B2812283
theorem B17095643 : Blo 1873638 17095643 := bstep (se 1 (by rfl) ⟨12821732, by rfl⟩ : syracuseStep 17095643 = 25643465) B25643465
theorem B7117865 : Blo 1873638 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B4217903 : Blo 1873638 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B7117895 : Blo 1873638 7117895 := bstep (se 1 (by rfl) ⟨5338421, by rfl⟩ : syracuseStep 7117895 = 10676843) B10676843
theorem B1875035 : Blo 1873638 1875035 := bstep (se 1 (by rfl) ⟨1406276, by rfl⟩ : syracuseStep 1875035 = 2812553) B2812553
theorem B1875151 : Blo 1873638 1875151 := bstep (se 1 (by rfl) ⟨1406363, by rfl⟩ : syracuseStep 1875151 = 2812727) B2812727
theorem B1875175 : Blo 1873638 1875175 := bstep (se 1 (by rfl) ⟨1406381, by rfl⟩ : syracuseStep 1875175 = 2812763) B2812763
theorem B1875271 : Blo 1873638 1875271 := bstep (se 1 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 1875271 = 2812907) B2812907
theorem B4505015 : Blo 1873638 4505015 := bstep (se 1 (by rfl) ⟨3378761, by rfl⟩ : syracuseStep 4505015 = 6757523) B6757523
theorem B2670031 : Blo 1873638 2670031 := bstep (se 1 (by rfl) ⟨2002523, by rfl⟩ : syracuseStep 2670031 = 4005047) B4005047
theorem B1875407 : Blo 1873638 1875407 := bstep (se 1 (by rfl) ⟨1406555, by rfl⟩ : syracuseStep 1875407 = 2813111) B2813111
theorem B32022053 : Blo 1873638 32022053 := bstep (se 4 (by rfl) ⟨3002067, by rfl⟩ : syracuseStep 32022053 = 6004135) B6004135
theorem B16236121 : Blo 1873638 16236121 := bstep (se 2 (by rfl) ⟨6088545, by rfl⟩ : syracuseStep 16236121 = 12177091) B12177091
theorem B1875567 : Blo 1873638 1875567 := bstep (se 1 (by rfl) ⟨1406675, by rfl⟩ : syracuseStep 1875567 = 2813351) B2813351
theorem B9010817 : Blo 1873638 9010817 := bstep (se 2 (by rfl) ⟨3379056, by rfl⟩ : syracuseStep 9010817 = 6758113) B6758113
theorem B1875623 : Blo 1873638 1875623 := bstep (se 1 (by rfl) ⟨1406717, by rfl⟩ : syracuseStep 1875623 = 2813435) B2813435
theorem B4218587 : Blo 1873638 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B6324047 : Blo 1873638 6324047 := bstep (se 1 (by rfl) ⟨4743035, by rfl⟩ : syracuseStep 6324047 = 9486071) B9486071
theorem B4218857 : Blo 1873638 4218857 := bstep (se 2 (by rfl) ⟨1582071, by rfl⟩ : syracuseStep 4218857 = 3164143) B3164143
theorem B24019001 : Blo 1873638 24019001 := bstep (se 2 (by rfl) ⟨9007125, by rfl⟩ : syracuseStep 24019001 = 18014251) B18014251
theorem B9486719 : Blo 1873638 9486719 := bstep (se 1 (by rfl) ⟨7115039, by rfl⟩ : syracuseStep 9486719 = 14230079) B14230079
theorem B6324641 : Blo 1873638 6324641 := bstep (se 2 (by rfl) ⟨2371740, by rfl⟩ : syracuseStep 6324641 = 4743481) B4743481
theorem B9495143 : Blo 1873638 9495143 := bstep (se 1 (by rfl) ⟨7121357, by rfl⟩ : syracuseStep 9495143 = 14242715) B14242715
theorem B2851615 : Blo 1873638 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B2810783 : Blo 1873638 2810783 := bstep (se 1 (by rfl) ⟨2108087, by rfl⟩ : syracuseStep 2810783 = 4216175) B4216175
theorem B6325181 : Blo 1873638 6325181 := bstep (se 3 (by rfl) ⟨1185971, by rfl⟩ : syracuseStep 6325181 = 2371943) B2371943
theorem B6325289 : Blo 1873638 6325289 := bstep (se 2 (by rfl) ⟨2371983, by rfl⟩ : syracuseStep 6325289 = 4743967) B4743967
theorem B13509767 : Blo 1873638 13509767 := bstep (se 1 (by rfl) ⟨10132325, by rfl⟩ : syracuseStep 13509767 = 20264651) B20264651
theorem B5702831 : Blo 1873638 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B2811071 : Blo 1873638 2811071 := bstep (se 1 (by rfl) ⟨2108303, by rfl⟩ : syracuseStep 2811071 = 4216607) B4216607
theorem B76989635 : Blo 1873638 76989635 := bstep (se 1 (by rfl) ⟨57742226, by rfl⟩ : syracuseStep 76989635 = 115484453) B115484453
theorem B2811215 : Blo 1873638 2811215 := bstep (se 1 (by rfl) ⟨2108411, by rfl⟩ : syracuseStep 2811215 = 4216823) B4216823
theorem B2811305 : Blo 1873638 2811305 := bstep (se 2 (by rfl) ⟨1054239, by rfl⟩ : syracuseStep 2811305 = 2108479) B2108479
theorem B2811455 : Blo 1873638 2811455 := bstep (se 1 (by rfl) ⟨2108591, by rfl⟩ : syracuseStep 2811455 = 4217183) B4217183
theorem B3606383 : Blo 1873638 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B10135439 : Blo 1873638 10135439 := bstep (se 1 (by rfl) ⟨7601579, by rfl⟩ : syracuseStep 10135439 = 15203159) B15203159
theorem B2811815 : Blo 1873638 2811815 := bstep (se 1 (by rfl) ⟨2108861, by rfl⟩ : syracuseStep 2811815 = 4217723) B4217723
theorem B11397095 : Blo 1873638 11397095 := bstep (se 1 (by rfl) ⟨8547821, by rfl⟩ : syracuseStep 11397095 = 17095643) B17095643
theorem B4745243 : Blo 1873638 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B2811935 : Blo 1873638 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B4745263 : Blo 1873638 4745263 := bstep (se 1 (by rfl) ⟨3558947, by rfl⟩ : syracuseStep 4745263 = 7117895) B7117895
theorem B18024707 : Blo 1873638 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B3557695 : Blo 1873638 3557695 := bstep (se 1 (by rfl) ⟨2668271, by rfl⟩ : syracuseStep 3557695 = 5336543) B5336543
theorem B6007211 : Blo 1873638 6007211 := bstep (se 1 (by rfl) ⟨4505408, by rfl⟩ : syracuseStep 6007211 = 9010817) B9010817
theorem B2812391 : Blo 1873638 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B21350951 : Blo 1873638 21350951 := bstep (se 1 (by rfl) ⟨16013213, by rfl⟩ : syracuseStep 21350951 = 32026427) B32026427
theorem B2812571 : Blo 1873638 2812571 := bstep (se 1 (by rfl) ⟨2109428, by rfl⟩ : syracuseStep 2812571 = 4218857) B4218857
theorem B36022967 : Blo 1873638 36022967 := bstep (se 1 (by rfl) ⟨27017225, by rfl⟩ : syracuseStep 36022967 = 54034451) B54034451
theorem B8006471 : Blo 1873638 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B2812793 : Blo 1873638 2812793 := bstep (se 2 (by rfl) ⟨1054797, by rfl⟩ : syracuseStep 2812793 = 2109595) B2109595
theorem B6327179 : Blo 1873638 6327179 := bstep (se 1 (by rfl) ⟨4745384, by rfl⟩ : syracuseStep 6327179 = 9490769) B9490769
theorem B4746235 : Blo 1873638 4746235 := bstep (se 1 (by rfl) ⟨3559676, by rfl⟩ : syracuseStep 4746235 = 7119353) B7119353
theorem B2813039 : Blo 1873638 2813039 := bstep (se 1 (by rfl) ⟨2109779, by rfl⟩ : syracuseStep 2813039 = 4219559) B4219559
theorem B2813135 : Blo 1873638 2813135 := bstep (se 1 (by rfl) ⟨2109851, by rfl⟩ : syracuseStep 2813135 = 4219703) B4219703
theorem B16018681 : Blo 1873638 16018681 := bstep (se 2 (by rfl) ⟨6007005, by rfl⟩ : syracuseStep 16018681 = 12014011) B12014011
theorem B7597331 : Blo 1873638 7597331 := bstep (se 1 (by rfl) ⟨5697998, by rfl⟩ : syracuseStep 7597331 = 11395997) B11395997
theorem B316386593 : Blo 1873638 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B2813255 : Blo 1873638 2813255 := bstep (se 1 (by rfl) ⟨2109941, by rfl⟩ : syracuseStep 2813255 = 4219883) B4219883
theorem B6327719 : Blo 1873638 6327719 := bstep (se 1 (by rfl) ⟨4745789, by rfl⟩ : syracuseStep 6327719 = 9491579) B9491579
theorem B4746671 : Blo 1873638 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B16018955 : Blo 1873638 16018955 := bstep (se 1 (by rfl) ⟨12014216, by rfl⟩ : syracuseStep 16018955 = 24028433) B24028433
theorem B12013373 : Blo 1873638 12013373 := bstep (se 3 (by rfl) ⟨2252507, by rfl⟩ : syracuseStep 12013373 = 4505015) B4505015
theorem B173207483 : Blo 1873638 173207483 := bstep (se 1 (by rfl) ⟨129905612, by rfl⟩ : syracuseStep 173207483 = 259811225) B259811225
theorem B5337215 : Blo 1873638 5337215 := bstep (se 1 (by rfl) ⟨4002911, by rfl⟩ : syracuseStep 5337215 = 8005823) B8005823
theorem B9490607 : Blo 1873638 9490607 := bstep (se 1 (by rfl) ⟨7117955, by rfl⟩ : syracuseStep 9490607 = 14235911) B14235911
theorem B9007357 : Blo 1873638 9007357 := bstep (se 3 (by rfl) ⟨1688879, by rfl⟩ : syracuseStep 9007357 = 3377759) B3377759
theorem B4747643 : Blo 1873638 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B36516257 : Blo 1873638 36516257 := bstep (se 2 (by rfl) ⟨13693596, by rfl⟩ : syracuseStep 36516257 = 27387193) B27387193
theorem B8663647 : Blo 1873638 8663647 := bstep (se 1 (by rfl) ⟨6497735, by rfl⟩ : syracuseStep 8663647 = 12995471) B12995471
theorem B3560041 : Blo 1873638 3560041 := bstep (se 2 (by rfl) ⟨1335015, by rfl⟩ : syracuseStep 3560041 = 2670031) B2670031
theorem B5337875 : Blo 1873638 5337875 := bstep (se 1 (by rfl) ⟨4003406, by rfl⟩ : syracuseStep 5337875 = 8006813) B8006813
theorem B21648161 : Blo 1873638 21648161 := bstep (se 2 (by rfl) ⟨8118060, by rfl⟩ : syracuseStep 21648161 = 16236121) B16236121
theorem B2372591 : Blo 1873638 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B5338183 : Blo 1873638 5338183 := bstep (se 1 (by rfl) ⟨4003637, by rfl⟩ : syracuseStep 5338183 = 8007275) B8007275
theorem B4216031 : Blo 1873638 4216031 := bstep (se 1 (by rfl) ⟨3162023, by rfl⟩ : syracuseStep 4216031 = 6324047) B6324047
theorem B87790949 : Blo 1873638 87790949 := bstep (se 4 (by rfl) ⟨8230401, by rfl⟩ : syracuseStep 87790949 = 16460803) B16460803
theorem B62444933 : Blo 1873638 62444933 := bstep (se 4 (by rfl) ⟨5854212, by rfl⟩ : syracuseStep 62444933 = 11708425) B11708425
theorem B4216463 : Blo 1873638 4216463 := bstep (se 1 (by rfl) ⟨3162347, by rfl⟩ : syracuseStep 4216463 = 6324695) B6324695
theorem B4216553 : Blo 1873638 4216553 := bstep (se 2 (by rfl) ⟨1581207, by rfl⟩ : syracuseStep 4216553 = 3162415) B3162415
theorem B9492227 : Blo 1873638 9492227 := bstep (se 1 (by rfl) ⟨7119170, by rfl⟩ : syracuseStep 9492227 = 14238341) B14238341
theorem B7116605 : Blo 1873638 7116605 := bstep (se 3 (by rfl) ⟨1334363, by rfl⟩ : syracuseStep 7116605 = 2668727) B2668727
theorem B4003663 : Blo 1873638 4003663 := bstep (se 1 (by rfl) ⟨3002747, by rfl⟩ : syracuseStep 4003663 = 6005495) B6005495
theorem B6330203 : Blo 1873638 6330203 := bstep (se 1 (by rfl) ⟨4747652, by rfl⟩ : syracuseStep 6330203 = 9495305) B9495305
theorem B5339105 : Blo 1873638 5339105 := bstep (se 2 (by rfl) ⟨2002164, by rfl⟩ : syracuseStep 5339105 = 4004329) B4004329
theorem B1873951 : Blo 1873638 1873951 := bstep (se 1 (by rfl) ⟨1405463, by rfl⟩ : syracuseStep 1873951 = 2810927) B2810927
theorem B10156103 : Blo 1873638 10156103 := bstep (se 1 (by rfl) ⟨7617077, by rfl⟩ : syracuseStep 10156103 = 15234155) B15234155
theorem B1874031 : Blo 1873638 1874031 := bstep (se 1 (by rfl) ⟨1405523, by rfl⟩ : syracuseStep 1874031 = 2811047) B2811047
theorem B6003035 : Blo 1873638 6003035 := bstep (se 1 (by rfl) ⟨4502276, by rfl⟩ : syracuseStep 6003035 = 9004553) B9004553
theorem B1874279 : Blo 1873638 1874279 := bstep (se 1 (by rfl) ⟨1405709, by rfl⟩ : syracuseStep 1874279 = 2811419) B2811419
theorem B2849183 : Blo 1873638 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B5339641 : Blo 1873638 5339641 := bstep (se 2 (by rfl) ⟨2002365, by rfl⟩ : syracuseStep 5339641 = 4004731) B4004731
theorem B5339675 : Blo 1873638 5339675 := bstep (se 1 (by rfl) ⟨4004756, by rfl⟩ : syracuseStep 5339675 = 8009513) B8009513
theorem B5069407 : Blo 1873638 5069407 := bstep (se 1 (by rfl) ⟨3802055, by rfl⟩ : syracuseStep 5069407 = 7604111) B7604111
theorem B1874535 : Blo 1873638 1874535 := bstep (se 1 (by rfl) ⟨1405901, by rfl⟩ : syracuseStep 1874535 = 2811803) B2811803
theorem B6003305 : Blo 1873638 6003305 := bstep (se 2 (by rfl) ⟨2251239, by rfl⟩ : syracuseStep 6003305 = 4502479) B4502479
theorem B1874559 : Blo 1873638 1874559 := bstep (se 1 (by rfl) ⟨1405919, by rfl⟩ : syracuseStep 1874559 = 2811839) B2811839
theorem B1874683 : Blo 1873638 1874683 := bstep (se 1 (by rfl) ⟨1406012, by rfl⟩ : syracuseStep 1874683 = 2812025) B2812025
theorem B1874939 : Blo 1873638 1874939 := bstep (se 1 (by rfl) ⟨1406204, by rfl⟩ : syracuseStep 1874939 = 2812409) B2812409
theorem B1874975 : Blo 1873638 1874975 := bstep (se 1 (by rfl) ⟨1406231, by rfl⟩ : syracuseStep 1874975 = 2812463) B2812463
theorem B1875263 : Blo 1873638 1875263 := bstep (se 1 (by rfl) ⟨1406447, by rfl⟩ : syracuseStep 1875263 = 2812895) B2812895
theorem B4218191 : Blo 1873638 4218191 := bstep (se 1 (by rfl) ⟨3163643, by rfl⟩ : syracuseStep 4218191 = 6327287) B6327287
theorem B9493847 : Blo 1873638 9493847 := bstep (se 1 (by rfl) ⟨7120385, by rfl⟩ : syracuseStep 9493847 = 14240771) B14240771
theorem B4218281 : Blo 1873638 4218281 := bstep (se 2 (by rfl) ⟨1581855, by rfl⟩ : syracuseStep 4218281 = 3163711) B3163711
theorem B24337925 : Blo 1873638 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B1875559 : Blo 1873638 1875559 := bstep (se 1 (by rfl) ⟨1406669, by rfl⟩ : syracuseStep 1875559 = 2813339) B2813339
theorem B8003225 : Blo 1873638 8003225 := bstep (se 2 (by rfl) ⟨3001209, by rfl⟩ : syracuseStep 8003225 = 6002419) B6002419
theorem B4005551 : Blo 1873638 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B21348035 : Blo 1873638 21348035 := bstep (se 1 (by rfl) ⟨16011026, by rfl⟩ : syracuseStep 21348035 = 32022053) B32022053
theorem B6324479 : Blo 1873638 6324479 := bstep (se 1 (by rfl) ⟨4743359, by rfl⟩ : syracuseStep 6324479 = 9486719) B9486719
theorem B12009809 : Blo 1873638 12009809 := bstep (se 2 (by rfl) ⟨4503678, by rfl⟩ : syracuseStep 12009809 = 9007357) B9007357
theorem B4743593 : Blo 1873638 4743593 := bstep (se 2 (by rfl) ⟨1778847, by rfl⟩ : syracuseStep 4743593 = 3557695) B3557695
theorem B7119521 : Blo 1873638 7119521 := bstep (se 2 (by rfl) ⟨2669820, by rfl⟩ : syracuseStep 7119521 = 5339641) B5339641
theorem B3801887 : Blo 1873638 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B11551529 : Blo 1873638 11551529 := bstep (se 2 (by rfl) ⟨4331823, by rfl⟩ : syracuseStep 11551529 = 8663647) B8663647
theorem B6759209 : Blo 1873638 6759209 := bstep (se 2 (by rfl) ⟨2534703, by rfl⟩ : syracuseStep 6759209 = 5069407) B5069407
theorem B2810687 : Blo 1873638 2810687 := bstep (se 1 (by rfl) ⟨2108015, by rfl⟩ : syracuseStep 2810687 = 4216031) B4216031
theorem B3802153 : Blo 1873638 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B2810975 : Blo 1873638 2810975 := bstep (se 1 (by rfl) ⟨2108231, by rfl⟩ : syracuseStep 2810975 = 4216463) B4216463
theorem B2811035 : Blo 1873638 2811035 := bstep (se 1 (by rfl) ⟨2108276, by rfl⟩ : syracuseStep 2811035 = 4216553) B4216553
theorem B4744403 : Blo 1873638 4744403 := bstep (se 1 (by rfl) ⟨3558302, by rfl⟩ : syracuseStep 4744403 = 7116605) B7116605
theorem B4220135 : Blo 1873638 4220135 := bstep (se 1 (by rfl) ⟨3165101, by rfl⟩ : syracuseStep 4220135 = 6330203) B6330203
theorem B3163495 : Blo 1873638 3163495 := bstep (se 1 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 3163495 = 4745243) B4745243
theorem B21358241 : Blo 1873638 21358241 := bstep (se 2 (by rfl) ⟨8009340, by rfl⟩ : syracuseStep 21358241 = 16018681) B16018681
theorem B5064887 : Blo 1873638 5064887 := bstep (se 1 (by rfl) ⟨3798665, by rfl⟩ : syracuseStep 5064887 = 7597331) B7597331
theorem B2812127 : Blo 1873638 2812127 := bstep (se 1 (by rfl) ⟨2109095, by rfl⟩ : syracuseStep 2812127 = 4218191) B4218191
theorem B2812187 : Blo 1873638 2812187 := bstep (se 1 (by rfl) ⟨2109140, by rfl⟩ : syracuseStep 2812187 = 4218281) B4218281
theorem B3164447 : Blo 1873638 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B5335483 : Blo 1873638 5335483 := bstep (se 1 (by rfl) ⟨4001612, by rfl⟩ : syracuseStep 5335483 = 8003225) B8003225
theorem B14232023 : Blo 1873638 14232023 := bstep (se 1 (by rfl) ⟨10674017, by rfl⟩ : syracuseStep 14232023 = 21348035) B21348035
theorem B6326909 : Blo 1873638 6326909 := bstep (se 3 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 6326909 = 2372591) B2372591
theorem B6327017 : Blo 1873638 6327017 := bstep (se 2 (by rfl) ⟨2372631, by rfl⟩ : syracuseStep 6327017 = 4745263) B4745263
theorem B3558143 : Blo 1873638 3558143 := bstep (se 1 (by rfl) ⟨2668607, by rfl⟩ : syracuseStep 3558143 = 5337215) B5337215
theorem B6327071 : Blo 1873638 6327071 := bstep (se 1 (by rfl) ⟨4745303, by rfl⟩ : syracuseStep 6327071 = 9490607) B9490607
theorem B3165095 : Blo 1873638 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B3558583 : Blo 1873638 3558583 := bstep (se 1 (by rfl) ⟨2668937, by rfl⟩ : syracuseStep 3558583 = 5337875) B5337875
theorem B48065885 : Blo 1873638 48065885 := bstep (se 3 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 48065885 = 18024707) B18024707
theorem B9006511 : Blo 1873638 9006511 := bstep (se 1 (by rfl) ⟨6754883, by rfl⟩ : syracuseStep 9006511 = 13509767) B13509767
theorem B51326423 : Blo 1873638 51326423 := bstep (se 1 (by rfl) ⟨38494817, by rfl⟩ : syracuseStep 51326423 = 76989635) B76989635
theorem B4746721 : Blo 1873638 4746721 := bstep (se 2 (by rfl) ⟨1780020, by rfl⟩ : syracuseStep 4746721 = 3560041) B3560041
theorem B58527299 : Blo 1873638 58527299 := bstep (se 1 (by rfl) ⟨43895474, by rfl⟩ : syracuseStep 58527299 = 87790949) B87790949
theorem B6328151 : Blo 1873638 6328151 := bstep (se 1 (by rfl) ⟨4746113, by rfl⟩ : syracuseStep 6328151 = 9492227) B9492227
theorem B2404255 : Blo 1873638 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B3559403 : Blo 1873638 3559403 := bstep (se 1 (by rfl) ⟨2669552, by rfl⟩ : syracuseStep 3559403 = 5339105) B5339105
theorem B7598063 : Blo 1873638 7598063 := bstep (se 1 (by rfl) ⟨5698547, by rfl⟩ : syracuseStep 7598063 = 11397095) B11397095
theorem B6328313 : Blo 1873638 6328313 := bstep (se 2 (by rfl) ⟨2373117, by rfl⟩ : syracuseStep 6328313 = 4746235) B4746235
theorem B6770735 : Blo 1873638 6770735 := bstep (se 1 (by rfl) ⟨5078051, by rfl⟩ : syracuseStep 6770735 = 10156103) B10156103
theorem B4002023 : Blo 1873638 4002023 := bstep (se 1 (by rfl) ⟨3001517, by rfl⟩ : syracuseStep 4002023 = 6003035) B6003035
theorem B3559783 : Blo 1873638 3559783 := bstep (se 1 (by rfl) ⟨2669837, by rfl⟩ : syracuseStep 3559783 = 5339675) B5339675
theorem B14233967 : Blo 1873638 14233967 := bstep (se 1 (by rfl) ⟨10675475, by rfl⟩ : syracuseStep 14233967 = 21350951) B21350951
theorem B4002203 : Blo 1873638 4002203 := bstep (se 1 (by rfl) ⟨3001652, by rfl⟩ : syracuseStep 4002203 = 6003305) B6003305
theorem B24015311 : Blo 1873638 24015311 := bstep (se 1 (by rfl) ⟨18011483, by rfl⟩ : syracuseStep 24015311 = 36022967) B36022967
theorem B5337647 : Blo 1873638 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B210924395 : Blo 1873638 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B6329231 : Blo 1873638 6329231 := bstep (se 1 (by rfl) ⟨4746923, by rfl⟩ : syracuseStep 6329231 = 9493847) B9493847
theorem B16225283 : Blo 1873638 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B10679303 : Blo 1873638 10679303 := bstep (se 1 (by rfl) ⟨8009477, by rfl⟩ : syracuseStep 10679303 = 16018955) B16018955
theorem B5338217 : Blo 1873638 5338217 := bstep (se 2 (by rfl) ⟨2001831, by rfl⟩ : syracuseStep 5338217 = 4003663) B4003663
theorem B8008915 : Blo 1873638 8008915 := bstep (se 1 (by rfl) ⟨6006686, by rfl⟩ : syracuseStep 8008915 = 12013373) B12013373
theorem B115471655 : Blo 1873638 115471655 := bstep (se 1 (by rfl) ⟨86603741, by rfl⟩ : syracuseStep 115471655 = 173207483) B173207483
theorem B16012667 : Blo 1873638 16012667 := bstep (se 1 (by rfl) ⟨12009500, by rfl⟩ : syracuseStep 16012667 = 24019001) B24019001
theorem B4216427 : Blo 1873638 4216427 := bstep (se 1 (by rfl) ⟨3162320, by rfl⟩ : syracuseStep 4216427 = 6324641) B6324641
theorem B24344171 : Blo 1873638 24344171 := bstep (se 1 (by rfl) ⟨18258128, by rfl⟩ : syracuseStep 24344171 = 36516257) B36516257
theorem B6330095 : Blo 1873638 6330095 := bstep (se 1 (by rfl) ⟨4747571, by rfl⟩ : syracuseStep 6330095 = 9495143) B9495143
theorem B1873855 : Blo 1873638 1873855 := bstep (se 1 (by rfl) ⟨1405391, by rfl⟩ : syracuseStep 1873855 = 2810783) B2810783
theorem B4216787 : Blo 1873638 4216787 := bstep (se 1 (by rfl) ⟨3162590, by rfl⟩ : syracuseStep 4216787 = 6325181) B6325181
theorem B4216859 : Blo 1873638 4216859 := bstep (se 1 (by rfl) ⟨3162644, by rfl⟩ : syracuseStep 4216859 = 6325289) B6325289
theorem B1874047 : Blo 1873638 1874047 := bstep (se 1 (by rfl) ⟨1405535, by rfl⟩ : syracuseStep 1874047 = 2811071) B2811071
theorem B1874143 : Blo 1873638 1874143 := bstep (se 1 (by rfl) ⟨1405607, by rfl⟩ : syracuseStep 1874143 = 2811215) B2811215
theorem B41629955 : Blo 1873638 41629955 := bstep (se 1 (by rfl) ⟨31222466, by rfl⟩ : syracuseStep 41629955 = 62444933) B62444933
theorem B1874203 : Blo 1873638 1874203 := bstep (se 1 (by rfl) ⟨1405652, by rfl⟩ : syracuseStep 1874203 = 2811305) B2811305
theorem B1874303 : Blo 1873638 1874303 := bstep (se 1 (by rfl) ⟨1405727, by rfl⟩ : syracuseStep 1874303 = 2811455) B2811455
theorem B6756959 : Blo 1873638 6756959 := bstep (se 1 (by rfl) ⟨5067719, by rfl⟩ : syracuseStep 6756959 = 10135439) B10135439
theorem B1874543 : Blo 1873638 1874543 := bstep (se 1 (by rfl) ⟨1405907, by rfl⟩ : syracuseStep 1874543 = 2811815) B2811815
theorem B1874623 : Blo 1873638 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B7117577 : Blo 1873638 7117577 := bstep (se 2 (by rfl) ⟨2669091, by rfl⟩ : syracuseStep 7117577 = 5338183) B5338183
theorem B1899455 : Blo 1873638 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B4004807 : Blo 1873638 4004807 := bstep (se 1 (by rfl) ⟨3003605, by rfl⟩ : syracuseStep 4004807 = 6007211) B6007211
theorem B1874927 : Blo 1873638 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B1875047 : Blo 1873638 1875047 := bstep (se 1 (by rfl) ⟨1406285, by rfl⟩ : syracuseStep 1875047 = 2812571) B2812571
theorem B10681469 : Blo 1873638 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B1875195 : Blo 1873638 1875195 := bstep (se 1 (by rfl) ⟨1406396, by rfl⟩ : syracuseStep 1875195 = 2812793) B2812793
theorem B4218119 : Blo 1873638 4218119 := bstep (se 1 (by rfl) ⟨3163589, by rfl⟩ : syracuseStep 4218119 = 6327179) B6327179
theorem B1875359 : Blo 1873638 1875359 := bstep (se 1 (by rfl) ⟨1406519, by rfl⟩ : syracuseStep 1875359 = 2813039) B2813039
theorem B57728429 : Blo 1873638 57728429 := bstep (se 3 (by rfl) ⟨10824080, by rfl⟩ : syracuseStep 57728429 = 21648161) B21648161
theorem B1875423 : Blo 1873638 1875423 := bstep (se 1 (by rfl) ⟨1406567, by rfl⟩ : syracuseStep 1875423 = 2813135) B2813135
theorem B1875503 : Blo 1873638 1875503 := bstep (se 1 (by rfl) ⟨1406627, by rfl⟩ : syracuseStep 1875503 = 2813255) B2813255
theorem B4218479 : Blo 1873638 4218479 := bstep (se 1 (by rfl) ⟨3163859, by rfl⟩ : syracuseStep 4218479 = 6327719) B6327719
theorem B4513823 : Blo 1873638 4513823 := bstep (se 1 (by rfl) ⟨3385367, by rfl⟩ : syracuseStep 4513823 = 6770735) B6770735
theorem B3162395 : Blo 1873638 3162395 := bstep (se 1 (by rfl) ⟨2371796, by rfl⟩ : syracuseStep 3162395 = 4743593) B4743593
theorem B4506139 : Blo 1873638 4506139 := bstep (se 1 (by rfl) ⟨3379604, by rfl⟩ : syracuseStep 4506139 = 6759209) B6759209
theorem B140616263 : Blo 1873638 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B4219487 : Blo 1873638 4219487 := bstep (se 1 (by rfl) ⟨3164615, by rfl⟩ : syracuseStep 4219487 = 6329231) B6329231
theorem B7119535 : Blo 1873638 7119535 := bstep (se 1 (by rfl) ⟨5339651, by rfl⟩ : syracuseStep 7119535 = 10679303) B10679303
theorem B3162935 : Blo 1873638 3162935 := bstep (se 1 (by rfl) ⟨2372201, by rfl⟩ : syracuseStep 3162935 = 4744403) B4744403
theorem B76981103 : Blo 1873638 76981103 := bstep (se 1 (by rfl) ⟨57735827, by rfl⟩ : syracuseStep 76981103 = 115471655) B115471655
theorem B10675111 : Blo 1873638 10675111 := bstep (se 1 (by rfl) ⟨8006333, by rfl⟩ : syracuseStep 10675111 = 16012667) B16012667
theorem B2810951 : Blo 1873638 2810951 := bstep (se 1 (by rfl) ⟨2108213, by rfl⟩ : syracuseStep 2810951 = 4216427) B4216427
theorem B16229447 : Blo 1873638 16229447 := bstep (se 1 (by rfl) ⟨12172085, by rfl⟩ : syracuseStep 16229447 = 24344171) B24344171
theorem B14238827 : Blo 1873638 14238827 := bstep (se 1 (by rfl) ⟨10679120, by rfl⟩ : syracuseStep 14238827 = 21358241) B21358241
theorem B4220063 : Blo 1873638 4220063 := bstep (se 1 (by rfl) ⟨3165047, by rfl⟩ : syracuseStep 4220063 = 6330095) B6330095
theorem B2811191 : Blo 1873638 2811191 := bstep (se 1 (by rfl) ⟨2108393, by rfl⟩ : syracuseStep 2811191 = 4216787) B4216787
theorem B2811239 : Blo 1873638 2811239 := bstep (se 1 (by rfl) ⟨2108429, by rfl⟩ : syracuseStep 2811239 = 4216859) B4216859
theorem B4744777 : Blo 1873638 4744777 := bstep (se 2 (by rfl) ⟨1779291, by rfl⟩ : syracuseStep 4744777 = 3558583) B3558583
theorem B9488015 : Blo 1873638 9488015 := bstep (se 1 (by rfl) ⟨7116011, by rfl⟩ : syracuseStep 9488015 = 14232023) B14232023
theorem B4745051 : Blo 1873638 4745051 := bstep (se 1 (by rfl) ⟨3558788, by rfl⟩ : syracuseStep 4745051 = 7117577) B7117577
theorem B7120979 : Blo 1873638 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B30804077 : Blo 1873638 30804077 := bstep (se 3 (by rfl) ⟨5775764, by rfl⟩ : syracuseStep 30804077 = 11551529) B11551529
theorem B2812079 : Blo 1873638 2812079 := bstep (se 1 (by rfl) ⟨2109059, by rfl⟩ : syracuseStep 2812079 = 4218119) B4218119
theorem B2812319 : Blo 1873638 2812319 := bstep (se 1 (by rfl) ⟨2109239, by rfl⟩ : syracuseStep 2812319 = 4218479) B4218479
theorem B5065213 : Blo 1873638 5065213 := bstep (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) B1899455
theorem B3205673 : Blo 1873638 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B5065375 : Blo 1873638 5065375 := bstep (se 1 (by rfl) ⟨3799031, by rfl⟩ : syracuseStep 5065375 = 7598063) B7598063
theorem B8006539 : Blo 1873638 8006539 := bstep (se 1 (by rfl) ⟨6004904, by rfl⟩ : syracuseStep 8006539 = 12009809) B12009809
theorem B9489311 : Blo 1873638 9489311 := bstep (se 1 (by rfl) ⟨7116983, by rfl⟩ : syracuseStep 9489311 = 14233967) B14233967
theorem B16010207 : Blo 1873638 16010207 := bstep (se 1 (by rfl) ⟨12007655, by rfl⟩ : syracuseStep 16010207 = 24015311) B24015311
theorem B3558431 : Blo 1873638 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B4746347 : Blo 1873638 4746347 := bstep (se 1 (by rfl) ⟨3559760, by rfl⟩ : syracuseStep 4746347 = 7119521) B7119521
theorem B4746377 : Blo 1873638 4746377 := bstep (se 2 (by rfl) ⟨1779891, by rfl⟩ : syracuseStep 4746377 = 3559783) B3559783
theorem B2534591 : Blo 1873638 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B7113977 : Blo 1873638 7113977 := bstep (se 2 (by rfl) ⟨2667741, by rfl⟩ : syracuseStep 7113977 = 5335483) B5335483
theorem B111013213 : Blo 1873638 111013213 := bstep (se 3 (by rfl) ⟨20814977, by rfl⟩ : syracuseStep 111013213 = 41629955) B41629955
theorem B3558811 : Blo 1873638 3558811 := bstep (se 1 (by rfl) ⟨2669108, by rfl⟩ : syracuseStep 3558811 = 5338217) B5338217
theorem B2813423 : Blo 1873638 2813423 := bstep (se 1 (by rfl) ⟨2110067, by rfl⟩ : syracuseStep 2813423 = 4220135) B4220135
theorem B2109631 : Blo 1873638 2109631 := bstep (se 1 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 2109631 = 3164447) B3164447
theorem B18018557 : Blo 1873638 18018557 := bstep (se 3 (by rfl) ⟨3378479, by rfl⟩ : syracuseStep 18018557 = 6756959) B6756959
theorem B10678553 : Blo 1873638 10678553 := bstep (se 2 (by rfl) ⟨4004457, by rfl⟩ : syracuseStep 10678553 = 8008915) B8008915
theorem B2372095 : Blo 1873638 2372095 := bstep (se 1 (by rfl) ⟨1779071, by rfl⟩ : syracuseStep 2372095 = 3558143) B3558143
theorem B2110063 : Blo 1873638 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B6328961 : Blo 1873638 6328961 := bstep (se 2 (by rfl) ⟨2373360, by rfl⟩ : syracuseStep 6328961 = 4746721) B4746721
theorem B32043923 : Blo 1873638 32043923 := bstep (se 1 (by rfl) ⟨24032942, by rfl⟩ : syracuseStep 32043923 = 48065885) B48065885
theorem B10679485 : Blo 1873638 10679485 := bstep (se 3 (by rfl) ⟨2002403, by rfl⟩ : syracuseStep 10679485 = 4004807) B4004807
theorem B9491741 : Blo 1873638 9491741 := bstep (se 3 (by rfl) ⟨1779701, by rfl⟩ : syracuseStep 9491741 = 3559403) B3559403
theorem B43267421 : Blo 1873638 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B2668015 : Blo 1873638 2668015 := bstep (se 1 (by rfl) ⟨2001011, by rfl⟩ : syracuseStep 2668015 = 4002023) B4002023
theorem B4216319 : Blo 1873638 4216319 := bstep (se 1 (by rfl) ⟨3162239, by rfl⟩ : syracuseStep 4216319 = 6324479) B6324479
theorem B2668135 : Blo 1873638 2668135 := bstep (se 1 (by rfl) ⟨2001101, by rfl⟩ : syracuseStep 2668135 = 4002203) B4002203
theorem B13506365 : Blo 1873638 13506365 := bstep (se 3 (by rfl) ⟨2532443, by rfl⟩ : syracuseStep 13506365 = 5064887) B5064887
theorem B1873791 : Blo 1873638 1873791 := bstep (se 1 (by rfl) ⟨1405343, by rfl⟩ : syracuseStep 1873791 = 2810687) B2810687
theorem B1873983 : Blo 1873638 1873983 := bstep (se 1 (by rfl) ⟨1405487, by rfl⟩ : syracuseStep 1873983 = 2810975) B2810975
theorem B1874023 : Blo 1873638 1874023 := bstep (se 1 (by rfl) ⟨1405517, by rfl⟩ : syracuseStep 1874023 = 2811035) B2811035
theorem B5069537 : Blo 1873638 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B1874751 : Blo 1873638 1874751 := bstep (se 1 (by rfl) ⟨1406063, by rfl⟩ : syracuseStep 1874751 = 2812127) B2812127
theorem B1874791 : Blo 1873638 1874791 := bstep (se 1 (by rfl) ⟨1406093, by rfl⟩ : syracuseStep 1874791 = 2812187) B2812187
theorem B4217939 : Blo 1873638 4217939 := bstep (se 1 (by rfl) ⟨3163454, by rfl⟩ : syracuseStep 4217939 = 6326909) B6326909
theorem B4217993 : Blo 1873638 4217993 := bstep (se 2 (by rfl) ⟨1581747, by rfl⟩ : syracuseStep 4217993 = 3163495) B3163495
theorem B4218011 : Blo 1873638 4218011 := bstep (se 1 (by rfl) ⟨3163508, by rfl⟩ : syracuseStep 4218011 = 6327017) B6327017
theorem B4218047 : Blo 1873638 4218047 := bstep (se 1 (by rfl) ⟨3163535, by rfl⟩ : syracuseStep 4218047 = 6327071) B6327071
theorem B12008681 : Blo 1873638 12008681 := bstep (se 2 (by rfl) ⟨4503255, by rfl⟩ : syracuseStep 12008681 = 9006511) B9006511
theorem B38485619 : Blo 1873638 38485619 := bstep (se 1 (by rfl) ⟨28864214, by rfl⟩ : syracuseStep 38485619 = 57728429) B57728429
theorem B34217615 : Blo 1873638 34217615 := bstep (se 1 (by rfl) ⟨25663211, by rfl⟩ : syracuseStep 34217615 = 51326423) B51326423
theorem B39018199 : Blo 1873638 39018199 := bstep (se 1 (by rfl) ⟨29263649, by rfl⟩ : syracuseStep 39018199 = 58527299) B58527299
theorem B4218767 : Blo 1873638 4218767 := bstep (se 1 (by rfl) ⟨3164075, by rfl⟩ : syracuseStep 4218767 = 6328151) B6328151
theorem B4218875 : Blo 1873638 4218875 := bstep (se 1 (by rfl) ⟨3164156, by rfl⟩ : syracuseStep 4218875 = 6328313) B6328313
theorem B7119035 : Blo 1873638 7119035 := bstep (se 1 (by rfl) ⟨5339276, by rfl⟩ : syracuseStep 7119035 = 10678553) B10678553
theorem B4219307 : Blo 1873638 4219307 := bstep (se 1 (by rfl) ⟨3164480, by rfl⟩ : syracuseStep 4219307 = 6328961) B6328961
theorem B6758909 : Blo 1873638 6758909 := bstep (se 3 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 6758909 = 2534591) B2534591
theorem B3162793 : Blo 1873638 3162793 := bstep (se 2 (by rfl) ⟨1186047, by rfl⟩ : syracuseStep 3162793 = 2372095) B2372095
theorem B28844947 : Blo 1873638 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B2810879 : Blo 1873638 2810879 := bstep (se 1 (by rfl) ⟨2108159, by rfl⟩ : syracuseStep 2810879 = 4216319) B4216319
theorem B6325343 : Blo 1873638 6325343 := bstep (se 1 (by rfl) ⟨4744007, by rfl⟩ : syracuseStep 6325343 = 9488015) B9488015
theorem B10675385 : Blo 1873638 10675385 := bstep (se 2 (by rfl) ⟨4003269, by rfl⟩ : syracuseStep 10675385 = 8006539) B8006539
theorem B3163367 : Blo 1873638 3163367 := bstep (se 1 (by rfl) ⟨2372525, by rfl⟩ : syracuseStep 3163367 = 4745051) B4745051
theorem B14239313 : Blo 1873638 14239313 := bstep (se 2 (by rfl) ⟨5339742, by rfl⟩ : syracuseStep 14239313 = 10679485) B10679485
theorem B4745081 : Blo 1873638 4745081 := bstep (se 2 (by rfl) ⟨1779405, by rfl⟩ : syracuseStep 4745081 = 3558811) B3558811
theorem B6326207 : Blo 1873638 6326207 := bstep (se 1 (by rfl) ⟨4744655, by rfl⟩ : syracuseStep 6326207 = 9489311) B9489311
theorem B3557353 : Blo 1873638 3557353 := bstep (se 2 (by rfl) ⟨1334007, by rfl⟩ : syracuseStep 3557353 = 2668015) B2668015
theorem B2811959 : Blo 1873638 2811959 := bstep (se 1 (by rfl) ⟨2108969, by rfl⟩ : syracuseStep 2811959 = 4217939) B4217939
theorem B3164231 : Blo 1873638 3164231 := bstep (se 1 (by rfl) ⟨2373173, by rfl⟩ : syracuseStep 3164231 = 4746347) B4746347
theorem B2811995 : Blo 1873638 2811995 := bstep (se 1 (by rfl) ⟨2108996, by rfl⟩ : syracuseStep 2811995 = 4217993) B4217993
theorem B3164251 : Blo 1873638 3164251 := bstep (se 1 (by rfl) ⟨2373188, by rfl⟩ : syracuseStep 3164251 = 4746377) B4746377
theorem B6326369 : Blo 1873638 6326369 := bstep (se 2 (by rfl) ⟨2372388, by rfl⟩ : syracuseStep 6326369 = 4744777) B4744777
theorem B2812007 : Blo 1873638 2812007 := bstep (se 1 (by rfl) ⟨2109005, by rfl⟩ : syracuseStep 2812007 = 4218011) B4218011
theorem B2812031 : Blo 1873638 2812031 := bstep (se 1 (by rfl) ⟨2109023, by rfl⟩ : syracuseStep 2812031 = 4218047) B4218047
theorem B3557513 : Blo 1873638 3557513 := bstep (se 2 (by rfl) ⟨1334067, by rfl⟩ : syracuseStep 3557513 = 2668135) B2668135
theorem B8005787 : Blo 1873638 8005787 := bstep (se 1 (by rfl) ⟨6004340, by rfl⟩ : syracuseStep 8005787 = 12008681) B12008681
theorem B2812511 : Blo 1873638 2812511 := bstep (se 1 (by rfl) ⟨2109383, by rfl⟩ : syracuseStep 2812511 = 4218767) B4218767
theorem B2812583 : Blo 1873638 2812583 := bstep (se 1 (by rfl) ⟨2109437, by rfl⟩ : syracuseStep 2812583 = 4218875) B4218875
theorem B3009215 : Blo 1873638 3009215 := bstep (se 1 (by rfl) ⟨2256911, by rfl⟩ : syracuseStep 3009215 = 4513823) B4513823
theorem B9489149 : Blo 1873638 9489149 := bstep (se 3 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 9489149 = 3558431) B3558431
theorem B12012371 : Blo 1873638 12012371 := bstep (se 1 (by rfl) ⟨9009278, by rfl⟩ : syracuseStep 12012371 = 18018557) B18018557
theorem B2108263 : Blo 1873638 2108263 := bstep (se 1 (by rfl) ⟨1581197, by rfl⟩ : syracuseStep 2108263 = 3162395) B3162395
theorem B2812841 : Blo 1873638 2812841 := bstep (se 2 (by rfl) ⟨1054815, by rfl⟩ : syracuseStep 2812841 = 2109631) B2109631
theorem B2812991 : Blo 1873638 2812991 := bstep (se 1 (by rfl) ⟨2109743, by rfl⟩ : syracuseStep 2812991 = 4219487) B4219487
theorem B2108623 : Blo 1873638 2108623 := bstep (se 1 (by rfl) ⟨1581467, by rfl⟩ : syracuseStep 2108623 = 3162935) B3162935
theorem B6753617 : Blo 1873638 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B6008185 : Blo 1873638 6008185 := bstep (se 2 (by rfl) ⟨2253069, by rfl⟩ : syracuseStep 6008185 = 4506139) B4506139
theorem B2813375 : Blo 1873638 2813375 := bstep (se 1 (by rfl) ⟨2110031, by rfl⟩ : syracuseStep 2813375 = 4220063) B4220063
theorem B2813417 : Blo 1873638 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B6327827 : Blo 1873638 6327827 := bstep (se 1 (by rfl) ⟨4745870, by rfl⟩ : syracuseStep 6327827 = 9491741) B9491741
theorem B6753833 : Blo 1873638 6753833 := bstep (se 2 (by rfl) ⟨2532687, by rfl⟩ : syracuseStep 6753833 = 5065375) B5065375
theorem B14233481 : Blo 1873638 14233481 := bstep (se 2 (by rfl) ⟨5337555, by rfl⟩ : syracuseStep 14233481 = 10675111) B10675111
theorem B4747319 : Blo 1873638 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B374976701 : Blo 1873638 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B148017617 : Blo 1873638 148017617 := bstep (se 2 (by rfl) ⟨55506606, by rfl⟩ : syracuseStep 148017617 = 111013213) B111013213
theorem B3379691 : Blo 1873638 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B36016973 : Blo 1873638 36016973 := bstep (se 3 (by rfl) ⟨6753182, by rfl⟩ : syracuseStep 36016973 = 13506365) B13506365
theorem B52024265 : Blo 1873638 52024265 := bstep (se 2 (by rfl) ⟨19509099, by rfl⟩ : syracuseStep 52024265 = 39018199) B39018199
theorem B22811743 : Blo 1873638 22811743 := bstep (se 1 (by rfl) ⟨17108807, by rfl⟩ : syracuseStep 22811743 = 34217615) B34217615
theorem B51320735 : Blo 1873638 51320735 := bstep (se 1 (by rfl) ⟨38490551, by rfl⟩ : syracuseStep 51320735 = 76981103) B76981103
theorem B21362615 : Blo 1873638 21362615 := bstep (se 1 (by rfl) ⟨16021961, by rfl⟩ : syracuseStep 21362615 = 32043923) B32043923
theorem B1873967 : Blo 1873638 1873967 := bstep (se 1 (by rfl) ⟨1405475, by rfl⟩ : syracuseStep 1873967 = 2810951) B2810951
theorem B10819631 : Blo 1873638 10819631 := bstep (se 1 (by rfl) ⟨8114723, by rfl⟩ : syracuseStep 10819631 = 16229447) B16229447
theorem B9492551 : Blo 1873638 9492551 := bstep (se 1 (by rfl) ⟨7119413, by rfl⟩ : syracuseStep 9492551 = 14238827) B14238827
theorem B1874127 : Blo 1873638 1874127 := bstep (se 1 (by rfl) ⟨1405595, by rfl⟩ : syracuseStep 1874127 = 2811191) B2811191
theorem B9492713 : Blo 1873638 9492713 := bstep (se 2 (by rfl) ⟨3559767, by rfl⟩ : syracuseStep 9492713 = 7119535) B7119535
theorem B1874159 : Blo 1873638 1874159 := bstep (se 1 (by rfl) ⟨1405619, by rfl⟩ : syracuseStep 1874159 = 2811239) B2811239
theorem B20536051 : Blo 1873638 20536051 := bstep (se 1 (by rfl) ⟨15402038, by rfl⟩ : syracuseStep 20536051 = 30804077) B30804077
theorem B1874719 : Blo 1873638 1874719 := bstep (se 1 (by rfl) ⟨1406039, by rfl⟩ : syracuseStep 1874719 = 2812079) B2812079
theorem B1874879 : Blo 1873638 1874879 := bstep (se 1 (by rfl) ⟨1406159, by rfl⟩ : syracuseStep 1874879 = 2812319) B2812319
theorem B2137115 : Blo 1873638 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B10673471 : Blo 1873638 10673471 := bstep (se 1 (by rfl) ⟨8005103, by rfl⟩ : syracuseStep 10673471 = 16010207) B16010207
theorem B4742651 : Blo 1873638 4742651 := bstep (se 1 (by rfl) ⟨3556988, by rfl⟩ : syracuseStep 4742651 = 7113977) B7113977
theorem B1875615 : Blo 1873638 1875615 := bstep (se 1 (by rfl) ⟨1406711, by rfl⟩ : syracuseStep 1875615 = 2813423) B2813423
theorem B25657079 : Blo 1873638 25657079 := bstep (se 1 (by rfl) ⟨19242809, by rfl⟩ : syracuseStep 25657079 = 38485619) B38485619
theorem B4219001 : Blo 1873638 4219001 := bstep (se 2 (by rfl) ⟨1582125, by rfl⟩ : syracuseStep 4219001 = 3164251) B3164251
theorem B4505939 : Blo 1873638 4505939 := bstep (se 1 (by rfl) ⟨3379454, by rfl⟩ : syracuseStep 4505939 = 6758909) B6758909
theorem B24011315 : Blo 1873638 24011315 := bstep (se 1 (by rfl) ⟨18008486, by rfl⟩ : syracuseStep 24011315 = 36016973) B36016973
theorem B2811017 : Blo 1873638 2811017 := bstep (se 2 (by rfl) ⟨1054131, by rfl⟩ : syracuseStep 2811017 = 2108263) B2108263
theorem B3163387 : Blo 1873638 3163387 := bstep (se 1 (by rfl) ⟨2372540, by rfl⟩ : syracuseStep 3163387 = 4745081) B4745081
theorem B9012509 : Blo 1873638 9012509 := bstep (se 3 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 9012509 = 3379691) B3379691
theorem B2811497 : Blo 1873638 2811497 := bstep (se 2 (by rfl) ⟨1054311, by rfl⟩ : syracuseStep 2811497 = 2108623) B2108623
theorem B6326099 : Blo 1873638 6326099 := bstep (se 1 (by rfl) ⟨4744574, by rfl⟩ : syracuseStep 6326099 = 9489149) B9489149
theorem B9488987 : Blo 1873638 9488987 := bstep (se 1 (by rfl) ⟨7116740, by rfl⟩ : syracuseStep 9488987 = 14233481) B14233481
theorem B3164879 : Blo 1873638 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B4746023 : Blo 1873638 4746023 := bstep (se 1 (by rfl) ⟨3559517, by rfl⟩ : syracuseStep 4746023 = 7119035) B7119035
theorem B2812871 : Blo 1873638 2812871 := bstep (se 1 (by rfl) ⟨2109653, by rfl⟩ : syracuseStep 2812871 = 4219307) B4219307
theorem B2108911 : Blo 1873638 2108911 := bstep (se 1 (by rfl) ⟨1581683, by rfl⟩ : syracuseStep 2108911 = 3163367) B3163367
theorem B27381401 : Blo 1873638 27381401 := bstep (se 2 (by rfl) ⟨10268025, by rfl⟩ : syracuseStep 27381401 = 20536051) B20536051
theorem B34213823 : Blo 1873638 34213823 := bstep (se 1 (by rfl) ⟨25660367, by rfl⟩ : syracuseStep 34213823 = 51320735) B51320735
theorem B14241743 : Blo 1873638 14241743 := bstep (se 1 (by rfl) ⟨10681307, by rfl⟩ : syracuseStep 14241743 = 21362615) B21362615
theorem B7213087 : Blo 1873638 7213087 := bstep (se 1 (by rfl) ⟨5409815, by rfl⟩ : syracuseStep 7213087 = 10819631) B10819631
theorem B6328367 : Blo 1873638 6328367 := bstep (se 1 (by rfl) ⟨4746275, by rfl⟩ : syracuseStep 6328367 = 9492551) B9492551
theorem B2109487 : Blo 1873638 2109487 := bstep (se 1 (by rfl) ⟨1582115, by rfl⟩ : syracuseStep 2109487 = 3164231) B3164231
theorem B2371675 : Blo 1873638 2371675 := bstep (se 1 (by rfl) ⟨1778756, by rfl⟩ : syracuseStep 2371675 = 3557513) B3557513
theorem B5337191 : Blo 1873638 5337191 := bstep (se 1 (by rfl) ⟨4002893, by rfl⟩ : syracuseStep 5337191 = 8005787) B8005787
theorem B6328475 : Blo 1873638 6328475 := bstep (se 1 (by rfl) ⟨4746356, by rfl⟩ : syracuseStep 6328475 = 9492713) B9492713
theorem B8024573 : Blo 1873638 8024573 := bstep (se 3 (by rfl) ⟨1504607, by rfl⟩ : syracuseStep 8024573 = 3009215) B3009215
theorem B8008247 : Blo 1873638 8008247 := bstep (se 1 (by rfl) ⟨6006185, by rfl⟩ : syracuseStep 8008247 = 12012371) B12012371
theorem B7115647 : Blo 1873638 7115647 := bstep (se 1 (by rfl) ⟨5336735, by rfl⟩ : syracuseStep 7115647 = 10673471) B10673471
theorem B4502411 : Blo 1873638 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B4502555 : Blo 1873638 4502555 := bstep (se 1 (by rfl) ⟨3376916, by rfl⟩ : syracuseStep 4502555 = 6753833) B6753833
theorem B273675509 : Blo 1873638 273675509 := bstep (se 5 (by rfl) ⟨12828539, by rfl⟩ : syracuseStep 273675509 = 25657079) B25657079
theorem B5698973 : Blo 1873638 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B249984467 : Blo 1873638 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B98678411 : Blo 1873638 98678411 := bstep (se 1 (by rfl) ⟨74008808, by rfl⟩ : syracuseStep 98678411 = 148017617) B148017617
theorem B34682843 : Blo 1873638 34682843 := bstep (se 1 (by rfl) ⟨26012132, by rfl⟩ : syracuseStep 34682843 = 52024265) B52024265
theorem B1873919 : Blo 1873638 1873919 := bstep (se 1 (by rfl) ⟨1405439, by rfl⟩ : syracuseStep 1873919 = 2810879) B2810879
theorem B4216895 : Blo 1873638 4216895 := bstep (se 1 (by rfl) ⟨3162671, by rfl⟩ : syracuseStep 4216895 = 6325343) B6325343
theorem B7116923 : Blo 1873638 7116923 := bstep (se 1 (by rfl) ⟨5337692, by rfl⟩ : syracuseStep 7116923 = 10675385) B10675385
theorem B4217057 : Blo 1873638 4217057 := bstep (se 2 (by rfl) ⟨1581396, by rfl⟩ : syracuseStep 4217057 = 3162793) B3162793
theorem B9492875 : Blo 1873638 9492875 := bstep (se 1 (by rfl) ⟨7119656, by rfl⟩ : syracuseStep 9492875 = 14239313) B14239313
theorem B38459929 : Blo 1873638 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B4217471 : Blo 1873638 4217471 := bstep (se 1 (by rfl) ⟨3163103, by rfl⟩ : syracuseStep 4217471 = 6326207) B6326207
theorem B1874639 : Blo 1873638 1874639 := bstep (se 1 (by rfl) ⟨1405979, by rfl⟩ : syracuseStep 1874639 = 2811959) B2811959
theorem B1874663 : Blo 1873638 1874663 := bstep (se 1 (by rfl) ⟨1405997, by rfl⟩ : syracuseStep 1874663 = 2811995) B2811995
theorem B4217579 : Blo 1873638 4217579 := bstep (se 1 (by rfl) ⟨3163184, by rfl⟩ : syracuseStep 4217579 = 6326369) B6326369
theorem B1874671 : Blo 1873638 1874671 := bstep (se 1 (by rfl) ⟨1406003, by rfl⟩ : syracuseStep 1874671 = 2812007) B2812007
theorem B1874687 : Blo 1873638 1874687 := bstep (se 1 (by rfl) ⟨1406015, by rfl⟩ : syracuseStep 1874687 = 2812031) B2812031
theorem B30415657 : Blo 1873638 30415657 := bstep (se 2 (by rfl) ⟨11405871, by rfl⟩ : syracuseStep 30415657 = 22811743) B22811743
theorem B1875007 : Blo 1873638 1875007 := bstep (se 1 (by rfl) ⟨1406255, by rfl⟩ : syracuseStep 1875007 = 2812511) B2812511
theorem B1875055 : Blo 1873638 1875055 := bstep (se 1 (by rfl) ⟨1406291, by rfl⟩ : syracuseStep 1875055 = 2812583) B2812583
theorem B8010913 : Blo 1873638 8010913 := bstep (se 2 (by rfl) ⟨3004092, by rfl⟩ : syracuseStep 8010913 = 6008185) B6008185
theorem B1875227 : Blo 1873638 1875227 := bstep (se 1 (by rfl) ⟨1406420, by rfl⟩ : syracuseStep 1875227 = 2812841) B2812841
theorem B1875327 : Blo 1873638 1875327 := bstep (se 1 (by rfl) ⟨1406495, by rfl⟩ : syracuseStep 1875327 = 2812991) B2812991
theorem B1875583 : Blo 1873638 1875583 := bstep (se 1 (by rfl) ⟨1406687, by rfl⟩ : syracuseStep 1875583 = 2813375) B2813375
theorem B1875611 : Blo 1873638 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B3161767 : Blo 1873638 3161767 := bstep (se 1 (by rfl) ⟨2371325, by rfl⟩ : syracuseStep 3161767 = 4742651) B4742651
theorem B4218551 : Blo 1873638 4218551 := bstep (se 1 (by rfl) ⟨3163913, by rfl⟩ : syracuseStep 4218551 = 6327827) B6327827
theorem B4743137 : Blo 1873638 4743137 := bstep (se 2 (by rfl) ⟨1778676, by rfl⟩ : syracuseStep 4743137 = 3557353) B3557353
theorem B4218911 : Blo 1873638 4218911 := bstep (se 1 (by rfl) ⟨3164183, by rfl⟩ : syracuseStep 4218911 = 6328367) B6328367
theorem B9617449 : Blo 1873638 9617449 := bstep (se 2 (by rfl) ⟨3606543, by rfl⟩ : syracuseStep 9617449 = 7213087) B7213087
theorem B4218983 : Blo 1873638 4218983 := bstep (se 1 (by rfl) ⟨3164237, by rfl⟩ : syracuseStep 4218983 = 6328475) B6328475
theorem B3162233 : Blo 1873638 3162233 := bstep (se 2 (by rfl) ⟨1185837, by rfl⟩ : syracuseStep 3162233 = 2371675) B2371675
theorem B5349715 : Blo 1873638 5349715 := bstep (se 1 (by rfl) ⟨4012286, by rfl⟩ : syracuseStep 5349715 = 8024573) B8024573
theorem B16007543 : Blo 1873638 16007543 := bstep (se 1 (by rfl) ⟨12005657, by rfl⟩ : syracuseStep 16007543 = 24011315) B24011315
theorem B9487529 : Blo 1873638 9487529 := bstep (se 2 (by rfl) ⟨3557823, by rfl⟩ : syracuseStep 9487529 = 7115647) B7115647
theorem B2811263 : Blo 1873638 2811263 := bstep (se 1 (by rfl) ⟨2108447, by rfl⟩ : syracuseStep 2811263 = 4216895) B4216895
theorem B4744615 : Blo 1873638 4744615 := bstep (se 1 (by rfl) ⟨3558461, by rfl⟩ : syracuseStep 4744615 = 7116923) B7116923
theorem B2811371 : Blo 1873638 2811371 := bstep (se 1 (by rfl) ⟨2108528, by rfl⟩ : syracuseStep 2811371 = 4217057) B4217057
theorem B6325991 : Blo 1873638 6325991 := bstep (se 1 (by rfl) ⟨4744493, by rfl⟩ : syracuseStep 6325991 = 9488987) B9488987
theorem B2811647 : Blo 1873638 2811647 := bstep (se 1 (by rfl) ⟨2108735, by rfl⟩ : syracuseStep 2811647 = 4217471) B4217471
theorem B2811719 : Blo 1873638 2811719 := bstep (se 1 (by rfl) ⟨2108789, by rfl⟩ : syracuseStep 2811719 = 4217579) B4217579
theorem B3164015 : Blo 1873638 3164015 := bstep (se 1 (by rfl) ⟨2373011, by rfl⟩ : syracuseStep 3164015 = 4746023) B4746023
theorem B2811881 : Blo 1873638 2811881 := bstep (se 2 (by rfl) ⟨1054455, by rfl⟩ : syracuseStep 2811881 = 2108911) B2108911
theorem B18254267 : Blo 1873638 18254267 := bstep (se 1 (by rfl) ⟨13690700, by rfl⟩ : syracuseStep 18254267 = 27381401) B27381401
theorem B2812367 : Blo 1873638 2812367 := bstep (se 1 (by rfl) ⟨2109275, by rfl⟩ : syracuseStep 2812367 = 4218551) B4218551
theorem B22809215 : Blo 1873638 22809215 := bstep (se 1 (by rfl) ⟨17106911, by rfl⟩ : syracuseStep 22809215 = 34213823) B34213823
theorem B2812649 : Blo 1873638 2812649 := bstep (se 2 (by rfl) ⟨1054743, by rfl⟩ : syracuseStep 2812649 = 2109487) B2109487
theorem B2812667 : Blo 1873638 2812667 := bstep (se 1 (by rfl) ⟨2109500, by rfl⟩ : syracuseStep 2812667 = 4219001) B4219001
theorem B14232509 : Blo 1873638 14232509 := bstep (se 3 (by rfl) ⟨2668595, by rfl⟩ : syracuseStep 14232509 = 5337191) B5337191
theorem B3001607 : Blo 1873638 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B3001703 : Blo 1873638 3001703 := bstep (se 1 (by rfl) ⟨2251277, by rfl⟩ : syracuseStep 3001703 = 4502555) B4502555
theorem B6008339 : Blo 1873638 6008339 := bstep (se 1 (by rfl) ⟨4506254, by rfl⟩ : syracuseStep 6008339 = 9012509) B9012509
theorem B40554209 : Blo 1873638 40554209 := bstep (se 2 (by rfl) ⟨15207828, by rfl⟩ : syracuseStep 40554209 = 30415657) B30415657
theorem B65785607 : Blo 1873638 65785607 := bstep (se 1 (by rfl) ⟨49339205, by rfl⟩ : syracuseStep 65785607 = 98678411) B98678411
theorem B23121895 : Blo 1873638 23121895 := bstep (se 1 (by rfl) ⟨17341421, by rfl⟩ : syracuseStep 23121895 = 34682843) B34682843
theorem B6328583 : Blo 1873638 6328583 := bstep (se 1 (by rfl) ⟨4746437, by rfl⟩ : syracuseStep 6328583 = 9492875) B9492875
theorem B2109919 : Blo 1873638 2109919 := bstep (se 1 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 2109919 = 3164879) B3164879
theorem B4215689 : Blo 1873638 4215689 := bstep (se 2 (by rfl) ⟨1580883, by rfl⟩ : syracuseStep 4215689 = 3161767) B3161767
theorem B3003959 : Blo 1873638 3003959 := bstep (se 1 (by rfl) ⟨2252969, by rfl⟩ : syracuseStep 3003959 = 4505939) B4505939
theorem B51279905 : Blo 1873638 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B1874011 : Blo 1873638 1874011 := bstep (se 1 (by rfl) ⟨1405508, by rfl⟩ : syracuseStep 1874011 = 2811017) B2811017
theorem B182450339 : Blo 1873638 182450339 := bstep (se 1 (by rfl) ⟨136837754, by rfl⟩ : syracuseStep 182450339 = 273675509) B273675509
theorem B3799315 : Blo 1873638 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B166656311 : Blo 1873638 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B1874331 : Blo 1873638 1874331 := bstep (se 1 (by rfl) ⟨1405748, by rfl⟩ : syracuseStep 1874331 = 2811497) B2811497
theorem B4217399 : Blo 1873638 4217399 := bstep (se 1 (by rfl) ⟨3163049, by rfl⟩ : syracuseStep 4217399 = 6326099) B6326099
theorem B21355325 : Blo 1873638 21355325 := bstep (se 3 (by rfl) ⟨4004123, by rfl⟩ : syracuseStep 21355325 = 8008247) B8008247
theorem B10681217 : Blo 1873638 10681217 := bstep (se 2 (by rfl) ⟨4005456, by rfl⟩ : syracuseStep 10681217 = 8010913) B8010913
theorem B4217849 : Blo 1873638 4217849 := bstep (se 2 (by rfl) ⟨1581693, by rfl⟩ : syracuseStep 4217849 = 3163387) B3163387
theorem B1875247 : Blo 1873638 1875247 := bstep (se 1 (by rfl) ⟨1406435, by rfl⟩ : syracuseStep 1875247 = 2812871) B2812871
theorem B9494495 : Blo 1873638 9494495 := bstep (se 1 (by rfl) ⟨7120871, by rfl⟩ : syracuseStep 9494495 = 14241743) B14241743
theorem B3162091 : Blo 1873638 3162091 := bstep (se 1 (by rfl) ⟨2371568, by rfl⟩ : syracuseStep 3162091 = 4743137) B4743137
theorem B4219055 : Blo 1873638 4219055 := bstep (se 1 (by rfl) ⟨3164291, by rfl⟩ : syracuseStep 4219055 = 6328583) B6328583
theorem B2810459 : Blo 1873638 2810459 := bstep (se 1 (by rfl) ⟨2107844, by rfl⟩ : syracuseStep 2810459 = 4215689) B4215689
theorem B6325019 : Blo 1873638 6325019 := bstep (se 1 (by rfl) ⟨4743764, by rfl⟩ : syracuseStep 6325019 = 9487529) B9487529
theorem B8004541 : Blo 1873638 8004541 := bstep (se 3 (by rfl) ⟨1500851, by rfl⟩ : syracuseStep 8004541 = 3001703) B3001703
theorem B2811599 : Blo 1873638 2811599 := bstep (se 1 (by rfl) ⟨2108699, by rfl⟩ : syracuseStep 2811599 = 4217399) B4217399
theorem B15206143 : Blo 1873638 15206143 := bstep (se 1 (by rfl) ⟨11404607, by rfl⟩ : syracuseStep 15206143 = 22809215) B22809215
theorem B6326153 : Blo 1873638 6326153 := bstep (se 2 (by rfl) ⟨2372307, by rfl⟩ : syracuseStep 6326153 = 4744615) B4744615
theorem B7120811 : Blo 1873638 7120811 := bstep (se 1 (by rfl) ⟨5340608, by rfl⟩ : syracuseStep 7120811 = 10681217) B10681217
theorem B9488339 : Blo 1873638 9488339 := bstep (se 1 (by rfl) ⟨7116254, by rfl⟩ : syracuseStep 9488339 = 14232509) B14232509
theorem B2811899 : Blo 1873638 2811899 := bstep (se 1 (by rfl) ⟨2108924, by rfl⟩ : syracuseStep 2811899 = 4217849) B4217849
theorem B2001071 : Blo 1873638 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B27036139 : Blo 1873638 27036139 := bstep (se 1 (by rfl) ⟨20277104, by rfl⟩ : syracuseStep 27036139 = 40554209) B40554209
theorem B30829193 : Blo 1873638 30829193 := bstep (se 2 (by rfl) ⟨11560947, by rfl⟩ : syracuseStep 30829193 = 23121895) B23121895
theorem B2812607 : Blo 1873638 2812607 := bstep (se 1 (by rfl) ⟨2109455, by rfl⟩ : syracuseStep 2812607 = 4218911) B4218911
theorem B12823265 : Blo 1873638 12823265 := bstep (se 2 (by rfl) ⟨4808724, by rfl⟩ : syracuseStep 12823265 = 9617449) B9617449
theorem B2812655 : Blo 1873638 2812655 := bstep (se 1 (by rfl) ⟨2109491, by rfl⟩ : syracuseStep 2812655 = 4218983) B4218983
theorem B2108155 : Blo 1873638 2108155 := bstep (se 1 (by rfl) ⟨1581116, by rfl⟩ : syracuseStep 2108155 = 3162233) B3162233
theorem B5065753 : Blo 1873638 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B2813225 : Blo 1873638 2813225 := bstep (se 2 (by rfl) ⟨1054959, by rfl⟩ : syracuseStep 2813225 = 2109919) B2109919
theorem B2002639 : Blo 1873638 2002639 := bstep (se 1 (by rfl) ⟨1501979, by rfl⟩ : syracuseStep 2002639 = 3003959) B3003959
theorem B2109343 : Blo 1873638 2109343 := bstep (se 1 (by rfl) ⟨1582007, by rfl⟩ : syracuseStep 2109343 = 3164015) B3164015
theorem B111104207 : Blo 1873638 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B12169511 : Blo 1873638 12169511 := bstep (se 1 (by rfl) ⟨9127133, by rfl⟩ : syracuseStep 12169511 = 18254267) B18254267
theorem B43857071 : Blo 1873638 43857071 := bstep (se 1 (by rfl) ⟨32892803, by rfl⟩ : syracuseStep 43857071 = 65785607) B65785607
theorem B4216121 : Blo 1873638 4216121 := bstep (se 2 (by rfl) ⟨1581045, by rfl⟩ : syracuseStep 4216121 = 3162091) B3162091
theorem B6329663 : Blo 1873638 6329663 := bstep (se 1 (by rfl) ⟨4747247, by rfl⟩ : syracuseStep 6329663 = 9494495) B9494495
theorem B136746413 : Blo 1873638 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B10671695 : Blo 1873638 10671695 := bstep (se 1 (by rfl) ⟨8003771, by rfl⟩ : syracuseStep 10671695 = 16007543) B16007543
theorem B1874175 : Blo 1873638 1874175 := bstep (se 1 (by rfl) ⟨1405631, by rfl⟩ : syracuseStep 1874175 = 2811263) B2811263
theorem B1874247 : Blo 1873638 1874247 := bstep (se 1 (by rfl) ⟨1405685, by rfl⟩ : syracuseStep 1874247 = 2811371) B2811371
theorem B4217327 : Blo 1873638 4217327 := bstep (se 1 (by rfl) ⟨3162995, by rfl⟩ : syracuseStep 4217327 = 6325991) B6325991
theorem B1874431 : Blo 1873638 1874431 := bstep (se 1 (by rfl) ⟨1405823, by rfl⟩ : syracuseStep 1874431 = 2811647) B2811647
theorem B1874479 : Blo 1873638 1874479 := bstep (se 1 (by rfl) ⟨1405859, by rfl⟩ : syracuseStep 1874479 = 2811719) B2811719
theorem B1874587 : Blo 1873638 1874587 := bstep (se 1 (by rfl) ⟨1405940, by rfl⟩ : syracuseStep 1874587 = 2811881) B2811881
theorem B121633559 : Blo 1873638 121633559 := bstep (se 1 (by rfl) ⟨91225169, by rfl⟩ : syracuseStep 121633559 = 182450339) B182450339
theorem B1874911 : Blo 1873638 1874911 := bstep (se 1 (by rfl) ⟨1406183, by rfl⟩ : syracuseStep 1874911 = 2812367) B2812367
theorem B28531813 : Blo 1873638 28531813 := bstep (se 4 (by rfl) ⟨2674857, by rfl⟩ : syracuseStep 28531813 = 5349715) B5349715
theorem B1875099 : Blo 1873638 1875099 := bstep (se 1 (by rfl) ⟨1406324, by rfl⟩ : syracuseStep 1875099 = 2812649) B2812649
theorem B1875111 : Blo 1873638 1875111 := bstep (se 1 (by rfl) ⟨1406333, by rfl⟩ : syracuseStep 1875111 = 2812667) B2812667
theorem B14236883 : Blo 1873638 14236883 := bstep (se 1 (by rfl) ⟨10677662, by rfl⟩ : syracuseStep 14236883 = 21355325) B21355325
theorem B4005559 : Blo 1873638 4005559 := bstep (se 1 (by rfl) ⟨3004169, by rfl⟩ : syracuseStep 4005559 = 6008339) B6008339
theorem B29238047 : Blo 1873638 29238047 := bstep (se 1 (by rfl) ⟨21928535, by rfl⟩ : syracuseStep 29238047 = 43857071) B43857071
theorem B2810747 : Blo 1873638 2810747 := bstep (se 1 (by rfl) ⟨2108060, by rfl⟩ : syracuseStep 2810747 = 4216121) B4216121
theorem B4219775 : Blo 1873638 4219775 := bstep (se 1 (by rfl) ⟨3164831, by rfl⟩ : syracuseStep 4219775 = 6329663) B6329663
theorem B2810873 : Blo 1873638 2810873 := bstep (se 2 (by rfl) ⟨1054077, by rfl⟩ : syracuseStep 2810873 = 2108155) B2108155
theorem B6325559 : Blo 1873638 6325559 := bstep (se 1 (by rfl) ⟨4744169, by rfl⟩ : syracuseStep 6325559 = 9488339) B9488339
theorem B2811551 : Blo 1873638 2811551 := bstep (se 1 (by rfl) ⟨2108663, by rfl⟩ : syracuseStep 2811551 = 4217327) B4217327
theorem B2812457 : Blo 1873638 2812457 := bstep (se 2 (by rfl) ⟨1054671, by rfl⟩ : syracuseStep 2812457 = 2109343) B2109343
theorem B2812703 : Blo 1873638 2812703 := bstep (se 1 (by rfl) ⟨2109527, by rfl⟩ : syracuseStep 2812703 = 4219055) B4219055
theorem B8113007 : Blo 1873638 8113007 := bstep (se 1 (by rfl) ⟨6084755, by rfl⟩ : syracuseStep 8113007 = 12169511) B12169511
theorem B5336189 : Blo 1873638 5336189 := bstep (se 3 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 5336189 = 2001071) B2001071
theorem B36048185 : Blo 1873638 36048185 := bstep (se 2 (by rfl) ⟨13518069, by rfl⟩ : syracuseStep 36048185 = 27036139) B27036139
theorem B91164275 : Blo 1873638 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B7114463 : Blo 1873638 7114463 := bstep (se 1 (by rfl) ⟨5335847, by rfl⟩ : syracuseStep 7114463 = 10671695) B10671695
theorem B4747207 : Blo 1873638 4747207 := bstep (se 1 (by rfl) ⟨3560405, by rfl⟩ : syracuseStep 4747207 = 7120811) B7120811
theorem B6754337 : Blo 1873638 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B8548843 : Blo 1873638 8548843 := bstep (se 1 (by rfl) ⟨6411632, by rfl⟩ : syracuseStep 8548843 = 12823265) B12823265
theorem B81089039 : Blo 1873638 81089039 := bstep (se 1 (by rfl) ⟨60816779, by rfl⟩ : syracuseStep 81089039 = 121633559) B121633559
theorem B9491255 : Blo 1873638 9491255 := bstep (se 1 (by rfl) ⟨7118441, by rfl⟩ : syracuseStep 9491255 = 14236883) B14236883
theorem B74069471 : Blo 1873638 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B1873639 : Blo 1873638 1873639 := bstep (se 1 (by rfl) ⟨1405229, by rfl⟩ : syracuseStep 1873639 = 2810459) B2810459
theorem B4216679 : Blo 1873638 4216679 := bstep (se 1 (by rfl) ⟨3162509, by rfl⟩ : syracuseStep 4216679 = 6325019) B6325019
theorem B1874399 : Blo 1873638 1874399 := bstep (se 1 (by rfl) ⟨1405799, by rfl⟩ : syracuseStep 1874399 = 2811599) B2811599
theorem B10672721 : Blo 1873638 10672721 := bstep (se 2 (by rfl) ⟨4002270, by rfl⟩ : syracuseStep 10672721 = 8004541) B8004541
theorem B4217435 : Blo 1873638 4217435 := bstep (se 1 (by rfl) ⟨3163076, by rfl⟩ : syracuseStep 4217435 = 6326153) B6326153
theorem B1874599 : Blo 1873638 1874599 := bstep (se 1 (by rfl) ⟨1405949, by rfl⟩ : syracuseStep 1874599 = 2811899) B2811899
theorem B38042417 : Blo 1873638 38042417 := bstep (se 2 (by rfl) ⟨14265906, by rfl⟩ : syracuseStep 38042417 = 28531813) B28531813
theorem B20552795 : Blo 1873638 20552795 := bstep (se 1 (by rfl) ⟨15414596, by rfl⟩ : syracuseStep 20552795 = 30829193) B30829193
theorem B1875071 : Blo 1873638 1875071 := bstep (se 1 (by rfl) ⟨1406303, by rfl⟩ : syracuseStep 1875071 = 2812607) B2812607
theorem B1875103 : Blo 1873638 1875103 := bstep (se 1 (by rfl) ⟨1406327, by rfl⟩ : syracuseStep 1875103 = 2812655) B2812655
theorem B1875483 : Blo 1873638 1875483 := bstep (se 1 (by rfl) ⟨1406612, by rfl⟩ : syracuseStep 1875483 = 2813225) B2813225
theorem B5340745 : Blo 1873638 5340745 := bstep (se 2 (by rfl) ⟨2002779, by rfl⟩ : syracuseStep 5340745 = 4005559) B4005559
theorem B2670185 : Blo 1873638 2670185 := bstep (se 2 (by rfl) ⟨1001319, by rfl⟩ : syracuseStep 2670185 = 2002639) B2002639
theorem B20274857 : Blo 1873638 20274857 := bstep (se 2 (by rfl) ⟨7603071, by rfl⟩ : syracuseStep 20274857 = 15206143) B15206143
theorem B54059359 : Blo 1873638 54059359 := bstep (se 1 (by rfl) ⟨40544519, by rfl⟩ : syracuseStep 54059359 = 81089039) B81089039
theorem B2811119 : Blo 1873638 2811119 := bstep (se 1 (by rfl) ⟨2108339, by rfl⟩ : syracuseStep 2811119 = 4216679) B4216679
theorem B7120493 : Blo 1873638 7120493 := bstep (se 3 (by rfl) ⟨1335092, by rfl⟩ : syracuseStep 7120493 = 2670185) B2670185
theorem B2811623 : Blo 1873638 2811623 := bstep (se 1 (by rfl) ⟨2108717, by rfl⟩ : syracuseStep 2811623 = 4217435) B4217435
theorem B3557459 : Blo 1873638 3557459 := bstep (se 1 (by rfl) ⟨2668094, by rfl⟩ : syracuseStep 3557459 = 5336189) B5336189
theorem B7120993 : Blo 1873638 7120993 := bstep (se 2 (by rfl) ⟨2670372, by rfl⟩ : syracuseStep 7120993 = 5340745) B5340745
theorem B19492031 : Blo 1873638 19492031 := bstep (se 1 (by rfl) ⟨14619023, by rfl⟩ : syracuseStep 19492031 = 29238047) B29238047
theorem B6327503 : Blo 1873638 6327503 := bstep (se 1 (by rfl) ⟨4745627, by rfl⟩ : syracuseStep 6327503 = 9491255) B9491255
theorem B2813183 : Blo 1873638 2813183 := bstep (se 1 (by rfl) ⟨2109887, by rfl⟩ : syracuseStep 2813183 = 4219775) B4219775
theorem B11398457 : Blo 1873638 11398457 := bstep (se 2 (by rfl) ⟨4274421, by rfl⟩ : syracuseStep 11398457 = 8548843) B8548843
theorem B7115147 : Blo 1873638 7115147 := bstep (se 1 (by rfl) ⟨5336360, by rfl⟩ : syracuseStep 7115147 = 10672721) B10672721
theorem B13701863 : Blo 1873638 13701863 := bstep (se 1 (by rfl) ⟨10276397, by rfl⟩ : syracuseStep 13701863 = 20552795) B20552795
theorem B101446445 : Blo 1873638 101446445 := bstep (se 3 (by rfl) ⟨19021208, by rfl⟩ : syracuseStep 101446445 = 38042417) B38042417
theorem B24032123 : Blo 1873638 24032123 := bstep (se 1 (by rfl) ⟨18024092, by rfl⟩ : syracuseStep 24032123 = 36048185) B36048185
theorem B6329609 : Blo 1873638 6329609 := bstep (se 2 (by rfl) ⟨2373603, by rfl⟩ : syracuseStep 6329609 = 4747207) B4747207
theorem B4502891 : Blo 1873638 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B1873831 : Blo 1873638 1873831 := bstep (se 1 (by rfl) ⟨1405373, by rfl⟩ : syracuseStep 1873831 = 2810747) B2810747
theorem B1873915 : Blo 1873638 1873915 := bstep (se 1 (by rfl) ⟨1405436, by rfl⟩ : syracuseStep 1873915 = 2810873) B2810873
theorem B4217039 : Blo 1873638 4217039 := bstep (se 1 (by rfl) ⟨3162779, by rfl⟩ : syracuseStep 4217039 = 6325559) B6325559
theorem B49379647 : Blo 1873638 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B1874367 : Blo 1873638 1874367 := bstep (se 1 (by rfl) ⟨1405775, by rfl⟩ : syracuseStep 1874367 = 2811551) B2811551
theorem B1874971 : Blo 1873638 1874971 := bstep (se 1 (by rfl) ⟨1406228, by rfl⟩ : syracuseStep 1874971 = 2812457) B2812457
theorem B1875135 : Blo 1873638 1875135 := bstep (se 1 (by rfl) ⟨1406351, by rfl⟩ : syracuseStep 1875135 = 2812703) B2812703
theorem B21634685 : Blo 1873638 21634685 := bstep (se 3 (by rfl) ⟨4056503, by rfl⟩ : syracuseStep 21634685 = 8113007) B8113007
theorem B60776183 : Blo 1873638 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B13516571 : Blo 1873638 13516571 := bstep (se 1 (by rfl) ⟨10137428, by rfl⟩ : syracuseStep 13516571 = 20274857) B20274857
theorem B4742975 : Blo 1873638 4742975 := bstep (se 1 (by rfl) ⟨3557231, by rfl⟩ : syracuseStep 4742975 = 7114463) B7114463
theorem B9494657 : Blo 1873638 9494657 := bstep (se 2 (by rfl) ⟨3560496, by rfl⟩ : syracuseStep 9494657 = 7120993) B7120993
theorem B9486557 : Blo 1873638 9486557 := bstep (se 3 (by rfl) ⟨1778729, by rfl⟩ : syracuseStep 9486557 = 3557459) B3557459
theorem B4743431 : Blo 1873638 4743431 := bstep (se 1 (by rfl) ⟨3557573, by rfl⟩ : syracuseStep 4743431 = 7115147) B7115147
theorem B9134575 : Blo 1873638 9134575 := bstep (se 1 (by rfl) ⟨6850931, by rfl⟩ : syracuseStep 9134575 = 13701863) B13701863
theorem B4219739 : Blo 1873638 4219739 := bstep (se 1 (by rfl) ⟨3164804, by rfl⟩ : syracuseStep 4219739 = 6329609) B6329609
theorem B2811359 : Blo 1873638 2811359 := bstep (se 1 (by rfl) ⟨2108519, by rfl⟩ : syracuseStep 2811359 = 4217039) B4217039
theorem B12994687 : Blo 1873638 12994687 := bstep (se 1 (by rfl) ⟨9746015, by rfl⟩ : syracuseStep 12994687 = 19492031) B19492031
theorem B4746995 : Blo 1873638 4746995 := bstep (se 1 (by rfl) ⟨3560246, by rfl⟩ : syracuseStep 4746995 = 7120493) B7120493
theorem B7598971 : Blo 1873638 7598971 := bstep (se 1 (by rfl) ⟨5699228, by rfl⟩ : syracuseStep 7598971 = 11398457) B11398457
theorem B14423123 : Blo 1873638 14423123 := bstep (se 1 (by rfl) ⟨10817342, by rfl⟩ : syracuseStep 14423123 = 21634685) B21634685
theorem B72079145 : Blo 1873638 72079145 := bstep (se 2 (by rfl) ⟨27029679, by rfl⟩ : syracuseStep 72079145 = 54059359) B54059359
theorem B67630963 : Blo 1873638 67630963 := bstep (se 1 (by rfl) ⟨50723222, by rfl⟩ : syracuseStep 67630963 = 101446445) B101446445
theorem B16021415 : Blo 1873638 16021415 := bstep (se 1 (by rfl) ⟨12016061, by rfl⟩ : syracuseStep 16021415 = 24032123) B24032123
theorem B1874079 : Blo 1873638 1874079 := bstep (se 1 (by rfl) ⟨1405559, by rfl⟩ : syracuseStep 1874079 = 2811119) B2811119
theorem B12007709 : Blo 1873638 12007709 := bstep (se 3 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 12007709 = 4502891) B4502891
theorem B1874415 : Blo 1873638 1874415 := bstep (se 1 (by rfl) ⟨1405811, by rfl⟩ : syracuseStep 1874415 = 2811623) B2811623
theorem B1053432469 : Blo 1873638 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B36044189 : Blo 1873638 36044189 := bstep (se 3 (by rfl) ⟨6758285, by rfl⟩ : syracuseStep 36044189 = 13516571) B13516571
theorem B4218335 : Blo 1873638 4218335 := bstep (se 1 (by rfl) ⟨3163751, by rfl⟩ : syracuseStep 4218335 = 6327503) B6327503
theorem B1875455 : Blo 1873638 1875455 := bstep (se 1 (by rfl) ⟨1406591, by rfl⟩ : syracuseStep 1875455 = 2813183) B2813183
theorem B40517455 : Blo 1873638 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B3161983 : Blo 1873638 3161983 := bstep (se 1 (by rfl) ⟨2371487, by rfl⟩ : syracuseStep 3161983 = 4742975) B4742975
theorem B6324371 : Blo 1873638 6324371 := bstep (se 1 (by rfl) ⟨4743278, by rfl⟩ : syracuseStep 6324371 = 9486557) B9486557
theorem B3162287 : Blo 1873638 3162287 := bstep (se 1 (by rfl) ⟨2371715, by rfl⟩ : syracuseStep 3162287 = 4743431) B4743431
theorem B38461661 : Blo 1873638 38461661 := bstep (se 3 (by rfl) ⟨7211561, by rfl⟩ : syracuseStep 38461661 = 14423123) B14423123
theorem B69304997 : Blo 1873638 69304997 := bstep (se 4 (by rfl) ⟨6497343, by rfl⟩ : syracuseStep 69304997 = 12994687) B12994687
theorem B1404576625 : Blo 1873638 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B8005139 : Blo 1873638 8005139 := bstep (se 1 (by rfl) ⟨6003854, by rfl⟩ : syracuseStep 8005139 = 12007709) B12007709
theorem B24029459 : Blo 1873638 24029459 := bstep (se 1 (by rfl) ⟨18022094, by rfl⟩ : syracuseStep 24029459 = 36044189) B36044189
theorem B2812223 : Blo 1873638 2812223 := bstep (se 1 (by rfl) ⟨2109167, by rfl⟩ : syracuseStep 2812223 = 4218335) B4218335
theorem B3164663 : Blo 1873638 3164663 := bstep (se 1 (by rfl) ⟨2373497, by rfl⟩ : syracuseStep 3164663 = 4746995) B4746995
theorem B2813159 : Blo 1873638 2813159 := bstep (se 1 (by rfl) ⟨2109869, by rfl⟩ : syracuseStep 2813159 = 4219739) B4219739
theorem B54023273 : Blo 1873638 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B90174617 : Blo 1873638 90174617 := bstep (se 2 (by rfl) ⟨33815481, by rfl⟩ : syracuseStep 90174617 = 67630963) B67630963
theorem B4215977 : Blo 1873638 4215977 := bstep (se 2 (by rfl) ⟨1580991, by rfl⟩ : syracuseStep 4215977 = 3161983) B3161983
theorem B6329771 : Blo 1873638 6329771 := bstep (se 1 (by rfl) ⟨4747328, by rfl⟩ : syracuseStep 6329771 = 9494657) B9494657
theorem B1874239 : Blo 1873638 1874239 := bstep (se 1 (by rfl) ⟨1405679, by rfl⟩ : syracuseStep 1874239 = 2811359) B2811359
theorem B10131961 : Blo 1873638 10131961 := bstep (se 2 (by rfl) ⟨3799485, by rfl⟩ : syracuseStep 10131961 = 7598971) B7598971
theorem B48052763 : Blo 1873638 48052763 := bstep (se 1 (by rfl) ⟨36039572, by rfl⟩ : syracuseStep 48052763 = 72079145) B72079145
theorem B10680943 : Blo 1873638 10680943 := bstep (se 1 (by rfl) ⟨8010707, by rfl⟩ : syracuseStep 10680943 = 16021415) B16021415
theorem B48717733 : Blo 1873638 48717733 := bstep (se 4 (by rfl) ⟨4567287, by rfl⟩ : syracuseStep 48717733 = 9134575) B9134575
theorem B25641107 : Blo 1873638 25641107 := bstep (se 1 (by rfl) ⟨19230830, by rfl⟩ : syracuseStep 25641107 = 38461661) B38461661
theorem B13509281 : Blo 1873638 13509281 := bstep (se 2 (by rfl) ⟨5065980, by rfl⟩ : syracuseStep 13509281 = 10131961) B10131961
theorem B2810651 : Blo 1873638 2810651 := bstep (se 1 (by rfl) ⟨2107988, by rfl⟩ : syracuseStep 2810651 = 4215977) B4215977
theorem B4219847 : Blo 1873638 4219847 := bstep (se 1 (by rfl) ⟨3164885, by rfl⟩ : syracuseStep 4219847 = 6329771) B6329771
theorem B184813325 : Blo 1873638 184813325 := bstep (se 3 (by rfl) ⟨34652498, by rfl⟩ : syracuseStep 184813325 = 69304997) B69304997
theorem B64956977 : Blo 1873638 64956977 := bstep (se 2 (by rfl) ⟨24358866, by rfl⟩ : syracuseStep 64956977 = 48717733) B48717733
theorem B2108191 : Blo 1873638 2108191 := bstep (se 1 (by rfl) ⟨1581143, by rfl⟩ : syracuseStep 2108191 = 3162287) B3162287
theorem B36015515 : Blo 1873638 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B60116411 : Blo 1873638 60116411 := bstep (se 1 (by rfl) ⟨45087308, by rfl⟩ : syracuseStep 60116411 = 90174617) B90174617
theorem B14241257 : Blo 1873638 14241257 := bstep (se 2 (by rfl) ⟨5340471, by rfl⟩ : syracuseStep 14241257 = 10680943) B10680943
theorem B5336759 : Blo 1873638 5336759 := bstep (se 1 (by rfl) ⟨4002569, by rfl⟩ : syracuseStep 5336759 = 8005139) B8005139
theorem B1872768833 : Blo 1873638 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B16019639 : Blo 1873638 16019639 := bstep (se 1 (by rfl) ⟨12014729, by rfl⟩ : syracuseStep 16019639 = 24029459) B24029459
theorem B2109775 : Blo 1873638 2109775 := bstep (se 1 (by rfl) ⟨1582331, by rfl⟩ : syracuseStep 2109775 = 3164663) B3164663
theorem B32035175 : Blo 1873638 32035175 := bstep (se 1 (by rfl) ⟨24026381, by rfl⟩ : syracuseStep 32035175 = 48052763) B48052763
theorem B4216247 : Blo 1873638 4216247 := bstep (se 1 (by rfl) ⟨3162185, by rfl⟩ : syracuseStep 4216247 = 6324371) B6324371
theorem B1874815 : Blo 1873638 1874815 := bstep (se 1 (by rfl) ⟨1406111, by rfl⟩ : syracuseStep 1874815 = 2812223) B2812223
theorem B1875439 : Blo 1873638 1875439 := bstep (se 1 (by rfl) ⟨1406579, by rfl⟩ : syracuseStep 1875439 = 2813159) B2813159
theorem B21356783 : Blo 1873638 21356783 := bstep (se 1 (by rfl) ⟨16017587, by rfl⟩ : syracuseStep 21356783 = 32035175) B32035175
theorem B2810831 : Blo 1873638 2810831 := bstep (se 1 (by rfl) ⟨2108123, by rfl⟩ : syracuseStep 2810831 = 4216247) B4216247
theorem B2810921 : Blo 1873638 2810921 := bstep (se 2 (by rfl) ⟨1054095, by rfl⟩ : syracuseStep 2810921 = 2108191) B2108191
theorem B123208883 : Blo 1873638 123208883 := bstep (se 1 (by rfl) ⟨92406662, by rfl⟩ : syracuseStep 123208883 = 184813325) B184813325
theorem B43304651 : Blo 1873638 43304651 := bstep (se 1 (by rfl) ⟨32478488, by rfl⟩ : syracuseStep 43304651 = 64956977) B64956977
theorem B40077607 : Blo 1873638 40077607 := bstep (se 1 (by rfl) ⟨30058205, by rfl⟩ : syracuseStep 40077607 = 60116411) B60116411
theorem B3557839 : Blo 1873638 3557839 := bstep (se 1 (by rfl) ⟨2668379, by rfl⟩ : syracuseStep 3557839 = 5336759) B5336759
theorem B1248512555 : Blo 1873638 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B2813033 : Blo 1873638 2813033 := bstep (se 2 (by rfl) ⟨1054887, by rfl⟩ : syracuseStep 2813033 = 2109775) B2109775
theorem B9006187 : Blo 1873638 9006187 := bstep (se 1 (by rfl) ⟨6754640, by rfl⟩ : syracuseStep 9006187 = 13509281) B13509281
theorem B2813231 : Blo 1873638 2813231 := bstep (se 1 (by rfl) ⟨2109923, by rfl⟩ : syracuseStep 2813231 = 4219847) B4219847
theorem B17094071 : Blo 1873638 17094071 := bstep (se 1 (by rfl) ⟨12820553, by rfl⟩ : syracuseStep 17094071 = 25641107) B25641107
theorem B10679759 : Blo 1873638 10679759 := bstep (se 1 (by rfl) ⟨8009819, by rfl⟩ : syracuseStep 10679759 = 16019639) B16019639
theorem B1873767 : Blo 1873638 1873767 := bstep (se 1 (by rfl) ⟨1405325, by rfl⟩ : syracuseStep 1873767 = 2810651) B2810651
theorem B24010343 : Blo 1873638 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B9494171 : Blo 1873638 9494171 := bstep (se 1 (by rfl) ⟨7120628, by rfl⟩ : syracuseStep 9494171 = 14241257) B14241257
theorem B14237855 : Blo 1873638 14237855 := bstep (se 1 (by rfl) ⟨10678391, by rfl⟩ : syracuseStep 14237855 = 21356783) B21356783
theorem B53436809 : Blo 1873638 53436809 := bstep (se 2 (by rfl) ⟨20038803, by rfl⟩ : syracuseStep 53436809 = 40077607) B40077607
theorem B4743785 : Blo 1873638 4743785 := bstep (se 2 (by rfl) ⟨1778919, by rfl⟩ : syracuseStep 4743785 = 3557839) B3557839
theorem B11396047 : Blo 1873638 11396047 := bstep (se 1 (by rfl) ⟨8547035, by rfl⟩ : syracuseStep 11396047 = 17094071) B17094071
theorem B7119839 : Blo 1873638 7119839 := bstep (se 1 (by rfl) ⟨5339879, by rfl⟩ : syracuseStep 7119839 = 10679759) B10679759
theorem B28869767 : Blo 1873638 28869767 := bstep (se 1 (by rfl) ⟨21652325, by rfl⟩ : syracuseStep 28869767 = 43304651) B43304651
theorem B832341703 : Blo 1873638 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B6329447 : Blo 1873638 6329447 := bstep (se 1 (by rfl) ⟨4747085, by rfl⟩ : syracuseStep 6329447 = 9494171) B9494171
theorem B1873887 : Blo 1873638 1873887 := bstep (se 1 (by rfl) ⟨1405415, by rfl⟩ : syracuseStep 1873887 = 2810831) B2810831
theorem B1873947 : Blo 1873638 1873947 := bstep (se 1 (by rfl) ⟨1405460, by rfl⟩ : syracuseStep 1873947 = 2810921) B2810921
theorem B82139255 : Blo 1873638 82139255 := bstep (se 1 (by rfl) ⟨61604441, by rfl⟩ : syracuseStep 82139255 = 123208883) B123208883
theorem B12008249 : Blo 1873638 12008249 := bstep (se 2 (by rfl) ⟨4503093, by rfl⟩ : syracuseStep 12008249 = 9006187) B9006187
theorem B1875355 : Blo 1873638 1875355 := bstep (se 1 (by rfl) ⟨1406516, by rfl⟩ : syracuseStep 1875355 = 2813033) B2813033
theorem B1875487 : Blo 1873638 1875487 := bstep (se 1 (by rfl) ⟨1406615, by rfl⟩ : syracuseStep 1875487 = 2813231) B2813231
theorem B16006895 : Blo 1873638 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B3162523 : Blo 1873638 3162523 := bstep (se 1 (by rfl) ⟨2371892, by rfl⟩ : syracuseStep 3162523 = 4743785) B4743785
theorem B4219631 : Blo 1873638 4219631 := bstep (se 1 (by rfl) ⟨3164723, by rfl⟩ : syracuseStep 4219631 = 6329447) B6329447
theorem B8005499 : Blo 1873638 8005499 := bstep (se 1 (by rfl) ⟨6004124, by rfl⟩ : syracuseStep 8005499 = 12008249) B12008249
theorem B1109788937 : Blo 1873638 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B4746559 : Blo 1873638 4746559 := bstep (se 1 (by rfl) ⟨3559919, by rfl⟩ : syracuseStep 4746559 = 7119839) B7119839
theorem B19246511 : Blo 1873638 19246511 := bstep (se 1 (by rfl) ⟨14434883, by rfl⟩ : syracuseStep 19246511 = 28869767) B28869767
theorem B54759503 : Blo 1873638 54759503 := bstep (se 1 (by rfl) ⟨41069627, by rfl⟩ : syracuseStep 54759503 = 82139255) B82139255
theorem B10671263 : Blo 1873638 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B9491903 : Blo 1873638 9491903 := bstep (se 1 (by rfl) ⟨7118927, by rfl⟩ : syracuseStep 9491903 = 14237855) B14237855
theorem B35624539 : Blo 1873638 35624539 := bstep (se 1 (by rfl) ⟨26718404, by rfl⟩ : syracuseStep 35624539 = 53436809) B53436809
theorem B15194729 : Blo 1873638 15194729 := bstep (se 2 (by rfl) ⟨5698023, by rfl⟩ : syracuseStep 15194729 = 11396047) B11396047
theorem B47499385 : Blo 1873638 47499385 := bstep (se 2 (by rfl) ⟨17812269, by rfl⟩ : syracuseStep 47499385 = 35624539) B35624539
theorem B12831007 : Blo 1873638 12831007 := bstep (se 1 (by rfl) ⟨9623255, by rfl⟩ : syracuseStep 12831007 = 19246511) B19246511
theorem B36506335 : Blo 1873638 36506335 := bstep (se 1 (by rfl) ⟨27379751, by rfl⟩ : syracuseStep 36506335 = 54759503) B54759503
theorem B2813087 : Blo 1873638 2813087 := bstep (se 1 (by rfl) ⟨2109815, by rfl⟩ : syracuseStep 2813087 = 4219631) B4219631
theorem B7114175 : Blo 1873638 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B6327935 : Blo 1873638 6327935 := bstep (se 1 (by rfl) ⟨4745951, by rfl⟩ : syracuseStep 6327935 = 9491903) B9491903
theorem B5336999 : Blo 1873638 5336999 := bstep (se 1 (by rfl) ⟨4002749, by rfl⟩ : syracuseStep 5336999 = 8005499) B8005499
theorem B10129819 : Blo 1873638 10129819 := bstep (se 1 (by rfl) ⟨7597364, by rfl⟩ : syracuseStep 10129819 = 15194729) B15194729
theorem B6328745 : Blo 1873638 6328745 := bstep (se 2 (by rfl) ⟨2373279, by rfl⟩ : syracuseStep 6328745 = 4746559) B4746559
theorem B4216697 : Blo 1873638 4216697 := bstep (se 2 (by rfl) ⟨1581261, by rfl⟩ : syracuseStep 4216697 = 3162523) B3162523
theorem B739859291 : Blo 1873638 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B63332513 : Blo 1873638 63332513 := bstep (se 2 (by rfl) ⟨23749692, by rfl⟩ : syracuseStep 63332513 = 47499385) B47499385
theorem B4219163 : Blo 1873638 4219163 := bstep (se 1 (by rfl) ⟨3164372, by rfl⟩ : syracuseStep 4219163 = 6328745) B6328745
theorem B2811131 : Blo 1873638 2811131 := bstep (se 1 (by rfl) ⟨2108348, by rfl⟩ : syracuseStep 2811131 = 4216697) B4216697
theorem B3557999 : Blo 1873638 3557999 := bstep (se 1 (by rfl) ⟨2668499, by rfl⟩ : syracuseStep 3557999 = 5336999) B5336999
theorem B17108009 : Blo 1873638 17108009 := bstep (se 2 (by rfl) ⟨6415503, by rfl⟩ : syracuseStep 17108009 = 12831007) B12831007
theorem B13506425 : Blo 1873638 13506425 := bstep (se 2 (by rfl) ⟨5064909, by rfl⟩ : syracuseStep 13506425 = 10129819) B10129819
theorem B48675113 : Blo 1873638 48675113 := bstep (se 2 (by rfl) ⟨18253167, by rfl⟩ : syracuseStep 48675113 = 36506335) B36506335
theorem B493239527 : Blo 1873638 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B1875391 : Blo 1873638 1875391 := bstep (se 1 (by rfl) ⟨1406543, by rfl⟩ : syracuseStep 1875391 = 2813087) B2813087
theorem B4742783 : Blo 1873638 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B4218623 : Blo 1873638 4218623 := bstep (se 1 (by rfl) ⟨3163967, by rfl⟩ : syracuseStep 4218623 = 6327935) B6327935
theorem B42221675 : Blo 1873638 42221675 := bstep (se 1 (by rfl) ⟨31666256, by rfl⟩ : syracuseStep 42221675 = 63332513) B63332513
theorem B9004283 : Blo 1873638 9004283 := bstep (se 1 (by rfl) ⟨6753212, by rfl⟩ : syracuseStep 9004283 = 13506425) B13506425
theorem B32450075 : Blo 1873638 32450075 := bstep (se 1 (by rfl) ⟨24337556, by rfl⟩ : syracuseStep 32450075 = 48675113) B48675113
theorem B11405339 : Blo 1873638 11405339 := bstep (se 1 (by rfl) ⟨8554004, by rfl⟩ : syracuseStep 11405339 = 17108009) B17108009
theorem B2812415 : Blo 1873638 2812415 := bstep (se 1 (by rfl) ⟨2109311, by rfl⟩ : syracuseStep 2812415 = 4218623) B4218623
theorem B2812775 : Blo 1873638 2812775 := bstep (se 1 (by rfl) ⟨2109581, by rfl⟩ : syracuseStep 2812775 = 4219163) B4219163
theorem B2371999 : Blo 1873638 2371999 := bstep (se 1 (by rfl) ⟨1778999, by rfl⟩ : syracuseStep 2371999 = 3557999) B3557999
theorem B1874087 : Blo 1873638 1874087 := bstep (se 1 (by rfl) ⟨1405565, by rfl⟩ : syracuseStep 1874087 = 2811131) B2811131
theorem B328826351 : Blo 1873638 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B3161855 : Blo 1873638 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B28147783 : Blo 1873638 28147783 := bstep (se 1 (by rfl) ⟨21110837, by rfl⟩ : syracuseStep 28147783 = 42221675) B42221675
theorem B3162665 : Blo 1873638 3162665 := bstep (se 2 (by rfl) ⟨1185999, by rfl⟩ : syracuseStep 3162665 = 2371999) B2371999
theorem B7603559 : Blo 1873638 7603559 := bstep (se 1 (by rfl) ⟨5702669, by rfl⟩ : syracuseStep 7603559 = 11405339) B11405339
theorem B2107903 : Blo 1873638 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B6002855 : Blo 1873638 6002855 := bstep (se 1 (by rfl) ⟨4502141, by rfl⟩ : syracuseStep 6002855 = 9004283) B9004283
theorem B21633383 : Blo 1873638 21633383 := bstep (se 1 (by rfl) ⟨16225037, by rfl⟩ : syracuseStep 21633383 = 32450075) B32450075
theorem B876870269 : Blo 1873638 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B1874943 : Blo 1873638 1874943 := bstep (se 1 (by rfl) ⟨1406207, by rfl⟩ : syracuseStep 1874943 = 2812415) B2812415
theorem B1875183 : Blo 1873638 1875183 := bstep (se 1 (by rfl) ⟨1406387, by rfl⟩ : syracuseStep 1875183 = 2812775) B2812775
theorem B2810537 : Blo 1873638 2810537 := bstep (se 2 (by rfl) ⟨1053951, by rfl⟩ : syracuseStep 2810537 = 2107903) B2107903
theorem B37530377 : Blo 1873638 37530377 := bstep (se 2 (by rfl) ⟨14073891, by rfl⟩ : syracuseStep 37530377 = 28147783) B28147783
theorem B2108443 : Blo 1873638 2108443 := bstep (se 1 (by rfl) ⟨1581332, by rfl⟩ : syracuseStep 2108443 = 3162665) B3162665
theorem B4001903 : Blo 1873638 4001903 := bstep (se 1 (by rfl) ⟨3001427, by rfl⟩ : syracuseStep 4001903 = 6002855) B6002855
theorem B14422255 : Blo 1873638 14422255 := bstep (se 1 (by rfl) ⟨10816691, by rfl⟩ : syracuseStep 14422255 = 21633383) B21633383
theorem B5069039 : Blo 1873638 5069039 := bstep (se 1 (by rfl) ⟨3801779, by rfl⟩ : syracuseStep 5069039 = 7603559) B7603559
theorem B584580179 : Blo 1873638 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B13517437 : Blo 1873638 13517437 := bstep (se 3 (by rfl) ⟨2534519, by rfl⟩ : syracuseStep 13517437 = 5069039) B5069039
theorem B2811257 : Blo 1873638 2811257 := bstep (se 2 (by rfl) ⟨1054221, by rfl⟩ : syracuseStep 2811257 = 2108443) B2108443
theorem B25020251 : Blo 1873638 25020251 := bstep (se 1 (by rfl) ⟨18765188, by rfl⟩ : syracuseStep 25020251 = 37530377) B37530377
theorem B389720119 : Blo 1873638 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B76918693 : Blo 1873638 76918693 := bstep (se 4 (by rfl) ⟨7211127, by rfl⟩ : syracuseStep 76918693 = 14422255) B14422255
theorem B2667935 : Blo 1873638 2667935 := bstep (se 1 (by rfl) ⟨2000951, by rfl⟩ : syracuseStep 2667935 = 4001903) B4001903
theorem B1873691 : Blo 1873638 1873691 := bstep (se 1 (by rfl) ⟨1405268, by rfl⟩ : syracuseStep 1873691 = 2810537) B2810537
theorem B519626825 : Blo 1873638 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B18023249 : Blo 1873638 18023249 := bstep (se 2 (by rfl) ⟨6758718, by rfl⟩ : syracuseStep 18023249 = 13517437) B13517437
theorem B16680167 : Blo 1873638 16680167 := bstep (se 1 (by rfl) ⟨12510125, by rfl⟩ : syracuseStep 16680167 = 25020251) B25020251
theorem B102558257 : Blo 1873638 102558257 := bstep (se 2 (by rfl) ⟨38459346, by rfl⟩ : syracuseStep 102558257 = 76918693) B76918693
theorem B7114493 : Blo 1873638 7114493 := bstep (se 3 (by rfl) ⟨1333967, by rfl⟩ : syracuseStep 7114493 = 2667935) B2667935
theorem B1874171 : Blo 1873638 1874171 := bstep (se 1 (by rfl) ⟨1405628, by rfl⟩ : syracuseStep 1874171 = 2811257) B2811257
theorem B68372171 : Blo 1873638 68372171 := bstep (se 1 (by rfl) ⟨51279128, by rfl⟩ : syracuseStep 68372171 = 102558257) B102558257
theorem B346417883 : Blo 1873638 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B11120111 : Blo 1873638 11120111 := bstep (se 1 (by rfl) ⟨8340083, by rfl⟩ : syracuseStep 11120111 = 16680167) B16680167
theorem B12015499 : Blo 1873638 12015499 := bstep (se 1 (by rfl) ⟨9011624, by rfl⟩ : syracuseStep 12015499 = 18023249) B18023249
theorem B4742995 : Blo 1873638 4742995 := bstep (se 1 (by rfl) ⟨3557246, by rfl⟩ : syracuseStep 4742995 = 7114493) B7114493
theorem B45581447 : Blo 1873638 45581447 := bstep (se 1 (by rfl) ⟨34186085, by rfl⟩ : syracuseStep 45581447 = 68372171) B68372171
theorem B230945255 : Blo 1873638 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B16020665 : Blo 1873638 16020665 := bstep (se 2 (by rfl) ⟨6007749, by rfl⟩ : syracuseStep 16020665 = 12015499) B12015499
theorem B7413407 : Blo 1873638 7413407 := bstep (se 1 (by rfl) ⟨5560055, by rfl⟩ : syracuseStep 7413407 = 11120111) B11120111
theorem B6323993 : Blo 1873638 6323993 := bstep (se 2 (by rfl) ⟨2371497, by rfl⟩ : syracuseStep 6323993 = 4742995) B4742995
theorem B4942271 : Blo 1873638 4942271 := bstep (se 1 (by rfl) ⟨3706703, by rfl⟩ : syracuseStep 4942271 = 7413407) B7413407
theorem B153963503 : Blo 1873638 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B30387631 : Blo 1873638 30387631 := bstep (se 1 (by rfl) ⟨22790723, by rfl⟩ : syracuseStep 30387631 = 45581447) B45581447
theorem B4215995 : Blo 1873638 4215995 := bstep (se 1 (by rfl) ⟨3161996, by rfl⟩ : syracuseStep 4215995 = 6323993) B6323993
theorem B10680443 : Blo 1873638 10680443 := bstep (se 1 (by rfl) ⟨8010332, by rfl⟩ : syracuseStep 10680443 = 16020665) B16020665
theorem B2810663 : Blo 1873638 2810663 := bstep (se 1 (by rfl) ⟨2107997, by rfl⟩ : syracuseStep 2810663 = 4215995) B4215995
theorem B7120295 : Blo 1873638 7120295 := bstep (se 1 (by rfl) ⟨5340221, by rfl⟩ : syracuseStep 7120295 = 10680443) B10680443
theorem B3294847 : Blo 1873638 3294847 := bstep (se 1 (by rfl) ⟨2471135, by rfl⟩ : syracuseStep 3294847 = 4942271) B4942271
theorem B102642335 : Blo 1873638 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B40516841 : Blo 1873638 40516841 := bstep (se 2 (by rfl) ⟨15193815, by rfl⟩ : syracuseStep 40516841 = 30387631) B30387631
theorem B68428223 : Blo 1873638 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B27011227 : Blo 1873638 27011227 := bstep (se 1 (by rfl) ⟨20258420, by rfl⟩ : syracuseStep 27011227 = 40516841) B40516841
theorem B4393129 : Blo 1873638 4393129 := bstep (se 2 (by rfl) ⟨1647423, by rfl⟩ : syracuseStep 4393129 = 3294847) B3294847
theorem B4746863 : Blo 1873638 4746863 := bstep (se 1 (by rfl) ⟨3560147, by rfl⟩ : syracuseStep 4746863 = 7120295) B7120295
theorem B1873775 : Blo 1873638 1873775 := bstep (se 1 (by rfl) ⟨1405331, by rfl⟩ : syracuseStep 1873775 = 2810663) B2810663
theorem B5857505 : Blo 1873638 5857505 := bstep (se 2 (by rfl) ⟨2196564, by rfl⟩ : syracuseStep 5857505 = 4393129) B4393129
theorem B3164575 : Blo 1873638 3164575 := bstep (se 1 (by rfl) ⟨2373431, by rfl⟩ : syracuseStep 3164575 = 4746863) B4746863
theorem B36014969 : Blo 1873638 36014969 := bstep (se 2 (by rfl) ⟨13505613, by rfl⟩ : syracuseStep 36014969 = 27011227) B27011227
theorem B45618815 : Blo 1873638 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B4219433 : Blo 1873638 4219433 := bstep (se 2 (by rfl) ⟨1582287, by rfl⟩ : syracuseStep 4219433 = 3164575) B3164575
theorem B30412543 : Blo 1873638 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B3905003 : Blo 1873638 3905003 := bstep (se 1 (by rfl) ⟨2928752, by rfl⟩ : syracuseStep 3905003 = 5857505) B5857505
theorem B24009979 : Blo 1873638 24009979 := bstep (se 1 (by rfl) ⟨18007484, by rfl⟩ : syracuseStep 24009979 = 36014969) B36014969
theorem B2812955 : Blo 1873638 2812955 := bstep (se 1 (by rfl) ⟨2109716, by rfl⟩ : syracuseStep 2812955 = 4219433) B4219433
theorem B2603335 : Blo 1873638 2603335 := bstep (se 1 (by rfl) ⟨1952501, by rfl⟩ : syracuseStep 2603335 = 3905003) B3905003
theorem B32013305 : Blo 1873638 32013305 := bstep (se 2 (by rfl) ⟨12004989, by rfl⟩ : syracuseStep 32013305 = 24009979) B24009979
theorem B40550057 : Blo 1873638 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B21342203 : Blo 1873638 21342203 := bstep (se 1 (by rfl) ⟨16006652, by rfl⟩ : syracuseStep 21342203 = 32013305) B32013305
theorem B3471113 : Blo 1873638 3471113 := bstep (se 2 (by rfl) ⟨1301667, by rfl⟩ : syracuseStep 3471113 = 2603335) B2603335
theorem B1875303 : Blo 1873638 1875303 := bstep (se 1 (by rfl) ⟨1406477, by rfl⟩ : syracuseStep 1875303 = 2812955) B2812955
theorem B27033371 : Blo 1873638 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B14228135 : Blo 1873638 14228135 := bstep (se 1 (by rfl) ⟨10671101, by rfl⟩ : syracuseStep 14228135 = 21342203) B21342203
theorem B9256301 : Blo 1873638 9256301 := bstep (se 3 (by rfl) ⟨1735556, by rfl⟩ : syracuseStep 9256301 = 3471113) B3471113
theorem B18022247 : Blo 1873638 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B6170867 : Blo 1873638 6170867 := bstep (se 1 (by rfl) ⟨4628150, by rfl⟩ : syracuseStep 6170867 = 9256301) B9256301
theorem B12014831 : Blo 1873638 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B9485423 : Blo 1873638 9485423 := bstep (se 1 (by rfl) ⟨7114067, by rfl⟩ : syracuseStep 9485423 = 14228135) B14228135
theorem B32039549 : Blo 1873638 32039549 := bstep (se 3 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 32039549 = 12014831) B12014831
theorem B4113911 : Blo 1873638 4113911 := bstep (se 1 (by rfl) ⟨3085433, by rfl⟩ : syracuseStep 4113911 = 6170867) B6170867
theorem B6323615 : Blo 1873638 6323615 := bstep (se 1 (by rfl) ⟨4742711, by rfl⟩ : syracuseStep 6323615 = 9485423) B9485423
theorem B21359699 : Blo 1873638 21359699 := bstep (se 1 (by rfl) ⟨16019774, by rfl⟩ : syracuseStep 21359699 = 32039549) B32039549
theorem B4215743 : Blo 1873638 4215743 := bstep (se 1 (by rfl) ⟨3161807, by rfl⟩ : syracuseStep 4215743 = 6323615) B6323615
theorem B2742607 : Blo 1873638 2742607 := bstep (se 1 (by rfl) ⟨2056955, by rfl⟩ : syracuseStep 2742607 = 4113911) B4113911
theorem B2810495 : Blo 1873638 2810495 := bstep (se 1 (by rfl) ⟨2107871, by rfl⟩ : syracuseStep 2810495 = 4215743) B4215743
theorem B14239799 : Blo 1873638 14239799 := bstep (se 1 (by rfl) ⟨10679849, by rfl⟩ : syracuseStep 14239799 = 21359699) B21359699
theorem B3656809 : Blo 1873638 3656809 := bstep (se 2 (by rfl) ⟨1371303, by rfl⟩ : syracuseStep 3656809 = 2742607) B2742607
theorem B4875745 : Blo 1873638 4875745 := bstep (se 2 (by rfl) ⟨1828404, by rfl⟩ : syracuseStep 4875745 = 3656809) B3656809
theorem B1873663 : Blo 1873638 1873663 := bstep (se 1 (by rfl) ⟨1405247, by rfl⟩ : syracuseStep 1873663 = 2810495) B2810495
theorem B9493199 : Blo 1873638 9493199 := bstep (se 1 (by rfl) ⟨7119899, by rfl⟩ : syracuseStep 9493199 = 14239799) B14239799
theorem B6328799 : Blo 1873638 6328799 := bstep (se 1 (by rfl) ⟨4746599, by rfl⟩ : syracuseStep 6328799 = 9493199) B9493199
theorem B6500993 : Blo 1873638 6500993 := bstep (se 2 (by rfl) ⟨2437872, by rfl⟩ : syracuseStep 6500993 = 4875745) B4875745
theorem B4219199 : Blo 1873638 4219199 := bstep (se 1 (by rfl) ⟨3164399, by rfl⟩ : syracuseStep 4219199 = 6328799) B6328799
theorem B17335981 : Blo 1873638 17335981 := bstep (se 3 (by rfl) ⟨3250496, by rfl⟩ : syracuseStep 17335981 = 6500993) B6500993
theorem B2812799 : Blo 1873638 2812799 := bstep (se 1 (by rfl) ⟨2109599, by rfl⟩ : syracuseStep 2812799 = 4219199) B4219199
theorem B23114641 : Blo 1873638 23114641 := bstep (se 2 (by rfl) ⟨8667990, by rfl⟩ : syracuseStep 23114641 = 17335981) B17335981
theorem B30819521 : Blo 1873638 30819521 := bstep (se 2 (by rfl) ⟨11557320, by rfl⟩ : syracuseStep 30819521 = 23114641) B23114641
theorem B1875199 : Blo 1873638 1875199 := bstep (se 1 (by rfl) ⟨1406399, by rfl⟩ : syracuseStep 1875199 = 2812799) B2812799
theorem B20546347 : Blo 1873638 20546347 := bstep (se 1 (by rfl) ⟨15409760, by rfl⟩ : syracuseStep 20546347 = 30819521) B30819521
theorem B27395129 : Blo 1873638 27395129 := bstep (se 2 (by rfl) ⟨10273173, by rfl⟩ : syracuseStep 27395129 = 20546347) B20546347
theorem B73053677 : Blo 1873638 73053677 := bstep (se 3 (by rfl) ⟨13697564, by rfl⟩ : syracuseStep 73053677 = 27395129) B27395129
theorem B194809805 : Blo 1873638 194809805 := bstep (se 3 (by rfl) ⟨36526838, by rfl⟩ : syracuseStep 194809805 = 73053677) B73053677
theorem B129873203 : Blo 1873638 129873203 := bstep (se 1 (by rfl) ⟨97404902, by rfl⟩ : syracuseStep 129873203 = 194809805) B194809805
theorem B86582135 : Blo 1873638 86582135 := bstep (se 1 (by rfl) ⟨64936601, by rfl⟩ : syracuseStep 86582135 = 129873203) B129873203
theorem B57721423 : Blo 1873638 57721423 := bstep (se 1 (by rfl) ⟨43291067, by rfl⟩ : syracuseStep 57721423 = 86582135) B86582135
theorem B76961897 : Blo 1873638 76961897 := bstep (se 2 (by rfl) ⟨28860711, by rfl⟩ : syracuseStep 76961897 = 57721423) B57721423
theorem B51307931 : Blo 1873638 51307931 := bstep (se 1 (by rfl) ⟨38480948, by rfl⟩ : syracuseStep 51307931 = 76961897) B76961897
theorem B136821149 : Blo 1873638 136821149 := bstep (se 3 (by rfl) ⟨25653965, by rfl⟩ : syracuseStep 136821149 = 51307931) B51307931
theorem B91214099 : Blo 1873638 91214099 := bstep (se 1 (by rfl) ⟨68410574, by rfl⟩ : syracuseStep 91214099 = 136821149) B136821149
theorem B60809399 : Blo 1873638 60809399 := bstep (se 1 (by rfl) ⟨45607049, by rfl⟩ : syracuseStep 60809399 = 91214099) B91214099
theorem B40539599 : Blo 1873638 40539599 := bstep (se 1 (by rfl) ⟨30404699, by rfl⟩ : syracuseStep 40539599 = 60809399) B60809399
theorem B27026399 : Blo 1873638 27026399 := bstep (se 1 (by rfl) ⟨20269799, by rfl⟩ : syracuseStep 27026399 = 40539599) B40539599
theorem B18017599 : Blo 1873638 18017599 := bstep (se 1 (by rfl) ⟨13513199, by rfl⟩ : syracuseStep 18017599 = 27026399) B27026399
theorem B24023465 : Blo 1873638 24023465 := bstep (se 2 (by rfl) ⟨9008799, by rfl⟩ : syracuseStep 24023465 = 18017599) B18017599
theorem B16015643 : Blo 1873638 16015643 := bstep (se 1 (by rfl) ⟨12011732, by rfl⟩ : syracuseStep 16015643 = 24023465) B24023465
theorem B10677095 : Blo 1873638 10677095 := bstep (se 1 (by rfl) ⟨8007821, by rfl⟩ : syracuseStep 10677095 = 16015643) B16015643
theorem B7118063 : Blo 1873638 7118063 := bstep (se 1 (by rfl) ⟨5338547, by rfl⟩ : syracuseStep 7118063 = 10677095) B10677095
theorem B4745375 : Blo 1873638 4745375 := bstep (se 1 (by rfl) ⟨3559031, by rfl⟩ : syracuseStep 4745375 = 7118063) B7118063
theorem B3163583 : Blo 1873638 3163583 := bstep (se 1 (by rfl) ⟨2372687, by rfl⟩ : syracuseStep 3163583 = 4745375) B4745375
theorem B2109055 : Blo 1873638 2109055 := bstep (se 1 (by rfl) ⟨1581791, by rfl⟩ : syracuseStep 2109055 = 3163583) B3163583
theorem B2812073 : Blo 1873638 2812073 := bstep (se 2 (by rfl) ⟨1054527, by rfl⟩ : syracuseStep 2812073 = 2109055) B2109055
theorem B1874715 : Blo 1873638 1874715 := bstep (se 1 (by rfl) ⟨1406036, by rfl⟩ : syracuseStep 1874715 = 2812073) B2812073

theorem C0 (j : ℕ) (h1 : 468409 ≤ j) (h2 : j ≤ 468908) : Blo 1873638 (4 * j + 3) := by
  interval_cases j
  · exact B1873639
  · exact B1873643
  · exact B1873647
  · exact B1873651
  · exact B1873655
  · exact B1873659
  · exact B1873663
  · exact B1873667
  · exact B1873671
  · exact B1873675
  · exact B1873679
  · exact B1873683
  · exact B1873687
  · exact B1873691
  · exact B1873695
  · exact B1873699
  · exact B1873703
  · exact B1873707
  · exact B1873711
  · exact B1873715
  · exact B1873719
  · exact B1873723
  · exact B1873727
  · exact B1873731
  · exact B1873735
  · exact B1873739
  · exact B1873743
  · exact B1873747
  · exact B1873751
  · exact B1873755
  · exact B1873759
  · exact B1873763
  · exact B1873767
  · exact B1873771
  · exact B1873775
  · exact B1873779
  · exact B1873783
  · exact B1873787
  · exact B1873791
  · exact B1873795
  · exact B1873799
  · exact B1873803
  · exact B1873807
  · exact B1873811
  · exact B1873815
  · exact B1873819
  · exact B1873823
  · exact B1873827
  · exact B1873831
  · exact B1873835
  · exact B1873839
  · exact B1873843
  · exact B1873847
  · exact B1873851
  · exact B1873855
  · exact B1873859
  · exact B1873863
  · exact B1873867
  · exact B1873871
  · exact B1873875
  · exact B1873879
  · exact B1873883
  · exact B1873887
  · exact B1873891
  · exact B1873895
  · exact B1873899
  · exact B1873903
  · exact B1873907
  · exact B1873911
  · exact B1873915
  · exact B1873919
  · exact B1873923
  · exact B1873927
  · exact B1873931
  · exact B1873935
  · exact B1873939
  · exact B1873943
  · exact B1873947
  · exact B1873951
  · exact B1873955
  · exact B1873959
  · exact B1873963
  · exact B1873967
  · exact B1873971
  · exact B1873975
  · exact B1873979
  · exact B1873983
  · exact B1873987
  · exact B1873991
  · exact B1873995
  · exact B1873999
  · exact B1874003
  · exact B1874007
  · exact B1874011
  · exact B1874015
  · exact B1874019
  · exact B1874023
  · exact B1874027
  · exact B1874031
  · exact B1874035
  · exact B1874039
  · exact B1874043
  · exact B1874047
  · exact B1874051
  · exact B1874055
  · exact B1874059
  · exact B1874063
  · exact B1874067
  · exact B1874071
  · exact B1874075
  · exact B1874079
  · exact B1874083
  · exact B1874087
  · exact B1874091
  · exact B1874095
  · exact B1874099
  · exact B1874103
  · exact B1874107
  · exact B1874111
  · exact B1874115
  · exact B1874119
  · exact B1874123
  · exact B1874127
  · exact B1874131
  · exact B1874135
  · exact B1874139
  · exact B1874143
  · exact B1874147
  · exact B1874151
  · exact B1874155
  · exact B1874159
  · exact B1874163
  · exact B1874167
  · exact B1874171
  · exact B1874175
  · exact B1874179
  · exact B1874183
  · exact B1874187
  · exact B1874191
  · exact B1874195
  · exact B1874199
  · exact B1874203
  · exact B1874207
  · exact B1874211
  · exact B1874215
  · exact B1874219
  · exact B1874223
  · exact B1874227
  · exact B1874231
  · exact B1874235
  · exact B1874239
  · exact B1874243
  · exact B1874247
  · exact B1874251
  · exact B1874255
  · exact B1874259
  · exact B1874263
  · exact B1874267
  · exact B1874271
  · exact B1874275
  · exact B1874279
  · exact B1874283
  · exact B1874287
  · exact B1874291
  · exact B1874295
  · exact B1874299
  · exact B1874303
  · exact B1874307
  · exact B1874311
  · exact B1874315
  · exact B1874319
  · exact B1874323
  · exact B1874327
  · exact B1874331
  · exact B1874335
  · exact B1874339
  · exact B1874343
  · exact B1874347
  · exact B1874351
  · exact B1874355
  · exact B1874359
  · exact B1874363
  · exact B1874367
  · exact B1874371
  · exact B1874375
  · exact B1874379
  · exact B1874383
  · exact B1874387
  · exact B1874391
  · exact B1874395
  · exact B1874399
  · exact B1874403
  · exact B1874407
  · exact B1874411
  · exact B1874415
  · exact B1874419
  · exact B1874423
  · exact B1874427
  · exact B1874431
  · exact B1874435
  · exact B1874439
  · exact B1874443
  · exact B1874447
  · exact B1874451
  · exact B1874455
  · exact B1874459
  · exact B1874463
  · exact B1874467
  · exact B1874471
  · exact B1874475
  · exact B1874479
  · exact B1874483
  · exact B1874487
  · exact B1874491
  · exact B1874495
  · exact B1874499
  · exact B1874503
  · exact B1874507
  · exact B1874511
  · exact B1874515
  · exact B1874519
  · exact B1874523
  · exact B1874527
  · exact B1874531
  · exact B1874535
  · exact B1874539
  · exact B1874543
  · exact B1874547
  · exact B1874551
  · exact B1874555
  · exact B1874559
  · exact B1874563
  · exact B1874567
  · exact B1874571
  · exact B1874575
  · exact B1874579
  · exact B1874583
  · exact B1874587
  · exact B1874591
  · exact B1874595
  · exact B1874599
  · exact B1874603
  · exact B1874607
  · exact B1874611
  · exact B1874615
  · exact B1874619
  · exact B1874623
  · exact B1874627
  · exact B1874631
  · exact B1874635
  · exact B1874639
  · exact B1874643
  · exact B1874647
  · exact B1874651
  · exact B1874655
  · exact B1874659
  · exact B1874663
  · exact B1874667
  · exact B1874671
  · exact B1874675
  · exact B1874679
  · exact B1874683
  · exact B1874687
  · exact B1874691
  · exact B1874695
  · exact B1874699
  · exact B1874703
  · exact B1874707
  · exact B1874711
  · exact B1874715
  · exact B1874719
  · exact B1874723
  · exact B1874727
  · exact B1874731
  · exact B1874735
  · exact B1874739
  · exact B1874743
  · exact B1874747
  · exact B1874751
  · exact B1874755
  · exact B1874759
  · exact B1874763
  · exact B1874767
  · exact B1874771
  · exact B1874775
  · exact B1874779
  · exact B1874783
  · exact B1874787
  · exact B1874791
  · exact B1874795
  · exact B1874799
  · exact B1874803
  · exact B1874807
  · exact B1874811
  · exact B1874815
  · exact B1874819
  · exact B1874823
  · exact B1874827
  · exact B1874831
  · exact B1874835
  · exact B1874839
  · exact B1874843
  · exact B1874847
  · exact B1874851
  · exact B1874855
  · exact B1874859
  · exact B1874863
  · exact B1874867
  · exact B1874871
  · exact B1874875
  · exact B1874879
  · exact B1874883
  · exact B1874887
  · exact B1874891
  · exact B1874895
  · exact B1874899
  · exact B1874903
  · exact B1874907
  · exact B1874911
  · exact B1874915
  · exact B1874919
  · exact B1874923
  · exact B1874927
  · exact B1874931
  · exact B1874935
  · exact B1874939
  · exact B1874943
  · exact B1874947
  · exact B1874951
  · exact B1874955
  · exact B1874959
  · exact B1874963
  · exact B1874967
  · exact B1874971
  · exact B1874975
  · exact B1874979
  · exact B1874983
  · exact B1874987
  · exact B1874991
  · exact B1874995
  · exact B1874999
  · exact B1875003
  · exact B1875007
  · exact B1875011
  · exact B1875015
  · exact B1875019
  · exact B1875023
  · exact B1875027
  · exact B1875031
  · exact B1875035
  · exact B1875039
  · exact B1875043
  · exact B1875047
  · exact B1875051
  · exact B1875055
  · exact B1875059
  · exact B1875063
  · exact B1875067
  · exact B1875071
  · exact B1875075
  · exact B1875079
  · exact B1875083
  · exact B1875087
  · exact B1875091
  · exact B1875095
  · exact B1875099
  · exact B1875103
  · exact B1875107
  · exact B1875111
  · exact B1875115
  · exact B1875119
  · exact B1875123
  · exact B1875127
  · exact B1875131
  · exact B1875135
  · exact B1875139
  · exact B1875143
  · exact B1875147
  · exact B1875151
  · exact B1875155
  · exact B1875159
  · exact B1875163
  · exact B1875167
  · exact B1875171
  · exact B1875175
  · exact B1875179
  · exact B1875183
  · exact B1875187
  · exact B1875191
  · exact B1875195
  · exact B1875199
  · exact B1875203
  · exact B1875207
  · exact B1875211
  · exact B1875215
  · exact B1875219
  · exact B1875223
  · exact B1875227
  · exact B1875231
  · exact B1875235
  · exact B1875239
  · exact B1875243
  · exact B1875247
  · exact B1875251
  · exact B1875255
  · exact B1875259
  · exact B1875263
  · exact B1875267
  · exact B1875271
  · exact B1875275
  · exact B1875279
  · exact B1875283
  · exact B1875287
  · exact B1875291
  · exact B1875295
  · exact B1875299
  · exact B1875303
  · exact B1875307
  · exact B1875311
  · exact B1875315
  · exact B1875319
  · exact B1875323
  · exact B1875327
  · exact B1875331
  · exact B1875335
  · exact B1875339
  · exact B1875343
  · exact B1875347
  · exact B1875351
  · exact B1875355
  · exact B1875359
  · exact B1875363
  · exact B1875367
  · exact B1875371
  · exact B1875375
  · exact B1875379
  · exact B1875383
  · exact B1875387
  · exact B1875391
  · exact B1875395
  · exact B1875399
  · exact B1875403
  · exact B1875407
  · exact B1875411
  · exact B1875415
  · exact B1875419
  · exact B1875423
  · exact B1875427
  · exact B1875431
  · exact B1875435
  · exact B1875439
  · exact B1875443
  · exact B1875447
  · exact B1875451
  · exact B1875455
  · exact B1875459
  · exact B1875463
  · exact B1875467
  · exact B1875471
  · exact B1875475
  · exact B1875479
  · exact B1875483
  · exact B1875487
  · exact B1875491
  · exact B1875495
  · exact B1875499
  · exact B1875503
  · exact B1875507
  · exact B1875511
  · exact B1875515
  · exact B1875519
  · exact B1875523
  · exact B1875527
  · exact B1875531
  · exact B1875535
  · exact B1875539
  · exact B1875543
  · exact B1875547
  · exact B1875551
  · exact B1875555
  · exact B1875559
  · exact B1875563
  · exact B1875567
  · exact B1875571
  · exact B1875575
  · exact B1875579
  · exact B1875583
  · exact B1875587
  · exact B1875591
  · exact B1875595
  · exact B1875599
  · exact B1875603
  · exact B1875607
  · exact B1875611
  · exact B1875615
  · exact B1875619
  · exact B1875623
  · exact B1875627
  · exact B1875631
  · exact B1875635

theorem solution (m : ℕ) (hlo : 1873638 ≤ m) (hhi : m ≤ 1875638) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 468409 ≤ j := by omega
    have hj2 : j ≤ 468908 := by omega
    have hb : Blo 1873638 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
